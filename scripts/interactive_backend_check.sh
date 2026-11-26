#!/usr/bin/env bash
# interactive_backend_check.sh — drive interactive mode over HTTP on both
# algebra backends and compare what the server answers.
#
# For each backend (maude, proved-only) the script starts
# `tamarin-rs interactive --algebra-backend=<backend>` on a free localhost
# port with a small Diffie-Hellman theory and a small XOR theory, and then,
# for one lemma of each theory:
#
#   1. loads the start page and the theory page,
#   2. opens the lemma (the applicable proof methods),
#   3. applies one manual proof step (method 1) and fetches the proof state
#      it leads to,
#   4. autoproves the rest from that state and fetches the finished proof
#      (overview, proof pane and the downloadable theory),
#   5. autoproves every lemma of the untouched theory.
#
# Every response body is saved under $OUT/<backend>/. After removing the
# lines that name the backend or a clock, the two directories must be
# identical, or identical up to the numbering of variables (see the
# comparison at the end). The server is stopped by its PID before the script
# returns.
#
# Usage:  scripts/interactive_backend_check.sh [<theory.spthy>:<lemma> ...]
# Env:    RS_PATH   prover binary built with --features lean-unification
#                   (default: target/ci/tamarin-rs, then target/release/tamarin-rs)
#         OUT       output directory (default: scripts/results/interactive_backend)
#         BACKENDS  backends to drive (default: "maude proved-only")
#         MEM_MAX   cgroup memory cap per server via systemd-run, when
#                   available (default 4G; empty for none)
#         LIFETIME  hard limit on one server's life in seconds (default 300)
#         MAUDE_PATH  Maude for the maude backend (default: `maude` on PATH)
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
examples=$root/tamarin-prover/examples
OUT=${OUT:-$root/scripts/results/interactive_backend}
BACKENDS=${BACKENDS:-maude proved-only}
MEM_MAX=${MEM_MAX-4G}
LIFETIME=${LIFETIME:-300}

if [ -z "${RS_PATH:-}" ]; then
    for candidate in "$root/target/ci/tamarin-rs" "$root/target/release/tamarin-rs"; do
        if [ -x "$candidate" ]; then RS_PATH=$candidate; break; fi
    done
fi
[ -x "${RS_PATH:-}" ] || { echo "no prover binary: set RS_PATH" >&2; exit 2; }

cases=("$@")
if [ ${#cases[@]} -eq 0 ]; then
    cases=("$examples/cav13/DH_example.spthy:Accept_Secret"
           "$examples/features/xor/CRxor.spthy:alive")
fi
theories=()
lemmas=()
for item in "${cases[@]}"; do
    theories+=("${item%:*}")
    lemmas+=("${item##*:}")
    [ -f "${item%:*}" ] || { echo "no such theory: ${item%:*}" >&2; exit 2; }
done

maude=${MAUDE_PATH:-$(command -v maude || true)}

cap=()
if [ -n "$MEM_MAX" ] && systemd-run --user --scope -q true 2>/dev/null; then
    cap=(systemd-run --user --scope -q --expand-environment=no
         -p "MemoryMax=$MEM_MAX" -p MemorySwapMax=0)
elif [ -n "$MEM_MAX" ]; then
    echo "note: systemd-run --user is unavailable; the servers run without a memory cap" >&2
fi

server_pid=
stop_server() {
    if [ -n "$server_pid" ]; then
        kill "$server_pid" 2>/dev/null || true
        wait "$server_pid" 2>/dev/null || true
        server_pid=
    fi
}
trap stop_server EXIT

free_port() {
    python3 -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])'
}

failures=0
step=0
# fetch <dir> <label> <path>: save the body, require HTTP 200, echo the body's file.
fetch() {
    local dir=$1 label=$2 path=$3 file code
    step=$((step + 1))
    file=$(printf '%s/%02d_%s' "$dir" "$step" "$label")
    code=$(curl -sS -m 120 -o "$file" -w '%{http_code}' "http://127.0.0.1:$port$path" || echo 000)
    printf '%s\t%s\t%s\n' "$code" "$label" "$path" >> "$dir/requests.tsv"
    if [ "$code" != 200 ]; then
        echo "  FAIL $code $path" >&2
        failures=$((failures + 1))
    fi
    printf '%s\n' "$file"
}

# The path a `{"redirect": ...}` reply names.
redirect_of() {
    python3 -c 'import json, sys; print(json.load(open(sys.argv[1])).get("redirect", ""))' "$1" 2>/dev/null || true
}

drive() {
    local backend=$1 dir=$OUT/$1 args i lemma reply target idx
    rm -rf "$dir"; mkdir -p "$dir"
    port=$(free_port)
    args=(interactive "--algebra-backend=$backend" "--port=$port")
    if [ "$backend" = maude ]; then
        [ -n "$maude" ] || { echo "no maude: set MAUDE_PATH" >&2; exit 2; }
        args+=("--with-maude=$maude")
    fi
    "${cap[@]}" timeout "$LIFETIME" "$RS_PATH" "${args[@]}" "${theories[@]}" \
        > "$dir/server.out" 2> "$dir/server.err" &
    server_pid=$!
    for _ in $(seq 1 300); do
        curl -s -o /dev/null "http://127.0.0.1:$port/" && break
        kill -0 "$server_pid" 2>/dev/null || break
        sleep 0.2
    done
    if ! curl -s -o /dev/null "http://127.0.0.1:$port/"; then
        echo "  FAIL the $backend server did not come up; see $dir/server.err" >&2
        failures=$((failures + 1))
        stop_server
        return
    fi
    echo "== $backend: server pid $server_pid on port $port"
    step=0
    fetch "$dir" root / > /dev/null
    for i in "${!theories[@]}"; do
        idx=$((i + 1)); lemma=${lemmas[$i]}
        fetch "$dir" "thy${idx}_overview" "/thy/trace/$idx/overview/help" > /dev/null
        fetch "$dir" "thy${idx}_rules" "/thy/trace/$idx/main/rules" > /dev/null
        fetch "$dir" "thy${idx}_open_lemma" "/thy/trace/$idx/main/proof/$lemma" > /dev/null
        # One manual step: the first applicable method at the lemma's root.
        reply=$(fetch "$dir" "thy${idx}_manual_step" "/thy/trace/$idx/main/method/$lemma/1")
        target=$(redirect_of "$reply")
        if [[ "$target" != /thy/trace/*/overview/* ]]; then
            echo "  FAIL the manual step of $lemma answered no redirect" >&2
            failures=$((failures + 1)); continue
        fi
        fetch "$dir" "thy${idx}_after_step_overview" "$target" > /dev/null
        fetch "$dir" "thy${idx}_after_step_state" "${target/overview/main}" > /dev/null
        # Autoprove from the state the manual step reached.
        reply=$(fetch "$dir" "thy${idx}_autoprove" \
            "$(sed -E 's#^(/thy/trace/[0-9]+)/overview/#\1/autoprove/idfs/0/False/#' <<< "$target")")
        target=$(redirect_of "$reply")
        if [[ "$target" != /thy/trace/*/overview/* ]]; then
            echo "  FAIL autoprove of $lemma answered no redirect" >&2
            failures=$((failures + 1)); continue
        fi
        proved=${target#/thy/trace/}; proved=${proved%%/*}
        fetch "$dir" "thy${idx}_proved_overview" "/thy/trace/$proved/overview/proof/$lemma" > /dev/null
        fetch "$dir" "thy${idx}_proved_state" "/thy/trace/$proved/main/proof/$lemma" > /dev/null
        fetch "$dir" "thy${idx}_proved_download" "/thy/trace/$proved/download/proved.spthy" > /dev/null
        # Every lemma of the untouched theory.
        reply=$(fetch "$dir" "thy${idx}_autoprove_all" "/thy/trace/$idx/autoproveAll/idfs/0/proof/$lemma")
        target=$(redirect_of "$reply")
        if [[ "$target" == /thy/trace/*/overview/* ]]; then
            proved=${target#/thy/trace/}; proved=${proved%%/*}
            fetch "$dir" "thy${idx}_all_download" "/thy/trace/$proved/download/all.spthy" > /dev/null
        else
            echo "  FAIL autoproveAll of theory $idx answered no redirect" >&2
            failures=$((failures + 1))
        fi
    done
    stop_server
    if grep -n "panicked" "$dir/server.err"; then
        echo "  FAIL the $backend server panicked" >&2
        failures=$((failures + 1))
    fi
    # What may differ between two runs or two backends: clocks, the port and
    # the lines that name the algebra engine.
    mkdir -p "$dir/normalized"
    for file in "$dir"/[0-9]*; do
        sed -E -e 's/[0-9]{2}:[0-9]{2}:[0-9]{2}/HH:MM:SS/g' \
               -e 's/[0-9]{4}-[0-9]{2}-[0-9]{2}/YYYY-MM-DD/g' \
               -e "s/127\.0\.0\.1:$port/127.0.0.1:PORT/g" \
               -e '/^Maude version /d' -e '/processing time/d' \
            "$file" > "$dir/normalized/$(basename "$file")"
    done
    cut -f1,2 "$dir/requests.tsv" > "$dir/normalized/requests.tsv"
    echo "   $(wc -l < "$dir/requests.tsv") requests, $(grep -vc '^200' "$dir/requests.tsv" || true) not 200"
}

mkdir -p "$OUT"
for backend in $BACKENDS; do
    drive "$backend"
done

# Where a unification is left to the AC engine, the proved unifier may list
# its complete family in another order than Maude and number the witnesses
# differently, which renumbers variables (`x.1` for `x`) and nothing else;
# batch output differs in the same way. Such responses must still agree once
# the indices are erased.
erase_indices() {
    mkdir -p "$1/unnumbered"
    for file in "$1"/normalized/*; do
        sed -E 's/([[:alnum:]_])\.[0-9]+/\1/g' "$file" > "$1/unnumbered/$(basename "$file")"
    done
}

# shellcheck disable=SC2086
set -- $BACKENDS
if [ $# -eq 2 ]; then
    if diff -r "$OUT/$1/normalized" "$OUT/$2/normalized" > "$OUT/backends.diff"; then
        echo "== $1 and $2 answered every request identically"
    else
        erase_indices "$OUT/$1"; erase_indices "$OUT/$2"
        renumbered=$(grep -c '^diff ' "$OUT/backends.diff" || true)
        if diff -r "$OUT/$1/unnumbered" "$OUT/$2/unnumbered" > "$OUT/backends.unnumbered.diff"; then
            echo "== $1 and $2 answered every request identically up to variable numbering"
            echo "   ($renumbered responses number variables differently; see $OUT/backends.diff)"
        else
            echo "== FAIL $1 and $2 differ; see $OUT/backends.unnumbered.diff" >&2
            diff -rq "$OUT/$1/unnumbered" "$OUT/$2/unnumbered" >&2 || true
            failures=$((failures + 1))
        fi
    fi
fi

if [ "$failures" -ne 0 ]; then
    echo "INTERACTIVE_BACKEND_CHECK verdict=FAIL failures=$failures"
    exit 1
fi
echo "INTERACTIVE_BACKEND_CHECK verdict=OK"
