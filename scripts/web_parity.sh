#!/usr/bin/env bash
# Web-parity gate: semantic (structural) equivalence of the interactive web
# server between HS (oracle) and the Rust port, across a corpus of theory
# files.  The web analogue of corpus_file_diff.sh.
#
# Per file, two strictly-sequential phases so HS and RS never contend:
#   Phase 1 (HS): boot `HS tamarin-prover interactive` on a temp workdir with
#                 the one theory, crawl it (web_crawl.py), cache the response
#                 manifest content-keyed by sha256(file) under .web_hs_cache/.
#   Phase 2 (RS): boot RS on the same workdir, crawl, diff (web_diff.py) the
#                 two manifests semantically (web_normalize.py) → per-url rows.
#
# Env: FILE_TIMEOUT (per-file cap, 300s), READY_TIMEOUT (server-boot wait, 90s),
#      HS_PORT (3021), RS_PORT (3022), CORPUS_ROOT (tamarin-prover/examples/), ALLOWLIST
#      (one relpath/line; default = seed list below), RESULTS_TSV, MAX_NODES
#      (400), CACHE, HS_PATH, RS_PATH, MAUDE_PATH, TAM_RS_NO_AUTO_BUILD.
# Output TSV (6 col): file  url  status  hs_http  rs_http  kind
#   status ∈ MATCH | DIFF | MISSING_RS | MISSING_HS | SKIP_*
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"

FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
READY_TIMEOUT="${READY_TIMEOUT:-90}"
HS_PORT="${HS_PORT:-3021}"
RS_PORT="${RS_PORT:-3022}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE="${CACHE:-$script_dir/.web_hs_cache}"
RESULTS_TSV="${RESULTS_TSV:-/tmp/web_parity.tsv}"
MAX_NODES="${MAX_NODES:-400}"
DIFFDIR="${DIFFDIR:-/tmp/web_parity_diffs}"
mkdir -p "$CACHE"

find_hs_bin() {
    local c
    for c in "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin)}" || { echo "no HS binary" >&2; exit 2; }
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-prover}"
MAUDE_PATH="${MAUDE_PATH:-$(command -v maude)}"

# Auto-build RS (opt out with TAM_RS_NO_AUTO_BUILD=1).
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    echo "building RS (release)..." >&2
    ( cd "$repo_root" && cargo build --release -q -p tamarin-prover ) || {
        echo "RS build failed" >&2; exit 2; }
fi
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }

# --- file list ---
seed_list() {
    cat <<EOF
Tutorial.spthy
EOF
}
filelist() {
    if [ -n "${ALLOWLIST:-}" ] && [ -f "${ALLOWLIST:-}" ]; then cat "$ALLOWLIST"
    else seed_list; fi
}

# Boot a server, wait until it answers on / , run the crawl, then kill it
# (whole process group, to reap maude children).  Args: bin port workdir out.
boot_crawl() {
    local bin="$1" port="$2" wd="$3" out="$4" kind="$5"
    local log="$wd/${kind}_server.log" pid
    # Pin the derivcheck budget like corpus_file_diff.sh does (30s): HS's
    # 5s default expires deterministically on ~12 corpus files even idle,
    # replacing the derivation report with a timeout block RS never emits
    # (48 bogus DIFF rows in the 2026-07-05 sweep).  RS parses the flag on
    # its web path too (hardcoded-5s load is a separate, tracked plumb).
    setsid "$bin" interactive "$wd/thy" --port="$port" \
        --derivcheck-timeout="${DERIVCHECK_TIMEOUT:-30}" >"$log" 2>&1 &
    pid=$!
    # wait for readiness
    local ok="" i
    for ((i=0; i<READY_TIMEOUT; i++)); do
        if curl -sf -o /dev/null "http://127.0.0.1:$port/"; then ok=1; break; fi
        kill -0 "$pid" 2>/dev/null || break
        sleep 1
    done
    if [ -z "$ok" ]; then
        echo "  $kind server not ready ($wd)" >&2
        kill -- -"$pid" 2>/dev/null; wait "$pid" 2>/dev/null
        return 1
    fi
    # shellcheck disable=SC2086  # CRAWL_EXTRA_ARGS must word-split
    timeout "$FILE_TIMEOUT" python3 "$script_dir/web_crawl.py" \
        "http://127.0.0.1:$port" "$out" --max-nodes "$MAX_NODES" ${CRAWL_EXTRA_ARGS:-} 2>>"$log"
    local rc=$?
    kill -- -"$pid" 2>/dev/null; wait "$pid" 2>/dev/null
    return $rc
}

one_file() {
    local rel="$1" f="$CORPUS_ROOT/$1"
    [ -f "$f" ] || { printf '%s\t-\tSKIP_NO_FILE\t-\t-\t-\n' "$rel"; return 0; }
    # A theory with no lemma declaration legitimately discovers 0 lemmas —
    # allow it; otherwise 0 discovered lemmas is a transient failure and
    # web_crawl.py exits 3 (→ SKIP_*_FAIL below, manifest never cached).
    local CRAWL_EXTRA_ARGS=""
    grep -qE '^[[:space:]]*(lemma|equivLemma|diffLemma)([[:space:]]|\[|:)' "$f" \
        || CRAWL_EXTRA_ARGS="--allow-no-lemmas"
    export CRAWL_EXTRA_ARGS
    local key; key=$(sha256sum "$f" | cut -d' ' -f1)
    local hs_manifest="$CACHE/$key.hs.json"
    local wd; wd=$(mktemp -d)
    mkdir -p "$wd/thy"; cp "$f" "$wd/thy/"
    # Sibling oracle scripts: `heuristic: o "./oracle-…"` resolves relative
    # to the server's theory dir on both engines (upstream's deforacle
    # recipe) — stage them next to the theory or oracle rankings fail.
    local __of
    for __of in "$(dirname "$f")"/oracle*; do
        [ -f "$__of" ] && cp "$__of" "$wd/thy/"
    done

    # Phase 1: HS (cached)
    if [ ! -f "$hs_manifest" ]; then
        if ! MAUDE_PATH="$MAUDE_PATH" boot_crawl "$HS_PATH" "$HS_PORT" "$wd" "$hs_manifest" hs; then
            rm -f "$hs_manifest"; rm -rf "$wd"
            printf '%s\t-\tSKIP_HS_FAIL\t-\t-\t-\n' "$rel"; return 0
        fi
    fi
    # Phase 2: RS
    local rs_manifest="$wd/rs.json"
    if ! boot_crawl "$RS_PATH" "$RS_PORT" "$wd" "$rs_manifest" rs; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_RS_FAIL\t-\t-\t-\n' "$rel"; return 0
    fi
    # diff
    python3 "$script_dir/web_diff.py" "$hs_manifest" "$rs_manifest" \
        "$wd/parity.tsv" "$DIFFDIR/$rel" >/dev/null 2>&1
    # prefix each row with the file
    awk -F'\t' -v r="$rel" '{print r"\t"$0}' "$wd/parity.tsv"
    rm -rf "$wd"
}

echo "web_parity: HS=$HS_PATH" >&2
echo "web_parity: RS=$RS_PATH  maude=$MAUDE_PATH" >&2
: > "$RESULTS_TSV"
N=$(filelist | grep -c .)
i=0
while IFS= read -r rel; do
    [ -n "$rel" ] || continue
    i=$((i+1)); echo "[$i/$N] $rel" >&2
    one_file "$rel" >> "$RESULTS_TSV"
done < <(filelist | grep .)

echo "=== SUMMARY ===" >&2
awk -F'\t' '{c[$3]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$RESULTS_TSV" >&2
echo "  files: $N   results: $RESULTS_TSV   diffs: $DIFFDIR" >&2
echo "DONE_WEB_PARITY" >&2
