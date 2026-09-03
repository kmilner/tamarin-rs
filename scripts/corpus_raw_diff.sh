#!/bin/bash
# Diff the RAW (uncanonicalised) `--prove` stdout of the Haskell prover vs the
# Rust BINARY (not the dump_proof example) for every lemma across the corpus.
#
# This is the strict end-state comparison: full rendered theory + proof +
# summary, byte-for-byte, with ONLY the inherently environment-dependent lines
# stripped (Git revision / Compiled at / processing time). No canonicalisation,
# no lemma slicing. Anything else that differs is a rendering or proof-search
# divergence to fix.
#
# HS results are cached as paired RAW stdout and exit status
# (<key>.full.gz + <key>.rc) in the cache shared with diff_proof_raw.sh. Only
# cap-bearing timeout markers written by the current harness are honoured;
# incomplete result pairs and ambiguous legacy markers are retried.
#
# Usage:
#   corpus_raw_diff.sh                 # smaller corpus (pre-expansion 17-dir list)
#   corpus_raw_diff.sh --all           # whole examples/ tree
#   corpus_raw_diff.sh file1 [file2..] # only the given .spthy files
#
# Env: TIMEOUT (HS-side cap, default 120), RS_TIMEOUT (RS-side cap, default 30),
#      JOBS (default nproc), EXTRA_ENV (RS env vars),
#      HS_CANON_CACHE, NO_HS_CACHE=1, CACHE_VERSION, CORPUS_ROOT,
#      RESULTS_TSV (persisted per-lemma TSV, default /tmp/corpus_raw_diff_results.tsv).
#
# The two caps are split on purpose (run-3 sweep data, 2026-06-11, 644 RS runs):
# the HS side has a real 30-300s band on uncached runs but is a one-time cached
# cost, so it keeps the high cap; the RS side is paid on EVERY sweep and its
# distribution has a knee at 30s (RS_TIMEOUT=30 keeps 193/201 MATCH + 251/281
# DIFF at ~18min wall vs ~104min at 300s; 30->60s buys only 2 more lemmas).
# The lost tail is the known slow noise/jcs18/SAPIC families - reverify those
# manually with RS_TIMEOUT=300 when working on them.
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
# Shared gate plumbing (gate_common.sh): OOM prologue, strip_env_lines, the
# oracle fingerprint recipe the cache key carries.
[ -r "$script_dir/gate_common.sh" ] || { echo "corpus_raw_diff: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
[ -r "$script_dir/proof_diff_common.sh" ] || { echo "corpus_raw_diff: missing proof_diff_common.sh" >&2; exit 2; }
. "$script_dir/proof_diff_common.sh"
# OOM discipline: every prover child inherits the cap and dies alone.
oom_prologue

TIMEOUT="${TIMEOUT:-120}"
RS_TIMEOUT="${RS_TIMEOUT:-30}"
JOBS="${JOBS:-$(nproc)}"
EXTRA_ENV="${EXTRA_ENV:-}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE_VERSION="${CACHE_VERSION:-1}"
# Deriv-check timeout (secs) passed to BOTH binaries so the message-derivation
# section compares deterministically.  HS default 5s fires on heavy theories
# (records a "Derivation checks timed out" placeholder) while RS computes fully
# — a spurious DIFF.  30s lets both compute fully (deriv-check verified faithful).
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"
HS_CANON_CACHE="${HS_CANON_CACHE:-$(shared_cache_dir "$repo_root" raw "$script_dir/.hs_canon_cache")}" || exit 2
NO_HS_CACHE="${NO_HS_CACHE:-}"
# HS RTS flags. Upstream commit 00a282da ("Canonicalise maude's returned
# substitution entries", Maude/Types.hs:134) made HS proofs schedule-
# INDEPENDENT — `+RTS -Nk` for any k now yields byte-identical proofs. So
# the cache can be (re)generated with PARALLEL HS instead of forced -N1,
# which is much faster for individually-slow lemmas. HS_RTS defaults to
# `-N$HS_N` cores per HS run; with JOBS lemmas in flight the product
# HS_N*JOBS should stay near nproc to avoid oversubscription.
HS_N="${HS_N:-4}"
HS_RTS="${HS_RTS:--N$HS_N}"
[ -n "$NO_HS_CACHE" ] || mkdir -p "$HS_CANON_CACHE" 2>/dev/null || true

hs_path=$(resolve_hs_oracle "$repo_root") || exit 2

# --- Build + locate the RS binary (the real prover, not the dump_proof example).
# `tamarin-prover` is the PACKAGE; its only bin target is `tamarin-rs`, so
# --bin tamarin-prover selects nothing and cargo errors out.
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    if ! cargo build --release -p tamarin-prover \
            --manifest-path "$repo_root/Cargo.toml" >&2; then
        echo "corpus_raw_diff.sh: cargo build -p tamarin-prover failed" >&2
        exit 2
    fi
fi
rs_path="$repo_root/target/release/tamarin-rs"
if [ ! -x "$rs_path" ]; then
    echo "corpus_raw_diff.sh: RS binary not built at $rs_path" >&2
    exit 2
fi
rs_stale_check "$rs_path" "$repo_root"

# --- Cache key: identical to diff_proof_raw.sh's flagless form. It carries the
# oracle and execution fingerprints, so a rebuilt oracle, changed Maude or
# derivation timeout is a MISS rather than a stale hit.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"
oracle_rev_check "$hs_path" "$MAUDE" "$repo_root"
execution_fingerprint "$MAUDE" "$DERIVCHECK_TIMEOUT" || exit 2

# --- strip_env_lines (gate_common.sh): delete the only lines that
# legitimately differ between the two binaries, keeping `analyzed:` visible
# (the cache hit rewrites its path to this invocation's).
export -f file_sha256 proof_now_ms proof_cache_key proof_cache_result proof_lemmas_of parser_input_manifest \
    manifest_encode manifest_normalize manifest_decode_into input_manifest _include_shas_from_manifest _oracle_shas_from_manifest \
    input_content_key strip_env_lines cache_entry_lock cache_entry_unlock \
    cache_publish_text cache_publish_gzip cache_publish_proof cache_gzip_valid binary_sha256 \
    binary_identity_unchanged execution_identity_unchanged \
    producer_identity_unchanged rs_identity_unchanged comparison_identity_unchanged \
    duration_seconds
export HS_PATH="$hs_path" RS_PATH="$rs_path" TIMEOUT RS_TIMEOUT EXTRA_ENV \
       HS_CANON_CACHE CACHE_VERSION NO_HS_CACHE DERIVCHECK_TIMEOUT HS_RTS \
       HS_FP HS_FP_PATH HS_FP_SALT EXEC_FP_SALT MAUDE_FP MAUDE_FP_PATH MAUDE GATE_COMMON_DIR

# --- Per-lemma worker. Emits ONE machine-parseable line:
#       <file>\t<lemma>\t<status>\t<hs_lines>\t<rs_lines>\t<diff>\t<hs_ms>\t<rs_ms>
worker() {
    local f="$1" lemma="$2" cache_template="$3"
    local tmp; tmp="$(mktemp -d)"
    # shellcheck disable=SC2064
    trap "rm -rf '$tmp'" RETURN

    local hs_out="$tmp/hs.out" hs_rc=0 hs_ms="-" hs_ready=0
    local key="" key_full="" key_rc="" key_timeout="" lock_fd=""
    if [ "$cache_template" = "!" ]; then
        printf '%s\t%s\tSKIP_INPUT_MANIFEST\t0\t0\t-\t-\t-\n' "$f" "$lemma"
        return 0
    fi
    local cache_id=${cache_template/__LEMMA__/$lemma}
    if [ -z "$NO_HS_CACHE" ]; then
        key="$HS_CANON_CACHE/$cache_id.canon"
        key_full="${key%.canon}.full.gz"
        key_rc="${key%.canon}.rc"
        key_timeout="${key%.canon}.timeout"
        cache_entry_lock "$HS_CANON_CACHE" "$cache_id" lock_fd || {
            printf '%s\t%s\tSKIP_CACHE_LOCK\t0\t0\t-\t-\t-\n' "$f" "$lemma"
            return 0
        }
    fi
    if [ -n "$key" ] && [ -f "$key_timeout" ]; then
        local old_cap old_seconds current_seconds
        old_cap=$(cat "$key_timeout")
        case "$old_cap" in timeout:*) old_cap=${old_cap#timeout:};; *) old_cap=;; esac
        old_seconds=$(duration_seconds "$old_cap") || old_seconds=
        current_seconds=$(duration_seconds "$TIMEOUT") || current_seconds=
        if [ -n "$old_seconds" ] && [ -n "$current_seconds" ] \
                && [ "$old_seconds" -ge "$current_seconds" ]; then
            hs_rc=124
            hs_ready=1
            : > "$hs_out"
        else
            rm -f "$key_timeout"
        fi
    fi
    if [ "$hs_ready" -eq 0 ] && [ -n "$key" ] \
            && proof_cache_result "$key_rc" "$key_full" hs_rc; then
        gzip -dc "$key_full" 2>/dev/null \
            | awk -v f="$f" '/^analyzed: / { print "analyzed: " f; next } { print }' \
            > "$hs_out"
        hs_ready=1
    elif [ "$hs_ready" -eq 0 ]; then
        # A payload without status is a legacy partial result, not a cache hit.
        [ -z "$key" ] || rm -f "$key_full" "$key_rc"
        local hs_t0; hs_t0=$(proof_now_ms)
        timeout "$TIMEOUT" "$HS_PATH" +RTS $HS_RTS -RTS --with-maude="$MAUDE" --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove="$lemma" "$f" 2>/dev/null > "$hs_out"
        hs_rc=$?
        hs_ms=$(( $(proof_now_ms) - hs_t0 ))
        if [ -n "$key" ]; then
            local checked_id
            if ! checked_id=$(proof_cache_key "$f" "$lemma") \
                    || [ "$checked_id" != "$cache_id" ] \
                    || ! producer_identity_unchanged; then
                cache_entry_unlock "$lock_fd"
                printf '%s\t%s\tSKIP_INPUT_CHANGED\t0\t0\t-\t%s\t-\n' "$f" "$lemma" "$hs_ms"
                return 0
            fi
            # timeout's reserved status range includes both its own 124 and
            # signal deaths (for example OOM's 137): never cache their partial
            # stdout.
            if [ "$hs_rc" -eq 124 ]; then
                cache_publish_text "$key_timeout" "timeout:${TIMEOUT}" 2>/dev/null || true
            elif [ "$hs_rc" -lt 124 ]; then
                cache_publish_proof "$key_rc" "$key_full" "$hs_rc" "$hs_out" 2>/dev/null || true
            fi
        fi
    fi
    [ -z "$lock_fd" ] || cache_entry_unlock "$lock_fd"

    # HS timed out or was signal-killed (cached timeout or live run): the
    # comparison is void, so do NOT run RS at all. The lemmas where HS times
    # out are exactly the jcs18-class monsters where RS's 300s of unbounded
    # search OOMs the machine (observed 17-43 GB RSS per worker, 2026-06-10).
    if [ "$hs_rc" -ge 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "0" "0" "-" "$hs_ms" "-"
        return 0
    fi

    local rs_t0; rs_t0=$(proof_now_ms)
    timeout "$RS_TIMEOUT" env $EXTRA_ENV "$RS_PATH" --with-maude="$MAUDE" --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove="$lemma" "$f" 2>/dev/null > "$tmp/rs.out"
    local rs_rc=$?
    local rs_ms=$(( $(proof_now_ms) - rs_t0 ))

    if ! checked_id=$(proof_cache_key "$f" "$lemma") \
            || [ "$checked_id" != "$cache_id" ] \
            || ! comparison_identity_unchanged; then
        printf '%s\t%s\tSKIP_INPUT_CHANGED\t0\t0\t-\t%s\t%s\n' \
            "$f" "$lemma" "$hs_ms" "$rs_ms"
        return 0
    fi

    strip_env_lines "$hs_out"    > "$tmp/hs.cmp"
    strip_env_lines "$tmp/rs.out" > "$tmp/rs.cmp"

    local hs_lines rs_lines d
    hs_lines=$(grep -c . "$tmp/hs.cmp"); hs_lines=${hs_lines// /}
    rs_lines=$(grep -c . "$tmp/rs.cmp"); rs_lines=${rs_lines// /}

    if [ "$hs_rc" -ge 124 ] || [ "$rs_rc" -ge 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$hs_rc" -ne "$rs_rc" ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "RC_DIFF" "$hs_lines" "$rs_lines" "$hs_rc/$rs_rc" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$hs_rc" -eq 0 ] && [ "$hs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_NO_HS" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$rs_rc" -eq 0 ] && [ "$rs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_RS_ERR" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi

    d=$(diff "$tmp/hs.cmp" "$tmp/rs.cmp" 2>/dev/null | wc -l); d=${d// /}
    if [ "$d" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "MATCH" "$hs_lines" "$rs_lines" "0" "$hs_ms" "$rs_ms"
    else
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "DIFF" "$hs_lines" "$rs_lines" "$d" "$hs_ms" "$rs_ms"
    fi
    return 0
}
export -f worker

# --- File-content filter.
file_is_comparable() {
    local f="$1"
    grep -q 'diff('       "$f" 2>/dev/null && return 1
    grep -q 'predicates:' "$f" 2>/dev/null && return 1
    grep -q 'process:'    "$f" 2>/dev/null && return 1
    return 0
}

# --- Candidate files. Default: the SMALLER pre-expansion corpus (17-dir
#     allowlist that produced the 2026-06 canon baselines); --all: whole tree.
declare -a files=()
case "${1:-}" in
    --all)
        while IFS= read -r cand; do
            case "$cand" in */testParser/include/*) continue;; esac
            files+=("$cand")
        done < <(find "$CORPUS_ROOT" -name '*.spthy' 2>/dev/null | sort)
        ;;
    "" )
        target_dirs=(loops csf23-subterms experiments regression ccs15 classic \
                     features related_work post17 cav13 jcs18 csf18-alethea \
                     csf17 csf12 testParser ake sp14)
        for dir in "${target_dirs[@]}"; do
            dpath="$CORPUS_ROOT/$dir"
            [ -d "$dpath" ] || continue
            while IFS= read -r cand; do
                case "$cand" in */testParser/include/*) continue;; esac
                files+=("$cand")
            done < <(find "$dpath" -maxdepth 2 -name '*.spthy' 2>/dev/null | sort)
        done
        ;;
    *)
        for cand in "$@"; do [ -f "$cand" ] && files+=("$cand"); done
        ;;
esac

tasklist="$(mktemp)"
filtered_files=0
total_files=0
for f in "${files[@]}"; do
    total_files=$((total_files+1))
    if ! file_is_comparable "$f"; then
        filtered_files=$((filtered_files+1))
        continue
    fi
    if ! cache_template=$(proof_cache_key "$f" "__LEMMA__"); then
        cache_template="!"
    fi
    while IFS= read -r lem; do
        [ -n "$lem" ] && printf '%s\t%s\t%s\n' \
            "$f" "$lem" "$cache_template" >> "$tasklist"
    done < <(proof_lemmas_of "$f")
done

n_tasks=$(wc -l < "$tasklist"); n_tasks=${n_tasks// /}
echo "# corpus_raw_diff: $n_tasks lemmas across $((total_files-filtered_files)) files (filtered out $filtered_files of $total_files), JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, RS_TIMEOUT=${RS_TIMEOUT}s, HS-cache=$([ -n "$NO_HS_CACHE" ] && echo off || echo "$HS_CANON_CACHE")" >&2

results="$(mktemp)"
trap "rm -f '$tasklist' '$results'" EXIT
tr '\t' '\n' < "$tasklist" | xargs -d '\n' -P "$JOBS" -n 3 bash -c 'worker "$0" "$1" "$2"' > "$results"

sort -t$'\t' -k1,1 -k2,2 "$results" > "$results.sorted"

# Persist the raw per-lemma TSV (path lemma status hs_lines rs_lines diff
# hs_ms rs_ms) - it carries the timing data the summary only aggregates.
RESULTS_TSV="${RESULTS_TSV:-/tmp/corpus_raw_diff_results.tsv}"
cp "$results.sorted" "$RESULTS_TSV" 2>/dev/null || true
echo "# per-lemma results: $RESULTS_TSV" >&2

match=0; diffn=0; rc_diff=0; skip_no_hs=0; skip_rs_err=0; skip_timeout=0
declare -a divergent=() rs_times=() hs_times=()
declare -a rs_slow=() hs_slow=()
while IFS=$'\t' read -r f lem status hs rs d hs_ms rs_ms; do
    hs_ms="${hs_ms:--}"; rs_ms="${rs_ms:--}"
    if [ "$hs_ms" = "-" ]; then t=" [hs:cache rs:${rs_ms}ms]"; else t=" [hs:${hs_ms}ms rs:${rs_ms}ms]"; fi
    case "$status" in
        MATCH)        match=$((match+1));        echo "$f::$lem: MATCH (HS:$hs, RS:$rs)$t";;
        DIFF)         diffn=$((diffn+1));         echo "$f::$lem: $d diff lines (HS:$hs, RS:$rs)$t"; divergent+=("$d"$'\t'"$f::$lem (HS:$hs, RS:$rs)");;
        RC_DIFF)      rc_diff=$((rc_diff+1));      echo "$f::$lem: RC_DIFF $d (HS:$hs, RS:$rs)$t";;
        SKIP_NO_HS)   skip_no_hs=$((skip_no_hs+1));   echo "$f::$lem: SKIP (no HS output)$t";;
        SKIP_INPUT_MANIFEST) skip_no_hs=$((skip_no_hs+1)); echo "$f::$lem: SKIP (input manifest failed)$t";;
        SKIP_RS_ERR)  skip_rs_err=$((skip_rs_err+1)); echo "$f::$lem: SKIP (RS produced no output; HS:$hs)$t";;
        SKIP_TIMEOUT) skip_timeout=$((skip_timeout+1)); echo "$f::$lem: SKIP (timeout HS:${TIMEOUT}s/RS:${RS_TIMEOUT}s)$t";;
        *)            echo "$f::$lem: SKIP (unknown status '$status')"; skip_no_hs=$((skip_no_hs+1));;
    esac
    if [ "$rs_ms" != "-" ]; then
        rs_times+=("$rs_ms"); rs_slow+=("$rs_ms"$'\t'"$status"$'\t'"$f::$lem")
    fi
    if [ "$hs_ms" != "-" ]; then
        hs_times+=("$hs_ms"); hs_slow+=("$hs_ms"$'\t'"$status"$'\t'"$f::$lem")
    fi
done < "$results.sorted"
rm -f "$results.sorted"

pctl() {
    local n; n=$(wc -l < "$2"); [ "$n" -eq 0 ] && { echo "-"; return; }
    local i=$(( (n * $1 + 99) / 100 )); [ "$i" -lt 1 ] && i=1
    sed -n "${i}p" "$2"
}
print_timing() {
    local -n times_ref=$2 slow_ref=$3
    local n=${#times_ref[@]}
    if [ "$n" -eq 0 ]; then echo "$1: no timed runs"; return; fi
    local sorted; sorted="$(mktemp)"
    printf '%s\n' "${times_ref[@]}" | sort -n > "$sorted"
    echo "$1 ($n timed runs, ms): p50=$(pctl 50 "$sorted") p90=$(pctl 90 "$sorted") p99=$(pctl 99 "$sorted") max=$(pctl 100 "$sorted")"
    echo "  slowest:"
    printf '%s\n' "${slow_ref[@]}" | sort -t$'\t' -k1,1nr | head -10 | \
        awk -F'\t' '{printf "    %8dms  %-12s %s\n", $1, $2, $3}'
    rm -f "$sorted"
}

total=$((match+diffn+rc_diff+skip_no_hs+skip_rs_err+skip_timeout))
echo ""
echo "================ SUMMARY ================"
echo "total lemmas enumerated : $total"
echo "  0 diff (MATCH)        : $match"
echo "  divergent (DIFF)      : $diffn"
echo "  status mismatch       : $rc_diff"
echo "  skipped               : $((skip_no_hs+skip_rs_err+skip_timeout))"
echo "      no HS output      : $skip_no_hs"
echo "      RS no output/err  : $skip_rs_err"
echo "      timeout (HS ${TIMEOUT}s / RS ${RS_TIMEOUT}s) : $skip_timeout"
if [ "${#divergent[@]}" -gt 0 ]; then
    echo ""
    echo "divergent lemmas (largest diff first):"
    printf '%s\n' "${divergent[@]}" | sort -t$'\t' -k1,1nr | sed 's/^/  /; s/\t/ diff lines: /'
fi
echo ""
echo "================ TIMING ================"
print_timing "RS" rs_times rs_slow
print_timing "HS (uncached only)" hs_times hs_slow
