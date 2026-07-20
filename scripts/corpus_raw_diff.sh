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
# HS results are cached as RAW gzipped stdout (<key>.full.gz) in the same cache
# dir as corpus_full_trace_diff.sh, with the same key scheme — one HS run feeds
# both the canon and the raw comparison. Existing <key>.timeout markers are
# honoured.
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
HS_CANON_CACHE="${HS_CANON_CACHE:-$script_dir/.hs_canon_cache}"
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

# --- Locate the HS binary (same discovery as corpus_full_trace_diff.sh).
find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        if [ -x "$c" ]; then echo "$c"; return 0; fi
    done
    return 1
}
hs_path="$(find_hs_bin "$repo_root" 2>/dev/null || true)"
if [ -z "$hs_path" ]; then
    main_root="$(git -C "$repo_root" worktree list --porcelain 2>/dev/null | awk '/^worktree/{print $2; exit}')"
    if [ -n "$main_root" ] && [ "$main_root" != "$repo_root" ]; then
        hs_path="$(find_hs_bin "$main_root" 2>/dev/null || true)"
    fi
fi
if [ -z "$hs_path" ]; then
    hs_path="$(command -v tamarin-prover 2>/dev/null || true)"
fi
if [ -z "$hs_path" ]; then
    echo "corpus_raw_diff.sh: no HS tamarin-prover binary found" >&2
    exit 2
fi

# --- Build + locate the RS binary (the real prover, not the dump_proof example).
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    if ! cargo build --release --bin tamarin-prover \
            --manifest-path "$repo_root/Cargo.toml" >&2; then
        echo "corpus_raw_diff.sh: cargo build --bin tamarin-prover failed" >&2
        exit 2
    fi
fi
rs_path="$repo_root/target/release/tamarin-rs"
if [ ! -x "$rs_path" ]; then
    echo "corpus_raw_diff.sh: RS binary not built at $rs_path" >&2
    exit 2
fi

# --- Cache key: identical scheme to corpus_full_trace_diff.sh.
hs_cache_key() {
    local f="$1" lemma="$2" h
    h=$(sha256sum "$f" 2>/dev/null | cut -d' ' -f1)
    printf '%s__%s__v%s.canon' "$h" "$lemma" "$CACHE_VERSION"
}

# --- Lemma enumeration (same comment-stripping awk as corpus_full_trace_diff.sh).
lemmas_of() {
    awk '
        BEGIN { depth = 0 }
        {
            line = $0
            while (length(line) > 0) {
                if (depth > 0) {
                    o = index(line, "/*")
                    c = index(line, "*/")
                    if (c == 0 && o == 0) { line = ""; break }
                    if (o > 0 && (c == 0 || o < c)) {
                        depth++; line = substr(line, o + 2)
                    } else {
                        depth--; line = substr(line, c + 2)
                    }
                } else {
                    lc = index(line, "//")
                    bc = index(line, "/*")
                    if (lc > 0 && (bc == 0 || lc < bc)) {
                        print substr(line, 1, lc - 1); line = ""; break
                    }
                    if (bc > 0) {
                        print substr(line, 1, bc - 1)
                        depth++; line = substr(line, bc + 2)
                    } else {
                        print line; line = ""; break
                    }
                }
            }
        }
    ' "$1" 2>/dev/null \
        | grep '^lemma ' \
        | sed -E 's/^lemma[[:space:]]+([A-Za-z0-9_]+).*/\1/'
}

# --- Strip the only lines that legitimately differ between the two binaries.
strip_env_lines() {
    grep -v -e '^Git revision:' -e '^Compiled at:' -e '^[[:space:]]*processing time:' "$1"
}
export -f hs_cache_key lemmas_of strip_env_lines
export HS_PATH="$hs_path" RS_PATH="$rs_path" TIMEOUT RS_TIMEOUT EXTRA_ENV \
       HS_CANON_CACHE CACHE_VERSION NO_HS_CACHE DERIVCHECK_TIMEOUT HS_RTS

# --- Per-lemma worker. Emits ONE machine-parseable line:
#       <file>\t<lemma>\t<status>\t<hs_lines>\t<rs_lines>\t<diff>\t<hs_ms>\t<rs_ms>
worker() {
    local f="$1" lemma="$2"
    local tmp; tmp="$(mktemp -d)"
    # shellcheck disable=SC2064
    trap "rm -rf '$tmp'" RETURN

    local hs_out="$tmp/hs.out" hs_rc=0 hs_ms="-"
    local key="" key_full="" key_timeout=""
    if [ -z "$NO_HS_CACHE" ]; then
        key="$HS_CANON_CACHE/$(hs_cache_key "$f" "$lemma")"
        key_full="${key%.canon}.full.gz"
        key_timeout="${key%.canon}.timeout"
    fi
    if [ -n "$key" ] && [ -f "$key_timeout" ]; then
        hs_rc=124
        : > "$hs_out"
    elif [ -n "$key" ] && [ -f "$key_full" ]; then
        # Content-keyed cache: rewrite the path-echoing "analyzed:" line to
        # THIS invocation's path (a hit recorded from another checkout/worktree
        # would otherwise produce a spurious path-only diff).
        gzip -dc "$key_full" 2>/dev/null \
            | awk -v f="$f" '/^analyzed: / { print "analyzed: " f; next } { print }' \
            > "$hs_out"
    else
        local hs_t0; hs_t0=$(date +%s%3N)
        timeout "$TIMEOUT" "$HS_PATH" +RTS $HS_RTS -RTS --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove="$lemma" "$f" 2>/dev/null > "$hs_out"
        hs_rc=$?
        hs_ms=$(( $(date +%s%3N) - hs_t0 ))
        if [ -n "$key" ]; then
            if [ "$hs_rc" -eq 124 ]; then
                : > "$key_timeout" 2>/dev/null || true
            elif [ -s "$hs_out" ]; then
                # Never cache EMPTY HS output: empty means HS failed to start
                # (missing maude on PATH, unset LANG, OOM, ...) and caching it
                # poisons every later sweep (642 entries on 2026-06-11).
                # Leave uncached so the lemma is retried next run.
                gzip -c "$hs_out" > "$key_full" 2>/dev/null || true
            fi
        fi
    fi

    # HS timed out (cached marker or live run): the comparison is void, so do
    # NOT run RS at all. The lemmas where HS times out are exactly the
    # jcs18-class monsters where RS's 300s of unbounded search OOMs the
    # machine (observed 17-43 GB RSS per worker, 2026-06-10).
    if [ "$hs_rc" -eq 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "0" "0" "-" "$hs_ms" "-"
        return 0
    fi

    local rs_t0; rs_t0=$(date +%s%3N)
    timeout "$RS_TIMEOUT" env $EXTRA_ENV "$RS_PATH" --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove="$lemma" "$f" 2>/dev/null > "$tmp/rs.out"
    local rs_rc=$?
    local rs_ms=$(( $(date +%s%3N) - rs_t0 ))

    strip_env_lines "$hs_out"    > "$tmp/hs.cmp"
    strip_env_lines "$tmp/rs.out" > "$tmp/rs.cmp"

    local hs_lines rs_lines d
    hs_lines=$(grep -c . "$tmp/hs.cmp"); hs_lines=${hs_lines// /}
    rs_lines=$(grep -c . "$tmp/rs.cmp"); rs_lines=${rs_lines// /}

    if [ "$hs_rc" -eq 124 ] || [ "$rs_rc" -eq 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$hs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_NO_HS" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$rs_lines" -eq 0 ]; then
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

# --- File-content filter (same as corpus_full_trace_diff.sh).
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
    while IFS= read -r lem; do
        [ -n "$lem" ] && printf '%s\t%s\n' "$f" "$lem" >> "$tasklist"
    done < <(lemmas_of "$f")
done

n_tasks=$(wc -l < "$tasklist"); n_tasks=${n_tasks// /}
echo "# corpus_raw_diff: $n_tasks lemmas across $((total_files-filtered_files)) files (filtered out $filtered_files of $total_files), JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, RS_TIMEOUT=${RS_TIMEOUT}s, HS-cache=$([ -n "$NO_HS_CACHE" ] && echo off || echo "$HS_CANON_CACHE")" >&2

results="$(mktemp)"
trap "rm -f '$tasklist' '$results'" EXIT
tr '\t' '\n' < "$tasklist" | xargs -d '\n' -P "$JOBS" -n 2 bash -c 'worker "$0" "$1"' > "$results"

sort -t$'\t' -k1,1 -k2,2 "$results" > "$results.sorted"

# Persist the raw per-lemma TSV (path lemma status hs_lines rs_lines diff
# hs_ms rs_ms) - it carries the timing data the summary only aggregates.
RESULTS_TSV="${RESULTS_TSV:-/tmp/corpus_raw_diff_results.tsv}"
cp "$results.sorted" "$RESULTS_TSV" 2>/dev/null || true
echo "# per-lemma results: $RESULTS_TSV" >&2

match=0; diffn=0; skip_no_hs=0; skip_rs_err=0; skip_timeout=0
declare -a divergent=() rs_times=() hs_times=()
declare -a rs_slow=() hs_slow=()
while IFS=$'\t' read -r f lem status hs rs d hs_ms rs_ms; do
    hs_ms="${hs_ms:--}"; rs_ms="${rs_ms:--}"
    if [ "$hs_ms" = "-" ]; then t=" [hs:cache rs:${rs_ms}ms]"; else t=" [hs:${hs_ms}ms rs:${rs_ms}ms]"; fi
    case "$status" in
        MATCH)        match=$((match+1));        echo "$f::$lem: MATCH (HS:$hs, RS:$rs)$t";;
        DIFF)         diffn=$((diffn+1));         echo "$f::$lem: $d diff lines (HS:$hs, RS:$rs)$t"; divergent+=("$d"$'\t'"$f::$lem (HS:$hs, RS:$rs)");;
        SKIP_NO_HS)   skip_no_hs=$((skip_no_hs+1));   echo "$f::$lem: SKIP (no HS output)$t";;
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

total=$((match+diffn+skip_no_hs+skip_rs_err+skip_timeout))
echo ""
echo "================ SUMMARY ================"
echo "total lemmas enumerated : $total"
echo "  0 diff (MATCH)        : $match"
echo "  divergent (DIFF)      : $diffn"
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
