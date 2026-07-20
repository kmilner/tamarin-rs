#!/usr/bin/env bash
# Full-FILE raw diff of HS vs RS `--prove <file>` (proves ALL lemmas in the
# file in one invocation — truest byte-identical metric, avoids per-lemma
# source recompute).
#
# Two strictly-sequential phases so HS and RS never contend:
#   Phase 1 (HS): run HS on every allowlisted file, cache stripped stdout by
#                 sha256(content) under .hs_file_cache/.  JOBS concurrent,
#                 -N$HS_N cores each.  Timeout → .timeout marker; empty/no
#                 output (diff theory / include fragment / error) → .nohs.
#   Phase 2 (RS): run RS on every file, diff against the cached HS output.
#
# Env: FILE_TIMEOUT (per-file cap both sides, default 300s), JOBS (4),
#      HS_N (RTS cores/HS, 4), HS_MAXHEAP (GHC -M g, 11), DERIVCHECK_TIMEOUT
#      (30), CORPUS_ROOT, RESULTS_TSV, ALLOWLIST (file with one rel-path per
#      line; default = derive from $PREV_TSV column 1).
# Output TSV (5 col, tab-sep): relpath  status  HS_lines  RS_lines  diffcount
#   status ∈ MATCH | DIFF | SKIP_HS_TIMEOUT | SKIP_NO_HS | SKIP_RS_TIMEOUT
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"

FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
JOBS="${JOBS:-4}"
HS_N="${HS_N:-4}"
HS_MAXHEAP="${HS_MAXHEAP:-11}"
HS_RTS="${HS_RTS:--N$HS_N -M${HS_MAXHEAP}g}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE="${CACHE:-$script_dir/.hs_file_cache}"
RESULTS_TSV="${RESULTS_TSV:-/tmp/corpus_file_diff.tsv}"
PREV_TSV="${PREV_TSV:-/tmp/corpus_file_diff.PREV.tsv}"
ALLOWLIST="${ALLOWLIST:-}"
mkdir -p "$CACHE"

find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin "$repo_root")}" || { echo "no HS binary" >&2; exit 2; }
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
export HS_PATH RS_PATH FILE_TIMEOUT DERIVCHECK_TIMEOUT HS_RTS CACHE CORPUS_ROOT

# Strip the volatile header lines from a tamarin run (Git rev / Compiled at /
# processing time / analyzed-path).  Stripping `analyzed:` on BOTH sides means
# no cache path-rewrite is needed.
strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
export -f strip_env

# --- per-file canonical flags (see file_flags.tsv) ---------------------------
# flags_for echoes the extra HS/RS flags for a relpath (empty if none).
# ckey salts the content-hash with a flags hash, so a flagged entry is a
# DISTINCT cache key from the bare one; flagless files keep the plain
# content-hash key → existing bare cache is untouched.
# Special token `@cd`: not a prover flag — run the prover from the file's
# OWN directory with the bare filename (upstream's deforacle recipe,
# Makefile:199-201: default-oracle lookup is cwd-relative). Stripped from
# the flag list before invocation; still salts the cache key.
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
export FLAGS_MAP
flags_for() {
    [ -f "$FLAGS_MAP" ] || return 0
    awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"
}
export -f flags_for
ckey() {  # <relpath> <abs-file>
    local h fl; h=$(sha256sum "$2" | cut -d' ' -f1); fl=$(flags_for "$1")
    if [ -n "$fl" ]; then
        printf '%s__f%s' "$h" "$(printf '%s' "$fl" | sha256sum | cut -c1-12)"
    else
        printf '%s' "$h"
    fi
}
export -f ckey

# --- file list (allowlist) ---
# Precedence: explicit ALLOWLIST env > committed canonical corpus
# (scripts/parity_corpus.txt) > derive from PREV_TSV.
filelist() {
    if [ -n "$ALLOWLIST" ] && [ -f "$ALLOWLIST" ]; then
        cat "$ALLOWLIST"
    elif [ -f "$script_dir/parity_corpus.txt" ]; then
        cat "$script_dir/parity_corpus.txt"
    elif [ -f "$PREV_TSV" ]; then
        cut -f1 "$PREV_TSV"
    else
        echo "no ALLOWLIST, no $script_dir/parity_corpus.txt, no $PREV_TSV to derive from" >&2; exit 2
    fi
}

# --- Phase 1: HS ---
hs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key out rc fl
    [ -f "$f" ] || return 0
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$CACHE/$key.full.gz" ] && return 0
    [ -f "$CACHE/$key.timeout" ] && return 0
    [ -f "$CACHE/$key.nohs" ] && return 0
    # Record the flags this entry was generated with, so the cache is
    # self-documenting (we don't "lose track" of what each file needs).
    # Only for flagged files — flagless entries stay clutter-free.
    [ -n "$fl" ] && printf '%s' "$fl" > "$CACHE/$key.flags"
    # Run HS to a temp file so we capture `timeout`'s OWN exit code (124 on
    # timeout) — piping straight into strip_env would make $? reflect grep's
    # exit, misclassifying timeouts as empty (SKIP_NO_HS).
    # `@cd` token: run from the file's directory with the bare filename.
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then
        fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f")
    fi
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$HS_PATH" +RTS $HS_RTS -RTS \
            $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$farg" ) >"$tmp" 2>/dev/null
    rc=$?
    out=$(strip_env < "$tmp"); rm -f "$tmp"
    if [ "$rc" = "124" ]; then
        touch "$CACHE/$key.timeout"; echo "  HS TIMEOUT  $rel" >&2
    elif [ -z "$out" ]; then
        touch "$CACHE/$key.nohs"; echo "  HS EMPTY!   $rel${fl:+  (flags: $fl)}" >&2
    else
        printf '%s' "$out" | gzip > "$CACHE/$key.full.gz"
    fi
}
export -f hs_one

# --- Phase 2: RS + diff ---
rs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key hs rs d rc fl
    [ -f "$f" ] || { printf '%s\tSKIP_NO_HS\t0\t0\t0\n' "$rel"; return 0; }
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    if [ -f "$CACHE/$key.timeout" ]; then printf '%s\tSKIP_HS_TIMEOUT\t0\t0\t0\n' "$rel"; return 0; fi
    if [ ! -f "$CACHE/$key.full.gz" ]; then printf '%s\tSKIP_NO_HS\t0\t0\t0\n' "$rel"; return 0; fi
    # `@cd` token: run from the file's directory with the bare filename.
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then
        fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f")
    fi
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$RS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$farg" ) >"$tmp" 2>/dev/null
    rc=$?
    rs=$(strip_env < "$tmp"); rm -f "$tmp"
    if [ "$rc" = "124" ]; then printf '%s\tSKIP_RS_TIMEOUT\t0\t0\t0\n' "$rel"; return 0; fi
    hs=$(zcat "$CACHE/$key.full.gz")
    local hsn rsn
    hsn=$(printf '%s\n' "$hs" | wc -l)
    rsn=$(printf '%s\n' "$rs" | wc -l)
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" = "0" ]; then printf '%s\tMATCH\t%s\t%s\t0\n' "$rel" "$hsn" "$rsn"
    else printf '%s\tDIFF\t%s\t%s\t%s\n' "$rel" "$hsn" "$rsn" "$d"; fi
}
export -f rs_one

N=$(filelist | grep -c .)
echo "corpus_file_diff: $N files, JOBS=$JOBS, -N$HS_N, FILE_TIMEOUT=${FILE_TIMEOUT}s, cache=$CACHE"
echo "=== PHASE 1: Haskell (all files first, no RS) ==="
filelist | grep . | xargs -P "$JOBS" -I{} bash -c 'hs_one "$@"' _ {}
echo "=== PHASE 2: Rust + diff ==="
: > "$RESULTS_TSV"
filelist | grep . | xargs -P "$JOBS" -I{} bash -c 'rs_one "$@"' _ {} >> "$RESULTS_TSV"
sort -o "$RESULTS_TSV" "$RESULTS_TSV"
echo "=== SUMMARY ==="
awk -F'\t' '{c[$2]++} END{for(k in c) printf "  %-18s %d\n", k, c[k]}' "$RESULTS_TSV"
echo "  results: $RESULTS_TSV"
echo "DONE_CORPUS_FILE_DIFF"
