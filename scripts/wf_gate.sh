#!/usr/bin/env bash
# Fast full-corpus WELLFORMEDNESS gate: diff the wf WARNING block of every
# corpus theory against the Haskell oracle.  The wf report is emitted at
# theory-load time, so this runs WITHOUT `--prove` (~1s/file vs minutes) —
# fast enough to run on every build.
#
# It reuses the batch gate's HS cache (scripts/.hs_file_cache, produced by
# corpus_file_diff.sh) for the reference side, extracting just the wf block.
# The RS side is whatever binary RS_PATH points at (default: the release
# build); a sealed-side harness that emits the same theory-load output can be
# gated the same way by setting RS_PATH.
#
# Env: RS_PATH, HS_CACHE (dir), JOBS, FILE_TIMEOUT, RESULTS_TSV, ALLOWLIST.
# Output TSV (3 col): relpath  MATCH|DIFF|SKIP_NO_HS  diffcount
set -u
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 25165824 2>/dev/null || true

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(dirname "$script_dir")
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
HS_CACHE="${HS_CACHE:-$script_dir/.hs_file_cache}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
JOBS="${JOBS:-4}"
FILE_TIMEOUT="${FILE_TIMEOUT:-120}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-10}"
RESULTS_TSV="${RESULTS_TSV:-$script_dir/results/wf_gate_results.tsv}"
mkdir -p "$(dirname "$RESULTS_TSV")"
export RS_PATH HS_CACHE CORPUS_ROOT FLAGS_MAP FILE_TIMEOUT DERIVCHECK_TIMEOUT
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }

strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
# Isolate the wf report: either the success line, or the WARNING block that
# opens the leading theory comment (up to its closing `*/`).
wf_block() {
    awk '
        /^\/\* All wellformedness checks were successful\. \*\/$/ { print; next }
        /^WARNING: the following wellformedness checks failed!$/  { f=1 }
        f { print }
        f && /^\*\/$/ { f=0 }
    '
}
flags_for() { [ -f "$FLAGS_MAP" ] && awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"; }
ckey() {
    local h fl; h=$(sha256sum "$2" | cut -d' ' -f1); fl=$(flags_for "$1")
    if [ -n "$fl" ]; then printf '%s__f%s' "$h" "$(printf '%s' "$fl" | sha256sum | cut -c1-12)"
    else printf '%s' "$h"; fi
}
export -f strip_env wf_block flags_for ckey

one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key fl hs rs d
    [ -f "$f" ] || { printf '%s\tSKIP_NO_HS\t0\n' "$rel"; return 0; }
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$HS_CACHE/$key.full.gz" ] || { printf '%s\tSKIP_NO_HS\t0\n' "$rel"; return 0; }
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* ]]; then fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f"); fi
    hs=$(zcat "$HS_CACHE/$key.full.gz" | strip_env | wf_block)
    # RS: theory-load only (NO --prove) so the wf block prints fast.
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$RS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" "$farg" ) >"$tmp" 2>/dev/null
    if [ "$?" = "124" ]; then rm -f "$tmp"; printf '%s\tSKIP_RS_TIMEOUT\t0\n' "$rel"; return 0; fi
    rs=$(strip_env < "$tmp" | wf_block); rm -f "$tmp"
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" = 0 ]; then printf '%s\tMATCH\t0\n' "$rel"; else printf '%s\tDIFF\t%s\n' "$rel" "$d"; fi
}
export -f one

filelist() {
    if [ -n "${ALLOWLIST:-}" ] && [ -f "$ALLOWLIST" ]; then cat "$ALLOWLIST"
    elif [ -f "$script_dir/parity_corpus.txt" ]; then cat "$script_dir/parity_corpus.txt"
    else (cd "$CORPUS_ROOT" && find . -name '*.spthy' | sed 's|^\./||'); fi
}

filelist | xargs -P"$JOBS" -I{} bash -c 'one "$@"' _ {} | sort > "$RESULTS_TSV"
m=$(awk -F'\t' '$2=="MATCH"' "$RESULTS_TSV" | wc -l)
diff=$(awk -F'\t' '$2=="DIFF"' "$RESULTS_TSV" | wc -l)
skip=$(awk -F'\t' '$2 ~ /^SKIP/' "$RESULTS_TSV" | wc -l)
echo "wf_gate: MATCH=$m DIFF=$diff SKIP=$skip  ->  $RESULTS_TSV"
[ "$diff" = 0 ]
