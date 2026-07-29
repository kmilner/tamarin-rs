#!/usr/bin/env bash
# Fast full-corpus THEORY PRETTY-PRINT gate: diff the rendered `theory <name>
# begin … end` echo of every corpus theory against the Haskell oracle.
#
# The theory echo is emitted at theory-load time, so this runs WITHOUT
# `--prove` (~1s/file vs minutes) — fast enough to run on every build, and it
# is exactly the observable the pretty-printer produces on the batch path.
#
# WHY A DEDICATED NON-PROVE HS CACHE (scripts/.hs_pretty_cache) and NOT the
# batch --prove cache (scripts/.hs_file_cache):  the batch cache is `--prove`
# output, so each lemma there is followed by its full PROOF TREE (solve(...) …
# qed).  That proof text is SOLVER output, not pretty-printer surface, and it
# does not appear on the no-prove echo path (lemmas render `by sorry`).  To
# compare the pure Theory→text render — including the LEMMA/RESTRICTION FORMULA
# rendering — both sides must be no-prove.  So we keep a separate no-prove HS
# reference cache; it is auto-filled on first run (fast) and reused warm after.
# We reuse corpus_file_diff.sh's ckey / flags / strip_env machinery verbatim so
# per-file canonical flags and the @cd recipe stay identical to the other gates.
#
# Extraction (extract_theory): keep `^theory ` … `^end$`; DROP the trailing
# formal-comment blocks tamarin appends inside that span — the wellformedness
# report (`/* All wellformedness checks were successful. */` OR the multi-line
# `/*\nWARNING …\n*/`, a SEPARATE slice owned by wf_gate.sh) and the volatile
# `/*\nGenerated from: …\n*/` build stamp — and everything after `end` (the
# summary-of-summaries, which carries processing time).  Interior comments
# (rule AC-variant blocks, `guarded formula characterizing …`) are KEPT: they
# are pretty-printer output.
#
# Env: RS_PATH, HS_PATH, HS_CACHE (dir), JOBS, FILE_TIMEOUT, DERIVCHECK_TIMEOUT,
#      RESULTS_TSV, ALLOWLIST, NO_HS_FILL (skip phase 0 if the cache is warm).
# Output TSV (3 col): relpath  MATCH|DIFF|SKIP_*  diffcount
set -u
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 25165824 2>/dev/null || true

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(dirname "$script_dir")
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
HS_CACHE="${HS_CACHE:-$script_dir/.hs_pretty_cache}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
JOBS="${JOBS:-4}"
FILE_TIMEOUT="${FILE_TIMEOUT:-120}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-10}"
RESULTS_TSV="${RESULTS_TSV:-$script_dir/results/pretty_gate_results.tsv}"
mkdir -p "$(dirname "$RESULTS_TSV")"
NO_HS_FILL="${NO_HS_FILL:-}"
mkdir -p "$HS_CACHE"

find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin "$repo_root")}" || true
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
export RS_PATH HS_PATH HS_CACHE CORPUS_ROOT FLAGS_MAP FILE_TIMEOUT DERIVCHECK_TIMEOUT

strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
# Isolate the pretty-printed theory echo: `theory … begin … end`, minus the
# trailing wf report and Generated-from stamp, minus the post-`end` summary.
extract_theory() {
    awk '
        /^theory /              { cap=1 }
        !cap                    { next }
        # wf SUCCESS single-line comment -> drop.
        /^\/\* All wellformedness checks were successful\. \*\/$/ { next }
        # column-0 `/*` opens a multi-line comment: peek to classify.
        /^\/\*$/ {
            if ((getline nxt) > 0) {
                if (nxt == "WARNING: the following wellformedness checks failed!" || nxt == "Generated from:") {
                    while ((getline z) > 0) { if (z == "*/") break }   # drop block
                    next
                }
                print; print nxt; next                                 # keep interior comment
            }
            print; next
        }
        { print }
        /^end$/                 { cap=0 }
    '
}
flags_for() { [ -f "$FLAGS_MAP" ] && awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"; }
ckey() {
    local h fl; h=$(sha256sum "$2" | cut -d' ' -f1); fl=$(flags_for "$1")
    if [ -n "$fl" ]; then printf '%s__f%s' "$h" "$(printf '%s' "$fl" | sha256sum | cut -c1-12)"
    else printf '%s' "$h"; fi
}
export -f strip_env extract_theory flags_for ckey

# --- Phase 0: fill any MISSING no-prove HS reference (fast; warm-cache reused).
hs_fill_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key fl
    [ -f "$f" ] || return 0
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$HS_CACHE/$key.theory.gz" ] && return 0
    [ -f "$HS_CACHE/$key.nohs" ] && return 0
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f"); fi
    # `--diff` theories are not on the RS-matchable path; skip filling them.
    case " $fl " in *" --diff "*) touch "$HS_CACHE/$key.nohs"; return 0;; esac
    local tmp out; tmp=$(mktemp)
    # shellcheck disable=SC2086
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$HS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" "$farg" ) >"$tmp" 2>/dev/null
    out=$(strip_env < "$tmp" | extract_theory); rm -f "$tmp"
    if [ -z "$out" ]; then touch "$HS_CACHE/$key.nohs"
    else printf '%s' "$out" | gzip > "$HS_CACHE/$key.theory.gz"; fi
}
export -f hs_fill_one

# --- Phase 1: RS no-prove + diff vs cached HS theory echo.
one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key fl hs rs d
    [ -f "$f" ] || { printf '%s\tSKIP_NO_HS\t0\n' "$rel"; return 0; }
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$HS_CACHE/$key.theory.gz" ] || { printf '%s\tSKIP_NO_HS\t0\n' "$rel"; return 0; }
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f"); fi
    hs=$(zcat "$HS_CACHE/$key.theory.gz")
    local tmp; tmp=$(mktemp)
    # shellcheck disable=SC2086
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$RS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" "$farg" ) >"$tmp" 2>/dev/null
    if [ "$?" = "124" ]; then rm -f "$tmp"; printf '%s\tSKIP_RS_TIMEOUT\t0\n' "$rel"; return 0; fi
    rs=$(strip_env < "$tmp" | extract_theory); rm -f "$tmp"
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" = 0 ]; then printf '%s\tMATCH\t0\n' "$rel"; else printf '%s\tDIFF\t%s\n' "$rel" "$d"; fi
}
export -f one

filelist() {
    if [ -n "${ALLOWLIST:-}" ] && [ -f "$ALLOWLIST" ]; then cat "$ALLOWLIST"
    elif [ -f "$script_dir/parity_corpus.txt" ]; then cat "$script_dir/parity_corpus.txt"
    else (cd "$CORPUS_ROOT" && find . -name '*.spthy' | sed 's|^\./||'); fi
}

if [ -z "$NO_HS_FILL" ]; then
    [ -x "${HS_PATH:-/nonexistent}" ] || { echo "no HS binary (set HS_PATH or NO_HS_FILL=1)" >&2; exit 2; }
    echo "=== PHASE 0: fill missing no-prove HS theory cache ($HS_CACHE) ==="
    filelist | grep . | xargs -P"$JOBS" -I{} bash -c 'hs_fill_one "$@"' _ {}
fi
echo "=== PHASE 1: RS no-prove + diff ==="
filelist | grep . | xargs -P"$JOBS" -I{} bash -c 'one "$@"' _ {} | sort > "$RESULTS_TSV"
m=$(awk -F'\t' '$2=="MATCH"' "$RESULTS_TSV" | wc -l)
diff=$(awk -F'\t' '$2=="DIFF"' "$RESULTS_TSV" | wc -l)
skip=$(awk -F'\t' '$2 ~ /^SKIP/' "$RESULTS_TSV" | wc -l)
echo "pretty_gate: MATCH=$m DIFF=$diff SKIP=$skip  ->  $RESULTS_TSV"
[ "$diff" = 0 ]
