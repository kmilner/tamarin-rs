#!/usr/bin/env bash
# Reference-output gate for CI: compare ONE Rust binary's stripped --prove
# stdout against a committed reference TSV of output hashes (generated from
# main by someone with a fast machine).  This is rs_vs_rs_diff.sh with the
# PRE side frozen into a file: a PR runner only builds and runs its own
# binary, so the job fits a slow GitHub runner.
#
#   scripts/rs_ref_check.sh generate   # run BIN, WRITE the reference (manual,
#                                      # on a trusted build of main)
#   scripts/rs_ref_check.sh check      # run BIN, DIFF against the reference;
#                                      # nonzero exit on any mismatch (CI)
#
# Reference rows: relpath \t input_key \t output_sha256 \t lines
#   input_key = sha256 of the theory file (+ flags-hash suffix when
#   file_flags.tsv adds flags), so a submodule bump or flag change shows up as
#   INPUT_CHANGED ("regenerate the reference"), never as a silent false DIFF.
#
# Cross-machine determinism: prover parallelism is pinned via EXTRA_FLAGS
# (default --processors=4 --maude-processes=4) so a 4-core runner and a
# 24-core workstation execute the same schedule.  Maude version must match
# the one recorded in the reference header (unifier enumeration order can
# differ between Maude versions).
#
# Env: BIN (default target/release/tamarin-rs), REF (default
#      scripts/ci_ref_fast.tsv), ALLOWLIST (default
#      scripts/parity_corpus_fast.txt), FLAGS_MAP, CORPUS, TIMEOUT (120),
#      DERIV (30), JOBS, EXTRA_FLAGS
set -u
LC_ALL=C

MODE="${1:-}"
case "$MODE" in generate|check) ;; *) echo "usage: $0 generate|check" >&2; exit 2;; esac

# OOM discipline (see rs_vs_rs_diff.sh): provers die alone, not the session.
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 25165824 2>/dev/null || true

ROOT="${ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
CORPUS="${CORPUS:-$ROOT/tamarin-prover/examples}"
BIN="${BIN:-$ROOT/target/release/tamarin-rs}"
REF="${REF:-$ROOT/scripts/ci_ref_fast.tsv}"
ALLOWLIST="${ALLOWLIST:-$ROOT/scripts/parity_corpus_fast.txt}"
FLAGS_MAP="${FLAGS_MAP:-$ROOT/scripts/file_flags.tsv}"
TIMEOUT="${TIMEOUT:-120}"
DERIV="${DERIV:-30}"
cores=$(nproc 2>/dev/null || echo 4)
JOBS="${JOBS:-$(( cores >= 24 ? 4 : cores >= 12 ? 2 : 1 ))}"
EXTRA_FLAGS="${EXTRA_FLAGS---processors=4 --maude-processes=4}"
export CORPUS BIN FLAGS_MAP TIMEOUT DERIV EXTRA_FLAGS

[ -x "$BIN" ] || { echo "rs_ref_check: no executable prover at '$BIN' (set BIN=)" >&2; exit 2; }
[ -f "$ALLOWLIST" ] || { echo "rs_ref_check: ALLOWLIST '$ALLOWLIST' does not exist" >&2; exit 2; }
command -v maude >/dev/null 2>&1 || { echo "rs_ref_check: 'maude' not on PATH — install it first" >&2; exit 2; }
if [ "$MODE" = check ]; then
    [ -f "$REF" ] || { echo "rs_ref_check: reference '$REF' missing — run generate first" >&2; exit 2; }
    ref_maude=$(awk -F': ' '/^# maude:/{print $2; exit}' "$REF")
    cur_maude=$(maude --version)
    if [ -n "$ref_maude" ] && [ "$ref_maude" != "$cur_maude" ]; then
        echo "rs_ref_check: maude version mismatch: reference was generated with $ref_maude, this machine has $cur_maude" >&2
        exit 2
    fi
fi

strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
flags_for() { [ -f "$FLAGS_MAP" ] && awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"; }
ikey() {  # input key: theory sha + flags-hash suffix (matches wf_gate's ckey)
    local h fl; h=$(sha256sum "$2" | cut -d' ' -f1); fl=$(flags_for "$1")
    if [ -n "$fl" ]; then printf '%s__f%s' "$h" "$(printf '%s' "$fl" | sha256sum | cut -c1-12)"
    else printf '%s' "$h"; fi
}
export -f strip_env flags_for ikey

# one <rel> → "rel \t ikey \t sha|TIMEOUT|ERROR=n \t lines"
one() {
    local rel="$1" f="$CORPUS/$1" fl rundir="" farg key rc out sha lines
    [ -f "$f" ] || { printf '%s\t-\tNOFILE\t0\n' "$rel"; return 0; }
    key=$(ikey "$rel" "$f"); fl=$(flags_for "$rel"); farg="$f"
    if [[ " $fl " == *" @cd "* ]]; then fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f"); fi
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$TIMEOUT" "$BIN" $fl $EXTRA_FLAGS --derivcheck-timeout="$DERIV" --prove "$farg" ) >"$tmp" 2>/dev/null; rc=$?
    if [ "$rc" = 124 ]; then rm -f "$tmp"; printf '%s\t%s\tTIMEOUT\t0\n' "$rel" "$key"; return 0; fi
    if [ "$rc" != 0 ]; then rm -f "$tmp"; printf '%s\t%s\tERROR=%s\t0\n' "$rel" "$key" "$rc"; return 0; fi
    out=$(strip_env <"$tmp"); rm -f "$tmp"
    sha=$(printf '%s\n' "$out" | sha256sum | cut -d' ' -f1)
    lines=$(printf '%s\n' "$out" | wc -l)
    printf '%s\t%s\t%s\t%s\n' "$rel" "$key" "$sha" "$lines"
}
export -f one

mapfile -t FILES < <(grep -v '^#' "$ALLOWLIST" | sort -u)
echo "rs_ref_check: $MODE — ${#FILES[@]} files, JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, BIN=$BIN"
RUN=$(mktemp)
printf '%s\n' "${FILES[@]}" | xargs -P "$JOBS" -I{} bash -c 'one "$@"' _ {} | sort > "$RUN"

bad=0
if [ "$MODE" = generate ]; then
    if grep -qE $'\t(TIMEOUT|ERROR=[0-9]+|NOFILE)\t' "$RUN"; then
        echo "rs_ref_check: refusing to write an incomplete reference — failed rows:" >&2
        grep -E $'\t(TIMEOUT|ERROR=[0-9]+|NOFILE)\t' "$RUN" >&2
        rm -f "$RUN"; exit 1
    fi
    { echo "# rs_ref_check reference — regenerate with: scripts/rs_ref_check.sh generate"
      echo "# maude: $(maude --version)"
      cat "$RUN"; } > "$REF"
    echo "rs_ref_check: wrote $(grep -vc '^#' "$REF") rows to $REF"
else
    while IFS=$'\t' read -r rel key sha lines; do
        refrow=$(awk -F'\t' -v r="$rel" '!/^#/ && $1==r {print; exit}' "$REF")
        if [ -z "$refrow" ]; then
            echo "  NOREF          $rel (not in reference — regenerate to add it)"; bad=$((bad+1)); continue
        fi
        rkey=$(printf '%s' "$refrow" | cut -f2); rsha=$(printf '%s' "$refrow" | cut -f3)
        if [ "$key" != "$rkey" ]; then
            echo "  INPUT_CHANGED  $rel (theory/flags changed — submodule bump? regenerate the reference)"; bad=$((bad+1)); continue
        fi
        case "$sha" in
            TIMEOUT|ERROR=*|NOFILE) echo "  $sha  $rel"; bad=$((bad+1)); continue;;
        esac
        if [ "$sha" = "$rsha" ]; then
            echo "  MATCH          $rel"
        else
            echo "  DIFF           $rel (output hash changed, $lines lines — reproduce locally with rs_vs_rs_diff.sh)"; bad=$((bad+1))
        fi
    done < "$RUN"
    total=$(wc -l < "$RUN")
    echo "rs_ref_check: $((total-bad))/$total match"
    [ "$bad" = 0 ] || { rm -f "$RUN"; echo "rs_ref_check: FAIL — $bad file(s) diverge from the committed main reference" >&2; exit 1; }
fi
rm -f "$RUN"
echo "DONE_RS_REF_CHECK"
