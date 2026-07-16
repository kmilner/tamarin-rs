#!/usr/bin/env bash
# Behavioral-equivalence sweep for a "refactor that shouldn't change output":
# run TWO Rust binaries (PRE-patch baseline vs POST-patch) over every example
# and diff their stripped --prove stdout.  No Haskell needed — if the two RS
# binaries agree everywhere, the refactor is behaviorally inert and inherits
# the baseline's HS-faithfulness by transitivity (covers even HS-timeout
# monsters).  Where they differ, those exact files get an HS comparison.
set -u
ROOT="${ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
CORPUS="${CORPUS:-$ROOT/tamarin-prover/examples}"
PRE="${PRE:-/tmp/rs-prepatch}"
POST="${POST:-/tmp/rs-patched}"
TIMEOUT="${TIMEOUT:-180}"
JOBS="${JOBS:-6}"
DERIV="${DERIV:-30}"
OUT="${OUT:-/tmp/rs_vs_rs.tsv}"
RESUME="${RESUME:-}"   # path to a prior TSV: files already present are skipped
export PRE POST TIMEOUT DERIV CORPUS

strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
export -f strip_env

one() {
    local rel="$1" f="$CORPUS/$1" a b ra rb da
    [ -f "$f" ] || { printf '%s\tNOFILE\t0\n' "$rel"; return 0; }
    local ta tb; ta=$(mktemp); tb=$(mktemp)
    timeout "$TIMEOUT" "$PRE"  --derivcheck-timeout="$DERIV" --prove "$f" >"$ta" 2>/dev/null; ra=$?
    timeout "$TIMEOUT" "$POST" --derivcheck-timeout="$DERIV" --prove "$f" >"$tb" 2>/dev/null; rb=$?
    if [ "$ra" = 124 ] && [ "$rb" = 124 ]; then rm -f "$ta" "$tb"; printf '%s\tTIMEOUT_BOTH\t0\n' "$rel"; return 0; fi
    if [ "$ra" = 124 ] || [ "$rb" = 124 ]; then rm -f "$ta" "$tb"; printf '%s\tTIMEOUT_ONE\tpre=%s,post=%s\n' "$rel" "$ra" "$rb"; return 0; fi
    a=$(strip_env <"$ta"); b=$(strip_env <"$tb"); rm -f "$ta" "$tb"
    da=$(diff <(printf '%s\n' "$a") <(printf '%s\n' "$b") | grep -c '^[<>]')
    if [ "$da" = 0 ]; then printf '%s\tSAME\t0\n' "$rel"
    else printf '%s\tDIFF\t%s\n' "$rel" "$da"; fi
}
export -f one

cd "$CORPUS"
# Resume: skip files already conclusively recorded in $RESUME (keep its rows).
declare -A DONE=()
if [ -n "$RESUME" ] && [ -f "$RESUME" ]; then
    while IFS=$'\t' read -r rel _; do DONE["$rel"]=1; done < "$RESUME"
    cp "$RESUME" "$OUT"
    echo "rs_vs_rs: resuming, ${#DONE[@]} files already done in $RESUME"
else
    : > "$OUT"
fi
# ALLOWLIST (one relpath per line) restricts the run, e.g. to the
# HS-comparable set (files HS can actually prove — anything else has no
# oracle to validate a behavioral diff against).  Empty = whole corpus.
if [ -n "${ALLOWLIST:-}" ] && [ -f "$ALLOWLIST" ]; then
    mapfile -t ALL < <(sort -u "$ALLOWLIST")
    echo "rs_vs_rs: ALLOWLIST=$ALLOWLIST (${#ALL[@]} files)"
else
    mapfile -t ALL < <(find . -name '*.spthy' | sed 's|^\./||' | sort)
fi
FILES=()
for f in "${ALL[@]}"; do [ -n "${DONE[$f]:-}" ] || FILES+=("$f"); done
echo "rs_vs_rs: ${#ALL[@]} total, ${#FILES[@]} to run, JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, PRE=$PRE POST=$POST"
[ "${#FILES[@]}" -gt 0 ] && printf '%s\n' "${FILES[@]}" | xargs -P "$JOBS" -I{} bash -c 'one "$@"' _ {} >> "$OUT"
sort -o "$OUT" "$OUT"
echo "=== SUMMARY ==="
awk -F'\t' '{c[$2]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$OUT"
echo "=== DIFFs (behavioral changes from the refactor) ==="
awk -F'\t' '$2=="DIFF"{print "  "$3"\t"$1}' "$OUT" | sort -rn
echo "  results: $OUT"
echo "DONE_RS_VS_RS"
