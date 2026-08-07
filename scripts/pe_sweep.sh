#!/bin/bash
# --partial-evaluation=summary parity sweep (no --prove) over the fast corpus
# subset, excluding the documented deliberate-divergence classes: macro theories
# (HS feeds PE macro-UNexpanded rules), SAPIC/accountability theories (HS
# removeTranslationItems + process-attr reconstruction), and files that need
# flags per file_flags.tsv (--diff / --auto-sources interplay is an un-analysed
# corner upstream).
#
# Stages: parallel pass at TIMEOUT, then a serial retry of ERROR rows at
# RETRY_TIMEOUT (heavy files are load-sensitive; the oracle cache remembers a
# timeout at its cap, so retries only burn the oracle once ever). Documented
# residuals resolve to LEDGERED via scripts/sweep_expected.tsv.
# FAMILY=1 restricts to scripts/pe_family.txt — one representative per
# divergence class, for inner-loop iteration.
set -u
. "$(dirname "$0")/sweep_common.sh"
OUT=${OUT:-$REPO/scripts/results/pe_sweep.tsv}
RETRY_TIMEOUT=${RETRY_TIMEOUT:-600}
mkdir -p "$(dirname "$OUT")"

eligible() {
  if [ "${FAMILY:-0}" = 1 ]; then
    family_list "$REPO/scripts/pe_family.txt" "$EXAMPLES"
    return
  fi
  # The files-need-flags exclusion is a whole-list filter (one grep) rather
  # than a per-file membership test.
  while read -r rel; do
    f="$EXAMPLES/$rel"
    [ -f "$f" ] || continue
    grep -qE '^\s*(macros\s*:|process\s*:|process\s*=|let\s+\w+\s*=|options\s*:.*translation|accountability|case-test|caseTest|verdictfunction)' "$f" && continue
    echo "$f"
  done < <(sed 's/#.*//;/^\s*$/d' "$REPO/scripts/parity_corpus_fast.txt" \
             | grep -vxF -f <(sed 's/#.*//;/^\s*$/d' "$REPO/scripts/file_flags.tsv" | cut -f1))
}

# one <file> [detail-tag] — appends one TSV row for the file at current TIMEOUT.
one() {
  f=$1; tag=${2:--}
  d=$(mktemp -d)
  hs_run "$d" "$f" "pe-summary-dct30" --derivcheck-timeout=30 --partial-evaluation=summary; hrc=$?
  # An oracle timeout is cached at this cap, so it comes back instantly while
  # the RS side would burn the full cap producing nothing to compare against.
  if [ $hrc -ge 124 ]; then echo -e "$f\tERROR\ttimeout/kill hs=$hrc rs=skipped $tag" >> "$OUT"; rm -rf "$d"; return; fi
  grun "$RS_BIN" --with-maude="$MAUDE" --derivcheck-timeout=30 --partial-evaluation=summary "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ $rrc -ge 124 ]; then echo -e "$f\tERROR\ttimeout/kill hs=$hrc rs=$rrc $tag" >> "$OUT"
  elif [ $hrc -ne $rrc ]; then echo -e "$f\tDIFF\trc hs=$hrc rs=$rrc $tag" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.out") <(norm < "$d/rs.out") >/dev/null; then echo -e "$f\tDIFF\tstdout $tag" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.err" | nerr) <(norm < "$d/rs.err" | nerr) >/dev/null; then echo -e "$f\tDIFF\tstderr $tag" >> "$OUT"
  else echo -e "$f\tOK\t$tag" >> "$OUT"; fi
  rm -rf "$d"
}
sweep_export

rs_stale_check
LIST=$(eligible | sort -u)
: > "$OUT"
sweep_banner pe_sweep "$(echo "$LIST" | grep -c .)"
echo "$LIST" | xargs -r -P "$JOBS" -n 1 bash -c 'one "$0"'
sweep_retry "$OUT" 2 "$RETRY_TIMEOUT"
sweep_finish "$OUT" pe 2
