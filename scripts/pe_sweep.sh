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
FLAGGED=$(sed 's/#.*//;/^\s*$/d' "$REPO/scripts/file_flags.tsv" | cut -f1)

eligible() {
  if [ "${FAMILY:-0}" = 1 ]; then
    sed 's/#.*//;/^\s*$/d' "$REPO/scripts/pe_family.txt" | sed "s|^|$EXAMPLES/|" \
      | while read -r f; do
          if [ -f "$f" ]; then echo "$f"; else echo "WARNING: family entry missing: $f" >&2; fi
        done
    return
  fi
  while read -r rel; do
    f="$EXAMPLES/$rel"
    [ -f "$f" ] || continue
    echo "$FLAGGED" | grep -qxF "$rel" && continue
    grep -qE '^\s*(macros\s*:|process\s*:|process\s*=|let\s+\w+\s*=|options\s*:.*translation)' "$f" && continue
    grep -qE '^\s*(accountability|case-test|caseTest|verdictfunction)' "$f" && continue
    echo "$f"
  done < <(sed 's/#.*//;/^\s*$/d' "$REPO/scripts/parity_corpus_fast.txt")
}

# one <file> [detail-tag] — appends one TSV row for the file at current TIMEOUT.
one() {
  f=$1; tag=${2:--}
  d=$(mktemp -d)
  hs_run "$d" "$f" "pe-summary-dct30" --derivcheck-timeout=30 --partial-evaluation=summary; hrc=$?
  grun "$RS_BIN" --with-maude="$MAUDE" --derivcheck-timeout=30 --partial-evaluation=summary "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ $hrc -ge 124 ] || [ $rrc -ge 124 ]; then echo -e "$f\tERROR\ttimeout/kill hs=$hrc rs=$rrc $tag" >> "$OUT"
  elif [ $hrc -ne $rrc ]; then echo -e "$f\tDIFF\trc hs=$hrc rs=$rrc $tag" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.out") <(norm < "$d/rs.out") >/dev/null; then echo -e "$f\tDIFF\tstdout $tag" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.err") <(norm < "$d/rs.err") >/dev/null; then echo -e "$f\tDIFF\tstderr $tag" >> "$OUT"
  else echo -e "$f\tOK\t$tag" >> "$OUT"; fi
  rm -rf "$d"
}
export -f one grun norm hs_run hs_fingerprint
export HS_BIN RS_BIN MAUDE OUT TIMEOUT HS_CACHE

rs_stale_check
LIST=$(eligible | sort -u)
: > "$OUT"
sweep_banner pe_sweep "$(echo "$LIST" | wc -l)"
echo "$LIST" | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'

# Serial retry of ERROR rows at the higher cap; retry rows replace originals.
RETRY=$(grep -P '\tERROR\t' "$OUT" | cut -f1 || true)
if [ -n "$RETRY" ]; then
  echo "== retrying $(echo "$RETRY" | wc -l) ERROR rows serially at TIMEOUT=$RETRY_TIMEOUT =="
  grep -vP '\tERROR\t' "$OUT" > "$OUT.keep" && mv "$OUT.keep" "$OUT"
  while read -r f; do
    # The parallel pass's timeout entry (lower cap) misses for this higher
    # cap; the retry's own outcome is cached at cap $RETRY_TIMEOUT for good.
    TIMEOUT=$RETRY_TIMEOUT one "$f" retry
  done <<< "$RETRY"
fi

sweep_finish "$OUT" pe 2
