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
# residuals resolve to LEDGERED via scripts/sweep_expected.tsv; a row where
# neither side analysed the theory is NO-COMPARE (see sweep_common.sh).
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
  # A SAPIC theory is recognised by its `process:` / `process =` block, which
  # every one of them carries; a bare `let <ident> =` is NOT a marker, since
  # that is also how an MSR rule abbreviates a term (`let X = 'g'^~ex`).
  local kept=0 dropped=0
  while read -r rel; do
    f="$EXAMPLES/$rel"
    [ -f "$f" ] || continue
    if grep -qE '^\s*(macros\s*:|process\s*:|process\s*=|options\s*:.*translation|accountability|case-test|caseTest|verdictfunction)' "$f"; then
      dropped=$((dropped + 1))
      continue
    fi
    kept=$((kept + 1))
    echo "$f"
  done < <(sed 's/#.*//;/^\s*$/d' "$REPO/scripts/parity_corpus_fast.txt" \
             | grep -vxF -f <(sed 's/#.*//;/^\s*$/d' "$REPO/scripts/file_flags.tsv" | cut -f1))
  # Report the shrinkage rather than letting it hide inside the denominator.
  echo "== pe_sweep eligibility: kept $kept, excluded $dropped ==" >&2
}

# one <file> [detail-tag] — appends one TSV row for the file at current TIMEOUT.
one() {
  f=$1; tag=${2:--}
  d=$(mktemp -d)
  hs_run "$d" "$f" "pe-summary-dct30" --derivcheck-timeout=30 --partial-evaluation=summary; hrc=$?
  # A broken environment is diagnosed before the cap is blamed for it: an
  # unusable maude both aborts and hangs, and "timeout" would be the wrong
  # story (and a ledgerable one).
  if infra_abort "$d/hs.err"; then echo -e "$f\tNO-COMPARE\tinfra-abort hs (rs not run) hs=$hrc $tag" >> "$OUT"; rm -rf "$d"; return; fi
  # An oracle timeout is cached at this cap, so it comes back instantly while
  # the RS side would burn the full cap producing nothing to compare against.
  if [ $hrc -ge 124 ]; then echo -e "$f\tERROR\ttimeout/kill hs=$hrc rs=skipped $tag" >> "$OUT"; rm -rf "$d"; return; fi
  grun "$RS_BIN" --with-maude="$MAUDE" --derivcheck-timeout=30 --partial-evaluation=summary "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ $rrc -ge 124 ]; then echo -e "$f\tERROR\ttimeout/kill hs=$hrc rs=$rrc $tag" >> "$OUT"
  elif nc=$(nocompare_check $hrc $rrc "$d/hs.err" "$d/rs.err" "$d/hs.out" "$d/rs.out"); then
    echo -e "$f\tNO-COMPARE\t$nc $tag" >> "$OUT"
  elif [ $hrc -ne $rrc ]; then echo -e "$f\tDIFF\trc hs=$hrc rs=$rrc $tag" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.out") <(norm < "$d/rs.out") >/dev/null; then echo -e "$f\tDIFF\tstdout $tag" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.err" | nerr) <(norm < "$d/rs.err" | nerr) >/dev/null; then echo -e "$f\tDIFF\tstderr $tag" >> "$OUT"
  else echo -e "$f\tOK\t$tag" >> "$OUT"; fi
  rm -rf "$d"
}
sweep_export

rs_stale_check
LIST=$(eligible) || exit 2
LIST=$(sort -u <<< "$LIST")
: > "$OUT"
sweep_banner pe_sweep "$(echo "$LIST" | grep -c .)"
echo "$LIST" | xargs -r -P "$JOBS" -n 1 bash -c 'one "$0"'
sweep_retry "$OUT" 2 "$RETRY_TIMEOUT"
sweep_finish "$OUT" pe 2
