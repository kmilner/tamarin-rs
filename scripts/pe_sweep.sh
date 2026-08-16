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
sweep_out "$REPO/scripts/results/pe_sweep.tsv"

list_files() {
  if [ "${FAMILY:-0}" = 1 ]; then
    resolve_list "$REPO/scripts/pe_family.txt" "$EXAMPLES"
    return
  fi
  # The files-need-flags exclusion is a whole-list filter (one grep) rather
  # than a per-file membership test.
  # A SAPIC theory is recognised by its `process:` / `process =` block, which
  # every one of them carries; a bare `let <ident> =` is NOT a marker, since
  # that is also how an MSR rule abbreviates a term (`let X = 'g'^~ex`).
  local rel f kept=0 dropped=0 missing=0
  while read -r rel; do
    f="$EXAMPLES/$rel"
    # Fatal for the same reason resolve_list's is: dropping the entry would
    # shrink the denominator with nothing left to notice it by.
    if [ ! -f "$f" ]; then
      echo "ERROR: corpus entry missing: $f" >&2; missing=$((missing + 1)); continue
    fi
    if grep -qE '^[[:space:]]*(macros[[:space:]]*:|process[[:space:]]*:|process[[:space:]]*=|options[[:space:]]*:.*translation|accountability|case-test|caseTest|verdictfunction)' "$f"; then
      dropped=$((dropped + 1))
      continue
    fi
    kept=$((kept + 1))
    echo "$f"
  done < <(list_lines "$REPO/scripts/parity_corpus_fast.txt" \
             | grep -vxF -f <(list_lines "$REPO/scripts/file_flags.tsv" | cut -f1))
  if [ "$missing" -gt 0 ]; then
    echo "ERROR: $missing entry/entries of parity_corpus_fast.txt no longer exist — fix the corpus list" >&2
    exit 2
  fi
  # Report the shrinkage rather than letting it hide inside the denominator.
  echo "== pe_sweep eligibility: kept $kept, excluded $dropped ==" >&2
}

# one <file> [detail-tag] — appends one TSV row for the file at current TIMEOUT
# (sweep_common's sweep_one: no unit column, the tag defaulting to '-').
one() {
  sweep_one "$1" '' "${2:--}" pe-summary-dct30 \
    --derivcheck-timeout=30 --partial-evaluation=summary
}
sweep_export
sweep_drive pe 2
