#!/bin/bash
# -m spthy/spthytyped/msr parity sweep: RS vs HS, translate-only (no proving).
# Corpus: parity_corpus.txt + every examples/sapic/**/*.spthy (deduped).
# A file where BOTH sides fail with the same rc + normalized stderr counts as
# agreement — unless neither side got as far as analysing the theory, which is
# NO-COMPARE (see sweep_common.sh). Documented residuals resolve to LEDGERED via
# scripts/sweep_expected.tsv (per file, or per file+module). FAMILY=1 restricts
# to scripts/module_family.txt.
#
# Stages: parallel pass at TIMEOUT, then a serial retry of ERROR rows at
# RETRY_TIMEOUT (heavy files are load-sensitive).
# Output: TSV rows  <file>\t<module>\t<OK|DIFF|ERROR|LEDGERED|NO-COMPARE>\t<detail>
set -u
. "$(dirname "$0")/sweep_common.sh"
sweep_out "$REPO/scripts/results/module_sweep.tsv"
MODULES=(spthy spthytyped msr)

list_files() {
  if [ "${FAMILY:-0}" = 1 ]; then
    resolve_list "$REPO/scripts/module_family.txt" "$EXAMPLES"
    return
  fi
  # A vanished sapic/ tree would take ~half the corpus with it while
  # parity_corpus.txt kept the denominator plausible, so it is checked rather
  # than left to `find`'s stderr.
  if [ ! -d "$EXAMPLES/sapic" ]; then
    echo "ERROR: $EXAMPLES/sapic does not exist — half this sweep's corpus is missing" >&2
    exit 2
  fi
  find "$EXAMPLES/sapic" -name '*.spthy' | sort
  resolve_list "$REPO/scripts/parity_corpus.txt" "$EXAMPLES"
}

# one <file> <module> — appends one TSV row (sweep_common's sweep_one: the
# module is the unit column, no detail tag; sweep_retry's extra 'retry'
# argument is deliberately ignored, as before).
one() {
  sweep_one "$1" "$2" '' "module-$2-dct30" --derivcheck-timeout=30 -m="$2"
}
sweep_export
sweep_drive module 3 2 "${MODULES[@]}"
