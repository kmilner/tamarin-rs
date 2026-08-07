#!/bin/bash
# -m spthy/spthytyped/msr parity sweep: RS vs HS, translate-only (no proving).
# Corpus: parity_corpus.txt + every examples/sapic/**/*.spthy (deduped).
# A file where BOTH sides fail with the same rc + normalized stderr counts as
# agreement. Documented residuals resolve to LEDGERED via
# scripts/sweep_expected.tsv (per file, or per file+module). FAMILY=1 restricts
# to scripts/module_family.txt.
#
# Stages: parallel pass at TIMEOUT, then a serial retry of ERROR rows at
# RETRY_TIMEOUT (heavy files are load-sensitive).
# Output: TSV rows  <file>\t<module>\t<OK|DIFF|ERROR|LEDGERED>\t<detail>
set -u
. "$(dirname "$0")/sweep_common.sh"
OUT=${OUT:-$REPO/scripts/results/module_sweep.tsv}
RETRY_TIMEOUT=${RETRY_TIMEOUT:-600}
mkdir -p "$(dirname "$OUT")"

list_files() {
  if [ "${FAMILY:-0}" = 1 ]; then
    family_list "$REPO/scripts/module_family.txt" "$EXAMPLES"
    return
  fi
  sed 's/#.*//;/^\s*$/d' "$REPO/scripts/parity_corpus.txt" | sed "s|^|$EXAMPLES/|"
  find "$EXAMPLES/sapic" -name '*.spthy' | sort
}

one() {
  f=$1; m=$2
  d=$(mktemp -d)
  hs_run "$d" "$f" "module-$m-dct30" --derivcheck-timeout=30 -m=$m; hrc=$?
  # An oracle timeout is cached at this cap, so it comes back instantly while
  # the RS side would burn the full cap producing nothing to compare against.
  if [ $hrc -ge 124 ]; then echo -e "$f\t$m\tERROR\ttimeout/kill hs=$hrc rs=skipped" >> "$OUT"; rm -rf "$d"; return; fi
  grun "$RS_BIN" --with-maude="$MAUDE" --derivcheck-timeout=30 -m=$m "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ $rrc -ge 124 ]; then echo -e "$f\t$m\tERROR\ttimeout/kill hs=$hrc rs=$rrc" >> "$OUT"
  elif [ $hrc -ne $rrc ]; then echo -e "$f\t$m\tDIFF\trc hs=$hrc rs=$rrc" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.out") <(norm < "$d/rs.out") >/dev/null; then echo -e "$f\t$m\tDIFF\tstdout" >> "$OUT"
  elif ! diff -q <(norm < "$d/hs.err" | nerr) <(norm < "$d/rs.err" | nerr) >/dev/null; then echo -e "$f\t$m\tDIFF\tstderr" >> "$OUT"
  else echo -e "$f\t$m\tOK\t-" >> "$OUT"; fi
  rm -rf "$d"
}
sweep_export

rs_stale_check
LIST=$(list_files | sort -u)
: > "$OUT"
sweep_banner module_sweep "$(($(echo "$LIST" | grep -c .) * 3))"
echo "$LIST" | grep . | while read -r f; do for m in spthy spthytyped msr; do echo "$f $m"; done; done \
  | xargs -r -P "$JOBS" -n 2 bash -c 'one "$0" "$1"'
sweep_retry "$OUT" 3 "$RETRY_TIMEOUT"
sweep_finish "$OUT" module 3 2
