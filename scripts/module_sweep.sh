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

one() {
  local f=$1 m=$2 d hrc rrc nc io
  # No tmpdir means every redirection below would target /, so bail and let
  # sweep_finish's row-count check report the row that never landed.
  d=$(mktemp -d) || return
  hs_run "$d" "$f" "module-$m-dct30" --derivcheck-timeout=30 -m="$m"; hrc=$?
  # A broken environment is diagnosed before the cap is blamed for it: an
  # unusable maude both aborts and hangs, and "timeout" would be the wrong
  # story (and a ledgerable one).
  if infra_abort "$d/hs.err"; then row "$f" "$m" NO-COMPARE "infra-abort hs (rs not run) hs=$hrc"; rm -rf "$d"; return; fi
  # An oracle timeout is cached at this cap, so it comes back instantly while
  # the RS side would burn the full cap producing nothing to compare against.
  if [ "$hrc" -ge 124 ]; then row "$f" "$m" ERROR "timeout/kill hs=$hrc rs=skipped"; rm -rf "$d"; return; fi
  grun "$RS_BIN" --with-maude="$MAUDE" --derivcheck-timeout=30 -m="$m" "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ "$rrc" -ge 124 ]; then row "$f" "$m" ERROR "timeout/kill hs=$hrc rs=$rrc"
  elif nc=$(nocompare_check "$hrc" "$rrc" "$d" "$d/hs.out" "$d/rs.out"); then row "$f" "$m" NO-COMPARE "$nc"
  elif [ "$hrc" -ne "$rrc" ]; then row "$f" "$m" DIFF "rc hs=$hrc rs=$rrc"
  elif ! io=$(io_diff "$d"); then row "$f" "$m" DIFF "$io"
  else row "$f" "$m" OK -; fi
  rm -rf "$d"
}
sweep_export

rs_stale_check
LIST=$(list_files) || exit 2
LIST=$(sort -u <<< "$LIST")
: > "$OUT"
sweep_banner module_sweep "$(( $(grep -c . <<< "$LIST") * ${#MODULES[@]} ))"
# -d '\n': one field per argument, with xargs' quote and backslash processing
# off, so nothing about a path's spelling can split or reshape it. Each job
# takes a (file, module) pair, hence two lines in and -n 2.
while IFS= read -r f; do
  for m in "${MODULES[@]}"; do printf '%s\n%s\n' "$f" "$m"; done
done <<< "$LIST" | xargs -r -d '\n' -P "$JOBS" -n 2 bash -uc 'one "$0" "$1"'
sweep_retry "$OUT" 3
sweep_finish "$OUT" module 3 2
