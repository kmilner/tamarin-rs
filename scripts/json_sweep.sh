#!/bin/bash
# --output-json + --output-dot byte-parity over stored-proof theories. No
# --prove: closeTheory replays stored proofs, so *_analyzed.spthy files yield
# real traces. BOTH documents are compared byte-for-byte — the dot body is a
# faithful `showDot` render (crates/tamarin-theory/src/constraint/system/
# dot_showdot.rs), so nothing about it is exempt; stdout and stderr
# compared normalized on every row, so a warning only one side prints under
# these flags cannot hide. A row where neither side analysed the theory is
# NO-COMPARE (see sweep_common.sh). Documented residuals resolve
# to LEDGERED via scripts/sweep_expected.tsv. FAMILY=1 restricts to
# scripts/json_family.txt (paths relative to case-studies-regression/).
#
# Stages: parallel pass at TIMEOUT, then a serial retry of ERROR rows at
# RETRY_TIMEOUT (heavy files are load-sensitive).
set -u
. "$(dirname "$0")/sweep_common.sh"
sweep_out "$REPO/scripts/results/json_sweep.tsv"

list_files() {
  if [ "${FAMILY:-0}" = 1 ]; then
    resolve_list "$REPO/scripts/json_family.txt" "$CSR"
    return
  fi
  find "$CSR" -name '*_analyzed.spthy' | sort
}

one() {
  local f=$1 d hrc rrc nc io
  # No tmpdir means every redirection below would target /, so bail and let
  # sweep_finish's row-count check report the row that never landed.
  d=$(mktemp -d) || return
  # --derivcheck-timeout=30 matches every other gate (pe/module sweeps,
  # corpus_file_diff). At HS's 5s default its Maude-backed derivation check
  # expires on theories RS finishes, which swaps the wf report's whole
  # "Derivation Checks" section for a timeout notice — a divergence the cap
  # manufactures rather than one the flags expose.
  hs_run "$d" "$f" "json+dot-dct30" --derivcheck-timeout=30 \
    --output-json="$d/hs.json" --output-dot="$d/hs.dot"; hrc=$?
  # A broken environment is diagnosed before the cap is blamed for it: an
  # unusable maude both aborts and hangs, and "timeout" would be the wrong
  # story (and a ledgerable one).
  if infra_abort "$d/hs.err"; then row "$f" NO-COMPARE "infra-abort hs (rs not run) hs=$hrc"; rm -rf "$d"; return; fi
  # An oracle timeout is cached at this cap, so it comes back instantly while
  # the RS side would burn the full cap producing nothing to compare against.
  if [ "$hrc" -ge 124 ]; then row "$f" ERROR "timeout/kill hs=$hrc rs=skipped"; rm -rf "$d"; return; fi
  grun "$RS_BIN" --with-maude="$MAUDE" --derivcheck-timeout=30 \
    --output-json="$d/rs.json" --output-dot="$d/rs.dot" "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ "$rrc" -ge 124 ]; then row "$f" ERROR "timeout/kill hs=$hrc rs=$rrc"
  # nocompare_check also fences off the both-fail branch below: a shared rc with
  # nothing printed on either side is its no-output family, not agreement.
  elif nc=$(nocompare_check "$hrc" "$rrc" "$d" "$d/hs.json" "$d/rs.json"); then row "$f" NO-COMPARE "$nc"
  elif [ "$hrc" -ne "$rrc" ]; then row "$f" DIFF "rc hs=$hrc rs=$rrc"
  # A shared nonzero rc is a matching failure, not parity: neither side wrote a
  # document, so the only evidence either produced is what it printed.
  elif [ "$hrc" -ne 0 ] && ! io=$(io_diff "$d"); then row "$f" DIFF "both-fail-$io rc=$hrc"
  elif [ "$hrc" -ne 0 ]; then row "$f" OK "both-fail rc=$hrc, stdout+stderr identical"
  elif ! cmp -s "$d/hs.json" "$d/rs.json"; then row "$f" DIFF json
  elif ! cmp -s "$d/hs.dot" "$d/rs.dot"; then row "$f" DIFF dot
  elif ! io=$(io_diff "$d"); then row "$f" DIFF "$io"
  else row "$f" OK -; fi
  rm -rf "$d"
}
sweep_export
sweep_drive json 2
