#!/bin/bash
# Quick HS<->RS raw --prove parity check for specific theory files, using the
# REPO's Haskell binary (1.13.0 stack build, NOT the 1.12.0 brew one on PATH)
# and this machine's corpus path. Strips only environment-volatile lines.
#
# Usage:
#   parity_check.sh <file.spthy> [file2.spthy ...]
#       file paths may be absolute, repo-relative, or relative to examples/.
# Env:
#   LEMMA=<name>     restrict to a single lemma (passes --prove=<name>)
#   TIMEOUT=120      per-prover wall cap (seconds)
#   RS_BIN, HS_BIN   override binaries
set -uo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HS_BIN="${HS_BIN:-$repo/tamarin-prover-testing/.stack-work/install/x86_64-linux-tinfo6/ec0cb11b1bfcf8776d45e0357bbc6d6ff2077f9222735af22115429c8cdfcef1/9.6.7/bin/tamarin-prover}"
RS_BIN="${RS_BIN:-$repo/target/release/tamarin-rs}"
TIMEOUT="${TIMEOUT:-120}"
prove_arg="--prove"
[ -n "${LEMMA:-}" ] && prove_arg="--prove=$LEMMA"

strip() { grep -vE '^(maude tool|Git revision|Compiled at| *processing time|Linux| checking version|The following|Generated from)' | sed -E 's/[0-9]+\.[0-9]+s//g'; }

resolve() {
  local f="$1"
  [ -f "$f" ] && { echo "$f"; return; }
  [ -f "$repo/$f" ] && { echo "$repo/$f"; return; }
  [ -f "$repo/tamarin-prover/examples/$f" ] && { echo "$repo/tamarin-prover/examples/$f"; return; }
  local hit; hit="$(find "$repo/tamarin-prover/examples" -name "$(basename "$f")" 2>/dev/null | head -1)"
  [ -n "$hit" ] && { echo "$hit"; return; }
  echo ""; return 1
}

fail=0
for raw in "$@"; do
  f="$(resolve "$raw")"
  if [ -z "$f" ]; then echo "MISS  $raw (not found)"; fail=1; continue; fi
  hs=$(mktemp); rs=$(mktemp)
  timeout "$TIMEOUT" "$HS_BIN" "$prove_arg" "$f" 2>/dev/null | strip > "$hs"
  timeout "$TIMEOUT" "$RS_BIN" "$prove_arg" "$f" 2>/dev/null | strip > "$rs"
  n=$(diff "$hs" "$rs" | grep -cE '^[<>]')
  if [ "$n" -eq 0 ]; then echo "MATCH $raw"; else
    echo "DIFF  $raw  ($n diff lines)"; fail=1
    if [ -n "${SHOW:-}" ]; then diff "$hs" "$rs" | head -"${SHOW}"; fi
  fi
  rm -f "$hs" "$rs"
done
exit $fail
