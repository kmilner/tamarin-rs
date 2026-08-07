#!/bin/bash
# --output-json byte-parity + --output-dot label/count parity over stored-proof
# theories. No --prove: closeTheory replays stored proofs, so *_analyzed.spthy
# files yield real traces. JSON compared byte-for-byte; DOT compared on
# digraph-label lines only (body dialect is an accepted divergence, documented
# in crates/tamarin-server/src/handlers/dot.rs). Documented residuals resolve
# to LEDGERED via scripts/sweep_expected.tsv. FAMILY=1 restricts to
# scripts/json_family.txt (paths relative to case-studies-regression/).
set -u
. "$(dirname "$0")/sweep_common.sh"
OUT=${OUT:-$REPO/scripts/results/json_sweep.tsv}
mkdir -p "$(dirname "$OUT")"

list_files() {
  if [ "${FAMILY:-0}" = 1 ]; then
    sed 's/#.*//;/^\s*$/d' "$REPO/scripts/json_family.txt" | sed "s|^|$CSR/|" \
      | while read -r f; do
          if [ -f "$f" ]; then echo "$f"; else echo "WARNING: family entry missing: $f" >&2; fi
        done
    return
  fi
  find "$CSR" -name '*_analyzed.spthy' | sort
}

one() {
  f=$1
  d=$(mktemp -d)
  hs_run "$d" "$f" "json+dot" --output-json="$d/hs.json" --output-dot="$d/hs.dot"; hrc=$?
  grun "$RS_BIN" --with-maude="$MAUDE" --output-json="$d/rs.json" --output-dot="$d/rs.dot" "$f" > /dev/null 2> "$d/rs.err"; rrc=$?
  if [ $hrc -ge 124 ] || [ $rrc -ge 124 ]; then echo -e "$f\tERROR\ttimeout/kill hs=$hrc rs=$rrc" >> "$OUT"
  elif [ $hrc -ne $rrc ]; then echo -e "$f\tDIFF\trc hs=$hrc rs=$rrc" >> "$OUT"
  elif [ $hrc -ne 0 ]; then echo -e "$f\tOK\tboth-fail rc=$hrc" >> "$OUT"
  elif ! cmp -s "$d/hs.json" "$d/rs.json"; then echo -e "$f\tDIFF\tjson" >> "$OUT"
  elif ! diff -q <(grep '^digraph ' "$d/hs.dot") <(grep '^digraph ' "$d/rs.dot") >/dev/null; then
    echo -e "$f\tDIFF\tdot-labels" >> "$OUT"
  else echo -e "$f\tOK\t-" >> "$OUT"; fi
  rm -rf "$d"
}
export -f one grun norm hs_run hs_fingerprint
export HS_BIN RS_BIN MAUDE OUT TIMEOUT HS_CACHE

rs_stale_check
LIST=$(list_files | sort -u)
: > "$OUT"
sweep_banner json_sweep "$(echo "$LIST" | wc -l)"
echo "$LIST" | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
sweep_finish "$OUT" json 2
