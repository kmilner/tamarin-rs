#!/usr/bin/env bash
# H16.9: Side-by-side HS↔RS Maude command/response trace for a lemma.
#
# Both engines emit `[hs-maude>]/[hs-maude<]` (HS) and `[maude>]/[maude<]`
# (RS) lines for every Maude command sent and reply received. With
# `TAM_*_DBG_MAUDE_IO=full`, the full text is dumped (no truncation).
# With `TAM_*_DBG_MAUDE_IO_FILTER=<substring>`, only commands matching
# the substring are dumped (e.g. "unify" to skip set/show noise).
#
# Outputs two files (one per engine) and a unified diff.
#
# Usage:
#   diff_maude_io.sh <theory.spthy> <lemma> [filter]
#
# Example:
#   diff_maude_io.sh tamarin-prover/examples/.../foo.spthy resolved1 unify
#     — captures only unify-related commands, diff highlights structural
#     differences in what each engine sends to Maude.

set -euo pipefail

if [ $# -lt 2 ] || [ $# -gt 3 ]; then
    echo "Usage: $0 <theory.spthy> <lemma> [filter]" >&2
    exit 1
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"

theory="$1"
lemma="$2"
filter="${3:-}"

HS_BIN=$(ls "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover 2>/dev/null | head -1)
RS_BIN="$repo_root/target/release/examples/dump_proof"

# Rebuild dump_proof first — plain `cargo build --release` does NOT rebuild
# examples (stale-binary trap). No-op when fresh. Skip: TAM_RS_NO_AUTO_BUILD=1.
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    cargo build --release --example dump_proof \
        --manifest-path "$repo_root/Cargo.toml" >&2 \
        || { echo "Error: cargo build --example dump_proof failed" >&2; exit 1; }
fi

if [ ! -x "$HS_BIN" ]; then echo "Error: HS binary not found"; exit 1; fi
if [ ! -x "$RS_BIN" ]; then echo "Error: RS binary not found"; exit 1; fi

outdir=$(mktemp -d)
trap 'echo "Logs at $outdir"' EXIT

hs_log="$outdir/hs.log"
rs_log="$outdir/rs.log"

echo "[diff_maude] Running HS..." >&2
export TAM_HS_DBG_MAUDE_IO=full
[ -n "$filter" ] && export TAM_HS_DBG_MAUDE_IO_FILTER="$filter"
timeout 180 "$HS_BIN" --prove="$lemma" "$theory" 2>"$hs_log" 1>/dev/null || true
unset TAM_HS_DBG_MAUDE_IO TAM_HS_DBG_MAUDE_IO_FILTER

echo "[diff_maude] Running RS..." >&2
export TAM_DBG_MAUDE_IO=full
[ -n "$filter" ] && export TAM_DBG_MAUDE_IO_FILTER="$filter"
timeout 180 "$RS_BIN" "$theory" "$lemma" 2>"$rs_log" 1>/dev/null || true
unset TAM_DBG_MAUDE_IO TAM_DBG_MAUDE_IO_FILTER

# Normalize: extract only the maude prompt/reply lines, strip engine prefix.
# `|| true` so grep returning empty (no matches) doesn't trigger `set -e`.
(grep -E "^\[hs-maude[><]\]" "$hs_log" || true) | sed 's|^\[hs-maude>\]|>|; s|^\[hs-maude<\][^:]*: *|<|' > "$outdir/hs.maude.norm"
(grep -E "^\[maude[><]\]"    "$rs_log" || true) | sed 's|^\[maude>\]|>|;    s|^\[maude<\][^:]*: *|<|'    > "$outdir/rs.maude.norm"

hs_count=$(wc -l < "$outdir/hs.maude.norm")
rs_count=$(wc -l < "$outdir/rs.maude.norm")

echo
echo "HS Maude calls: $hs_count"
echo "RS Maude calls: $rs_count"
echo

# Show the first N commands side-by-side to see where they diverge.
N="${MAUDE_DIFF_HEAD:-20}"
echo "=== First $N HS commands ==="
head -n "$N" "$outdir/hs.maude.norm"
echo
echo "=== First $N RS commands ==="
head -n "$N" "$outdir/rs.maude.norm"

# Optional: full diff if `MAUDE_DIFF_FULL=1`.
if [ "${MAUDE_DIFF_FULL:-}" = "1" ]; then
    echo
    echo "=== Full diff ==="
    diff "$outdir/hs.maude.norm" "$outdir/rs.maude.norm" || true
fi

echo
echo "Files: $outdir/hs.log, $outdir/rs.log, $outdir/hs.maude.norm, $outdir/rs.maude.norm"
trap - EXIT
