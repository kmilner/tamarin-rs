#!/usr/bin/env bash
# H16.4: Compare apply_eq_store call counts per labeled site between
# HS and RS for a given lemma. Helps find divergences in solver flow
# (which sites fire more/fewer times in RS vs HS).
#
# Usage:
#   diff_aes_calls.sh <theory.spthy> <lemma>
#
# Outputs per-label count table:
#   Label                                    | HS  | RS  | Diff
#   addEqs.single-unifier@solveTermEqs       |  52 |  83 | +31
#   foreachDisj:simpAbstractFun@solveTermEqs |  41 |  90 | +49
#   ...

set -euo pipefail

if [ $# -ne 2 ]; then
    echo "Usage: $0 <theory.spthy> <lemma>" >&2
    exit 1
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"

theory="$1"
lemma="$2"

# Locate HS + RS binaries.
HS_BIN=$(ls "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover 2>/dev/null | head -1)
RS_BIN="$repo_root/target/release/examples/dump_proof"

# Rebuild dump_proof first — plain `cargo build --release` does NOT rebuild
# examples (stale-binary trap). No-op when fresh. Skip: TAM_RS_NO_AUTO_BUILD=1.
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    cargo build --release --example dump_proof \
        --manifest-path "$repo_root/Cargo.toml" >&2 \
        || { echo "Error: cargo build --example dump_proof failed" >&2; exit 1; }
fi

if [ ! -x "$HS_BIN" ]; then
    echo "Error: HS binary not found ($HS_BIN)" >&2
    exit 1
fi
if [ ! -x "$RS_BIN" ]; then
    echo "Error: RS binary not found ($RS_BIN)" >&2
    exit 1
fi

tmphs=$(mktemp)
tmprs=$(mktemp)
trap 'rm -f "$tmphs" "$tmprs"' EXIT

echo "[diff_aes] Running HS..." >&2
timeout 120 env \
    TAM_HS_DBG_APPLY_EQ_STORE=1 \
    TAM_HS_DBG_APPLY_EQ_STORE_FILTER=substantive \
    "$HS_BIN" --prove="$lemma" "$theory" 2>/dev/null 1>"$tmphs"

echo "[diff_aes] Running RS..." >&2
timeout 120 env \
    TAM_RS_DBG_APPLY_EQ_STORE=1 \
    TAM_RS_DBG_APPLY_EQ_STORE_FILTER=substantive \
    "$RS_BIN" "$theory" "$lemma" 2>"$tmprs" >/dev/null

# Normalize HS labels: extract `site=...` part, strip trailing.
# Normalize RS labels: strip `crates/tamarin-theory/src/` prefix from
# file path so labels are short; map to HS canonical form where possible.
canonicalize_rs() {
    # RS site format: crates/tamarin-theory/src/tools/equation_store.rs:LINE@<label>
    # Map to HS canonical form using the @<label> suffix (which is
    # robust to line number changes).
    sed -E 's|^crates/tamarin-theory/src/||;
            s|tools/equation_store\.rs:[0-9]+@simpAbstractFun@|foreachDisj:simpAbstractFun@|;
            s|tools/equation_store\.rs:[0-9]+@simpIdentify@|foreachDisj:simpIdentify@|;
            s|tools/equation_store\.rs:[0-9]+@simpAbstractName@|foreachDisj:simpAbstractName@|;
            s|tools/equation_store\.rs:[0-9]+@simpSingleton@|foreachDisj:simpSingleton@|;
            s|tools/equation_store\.rs:[0-9]+@simpAbstractSortedVar@|foreachDisj:simpAbstractSortedVar@|;
            s|tools/equation_store\.rs:[0-9]+@|addEqs.single-unifier@|;
            s|constraint/solver/sources\.rs:[0-9]+@|conjoinRefilter@|'
}

hs_counts=$(grep "hs-aes-tick" "$tmphs" \
    | sed 's|^.*site=||; s/ conj=.*//' \
    | sort | uniq -c | sort -rn)
rs_counts=$(grep "rs-aes-tick" "$tmprs" \
    | sed 's|^.*site=||; s/ conj=.*//' \
    | canonicalize_rs \
    | sort | uniq -c | sort -rn)

# Combine for side-by-side output.
{
    echo "$hs_counts" | awk '{
        n=$1
        $1=""
        sub(/^[ \t]+/, "")
        print "HS\t" n "\t" $0
    }'
    echo "$rs_counts" | awk '{
        n=$1
        $1=""
        sub(/^[ \t]+/, "")
        print "RS\t" n "\t" $0
    }'
} | awk -F'\t' '
{
    if ($1 == "HS") hs[$3] = $2
    if ($1 == "RS") rs[$3] = $2
}
END {
    # Collect all unique labels.
    for (k in hs) keys[k] = 1
    for (k in rs) keys[k] = 1
    n = 0
    for (k in keys) {
        h = (k in hs) ? hs[k] : 0
        r = (k in rs) ? rs[k] : 0
        d = r - h
        sign = (d > 0) ? "+" : ""
        n++
        items[n] = sprintf("%5d | %5d | %s%d\t%s", h, r, sign, d, k)
        absdiff[n] = (d < 0) ? -d : d
    }
    # Sort by absolute diff descending.
    for (i = 1; i <= n; i++) for (j = i+1; j <= n; j++)
        if (absdiff[j] > absdiff[i]) {
            tmp = items[i]; items[i] = items[j]; items[j] = tmp
            tmp = absdiff[i]; absdiff[i] = absdiff[j]; absdiff[j] = tmp
        }
    printf "  HS  |  RS   | Diff\tLabel\n"
    printf "------+-------+-----\t-----\n"
    for (i = 1; i <= n; i++) print items[i]
}'
