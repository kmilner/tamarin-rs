#!/bin/bash
# Run diff_proof_tree.sh across a hand-picked corpus and tally PASS/FAIL.
# Sanity check for HS↔Rust proof-tree structural match outside the in-test
# probe.  Use the cargo test (corpus_proof_skeleton_match_probe) for the
# canonical metric — this script is for quick local sweeps.
#
# Usage: corpus_diff_proof_trees.sh
set -uo pipefail
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
diff_tree="$script_dir/diff_proof_tree.sh"

cd "$repo_root"

PASS=0
FAIL=0
declare -a fails
for f in tamarin-prover/examples/Tutorial.spthy \
         tamarin-prover/examples/csf12/KAS2_eCK.spthy \
         tamarin-prover/examples/csf12/KAS2_original.spthy \
         tamarin-prover/examples/classic/NSPK3.spthy \
         tamarin-prover/examples/classic/NSLPK3.spthy \
         tamarin-prover/examples/classic/NSLPK3_untagged.spthy \
         tamarin-prover/examples/loops/TESLA_Scheme1.spthy \
         tamarin-prover/examples/loops/Minimal_Crypto_API.spthy; do
    [ -f "$f" ] || continue
    for lem in $(grep "^lemma " "$f" 2>/dev/null | awk -F'[ :]' '{print $2}'); do
        line=$(timeout 180 bash "$diff_tree" "$f" "$lem" 2>/dev/null)
        diff_lines=$(echo "$line" | awk '{print $2}')
        if [ "$diff_lines" = "0" ]; then
            PASS=$((PASS+1))
        else
            FAIL=$((FAIL+1))
            fails+=("$f::$lem: $line")
        fi
    done
done
echo "PASS: $PASS"
echo "FAIL: $FAIL"
for x in "${fails[@]}"; do echo "  $x"; done
