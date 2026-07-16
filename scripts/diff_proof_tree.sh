#!/bin/bash
# Diff a single lemma's proof tree between Haskell and Rust.
#
# Usage: diff_proof_tree.sh <theory.spthy> <lemma> [EXTRA_ENV="VAR=val ..."]
#
# Prints "  <lemma>: N diff lines (HS: H, RS: R)" where H/R are line
# counts of the canonicalized proof trees and N is the diff line count.
#
# Pre-requisites:
#   - Haskell binary built via `stack build` (auto-discovered below).
#   - Rust binary auto-built (`cargo build --release --example dump_proof`)
#     unless TAM_RS_NO_AUTO_BUILD=1 is set.
#   - python3 in PATH.
set -uo pipefail
f="$1"
lemma="$2"
extra_env="${3:-}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
canon="$script_dir/canon_proof_tree.py"

# Locate the HS binary. Search worktree-local .stack-work first; fall back to the
# main worktree's .stack-work (git worktree doesn't copy untracked dirs like
# .stack-work, so isolated agent worktrees won't have it). Final fallback: $PATH.
find_hs_bin() {
    local root="$1"
    local c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        if [ -x "$c" ]; then echo "$c"; return 0; fi
    done
    return 1
}

hs_path="$(find_hs_bin "$repo_root" 2>/dev/null || true)"
if [ -z "$hs_path" ]; then
    # Fall back to main worktree (first entry of `git worktree list --porcelain`).
    main_root="$(git -C "$repo_root" worktree list --porcelain 2>/dev/null | awk '/^worktree/{print $2; exit}')"
    if [ -n "$main_root" ] && [ "$main_root" != "$repo_root" ]; then
        hs_path="$(find_hs_bin "$main_root" 2>/dev/null || true)"
    fi
fi
if [ -z "$hs_path" ]; then
    hs_path="$(command -v tamarin-prover 2>/dev/null || true)"
fi
if [ -z "$hs_path" ]; then
    echo "diff_proof_tree.sh: no HS tamarin-prover binary found" >&2
    exit 2
fi

# Always (re)build dump_proof before measuring — plain `cargo build --release`
# does NOT rebuild examples, which has silently produced stale-binary
# measurements. No-op (<1s) when already fresh. Skip: TAM_RS_NO_AUTO_BUILD=1.
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    if ! cargo build --release --example dump_proof \
            --manifest-path "$repo_root/Cargo.toml" >&2; then
        echo "diff_proof_tree.sh: cargo build --example dump_proof failed" >&2
        exit 2
    fi
fi

rs_path="$repo_root/target/release/examples/dump_proof"
if [ ! -x "$rs_path" ]; then
    rs_path="$repo_root/target/debug/examples/dump_proof"
fi
if [ ! -x "$rs_path" ]; then
    echo "diff_proof_tree.sh: dump_proof not built; run \`cargo build --example dump_proof\` at the repo root" >&2
    exit 2
fi

tmp=$(mktemp -d)
trap "rm -rf $tmp" EXIT

# HS has no built-in deadline; wrap in `timeout`. Mirrors RS-side TAM_PROVE_DEADLINE_MS.
# Seconds = max(60, ms/1000 + 30); default 600. Override via DIFF_HS_TIMEOUT_S.
hs_timeout_s="${DIFF_HS_TIMEOUT_S:-}"
if [ -z "$hs_timeout_s" ]; then
    if [ -n "${TAM_PROVE_DEADLINE_MS:-}" ]; then
        hs_timeout_s=$(( TAM_PROVE_DEADLINE_MS / 1000 + 30 ))
        [ "$hs_timeout_s" -lt 60 ] && hs_timeout_s=60
    else
        hs_timeout_s=600
    fi
fi
timeout --kill-after=5 "$hs_timeout_s" "$hs_path" +RTS -N1 -RTS --prove="$lemma" "$f" 2>/dev/null > "$tmp/hs.out" || true
awk -v lem="^lemma ${lemma}( |\\[|:)" '$0 ~ lem {p=1} p && /^lemma / && !($0 ~ lem) {exit} p' \
    "$tmp/hs.out" | python3 "$canon" > "$tmp/hs.canon"
# RS's TAM_PROVE_DEADLINE_MS is internal-only — doesn't trigger when RS is blocked
# on Maude IPC. Wrap in `timeout` matching the HS deadline. Override via DIFF_RS_TIMEOUT_S.
rs_timeout_s="${DIFF_RS_TIMEOUT_S:-$hs_timeout_s}"
timeout --kill-after=5 "$rs_timeout_s" env $extra_env "$rs_path" "$f" "$lemma" 2>/dev/null | python3 "$canon" > "$tmp/rs.canon"

d=$(diff "$tmp/hs.canon" "$tmp/rs.canon" 2>/dev/null | wc -l || true)
hs_lines=$(wc -l < "$tmp/hs.canon")
rs_lines=$(wc -l < "$tmp/rs.canon")
echo "  $lemma: $d diff lines (HS: $hs_lines, RS: $rs_lines)"
