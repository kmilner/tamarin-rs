#!/usr/bin/env bash
# Repository setup.
#
#   ./setup.sh            initialise the tamarin-prover submodule (pristine
#                         upstream checkout at the pinned commit).  This is
#                         all a plain `cargo build` needs: the build embeds
#                         tamarin-prover/data/intruder_variants_{dh,bp}.spthy
#                         at compile time, the web server serves the
#                         submodule's data/ assets, and the example corpus
#                         lives at tamarin-prover/examples/.
#
#   ./setup.sh testing    additionally materialise a PATCHED copy of the
#                         Haskell prover at tamarin-prover-testing/ and build
#                         it with stack.  The parity/test scripts under
#                         scripts/ use that binary as the byte-parity oracle.
#                         The submodule itself is never modified, so it stays
#                         trivially in sync with upstream.
#
# The files in patches/series mirror fixes that are still under upstream
# review. Keeping one patch per PR makes each fix easy to drop after it lands.
# Only the testing oracle needs them; the submodule stays pristine.
set -eu
root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
sub="$root/tamarin-prover"
testdir="$root/tamarin-prover-testing"
series="$root/patches/series"

git -C "$root" submodule update --init tamarin-prover
echo "submodule ready (pristine upstream @ $(git -C "$sub" rev-parse --short HEAD))"

[ "${1:-}" = "testing" ] || exit 0

# Materialise the patched testing tree as a git worktree of the submodule's
# pinned commit: shares the object store (cheap) and keeps git metadata so
# the built binary's version splice resolves.
pinned="$(git -C "$sub" rev-parse HEAD)"
if [ ! -d "$testdir" ]; then
    git -C "$sub" worktree add --detach "$testdir" "$pinned"
fi

# This is a generated worktree. Reset tracked and untracked patch output on
# every run, while retaining ignored .stack-work build artifacts as a durable
# compiler cache.
git -C "$testdir" reset --hard -q "$pinned"
git -C "$testdir" clean -fdq

applied=0
while IFS= read -r name || [ -n "$name" ]; do
    case "$name" in ''|'#'*) continue ;; esac
    patch="$root/patches/$name"
    if [ ! -f "$patch" ]; then
        echo "ERROR: patch listed in patches/series is missing: $name" >&2
        exit 1
    fi
    if git -C "$testdir" apply --reverse --check "$patch" 2>/dev/null; then
        echo "already upstream/applied: $name"
    elif git -C "$testdir" apply --check "$patch" 2>/dev/null; then
        git -C "$testdir" apply "$patch"
        echo "applied: $name"
        applied=$((applied + 1))
    else
        echo "ERROR: $name does not apply cleanly in $testdir." >&2
        echo "Run scripts/bump_submodule.sh --check for a per-patch report." >&2
        exit 1
    fi
done < "$series"
echo "testing tree patched ($applied patch(es))"

echo "building the patched Haskell oracle (first build takes a while)..."
( cd "$testdir" && stack build )
echo "done. scripts/*.sh discover the oracle under tamarin-prover-testing/"
echo "automatically; override with HS_PATH=<binary> if needed."
