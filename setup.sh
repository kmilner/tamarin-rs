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
# The patch (patches/tamarin-prover-fixes.patch) carries local fixes the port
# is byte-compared against that are not yet merged upstream: fresh-variable
# canonicalisation in msubstToLSubstVFresh, stored-formula normalisation and
# gconj idempotence, the Iff expansion fix, and the solver trace
# instrumentation used by the diff harnesses.  Only the testing oracle needs
# it; nothing in the patch affects the web assets or the corpus.
set -eu
root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
sub="$root/tamarin-prover"
testdir="$root/tamarin-prover-testing"
patch="$root/patches/tamarin-prover-fixes.patch"

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
if git -C "$testdir" apply --reverse --check "$patch" 2>/dev/null; then
    echo "testing tree already patched"
elif git -C "$testdir" apply --check "$patch" 2>/dev/null; then
    git -C "$testdir" apply "$patch"
    echo "patched testing tree ($(basename "$patch"))"
else
    echo "ERROR: patch neither applies nor is already applied in $testdir." >&2
    echo "Reset it with:  git -C tamarin-prover-testing checkout -- . \\" >&2
    echo "                && git -C tamarin-prover-testing clean -fd    " >&2
    exit 1
fi

echo "building the patched Haskell oracle (first build takes a while)..."
( cd "$testdir" && stack build )
echo "done. scripts/*.sh discover the oracle under tamarin-prover-testing/"
echo "automatically; override with HS_PATH=<binary> if needed."
