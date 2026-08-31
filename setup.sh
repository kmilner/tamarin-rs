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
[ -r "$root/scripts/gate_common.sh" ] || {
    echo "ERROR: missing scripts/gate_common.sh" >&2; exit 1; }
. "$root/scripts/gate_common.sh"

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

# Return success only when the generated worktree is exactly the current patch
# series applied to the pin. A temporary index stages its actual state, then
# removes the patches in reverse order; this handles overlapping patches while
# also detecting stray tracked or untracked files. Ignored .stack-work output
# never enters the index.
testing_tree_current() {
    [ "$(git -C "$testdir" rev-parse HEAD)" = "$pinned" ] || return 1
    local state_index name i
    local -a patch_files=()
    state_index=$(mktemp) || return 1
    rm -f "$state_index"
    if ! GIT_INDEX_FILE="$state_index" git -C "$testdir" read-tree "$pinned" \
            || ! GIT_INDEX_FILE="$state_index" git -C "$testdir" add -A -- .; then
        rm -f "$state_index"
        return 1
    fi
    while IFS= read -r name || [ -n "$name" ]; do
        case "$name" in ''|'#'*) continue ;; esac
        patch_files+=("$root/patches/$name")
    done < "$series"
    for ((i=${#patch_files[@]} - 1; i >= 0; i--)); do
        if ! GIT_INDEX_FILE="$state_index" git -C "$testdir" \
                apply --cached --reverse "${patch_files[$i]}" 2>/dev/null; then
            rm -f "$state_index"
            return 1
        fi
    done
    local status=0
    GIT_INDEX_FILE="$state_index" git -C "$testdir" \
        diff-index --cached --quiet "$pinned" -- || status=$?
    rm -f "$state_index"
    return "$status"
}

tree_current=0
if testing_tree_current; then
    tree_current=1
    echo "testing tree already has the current patch series"
else
    # This is a generated worktree. Reset tracked and untracked patch output,
    # while retaining ignored .stack-work build artifacts as a durable cache.
    git -C "$testdir" reset --hard -q "$pinned"
    git -C "$testdir" clean -fdq
fi

applied=0
while IFS= read -r name || [ -n "$name" ]; do
    case "$name" in ''|'#'*) continue ;; esac
    patch="$root/patches/$name"
    if [ ! -f "$patch" ]; then
        echo "ERROR: patch listed in patches/series is missing: $name" >&2
        exit 1
    fi
    if [ "$tree_current" = 1 ]; then
        applied=$((applied + 1))
    elif git -C "$testdir" apply --reverse --check "$patch" 2>/dev/null; then
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

install_root="$(cd "$testdir" && stack path --local-install-root)"
oracle="$install_root/bin/tamarin-prover"
patch_fp=$(patch_series_fingerprint "$root") || {
    echo "ERROR: cannot fingerprint patches/series" >&2; exit 1; }

# A no-op setup must not relink the timestamp-bearing executable and thereby
# manufacture a new cache fingerprint. Reuse it only when both the generated
# source tree and its complete setup attestation are current.
build_needed=1
stamp="${oracle}.tamarin-rs-oracle"
if [ "$tree_current" = 1 ] && [ -x "$oracle" ] && [ -r "$stamp" ]; then
    stamp_pin=$(sed -n 's/^pin=//p' "$stamp")
    stamp_series=$(sed -n 's/^patch_series_sha256=//p' "$stamp")
    stamp_binary=$(sed -n 's/^binary_sha256=//p' "$stamp")
    binary_fp=$(binary_sha256 "$oracle")
    if [ "$stamp_pin" = "$pinned" ] && [ "$stamp_series" = "$patch_fp" ] \
            && [ "$stamp_binary" = "$binary_fp" ]; then
        build_needed=0
        echo "patched Haskell oracle is already current"
    fi
fi
if [ "$build_needed" = 1 ]; then
    echo "building the patched Haskell oracle (first build takes a while)..."
    ( cd "$testdir" && stack build )
    [ -x "$oracle" ] || {
        echo "ERROR: stack build produced no oracle at $oracle" >&2; exit 1; }
    binary_fp=$(binary_sha256 "$oracle")
fi

write_oracle_stamp() {
    local target=$1 tmp="${1}.tmp.$$"
    {
        printf 'pin=%s\n' "$pinned"
        printf 'patch_series_sha256=%s\n' "$patch_fp"
        printf 'binary_sha256=%s\n' "$binary_fp"
    } > "$tmp"
    mv "$tmp" "$target"
}
write_oracle_stamp "$stamp"
# Fixed-location attestation lets byte-identical HS_PATH copies be verified
# without requiring callers to copy a sidecar alongside the executable.
write_oracle_stamp "$testdir/.stack-work/tamarin-rs-oracle"
echo "done. scripts/*.sh discover the oracle under tamarin-prover-testing/"
echo "automatically; override with HS_PATH=<binary> if needed."
