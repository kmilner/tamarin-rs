#!/usr/bin/env bash
# Bump the tamarin-prover submodule to a newer upstream commit and rebase
# patches/tamarin-prover-fixes.patch onto the new pin.
#
# Usage:
#   scripts/bump_submodule.sh [<ref>]        bump to <ref> (default: origin/develop)
#   scripts/bump_submodule.sh --check [<ref>]
#                                            dry run: report whether the patch
#                                            rebases cleanly onto <ref>; changes
#                                            nothing
#   scripts/bump_submodule.sh --continue     resume after resolving conflicts in
#                                            tamarin-prover-rebase/
#   scripts/bump_submodule.sh --abort        discard an in-progress bump
#
# Environment:
#   SKIP_BUILD=1   skip the oracle stack build and cargo release build
#
# The patch is rebased in a scratch worktree (tamarin-prover-rebase/) with
# `git apply -3`. Conflicts stop the script for manual resolution; rerun with
# --continue afterwards. The rebased patch is regenerated with `git diff`,
# verified against the pristine new pin, and installed. The script then stages
# the new gitlink and patch, resets + re-patches + rebuilds the testing oracle
# via ./setup.sh testing, rebuilds the Rust binary (it embeds submodule data
# files at compile time), and archives the gate caches (their entries key on
# oracle output, so a new oracle silently invalidates them). It never commits:
# run the batch and web gates first (it prints the checklist).
set -eu

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
sub="$root/tamarin-prover"
testdir="$root/tamarin-prover-testing"
rebasedir="$root/tamarin-prover-rebase"
patch="$root/patches/tamarin-prover-fixes.patch"

tmp="$(mktemp -d)"
remove_worktree_on_exit=0
cleanup() {
    rm -rf "$tmp"
    if [ "$remove_worktree_on_exit" = 1 ]; then
        git -C "$sub" worktree remove --force "$rebasedir" 2>/dev/null || true
    fi
}
trap cleanup EXIT

die() { echo "ERROR: $*" >&2; exit 1; }

patch_files() { sed -n 's|^diff --git a/\(.*\) b/.*|\1|p' "$1" | sort; }

indent_list() { printf '%s\n' "$2" | sed "1s/^/$1/;2,\$s/^/  /"; }

# Regenerate the patch from the (clean or conflict-resolved) rebase worktree,
# verify it applies to the pristine new pin, install it, and finish the bump.
finalize() {
    new="$(git -C "$rebasedir" rev-parse HEAD)"
    old="$(git -C "$root" rev-parse HEAD:tamarin-prover)"
    oldshort="$(git -C "$sub" rev-parse --short "$old")"
    newshort="$(git -C "$sub" rev-parse --short "$new")"

    git -C "$rebasedir" add -A
    if git -C "$rebasedir" diff --cached --check | grep -q 'leftover conflict marker'; then
        die "unresolved conflict markers remain (git -C tamarin-prover-rebase diff --cached --check); resolve, then rerun --continue"
    fi

    git -C "$rebasedir" diff --cached > "$tmp/new.patch"
    if [ ! -s "$tmp/new.patch" ]; then
        die "rebased patch is empty — upstream has merged everything. Finish by hand: drop the patch, simplify setup.sh, bump the gitlink."
    fi

    patch_files "$patch"          > "$tmp/files.old"
    patch_files "$tmp/new.patch"  > "$tmp/files.new"
    merged="$(comm -23 "$tmp/files.old" "$tmp/files.new")"
    added="$(comm -13 "$tmp/files.old" "$tmp/files.new")"
    oldn="$(wc -l < "$tmp/files.old")"
    newn="$(wc -l < "$tmp/files.new")"

    # The regenerated patch must apply to the PRISTINE new pin (never trust a
    # patch verified only against the tree it was diffed from).
    git -C "$rebasedir" reset --hard -q HEAD
    git -C "$rebasedir" clean -fdq
    if ! git -C "$rebasedir" apply --check "$tmp/new.patch"; then
        cp "$tmp/new.patch" "$patch.rejected"
        die "regenerated patch does not apply to pristine $newshort (kept at $patch.rejected)"
    fi
    cp "$tmp/new.patch" "$patch"

    git -C "$sub" worktree remove --force "$rebasedir"
    git -C "$sub" checkout -q --detach "$new"
    git -C "$root" add tamarin-prover "$patch"

    if [ -d "$testdir" ]; then
        git -C "$testdir" reset --hard -q "$new"
        git -C "$testdir" clean -fdq
    fi

    # Gate caches key on oracle/theory-file content only — after an oracle
    # change they are silently stale, so archive them rather than trusting
    # any freshness heuristic.
    for c in .hs_file_cache .web_hs_cache; do
        d="$root/scripts/$c"
        [ -d "$d" ] || continue
        dest="$d.pre-bump-$oldshort"
        [ -e "$dest" ] && dest="$dest.$(date +%Y%m%d%H%M%S)"
        mv "$d" "$dest"
        echo "archived scripts/$c -> scripts/$(basename "$dest")"
    done

    if [ "${SKIP_BUILD:-0}" != 1 ]; then
        "$root/setup.sh" testing
        ( cd "$root" && cargo build --release )
    fi

    echo
    echo "== bumped tamarin-prover $oldshort -> $newshort =="
    echo "patch: $oldn -> $newn files"
    [ -n "$merged" ] && indent_list 'merged upstream (dropped from patch): ' "$merged"
    [ -n "$added" ] && indent_list 'NEW in patch (expected only if you added files while resolving): ' "$added"
    if git -C "$sub" diff --name-only "$old" "$new" -- data/ | grep -q .; then
        echo "NOTE: data/ files changed upstream — the Rust binary embeds them, expect legitimate output changes."
    fi
    [ "${SKIP_BUILD:-0}" != 1 ] || echo "builds skipped (SKIP_BUILD=1): run ./setup.sh testing && cargo build --release"
    cat <<EOF
staged (NOT committed): tamarin-prover gitlink + patches/$(basename "$patch")
Verify before committing:
  1. RESULTS_TSV=scripts/results/fullgate_bump.tsv scripts/corpus_file_diff.sh   # full batch gate, cold cache
     - heavy files (BP_IBS_2/3, fm24 C8, alethea_votingphase_malS_abstain) need FILE_TIMEOUT>=600 cold
     - retries short-circuit on cached markers: find scripts/.hs_file_cache -name '*.timeout' -delete first
  2. Web ladder: guards -> family files -> scripts/websweep_residual.txt (regenerates scripts/.web_hs_cache)
  3. git commit -m "chore: bump tamarin-prover submodule to $newshort"
EOF
}

mode=bump ref=origin/develop
case "${1:-}" in
    --continue) mode=continue ;;
    --abort)    mode=abort ;;
    --check)    mode=check; ref="${2:-origin/develop}" ;;
    -h|--help)  sed -n '2,${/^#/!q;s/^# \{0,1\}//p;}' "$0"; exit 0 ;;
    --*)        die "unknown option: $1" ;;
    ?*)         ref="$1" ;;
esac

case "$mode" in
abort)
    if [ -d "$rebasedir" ]; then
        git -C "$sub" worktree remove --force "$rebasedir" \
            || { rm -rf "$rebasedir"; git -C "$sub" worktree prune; }
        echo "aborted: rebase worktree removed (patch and gitlink untouched)"
    else
        echo "no bump in progress"
    fi
    ;;

continue)
    [ -d "$rebasedir" ] || die "no bump in progress ($rebasedir missing)"
    finalize
    ;;

bump|check)
    [ -f "$patch" ] || die "patch not found: $patch"
    [ -e "$sub/.git" ] || die "submodule not initialised — run ./setup.sh first"
    [ -d "$rebasedir" ] && die "a bump is already in progress — rerun with --continue or --abort"

    old="$(git -C "$root" rev-parse HEAD:tamarin-prover)"
    if [ "$mode" = bump ]; then
        [ -z "$(git -C "$root" status --porcelain -- tamarin-prover patches)" ] \
            || die "uncommitted changes under tamarin-prover/patches — commit or reset first"
        [ "$(git -C "$sub" rev-parse HEAD)" = "$old" ] \
            || die "submodule checkout does not match the recorded pin — run ./setup.sh first"
    fi

    git -C "$sub" fetch origin
    new="$(git -C "$sub" rev-parse --verify "$ref^{commit}")" || die "cannot resolve '$ref' in the submodule"

    if [ "$mode" = bump ] && [ "$new" = "$old" ]; then
        echo "already at $ref ($(git -C "$sub" rev-parse --short "$new")) — nothing to do"
        exit 0
    fi

    echo "== rebasing patch: $(git -C "$sub" rev-parse --short "$old") -> $(git -C "$sub" rev-parse --short "$new") ($ref, $(git -C "$sub" rev-list --count "$old..$new") new commits) =="
    overlap="$(comm -12 <(patch_files "$patch") <(git -C "$sub" diff --name-only "$old" "$new" | sort))"
    [ -n "$overlap" ] && indent_list 'upstream touched patched files (conflicts, if any, will be here): ' "$overlap"

    git -C "$sub" worktree add -q --detach "$rebasedir" "$new"
    [ "$mode" = check ] && remove_worktree_on_exit=1

    if git -C "$rebasedir" apply -3 "$patch" 2>"$tmp/apply.err"; then
        if [ "$mode" = check ]; then
            echo "OK: patch rebases cleanly onto $(git -C "$sub" rev-parse --short "$new") (nothing changed; run without --check to bump)"
            exit 0
        fi
        finalize
    else
        conflicts="$(git -C "$rebasedir" diff --name-only --diff-filter=U)"
        if [ -z "$conflicts" ]; then
            cat "$tmp/apply.err" >&2
            remove_worktree_on_exit=1
            die "git apply -3 failed outright (not a content conflict) — see errors above"
        fi
        indent_list 'CONFLICTS in: ' "$conflicts"
        [ "$mode" = check ] && exit 2
        cat <<EOF
Resolve the <<<<<<< markers in tamarin-prover-rebase/, then:
  scripts/bump_submodule.sh --continue
or discard with:
  scripts/bump_submodule.sh --abort
EOF
        exit 2
    fi
    ;;
esac
