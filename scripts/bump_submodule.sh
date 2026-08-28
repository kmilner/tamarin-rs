#!/usr/bin/env bash
# Bump the tamarin-prover submodule while preserving the per-PR patch series.
#
# Usage:
#   scripts/bump_submodule.sh [<ref>]           bump (default: origin/develop)
#   scripts/bump_submodule.sh --check [<ref>]   check only; change nothing
#
# Environment:
#   SKIP_BUILD=1   skip rebuilding the Haskell oracle and Rust release binary
#
# Each entry in patches/series is tried independently and in order. A patch
# whose reverse applies is reported as already upstream; remove that entry and
# file after confirming its PR landed. A conflicting patch is named precisely
# and must be refreshed from its PR before retrying the bump.
set -eu

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
sub="$root/tamarin-prover"
testdir="$root/tamarin-prover-testing"
rebasedir="$root/tamarin-prover-rebase"
series="$root/patches/series"
tmp="$(mktemp -d)"

cleanup() {
    if [ -d "$rebasedir" ]; then
        git -C "$sub" worktree remove --force "$rebasedir" 2>/dev/null || true
    fi
    rm -rf "$tmp"
}
trap cleanup EXIT

die() { echo "ERROR: $*" >&2; exit 1; }

apply_series() {
    tree="$1"
    : > "$tmp/applied"
    : > "$tmp/upstream"
    while IFS= read -r name || [ -n "$name" ]; do
        case "$name" in ''|'#'*) continue ;; esac
        patch="$root/patches/$name"
        [ -f "$patch" ] || die "patch listed in patches/series is missing: $name"
        if git -C "$tree" apply --reverse --check "$patch" 2>/dev/null; then
            echo "$name" >> "$tmp/upstream"
            echo "already upstream: $name"
        elif git -C "$tree" apply --check "$patch" 2>/dev/null; then
            git -C "$tree" apply "$patch"
            echo "$name" >> "$tmp/applied"
            echo "applies cleanly:  $name"
        elif git -C "$tree" apply -3 "$patch" 2>"$tmp/apply.err"; then
            echo "$name" >> "$tmp/applied"
            echo "applies three-way: $name"
        else
            cat "$tmp/apply.err" >&2
            conflicts="$(git -C "$tree" diff --name-only --diff-filter=U)"
            [ -z "$conflicts" ] || printf 'conflicts:\n%s\n' "$conflicts" >&2
            die "$name no longer applies; refresh this patch from its upstream PR"
        fi
    done < "$series"
}

mode=bump
ref=origin/develop
case "${1:-}" in
    --check) mode=check; ref="${2:-origin/develop}" ;;
    -h|--help) sed -n '2,${/^#/!q;s/^# \{0,1\}//p;}' "$0"; exit 0 ;;
    --*) die "unknown option: $1" ;;
    ?*) ref="$1" ;;
esac

[ -f "$series" ] || die "missing patch series: $series"
[ -e "$sub/.git" ] || die "submodule not initialised — run ./setup.sh first"
[ ! -d "$rebasedir" ] || die "scratch worktree already exists: $rebasedir"

old="$(git -C "$root" rev-parse HEAD:tamarin-prover)"
if [ "$mode" = bump ]; then
    [ -z "$(git -C "$root" status --porcelain -- tamarin-prover patches)" ] \
        || die "uncommitted changes under tamarin-prover/patches — commit or reset first"
    [ "$(git -C "$sub" rev-parse HEAD)" = "$old" ] \
        || die "submodule checkout does not match the recorded pin — run ./setup.sh first"
fi

git -C "$sub" fetch origin
new="$(git -C "$sub" rev-parse --verify "$ref^{commit}")" \
    || die "cannot resolve '$ref' in the submodule"
oldshort="$(git -C "$sub" rev-parse --short "$old")"
newshort="$(git -C "$sub" rev-parse --short "$new")"

git -C "$sub" worktree add -q --detach "$rebasedir" "$new"
echo "== checking patch series: $oldshort -> $newshort =="
apply_series "$rebasedir"

if [ -s "$tmp/upstream" ]; then
    echo "NOTE: verify and remove these now-upstream patches:"
    sed 's/^/  /' "$tmp/upstream"
fi
if [ "$mode" = check ]; then
    echo "OK: patch series applies to $newshort (nothing changed)"
    exit 0
fi

git -C "$sub" worktree remove --force "$rebasedir"
git -C "$sub" checkout -q --detach "$new"
git -C "$root" add tamarin-prover

if [ -d "$testdir" ]; then
    git -C "$testdir" reset --hard -q "$new"
    git -C "$testdir" clean -fdq
fi

mkdir -p "$root/scripts/results"
remap_report="scripts/results/cite_remap_$newshort.txt"
python3 "$root/scripts/remap_hs_cites.py" --old "$old" --new "$new" --apply \
    2>&1 | tee "$root/$remap_report"
remap_status="${PIPESTATUS[0]}"
[ "$remap_status" = 0 ] \
    || echo "WARNING: cite remap failed — see $remap_report" >&2

wrapped="$(cd "$root" && grep -rnE '\.hs:[0-9]+([,-][0-9]+)*,[[:space:]]*$' \
    crates --include='*.rs' || true)"
if [ -n "$wrapped" ]; then
    {
        echo
        echo "WRAPPED CITES — verify these were remapped as a whole:"
        printf '%s\n' "$wrapped"
    } >> "$root/$remap_report"
fi

if (cd "$root" && python3 scripts/check_hs_cites.py) >> "$root/$remap_report" 2>&1; then
    echo "cite gate: check_hs_cites.py OK"
else
    echo "WARNING: check_hs_cites.py found stale cites — see $remap_report" >&2
fi

if [ "${SKIP_BUILD:-0}" != 1 ]; then
    "$root/setup.sh" testing
    (cd "$root" && cargo build --release)
fi

cat <<EOF
== bumped tamarin-prover $oldshort -> $newshort ==
staged (not committed): tamarin-prover gitlink
review: $remap_report and any Haskell cite rewrites

The rebuilt oracle has a new fingerprint, so old cache entries are safe but
will miss. Re-run the batch, proof-output divergence, and web parity gates to
populate and certify the new cache generation.
EOF
