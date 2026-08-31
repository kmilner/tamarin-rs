#!/usr/bin/env bash
# Bump the tamarin-prover submodule while preserving the per-PR patch series.
#
# Usage:
#   scripts/bump_submodule.sh [<ref>]           bump (default: origin/develop)
#   scripts/bump_submodule.sh --check [<ref>]   check only; change nothing
#
# Environment:
#   SKIP_BUILD=1   skip rebuilding the Haskell oracle, refreshing its server
#                  fixtures, and building the Rust release binary
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
server_captures_rel="crates/tamarin-server/tests/fixtures/haskell-responses"
tmp="$(mktemp -d)"
owns_rebasedir=0

cleanup() {
    if [ "$owns_rebasedir" = 1 ] && [ -d "$rebasedir" ]; then
        git -C "$sub" worktree remove --force "$rebasedir" 2>/dev/null || true
    fi
    rm -rf "$tmp"
}
trap cleanup EXIT

die() { echo "ERROR: $*" >&2; exit 1; }

apply_series() {
    tree="$1"
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
            echo "applies cleanly:  $name"
        else
            die "$name no longer applies cleanly; refresh this patch from its upstream PR"
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
    [ -z "$(git -C "$root" status --porcelain -- tamarin-prover patches "$server_captures_rel")" ] \
        || die "uncommitted submodule, patch, or Haskell server fixture changes — commit or reset first"
    [ "$(git -C "$sub" rev-parse HEAD)" = "$old" ] \
        || die "submodule checkout does not match the recorded pin — run ./setup.sh first"
fi

git -C "$sub" fetch origin
new="$(git -C "$sub" rev-parse --verify "$ref^{commit}")" \
    || die "cannot resolve '$ref' in the submodule"
oldshort="$(git -C "$sub" rev-parse --short "$old")"
newshort="$(git -C "$sub" rev-parse --short "$new")"
if [ "$mode" = bump ] && [ "$new" = "$old" ]; then
    echo "already at $ref ($newshort) — nothing to do"
    exit 0
fi

git -C "$sub" worktree add -q --detach "$rebasedir" "$new"
owns_rebasedir=1
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
owns_rebasedir=0
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

staged_outputs="tamarin-prover gitlink"
if [ "${SKIP_BUILD:-0}" != 1 ]; then
    "$root/setup.sh" testing
    "$root/crates/tamarin-server/tests/capture_haskell_fixtures.sh"
    git -C "$root" add "$server_captures_rel"
    staged_outputs="$staged_outputs and refreshed HTTP captures"
    (cd "$root" && cargo build --release)
else
    echo "WARNING: SKIP_BUILD=1 also skipped the Haskell server fixture capture" >&2
fi

cat <<EOF
== bumped tamarin-prover $oldshort -> $newshort ==
staged (not committed): $staged_outputs
review: $remap_report and any Haskell cite rewrites

The rebuilt oracle has a new fingerprint, so old cache entries are safe but
will miss; run scripts/migrate_hs_cache_fp.sh when preserving a compatible
local cache generation. Re-certify the new source/cache generation:
  1. scripts/divergence_fixtures/capture.sh && git diff -- scripts/divergence_fixtures/expected
  2. scripts/capture_cli_refs.sh && cargo test -p tamarin-prover --test cli_e2e
  3. scripts/corpus_file_diff.sh 2>&1 | tee /tmp/fullgate.log
     scripts/rs_ref_check.sh generate --certified-by /tmp/fullgate.log
  4. scripts/wf_gate.sh && scripts/pretty_gate.sh; run all three flag sweeps
  5. cargo test -p tamarin-server (HTTP captures refreshed automatically above;
     with SKIP_BUILD=1, build the oracle and run capture_haskell_fixtures.sh first)
  6. run web_parity.sh on the milestone list and pane_byte_check.sh on its captures
EOF
