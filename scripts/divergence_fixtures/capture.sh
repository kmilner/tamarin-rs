#!/usr/bin/env bash
# Capture the Haskell oracle's bytes for every fixture in fixtures.tsv.
#
# Usage:
#   scripts/divergence_fixtures/capture.sh              capture the oracle side
#   scripts/divergence_fixtures/capture.sh --record-rs  ALSO rewrite the port
#                                                       side of every `diverge`
#                                                       fixture (review the
#                                                       diff before committing)
#
# Environment: HS_PATH (oracle binary), RS_PATH (port binary, --record-rs only),
#              FILE_TIMEOUT (per run, default 300s).
#
# The oracle must be the build of the submodule pin: these bytes ARE the
# reference, so a capture from any other revision would silently redefine what
# the port is checked against.  The script resolves the pinned oracle inside
# tamarin-prover-testing/ and refuses any binary whose baked git revision
# differs from the recorded gitlink — the PATH `tamarin-prover` on a developer
# machine is usually a release build, which is not it.
#
# Re-run at every submodule bump (bump_submodule.sh's checklist says so), then
# `git diff scripts/divergence_fixtures/expected/`: a changed .hs.txt is
# upstream behaviour moving under the fixture.
set -eu
# shellcheck source=_common.sh
. "$(dirname "${BASH_SOURCE[0]}")/_common.sh"

record_rs=0
case "${1:-}" in
    '')           ;;
    --record-rs)  record_rs=1 ;;
    -h|--help)    sed -n '2,${/^#/!q;s/^# \{0,1\}//p;}' "$0"; exit 0 ;;
    *)            die "unknown option: $1" ;;
esac

find_hs_bin() {
    local c
    for c in "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$repo_root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done
    return 1
}

HS_PATH="${HS_PATH:-$(find_hs_bin || true)}"
[ -n "$HS_PATH" ] && [ -x "$HS_PATH" ] \
    || die "no oracle binary — build it with ./setup.sh testing, or set HS_PATH"

pin="$(git -C "$repo_root" rev-parse :tamarin-prover)"
binrev="$(timeout 60 "$HS_PATH" --version "${hs_rts[@]}" 2>/dev/null \
    | sed -n 's/^Git revision: \([0-9a-f]*\).*/\1/p')"
[ "$binrev" = "$pin" ] \
    || die "oracle $HS_PATH is revision '${binrev:-unknown}' but the submodule pin is $pin — rebuild with ./setup.sh testing"

mkdir -p "$expected"

# Only what the manifest names is ever captured, so a `.spthy` no row mentions
# would never be visited and a capture left behind by a retired row would keep
# its stale bytes.  Census the directory against the manifest in both
# directions before the oracle runs.  Same block as check.sh's census — keep
# the two in step.
declare -A claimed=([oracle_rev]=1)
claim_one() {
    local name="$1" slices="$2" mode="$3" sl
    case "$mode" in
        match|diverge) ;;
        *) die "$manifest gives $name the unknown mode '$mode'" ;;
    esac
    claimed["$name.spthy"]=1
    for sl in $(slices_of "$slices"); do
        claimed["$name.$sl.hs.txt"]=1
        if [ "$mode" = diverge ]; then claimed["$name.$sl.rs.txt"]=1; fi
    done
}
for_each_fixture claim_one
for f in "$fixdir"/*.spthy "$expected"/*; do
    # A first-ever capture finds expected/ empty, leaving that glob unexpanded.
    [ -e "$f" ] || continue
    [ -n "${claimed[$(basename "$f")]:-}" ] \
        || die "$(basename "$f") is claimed by no row of $manifest — add a row or delete the file"
done

# `cut_slices <raw-file> <name> <slices> <side>` — write one expected file per
# slice.  An empty slice means the fixture stopped producing the block it
# exists to pin, which must not be committed as a reference.
cut_slices() {
    local raw="$1" name="$2" slices="$3" side="$4" sl dest
    for sl in $(slices_of "$slices"); do
        dest="$expected/$name.$sl.$side.txt"
        slice "$sl" < "$raw" > "$dest"
        [ -s "$dest" ] || die "$side side produced an EMPTY $sl slice for $name.spthy"
        printf '  %-24s %-6s %-2s %s lines\n' "$name" "$sl" "$side" "$(wc -l < "$dest")"
    done
}

capture_one() {
    local name="$1" slices="$2" mode="$3" flags="$4" raw
    raw="$(mktemp)"
    load "$HS_PATH" "$name" "$flags" "${hs_rts[@]}" > "$raw" \
        || { rm -f "$raw"; die "oracle failed or timed out on $name.spthy"; }
    cut_slices "$raw" "$name" "$slices" hs
    rm -f "$raw"

    [ "$mode" = diverge ] && [ "$record_rs" = 1 ] || return 0
    [ -x "$RS_PATH" ] || die "no port binary at $RS_PATH (cargo build --release)"
    raw="$(mktemp)"
    load "$RS_PATH" "$name" "$flags" > "$raw" \
        || { rm -f "$raw"; die "the port failed or timed out on $name.spthy"; }
    cut_slices "$raw" "$name" "$slices" rs
    rm -f "$raw"
    echo "  ^ RECORDED port side — review before committing"
}

echo "capturing with $HS_PATH (revision $pin)"
for_each_fixture capture_one
printf '%s' "$pin" > "$expected/oracle_rev"
echo "done — review: git diff scripts/divergence_fixtures/expected/"
