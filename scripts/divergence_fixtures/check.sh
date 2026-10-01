#!/usr/bin/env bash
# Assert the port's behaviour on the corners no corpus theory reaches.
#
# Usage: scripts/divergence_fixtures/check.sh
# Environment: RS_PATH (port binary), FILE_TIMEOUT (per run, default 300s).
#
# Each fixture is a theory whose interesting output survives in one or more gate
# slices (fixtures.tsv says which).  A `match` row must reproduce the pinned
# oracle's captured bytes; a `diverge` row must NOT, and must diverge in
# exactly the shape divergence_shape below documents — so the check goes red
# both when the port moves and when a submodule bump moves upstream.
#
# Only the port runs here: the oracle side is the committed capture under
# expected/, refreshed by capture.sh at bump time.  Nothing in the corpus
# reaches these shapes, so wf_gate/pretty_gate/corpus_file_diff stay green
# across a regression in any of them.
set -eu
# shellcheck source=_common.sh
. "$(dirname "${BASH_SOURCE[0]}")/_common.sh"

case "${1:-}" in
    '')        ;;
    -h|--help) sed -n '2,${/^#/!q;s/^# \{0,1\}//p;}' "$0"; exit 0 ;;
    *)         die "unknown option: $1 (this script takes none)" ;;
esac

[ -x "$RS_PATH" ] || die "no port binary at $RS_PATH (cargo build --release)"
[ -f "$expected/oracle_rev" ] \
    || die "no captured oracle bytes — run scripts/divergence_fixtures/capture.sh"
pin="$(git -C "$repo_root" rev-parse :tamarin-prover)"
stamped="$(cat "$expected/oracle_rev")"
[ "$stamped" = "$pin" ] \
    || die "expected/ was captured from oracle $stamped but the submodule pin is now $pin — re-run capture.sh and review the diff"

fail=0
report() { printf '  %-24s %-6s %-8s %s\n' "$1" "$2" "$3" "$4"; }

# The directory and the manifest must agree before anything is loaded.
census_fixture_dir

# Extra assertions for `diverge` fixtures: the SHAPE of each divergence, not
# just its existence. There are currently no intentional divergences; adding
# one requires a documented arm here so unrelated changes cannot pass it.
divergence_shape() {
    case "$1.$2" in
    *)  echo "    no documented shape for the $1.$2 divergence — add an arm here" >&2; return 1 ;;
    esac
}

# `check_slice <name> <slice> <mode> < raw` — compare one block of one load.
# A reference must be non-empty (`-s`, not `-f`).  An empty reference matches
# an engine that printed nothing at all.  That is the one way this comparison
# can pass while it asserts nothing.  capture.sh writes each reference by
# redirection, and it unlinks the file again when the slice comes out empty.
# A 0-byte file here is therefore a capture that was killed in between.
check_slice() {
    local name="$1" sl="$2" mode="$3" hs="$expected/$1.$2.hs.txt" ref got
    if [ ! -s "$hs" ]; then
        report "$name" "$sl" FAIL "no captured oracle bytes — run capture.sh"; fail=1; return 0
    fi
    got="$(mktemp)"; slice "$sl" > "$got"

    ref="$hs"
    if [ "$mode" = diverge ]; then
        ref="$expected/$name.$sl.rs.txt"
        if [ ! -s "$ref" ]; then
            rm -f "$got"
            report "$name" "$sl" FAIL "no recorded port bytes — run capture.sh --record-rs"; fail=1; return 0
        fi
        if cmp -s "$hs" "$ref"; then
            rm -f "$got"
            report "$name" "$sl" FAIL "the documented divergence is GONE (oracle and port bytes now agree)"
            echo "    upstream may have fixed it: retire this fixture and update the upstream-bug write-up" >&2
            fail=1; return 0
        fi
        if ! divergence_shape "$name" "$sl"; then
            rm -f "$got"; report "$name" "$sl" FAIL "divergence changed shape"; fail=1; return 0
        fi
    fi

    if cmp -s "$ref" "$got"; then
        report "$name" "$sl" OK "$mode"
    else
        report "$name" "$sl" FAIL "differs from $(basename "$ref")"
        diff "$ref" "$got" | head -40 >&2
        fail=1
    fi
    rm -f "$got"
}

check_one() {
    local name="$1" slices="$2" mode="$3" flags="$4" raw sl
    raw="$(mktemp)"
    if ! load "$RS_PATH" "$name" "$flags" > "$raw"; then
        rm -f "$raw"
        for sl in $(slices_of "$slices"); do report "$name" "$sl" FAIL "the port failed or timed out"; done
        fail=1; return 0
    fi
    for sl in $(slices_of "$slices"); do check_slice "$name" "$sl" "$mode" < "$raw"; done
    rm -f "$raw"
}

echo "divergence fixtures ($RS_PATH vs expected/ captured at $stamped)"
for_each_fixture check_one
[ "$fail" = 0 ] || { echo "divergence_fixtures: FAILED" >&2; exit 1; }
echo "divergence_fixtures: all OK"
