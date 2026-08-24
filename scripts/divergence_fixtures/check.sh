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

# Extra assertions for a `diverge` fixture: the SHAPE of the divergence, not
# just its existence, so an unrelated change to either side cannot leave the
# fixture in a passing state for the wrong reason.  A `diverge` row with no arm
# here asserts nothing more than "the two files differ".  The fallthrough is
# therefore a failure.
divergence_shape() {
    case "$1.$2" in
    ac_marker_collapse.theory)
        # Documented upstream bug: upstream rebuilds the Maude reply as an AC
        # term and `fAppAC _ [a] = a` deletes the unary application, so the
        # oracle's closed rule outputs the bare argument; the port keeps the
        # application.
        grep -qF "Out( (a++y) )"            "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side no longer collapses tamXCAbar(a) — expected \`Out( (a++y) )\`" >&2; return 1; }
        grep -qF "Out( (y++tamXCAbar(a)) )" "$expected/$1.$2.rs.txt" \
            || { echo "    port side no longer keeps tamXCAbar(a) — expected \`Out( (y++tamXCAbar(a)) )\`" >&2; return 1; }
        ;;
    s1_ac_display_order.theory)
        # Upstream substitutes the freshened display variable into the body
        # before printing, so the AC arguments are re-sorted by the display
        # index; the port orders them once, with the variables as written.
        grep -qF "⇒ (∃ ~x.1 #j. B( (x++~x.1) ) @ #j)" "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not re-sort the AC arguments by the display index — expected \`B( (x++~x.1) )\`" >&2; return 1; }
        grep -qF "⇒ (∃ ~x.1 #j. B( (~x.1++x) ) @ #j)" "$expected/$1.$2.rs.txt" \
            || { echo "    port side does not order the AC arguments by the written sort — expected \`B( (~x.1++x) )\`" >&2; return 1; }
        ;;
    sapic_cond_wrap.theory)
        # A conditional's formula is rendered standalone at the HughesPJ
        # default width, so the conjunction breaks and the second conjunct
        # starts at column 0; the port renders it flat.  The derived rule name
        # is `filter isAlpha` over the same string and drops the break, so it
        # has to stay identical on both sides.
        grep -qxF '(Longer( cccccccccc(zzzzzzzzzz.1), aaaaaaaaaa(yyyyyyyyyy.1) ))",' "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not break the conjunction onto its own line at column 0" >&2; return 1; }
        grep -qF ') )) ∧ (Longer( cccccccccc(zzzzzzzzzz.1)' "$expected/$1.$2.rs.txt" \
            || { echo "    port side does not keep the conjunction on one line" >&2; return 1; }
        local nm=ifLongeraaaaaaaaaaxxxxxxxxxxbbbbbbbbbbyyyyyyyyyyLongercccccccccczzzzzzzzzzaaaaaaaaaayyyyyyyyyy_0_1
        grep -qF "$nm" "$expected/$1.$2.hs.txt" && grep -qF "$nm" "$expected/$1.$2.rs.txt" \
            || { echo "    the derived rule name $nm is not on both sides — the layout has reached the name" >&2; return 1; }
        ;;
    sapic_cond_type_tag.theory)
        # A condition's variables are `SapicLVar`s, and `-m=spthytyped` prints
        # a process definition's formals with their type tag.  The port prints
        # every formal untagged.  Row `V` carries the positional rule — a
        # predicate argument takes `sapicvar` whatever its spelling — and
        # agrees on both sides.
        grep -qxF "let  S (#k.1:node,#l.1:node) = out('yes') if #k.1 < #l.1 out('no')" "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not tag the two operands of \`<\` — expected \`(#k.1:node,#l.1:node)\`" >&2; return 1; }
        grep -qxF "let  P (x.1:foo) = out('yes') if Eq( x.1, 'a' ) out('no')" "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not carry the written type — expected \`(x.1:foo)\`" >&2; return 1; }
        grep -qxF "let  S (#k.1,#l.1) = out('yes') if #k.1 < #l.1 out('no')" "$expected/$1.$2.rs.txt" \
            || { echo "    port side does not print the \`<\` operands untagged — expected \`(#k.1,#l.1)\`" >&2; return 1; }
        grep -qxF "let  P (x.1) = out('yes') if Eq( x.1, 'a' ) out('no')" "$expected/$1.$2.rs.txt" \
            || { echo "    port side does not print the typed variable untagged — expected \`(x.1)\`" >&2; return 1; }
        local v="let  V (y.1,#p.1) = out('yes') if Pred( #p.1, y.1 ) out('no')"
        grep -qxF "$v" "$expected/$1.$2.hs.txt" && grep -qxF "$v" "$expected/$1.$2.rs.txt" \
            || { echo "    a predicate argument is no plain \`sapicvar\` on one of the two sides — expected \`(y.1,#p.1)\`" >&2; return 1; }
        ;;
    sapic_msr_restrict_wrap.theory)
        # The restriction item is a Doc composition `_restrict(` <> formula <>
        # `)`, so the formula's break indents by the ten columns of the
        # opening operator; the port flattens the formula before the rule's
        # layout sees it.
        grep -qxF '_restrict((aaaaaaaaaa(xxxxxxxxxx.1) = bbbbbbbbbb(yyyyyyyyyy.1)) ∧' "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not break the restriction formula after the conjunction" >&2; return 1; }
        grep -qxF '          (cccccccccc(zzzzzzzzzz.1) = aaaaaaaaaa(yyyyyyyyyy.1)))' "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not indent the continuation by the ten columns of \`_restrict(\`" >&2; return 1; }
        grep -qxF '_restrict((aaaaaaaaaa(xxxxxxxxxx.1) = bbbbbbbbbb(yyyyyyyyyy.1)) ∧ (cccccccccc(zzzzzzzzzz.1) = aaaaaaaaaa(yyyyyyyyyy.1)))' "$expected/$1.$2.rs.txt" \
            || { echo "    port side does not keep the restriction formula on one line" >&2; return 1; }
        ;;
    sapic_pubname_in_restrict.wf)
        # `universeBi` reaches the source subprocess a translated rule carries,
        # so a public name occurring only inside an embedded `_restrict`
        # formula joins the capitalization check; the port harvests the
        # embedded rule's facts and not its restrictions.
        grep -qF "1. rule \"Init\":  name 'Foo', 'foo'" "$expected/$1.$2.hs.txt" \
            || { echo "    oracle side does not report the clash — expected \`rule \"Init\":  name 'Foo', 'foo'\`" >&2; return 1; }
        grep -qxF '/* All wellformedness checks were successful. */' "$expected/$1.$2.rs.txt" \
            || { echo "    port side does not report the run clean" >&2; return 1; }
        ;;
    *)  echo "    no documented shape for the $1.$2 divergence — add an arm here" >&2; return 1 ;;
    esac
    return 0
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
