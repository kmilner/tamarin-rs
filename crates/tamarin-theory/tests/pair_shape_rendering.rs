// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins the pair arm of HS `prettyTerm` and the `Ord` that arranges
//! pair-headed AC operands, both observed on the `rule (modulo E)` echo.
//!
//! `prettyTerm` selects `ppTerms ", " 1 "<" ">" (split t)` for every
//! `pairSym`-headed term (Term/Term.hs:313), so the SHAPE decides — the
//! source spelling `pair(a, b)` renders `<a, b>` exactly like `<a, b>`.
//! `split` (Term/Term.hs:323-324) walks the RIGHT spine only, so a
//! left-nested `pair(pair(a, b), c)` keeps its inner brackets.
//!
//! The same nesting drives `Ord`: HS's pair carries the arity-2 argument list
//! `[t1, t2]` (`fAppPair`, Term/Term.hs:163), so comparing `<a, z>` with
//! `<a, b, c>` pits `z` against `pair(b, c)` at position 2, where
//! `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74) puts `<a, z>` first in the
//! sorted `++` chain (`fAppAC`, Term/Term/Raw.hs:118-122).
//!
//! Expected strings are the pinned oracle's bytes (Git revision ef3f0468) for
//! the same theories, plain no-prove render.

use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::pretty_theory::web_proto_rules;

/// The `rule (modulo E)` echo of a probe theory's single rule.  The rendered
/// rule carries HS's AC-variant annotation below that echo
/// (`prettyProtoRuleACInfo`, Theory/Model/Rule.hs), whose content depends on
/// the variant computation rather than on `prettyTerm`; the expected bytes
/// below cover the echo, so the annotation block is split off here.
fn rule_echo(src: &str) -> String {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = elaborate(&thy).expect("elaborate");
    let mut rendered = web_proto_rules(&thy, &elaborated);
    assert_eq!(rendered.len(), 1, "one rule per probe theory");
    let rule = rendered.remove(0);
    match rule.split_once("\n\n  /*") {
        Some((echo, _annotation)) => echo.to_string(),
        None => rule,
    }
}

/// A prefix `pair(a, b)` and the `<c, d>` spelling reach the same arm, and a
/// pair nested on the RIGHT (`fst(<e, f>)`'s argument) splices flat.
#[test]
fn prefix_pair_renders_between_angle_brackets() {
    let src = "theory P8 begin\n\
               builtins: multiset\n\
               rule Test: [ Out( pair(a,b) ++ <c,d> ++ fst(<e,f>) ) ] --[ ]-> []\n\
               end\n";
    assert_eq!(
        rule_echo(src),
        "rule (modulo E) Test:\n   [ Out( (fst(<e, f>)++<a, b>++<c, d>) ) ] --> [ ]"
    );
}

/// `split` recurses on the right child only, so `pair(pair(a, b), c)` renders
/// `<<a, b>, c>` — the left operand stays a bracketed pair of its own.
#[test]
fn left_nested_pair_keeps_its_inner_brackets() {
    let src = "theory Q1 begin\n\
               rule Test: [ In( pair(a,b) ) ] --[ ]-> [ Out( pair(pair(a,b),c) ) ]\n\
               end\n";
    assert_eq!(
        rule_echo(src),
        "rule (modulo E) Test:\n   [ In( <a, b> ) ] --> [ Out( <<a, b>, c> ) ]"
    );
}

/// Two pairs sharing a prefix order by their NESTED argument lists, so the
/// SHORTER `<a, z>` sorts before `<a, b, c>` — the reverse of an element-wise
/// comparison of the flat operand lists (`b` before `z`).
#[test]
fn pair_ac_operands_order_by_the_nested_spine() {
    let src = "theory PairOrd begin\n\
               builtins: multiset\n\
               rule R:\n\
               \x20 [ In(a), In(b), In(c), In(z) ] --[ ]-> [ Out( <a,b,c> ++ <a,z> ) ]\n\
               end\n";
    assert_eq!(
        rule_echo(src),
        "rule (modulo E) R:\n   \
         [ In( a ), In( b ), In( c ), In( z ) ] --> [ Out( (<a, z>++<a, b, c>) ) ]"
    );
}

/// The pair spelling must not disturb the AC operand order: a `++` chain
/// mixing a bare literal, both pair lengths and two `*` products keeps HS's
/// `FunSym`-then-argument order, with the pairs adjacent and short-first.
#[test]
fn pair_operands_keep_their_place_among_other_ac_heads() {
    let src = "theory MixedAc begin\n\
               builtins: multiset\n\
               rule SameHead:\n\
               \x20 [ Out( ((b*c)*a) ++ (b*z) ++ <a,b,c> ++ <a,z> ++ h ) ] --[ ]-> []\n\
               end\n";
    assert_eq!(
        rule_echo(src),
        "rule (modulo E) SameHead:\n   \
         [ Out( (h++<a, z>++<a, b, c>++(a*b*c)++(b*z)) ) ] --> [ ]"
    );
}
