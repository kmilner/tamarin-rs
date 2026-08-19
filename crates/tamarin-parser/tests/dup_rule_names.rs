// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parity for the duplicate-rule / duplicate-restriction guards
//! `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) runs after each
//! protocol rule parses:
//!
//!   * `addOpenProtoRule` (OpenTheory.hs:691-702) rejects a rule whose name is
//!     already bound to a DIFFERENT rule — an identical duplicate passes the
//!     guard and is appended a second time;
//!   * each `_restrict` formula's minted `Restr_<rule>_<i>` restriction goes
//!     through `addRestriction` (TheoryObject.hs:453-456) FIRST, which rejects
//!     on an existing NAME alone.
//!
//! Both rejections are `throwM` → `fail (show e)` (Token.hs:210-211) with
//! `show (DuplicateItem …)` (Parser/Exceptions.hs:38-40): a recoverable
//! failure, which the port reports as [`ParseError::ConflictingDeclarations`]
//! (context [`ParseContext::Rule`] / [`ParseContext::Restriction`]) carrying
//! both items' source spans.
//!
//! Which theories are rejected (and which load) is pinned to the Haskell
//! oracle (Git revision ef3f0468); every accepted theory loads with exit 0
//! there.

use tamarin_parser::ast::TheoryItem;
use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError};

/// The `(name, first_at, second_at)` of `src`'s duplicate-rule
/// [`ParseError::ConflictingDeclarations`], positions flattened to
/// `(line, col)`.
#[track_caller]
fn dup_rule_err(src: &str) -> (String, (u32, u32), (u32, u32)) {
    dup_rule_check(parse_theory(src, &[]))
}

/// [`dup_rule_err`] for an already-run parse.
#[track_caller]
fn dup_rule_check<T>(res: Result<T, ParseError>) -> (String, (u32, u32), (u32, u32)) {
    let e = match res {
        Ok(_) => panic!("the probes below must all fail to parse"),
        Err(e) => e,
    };
    let ParseError::ConflictingDeclarations {
        name,
        context: ParseContext::Rule,
        first_at,
        second_at,
    } = e
    else {
        panic!("expected the duplicate-rule variant, got {e:?}");
    };
    let first_at = first_at.expect("a duplicate rule has a first site");
    (
        name,
        (first_at.line, first_at.col),
        (second_at.line, second_at.col),
    )
}

/// The same for the duplicate-restriction context.
#[track_caller]
fn dup_restriction_err(src: &str) -> (String, (u32, u32), (u32, u32)) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::ConflictingDeclarations {
        name,
        context: ParseContext::Restriction,
        first_at,
        second_at,
    } = e
    else {
        panic!("expected the duplicate-restriction variant, got {e:?}");
    };
    let first_at = first_at.expect("a duplicate restriction has a first site");
    (
        name,
        (first_at.line, first_at.col),
        (second_at.line, second_at.col),
    )
}

/// The names of the protocol-rule items in `src`'s parsed theory.
fn rule_names(src: &str) -> Vec<String> {
    parse_theory(src, &[])
        .expect("theory should parse")
        .items
        .iter()
        .filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r.name.clone()),
            _ => None,
        })
        .collect()
}

/// Same name, different `color=` attribute: attributes are part of the
/// `ProtoRuleE` the guard compares (`ru ==`, OpenTheory.hs:697), so this is a
/// different rule and dies at the second rule's add, with both rules' spans
/// in the error.
#[test]
fn different_color_same_name_is_a_duplicate() {
    let src = "theory T begin\n\n\
               rule R1[color=ff0000]: [ ] --> [ ]\n\
               rule R1[color=00ff00]: [ ] --> [ ]\n\n\
               end\n";
    assert_eq!(dup_rule_err(src), ("R1".to_string(), (3, 1), (4, 1)));
}

/// Same name, different conclusions.
#[test]
fn different_body_same_name_is_a_duplicate() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               end\n";
    assert_eq!(dup_rule_err(src), ("R1".to_string(), (3, 1), (4, 1)));
}

/// The guard fires as soon as the second rule has parsed — mid-file, before a
/// later parse error is ever reached.
#[test]
fn duplicate_fires_before_a_later_parse_error() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --> [ Out('b') ]\n\n\
               rule Broken: [ ] --> [\n\
               end\n";
    assert_eq!(dup_rule_err(src), ("R1".to_string(), (3, 1), (4, 1)));
}

/// A byte-identical duplicate passes `addOpenProtoRule`'s
/// `maybe True (ru ==) …` guard and is appended AGAIN — both copies are
/// items (and both render).  The corpus relies on this (e.g.
/// examples/asiaccs20-POIDC/OIDC_CodeFlow_with_ClientSecret.spthy carries
/// two identical `Get_pk` rules, which is the shape of the second case).  The
/// oracle loads both theories with exit 0.  It prints their
/// `rule (modulo E) …` echo twice.
#[test]
fn identical_duplicates_are_accepted_and_appended_twice() {
    for (case, name, src) in [
        (
            "empty rule",
            "R1",
            "theory T begin\n\n\
             rule R1: [ ] --> [ ]\n\
             rule R1: [ ] --> [ ]\n\n\
             end\n",
        ),
        (
            "corpus shape",
            "Get_pk",
            "theory T begin\n\n\
             rule Get_pk:\n    [ !Pk(A, pubkey) ]\n  -->\n    [ Out(pubkey) ]\n\n\
             rule Get_pk:\n    [ !Pk(A, pubkey) ]\n  -->\n    [ Out(pubkey) ]\n\n\
             end\n",
        ),
    ] {
        assert_eq!(rule_names(src), [name, name], "case {case}");
    }
}

/// Two `_restrict`-carrying rules with the same name die at the RESTRICTION
/// guard, before the rule-equality comparison: `liftedAddProtoRule` adds the
/// expanded `Restr_<rule>_<i>` restrictions first (Text/Parser.hs:177-179), and
/// `addRestriction` rejects on the existing NAME even though both rules (and
/// both restrictions) are byte-identical.
#[test]
fn identical_restrict_duplicate_dies_at_the_restriction() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert_eq!(
        dup_restriction_err(src),
        ("Restr_R1_1".to_string(), (3, 29), (4, 29))
    );
}

/// A user restriction that happens to carry a minted `Restr_<rule>_<i>` name
/// blocks the `_restrict` expansion the same way — `addRestriction` checks
/// against ALL restrictions in the theory.
#[test]
fn user_restriction_blocks_restrict_expansion() {
    let src = "theory T begin\n\n\
               restriction Restr_R1_1:\n  \
               \"All x #i #j. B(x) @ #i & B(x) @ #j ==> #i = #j\"\n\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    // `first_at` is the user restriction's own span; `second_at` the minted
    // restriction's origin, the `_restrict(…)` action.
    assert_eq!(
        dup_restriction_err(src),
        ("Restr_R1_1".to_string(), (3, 1), (6, 29))
    );
}

/// When only the SECOND rule carries `_restrict`, its restriction name is
/// fresh, so the restriction adds fine and the guard falls through to the
/// rule comparison — which fails on the differing actions.
#[test]
fn second_rule_with_restrict_is_a_duplicate_rule() {
    let src = "theory T begin\n\n\
               rule R1: [ ] --> [ Out('a') ]\n\
               rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j ==> #i = #j ) ]-> [ Out('a') ]\n\n\
               end\n";
    assert_eq!(dup_rule_err(src), ("R1".to_string(), (3, 1), (4, 1)));
}

/// The guard spans `#include` fragments: HS runs one `addItems` accumulation
/// across included files, so a rule in the fragment collides with a
/// different same-named rule in the including file.  `first_at` carries the
/// included rule's position in the FRAGMENT's own coordinates (a known rough
/// edge: the error does not record which file that span belongs to).
#[test]
fn duplicate_across_include_is_rejected() {
    let dir = std::env::temp_dir().join(format!(
        "tamarin_parser_dup_rule_names_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("mkdir");
    std::fs::write(
        dir.join("frag.spthy"),
        "rule R1[color=ff0000]: [ ] --> [ ]\n",
    )
    .expect("write fragment");
    let src = "theory T begin\n\n\
               #include \"frag.spthy\"\n\n\
               rule R1[color=00ff00]: [ ] --> [ ]\n\n\
               end\n";
    assert_eq!(
        dup_rule_check(tamarin_parser::parse_theory_with_base(
            src,
            &[],
            Some(dir.clone())
        )),
        ("R1".to_string(), (1, 1), (5, 1))
    );
    let _ = std::fs::remove_dir_all(&dir);
}
