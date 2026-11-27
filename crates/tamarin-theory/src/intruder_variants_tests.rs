// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use tamarin_term::maude_sig::dh_maude_sig;

/// `parse_intruder_rules` is the public entry point with full HS
/// signature `MaudeSig → ctxtDesc → source → Result`.  Verify it
/// works directly on a tiny inline source.
#[test]
fn parse_intruder_rules_handles_tiny_inline() {
    let src = "rule (modulo AC) c_exp:\n   [ !KU( x ), !KU( x.1 ) ] --[ !KU( x^x.1 ) ]-> [ !KU( x^x.1 ) ]\n";
    let rules = parse_intruder_rules(&dh_maude_sig(), "<inline>", src)
        .expect("parse_intruder_rules on inline src");
    assert_eq!(rules.len(), 1);
    match &rules[0].info {
        IntrRuleACInfo::ConstrRule { name, fun } => {
            assert_eq!(name.as_slice(), b"_exp");
            assert_eq!(
                *fun,
                tamarin_term::function_symbols::FunSym::NoEq(
                    tamarin_term::function_symbols::exp_sym()
                ),
                "c_exp must resolve `exp` against the signature"
            );
        }
        other => panic!("expected ConstrRule, got {:?}", other),
    }
}

/// Rule names that don't start with `c` or `d` must be rejected.
/// DELIBERATE DIVERGENCE: HS `intrInfo`'s `case name of` has only the
/// `'c':cname` and `'d':dname` arms (Theory/Text/Parser/Rule.hs), so a
/// third prefix is an incomplete-pattern crash there; we return a parse error
/// instead.
#[test]
fn parse_intruder_rules_rejects_non_c_d_prefix() {
    let src = "rule (modulo AC) xfoo:\n   [ ] --> [ ]\n";
    let err = parse_intruder_rules(&dh_maude_sig(), "<bad>", src)
        .expect_err("rule named `xfoo` should be rejected");
    assert!(
        err.message.contains("invalid intruder rule name"),
        "expected `invalid intruder rule name` in error; got {}",
        err.message
    );
}

/// Counterpart to `dh_one_and_dh_neutral_parse_as_constants`: with
/// NO DH builtin enabled, parsing a rule containing a bare `one`
/// must NOT magically convert it to a constant — the parser searches
/// the seeded signature.  HS behaviour: under `pairMaudeSig`, `funSyms`
/// excludes `oneSym`, so `nullaryApp` falls through to `plit` and `one`
/// parses as a variable.  Confirms our seeding mirrors HS.
#[test]
fn one_is_var_when_no_dh_builtin_in_maude_sig() {
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // The rule name must resolve against the signature (`lookupFun`),
    // so use the always-present `pair` symbol; the point of the test
    // is the bare `one` in the facts.
    let src = "rule (modulo AC) c_pair:\n   [ ] --[ !KU( one ) ]-> [ !KU( one ) ]\n";
    let rules = parse_intruder_rules(&pair_maude_sig(), "<no-dh>", src)
        .expect("parse_intruder_rules under pair_maude_sig");
    assert_eq!(rules.len(), 1);
    let action_term = &rules[0].actions[0].terms()[0];
    match action_term {
        Term::Lit(Lit::Var(v)) => {
            assert_eq!(
                v.name, "one",
                "under pair_maude_sig, `one` should remain a Var; HS-equivalent: \
                     `funSyms pairMaudeSig` does not include `oneSym`"
            );
        }
        other => panic!(
            "expected Var (no DH builtin → MaudeSig has no `one` constant), \
                 got {:?}",
            other,
        ),
    }
}
