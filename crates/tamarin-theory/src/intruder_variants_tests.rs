// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};

/// The cached DH file is documented to contain exactly 51 rules:
/// 5 constructors (`c_exp`, `c_inv`, `c_one`, `c_DH_neutral`, `c_mult`)
/// + 45 `d_exp` destructor variants + 1 `d_inv` destructor variant.
///   `grep -c "^rule " data/intruder_variants_dh.spthy` = 51.
#[test]
fn dh_variants_file_parses_to_51_rules() {
    let rules = mk_dh_intruder_variants(&dh_maude_sig());
    assert_eq!(
        rules.len(),
        51,
        "data/intruder_variants_dh.spthy should yield exactly 51 rules \
             (HS-cached output of `dhIntruderRules`); got {}",
        rules.len()
    );
}

/// Count check for the BP cached file
/// (`grep -c "^rule " data/intruder_variants_bp.spthy` = 75).
#[test]
fn bp_variants_file_parses_to_75_rules() {
    let rules = mk_bp_intruder_variants(&bp_maude_sig());
    assert_eq!(
        rules.len(),
        75,
        "data/intruder_variants_bp.spthy should yield exactly 75 rules; got {}",
        rules.len()
    );
}

/// The 5 constructor rules MUST be present with their HS-canonical
/// underscore-prefixed names (`c_exp` → `ConstrRule "_exp"`, etc).
/// HS reference: Theory/Tools/IntruderRules.hs:292-299 +
/// Theory/Text/Parser/Rule.hs:163-172, see line 171 (`'c':cname → ConstrRule (BC.pack cname)`).
#[test]
fn dh_variants_contains_five_constructors_with_underscore_prefix() {
    let rules = mk_dh_intruder_variants(&dh_maude_sig());
    let constr_names: Vec<&[u8]> = rules
        .iter()
        .filter_map(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
            _ => None,
        })
        .collect();
    assert_eq!(
        constr_names.len(),
        5,
        "expected exactly 5 ConstrRules; got {:?}",
        constr_names
            .iter()
            .map(|n| String::from_utf8_lossy(n).to_string())
            .collect::<Vec<_>>()
    );
    for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
        assert!(
            constr_names.contains(expected),
            "missing constructor named {} in DH variants; got names {:?}",
            String::from_utf8_lossy(expected),
            constr_names
                .iter()
                .map(|n| String::from_utf8_lossy(n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// Every destructor rule in DH must have shape
/// `DestrRule name 0 True False funs` (HS `intrInfo` hard-codes
/// `(fromIntegral limit) True False`, and `option 0 natural` means
/// limit=0 when none is parsed — none of the cached destructors have a
/// numeric limit).  The name must start with `_` (HS strips the leading
/// `d` and keeps the `_<rest>` as-is), and the attached function-symbol
/// list resolves the name via `constrNameFunc` + `lookupFun`.
#[test]
fn dh_variants_destructors_are_d_exp_or_d_inv_with_limit_0() {
    use tamarin_term::function_symbols::{exp_sym, inv_sym, FunSym};
    let rules = mk_dh_intruder_variants(&dh_maude_sig());
    let destrs: Vec<&IntrRuleAC> = rules
        .iter()
        .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule { .. }))
        .collect();
    assert_eq!(
        destrs.len(),
        46,
        "DH cached file: 5 constr + 46 destr = 51 (45 d_exp + 1 d_inv); \
             got {} destructors",
        destrs.len()
    );
    for d in &destrs {
        if let IntrRuleACInfo::DestrRule {
            name,
            remaining_applications: limit,
            rhs_is_proper_subterm: subterm,
            rhs_is_constant: constant,
            funs,
        } = &d.info
        {
            assert!(
                name.starts_with(b"_"),
                "destructor name must start with `_` (HS leading `d` is consumed, \
                     rest goes to the bytestring); got {}",
                String::from_utf8_lossy(name)
            );
            assert_eq!(
                *limit, 0,
                "DestrRule limit must be 0 (HS `fromIntegral limit` \
                     with `option 0 natural` and no numeric in the cached file); \
                     got {}",
                limit
            );
            assert!(
                *subterm,
                "DestrRule subterm must be True (HS intrInfo hard-codes True)"
            );
            assert!(
                !(*constant),
                "DestrRule constant must be False (HS intrInfo hard-codes False)"
            );
            // Names in the DH file: only `_exp` and `_inv`; the funs
            // list carries the resolved symbol.
            if name == b"_exp" {
                assert_eq!(funs, &vec![FunSym::NoEq(exp_sym())]);
            } else if name == b"_inv" {
                assert_eq!(funs, &vec![FunSym::NoEq(inv_sym())]);
            } else {
                panic!(
                    "DH destructor name must be `_exp` or `_inv`; got {}",
                    String::from_utf8_lossy(name)
                );
            }
        }
    }
}

/// The name index behind [`KnownFuns::lookup`] must answer exactly what
/// HS `lookupFun`'s `find ((== f) . showFunSymName) knownFuns` answers,
/// INCLUDING on a name collision: `show_fun_sym_name` is not injective —
/// a user-defined AC symbol and a user-defined NoEq symbol may carry the
/// same name, and only their `FunSym` variant separates them.
///
/// `Ord FunSym` puts `NoEq` before `AC` (FunctionSymbols.hs:150-154), so
/// in `S.toList` order the NoEq symbol is the earlier one and `find`
/// returns it.  An index built by plain `insert` would return the AC one.
#[test]
fn lookup_is_first_wins_when_two_symbols_share_a_name() {
    use std::collections::BTreeSet;
    use tamarin_term::function_symbols::{
        AcFctSym, AcSym, Constructability, NdcState, NoEqSym, Privacy,
    };

    let noeq_foo = NoEqSym::new(
        b"foo".to_vec(),
        2,
        Privacy::Public,
        Constructability::Constructor,
    );
    let ac_foo = AcFctSym::new(
        b"foo".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    assert_eq!(
        show_fun_sym_name(&FunSym::NoEq(noeq_foo)),
        show_fun_sym_name(&FunSym::Ac(AcSym::AcFct(ac_foo))),
        "the two symbols must collide for this test to mean anything"
    );

    // Same construction `parse_intruder_rules` uses: a `BTreeSet` drained
    // in order, i.e. HS `S.toList (funSyms msig)`.
    let syms: Vec<FunSym> = [FunSym::Ac(AcSym::AcFct(ac_foo)), FunSym::NoEq(noeq_foo)]
        .into_iter()
        .collect::<BTreeSet<FunSym>>()
        .into_iter()
        .collect();
    let linear_scan = syms
        .iter()
        .copied()
        .find(|fun| show_fun_sym_name(fun) == "foo")
        .expect("linear scan must find `foo`");

    assert_eq!(
        KnownFuns::new(syms)
            .lookup("foo")
            .expect("index finds `foo`"),
        linear_scan,
        "the index must return the same symbol the linear `find` returns"
    );
    assert_eq!(
        linear_scan,
        FunSym::NoEq(noeq_foo),
        "`NoEq` sorts before `AC`, so the NoEq `foo` is the first match"
    );
}

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
/// `'c':cname` and `'d':dname` arms (Theory/Text/Parser/Rule.hs:170-172), so a
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

/// Regression test for the `c_one` / `c_DH_neutral` soundness invariant:
/// under `dh_maude_sig()`, the rule `[ ] --[ !KU( one ) ]-> [ !KU( one ) ]`
/// must have ROOT = the 0-arity NoEq application `oneSym{}`, NOT a Msg-sort
/// var `one` (which would unify with every KU goal, falsely closing 8+ DH
/// corpus branches).  HS: Theory/Text/Parser/Term.hs:139-153, see line 151
/// (`nullaryApp` against `funSyms maudeSig`) and
/// lib/term/src/Term/Term/FunctionSymbols.hs:255-255
/// (`oneSym = (oneSymString,(0,Public,Constructor,NotNDC))`).
#[test]
fn dh_one_and_dh_neutral_parse_as_constants() {
    use tamarin_term::function_symbols::{DH_NEUTRAL_SYM_STRING, ONE_SYM_STRING};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    let rules = mk_dh_intruder_variants(&dh_maude_sig());
    let c_one = rules
        .iter()
        .find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => name.as_slice() == b"_one",
            _ => false,
        })
        .expect("c_one rule should be present");
    let c_dh_neutral = rules
        .iter()
        .find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => name.as_slice() == b"_DH_neutral",
            _ => false,
        })
        .expect("c_DH_neutral rule should be present");

    // Each rule has shape `[ ] --[ !KU( <const> ) ]-> [ !KU( <const> ) ]`.
    // The action and conclusion fact must carry a 0-arity NoEq term
    // whose name is the canonical sym-string.  Crucially, it must
    // NOT be a `Term::Lit(Lit::Var(_))`.
    for (label, rule, expected_name) in [
        ("c_one", c_one, ONE_SYM_STRING),
        ("c_DH_neutral", c_dh_neutral, DH_NEUTRAL_SYM_STRING),
    ] {
        assert_eq!(rule.actions.len(), 1, "{}: expected one action", label);
        let action_term = &rule.actions[0].terms[0];
        match action_term {
            Term::App(sym, args) => {
                if let tamarin_term::function_symbols::FunSym::NoEq(s) = sym {
                    assert_eq!(s.name, expected_name, "{}: action term sym name", label);
                    assert_eq!(s.arity, 0, "{}: action term arity", label);
                    assert!(args.is_empty(), "{}: action term args", label);
                } else {
                    panic!("{}: expected NoEq sym, got {:?}", label, sym);
                }
            }
            Term::Lit(Lit::Var(v)) => panic!(
                "{}: REGRESSION — action term is a free variable {:?} \
                     instead of a 0-arity NoEq constant. The `{}` symbol \
                     was not recognised against the MaudeSig; check that \
                     `parse_intruder_rules` seeds the parser state with it.",
                label,
                v,
                String::from_utf8_lossy(expected_name),
            ),
            other => panic!("{}: unexpected action term {:?}", label, other),
        }
    }
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
    let action_term = &rules[0].actions[0].terms[0];
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
