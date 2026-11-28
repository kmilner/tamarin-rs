// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::rule::is_subset_of;
use tamarin_test_support::require_maude_path;

/// Pins every `show_fun_sym_name` arm to the display name HS
/// `showFunSymName` (Term/Term.hs) produces.  The arms read
/// `tamarin_term::function_symbols`' `*SymString` constants, which are
/// also what `maude_print` emits into the Maude module, so an edit to one
/// of them moves intruder-rule names, `close_rule.rs` case names and
/// `reduction.rs` term rendering in lockstep — this test is what makes
/// such an edit loud.
///
/// Note the `Union` trap: it renders as `munSymString` ("mun"), NOT
/// `unionSymString` ("union").
#[test]
fn show_fun_sym_name_pins_the_builtin_display_names() {
    use tamarin_term::function_symbols::{
        pair_sym, AcFctSym, AcSym, CSym, Constructability, NdcState, Privacy,
    };
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::Union)), "mun");
    assert_ne!(show_fun_sym_name(&FunSym::Ac(AcSym::Union)), "union");
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::Mult)), "mult");
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::Xor)), "xor");
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::NatPlus)), "tplus");
    assert_eq!(show_fun_sym_name(&FunSym::C(CSym::EMap)), "em");
    assert_eq!(show_fun_sym_name(&FunSym::List), "List");
    // The two user arms print the symbol's own interned name.
    assert_eq!(show_fun_sym_name(&FunSym::NoEq(pair_sym())), "pair");
    let ac_foo = AcFctSym::new(
        b"foo".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    assert_eq!(show_fun_sym_name(&FunSym::Ac(AcSym::AcFct(ac_foo))), "foo");
}

// Pins HS `subsetOf` (Utils/Misc.hs) as a SET subset:
// `(S.fromList xs) `S.isSubsetOf` (S.fromList ys)` deduplicates BOTH
// sides, so `is_subset_of` must ignore multiplicity entirely.
#[test]
fn is_subset_of_ignores_multiplicity() {
    use tamarin_term::vterm::var_term;
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let z = var_term(LVar::new("z", LSort::Msg, 0));
    // {KU(y)} ⊆ {KU(y), KU(z)}: as a SET subset (HS `subsetOf`) this holds
    // even though a=[KU(y),KU(y)] has higher multiplicity than the single
    // KU(y) in b — a multiset-subset check would reject it (no second
    // KU(y) in b to consume).
    let a = vec![ku_fact(y.clone()), ku_fact(y.clone())];
    let b = vec![ku_fact(y.clone()), ku_fact(z.clone())];
    assert!(is_subset_of(&a, &b));
    // A distinct element of `a` not in `b` ⇒ not a subset.
    assert!(!is_subset_of(&b, &a));
}

// This test covers `specialIntruderRules` (IntruderRules.hs) in full.
// It checks the five rules in HS's list order.  For each rule it
// compares the premises, the conclusions, the actions and the new variables.
// The sort of each rule's variable carries meaning, and a check on the fact
// tags alone does not see it.  The `x:pub` of `PubConstr` is what makes
// `!KU($x)` derivable for public names only.  The `x:fresh` of `FreshConstr`
// is what ties the rule to an `Fr` premise.
#[test]
fn special_rules_have_the_hs_shapes() {
    use crate::fact::{fresh_fact, in_fact, k_log_fact, kd_fact, ku_fact, out_fact};
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let x_pub = var_term(LVar::new("x", LSort::Pub, 0));
    let x_fresh = var_term(LVar::new("x", LSort::Fresh, 0));

    let r = special_intruder_rules();
    assert_eq!(r.len(), 5);
    assert!(matches!(r[0].info, IntrRuleACInfo::Coerce));
    assert!(matches!(r[1].info, IntrRuleACInfo::PubConstr));
    assert!(matches!(r[2].info, IntrRuleACInfo::FreshConstr));
    assert!(matches!(r[3].info, IntrRuleACInfo::ISend));
    assert!(matches!(r[4].info, IntrRuleACInfo::IRecv));

    // (label, premises, conclusions, actions, new_vars)
    let expected: [(&str, Vec<LNFact>, Vec<LNFact>, Vec<LNFact>, Vec<LNTerm>); 5] = [
        (
            "Coerce: [KD(x)] --[KU(x)]-> [KU(x)]",
            vec![kd_fact(x.clone())],
            vec![ku_fact(x.clone())],
            vec![ku_fact(x.clone())],
            vec![],
        ),
        (
            "PubConstr: [] --[KU($x)]-> [KU($x)], $x rule-new",
            vec![],
            vec![ku_fact(x_pub.clone())],
            vec![ku_fact(x_pub.clone())],
            vec![x_pub],
        ),
        (
            "FreshConstr: [Fr(~x)] --[KU(~x)]-> [KU(~x)]",
            vec![fresh_fact(x_fresh.clone())],
            vec![ku_fact(x_fresh.clone())],
            vec![ku_fact(x_fresh)],
            vec![],
        ),
        (
            "ISend: [KU(x)] --[K(x)]-> [In(x)]",
            vec![ku_fact(x.clone())],
            vec![in_fact(x.clone())],
            vec![k_log_fact(x.clone())],
            vec![],
        ),
        (
            "IRecv: [Out(x)] --[]-> [KD(x)]",
            vec![out_fact(x.clone())],
            vec![kd_fact(x.clone())],
            vec![],
            vec![],
        ),
    ];
    for (rule, (label, prems, concs, acts, nvs)) in r.iter().zip(expected) {
        assert_eq!(rule.premises, prems, "{label}: premises");
        assert_eq!(rule.conclusions, concs, "{label}: conclusions");
        assert_eq!(rule.actions, acts, "{label}: actions");
        assert_eq!(rule.new_vars, nvs, "{label}: new_vars");
    }
}

// =========================================================================
// construction_rules: per-symbol KU constructor generation.
//
// Direct Haskell-spec mirror — Theory.Tools.IntruderRules.hs:
//
//     constructionRules fSig =
//         [ createRuleNoEq s f k | NoEqUser f@(s,(k,Public,Constructor,_)) <- S.toList fSig ] ++
//         [ createRuleAC s f | ACfctUser f@(s,(Public,Constructor,_)) <- S.toList fSig ]
// =========================================================================

/// The `Constructability` filter of HS `constructionRules`
/// (IntruderRules.hs) is the purpose of the comprehension.  A test that
/// runs against one signature does not see the filter.  `pairMaudeSig` and
/// `pairDestMaudeSig` carry the same three names.  They differ only in
/// whether `fst` and `snd` are constructors.  Without the filter, the code
/// emits `_fst` and `_snd` KU-construction rules under `dest-pairing`.  That
/// lets the intruder construct a projection that it may only narrow.
#[test]
fn construction_rules_emit_one_rule_per_public_constructor() {
    let names = |sig: &tamarin_term::maude_sig::MaudeSig| -> Vec<String> {
        let mut ns: Vec<String> = construction_rules(&sig.user_defined_st_fun_syms())
            .iter()
            .map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule { name, .. } => {
                    String::from_utf8_lossy(name).to_string()
                }
                other => panic!("expected ConstrRule, got {other:?}"),
            })
            .collect();
        ns.sort();
        ns
    };
    // `pair/2`, `fst/1`, `snd/1`, all Public+Constructor.
    assert_eq!(
        names(&tamarin_term::maude_sig::pair_maude_sig()),
        vec!["_fst", "_pair", "_snd"]
    );
    // Under `dest-pairing` the names are the same, but `fst` and `snd` are
    // destructors.
    assert_eq!(
        names(&tamarin_term::maude_sig::pair_dest_maude_sig()),
        vec!["_pair"]
    );

    // `pair/2` gives 2 KU premises, 1 KU conclusion and 1 KU action.  HS
    // `createRuleNoEq` reuses `concfact` for the conclusion and for the
    // action, so the two are equal.
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let rules = construction_rules(&sig.user_defined_st_fun_syms());
    let pair_rule = rules
        .iter()
        .find(|r| matches!(&r.info, IntrRuleACInfo::ConstrRule { name, .. } if name == b"_pair"))
        .expect("expected pair construction rule");
    assert_eq!(pair_rule.premises.len(), 2);
    assert_eq!(pair_rule.conclusions.len(), 1);
    assert_eq!(pair_rule.actions, pair_rule.conclusions);
    for f in pair_rule
        .premises
        .iter()
        .chain(&pair_rule.conclusions)
        .chain(&pair_rule.actions)
    {
        assert_eq!(f.tag, crate::fact::FactTag::Ku);
    }
}

/// A maude that speaks `sig`, or `None` when no maude resolved at all.  The
/// `None` case is the accepted skip.  See [`tamarin_test_support::require_maude_path`].
///
/// A maude that resolves but does not start is the same misconfiguration as
/// a dangling `MAUDE_PATH`.  An `.ok()` here would silently skip every pin in
/// this file, so this function panics instead.
fn maude_handle_for(
    sig: tamarin_term::maude_sig::MaudeSig,
) -> Option<tamarin_term::maude_proc::MaudeHandle> {
    let path = require_maude_path()?;
    Some(
        tamarin_term::maude_proc::MaudeHandle::start(&path, sig).unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 pin here would otherwise skip silently"
            )
        }),
    )
}

fn maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    maude_handle_for(tamarin_term::maude_sig::pair_maude_sig())
}

/// A `[ KU(v) ] --[ KU(t(v)) ]-> [ KU(t(v)) ]` constructor-shaped rule over
/// the variable `v.idx`.
fn ku_rule(name: &[u8], v: &str, idx: u64, t: impl Fn(LNTerm) -> LNTerm) -> IntrRuleAC {
    let a = var_term(LVar::new(v, LSort::Msg, idx));
    let concfact = ku_fact(t(a.clone()));
    Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: name.to_vec(),
            fun: FunSym::NoEq(tamarin_term::function_symbols::pair_sym()),
        },
        vec![ku_fact(a)],
        vec![concfact.clone()],
        vec![concfact],
    )
}

/// A destructor-shaped rule with the given premises and conclusion.
fn destr_rule(prems: Vec<LNFact>, conc: LNFact) -> IntrRuleAC {
    Rule::new(
        IntrRuleACInfo::DestrRule {
            name: b"_d".to_vec(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        prems,
        vec![conc],
        vec![],
    )
}

enum Subsumption {
    /// `equalRuleUpToRenaming r1 r2` (Theory/Model/Rule.hs): same info and
    /// a unifier that renames each rule.
    Equal(IntrRuleAC, IntrRuleAC, bool),
    /// `equalSubsetRuleUpToRenaming r1 r2`: the conclusions unify by a
    /// renaming and r2's premises map into r1's as a SET (`subsetOf`).
    Subset(IntrRuleAC, IntrRuleAC, bool),
    /// `minimizeIntruderRules False`: HS `go` drops a rule as soon as a peer
    /// in `checked ++ unchecked` subsumes it, so of two duplicates the
    /// earlier goes.
    Minimize(Vec<IntrRuleAC>, Vec<IntrRuleAC>),
}

#[test]
fn intruder_rule_subsumption_table() {
    use tamarin_term::builtin::pair;
    use tamarin_term::function_symbols::fst_dest_sym;
    use tamarin_term::term::f_app_no_eq;
    use Subsumption::*;
    let Some(maude) = maude_handle() else { return };
    let v = |n: &str, idx| var_term(LVar::new(n, LSort::Msg, idx));
    let (x, y, z) = (v("x", 0), v("y", 0), v("z", 1));
    let pair_x = ku_rule(b"_pair", "x", 0, |a| pair(a.clone(), a));
    let pair_y7 = ku_rule(b"_pair", "y", 7, |a| pair(a.clone(), a));
    let dup_a = ku_rule(b"_pair", "a", 0, |a| pair(a.clone(), a));
    let dup_b = ku_rule(b"_pair", "b", 1, |a| pair(a.clone(), a));
    let fst_rule = ku_rule(b"_shape", "d", 0, |a| f_app_no_eq(fst_dest_sym(), vec![a]));
    // Pair-shaped like the duplicates, but `pair(c, pair(c, c))` and
    // `pair(b, b)` fail the occurs check.
    let collide_rule = ku_rule(b"_shape", "c", 0, |a| pair(a.clone(), pair(a.clone(), a)));
    // `[KU(y), KU(y)]` subsumes `[KU(y), KU(z)]` with the same conclusion:
    // its distinct premises {KU(y)} are a subset, whatever the multiplicity.
    let subsumer = destr_rule(
        vec![ku_fact(y.clone()), ku_fact(y.clone())],
        kd_fact(x.clone()),
    );
    let subsumed = destr_rule(vec![ku_fact(y.clone()), ku_fact(z)], kd_fact(x.clone()));

    let rows = vec![
        Equal(pair_x.clone(), pair_y7.clone(), true),
        Equal(pair_y7.clone(), pair_x.clone(), true),
        Equal(pair_x.clone(), pair_x.clone(), true),
        // `KU(pair(x, x))` against `KU(x)`: no renaming unifies them.
        Equal(pair_x.clone(), ku_rule(b"_pair", "x", 0, |a| a), false),
        // Different info short-circuits, whatever the facts.
        Equal(
            pair_x.clone(),
            ku_rule(b"_OTHER", "x", 0, |a| pair(a.clone(), a)),
            false,
        ),
        // Conclusion tags differ.
        Subset(
            destr_rule(vec![ku_fact(y.clone())], kd_fact(x.clone())),
            destr_rule(vec![ku_fact(y.clone())], ku_fact(x.clone())),
            false,
        ),
        // r2's `KD(y)` premise has no KD premise in r1 to map onto.
        Subset(
            destr_rule(vec![ku_fact(y.clone())], kd_fact(x.clone())),
            destr_rule(vec![kd_fact(y)], kd_fact(x)),
            false,
        ),
        Minimize(vec![subsumer.clone(), subsumed], vec![subsumer]),
        Minimize(
            vec![dup_a, fst_rule.clone(), collide_rule.clone(), dup_b.clone()],
            vec![fst_rule, collide_rule, dup_b],
        ),
    ];
    for (i, row) in rows.into_iter().enumerate() {
        match row {
            Equal(r1, r2, want) => {
                assert_eq!(
                    equal_rule_up_to_renaming(&maude, &r1, &r2).unwrap(),
                    want,
                    "row {i}"
                )
            }
            Subset(r1, r2, want) => assert_eq!(
                equal_subset_rule_up_to_renaming(&maude, &r1, &r2).unwrap(),
                want,
                "row {i}"
            ),
            Minimize(rules, want) => {
                assert_eq!(
                    minimize_intruder_rules(&maude, rules).unwrap(),
                    want,
                    "row {i}"
                )
            }
        }
    }
}

/// `destructionRules False` (IntruderRules.hs) per subterm-convergent
/// rule: one destructor per rule, whose single `KD` premise is the
/// destructed term and whose other premises are `KU`, concluding one `KD`.
/// The skip-last guard elides the inner step of a two-step position (no
/// `KD(x) KU(..) --> KD(x)` self-loop), and a closed public rhs yields
/// nothing.
#[test]
fn destruction_rules_table() {
    use tamarin_term::builtin::{pair, senc};
    use tamarin_term::lterm::Name;
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::vterm::const_term;
    use tamarin_term::vterm::var_term as vt;

    // `senc(x, <$a, $b>) = $a`, rhs at position [1, 0].
    let a = const_term(Name::new(tamarin_term::lterm::NameTag::Pub, "a"));
    let b = const_term(Name::new(tamarin_term::lterm::NameTag::Pub, "b"));
    let closed = CtxtStRule::new(
        senc(vt(LVar::new("x", LSort::Msg, 1)), pair(a.clone(), b)),
        StRhs {
            positions: vec![vec![1, 0]],
            term: a,
        },
    );
    let rows: [(&str, Vec<CtxtStRule>, usize); 4] = [
        (
            "sym-enc",
            tamarin_term::maude_sig::sym_enc_maude_sig()
                .st_rules
                .into_iter()
                .collect(),
            1,
        ),
        (
            "asym-enc",
            tamarin_term::maude_sig::asym_enc_maude_sig()
                .st_rules
                .into_iter()
                .collect(),
            1,
        ),
        (
            "pair",
            tamarin_term::maude_sig::pair_maude_sig()
                .st_rules
                .into_iter()
                .collect(),
            2,
        ),
        ("closed public rhs", vec![closed], 0),
    ];
    for (case, st_rules, count) in rows {
        let rules: Vec<IntrRuleAC> = st_rules.iter().flat_map(destruction_rules).collect();
        assert_eq!(rules.len(), count, "{case}");
        for r in &rules {
            assert_eq!(r.premises[0].tag, crate::fact::FactTag::Kd, "{case}");
            assert!(
                r.premises[1..]
                    .iter()
                    .all(|p| p.tag == crate::fact::FactTag::Ku),
                "{case}"
            );
            let concs: Vec<_> = r.conclusions.iter().map(|c| c.tag).collect();
            assert_eq!(concs, [crate::fact::FactTag::Kd], "{case}");
        }
    }
}
