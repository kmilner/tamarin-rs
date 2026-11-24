// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::rule::is_subset_of;

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

// minimize_intruder_rules' trace-mode subsumption goes through
// `equal_subset_rule_up_to_renaming`, whose premise check is the
// SET-subset `is_subset_of` (HS `srpr2 `subsetOf` spr1`): a peer whose
// DISTINCT premise set is a subset subsumes this rule even at higher
// multiplicity.
#[test]
fn minimize_drops_set_subsumed_rule() {
    use tamarin_term::vterm::var_term;
    let Some(maude) = maude_handle() else { return };
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let z = var_term(LVar::new("z", LSort::Msg, 1));
    let name = b"_subsume_test".to_vec();
    // r_j (subsumer): premises [KU(y), KU(y)], conclusion KD(x).
    let r_j = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![ku_fact(y.clone()), ku_fact(y.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    // r_i (subsumed): premises [KU(y), KU(z)], same conclusion KD(x).
    // The conclusions unify by the empty (renaming) substitution, and
    // distinct premises of r_j ({KU(y)}) ⊆ distinct premises of r_i
    // ({KU(y), KU(z)}), so r_j subsumes r_i → r_i dropped.  r_j itself
    // is not dropped: KU(z) of r_i is absent from r_j's premise set.
    let r_i = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![ku_fact(y.clone()), ku_fact(z.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    let out = minimize_intruder_rules(&maude, vec![r_j.clone(), r_i.clone()]);
    // Set-subset: r_i is dropped; only r_j survives.  (Multiset bookkeeping
    // would have kept both, since r_j has two KU(y) but r_i only one.)
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].premises, r_j.premises);
}

// `equal_subset_rule_up_to_renaming` answers false when the head
// conclusions' tags differ (`unifyLNFactEqs` = []), and when an `r2` premise
// has no `r1` premise to map onto even though the conclusions unify.
#[test]
fn equal_subset_rejects_unmatched_conclusions_and_premises() {
    use tamarin_term::vterm::var_term;
    let Some(maude) = maude_handle() else { return };
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let name = b"_subset_reject_test".to_vec();
    let mk = |prems: Vec<LNFact>, conc: LNFact| {
        Rule::new(
            IntrRuleACInfo::DestrRule {
                name: name.clone(),
                remaining_applications: -1,
                rhs_is_proper_subterm: true,
                rhs_is_constant: false,
                funs: vec![],
            },
            prems,
            vec![conc],
            vec![],
        )
    };
    // (a) conclusion KD(x) vs KU(x): tags differ.
    let r1 = mk(vec![ku_fact(y.clone())], kd_fact(x.clone()));
    let r2 = mk(vec![ku_fact(y.clone())], ku_fact(x.clone()));
    assert!(!equal_subset_rule_up_to_renaming(&maude, &r1, &r2));
    // (b) r2's KD(y) premise has no KD premise in r1 to map onto, even
    // though the KD(x) conclusions unify by a renaming.
    let r1 = mk(vec![ku_fact(y.clone())], kd_fact(x.clone()));
    let r2 = mk(vec![kd_fact(y.clone())], kd_fact(x.clone()));
    assert!(!equal_subset_rule_up_to_renaming(&maude, &r1, &r2));
}

/// A `[ KU(v) ] --[ KU(t) ]-> [ KU(t) ]` rule over the single variable `v`.
fn ku_rule_over_var(v: &str, t: impl Fn(LNTerm) -> LNTerm) -> IntrRuleAC {
    use tamarin_term::function_symbols::pair_sym;
    let a = var_term(LVar::new(v, LSort::Msg, 0));
    let concfact = ku_fact(t(a.clone()));
    Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_shape".to_vec(),
            fun: FunSym::NoEq(pair_sym()),
        },
        vec![ku_fact(a)],
        vec![concfact.clone()],
        vec![concfact],
    )
}

// `minimize_intruder_rules` keeps the HS `go` survivors in order, on rules
// whose conclusions differ in top symbol, share it without being
// duplicates, and are alpha-variants.
#[test]
fn minimize_keeps_the_hs_survivors_in_order() {
    use tamarin_term::builtin::pair;
    use tamarin_term::function_symbols::fst_dest_sym;
    use tamarin_term::term::f_app_no_eq;
    let Some(maude) = maude_handle() else { return };
    let fst_rule = ku_rule_over_var("d", |a| f_app_no_eq(fst_dest_sym(), vec![a]));
    // Pair-shaped like the duplicates, but `pair(c, pair(c,c))` and
    // `pair(b,b)` fail the occurs check.
    let collide_rule = ku_rule_over_var("c", |a| pair(a.clone(), pair(a.clone(), a)));
    // True duplicates: alpha-variants of one another.
    let dup_a = ku_pair_rule_with_var("a", 0);
    let dup_b = ku_pair_rule_with_var("b", 1);

    let rules = vec![
        dup_a.clone(),
        fst_rule.clone(),
        collide_rule.clone(),
        dup_b.clone(),
    ];
    // HS `go` drops a rule as soon as a peer in `checked ++ unchecked`
    // matches, so of the two duplicates the EARLIER one goes: `dup_a`
    // sees `dup_b` in `unchecked`, while `dup_b` sees no kept duplicate.
    let out = minimize_intruder_rules(&maude, rules);
    assert_eq!(out, vec![fst_rule, collide_rule, dup_b]);
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

/// `subtermConstructorRules` on a sym-enc signature yields only
/// CONSTRUCTOR rules (the senc constructor; the sdec destructors come
/// from the narrowing-based `destruction_rules_no_eq` instead).
#[test]
fn subterm_constructor_rules_emits_only_constructors() {
    let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
    let Some(maude) = maude_handle_for(sig.clone()) else {
        return;
    };
    let rules = subterm_constructor_rules(&maude, &sig);
    assert!(
        rules
            .iter()
            .all(|r| matches!(r.info, IntrRuleACInfo::ConstrRule { .. })),
        "subterm_constructor_rules must yield only ConstrRules"
    );
    assert!(
        !rules.is_empty(),
        "sym-enc sig has at least the senc constructor"
    );
}

#[test]
fn construction_rules_premise_count_equals_arity() {
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    for r in construction_rules(&sig.user_defined_st_fun_syms()) {
        // Pull the symbol's arity from the rule's KU action term.
        let conc_term = &r.conclusions[0].terms[0];
        let arity = match conc_term {
            tamarin_term::term::Term::App(_, args) => args.len(),
            tamarin_term::term::Term::Lit(_) => 0,
        };
        assert_eq!(
            r.premises.len(),
            arity,
            "premise count must equal symbol arity"
        );
        assert_eq!(r.conclusions.len(), 1);
        assert_eq!(r.actions.len(), 1);
    }
}

// =========================================================================
// Haskell-faithfulness invariants for `destruction_rules`.
//
// Mirrors IntruderRules.hs.  Two easy-to-break patterns:
//
//   1. Pattern #1: at the LAST position step, if the
//      current term is an FApp AND rhs has free vars, return [].
//      (The "skip-last" case.)
//
//   2. Private-symbol stop: descending through a Private
//      constructor terminates the loop early.
// =========================================================================

/// `destructionRules` for the sym-enc rule `sdec(senc(x, y), y) = x`
/// must emit EXACTLY ONE destructor, not two.
///
/// The rule has rhs position [0, 0] — two steps.  Without the
/// skip-last guard, Rust emits a second (degenerate) destructor at
/// the inner step, producing `KD(x) + KU(...) → KD(x)` — a
/// self-loop that explodes the chain search on denning_sacco.
#[test]
fn destruction_rules_sym_enc_emits_exactly_one_destructor() {
    let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(r))
        .collect();
    assert_eq!(
        rules.len(),
        1,
        "sym-enc rule `sdec(senc(x, y), y) = x` must yield EXACTLY ONE \
             destructor — the skip-last pattern (IntruderRules.hs) \
             elides the inner step.  Got {} rules.  If this regresses, \
             denning_sacco-class chain explosion will silently reappear.",
        rules.len()
    );
    let r = &rules[0];
    // Premise[0] is KD(senc(x, y)).  The premises after it are KU(y).  The
    // single conclusion is the extracted KD(x).
    assert_eq!(r.premises[0].tag, crate::fact::FactTag::Kd);
    // The code elides the inner step, so there is no
    // `KD(x) KU(x) -> KD(x)` self-loop.
    for p in &r.premises[1..] {
        assert_eq!(p.tag, crate::fact::FactTag::Ku);
    }
    assert_eq!(r.conclusions.len(), 1);
    assert_eq!(r.conclusions[0].tag, crate::fact::FactTag::Kd);
}

/// `destructionRules` for the asym-enc rule
/// `adec(aenc(x, pk(y)), y) = x` likewise emits EXACTLY ONE
/// destructor (position [0, 0], rhs free var x).
#[test]
fn destruction_rules_asym_enc_emits_exactly_one_destructor() {
    let sig = tamarin_term::maude_sig::asym_enc_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(r))
        .collect();
    assert_eq!(
        rules.len(),
        1,
        "asym-enc rule must yield EXACTLY ONE destructor; got {} rules. \
             Skip-last pattern was probably regressed.",
        rules.len()
    );
}

/// `destructionRules` for pair `fst(<x,y>) = x` and `snd(<x,y>) = y`
/// each yield EXACTLY ONE destructor.  Pair is a one-step rule
/// (position [0]), but skip-last doesn't apply to the FIRST step
/// because step_idx == 0 and pos_iter.len() == 1 → step_idx+1 == len,
/// and `t` is `pair(x,y)` (FApp) and rhs is a var (free) — so
/// skip-last DOES fire.  This means the destructor must be emitted
/// at the WRAPPING-step (the outer match arm where we step from
/// the destructor's lhs into pair), NOT at the inner step.
///
/// (This is subtle and worth pinning explicitly.)
#[test]
fn destruction_rules_pair_emits_exactly_two_destructors() {
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let rules: Vec<IntrRuleAC> = sig
        .st_rules
        .iter()
        .flat_map(|r| destruction_rules(r))
        .collect();
    assert_eq!(
        rules.len(),
        2,
        "pair signature must yield exactly fst + snd destructors \
             (2 total); got {} rules.  Pair rules are `fst(<x,y>) = x` \
             and `snd(<x,y>) = y` at position [0] each.",
        rules.len()
    );
}

// =========================================================================
// `equal_rule_up_to_renaming` (Theory/Model/Rule.hs).  Mirrors HS:
//
//   equalRuleUpToRenaming r1 r2 = reader $ \hnd ->
//     case eqs of
//       Nothing   -> False
//       Just eqs' -> (rn1 == rn2) && any isRenamingPerRule (unifs eqs' hnd)
//
// Pin both ends of the predicate: a positive (two rules differing only
// in variable names) and a negative (structurally different).
// =========================================================================
use tamarin_test_support::require_maude_path;

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

/// Build a rule `[ KU(a) ] --[ KU(pair(a, a)) ]-> [ KU(pair(a, a)) ]`
/// (a constructor-shape rule with one var `a`).  Used to test
/// `equal_rule_up_to_renaming` with two alpha-equivalent rules.
fn ku_pair_rule_with_var(var_name: &str, idx: u64) -> IntrRuleAC {
    use tamarin_term::builtin::pair;
    use tamarin_term::function_symbols::pair_sym;
    use tamarin_term::lterm::{LSort, LVar};
    let a = var_term(LVar::new(var_name, LSort::Msg, idx));
    let p = pair(a.clone(), a.clone());
    Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_pair".to_vec(),
            fun: FunSym::NoEq(pair_sym()),
        },
        vec![ku_fact(a.clone())],
        vec![ku_fact(p.clone())],
        vec![ku_fact(p)],
    )
}

/// Positive: two rules that differ ONLY in their bound variable's
/// name (and possibly idx) must compare equal-up-to-renaming.
///
/// HS: `unifyLNTerm` produces a renaming `[x.0 ~> y.7]`; its
/// restriction to each rule's vars (each is the singleton `{x.0}`
/// vs `{y.7}`) is a renaming, so `isRenamingPerRule` holds.
#[test]
fn equal_rule_up_to_renaming_alpha_equivalent_pair_rules() {
    let Some(maude) = maude_handle() else { return };
    let r1 = ku_pair_rule_with_var("x", 0);
    let r2 = ku_pair_rule_with_var("y", 7);
    assert!(
        equal_rule_up_to_renaming(&maude, &r1, &r2),
        "two rules differing only in their bound var's name+idx \
             must be equal-up-to-renaming.  HS: `unifyLNTerm` yields a \
             renaming `[x.0 ~> y.7]`, isRenaming on each rule's restricted \
             var set holds.  See Theory/Model/Rule.hs."
    );
    // Symmetric: r2 vs r1.
    assert!(
        equal_rule_up_to_renaming(&maude, &r2, &r1),
        "equal_rule_up_to_renaming must be symmetric"
    );
    // Reflexive: r1 vs r1.
    assert!(
        equal_rule_up_to_renaming(&maude, &r1, &r1),
        "equal_rule_up_to_renaming must be reflexive"
    );
}

/// Negative: two rules with structurally different conclusions
/// (different fact shapes) must NOT be equal-up-to-renaming.
///
/// HS: `matchFacts` returns `Nothing` because tags differ → False.
#[test]
fn equal_rule_up_to_renaming_structurally_different_rules_diverge() {
    use tamarin_term::lterm::{LSort, LVar};
    let Some(maude) = maude_handle() else { return };
    let r1 = ku_pair_rule_with_var("x", 0);
    // r2 has a single KU premise but a DIFFERENT conclusion shape:
    // it concludes KU(x) (the variable directly) instead of
    // KU(pair(x, x)).  No renaming can make `KU(x)` == `KU(pair(x, x))`.
    let a = var_term(LVar::new("x", LSort::Msg, 0));
    let r2 = Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_pair".to_vec(),
            fun: FunSym::NoEq(tamarin_term::function_symbols::pair_sym()),
        },
        vec![ku_fact(a.clone())],
        vec![ku_fact(a.clone())],
        vec![ku_fact(a)],
    );
    assert!(
        !equal_rule_up_to_renaming(&maude, &r1, &r2),
        "rules with structurally distinct conclusions (KU(pair(x,x)) \
             vs KU(x)) cannot be equal-up-to-renaming — no unifier \
             matches `pair(x,x) =? x`.  HS: matchFacts builds the eqs, \
             unifyLNTerm fails or yields a non-renaming."
    );
    // Different info also makes them unequal even when terms match.
    let r3 = Rule::new(
        IntrRuleACInfo::ConstrRule {
            name: b"_OTHER".to_vec(),
            fun: FunSym::NoEq(tamarin_term::function_symbols::pair_sym()),
        },
        r1.premises.clone(),
        r1.conclusions.clone(),
        r1.actions.clone(),
    );
    assert!(
        !equal_rule_up_to_renaming(&maude, &r1, &r3),
        "differing info field (rule names) must short-circuit to False \
             — HS: `if r1.info /= r2.info then False else ...`"
    );
}

// =========================================================================
// `variants_intruder` (IntruderRules.hs).
// =========================================================================

/// HS's `guard` (IntruderRules.hs) drops the identity variant of a rule
/// whose conclusion is also a premise: `ruvariant /= ru` and
/// `rConcs \\ rPrems /= []` both fail.  A broken Maude round trip would
/// fall back to `vec![ru]` before the filters, so this also checks it.
#[test]
fn variants_intruder_drops_a_premise_covered_identity_variant() {
    let Some(maude) = maude_handle() else { return };
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    // `[ KD(x) ] --> [ KD(x) ]`: `rConcs \\ rPrems == []`, and the
    // identity variant is the rule itself, so `ruvariant == ru` too.
    let ru = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: b"_conc_in_prems".to_vec(),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![],
        },
        vec![kd_fact(x.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );

    assert!(
        variants_intruder(&maude, &ru).is_empty(),
        "the identity variant of a rule whose conclusion is also a premise \
         must be dropped"
    );
}

/// `destructionRules` short-circuits when the rhs is a closed term
/// (no free vars) AND `diff=false` AND rhs has no Private symbol.
/// This is the outer guard at IntruderRules.hs — the function
/// returns [] before even starting the position walk.
///
/// Pin this by constructing a CtxtStRule whose rhs is a public
/// constant (no free vars).
#[test]
fn destruction_rules_returns_empty_for_closed_rhs_in_non_diff_mode() {
    use tamarin_term::builtin::{pair, senc};
    use tamarin_term::lterm::{LNTerm, LSort, LVar, Name, NameId, NameTag};
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Build: lhs = senc(x, pair($a, $b)), rhs = $a (pub const, no frees).
    // Position [1, 0] — into senc's arg 1 (the pair), then into pair's
    // arg 0 ($a).
    let x = LVar::new("x", LSort::Msg, 1);
    let pub_a = Name {
        tag: NameTag::Pub,
        id: NameId::new("a"),
    };
    let pub_b = Name {
        tag: NameTag::Pub,
        id: NameId::new("b"),
    };
    let pa: LNTerm = Term::Lit(Lit::Con(pub_a));
    let pb: LNTerm = Term::Lit(Lit::Con(pub_b));
    let lhs = senc(Term::Lit(Lit::Var(x)), pair(pa.clone(), pb));
    let rhs_st = StRhs {
        positions: vec![vec![1, 0]],
        term: pa,
    };
    let rule = CtxtStRule::new(lhs, rhs_st);

    // diff=false, rhs has no free vars, rhs has no private symbol →
    // outer guard returns [].
    let out = destruction_rules(&rule);
    assert!(
        out.is_empty(),
        "diff=false + closed rhs (no frees, no private) must short-\
             circuit to empty.  Mirrors IntruderRules.hs outer guard. \
             Got {} rules.",
        out.len()
    );
}

// =========================================================================
// `dh_intruder_rules` (IntruderRules.hs — definition above).
//
// The expected output for `dh_intruder_rules(false)` is exactly the
// contents of `data/intruder_variants_dh.spthy`, which the HS
// production pipeline embeds and parses (TheoryLoader.hs).
// That file has:
//   * 5 ConstrRules: `_exp` `_inv` `_DH_neutral` `_one` `_mult`
//   * 45 `d_exp` (DestrRule "_exp")  destructor variants
//   * 1  `d_inv` (DestrRule "_inv")  destructor variant
//   = 51 rules total.
//
// We measured this directly:
//   $ grep -c "^rule" data/intruder_variants_dh.spthy
//   51
//   $ grep -c "^rule (modulo AC) c_" data/intruder_variants_dh.spthy → 5
//   $ grep -c "^rule (modulo AC) d_exp" data/intruder_variants_dh.spthy → 45
//   $ grep -c "^rule (modulo AC) d_inv" data/intruder_variants_dh.spthy → 1
//
// The variants enumeration depends on Maude's narrowing
// implementation; the exact count is Maude-version-sensitive.  We
// assert structural invariants (constructor count, name shapes,
// KU/KD wiring) and let a slightly-looser bound check the variants
// count, deferring exact byte parity to the corpus probe.
// =========================================================================

fn dh_maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    maude_handle_for(tamarin_term::maude_sig::dh_maude_sig())
}

fn bp_maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    maude_handle_for(tamarin_term::maude_sig::bp_maude_sig())
}

/// `bp_intruder_rules(false)` yields exactly 74 bilinear-pairing
/// intruder rules (2 constructors `_pmult`/`_em` + the pmult- and
/// em-destructor variant expansions), matching HS `bpIntruderRules
/// False` in the pinned upstream tree, whose Maude-backed
/// `minimizeIntruderRules` subsumption drops one BP destructor
/// variant.  Upstream's committed `data/intruder_variants_bp.spthy`
/// holds 75 rules; production loads that cached file byte-for-byte
/// (as HS does), so this count applies to the generator only.
#[test]
fn bp_intruder_rules_yields_74() {
    let Some(maude) = bp_maude_handle() else {
        return;
    };
    let rules = bp_intruder_rules(&maude);
    assert_eq!(
        rules.len(),
        74,
        "bp_intruder_rules(false) must produce exactly 74 rules; got {}",
        rules.len()
    );
    // Sanity: the two construction rules are present and named.
    let constr_names: Vec<&[u8]> = rules
        .iter()
        .filter_map(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
            _ => None,
        })
        .collect();
    assert!(constr_names.contains(&b"_pmult".as_slice()));
    assert!(constr_names.contains(&b"_em".as_slice()));
}

/// Helper: extract the bytestring name of a ConstrRule or DestrRule.
fn rule_name(info: &IntrRuleACInfo) -> Option<&[u8]> {
    match info {
        IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
        IntrRuleACInfo::DestrRule { name, .. } => Some(name.as_slice()),
        _ => None,
    }
}

/// `dh_intruder_rules(false)` returns the 5 hard-coded constructor
/// rules (`_exp`, `_inv`, `_DH_neutral`, `_one`, `_mult`) plus a
/// non-empty list of destructor variants.  The 5 ConstrRules are
/// the immediately-known core; the variant count depends on Maude's
/// narrowing enumeration but is at minimum 1 (the identity variant
/// of `_exp` or `_inv` survives `applyFilters=True` filters when
/// the variant has non-ground conclusions).
///
/// HS reference: IntruderRules.hs.  The cached output at
/// `data/intruder_variants_dh.spthy` shows the expected shape (5
/// constr + 45 d_exp + 1 d_inv = 51 rules total).
#[test]
fn dh_intruder_rules_emits_five_constructors_and_some_destructors() {
    let Some(maude) = dh_maude_handle() else {
        return;
    };
    let rules = dh_intruder_rules(&maude);

    // 5 ConstrRules with the known names.
    let names: Vec<&[u8]> = rules
        .iter()
        .filter_map(|r| match &r.info {
            IntrRuleACInfo::ConstrRule { name, .. } => Some(name.as_slice()),
            _ => None,
        })
        .collect();
    assert_eq!(
        names.len(),
        5,
        "expected exactly 5 ConstrRules (_exp/_inv/_DH_neutral/_one/_mult); \
             got: {:?}",
        names
            .iter()
            .map(|n| String::from_utf8_lossy(n).to_string())
            .collect::<Vec<_>>()
    );
    // All constructor names start with `_` (HS pack "_" prefix).
    for n in &names {
        assert!(
            n.starts_with(b"_"),
            "constructor rule name must start with `_` (HS appends pack \"_\" — \
                 IntruderRules.hs); got {}",
            String::from_utf8_lossy(n)
        );
    }
    // Specific names present.
    let name_strings: Vec<&[u8]> = names.to_vec();
    for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
        assert!(
            name_strings.contains(expected),
            "missing constructor rule named {}; got names {:?}",
            String::from_utf8_lossy(expected),
            name_strings
                .iter()
                .map(|n| String::from_utf8_lossy(n).to_string())
                .collect::<Vec<_>>()
        );
    }

    // Destructor rules also present (variants of _exp and _inv).
    let destrs: Vec<&IntrRuleAC> = rules
        .iter()
        .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule { .. }))
        .collect();
    assert!(
        !destrs.is_empty(),
        "expected at least one DestrRule variant (HS \
             `variantsIntruder (exp-destr|inv-destr)` produces several); \
             got 0 destructors out of {} total rules",
        rules.len()
    );
    for d in &destrs {
        let n = rule_name(&d.info).expect("DestrRule has name");
        assert!(
            n.starts_with(b"_"),
            "destructor rule name must start with `_`; got {}",
            String::from_utf8_lossy(n)
        );
    }

    // EXACT byte-faithful shape vs HS `dhIntruderRules False`
    // (data/intruder_variants_dh.spthy): 5 constr + 45 `d_exp` +
    // 1 `d_inv` = 51 rules.  The lone `d_inv` is the swap variant
    // `[KD(inv(x))] -> [KD(x)]`; the IDENTITY variants of the `_exp`
    // and `_inv` destructors (`KD(x)->KD(inv(x))`, `[KD(x),KU(y)]->
    // [KD(x^y)]`) MUST be dropped — Maude returns them as `x0 --> #N`
    // fresh-witness renamings which HS's `removeRenamings`
    // (Maude/Types.hs) collapses to the empty subst, so the
    // `ruvariant /= ru` guard (IntruderRules.hs) discards them.
    // A regression here (53 rules: +1 d_exp, +1 d_inv) means the
    // `removeRenamings` in `MaudeHandle::variants` was lost.
    let (n_exp, n_inv) = destrs.iter().fold((0usize, 0usize), |(e, i), d| {
        let n = rule_name(&d.info).unwrap();
        let s = String::from_utf8_lossy(n);
        if s.contains("inv") {
            (e, i + 1)
        } else if s.contains("exp") {
            (e + 1, i)
        } else {
            (e, i)
        }
    });
    assert_eq!(
        rules.len(),
        51,
        "dhIntruderRules must yield exactly 51 rules (5 constr + 45 d_exp \
             + 1 d_inv) byte-identically to HS; got {} (n_exp={}, n_inv={}). \
             53 indicates the dropped-identity-variant `removeRenamings` \
             step regressed.",
        rules.len(),
        n_exp,
        n_inv
    );
    assert_eq!(
        n_exp, 45,
        "expected exactly 45 d_exp destructors; got {}",
        n_exp
    );
    assert_eq!(
        n_inv, 1,
        "expected exactly 1 d_inv destructor (the swap \
             variant); got {} (2 means the identity variant KD(x)->KD(inv(x)) \
             leaked)",
        n_inv
    );
}

/// The 5 ConstrRules MUST have the HS-specified shape:
/// - `_exp` premises: `[KU(x.0), KU(x.1)]`, conc: `KU(exp(x.0, x.1))`
/// - `_inv` premises: `[KU(x.0)]`, conc: `KU(inv(x.0))`
/// - `_DH_neutral` premises: `[]`, conc: `KU(DH_neutral)`
/// - `_one` premises: `[]`, conc: `KU(one)`
/// - `_mult` premises: `[KU(x.0), KU(x.1)]`, conc: `KU(x.0 * x.1)`
///
/// HS: see expRule/invRule/multRule/oneRule/dhNeutralRule helpers at
/// IntruderRules.hs — each is `Rule mkInfo prems [concfact]
/// (mkAction concfact) []` where `concfact = kudFact conc`.
#[test]
fn dh_intruder_rules_constructors_have_expected_shape() {
    let Some(maude) = dh_maude_handle() else {
        return;
    };
    let rules = dh_intruder_rules(&maude);
    let find = |name: &[u8]| -> &IntrRuleAC {
        rules
            .iter()
            .find(|r| match &r.info {
                IntrRuleACInfo::ConstrRule { name: n, .. } => n.as_slice() == name,
                _ => false,
            })
            .unwrap_or_else(|| {
                panic!(
                    "no constructor rule named {}",
                    String::from_utf8_lossy(name)
                )
            })
    };

    // All constructor rules emit a single action equal to the conclusion
    // (HS: `mkAction = return`, so `acts = [concfact]`).
    for name in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
        let r = find(name);
        assert_eq!(
            r.conclusions.len(),
            1,
            "{}: must have 1 conclusion",
            String::from_utf8_lossy(name)
        );
        assert_eq!(
            r.actions.len(),
            1,
            "{}: HS `return concfact` ⇒ 1 action",
            String::from_utf8_lossy(name)
        );
        assert_eq!(
            r.actions[0],
            r.conclusions[0],
            "{}: action must equal conclusion (HS `mkAction concfact` ⇒ \
                 `[concfact]`)",
            String::from_utf8_lossy(name)
        );
        // No `new_vars`.
        assert!(
            r.new_vars.is_empty(),
            "{}: constructors have empty new_vars (HS Rule mkInfo prems concs acts [])",
            String::from_utf8_lossy(name)
        );
        // Every fact tag is KU (HS `kudFact = kuFact`).
        for f in r.premises.iter().chain(&r.conclusions).chain(&r.actions) {
            assert_eq!(
                f.tag,
                FactTag::Ku,
                "{}: all facts must be KU (HS `kudFact = kuFact`)",
                String::from_utf8_lossy(name)
            );
        }
    }

    // Premise counts match HS shape.
    assert_eq!(
        find(b"_exp").premises.len(),
        2,
        "_exp: 2 KU premises (HS expRule)"
    );
    assert_eq!(
        find(b"_inv").premises.len(),
        1,
        "_inv: 1 KU premise (HS invRule)"
    );
    assert_eq!(
        find(b"_DH_neutral").premises.len(),
        0,
        "_DH_neutral: 0 premises"
    );
    assert_eq!(find(b"_one").premises.len(), 0, "_one: 0 premises");
    assert_eq!(find(b"_mult").premises.len(), 2, "_mult: 2 KU premises");
}

/// Destructor rules in `dh_intruder_rules` are KD-rules: their
/// first premise (the term-being-deconstructed) has KD tag, the
/// conclusion is KD, and actions are empty (HS `mkAction = const []`
/// for destructors).
#[test]
fn dh_intruder_rules_destructors_have_kd_shape() {
    let Some(maude) = dh_maude_handle() else {
        return;
    };
    let rules = dh_intruder_rules(&maude);
    let destrs: Vec<&IntrRuleAC> = rules
        .iter()
        .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule { .. }))
        .collect();
    assert!(
        !destrs.is_empty(),
        "expected at least one destructor variant"
    );
    for d in &destrs {
        assert!(
            !d.premises.is_empty(),
            "destructor must have premises; got rule with 0 prems"
        );
        assert_eq!(
            d.premises[0].tag,
            FactTag::Kd,
            "destructor's first premise must be KD (HS `kudFact = kdFact`)"
        );
        assert_eq!(
            d.conclusions.len(),
            1,
            "destructor must have exactly 1 KD conclusion"
        );
        assert_eq!(
            d.conclusions[0].tag,
            FactTag::Kd,
            "destructor conclusion must be KD"
        );
        assert!(
            d.actions.is_empty(),
            "destructor actions must be empty (HS `mkAction = const []`)"
        );
        assert!(d.new_vars.is_empty(), "destructor new_vars must be empty");
    }
}
