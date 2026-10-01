// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::elaborate::formula_to_guarded_parsed;
use tamarin_parser::ast as p;
use tamarin_parser::parser::parse_formula_str;
use tamarin_term::function_symbols::{AcSym, CSym, Constructability, NoEqSym, Privacy};
use tamarin_term::lterm::pub_term;
use tamarin_term::maude_sig::pair_maude_sig;
use tamarin_term::subst::apply_vterm;
use tamarin_term::term::{f_app_ac, f_app_c, f_app_no_eq};

fn g(s: &str) -> Result<Guarded, GuardError> {
    let sig = pair_maude_sig();
    let f = parse_formula_str(s, &sig).map_err(|e| err(format!("parse: {}", e)))?;
    formula_to_guarded_parsed(&f, &sig)
}

/// A free variable leaf of a guarded formula's term.
fn bfree(name: &str, idx: u64, sort: LSort) -> BLNTerm {
    var_term(BVar::Free(LVar::new(name, sort, idx)))
}

/// A public-name leaf of a guarded formula's term.
fn bpub(name: &str) -> BLNTerm {
    pub_term(name)
}

/// A user-declared public constructor of the given arity.
fn user_sym(name: &str, arity: usize) -> NoEqSym {
    NoEqSym::new(
        name.as_bytes().to_vec(),
        arity,
        Privacy::Public,
        Constructability::Constructor,
    )
}

/// An opened atom carries its free variables straight across.
#[test]
fn bvar_to_lvar_frees_an_opened_atom() {
    use crate::atom::ProtoAtom;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    let i = LVar::new("i", LSort::Node, 0);
    let a: Atom<BLNTerm> = ProtoAtom::Last(var_term(tamarin_term::lterm::BVar::Free(i)));
    assert_eq!(bvar_to_lvar(&a), ProtoAtom::Last(var_term(i)));
}

/// HS `bvarToLVar`'s `boundError` (Guarded.hs:326-327): the atom must have
/// every enclosing binder opened before it is read over plain `LVar`s.
#[test]
#[should_panic(expected = "bvarToLVar: left-over bound variable '2'")]
fn bvar_to_lvar_rejects_a_left_over_bound_variable() {
    use crate::atom::ProtoAtom;
    use tamarin_term::vterm::var_term;
    let a: Atom<BLNTerm> = ProtoAtom::Last(var_term(tamarin_term::lterm::BVar::Bound(2)));
    bvar_to_lvar(&a);
}

#[test]
fn ground_truth() {
    let r = g("T").unwrap();
    assert_eq!(r, gtrue());
}

// A guarded fact with the given multiplicity, name and argument count. The
// tag is whatever `fact_tag_of` gives the parser fact, so a reserved name
// reaches its own `FactTag` constructor and every other name stays a
// `ProtoFact`.
fn gf_args(persistent: bool, name: &str, arity: usize) -> Fact<BLNTerm> {
    bfact(
        persistent,
        name,
        (0..arity)
            .map(|i| bfree("a", i as u64, LSort::Msg))
            .collect(),
    )
}

/// A guarded fact over the given argument terms, tagged as `fact_tag_of`
/// tags the parser fact of the same name and arity.
fn bfact(persistent: bool, name: &str, args: Vec<BLNTerm>) -> Fact<BLNTerm> {
    let tag = crate::elaborate::fact_tag_of(&p::Fact {
        persistent,
        name: name.into(),
        args: vec![p::Term::PubLit("_".into()); args.len()],
        annotations: vec![],
    });
    Fact::new(tag, args)
}

fn gf(persistent: bool, name: &str) -> Fact<BLNTerm> {
    gf_args(persistent, name, 0)
}

// The guarded fact order, as the solver reaches it: the derived
// `Ord (ProtoAtom s t)` (Atom.hs:78-84) compares an `Action`'s timepoint and
// then its fact, so a shared timepoint leaves the fact deciding.  The fact
// half is HS `Ord (Fact t)` (Theory/Model/Fact.hs:173-174) — the `FactTag`
// first, then the term list.
fn cmp_gfact(a: &Fact<BLNTerm>, b: &Fact<BLNTerm>) -> std::cmp::Ordering {
    let at = |f: &Fact<BLNTerm>| -> Atom<BLNTerm> {
        ProtoAtom::Action(var_term(BVar::Bound(0)), f.clone())
    };
    at(a).cmp(&at(b))
}

/// `FactTag`'s derived Ord segregates every ProtoFact before every reserved
/// tag and orders the reserved tags in declaration sequence
/// (Theory/Model/Fact.hs:137-148).  `fact_tag_of` recovers the reserved tags
/// from the names the parser canonicalises to (`mkProtoFact`,
/// Theory/Text/Parser/Fact.hs:56-63), leaving every other name a `ProtoFact`.
#[test]
fn guarded_facts_sort_every_proto_before_every_reserved_tag() {
    use std::cmp::Ordering::Less;
    // A ProtoFact with a name that lexically sorts AFTER every reserved
    // name must still come FIRST (the constructor index dominates).
    let proto_z = gf(false, "Zebra");
    for reserved in ["Fr", "Out", "In", "KU", "KD", "Ded"] {
        let persistent = matches!(reserved, "KU" | "KD");
        let s = gf(persistent, reserved);
        assert_eq!(
            cmp_gfact(&proto_z, &s),
            Less,
            "a ProtoFact must sort before the reserved tag {reserved}"
        );
    }
    // The reserved tags order in declaration sequence.
    assert_eq!(cmp_gfact(&gf(false, "Fr"), &gf(false, "Out")), Less);
    assert_eq!(cmp_gfact(&gf(false, "Out"), &gf(false, "In")), Less);
    assert_eq!(cmp_gfact(&gf(false, "In"), &gf(true, "KU")), Less);
    assert_eq!(cmp_gfact(&gf(true, "KU"), &gf(true, "KD")), Less);
    assert_eq!(cmp_gfact(&gf(true, "KD"), &gf(false, "Ded")), Less);
    // "K" and "Term" are ordinary ProtoFacts, so both precede Fr.
    assert_eq!(cmp_gfact(&gf(false, "K"), &gf(false, "Fr")), Less);
    assert_eq!(cmp_gfact(&gf(false, "Term"), &gf(false, "Fr")), Less);
}

/// ProtoFacts compare by the `(Multiplicity, String, Int)` triple, and the
/// arity in that triple is compared BEFORE the term list, exactly as
/// `compare tag tag'` precedes `compare ts ts'`.
#[test]
fn guarded_proto_facts_sort_by_multiplicity_then_name_then_arity() {
    use std::cmp::Ordering::Less;
    // Persistent < Linear.
    assert_eq!(cmp_gfact(&gf(true, "P"), &gf(false, "P")), Less);
    // Then by name.
    assert_eq!(cmp_gfact(&gf(false, "A"), &gf(false, "B")), Less);
    // Then by arity, before any term is looked at: the one-argument fact wins
    // even though its argument sorts AFTER the two-argument fact's first.
    let mk = |args: Vec<BLNTerm>| bfact(false, "P", args);
    assert_eq!(
        cmp_gfact(
            &mk(vec![bfree("z", 0, LSort::Msg)]),
            &mk(vec![bfree("a", 0, LSort::Msg), bfree("a", 1, LSort::Msg)])
        ),
        Less
    );
}

/// The guarded fact ignores its annotations in equality, as HS's `Eq (Fact t)`
/// does (Theory/Model/Fact.hs:169-174).
#[test]
fn guarded_facts_ignore_their_annotations() {
    let plain = gf_args(false, "P", 1);
    let mut annotated = gf_args(false, "P", 1);
    annotated
        .annotations
        .insert(crate::fact::FactAnnotation::SolveFirst);
    assert_eq!(plain, annotated);
    assert_eq!(cmp_gfact(&plain, &annotated), std::cmp::Ordering::Equal);
}

/// A pair is a nested arity-2 FAPP (`fAppPair`, Term/Term.hs:163), so
/// `<a, z>` and `<a, b, c>` first differ at argument 2 — `z` against
/// `pair(b, c)` — where `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74) puts
/// `<a, z>` first.
#[test]
fn ord_orders_pairs_by_their_nested_spine() {
    use std::cmp::Ordering::{Greater, Less};
    let pair = |a: BLNTerm, b: BLNTerm| {
        f_app_no_eq(tamarin_term::function_symbols::pair_sym(), vec![a, b])
    };
    let msg = |n: &str| bfree(n, 0, LSort::Msg);
    let short = pair(msg("a"), msg("z"));
    let long = pair(msg("a"), pair(msg("b"), msg("c")));
    assert_eq!(short.cmp(&long), Less);
    assert_eq!(long.cmp(&short), Greater);
}

/// Both variable orderings compare the sort with `LSort`'s derived `Ord`,
/// which ranks the five sorts in their declaration order
/// (Term/LTerm.hs:165-170): `Pub`, `Fresh`, `Msg`, `Node`, `Nat`.  The printed
/// operand order of an AC application rides on this through `Ord LVar`, so a
/// reordering of the `LSort` variants moves printed output.
#[test]
fn variable_ordering_ranks_sorts_in_lsort_declaration_order() {
    let declared = [
        LSort::Pub,
        LSort::Fresh,
        LSort::Msg,
        LSort::Node,
        LSort::Nat,
    ];

    let v = |sort| LVar::new("x", sort, 0);
    let b = |sort| ("x".to_string(), sort);
    for (i, &s) in declared.iter().enumerate() {
        for (j, &t) in declared.iter().enumerate() {
            let want = i.cmp(&j);
            assert_eq!(v(s).cmp(&v(t)), want, "{s:?} vs {t:?}");
            assert_eq!(b(s).cmp(&b(t)), want, "{s:?} vs {t:?}");
        }
    }
}

/// HS `data Quantifier = All | Ex` (Theory/Model/Formula.hs:111-112) derives
/// Ord, so `All` sorts before `Ex` — the first field the guarded formula's
/// `GGuarded` comparison reads.
#[test]
fn quantifier_orders_all_before_ex() {
    assert!(Quantifier::All < Quantifier::Ex);
}

#[test]
fn gnot_true_is_false() {
    assert_eq!(gnot(&gtrue()), gfalse());
}

#[test]
fn gnot_false_is_true() {
    assert_eq!(gnot(&gfalse()), gtrue());
}

/// De Morgan: `gnot (gconj [a, b]) = gdisj [gnot a, gnot b]`.  This is the
/// dual of [`gnot_distributes_over_disj`].  The test asserts on atoms, and
/// not on the propositional constants.  `¬(T ∧ T)` collapses to `⊥` under
/// `gdisj` and under `gconj` alike, so the constants cannot tell the two
/// smart constructors apart.
#[test]
fn gnot_conj_becomes_disj() {
    let a = g("last(#i)").unwrap();
    let b = g("last(#j)").unwrap();
    let neg = gnot(&Guarded::Conj(vec![a.clone(), b.clone()].into()));
    match &neg {
        Guarded::Disj(items) => {
            assert_eq!(items.len(), 2, "¬(a ∧ b) must keep both disjuncts");
            assert_eq!(items[0], gnot(&a));
            assert_eq!(items[1], gnot(&b));
        }
        other => panic!("expected Disj([¬a, ¬b]), got {:?}", other),
    }
}

#[test]
fn ginduct_rejects_action_free_formula() {
    // gtrue contains no action atom — ginduct should reject.
    assert!(ginduct(&gtrue()).is_err());
    assert!(ginduct(&gfalse()).is_err());
}

/// HS `satisfiedByEmptyTrace` decides a `GGuarded` on its quantifier
/// (Guarded.hs:588-594).  The empty trace satisfies a guarded `∀` vacuously.
/// The empty trace does not satisfy a guarded `∃`.  A bare atom outside every
/// quantifier is an error, because such a formula is not doubly guarded.  The
/// test checks all three arms.  The `∀` case alone cannot tell the real
/// function apart from a constant `Ok(true)`.
#[test]
fn satisfied_by_empty_trace_handles_quants() {
    let all = g("All x #i. P(x)@#i ==> Q(x)@#i").expect("guarded");
    assert!(satisfied_by_empty_trace(&all).unwrap(), "∀ holds vacuously");
    let ex = g("Ex x #i. P(x)@#i").expect("guarded");
    assert!(!satisfied_by_empty_trace(&ex).unwrap(), "∃ needs an action");
    let atom = g("last(#i)").expect("guarded");
    assert!(
        satisfied_by_empty_trace(&atom).is_err(),
        "a quantifier-free atom is not doubly guarded"
    );
}

#[test]
fn ginduct_existential_action_succeeds() {
    // Ex k #i. P(k) @ #i — closed, contains an action atom, not last-bearing.
    let gf = g("Ex k #i. P(k)@#i").expect("guarded");
    let (base, step) = ginduct(&gf).expect("ginduct");
    // Empty-trace satisfaction: ∃ over empty trace is vacuously false.
    assert_eq!(base, gfalse());
    // Step case is `gconj [g, IH]` — typically wraps both.
    match &step {
        Guarded::Conj(items) => {
            assert!(
                items.iter().any(|x| x == &gf),
                "step case should contain the original formula"
            );
        }
        other => panic!("expected Conj, got {:?}", other),
    }
}

#[test]
fn ground_false() {
    let r = g("F").unwrap();
    assert_eq!(r, gfalse());
}

#[test]
fn simple_action_under_all() {
    // All k #i. Setup(k) @ i ==> F
    // The All has guard `Setup(k) @ i`, which binds both k and #i.
    let r = g("All k #i. Setup(k) @ #i ==> F").unwrap();
    match r {
        Guarded::GGuarded {
            qua, vars, guards, ..
        } => {
            assert_eq!(qua, Quantifier::All);
            assert_eq!(vars.len(), 2);
            assert_eq!(guards.len(), 1);
        }
        x => panic!("expected GGuarded, got {:?}", x),
    }
}

#[test]
fn unguarded_variable_rejected() {
    // All k. F  — `k` has no action atom guarding it.
    let res = g("All k. F");
    assert!(res.is_err(), "expected unguarded error");
}

#[test]
fn exists_with_guarded_var() {
    // Ex k #i. Setup(k) @ i — k and #i are guarded by Setup(k) @ i.
    let r = g("Ex k #i. Setup(k) @ #i").unwrap();
    match r {
        Guarded::GGuarded { qua, vars, .. } => {
            assert_eq!(qua, Quantifier::Ex);
            assert_eq!(vars.len(), 2);
        }
        x => panic!("expected GGuarded(Ex), got {:?}", x),
    }
}

#[test]
fn safety_no_existential() {
    let r = g("All k #i. Setup(k) @ #i ==> F").unwrap();
    assert!(is_safety_formula(&r));
}

#[test]
fn safety_rejects_existential() {
    let r = g("All k #i. Setup(k) @ #i ==> Ex j #t. Foo(j) @ #t").unwrap();
    assert!(!is_safety_formula(&r));
}

// `remainingUnguarded` identity: HS compares LVars by (name, sort, idx),
// so an indexed binder is a different variable from a same-named outer
// one.  The three cases below are the discriminating triple checked
// against the pinned oracle (Git revision ef3f0468): the restriction
// `All x #NOW. Foo(x) @ #NOW ==> (All <inner> z. (<inner, z> = x) ==> F)`
// is accepted for every choice of `<inner>` that is not literally `x`,
// and the oracle prints `// safety formula` under it plus
// "All wellformedness checks were successful."

#[test]
fn indexed_inner_binder_is_guarded_against_same_named_outer_var() {
    // Binders [x.1, z], guard `<x.1, z> = x`: the equation's right-hand
    // side is the OUTER `x`, which is covered (it is not in the unguarded
    // set), so the left-hand side's variables x.1 and z are guarded.
    let r = g("All x #NOW. Foo(x) @ #NOW ==> (All x.1 z. (<x.1, z> = x) ==> F)")
        .expect("x.1 and z are guarded by the pair equation");
    assert!(is_safety_formula(&r));
    match &r {
        Guarded::GGuarded {
            qua, vars, guards, ..
        } => {
            assert_eq!(*qua, Quantifier::All);
            assert_eq!(vars.len(), 2, "outer binders x and #NOW");
            assert_eq!(guards.len(), 1, "outer guard Foo(x) @ #NOW");
        }
        x => panic!("expected GGuarded, got {:?}", x),
    }
}

#[test]
fn distinctly_named_inner_binders_are_guarded() {
    // Control: no name collision at all.
    let r = g("All x #NOW. Foo(x) @ #NOW ==> (All y z. (<y, z> = x) ==> F)")
        .expect("y and z are guarded by the pair equation");
    assert!(is_safety_formula(&r));
    // Control: collision only on the index-carrying spelling.
    let r = g("All x #NOW. Foo(x) @ #NOW ==> (All y.1 z. (<y.1, z> = x) ==> F)")
        .expect("y.1 and z are guarded by the pair equation");
    assert!(is_safety_formula(&r));
}

#[test]
fn unindexed_shadowing_inner_binder_stays_unguarded() {
    // Binders [x, z], guard `<x, z> = x`: the right-hand side is the
    // inner (shadowing) `x`, so neither side is covered and nothing is
    // removed from the unguarded set.
    let res = g("All x #NOW. Foo(x) @ #NOW ==> (All x z. (<x, z> = x) ==> F)");
    assert!(res.is_err(), "expected unguarded error, got {:?}", res);
}

#[test]
fn timepoint_guard_matches_sigilless_occurrence() {
    // HS parses the `@`-argument with `nodevar` (Token.hs:444-448), which
    // assigns `LSortNode` whether or not the `#` sigil is written, so the
    // binder `#j` is guarded by `Bar(x) @ j`.
    let r = g("Ex #j. Bar(x) @ j").expect("#j is guarded by the action's timepoint");
    match &r {
        Guarded::GGuarded { qua, vars, .. } => {
            assert_eq!(*qua, Quantifier::Ex);
            assert_eq!(vars.len(), 1);
        }
        x => panic!("expected GGuarded(Ex), got {:?}", x),
    }
}

/// A top-level implication does not become a disjunction.  The action atom
/// of the antecedent becomes the guard of the universal, and the consequent
/// becomes its body.  `All k #i. Setup(k)@#i ==> (Ex j #t. Setup(j)@#t)`
/// therefore nests one guarded quantifier inside the other.
#[test]
fn implication_distributes() {
    let r = g("All k #i. Setup(k) @ #i ==> (Ex j #t. Setup(j) @ #t)").unwrap();
    match &r {
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => {
            assert_eq!(*qua, Quantifier::All);
            assert_eq!(vars.len(), 2, "binders k and #i");
            assert_eq!(guards.len(), 1, "the antecedent is the guard");
            match &**body {
                Guarded::GGuarded { qua, vars, .. } => {
                    assert_eq!(*qua, Quantifier::Ex);
                    assert_eq!(vars.len(), 2, "binders j and #t");
                }
                other => panic!("expected the consequent as the body, got {:?}", other),
            }
        }
        x => panic!("got {:?}", x),
    }
}

// =========================================================================
// Substitution correctness tests
// =========================================================================

fn var(name: &str, idx: u64) -> LNTerm {
    var_term(LVar::new(name, LSort::Msg, idx))
}
fn pubconst(s: &str) -> LNTerm {
    pub_term(s)
}
fn lpair(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_no_eq(tamarin_term::function_symbols::pair_sym(), vec![a, b])
}

/// The `LVar` key of a substitution entry, at the sort [`var`] builds.
fn key(name: &str, idx: u64) -> LVar {
    LVar::new(name, LSort::Msg, idx)
}

#[test]
fn subst_var_to_non_var_term() {
    // Bind `k` to the public constant 'foo'.
    let s = LNSubst::from_list(vec![(key("k", 0), pubconst("foo"))]);
    let result = apply_vterm(&s, var("k", 0));
    assert_eq!(result, pubconst("foo"));
}

#[test]
fn subst_descends_into_app_args() {
    // `f(k, m)` where `k` is bound to 'foo'.
    let s = LNSubst::from_list(vec![(key("k", 0), pubconst("foo"))]);
    let f = user_sym("f", 2);
    let t = f_app_no_eq(f, vec![var("k", 0), var("m", 0)]);
    let result = apply_vterm(&s, t);
    let expected = f_app_no_eq(f, vec![pubconst("foo"), var("m", 0)]);
    assert_eq!(result, expected);
}

/// The substitution is keyed by the whole `LVar`, so a variable that differs
/// from the domain entry in its index or in its sort is another variable and
/// passes through unchanged (`Ord LVar`, LTerm.hs:546-548).
#[test]
fn subst_keys_on_the_whole_variable() {
    let s = LNSubst::from_list(vec![(key("x", 5), var("y", 0))]);
    assert_eq!(apply_vterm(&s, var("x", 5)), var("y", 0));
    assert_eq!(apply_vterm(&s, var("x", 6)), var("x", 6));
    let fresh_x = var_term(LVar::new("x", LSort::Fresh, 5));
    assert_eq!(apply_vterm(&s, fresh_x.clone()), fresh_x);
}

#[test]
fn subst_pair_descent() {
    let s = LNSubst::from_list(vec![(key("a", 0), pubconst("X"))]);
    let t = lpair(var("a", 0), var("b", 0));
    let result = apply_vterm(&s, t);
    let expected = lpair(pubconst("X"), var("b", 0));
    assert_eq!(result, expected);
}

/// The parser sorts the `#i` binder and the `@ i` occurrence alike, as
/// `Node`, so `close_subst` binds the body occurrence and `gnot`/`ginduct`
/// see a closed formula.
#[test]
fn injectivity_check_ginduct_succeeds() {
    let gf = g("not (Ex id #i #j #k. Initiated(id) @ i & Removed(id) @ j & Copied(id) @ k & #i < #j & #j < #k)").expect("guarded");
    let g_neg = gnot(&gf);
    assert!(frees(&g_neg).is_empty(), "gnot should be closed");
    assert!(ginduct(&g_neg).is_ok(), "ginduct should succeed");
}

#[test]
fn applying_a_substitution_to_a_guarded_formula_leaves_bound_leaves_alone() {
    // `Ex k. Action(k) @ i` — substituting `k` from outside should
    // NOT rewrite the inner `k` because it's positionally bound
    // (DeBruijn `Bound(0)` in the body, not Free LVar `k:0`).
    let s = LNSubst::from_list(vec![(key("k", 0), pubconst("OUTER"))]);
    let inner_k = LVar::new("k", LSort::Msg, 0);
    // Build via close_guarded so that `k` becomes Bound(0) in the body.
    let g = close_guarded(
        Quantifier::Ex,
        vec![inner_k],
        Vec::new(),
        Guarded::Atom(ProtoAtom::Action(
            var_term(BVar::Free(LVar::new("i", LSort::Node, 0))),
            bfact(false, "Action", vec![bfree("k", 0, LSort::Msg)]),
        )),
    );
    let result = subst_guarded(&g, &s);
    // Body should be unchanged: subst on Free `(k, 0)` doesn't
    // touch the Bound `k` reference.
    match result {
        Guarded::GGuarded { body, .. } => match &*body {
            Guarded::Atom(ProtoAtom::Action(_, fa)) => {
                // Walk the body atom and verify the `k` slot is still Bound(0).
                match &fa.terms[0] {
                    Term::Lit(Lit::Var(BVar::Bound(0))) => {}
                    other => panic!("expected Bound(0), got {:?}", other),
                }
            }
            other => panic!("expected Atom(Action), got {:?}", other),
        },
        other => panic!("expected GGuarded, got {:?}", other),
    }
}

/// The test runs `ginduct` on an `All`-quantified formula.  The base case is
/// the empty-trace verdict, which is vacuously true here.  The step case is
/// `gconj [gf, toInductionHypothesis gf]`.  The original formula comes first,
/// and the IH comes after it.  The outer quantifier of the IH is the `Ex`
/// dual.
#[test]
fn ginduct_extracts_two_cases() {
    let gf = g("All k #i. Setup(k) @ #i ==> Ex #j. Setup(k) @ #j & #j < #i").unwrap();
    let (base, step) = ginduct(&gf).expect("ginduct should succeed");
    assert_eq!(base, gtrue(), "the empty trace satisfies the outer ∀");
    match &step {
        Guarded::Conj(items) => {
            assert_eq!(items.len(), 2, "step case is `gconj [gf, IH]`");
            assert_eq!(items[0], gf, "the original formula comes first");
            assert!(
                matches!(
                    &items[1],
                    Guarded::GGuarded {
                        qua: Quantifier::Ex,
                        ..
                    }
                ),
                "the IH flips the outer quantifier: {:?}",
                items[1]
            );
        }
        other => panic!("expected Conj of 2 items, got {:?}", other),
    }
}

/// Returns every `Last(Bound n)` index that the guarded formula reaches, in
/// traversal order.  The traversal takes the guards of a quantifier before
/// its body.  This is the order in which `to_induction_hypothesis` emits its
/// `lastAtos`.
fn last_bound_indices(g: &Guarded) -> Vec<u64> {
    fn go(g: &Guarded, out: &mut Vec<u64>) {
        match g {
            Guarded::Atom(ProtoAtom::Last(Term::Lit(Lit::Var(BVar::Bound(n))))) => out.push(*n),
            Guarded::Atom(_) => {}
            Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().for_each(|x| go(x, out)),
            Guarded::GGuarded { guards, body, .. } => {
                for a in guards.iter() {
                    if let ProtoAtom::Last(Term::Lit(Lit::Var(BVar::Bound(n)))) = a {
                        out.push(*n);
                    }
                }
                go(body, out);
            }
        }
    }
    let mut out = Vec::new();
    go(g, &mut out);
    out
}

/// Pin Haskell parity for `lastAtos`: the IH for an `All`-guarded
/// formula introduces a `¬Last(v)` for every node-sorted bound
/// variable.  Mirrors the Haskell:
///
///   toInductionHypothesis (GGuarded All ss as gf) =
///       gex ss as (gconj (map gnotAtom lastAtos ++ [IH gf]))
///     where lastAtos = [Last (Bound j) | (j,(_,LSortNode)) ← ...]
#[test]
fn induction_hypothesis_emits_last_atoms_for_node_sorted_binders() {
    // `All #i. Setup('k') @ #i ⇒ …` is doubly guarded with one
    // node-sorted binder.  The IH must contain `Last(#i)` (in
    // *negated* form, since the outer quantifier flips All→Ex and
    // we conjoin `¬Last(v)` per node binder).
    let g = g("All #i. Setup('k') @ #i ==> G('x') @ #i").unwrap();
    let ih = to_induction_hypothesis(&g).expect("should produce IH");

    // The outer quantifier must flip All → Ex and must keep its binder.  The
    // body must mention the `Last` of the innermost binder.  In DeBruijn form
    // that is `Last(Bound 0)`.
    match &ih {
        Guarded::GGuarded {
            qua, vars, body, ..
        } => {
            assert_eq!(*qua, Quantifier::Ex);
            assert_eq!(vars.len(), 1);
            assert_eq!(
                last_bound_indices(body),
                vec![0],
                "IH body should mention Last(Bound 0) for the node binder; got {:?}",
                body
            );
        }
        other => panic!("expected GGuarded(Ex, ...), got {:?}", other),
    }
}

/// `lastAtos = [Last (Bound j) | (j, (_, LSortNode)) <- zip [0..] (reverse ss)]`
/// (Guarded.hs:613-616) has two parts that discriminate, and the exact index
/// list checks both.  The first part is the `LSortNode` filter: a `Msg`-sorted
/// binder contributes nothing.  The second part is the `reverse`: the indices
/// count from the innermost binder outwards.  Without the `reverse`, the pair
/// would shift to `[1, 2]` and would invert the case labels of the
/// `last`-disjunction.
#[test]
fn induction_hypothesis_skips_non_node_binders() {
    // The binders are `[k:msg, #i, #j]`.  Reversed, they are `[#j, #i, k]`.
    // The two node binders therefore take the indices 0 and 1, and the
    // message binder takes none.
    let g = g("All k #i #j. (Setup(k) @ #i & Setup(k) @ #j) ==> F").unwrap();
    let ih = to_induction_hypothesis(&g).expect("should produce IH");
    assert_eq!(
        last_bound_indices(&ih),
        vec![0, 1],
        "one Last per node binder, innermost first; got {:?}",
        ih
    );
}

// =========================================================================
// simplify_guarded_with — partial-atom-valuation rewriting
//
// Mirrors Haskell's `simplifyGuardedOrReturn` from
// `Theory.Constraint.System.Guarded`:
//   simp (GAto a)       = maybe fm gtf (valuation a)
//   simp (GDisj fms)    = gdisj (map simp fms)
//   simp (GConj fms)    = gconj (map simp fms)
//   simp (GGuarded All [] atos gf)
//     | any (Just False ==) (map valuation atos) = gtrue
//     | otherwise = gall [] (filter unknown atos) (simp gf)
//   simp (GGuarded ...) = fm  -- delay past binders
// =========================================================================

/// The `a = b` equality over two free `Msg` leaves, as the guarded store
/// holds it.
fn mk_gatom_eq(a: &str, b: &str) -> Atom<BLNTerm> {
    ProtoAtom::EqE(bfree(a, 0, LSort::Msg), bfree(b, 0, LSort::Msg))
}

/// The same equality over plain `LVar`s, as `simplify_guarded_with` hands it
/// to its valuation (HS `unbindAtom`, Guarded.hs:351-352).
fn mk_eq(a: &str, b: &str) -> Atom<LNTerm> {
    bvar_to_lvar(&mk_gatom_eq(a, b))
}

fn mk_atom_eq(a: &str, b: &str) -> Guarded {
    Guarded::Atom(mk_gatom_eq(a, b))
}

#[test]
fn simplify_atom_with_known_true_collapses_to_gtrue() {
    let g = mk_atom_eq("x", "y");
    let val = |_a: &Atom<LNTerm>| Some(true);
    assert_eq!(simplify_guarded_with(&g, &val), gtrue());
}

#[test]
fn simplify_atom_with_known_false_collapses_to_gfalse() {
    let g = mk_atom_eq("x", "y");
    let val = |_a: &Atom<LNTerm>| Some(false);
    assert_eq!(simplify_guarded_with(&g, &val), gfalse());
}

#[test]
fn simplify_atom_unknown_left_intact() {
    let g = mk_atom_eq("x", "y");
    let val = |_a: &Atom<LNTerm>| None;
    assert_eq!(simplify_guarded_with(&g, &val), g);
}

#[test]
fn simplify_disj_drops_false_branches() {
    // a ∨ b — if b evaluates False and a is unknown, result = a.
    let a = mk_atom_eq("p", "q");
    let b = mk_eq("r", "s");
    let g = Guarded::Disj(vec![a.clone(), Guarded::Atom(mk_gatom_eq("r", "s"))].into());
    let val = move |atom: &Atom<LNTerm>| if atom == &b { Some(false) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), a);
}

#[test]
fn simplify_conj_short_circuits_on_false() {
    // a ∧ b — if b evaluates False, conj should be gfalse.
    let b = mk_eq("r", "s");
    let g = Guarded::Conj(vec![mk_atom_eq("p", "q"), Guarded::Atom(mk_gatom_eq("r", "s"))].into());
    let val = move |atom: &Atom<LNTerm>| if atom == &b { Some(false) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), gfalse());
}

/// Returns a binder-free universal with the given guards over the body
/// `p = q`.
fn mk_universal(vars: Vec<(String, LSort)>, guards: &[(&str, &str)]) -> Guarded {
    Guarded::GGuarded {
        qua: Quantifier::All,
        vars: vars.into(),
        guards: guards.iter().map(|(a, b)| mk_gatom_eq(a, b)).collect(),
        body: std::sync::Arc::new(mk_atom_eq("p", "q")),
    }
}

#[test]
fn simplify_universal_with_one_false_guard_is_gtrue() {
    // (All vars[]. [a, b]. body) with a=False → gtrue (vacuous).
    let a = mk_eq("a", "b");
    let g = mk_universal(Vec::new(), &[("a", "b"), ("c", "d")]);
    let val = move |atom: &Atom<LNTerm>| if atom == &a { Some(false) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), gtrue());
}

#[test]
fn simplify_universal_drops_true_guards_keeps_unknown() {
    let a = mk_eq("a", "b");
    let g = mk_universal(Vec::new(), &[("a", "b"), ("c", "d")]);
    // The valuation decides `a` as True, so the code drops it.  Every other
    // atom is unknown: `c = d` and the atom in the body.  Each unknown atom
    // survives unchanged.
    let val = move |atom: &Atom<LNTerm>| if atom == &a { Some(true) } else { None };
    match simplify_guarded_with(&g, &val) {
        Guarded::GGuarded { vars, guards, .. } => {
            assert!(vars.is_empty());
            assert_eq!(guards, vec![mk_gatom_eq("c", "d")].into());
        }
        other => panic!("expected GGuarded with one guard, got {:?}", other),
    }
}

/// With every guard True, the universal collapses to `gall [] [] body`.
/// That is the simplified body (HS `gall _ [] gf = gf`, Guarded.hs:449-453).
/// The atom in the body stays unknown here.  If the valuation also decided
/// that atom as True, the `gf == gtrue` arm of `gall` would return `gtrue`.
/// It would return `gtrue` whether or not the code dropped the True guards,
/// and the test could not tell the two cases apart.
#[test]
fn simplify_universal_with_all_true_guards_returns_body() {
    let a = mk_eq("a", "b");
    let g = mk_universal(Vec::new(), &[("a", "b")]);
    let val = move |atom: &Atom<LNTerm>| if atom == &a { Some(true) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), mk_atom_eq("p", "q"));
}

#[test]
fn simplify_universal_with_quantifier_left_intact() {
    // GGuarded with bound vars is left alone — Haskell delays
    // simplification past the binder.
    let bound_var = ("x".to_string(), LSort::Msg);
    let g = mk_universal(vec![bound_var], &[("a", "b")]);
    let val = |_atom: &Atom<LNTerm>| Some(true);
    assert_eq!(simplify_guarded_with(&g, &val), g);
}

// =========================================================================
// Haskell-faithfulness invariants for guarded-formula smart ctors.
//
// `gconj` / `gdisj` mirror Haskell's smart constructors in
// `Theory.Constraint.System.Guarded` (gconj: Guarded.hs:415-423; gdisj:
// Guarded.hs:426-437).  They
// SHORT-CIRCUIT on `gtrue`/`gfalse` and dedupe via `nub`.
// =========================================================================

/// `gtrue` is represented as `Conj []` and `gfalse` as `Disj []`.
/// This is a Haskell convention (`gtf False = GDisj (Disj [])`,
/// `gtf True = GConj (Conj [])`, Guarded.hs:397-400).  Many
/// short-circuit checks rely on it (e.g. `x == gfalse()` in
/// `gconj`).  If we accidentally encode them differently, every
/// short-circuit silently breaks.
#[test]
fn gtrue_is_empty_conj_and_gfalse_is_empty_disj() {
    assert_eq!(gtrue(), Guarded::Conj(vec![].into()));
    assert_eq!(gfalse(), Guarded::Disj(vec![].into()));
    assert_ne!(
        gtrue(),
        gfalse(),
        "gtrue and gfalse must be distinguishable"
    );
}

/// `gconj([gtrue, gtrue, ...])` reduces to `gtrue`.  Empty/trivial
/// conjunction is True.  Mirrors Haskell `gconj`'s elimination of
/// `gtrue` items.
#[test]
fn gconj_of_only_gtrue_items_is_gtrue() {
    // Guarded.hs:422: `gconj`'s `flatten` should collapse all-true conjunctions.
    // Rust impl flattens `Conj` items (gtrue is Conj([])), so all
    // gtrue items dissolve into empty.  Result: `Conj([])` = gtrue.
    let g = gconj(vec![gtrue(), gtrue(), gtrue()]);
    assert_eq!(
        g,
        gtrue(),
        "gconj of only-True items must collapse to gtrue"
    );
}

/// `gconj([..., gfalse, ...])` SHORT-CIRCUITS to `gfalse` regardless
/// of other items.  This is the "any-false makes conjunction false"
/// short-circuit at Guarded.hs:415-423, see line 418.
#[test]
fn gconj_short_circuits_on_gfalse() {
    // Build a non-trivial atom by parsing a small formula.
    let atom_g = g("last(#i)").unwrap();
    // Any gfalse in the items short-circuits to gfalse.
    let g = gconj(vec![gtrue(), gfalse(), atom_g.clone()]);
    assert_eq!(
        g,
        gfalse(),
        "gconj must short-circuit when any item is gfalse"
    );
    let g2 = gconj(vec![atom_g, gfalse()]);
    assert_eq!(g2, gfalse());
}

/// `gdisj([gfalse, gfalse, ...])` reduces to `gfalse`. Empty
/// disjunction is False.
#[test]
fn gdisj_of_only_gfalse_items_is_gfalse() {
    let g = gdisj(vec![gfalse(), gfalse()]);
    assert_eq!(
        g,
        gfalse(),
        "gdisj of only-False items must collapse to gfalse"
    );
}

/// `gdisj([..., gtrue, ...])` short-circuits to `gtrue`.
#[test]
fn gdisj_short_circuits_on_gtrue() {
    let g = gdisj(vec![gfalse(), gtrue(), gfalse()]);
    assert_eq!(
        g,
        gtrue(),
        "gdisj must short-circuit on first gtrue encountered"
    );
}

/// `gconj` deduplicates syntactically-equal items.  Mirrors
/// Haskell's `nub gfs` (Guarded.hs:415-423, see line 420).  Dedup is ORDER-PRESERVING
/// (Haskell `Data.List.nub` keeps first occurrence).
#[test]
fn gconj_dedupes_syntactic_duplicates() {
    let a = g("last(#i)").unwrap();
    let b = g("last(#j)").unwrap();
    let out = gconj(vec![a.clone(), b.clone(), a.clone()]);
    // Expected: Conj([a, b]) — second occurrence of `a` dropped.
    match out {
        Guarded::Conj(items) => {
            assert_eq!(items.len(), 2, "gconj must dedupe identical items via nub");
            assert_eq!(items[0], a);
            assert_eq!(items[1], b);
        }
        _ => panic!("expected Conj"),
    }
}

/// Dedup happens BEFORE the singleton unwrap: `gconj([a, a])` must be
/// `a` itself, not the non-normal singleton `Conj([a])` that only a
/// second application would unwrap.  `normalise_guarded_cow` relies
/// on this one-pass idempotence (mirrors HS `gconj`).
#[test]
fn gconj_duplicates_collapse_to_bare_item() {
    let a = g("last(#i)").unwrap();
    let out = gconj(vec![a.clone(), a.clone()]);
    assert_eq!(out, a, "gconj must dedupe before the singleton unwrap");
}

/// `gdisj` deduplicates syntactically-equal items.  Same as above,
/// for disjunction.  Without this dedup, `verify_checksign_test`-class
/// SplitG variants double up.
#[test]
fn gdisj_dedupes_syntactic_duplicates() {
    let a = g("last(#i)").unwrap();
    let b = g("last(#j)").unwrap();
    let out = gdisj(vec![a.clone(), b.clone(), a.clone(), b.clone()]);
    match out {
        Guarded::Disj(items) => {
            assert_eq!(items.len(), 2, "gdisj must dedupe identical items via nub");
            assert_eq!(items[0], a);
            assert_eq!(items[1], b);
        }
        _ => panic!("expected Disj"),
    }
}

/// `gconj` with a single non-trivial item collapses to that item
/// (no Conj wrapper).  Mirrors Haskell's `case gfs' of [g] -> g`
/// pattern.
#[test]
fn gconj_singleton_unwraps() {
    let a = g("last(#i)").unwrap();
    let out = gconj(vec![a.clone()]);
    assert_eq!(out, a, "singleton gconj must unwrap to the lone item");
}

/// `gconj` flattens nested `Conj` one level.  Mirrors Haskell's
/// `concatMap` flatten.
#[test]
fn gconj_flattens_nested_conj_one_level() {
    let a = g("last(#i)").unwrap();
    let b = g("last(#j)").unwrap();
    let c = g("last(#k)").unwrap();
    let inner = Guarded::Conj(vec![a.clone(), b.clone()].into());
    let out = gconj(vec![inner, c.clone()]);
    match out {
        Guarded::Conj(items) => {
            assert_eq!(
                items.len(),
                3,
                "nested Conj should be flattened: 2 inner + 1 outer = 3"
            );
            assert_eq!(items, vec![a, b, c].into());
        }
        _ => panic!("expected Conj"),
    }
}

/// `gdisj` recursively flattens ARBITRARILY deeply nested `Disj`s.
/// Mirrors HS `gdisj`'s `flatten (GDisj disj) = concatMap flatten $
/// getDisj disj` (Guarded.hs:426-437, see line 436), which unwraps every level, not
/// just one — a 5-way `∨` parsed as a binary-Or chain must flatten to a
/// single 5-alt Disj goal.
#[test]
fn gdisj_deeply_nested_disj_flattens_to_5_alts() {
    let a = g("last(#a)").unwrap();
    let b = g("last(#b)").unwrap();
    let c = g("last(#c)").unwrap();
    let d = g("last(#d)").unwrap();
    let e = g("last(#e)").unwrap();
    // Build the left-leaning binary-Or chain
    // `Disj(Disj(Disj(Disj(a, b), c), d), e)`.
    let lvl1 = Guarded::Disj(vec![a.clone(), b.clone()].into());
    let lvl2 = Guarded::Disj(vec![lvl1, c.clone()].into());
    let lvl3 = Guarded::Disj(vec![lvl2, d.clone()].into());
    let lvl4 = Guarded::Disj(vec![lvl3, e.clone()].into());
    let out = gdisj(vec![lvl4]);
    match out {
        Guarded::Disj(items) => {
            assert_eq!(
                items.len(),
                5,
                "4-level-nested binary-Or chain must flatten to 5 \
                     alts (HS `flatten` recurses) — got {} alts",
                items.len()
            );
            assert_eq!(
                items,
                vec![a, b, c, d, e].into(),
                "flatten preserves leaf order (HS uses concatMap)"
            );
        }
        other => panic!("expected Disj of 5 items, got {:?}", other),
    }
}

/// Symmetric: `gconj` recursively flattens deeply nested `Conj`s.
/// Mirrors HS Guarded.hs:415-423, see line 422 `flatten (GConj conj) = concatMap
/// flatten $ getConj conj`.
#[test]
fn gconj_deeply_nested_conj_flattens() {
    let a = g("last(#a)").unwrap();
    let b = g("last(#b)").unwrap();
    let c = g("last(#c)").unwrap();
    let d = g("last(#d)").unwrap();
    let e = g("last(#e)").unwrap();
    let lvl1 = Guarded::Conj(vec![a.clone(), b.clone()].into());
    let lvl2 = Guarded::Conj(vec![lvl1, c.clone()].into());
    let lvl3 = Guarded::Conj(vec![lvl2, d.clone()].into());
    let lvl4 = Guarded::Conj(vec![lvl3, e.clone()].into());
    let out = gconj(vec![lvl4]);
    match out {
        Guarded::Conj(items) => {
            assert_eq!(
                items.len(),
                5,
                "4-level-nested binary-And chain must flatten to 5 \
                     conj items — got {}",
                items.len()
            );
            assert_eq!(items, vec![a, b, c, d, e].into());
        }
        other => panic!("expected Conj of 5 items, got {:?}", other),
    }
}

// =========================================================================
// Haskell-faithfulness invariants for `gnot` and quantifier swap.
//
// Mirrors Haskell `gnot` (Guarded.hs):
//     gnot (GGuarded All ss as gf) = gex  ss as (gnot gf)
//     gnot (GGuarded Ex  ss as gf) = gall ss as (gnot gf)
//
// The All↔Ex swap under negation is critical: proto-fact actions need
// a specific Haskell-faithful negation shape, and getting this wrong
// has downstream nondeterminism impact on trace search.
// =========================================================================

/// `gnot ∘ gnot = id` (involution) for ground formulas.
/// This is the most fundamental algebraic property of negation.
/// If gnot doesn't round-trip, every double-negation in IH
/// reasoning silently degrades.
#[test]
fn gnot_double_negation_is_identity() {
    assert_eq!(gnot(&gnot(&gtrue())), gtrue());
    assert_eq!(gnot(&gnot(&gfalse())), gfalse());
    // Atom case.
    let a = g("last(#i)").unwrap();
    assert_eq!(
        gnot(&gnot(&a)),
        a,
        "gnot is involutive on atomic formulas — \
                    needed for `to_induction_hypothesis` round-trip."
    );
}

/// `gnot (All ... body) = Ex ... gnot(body)`.  Haskell:
/// `gnot (GGuarded All ss as gf) = gex ss as (gnot gf)`.
///
/// **The quantifier flips on negation.**  If we forget to flip,
/// `to_induction_hypothesis` produces the wrong dual and the IH
/// becomes vacuous or false.
#[test]
fn gnot_flips_universal_to_existential() {
    // ∀ x #i. P(x)@#i ⇒ Q(x)@#i — guarded universal.
    // Negation flips to: ∃ x #i. P(x)@#i ∧ ¬Q(x)@#i.
    let f = g("All x #i. P(x)@#i ==> Q(x)@#i").unwrap();
    let n = gnot(&f);
    // The resulting quantifier MUST be Ex.
    match n {
        Guarded::GGuarded {
            qua: Quantifier::Ex,
            ..
        } => {}
        other => panic!("expected Ex quantifier after negating All; got {:?}", other),
    }
}

/// `gnot (Ex ... body) = All ... gnot(body)`.  Symmetric to above.
///
/// Together these ensure that `gnot ∘ gnot` round-trips through
/// the quantifier — Ex → All → Ex.  Without the flip on either
/// side, the double-negation property breaks.
#[test]
fn gnot_flips_existential_to_universal() {
    let f = g("Ex x #i. P(x)@#i").unwrap();
    // Sanity: starts as Ex.
    match &f {
        Guarded::GGuarded {
            qua: Quantifier::Ex,
            ..
        } => {}
        other => panic!("test setup: expected Ex; got {:?}", other),
    }
    let n = gnot(&f);
    // After negation, outer quantifier must be All (or the formula
    // simplified — but for this non-trivial body it remains All).
    match n {
        Guarded::GGuarded {
            qua: Quantifier::All,
            ..
        } => {}
        other => panic!("expected All quantifier after negating Ex; got {:?}", other),
    }
}

/// De Morgan: `gnot (gconj [a, b]) = gdisj [gnot a, gnot b]`.
/// Already exercised in `gnot_conj_becomes_disj` — pin the dual.
#[test]
fn gnot_distributes_over_disj() {
    // ¬(a ∨ b) = ¬a ∧ ¬b
    let a = g("last(#i)").unwrap();
    let b = g("last(#j)").unwrap();
    let or = Guarded::Disj(vec![a.clone(), b.clone()].into());
    let neg = gnot(&or);
    // Should be Conj([¬a, ¬b]) — both negated.
    let expected = gconj(vec![gnot(&a), gnot(&b)]);
    assert_eq!(
        neg, expected,
        "De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b — required for IH derivation"
    );
}

/// `em` is the sole commutative (C) function symbol, and `fAppC` stores it in
/// sorted-arg form (`fAppC nacsym as = FAPP (C nacsym) (sort as)`,
/// Term/Term/Raw.hs:133-134).  Every guarded term is built through it, so the
/// two spellings of one pairing are ONE value and a substituted
/// solved-formula compares equal to a freshly-derived implied-formula over
/// the same pairing (the idbased/BP_IBS bilinear divergence).
#[test]
fn guarded_ac_arguments_are_sorted_by_construction() {
    // em(x, 'P') — the derived `Ord (Lit c v)` puts `Con` before `Var`
    // (VTerm.hs:56-57), so the sorted form leads with the constant.
    let x = bfree("x", 0, LSort::Msg);
    let p_lit = bpub("P");
    let em_unsorted = f_app_c(CSym::EMap, vec![x.clone(), p_lit.clone()]);
    let em_sorted = f_app_c(CSym::EMap, vec![p_lit.clone(), x.clone()]);
    assert_eq!(em_unsorted, em_sorted);
    let Term::App(_, args) = &em_sorted else {
        panic!("an application")
    };
    assert_eq!(args.as_ref(), &[p_lit.clone(), x.clone()]);

    // The same holds one level down, under exp(em(...), x) — the BP_IBS
    // shape — and inside the atom the store keeps.
    let mk = |t: BLNTerm| Guarded::Atom(ProtoAtom::EqE(t, bpub("z")));
    let exp = |inner: BLNTerm| {
        f_app_no_eq(
            tamarin_term::function_symbols::exp_sym(),
            vec![inner, x.clone()],
        )
    };
    assert_eq!(mk(exp(em_unsorted)), mk(exp(em_sorted)));

    // An AC argument list is flattened as well as sorted
    // (`fAppAC`, Term/Term/Raw.hs:119-129), so a chain folded either way
    // round is the same three-argument application.
    let leaf = |n: &str| bfree(n, 0, LSort::Msg);
    let mult = |a: BLNTerm, b: BLNTerm| f_app_ac(AcSym::Mult, vec![a, b]);
    let left = mult(mult(leaf("a"), leaf("b")), leaf("c"));
    let right = mult(leaf("a"), mult(leaf("b"), leaf("c")));
    assert_eq!(left, right);
    let Term::App(_, args) = &left else {
        panic!("an application")
    };
    assert_eq!(args.len(), 3);
}

/// `closeGuarded` substitutes each abstracted variable for its De Bruijn
/// index through `substFreeAtom`, whose `fmapTerm` rebuilds every
/// application with `fApp` (Guarded.hs:289-296).  The derived `Ord BVar`
/// puts `Bound i` before `Free x` (LTerm.hs:476-478), so an AC argument
/// list whose second operand is the one being bound comes back re-sorted
/// under the index.
#[test]
fn close_guarded_resorts_ac_arguments_under_the_bound_indices() {
    // `a * x` with `a` and `x` both free sorts to [a, x] (Ord LVar is
    // (idx, sort, name), LTerm.hs:546-548).
    let a = LVar::new("a", LSort::Msg, 0);
    let x = LVar::new("x", LSort::Msg, 0);
    let open: BLNTerm = f_app_ac(
        AcSym::Mult,
        vec![var_term(BVar::Free(a)), var_term(BVar::Free(x))],
    );
    let Term::App(_, open_args) = &open else {
        panic!("an application")
    };
    assert_eq!(
        open_args.as_ref(),
        &[var_term(BVar::Free(a)), var_term(BVar::Free(x))]
    );

    let closed = close_guarded(
        Quantifier::Ex,
        vec![x],
        vec![ProtoAtom::EqE(
            f_app_ac(AcSym::Mult, vec![var_term(a), var_term(x)]),
            pub_term("z"),
        )],
        gtrue(),
    );
    let Guarded::GGuarded { guards, .. } = &closed else {
        panic!("close_guarded builds a GGuarded")
    };
    let ProtoAtom::EqE(lhs, _) = &guards[0] else {
        panic!("the guard is the equality")
    };
    let Term::App(_, args) = lhs else {
        panic!("an application")
    };
    assert_eq!(
        args.as_ref(),
        &[var_term(BVar::Bound(0)), var_term(BVar::Free(a))],
        "binding `x` moves it ahead of the free `a`"
    );
}

/// `em/2` occupies the `C` tier of HS's derived `Ord FunSym`
/// (`NoEq < AC < C < List`, FunctionSymbols.hs:150-154), so it outranks
/// every `NoEq` and every `AC` head whatever the names involved.  The
/// classification is by name alone — `naryOpApp` builds `fAppC EMap` for
/// any `em(…)` application, builtin-declared or user-declared
/// (Theory/Text/Parser/Term.hs:103) — while the `op{t1}t2` spelling goes
/// through `binaryAlgApp`, which has no `em` case and yields `fAppNoEq`
/// (Theory/Text/Parser/Term.hs:109-121).
///
/// Oracle bytes (pinned build, Git revision ef3f0468), each from a theory
/// whose source order is `em` first:
///   * `builtins: bilinear-pairing` + `functions: f/2`,
///     `Test(em('g','h') * f('g','h'))`
///     renders `Test( (f('g', 'h')*em('g', 'h')) )` — `f` FIRST, though
///     `"em" < "f"` as names.
///   * same theory with `Test(em{'g'}'h' * f('g','h'))`
///     renders `Test( (em('g', 'h')*f('g', 'h')) )` — `em` FIRST, the
///     `NoEq` name order.
///   * `builtins: bilinear-pairing, multiset`,
///     `Test(em(~a,~b) + (~a * ~b))`
///     renders `Test( ((~a*~b)++em(~a, ~b)) )` — the `AC` product first.
///   * `builtins: diffie-hellman` + `functions: em/2, f/2` (no pairing
///     builtin), `Test(em('g','h') * f('g','h'))`
///     still renders `Test( (f('g', 'h')*em('g', 'h')) )`.
#[test]
fn em_funsym_key_is_c_tier() {
    use std::cmp::Ordering::{Greater, Less};
    let gl = bpub("g");
    let hl = bpub("h");
    let gh = vec![gl.clone(), hl.clone()];
    let em = f_app_c(CSym::EMap, gh.clone());
    let f = f_app_no_eq(user_sym("f", 2), gh.clone());

    // C(2) beats NoEq(0) in BOTH directions, name order notwithstanding.
    assert_eq!(
        f.cmp(&em),
        Less,
        "NoEq `f/2` must sort before C `em/2` despite \"em\" < \"f\""
    );
    assert_eq!(em.cmp(&f), Greater, "the order must be antisymmetric");
    // A NoEq name that already precedes "em" stays first — the tier, not
    // the name, is what moved.
    let aaa = f_app_no_eq(user_sym("aaa", 2), gh.clone());
    assert_eq!(aaa.cmp(&em), Less);

    // AC(1) < C(2): the multiset operand `'g'*'h'` precedes the pairing.
    let prod = f_app_ac(AcSym::Mult, gh.clone());
    assert_eq!(
        prod.cmp(&em),
        Less,
        "an AC head must sort before the C `em/2`"
    );

    // `em{'g'}'h'` is `fAppNoEq`, so it sorts by name and precedes `f/2`.
    let em_alg = f_app_no_eq(user_sym("em", 2), gh.clone());
    assert_eq!(
        em_alg.cmp(&f),
        Less,
        "the `op{{t1}}t2` spelling of em is a NoEq symbol, ordered by name"
    );
    assert_eq!(
        em_alg.cmp(&em),
        Less,
        "NoEq `em/2` and C `em/2` are distinct FunSyms, NoEq first"
    );

    // Two C terms tie on the whole FunSym key (`CSym` is a single nullary
    // constructor) and fall through to the argument list.
    let em_gg = f_app_c(CSym::EMap, vec![gl.clone(), gl.clone()]);
    assert_eq!(
        em_gg.cmp(&em),
        Less,
        "same-FunSym C terms compare by their arguments"
    );

    // Only the binary form is a C symbol: `viewTerm2` rejects a `C` node
    // of any other arity (Term/Term/Raw.hs:190), so a 3-ary `em` carries the
    // NoEq key and its name order.
    let em3 = f_app_no_eq(user_sym("em", 3), vec![gl.clone(), hl.clone(), gl.clone()]);
    assert_eq!(em3.cmp(&f), Less);
}

/// `subst_blnterm_cow` reports `Some` exactly on a domain hit: the leaf's
/// whole `LVar` is the key, and a `Subst` holds no `x ~> x` mapping
/// (SubstVFree.hs:163-165), so a hit always changes the leaf.  The image is
/// lifted through `fmapTerm (fmap Free)` (SubstVFree.hs:297-302).
#[test]
fn subst_blnterm_cow_reports_a_domain_hit() {
    let s = LNSubst::from_list(vec![(
        LVar::new("x", LSort::Msg, 0),
        var_term(LVar::new("x", LSort::Msg, 7)),
    )]);

    let leaf = |sort: LSort| bfree("x", 0, sort);

    // A hit rebuilds to the lifted image.
    assert_eq!(
        subst_blnterm_cow(&leaf(LSort::Msg), &s),
        Some(bfree("x", 7, LSort::Msg)),
        "a domain hit must rebuild to the lifted image"
    );

    // A leaf that shares the name and the index but carries another sort is
    // another variable, so it is a miss.
    assert_eq!(
        subst_blnterm_cow(&leaf(LSort::Fresh), &s),
        None,
        "a leaf of another sort must report None"
    );

    // A leaf whose name is not in the domain returns None (miss).
    assert_eq!(
        subst_blnterm_cow(&bfree("y", 0, LSort::Msg), &s),
        None,
        "a domain miss must report None"
    );

    // A `Bound` leaf carries no variable identity, so it is never a hit.
    assert_eq!(subst_blnterm_cow(&var_term(BVar::Bound(0)), &s), None);
}

/// The witness map keys on the whole `LVar`, so two `x`-named leaves that
/// share an index but differ in sort each keep their own sort under the
/// `idx == 0` canonicalisation.
#[test]
fn witness_subst_keys_distinguish_sorts() {
    let msg_x = LVar::new("x", LSort::Msg, 3);
    let fresh_x = LVar::new("x", LSort::Fresh, 3);
    let g = Guarded::Atom(ProtoAtom::Action(
        var_term(BVar::Free(LVar::new("i", LSort::Node, 0))),
        bfact(
            false,
            "A",
            vec![var_term(BVar::Free(msg_x)), var_term(BVar::Free(fresh_x))],
        ),
    ));
    let normalised = normalize_witness_lvars_cow(&g).expect("both witnesses move to idx 0");
    let Guarded::Atom(ProtoAtom::Action(_, fa)) = &normalised else {
        panic!("expected Atom(Action), got {normalised:?}");
    };
    assert_eq!(
        fa.terms.as_ref(),
        [
            var_term(BVar::Free(LVar::new("x", LSort::Msg, 0))),
            var_term(BVar::Free(LVar::new("x", LSort::Fresh, 0))),
        ]
    );
}

// =============================================================================
// Opened binders
// =============================================================================

/// HS's formula parser reads a bare fact as `Syntactic . Pred`
/// (Theory/Text/Parser/Formula.hs:51), which `to_lnformula` cannot strip
/// (Theory/Model/Formula.hs:369-373).  A formula that reaches the conversion
/// without predicate expansion is a [`GuardError`], where the expanded one
/// converts.
#[test]
fn formula_to_guarded_parsed_reports_a_residual_predicate_atom() {
    let sig = pair_maude_sig();
    let f = parse_formula_str("Ex x #i. A(x) @ #i & P(x)", &sig).expect("parse");
    let e = formula_to_guarded_parsed(&f, &sig).expect_err("the predicate atom is sugar");
    assert_eq!(
        e.message,
        "Syntactic sugar is not allowed, guarded formula expected."
    );
}

/// HS `noUnguardedVars` names the survivors of the prefix `openFormulaPrefix`
/// drew (Guarded.hs:507-514), and `avoidPrecise` seeds that supply from the
/// free variables (LTerm.hs:706-709,714-715), so a free `x.3` puts the
/// binder `x` at index 4.  The expected bytes are the pinned oracle's, as
/// `tests/guarded_unguarded_freshening.rs` records them.
#[test]
fn reports_the_unguarded_variable_under_its_freshened_name() {
    let e =
        g("Foo(x.3) @ #i ==> (All x z. (<x, z> = x) ==> F)").expect_err("x and z are unguarded");
    assert_eq!(
        e.message,
        "unguarded variable(s) 'x.4', 'z' in the subformula"
    );
}

/// A binder whose name an enclosing binder already took is drawn one index
/// further on, which both names it in the diagnostic and makes it a variable
/// of its own: written with that index in the source, the same shape is
/// guarded, because the equation's right-hand side is then the OUTER `x` and
/// is covered.
#[test]
fn opens_a_shadowed_binder_under_a_fresh_index() {
    let e = g("All x #NOW. Foo(x) @ #NOW ==> (All x z. (<x, z> = x) ==> F)")
        .expect_err("the inner x and z are unguarded");
    assert_eq!(
        e.message,
        "unguarded variable(s) 'x.1', 'z' in the subformula"
    );
    let r = g("All x #NOW. Foo(x) @ #NOW ==> (All x.1 z. (<x.1, z> = x) ==> F)")
        .expect("x.1 and z are guarded by the pair equation");
    assert!(is_safety_formula(&r));
}

/// HS `convAll` accepts only `Conn Imp ante suc` beneath the prefix
/// (Guarded.hs:546-563).
#[test]
fn rejects_a_universal_without_a_toplevel_implication() {
    let e = g("All k #i. Setup(k) @ #i").expect_err("the body is an action, not an implication");
    assert_eq!(
        e.message,
        "universal quantifier without toplevel implication"
    );
}

/// HS `convert polarity (Conn Iff f1 f2)` is `gconj` of the two implications
/// (Guarded.hs:565-566), which at the entry polarity is what the written
/// conjunction of them converts to.
#[test]
fn treats_iff_as_two_implications() {
    let iff = g("(Ex x #i. A(x) @ #i) <=> (Ex y #j. B(y) @ #j)").expect("both sides are guarded");
    let spelled_out = g("((Ex x #i. A(x) @ #i) ==> (Ex y #j. B(y) @ #j)) & \
         ((Ex y #j. B(y) @ #j) ==> (Ex x #i. A(x) @ #i))")
    .expect("both sides are guarded");
    assert_eq!(iff, spelled_out);
    assert!(
        matches!(&iff, Guarded::Conj(items) if items.len() == 2),
        "the two implications are conjoined, got {iff:?}"
    );
}

// =============================================================================
// openGuarded (Guarded.hs:364-373)
// =============================================================================

/// `openGuarded` draws one variable per binder through `freshLVar`
/// (Guarded.hs:367, LTerm.hs:301-302), so three nested prefixes that all bind
/// the name `x` take the indices 0, 1 and 2 from one supply.  Those are the
/// names the printer shows, because `prettyGuarded`'s `GGuarded` arm opens
/// the binder from the very supply its `scopeFreshness` holds
/// (Guarded.hs:847-849).
#[test]
fn open_guarded_draws_the_binder_names_the_printer_shows() {
    use tamarin_utils::fresh::PreciseFreshState;
    let gf = g("Ex x #i. A(x) @ #i & (Ex x #j. A(x) @ #j & (Ex x #k. A(x) @ #k))")
        .expect("guarded conversion");

    let mut fresh = PreciseFreshState::nothing_used();
    let mut drawn: Vec<String> = Vec::new();
    let mut cur = gf.clone();
    while let Some((_qua, vs, _ats, body)) = open_guarded(&cur, &mut fresh) {
        drawn.extend(vs.iter().map(|v| v.to_string()));
        cur = body;
    }
    assert_eq!(
        drawn,
        vec!["x", "#i", "x.1", "#j", "x.2", "#k"],
        "each prefix draws the next index for the name it repeats"
    );

    // The printed formula names the same binders.
    let shown = crate::pretty_formula::pretty_guarded(&gf);
    for prefix in ["\u{2203} x #i.", "\u{2203} x.1 #j.", "\u{2203} x.2 #k."] {
        assert!(shown.contains(prefix), "missing {prefix:?} in {shown:?}");
    }
}

/// `openGuarded`'s `substBoundAtom` is `fmap (fmapTerm (fmap subst))`
/// (Guarded.hs:290), which rebuilds the application through `fApp`, and
/// `fAppC` sorts a commutative symbol's arguments
/// (`fAppC nacsym as = FAPP (C nacsym) (sort as)`, Term/Term/Raw.hs:133-134).
/// So a stored `em` whose arguments the drawn variable puts out of order comes
/// back sorted.
#[test]
fn open_guarded_sorts_a_commutative_argument_pair() {
    use std::sync::Arc;
    use tamarin_utils::fresh::PreciseFreshState;
    let a = LVar::new("a", LSort::Msg, 0);
    // `em(Bound 0, a)` with `x` the binder: `Ord BVar` puts `Bound` first
    // (LTerm.hs:476-478), and `Ord LVar` is (idx, sort, name)
    // (LTerm.hs:546-548), so opening `x` at index 0 puts `a` first.
    let em = f_app_c(
        CSym::EMap,
        vec![var_term(BVar::Bound(0)), var_term(BVar::Free(a))],
    );
    let gf = Guarded::GGuarded {
        qua: Quantifier::Ex,
        vars: vec![("x".to_string(), LSort::Msg)].into(),
        guards: vec![ProtoAtom::EqE(em, bpub("z"))].into(),
        body: Arc::new(gtrue()),
    };

    let mut fresh = PreciseFreshState::nothing_used();
    let (qua, vs, ats, body) = open_guarded(&gf, &mut fresh).expect("a GGuarded opens");
    assert_eq!(qua, Quantifier::Ex);
    assert_eq!(vs, vec![LVar::new("x", LSort::Msg, 0)]);
    assert_eq!(
        ats,
        vec![ProtoAtom::EqE(
            f_app_c(CSym::EMap, vec![var_term(a), var_term(vs[0])]),
            pub_term("z"),
        )]
    );
    assert_eq!(body, gtrue());
}

/// Anything but a `GGuarded` opens to `None` (HS `openGuarded _ = return
/// Nothing`, Guarded.hs:373).
#[test]
fn open_guarded_declines_a_non_guarded_formula() {
    use tamarin_utils::fresh::PreciseFreshState;
    let mut fresh = PreciseFreshState::nothing_used();
    assert!(open_guarded(&gtrue(), &mut fresh).is_none());
    assert!(open_guarded(&gfalse(), &mut fresh).is_none());
}

// =============================================================================
// HasFrees for Guarded (Guarded.hs:272-277)
// =============================================================================

fn hf_leaf(name: &str, idx: u64, sort: LSort) -> BLNTerm {
    bfree(name, idx, sort)
}

fn hf_fact(name: &str, args: Vec<BLNTerm>) -> Fact<BLNTerm> {
    bfact(false, name, args)
}

fn hf_names(g: &Guarded) -> Vec<String> {
    let mut out = Vec::new();
    g.for_each_free(&mut |v| out.push(format!("{}.{}", v.name, v.idx)));
    out
}

/// HS `Foldable`/`Traversable ProtoAtom` fold the timepoint of an `Action`
/// before the fact (Atom.hs:130-131, 139-140).  Both directions of the
/// `HasFrees` instance carry that order.
#[test]
fn action_atom_visits_timepoint_before_fact() {
    let atom = ProtoAtom::Action(
        hf_leaf("i", 2, LSort::Node),
        hf_fact("A", vec![hf_leaf("x", 1, LSort::Msg)]),
    );
    let g = Guarded::Atom(atom.clone());

    assert_eq!(hf_names(&g), vec!["i.2", "x.1"]);

    assert_eq!(
        tamarin_term::lterm::frees_list(&atom)
            .iter()
            .map(|v| v.name)
            .collect::<Vec<_>>(),
        vec!["i", "x"]
    );

    let mut mapped = Vec::new();
    let _ = atom.clone().map_free(&mut |v| {
        mapped.push(v.name.to_string());
        v
    });
    assert_eq!(mapped, vec!["i", "x"]);
}

/// `BVar::Bound` leaves are positional and carry no variable identity, so
/// neither direction of the instance touches them (Guarded.hs:259-263 folds
/// through the atoms only).
#[test]
fn bound_leaves_are_skipped() {
    let g = Guarded::GGuarded {
        qua: Quantifier::Ex,
        vars: vec![("z".to_string(), LSort::Msg)].into(),
        guards: vec![ProtoAtom::EqE(
            var_term(BVar::Bound(0)),
            hf_leaf("y", 4, LSort::Msg),
        )]
        .into(),
        body: std::sync::Arc::new(gtrue()),
    };

    assert_eq!(hf_names(&g), vec!["y.4"]);

    let renamed = g
        .clone()
        .map_free(&mut |v| LVar::new("r", v.sort, v.idx + 10));
    let Guarded::GGuarded { guards, vars, .. } = &renamed else {
        panic!("map_free must keep the GGuarded shape")
    };
    assert_eq!(vars[0].0, "z", "the binder list stays verbatim");
    assert_eq!(
        guards[0],
        ProtoAtom::EqE(var_term(BVar::Bound(0)), hf_leaf("r", 14, LSort::Msg))
    );
}

/// HS folds a `GGuarded`'s guard atoms before its body
/// (`foldMap … as `mappend` b`, Guarded.hs:259-263).
#[test]
fn guards_visited_before_body() {
    let g = Guarded::GGuarded {
        qua: Quantifier::All,
        vars: vec![].into(),
        guards: vec![ProtoAtom::EqE(
            hf_leaf("g", 1, LSort::Msg),
            hf_leaf("h", 2, LSort::Msg),
        )]
        .into(),
        body: std::sync::Arc::new(Guarded::Conj(
            vec![Guarded::Atom(ProtoAtom::Last(hf_leaf("b", 3, LSort::Node)))].into(),
        )),
    };
    assert_eq!(hf_names(&g), vec!["g.1", "h.2", "b.3"]);
}

/// HS `mapFrees`/`foldFrees` on a guarded formula reach the `LVar` inside a
/// `Free` leaf and write the mapped variable back WHOLE (Guarded.hs:272-277
/// through `HasFrees LVar`, LTerm.hs:746-752), so the mapped sort is the one
/// the leaf carries afterwards.
#[test]
fn hasfrees_map_takes_the_mapped_sort() {
    let g = Guarded::Atom(ProtoAtom::Last(hf_leaf("x", 1, LSort::Fresh)));

    let renamed = g.map_free(&mut |v| {
        assert_eq!(v.sort, LSort::Fresh);
        LVar::new("w", LSort::Msg, 9)
    });
    assert_eq!(
        renamed,
        Guarded::Atom(ProtoAtom::Last(hf_leaf("w", 9, LSort::Msg)))
    );
}

/// `mapFrees` rebuilds each application through `fApp`
/// (`fmapTerm`, Term/Term/Raw.hs:111-115), so a rename that reorders an AC
/// argument list under `Ord LVar` comes back sorted.
#[test]
fn renaming_a_guarded_formula_resorts_its_ac_arguments() {
    // `a * b` sorts to [a, b]; renaming `a` to `z` must swap them.
    let a = LVar::new("a", LSort::Msg, 0);
    let b = LVar::new("b", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let g = Guarded::Atom(ProtoAtom::EqE(
        f_app_ac(
            AcSym::Mult,
            vec![var_term(BVar::Free(a)), var_term(BVar::Free(b))],
        ),
        bpub("t"),
    ));

    let renamed = g.map_free(&mut |v| if v == a { z } else { v });
    assert_eq!(
        renamed,
        Guarded::Atom(ProtoAtom::EqE(
            f_app_ac(
                AcSym::Mult,
                vec![var_term(BVar::Free(b)), var_term(BVar::Free(z))],
            ),
            bpub("t"),
        ))
    );
}

// =============================================================================
// The spelling an internal term takes inside the guarded store
// =============================================================================

/// The guarded atom an `LNTerm` equation takes: HS `freeTerm = fmap (fmap
/// freeLNTerm)` on both sides (LTerm.hs:521-523).
fn stored_eq(l: &LNTerm, r: &LNTerm) -> Atom<BLNTerm> {
    ProtoAtom::EqE(lift_free(l), lift_free(r))
}

/// The store keeps an AC application's argument list FLAT and sorted, as
/// `fAppAC` builds it (Term/Term/Raw.hs:119-129) — never a nested binary
/// chain over the same leaves.
#[test]
fn guarded_store_holds_a_flat_ac_application() {
    let t: LNTerm = f_app_ac(
        AcSym::Mult,
        vec![pub_term("c"), pub_term("a"), pub_term("b")],
    );
    let ProtoAtom::EqE(lhs, _) = stored_eq(&t, &t) else {
        panic!("an equality")
    };
    let Term::App(sym, args) = &lhs else {
        panic!("an application")
    };
    assert_eq!(
        *sym,
        tamarin_term::function_symbols::FunSym::Ac(AcSym::Mult)
    );
    assert_eq!(
        args.as_ref(),
        &[bpub("a"), bpub("b"), bpub("c")],
        "the three operands stay in one sorted list"
    );
}

/// `one`, `tone` and `DH_neutral` are nullary `NoEq` applications, and the
/// store keeps them as such (FunctionSymbols.hs:255,257,267).
#[test]
fn guarded_store_holds_the_nullary_constants_as_applications() {
    use tamarin_term::function_symbols::{dh_neutral_sym, nat_one_sym, one_sym};

    for sym in [one_sym(), nat_one_sym(), dh_neutral_sym()] {
        let t: LNTerm = f_app_no_eq(sym, vec![]);
        assert_eq!(
            stored_eq(&t, &t),
            ProtoAtom::EqE(f_app_no_eq(sym, vec![]), f_app_no_eq(sym, vec![]))
        );
    }
}

/// A tuple is a RIGHT-nested chain of the binary `pairSym`
/// (`fAppPair`, Term/Term.hs:163), and the store keeps that chain: the
/// UM_three_pass `CK_secure_UM3` term is `<'UM3', <B, <A, <'1', 'g'^~ex>>>>`,
/// four `pair` nodes deep.
#[test]
fn guarded_store_holds_a_binary_pair_chain() {
    use tamarin_term::function_symbols::{exp_sym, pair_sym};

    let pair = |a: LNTerm, b: LNTerm| f_app_no_eq(pair_sym(), vec![a, b]);
    let b: LNTerm = var_term(LVar::new("B", LSort::Msg, 0));
    let a: LNTerm = var_term(LVar::new("A", LSort::Msg, 0));
    let ex: LNTerm = f_app_no_eq(
        exp_sym(),
        vec![pub_term("g"), var_term(LVar::new("ex", LSort::Fresh, 0))],
    );
    let t: LNTerm = pair(
        pub_term("UM3"),
        pair(b.clone(), pair(a.clone(), pair(pub_term("1"), ex.clone()))),
    );

    let bpair = |x: BLNTerm, y: BLNTerm| f_app_no_eq(pair_sym(), vec![x, y]);
    let chain = bpair(
        bpub("UM3"),
        bpair(
            lift_free(&b),
            bpair(lift_free(&a), bpair(bpub("1"), lift_free(&ex))),
        ),
    );
    assert_eq!(stored_eq(&t, &t), ProtoAtom::EqE(chain.clone(), chain));

    // Every node of the chain is the binary `pairSym`, so the depth is the
    // number of components less one.
    let mut depth = 0usize;
    let mut cur = lift_free(&t);
    while let Term::App(sym, args) = &cur {
        if *sym != tamarin_term::function_symbols::FunSym::NoEq(pair_sym()) {
            break;
        }
        assert_eq!(args.len(), 2, "a pair node is binary");
        depth += 1;
        cur = args[1].clone();
    }
    assert_eq!(depth, 4);
}
