// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_parser::parser::parse_formula_str;
use tamarin_term::maude_sig::pair_maude_sig;

fn g(s: &str) -> Result<Guarded, GuardError> {
    let f = parse_formula_str(s, &pair_maude_sig()).map_err(|e| err(format!("parse: {}", e)))?;
    formula_to_guarded(&f)
}

#[test]
fn ground_truth() {
    let r = g("T").unwrap();
    assert_eq!(r, gtrue());
}

// GFact builder for cmp_fact ordering tests.
fn gf(persistent: bool, name: &str) -> GFact {
    GFact {
        persistent,
        name: name.into(),
        args: vec![].into(),
        annotations: vec![],
    }
}

/// HS `FactTag` derived Ord segregates all ProtoFacts before every
/// special tag, and orders the special tags in declaration sequence
/// (Fr < Out < In < KU < KD < Ded < Term).  cmp_fact must reproduce
/// this from the canonicalised name string.
#[test]
fn cmp_fact_special_tag_segregation() {
    use std::cmp::Ordering::Less;
    // A ProtoFact with a name that lexically sorts AFTER every special
    // name must still come FIRST (constructor index dominates).
    let proto_z = gf(false, "Zebra");
    for special in ["Fr", "Out", "In", "KU", "KD", "Ded", "Term"] {
        let persistent = matches!(special, "KU" | "KD");
        let s = gf(persistent, special);
        assert_eq!(
            cmp_fact(&proto_z, &s),
            Less,
            "ProtoFact must sort before special tag {special}"
        );
    }
    // Special tags order in declaration sequence.
    assert_eq!(cmp_fact(&gf(false, "Fr"), &gf(false, "Out")), Less);
    assert_eq!(cmp_fact(&gf(false, "Out"), &gf(false, "In")), Less);
    assert_eq!(cmp_fact(&gf(false, "In"), &gf(true, "KU")), Less);
    assert_eq!(cmp_fact(&gf(true, "KU"), &gf(true, "KD")), Less);
    assert_eq!(cmp_fact(&gf(true, "KD"), &gf(false, "Ded")), Less);
    assert_eq!(cmp_fact(&gf(false, "Ded"), &gf(false, "Term")), Less);
    // "K" is an ordinary ProtoFact (not special), so it precedes Fr.
    assert_eq!(cmp_fact(&gf(false, "K"), &gf(false, "Fr")), Less);
}

/// ProtoFacts compare by (Persistent<Linear, name, arity).
#[test]
fn cmp_fact_proto_triple() {
    use std::cmp::Ordering::Less;
    // Persistent < Linear (reversed bool).
    assert_eq!(cmp_fact(&gf(true, "P"), &gf(false, "P")), Less);
    // Then by name.
    assert_eq!(cmp_fact(&gf(false, "A"), &gf(false, "B")), Less);
    // Then by arity.
    let a1 = GFact {
        persistent: false,
        name: "P".into(),
        args: vec![].into(),
        annotations: vec![],
    };
    let a2 = GFact {
        persistent: false,
        name: "P".into(),
        args: vec![crate::guarded_types::GTerm::Var(
            crate::guarded_types::BVar::Bound(0),
        )]
        .into(),
        annotations: vec![],
    };
    assert_eq!(cmp_fact(&a1, &a2), Less);
}

/// HS's pair is a nested arity-2 FAPP (`fAppPair`, Term/Term.hs:163), so
/// `<a, z>` and `<a, b, c>` first differ at argument 2 — `z` against
/// `pair(b, c)` — where `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74) puts
/// `<a, z>` first.  Comparing RS's FLAT operand vectors element-wise
/// would weigh `b` against `z` and reverse the two.
#[test]
fn cmp_term_orders_pairs_by_their_nested_spine() {
    use crate::guarded_types::term_to_gterm_free;
    use std::cmp::Ordering::{Equal, Greater, Less};
    let short = term_to_gterm_free(&p::Term::Pair(vec![var("a", 0), var("z", 0)]));
    let long = term_to_gterm_free(&p::Term::Pair(vec![var("a", 0), var("b", 0), var("c", 0)]));
    assert_eq!(cmp_term(&short, &long), Less);
    assert_eq!(cmp_term(&long, &short), Greater);
    // The right-nested spelling of the SAME term compares equal, so the
    // flat `Pair` and the tail it stands for are interchangeable.
    let nested = term_to_gterm_free(&p::Term::Pair(vec![
        var("a", 0),
        p::Term::Pair(vec![var("b", 0), var("c", 0)]),
    ]));
    assert_eq!(cmp_term(&long, &nested), Equal);
}

/// The source spelling `pair(a, b)` is HS's `pairSym` FAPP just like
/// `<a, b>` (`naryOpApp`, Theory/Text/Parser/Term.hs:88-105, see line
/// 104), so the two `GTerm` shapes tie — and both order against a longer
/// pair through the same nested spine.
#[test]
fn cmp_term_ties_the_prefix_pair_spelling_with_the_bracket_spelling() {
    use crate::guarded_types::term_to_gterm_free;
    use std::cmp::Ordering::{Equal, Less};
    let prefix = term_to_gterm_free(&p::Term::App("pair".into(), vec![var("a", 0), var("z", 0)]));
    let bracket = term_to_gterm_free(&p::Term::Pair(vec![var("a", 0), var("z", 0)]));
    assert_eq!(cmp_term(&prefix, &bracket), Equal);
    let long = term_to_gterm_free(&p::Term::Pair(vec![var("a", 0), var("b", 0), var("c", 0)]));
    assert_eq!(cmp_term(&prefix, &long), Less);
}

/// Both variable orderings compare the sort with `LSort`'s derived `Ord`,
/// which ranks the five sorts in their declaration order
/// (Term/LTerm.hs:165-170): `Pub`, `Fresh`, `Msg`, `Node`, `Nat`.  The printed
/// operand order of an AC application rides on this through `cmp_term`, so a
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

    let vs = |sort| p::VarSpec {
        name: "x".into(),
        idx: 0,
        sort,
        typ: None,
    };
    let b = |sort| GBinding {
        name: "x".into(),
        sort,
    };
    for (i, &s) in declared.iter().enumerate() {
        for (j, &t) in declared.iter().enumerate() {
            let want = i.cmp(&j);
            assert_eq!(cmp_varspec(&vs(s), &vs(t)), want, "{s:?} vs {t:?}");
            assert_eq!(cmp_binding(&b(s), &b(t)), want, "{s:?} vs {t:?}");
        }
    }
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
    let a = g("Last(#i)").unwrap();
    let b = g("Last(#j)").unwrap();
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
    let atom = g("Last(#i)").expect("guarded");
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
            assert_eq!(qua, Quant::All);
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
            assert_eq!(qua, Quant::Ex);
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
            assert_eq!(*qua, Quant::All);
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
            assert_eq!(*qua, Quant::Ex);
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
            assert_eq!(*qua, Quant::All);
            assert_eq!(vars.len(), 2, "binders k and #i");
            assert_eq!(guards.len(), 1, "the antecedent is the guard");
            match &**body {
                Guarded::GGuarded { qua, vars, .. } => {
                    assert_eq!(*qua, Quant::Ex);
                    assert_eq!(vars.len(), 2, "binders j and #t");
                }
                other => panic!("expected the consequent as the body, got {:?}", other),
            }
        }
        x => panic!("got {:?}", x),
    }
}

// =========================================================================
// VarSubst correctness tests — the term-based substitution model
// =========================================================================

fn var(name: &str, idx: u64) -> p::Term {
    p::Term::Var(p::VarSpec {
        name: name.into(),
        idx,
        sort: LSort::Msg,
        typ: None,
    })
}
fn pubconst(s: &str) -> p::Term {
    p::Term::PubLit(s.into())
}

#[test]
fn varsubst_var_to_non_var_term() {
    // Bind `k` to the public constant 'foo'.
    let mut s = VarSubst::default();
    s.insert(("k", 0), pubconst("foo"));
    let result = subst_term(&var("k", 0), &s);
    assert_eq!(result, pubconst("foo"));
}

#[test]
fn varsubst_descends_into_app_args() {
    // `f(k, m)` where `k` is bound to 'foo'.
    let mut s = VarSubst::default();
    s.insert(("k", 0), pubconst("foo"));
    let t = p::Term::App("f".into(), vec![var("k", 0), var("m", 0)]);
    let result = subst_term(&t, &s);
    let expected = p::Term::App("f".into(), vec![pubconst("foo"), var("m", 0)]);
    assert_eq!(result, expected);
}

/// The substitution uses `(name, idx)` as the key.  A variable with the same
/// name but a different index is another variable.  It passes through
/// unchanged.
#[test]
fn varsubst_idx_aware() {
    let mut s = VarSubst::default();
    s.insert(("x", 5), var("y", 0));
    // x with idx 5 → y, x with idx 6 unchanged.
    assert_eq!(subst_term(&var("x", 5), &s), var("y", 0));
    assert_eq!(subst_term(&var("x", 6), &s), var("x", 6));
}

#[test]
fn varsubst_pair_descent() {
    let mut s = VarSubst::default();
    s.insert(("a", 0), pubconst("X"));
    let t = p::Term::Pair(vec![var("a", 0), var("b", 0)]);
    let result = subst_term(&t, &s);
    let expected = p::Term::Pair(vec![pubconst("X"), var("b", 0)]);
    assert_eq!(result, expected);
}

/// The parser sorts the `#i` binder and the `@ i` occurrence alike, as
/// `Node`, so `close_subst` binds the body occurrence and `gnot`/`ginduct`
/// see a closed formula.
#[test]
fn injectivity_check_ginduct_succeeds() {
    let gf = g("not (Ex id #i #j #k. Initiated(id) @ i & Removed(id) @ j & Copied(id) @ k & #i < #j & #j < #k)").expect("guarded");
    let g_neg = gnot(&gf);
    assert!(free_vars(&g_neg).is_empty(), "gnot should be closed");
    assert!(ginduct(&g_neg).is_ok(), "ginduct should succeed");
}

#[test]
fn varsubst_shadowing_blocks_inner_binder() {
    // `Ex k. Action(k) @ i` — substituting `k` from outside should
    // NOT rewrite the inner `k` because it's positionally bound
    // (DeBruijn `Bound(0)` in the body, not Free LVar `k:0`).
    let mut s = VarSubst::default();
    s.insert(("k", 0), pubconst("OUTER"));
    let inner_k = p::VarSpec {
        name: "k".into(),
        idx: 0,
        sort: LSort::Msg,
        typ: None,
    };
    let mkfact = |t: p::Term| p::Fact {
        persistent: false,
        annotations: Vec::new(),
        name: "Action".into(),
        args: vec![t],
    };
    // Build via close_guarded so that `k` becomes Bound(0) in the body.
    let g = close_guarded(
        Quant::Ex,
        vec![inner_k.clone()],
        Vec::new(),
        Guarded::Atom(atom_to_gatom_free(&p::Atom::Action(
            mkfact(var("k", 0)),
            var("i", 0),
        ))),
    );
    let result = subst_guarded(&g, &s);
    // Body should be unchanged: subst on Free `(k, 0)` doesn't
    // touch the Bound `k` reference.
    match result {
        Guarded::GGuarded { body, .. } => match &*body {
            Guarded::Atom(GAtom::Action(fa, _)) => {
                // Walk the body atom and verify the `k` slot is still Bound(0).
                match &fa.args[0] {
                    GTerm::Var(BVar::Bound(0)) => {}
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
                matches!(&items[1], Guarded::GGuarded { qua: Quant::Ex, .. }),
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
fn last_bound_indices(g: &Guarded) -> Vec<u32> {
    fn go(g: &Guarded, out: &mut Vec<u32>) {
        match g {
            Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Bound(n)))) => out.push(*n),
            Guarded::Atom(_) => {}
            Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().for_each(|x| go(x, out)),
            Guarded::GGuarded { guards, body, .. } => {
                for a in guards.iter() {
                    if let GAtom::Last(GTerm::Var(BVar::Bound(n))) = a {
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
            assert_eq!(*qua, Quant::Ex);
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

fn mk_eq(a: &str, b: &str) -> p::Atom {
    p::Atom::Eq(var(a, 0), var(b, 0))
}

fn mk_atom_eq(a: &str, b: &str) -> Guarded {
    Guarded::Atom(atom_to_gatom_free(&mk_eq(a, b)))
}

#[test]
fn simplify_atom_with_known_true_collapses_to_gtrue() {
    let g = mk_atom_eq("x", "y");
    let val = |_a: &p::Atom| Some(true);
    assert_eq!(simplify_guarded_with(&g, &val), gtrue());
}

#[test]
fn simplify_atom_with_known_false_collapses_to_gfalse() {
    let g = mk_atom_eq("x", "y");
    let val = |_a: &p::Atom| Some(false);
    assert_eq!(simplify_guarded_with(&g, &val), gfalse());
}

#[test]
fn simplify_atom_unknown_left_intact() {
    let g = mk_atom_eq("x", "y");
    let val = |_a: &p::Atom| None;
    assert_eq!(simplify_guarded_with(&g, &val), g);
}

#[test]
fn simplify_disj_drops_false_branches() {
    // a ∨ b — if b evaluates False and a is unknown, result = a.
    let a = mk_atom_eq("p", "q");
    let b = mk_eq("r", "s");
    let g = Guarded::Disj(vec![a.clone(), Guarded::Atom(atom_to_gatom_free(&b))].into());
    let val = move |atom: &p::Atom| if atom == &b { Some(false) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), a);
}

#[test]
fn simplify_conj_short_circuits_on_false() {
    // a ∧ b — if b evaluates False, conj should be gfalse.
    let b = mk_eq("r", "s");
    let g = Guarded::Conj(vec![mk_atom_eq("p", "q"), Guarded::Atom(atom_to_gatom_free(&b))].into());
    let val = move |atom: &p::Atom| if atom == &b { Some(false) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), gfalse());
}

/// Returns a binder-free universal with the given guards over the body
/// `p = q`.
fn mk_universal(vars: Vec<GBinding>, guards: &[p::Atom]) -> Guarded {
    Guarded::GGuarded {
        qua: Quant::All,
        vars: vars.into(),
        guards: guards.iter().map(atom_to_gatom_free).collect(),
        body: std::sync::Arc::new(mk_atom_eq("p", "q")),
    }
}

#[test]
fn simplify_universal_with_one_false_guard_is_gtrue() {
    // (All vars[]. [a, b]. body) with a=False → gtrue (vacuous).
    let a = mk_eq("a", "b");
    let g = mk_universal(Vec::new(), &[a.clone(), mk_eq("c", "d")]);
    let val = move |atom: &p::Atom| if atom == &a { Some(false) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), gtrue());
}

#[test]
fn simplify_universal_drops_true_guards_keeps_unknown() {
    let a = mk_eq("a", "b");
    let b = mk_eq("c", "d");
    let g = mk_universal(Vec::new(), &[a.clone(), b.clone()]);
    // The valuation decides `a` as True, so the code drops it.  Every other
    // atom is unknown: `b` and the atom in the body.  Each unknown atom
    // survives unchanged.
    let val = move |atom: &p::Atom| if atom == &a { Some(true) } else { None };
    match simplify_guarded_with(&g, &val) {
        Guarded::GGuarded { vars, guards, .. } => {
            assert!(vars.is_empty());
            assert_eq!(guards, vec![atom_to_gatom_free(&b)].into());
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
    let g = mk_universal(Vec::new(), std::slice::from_ref(&a));
    let val = move |atom: &p::Atom| if atom == &a { Some(true) } else { None };
    assert_eq!(simplify_guarded_with(&g, &val), mk_atom_eq("p", "q"));
}

#[test]
fn simplify_universal_with_quantifier_left_intact() {
    // GGuarded with bound vars is left alone — Haskell delays
    // simplification past the binder.
    let bound_var = GBinding {
        name: "x".into(),
        sort: LSort::Msg,
    };
    let g = mk_universal(vec![bound_var], &[mk_eq("a", "b")]);
    let val = |_atom: &p::Atom| Some(true);
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
    let atom_g = g("Last(#i)").unwrap();
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
    let a = g("Last(#i)").unwrap();
    let b = g("Last(#j)").unwrap();
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
/// second application would unwrap.  `normalise_guarded` relies on
/// this one-pass idempotence (mirrors HS `gconj`).
#[test]
fn gconj_duplicates_collapse_to_bare_item() {
    let a = g("Last(#i)").unwrap();
    let out = gconj(vec![a.clone(), a.clone()]);
    assert_eq!(out, a, "gconj must dedupe before the singleton unwrap");
}

/// `gdisj` deduplicates syntactically-equal items.  Same as above,
/// for disjunction.  Without this dedup, `verify_checksign_test`-class
/// SplitG variants double up.
#[test]
fn gdisj_dedupes_syntactic_duplicates() {
    let a = g("Last(#i)").unwrap();
    let b = g("Last(#j)").unwrap();
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
    let a = g("Last(#i)").unwrap();
    let out = gconj(vec![a.clone()]);
    assert_eq!(out, a, "singleton gconj must unwrap to the lone item");
}

/// `gconj` flattens nested `Conj` one level.  Mirrors Haskell's
/// `concatMap` flatten.
#[test]
fn gconj_flattens_nested_conj_one_level() {
    let a = g("Last(#i)").unwrap();
    let b = g("Last(#j)").unwrap();
    let c = g("Last(#k)").unwrap();
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
    let a = g("Last(#a)").unwrap();
    let b = g("Last(#b)").unwrap();
    let c = g("Last(#c)").unwrap();
    let d = g("Last(#d)").unwrap();
    let e = g("Last(#e)").unwrap();
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
    let a = g("Last(#a)").unwrap();
    let b = g("Last(#b)").unwrap();
    let c = g("Last(#c)").unwrap();
    let d = g("Last(#d)").unwrap();
    let e = g("Last(#e)").unwrap();
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
    let a = g("Last(#i)").unwrap();
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
        Guarded::GGuarded { qua: Quant::Ex, .. } => {}
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
        Guarded::GGuarded { qua: Quant::Ex, .. } => {}
        other => panic!("test setup: expected Ex; got {:?}", other),
    }
    let n = gnot(&f);
    // After negation, outer quantifier must be All (or the formula
    // simplified — but for this non-trivial body it remains All).
    match n {
        Guarded::GGuarded {
            qua: Quant::All, ..
        } => {}
        other => panic!("expected All quantifier after negating Ex; got {:?}", other),
    }
}

/// De Morgan: `gnot (gconj [a, b]) = gdisj [gnot a, gnot b]`.
/// Already exercised in `gnot_conj_becomes_disj` — pin the dual.
#[test]
fn gnot_distributes_over_disj() {
    // ¬(a ∨ b) = ¬a ∧ ¬b
    let a = g("Last(#i)").unwrap();
    let b = g("Last(#j)").unwrap();
    let or = Guarded::Disj(vec![a.clone(), b.clone()].into());
    let neg = gnot(&or);
    // Should be Conj([¬a, ¬b]) — both negated.
    let expected = gconj(vec![gnot(&a), gnot(&b)]);
    assert_eq!(
        neg, expected,
        "De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b — required for IH derivation"
    );
}

/// `em` is the sole commutative (C) function symbol; HS stores it in
/// sorted-arg form (`fAppC EMap (sort [a,b])`).  `canonicalize_ac_in_guarded`
/// must sort the two `em` args so a substituted solved-formula and a
/// freshly-derived implied-formula over the same pairing compare equal —
/// otherwise `insertImpliedFormulas` re-fires a discharged reuse-lemma
/// disjunction (the idbased/BP_IBS bilinear divergence).
#[test]
fn canonicalize_sorts_commutative_em_args() {
    use std::sync::Arc;
    // Build em(x, 'P') — var-before-pub, i.e. NON-canonical, since
    // constants sort before variables in cmp_term.
    let x = GTerm::Var(BVar::Free(p::VarSpec {
        name: "x".into(),
        idx: 0,
        sort: LSort::Msg,
        typ: None,
    }));
    let p_lit = GTerm::PubLit("P".into());
    let em_unsorted = GTerm::App(Arc::from("em"), Arc::from(vec![x.clone(), p_lit.clone()]));
    let em_sorted = GTerm::App(Arc::from("em"), Arc::from(vec![p_lit.clone(), x.clone()]));
    // Wrap each in an Eq atom inside a trivial guarded formula so we
    // exercise the real `canonicalize_ac_in_guarded` entry point.
    let mk = |t: &GTerm| Guarded::Atom(GAtom::Eq(t.clone(), GTerm::PubLit("z".into())));
    let canon_unsorted = canonicalize_ac_in_guarded(&mk(&em_unsorted));
    let canon_sorted = canonicalize_ac_in_guarded(&mk(&em_sorted));
    // Both must canonicalise to the sorted form, hence be equal.
    assert_eq!(
        canon_unsorted, canon_sorted,
        "em(x,'P') and em('P',x) must canonicalise to the same form"
    );
    assert_eq!(
        canon_unsorted,
        mk(&em_sorted),
        "em args must be sorted to (pub, var) = ('P', x)"
    );
    // Also exercise em nested under exp(em(...), m) — the BP_IBS shape.
    let exp_unsorted = GTerm::BinOp(
        p::BinOp::Exp,
        Arc::new(em_unsorted.clone()),
        Arc::new(x.clone()),
    );
    let exp_sorted = GTerm::BinOp(
        p::BinOp::Exp,
        Arc::new(em_sorted.clone()),
        Arc::new(x.clone()),
    );
    assert_eq!(
        canonicalize_ac_in_guarded(&mk(&exp_unsorted)),
        canonicalize_ac_in_guarded(&mk(&exp_sorted)),
        "em nested under exp must also have its args sorted"
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
    use std::sync::Arc;
    let gl = GTerm::PubLit("g".into());
    let hl = GTerm::PubLit("h".into());
    let gh: Arc<[GTerm]> = Arc::from(vec![gl.clone(), hl.clone()]);
    let em = GTerm::App(Arc::from("em"), gh.clone());
    let f = GTerm::App(Arc::from("f"), gh.clone());

    // C(2) beats NoEq(0) in BOTH directions, name order notwithstanding.
    assert_eq!(
        cmp_term(&f, &em),
        Less,
        "NoEq `f/2` must sort before C `em/2` despite \"em\" < \"f\""
    );
    assert_eq!(cmp_term(&em, &f), Greater, "cmp_term must be antisymmetric");
    // A NoEq name that already precedes "em" stays first — the tier, not
    // the name, is what moved.
    let aaa = GTerm::App(Arc::from("aaa"), gh.clone());
    assert_eq!(cmp_term(&aaa, &em), Less);

    // AC(1) < C(2): the multiset operand `~a*~b` precedes the pairing.
    let prod = GTerm::BinOp(p::BinOp::Mult, Arc::new(gl.clone()), Arc::new(hl.clone()));
    assert_eq!(
        cmp_term(&prod, &em),
        Less,
        "an AC head must sort before the C `em/2`"
    );

    // `em{'g'}'h'` is `fAppNoEq`, so it sorts by name and precedes `f/2`.
    let em_alg = GTerm::AlgApp(Arc::from("em"), Arc::new(gl.clone()), Arc::new(hl.clone()));
    assert_eq!(
        cmp_term(&em_alg, &f),
        Less,
        "the `op{{t1}}t2` spelling of em is a NoEq symbol, ordered by name"
    );
    assert_eq!(
        cmp_term(&em_alg, &em),
        Less,
        "NoEq `em/2` and C `em/2` are distinct FunSyms, NoEq first"
    );

    // Two C terms tie on the whole FunSym key (`CSym` is a single nullary
    // constructor) and fall through to the argument list.
    let em_gg = GTerm::App(Arc::from("em"), Arc::from(vec![gl.clone(), gl.clone()]));
    assert_eq!(
        cmp_term(&em_gg, &em),
        Less,
        "same-FunSym C terms compare by their arguments"
    );

    // Only the binary form is a C symbol: `viewTerm2` rejects a `C` node
    // of any other arity (Term/Term/Raw.hs:190), so a 3-ary `em` keeps the
    // NoEq key and its name order.
    let em3 = GTerm::App(
        Arc::from("em"),
        Arc::from(vec![gl.clone(), hl.clone(), gl.clone()]),
    );
    assert_eq!(cmp_term(&em3, &f), Less);
}

#[test]
fn subst_gterm_cow_var_value_equality() {
    // The value-equality COW in `subst_gterm_cow`'s Var arm must return
    // `None` ONLY when the replacement reproduces the exact same leaf, and
    // must still rebuild (`Some`) whenever the hit normalises the leaf's
    // spelling — otherwise the leaf-canonicalisation of `term_to_gterm_free`
    // (the dropped `typ`) would be silently lost.
    let mut s: VarSubst = VarSubst::default();
    // Replacement is the canonical Msg-sorted, no-typ leaf.
    s.insert(
        ("x", 0),
        p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        }),
    );

    let leaf = |sort: LSort, typ: Option<&str>| {
        GTerm::Var(BVar::Free(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort,
            typ: typ.map(str::to_string),
        }))
    };

    // Exact identity hit: replacement == leaf → reuse the input (`None`).
    assert_eq!(
        subst_gterm_cow(&leaf(LSort::Msg, None), &s),
        None,
        "an identity hit must report None so the caller reuses the leaf"
    );

    // The Var arm keys on (name, idx), so a leaf of another sort is a hit
    // and must rebuild to the Msg-sorted replacement.
    assert_eq!(
        subst_gterm_cow(&leaf(LSort::Fresh, None), &s),
        Some(term_to_gterm_free(s.get(&("x", 0)).unwrap())),
        "a fresh-sorted leaf must rebuild to the Msg-sorted replacement"
    );

    // Typ-dropping hit — leaf carries a SAPIC `typ`, replacement drops it:
    // must rebuild so the `typ` is dropped.
    assert_eq!(
        subst_gterm_cow(&leaf(LSort::Msg, Some("A")), &s),
        Some(term_to_gterm_free(s.get(&("x", 0)).unwrap())),
        "a typ-annotated leaf must rebuild to the typ-dropped replacement"
    );

    // Non-identity idx remap still rebuilds.
    let mut s2: VarSubst = VarSubst::default();
    s2.insert(
        ("x", 0),
        p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 7,
            sort: LSort::Msg,
            typ: None,
        }),
    );
    assert_eq!(
        subst_gterm_cow(&leaf(LSort::Msg, None), &s2),
        Some(term_to_gterm_free(s2.get(&("x", 0)).unwrap())),
        "a real idx remap must rebuild"
    );

    // A leaf whose (name, idx) is not in the domain returns None (miss).
    assert_eq!(
        subst_gterm_cow(
            &GTerm::Var(BVar::Free(p::VarSpec {
                name: "y".into(),
                idx: 0,
                sort: LSort::Msg,
                typ: None,
            })),
            &s
        ),
        None,
        "a domain miss must report None"
    );
}
