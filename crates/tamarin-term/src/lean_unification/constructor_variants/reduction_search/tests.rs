mod inert_products;
mod projected;
mod total_free;

use super::*;
use crate::algebra_backend::AlgebraBackend;
use crate::builtin::{fst, hash, pair};
use crate::lterm::{pub_term, LVar};
use crate::maude_proc::MaudeHandle;
use crate::maude_sig::{hash_maude_sig, mset_maude_sig, pair_maude_sig, MaudeSig};
use crate::subterm_rule::{CtxtStRule, StRhs};
use crate::vterm::Lit;

fn bag<const N: usize>(terms: [LNTerm; N]) -> LNTerm {
    f_app_ac(AcSym::Union, terms.to_vec())
}

fn var(name: &str) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
}

/// A native-only session whose theory author asserts convergence. Reduction
/// no longer consults the specialised Rust reducer: a table the certifier
/// does not accept is normalized along one rewrite path under that premise,
/// and a raw session reports the table instead.
fn theory_session(sig: &MaudeSig) -> MaudeHandle {
    MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        sig.clone(),
        AlgebraBackend::NativeOnly,
        Default::default(),
    )
    .unwrap()
}

fn signature(rules: impl IntoIterator<Item = (LNTerm, LNTerm)>) -> MaudeSig {
    let mut sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    for (lhs, rhs) in rules {
        sig.st_rules.insert(CtxtStRule::new(
            lhs,
            StRhs {
                positions: vec![],
                term: rhs,
            },
        ));
    }
    sig.refresh()
}

#[test]
fn native_oracle_proper_subproducts_and_converging_branches() {
    let u = var("u");
    let k = var("k");
    let sig = signature([
        (bag([pair(u.clone(), k.clone()), k.clone()]), u.clone()),
        (bag([hash(u.clone()), u.clone()]), u.clone()),
        (
            bag([hash(hash(u.clone())), u.clone()]),
            bag([hash(u.clone()), u.clone()]),
        ),
    ]);
    let native = MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        sig.clone(),
        AlgebraBackend::NativeOnly,
        Default::default(),
    )
    .unwrap();
    let oracle = tamarin_test_support::require_maude_path()
        .map(|path| MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap());
    let a = pub_term("a");
    let b = pub_term("b");
    let c = pub_term("c");
    let d = pub_term("d");
    let protected = pair(pair(a.clone(), b.clone()), c.clone());
    let two_steps = bag([protected, c.clone(), b.clone(), d.clone()]);
    let open = bag([u.clone(), k.clone()]);
    let diamond = bag([hash(hash(a.clone())), hash(a.clone()), a.clone()]);
    for (input, normal) in [
        (two_steps.clone(), bag([a.clone(), d.clone()])),
        (hash(two_steps), hash(bag([a.clone(), d.clone()]))),
        // A repeated rule variable can consume a whole proper subproduct
        // containing rigid subject variables which use the same names.
        (
            bag([hash(open), u.clone(), k.clone(), d.clone()]),
            bag([u, k, d]),
        ),
        // Several distinct first steps have the same eventual normal state.
        (diamond, a.clone()),
        (
            bag([hash(a.clone()), hash(a.clone()), a.clone(), b.clone()]),
            bag([a, b]),
        ),
    ] {
        assert_eq!(native.reduce(&input).unwrap(), normal, "{input}");
        if let Some(oracle) = &oracle {
            assert_eq!(oracle.reduce(&input).unwrap(), normal, "{input}");
        }
    }
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn rejects_divergent_or_incomplete_subproduct_search() {
    let u = var("u");
    let k = var("k");
    let a = pub_term("a");
    let b = pub_term("b");
    let c = pub_term("c");
    let lhs = bag([pair(u.clone(), k.clone()), k.clone()]);
    let q = bag([pair(a.clone(), b.clone()), b.clone(), c.clone()]);
    let table = |rules| RuleTable::new(&signature(rules)).unwrap();
    let normal = table(vec![(lhs.clone(), u.clone())]);
    assert_eq!(
        normal.search_with_budget(&q, 100_000).unwrap(),
        Some(bag([a.clone(), c.clone()]))
    );
    assert_eq!(normal.search_with_budget(&q, 1).unwrap(), None);
    // A second normal endpoint in the same complement prevents commitment.
    let divergent = table(vec![(lhs.clone(), u.clone()), (lhs.clone(), k.clone())]);
    assert_eq!(divergent.reduce_native(&q).unwrap(), None);
    // The cycle must be noticed even when a normal exit also exists.
    let cyclic = table(vec![(lhs.clone(), u.clone()), (lhs.clone(), lhs.clone())]);
    assert_eq!(cyclic.search_reduction(&q).unwrap(), None);
    // A free rewrite can finish inside the untouched AC context.
    let mixed = table(vec![(lhs, fst(pair(u, k)))]);
    assert_eq!(mixed.search_reduction(&q).unwrap(), Some(bag([a, c])));
}

#[test]
fn native_oracle_idempotence_on_all_small_bags() {
    let x = var("x");
    let sig = signature([(bag([x.clone(), x.clone()]), x.clone())]);
    let native = MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        sig.clone(),
        AlgebraBackend::NativeOnly,
        Default::default(),
    )
    .unwrap();
    let oracle = tamarin_test_support::require_maude_path()
        .map(|path| MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap());
    let a = pub_term("a");
    let b = pub_term("b");
    let factors = [x.clone(), a, b, hash(x)];
    fn bags(factors: &[LNTerm], width: usize) -> Vec<Vec<LNTerm>> {
        if width == 0 {
            return vec![vec![]];
        }
        let mut rows = Vec::new();
        for (i, factor) in factors.iter().enumerate() {
            for mut row in bags(&factors[i..], width - 1) {
                row.push(factor.clone());
                rows.push(row);
            }
        }
        rows
    }
    let mut queries = 0;
    for width in 2..=5 {
        for mut terms in bags(&factors, width) {
            let input = f_app_ac(AcSym::Union, terms.clone());
            terms.dedup();
            let expected = f_app_ac(AcSym::Union, terms);
            assert_eq!(native.reduce(&input).unwrap(), expected, "{input}");
            if let Some(oracle) = &oracle {
                assert_eq!(oracle.reduce(&input).unwrap(), expected, "{input}");
            }
            queries += 1;
        }
    }
    assert_eq!(queries, 121);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_matching_with_extension_preserves_the_whole_remainder() {
    let u = var("rest");
    let k = var("k");
    let caller = Term::Lit(Lit::Var(LVar::new("rest", LSort::Msg, 1)));
    let sig = signature([(
        bag([pair(u.clone(), k.clone()), hash(k.clone())]),
        u.clone(),
    )]);
    let native = theory_session(&sig);
    let oracle = tamarin_test_support::require_maude_path().map(|path| {
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap()
    });
    let mut frame: Vec<_> = (0..9).map(|i| pub_term(format!("pad{i}"))).collect();
    frame.push(u);
    let mut input = frame.clone();
    input.extend([pair(caller.clone(), k.clone()), hash(k.clone())]);
    frame.push(caller);
    let expected = f_app_ac(AcSym::Union, frame);
    let q = f_app_ac(AcSym::Union, input.clone());
    assert_eq!(native.reduce(&q).unwrap(), expected);
    if let Some(oracle) = oracle {
        assert_eq!(oracle.reduce(&q).unwrap(), expected);
    }
    assert_eq!(native.stats().norm_count, 0);

    // Either pair can consume the only hash. Their complements give distinct
    // endpoints; selecting a single extension would lose that ambiguity.
    input.push(pair(pub_term("alternative"), k));
    let ambiguous = f_app_ac(AcSym::Union, input);
    assert_eq!(
        RuleTable::new(&sig)
            .unwrap()
            .search_reduction(&ambiguous)
            .unwrap(),
        None
    );
}

#[test]
fn wide_nat_subproduct_checks_the_sort_of_the_replacement() {
    use crate::function_symbols::nat_one_sym;
    use crate::maude_sig::nat_maude_sig;
    use crate::term::f_app_no_eq;

    let one = f_app_no_eq(nat_one_sym(), vec![]);
    let sum = |ts| f_app_ac(AcSym::NatPlus, ts);
    let lhs = sum(vec![one.clone(), one.clone()]);
    let table = |rhs: LNTerm| {
        signature([(lhs.clone(), rhs)])
            .merge(nat_maude_sig())
            .refresh()
    };
    let valid = table(one.clone());
    let native = theory_session(&valid);
    let mut operands: Vec<_> = (0..10)
        .map(|i| Term::Lit(Lit::Var(LVar::new("rest", LSort::Nat, i))))
        .collect();
    operands.push(one.clone());
    let expected = sum(operands.clone());
    operands.push(one.clone());
    let term = sum(operands);
    assert_eq!(native.reduce(&term).unwrap(), expected);
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, valid, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&term).unwrap(), expected);
    }
    let invalid = table(hash(one));
    assert_eq!(
        RuleTable::new(&invalid)
            .unwrap()
            .search_reduction(&term)
            .unwrap(),
        None
    );
}

#[test]
fn interleaves_rewrites_below_inert_constructors_with_root_steps() {
    let u = var("u");
    let repeat = |t: LNTerm| bag([t.clone(), t]);
    let a = pub_term("a");
    let inner = repeat(a.clone());
    let subject = bag([hash(inner.clone()), hash(hash(a.clone()))]);
    let competing = bag([hash(repeat(u.clone())), hash(hash(u.clone()))]);
    let sig = signature([(repeat(u.clone()), u.clone()), (competing, u.clone())]);
    let ambiguous = RuleTable::new(&sig).unwrap();
    let steps = ambiguous
        .successors(&subject, &mut 100_000)
        .unwrap()
        .unwrap();
    assert!(steps.contains(&a));
    assert!(steps.contains(&bag([hash(a.clone()), hash(hash(a.clone()))])));
    assert_eq!(ambiguous.reduce_native(&subject).unwrap(), None);

    // With only idempotence, parent and child rewrites can happen in either
    // order and both paths preserve the same protected residual factors.
    let sig = signature([(repeat(u.clone()), u)]);
    let input = bag([a.clone(), a.clone(), hash(bag([inner, pub_term("b")]))]);
    let expected = bag([a.clone(), hash(bag([a, pub_term("b")]))]);
    assert_eq!(
        RuleTable::new(&sig).unwrap().reduce_native(&input).unwrap(),
        Some(expected.clone())
    );
    if let Some(path) = tamarin_test_support::require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(oracle.reduce(&input).unwrap(), expected);
    }
}

#[test]
fn native_oracle_free_commutative_and_ac_rewrites_reach_one_endpoint() {
    use crate::builtin::{emap, exp, mult, one_const, pmult};
    use crate::maude_sig::bp_maude_sig;
    let u = var("u");
    let k = var("k");
    // Both free-root rules are applicable. The first needs a C-root rewrite
    // to reach the second one's result; the enclosed user AC can change too.
    let lhs = hash(pair(u.clone(), k.clone()));
    let sig = signature([
        (bag([u.clone(), u.clone()]), u.clone()),
        (lhs.clone(), emap(pmult(u.clone(), k.clone()), k.clone())),
        (lhs, exp(emap(k.clone(), k.clone()), u.clone())),
    ])
    .merge(bp_maude_sig());
    let a = pub_term("a");
    let b = pub_term("b");
    let native = theory_session(&sig);
    let oracle = tamarin_test_support::require_maude_path()
        .map(|path| MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap());
    for (input, normal) in [
        (
            hash(pair(bag([a.clone(), a.clone()]), b.clone())),
            exp(emap(b.clone(), b.clone()), a.clone()),
        ),
        (
            emap(pmult(u.clone(), a.clone()), pmult(k.clone(), b.clone())),
            exp(emap(a.clone(), b.clone()), mult(u.clone(), k.clone())),
        ),
    ] {
        assert_eq!(native.reduce(&input).unwrap(), normal, "{input}");
        if let Some(oracle) = &oracle {
            assert_eq!(oracle.reduce(&input).unwrap(), normal, "{input}");
        }
    }
    // Point multiplication may peel on either side of the commutative
    // map, and nested scalars may collapse before or after that step.
    let towers = |point: &LNTerm| {
        [
            (point.clone(), vec![]),
            (pmult(one_const(), point.clone()), vec![]),
            (pmult(u.clone(), point.clone()), vec![u.clone()]),
            (
                pmult(k.clone(), pmult(u.clone(), point.clone())),
                vec![k.clone(), u.clone()],
            ),
        ]
    };
    for (left, left_exponents) in towers(&a) {
        for (right, mut exponents) in towers(&b) {
            let input = emap(left.clone(), right);
            exponents.extend(left_exponents.iter().cloned());
            let base = emap(a.clone(), b.clone());
            let normal = if exponents.is_empty() {
                base
            } else {
                exp(base, f_app_ac(AcSym::Mult, exponents))
            };
            assert_eq!(native.reduce(&input).unwrap(), normal, "{input}");
            if let Some(oracle) = &oracle {
                assert_eq!(oracle.reduce(&input).unwrap(), normal, "{input}");
            }
        }
    }
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn distinguishes_ambiguity_of_a_child_from_ambiguity_of_the_whole() {
    use crate::builtin::{emap, true_const, true_sym};
    use crate::maude_sig::bp_maude_sig;
    let u = var("u");
    let k = var("k");
    let pick = hash(pair(u.clone(), k.clone()));
    let both = emap(hash(u.clone()), hash(k.clone()));
    let mut sig = signature([
        (pick.clone(), u.clone()),
        (pick, k.clone()),
        // A C match may select either operand for u.
        (both, u.clone()),
        // A rewriting parent can erase its child's ambiguity.
        (hash(hash(u.clone())), true_const()),
        (hash(u), true_const()),
    ])
    .merge(bp_maude_sig());
    sig.st_fun_syms.insert(true_sym());
    let sig = sig.refresh();
    let table = RuleTable::new(&sig).unwrap();
    let a = pub_term("a");
    let b = pub_term("b");
    assert_eq!(
        table
            .reduce_native(&emap(hash(a.clone()), hash(b.clone())))
            .unwrap(),
        None
    );
    assert_eq!(
        table
            .reduce_native(&hash(pair(a.clone(), b.clone())))
            .unwrap(),
        None
    );
    // All child values become arguments to the outer hash rule.
    assert_eq!(
        table.reduce_native(&hash(hash(pair(a, b)))).unwrap(),
        Some(true_const())
    );
}

#[test]
fn rejects_incomplete_buckets_for_free_and_commutative_heads() {
    use crate::builtin::emap;
    use crate::maude_sig::bp_maude_sig;
    let u = var("u");
    let k = var("k");
    let a = pub_term("a");
    let sig = signature([
        (hash(u.clone()), u.clone()),
        (hash(a.clone()), a.clone()),
        (emap(u.clone(), u.clone()), u),
        (emap(a.clone(), k.clone()), k),
    ])
    .merge(bp_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    // Literal name identities are local to Maude's rule and query encodings.
    // One such rule makes the entire ordinary bucket uninterpretable.
    for input in [hash(a.clone()), emap(a.clone(), a)] {
        assert_eq!(table.search_reduction(&input).unwrap(), None);
    }
}

#[test]
fn commutative_rule_can_have_distinct_normal_images_on_its_two_orientations() {
    use crate::builtin::emap;
    use crate::maude_sig::bp_maude_sig;
    let u = var("u");
    let k = var("k");
    let sig = signature([(emap(hash(u.clone()), hash(k)), u)]).merge(bp_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let a = pub_term("a");
    let b = pub_term("b");
    assert_eq!(
        table
            .reduce_native(&emap(hash(a.clone()), hash(b)))
            .unwrap(),
        None
    );
    assert_eq!(
        table
            .reduce_native(&emap(hash(a.clone()), hash(a.clone())))
            .unwrap(),
        Some(a)
    );
}

#[test]
fn linked_postorder_graph_checks_all_edges_and_terminals() {
    for (rows, accepted) in [
        (vec![], false),
        (vec![vec![]], true),
        (vec![vec![], vec![0], vec![0], vec![1, 2]], true),
        (vec![vec![], vec![0, 0]], true),
        (vec![vec![], vec![], vec![0, 1]], false),
        (vec![vec![], vec![1, 0]], false),
        (vec![vec![], vec![u64::MAX]], false),
        (vec![vec![9]], false),
    ] {
        assert_eq!(certified_graph(&rows).unwrap(), accepted, "{rows:?}");
    }
}
