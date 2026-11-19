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
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
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
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
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
        normal.ac_reduction_search(&q, 100_000).unwrap(),
        Some(bag([a, c]))
    );
    assert_eq!(normal.ac_reduction_search(&q, 1).unwrap(), None);
    // A second normal endpoint in the same complement prevents commitment.
    let divergent = table(vec![(lhs.clone(), u.clone()), (lhs.clone(), k.clone())]);
    assert_eq!(divergent.reduce_native(&q).unwrap(), None);
    // The cycle must be noticed even when a normal exit also exists.
    let cyclic = table(vec![(lhs.clone(), u.clone()), (lhs.clone(), lhs.clone())]);
    assert_eq!(cyclic.ac_root_reduce(&q).unwrap(), None);
    // A rule can introduce a reducible factor under the untouched context.
    let unknown = table(vec![(lhs, fst(pair(u, k)))]);
    assert_eq!(unknown.ac_root_reduce(&q).unwrap(), None);
}

#[test]
fn native_oracle_idempotence_on_all_small_bags() {
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let x = var("x");
    let sig = signature([(bag([x.clone(), x.clone()]), x.clone())]);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
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
    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let u = var("rest");
    let k = var("k");
    let caller = Term::Lit(Lit::Var(LVar::new("rest", LSort::Msg, 1)));
    let sig = signature([(
        bag([pair(u.clone(), k.clone()), hash(k.clone())]),
        u.clone(),
    )]);
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
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
            .ac_root_reduce(&ambiguous)
            .unwrap(),
        None
    );
}

#[test]
fn wide_nat_subproduct_checks_the_sort_of_the_replacement() {
    use crate::function_symbols::nat_one_sym;
    use crate::maude_sig::nat_maude_sig;
    use crate::term::f_app_no_eq;

    if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
        return;
    }
    let one = f_app_no_eq(nat_one_sym(), vec![]);
    let sum = |ts| f_app_ac(AcSym::NatPlus, ts);
    let lhs = sum(vec![one.clone(), one.clone()]);
    let table = |rhs: LNTerm| {
        signature([(lhs.clone(), rhs)])
            .merge(nat_maude_sig())
            .refresh()
    };
    let valid = table(one.clone());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", valid.clone(), AlgebraBackend::NativeOnly)
            .unwrap();
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
            .ac_root_reduce(&term)
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
