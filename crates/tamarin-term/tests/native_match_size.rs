#![cfg(feature = "lean-unification")]

use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::builtin::pair;
use tamarin_term::function_symbols::{AcSym, FunSym};
use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::maude_sig::{mset_maude_sig, pair_maude_sig};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::{f_app_ac, Term};
use tamarin_term::vterm::var_term;

fn handle() -> MaudeHandle {
    MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig().merge(pair_maude_sig()),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap()
}

fn forward(lhs: LNTerm, rhs: LNTerm) -> Equal<LNTerm> {
    Equal { lhs, rhs }
}

fn ordinary(equations: &[Equal<LNTerm>]) -> Vec<Equal<LNTerm>> {
    equations
        .iter()
        .map(|e| forward(e.rhs.clone(), e.lhs.clone()))
        .collect()
}

fn large_guard(factor: LNTerm, width: usize) -> LNTerm {
    pair(
        pub_term("left"),
        f_app_ac(AcSym::Union, vec![factor; width]),
    )
}

#[test]
fn checked_rigid_size_refutes_shared_and_open_conjunctions() {
    let h = handle();
    let x = LVar::new("x", LSort::Msg, 3);
    let y = LVar::new("y", LSort::Msg, 9);
    let atom = pub_term("c");
    // Each shared child contains four rigid operators/atoms. Expanding the
    // pattern exceeds the search ceiling, while the graph fits the reader.
    let leaf = |t| pair(atom.clone(), pair(t, atom.clone()));
    for rigid in [true, false] {
        let factor = leaf(if rigid { atom.clone() } else { var_term(y) });
        let mut eqs = vec![
            forward(
                large_guard(factor, 16_385),
                large_guard(leaf(var_term(y)), 33),
            ),
            forward(var_term(x), pair(var_term(y), var_term(y))),
        ];
        for _ in 0..2 {
            assert!(h.match_eqs(&ordinary(&eqs)).unwrap().is_empty());
            assert!(!h.has_match_eqs(&ordinary(&eqs)).unwrap());
            let vars = [(x.name, x.idx), (y.name, y.idx)].into_iter().collect();
            assert!(h.match_eqs_skolemize_both(&eqs, &vars).unwrap().is_empty());
            eqs.reverse();
        }
    }
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn size_refutation_requires_every_conjunct_to_be_declared_and_sorted() {
    let x = LVar::new("x", LSort::Msg, 3);
    let vars = [(x.name, x.idx)].into_iter().collect();
    let atom = pub_term("c");
    let leaf = pair(atom.clone(), pair(atom.clone(), atom.clone()));
    for malformed in [
        Term::App(FunSym::Ac(AcSym::Union), vec![].into()),
        Term::App(FunSym::Ac(AcSym::NatPlus), vec![atom.clone(); 2].into()),
    ] {
        let eqs = [
            forward(large_guard(leaf.clone(), 16_385), atom.clone()),
            forward(var_term(x), malformed),
        ];
        assert!(matches!(
            handle().match_eqs(&ordinary(&eqs)),
            Err(MaudeError::UnsupportedOperation(_))
        ));
        assert!(matches!(
            handle().match_eqs_skolemize_both(&eqs, &vars),
            Err(MaudeError::UnsupportedOperation(_))
        ));
    }
    // A Node inside a declared Msg constructor gives a kind-level term.
    // The total matcher still decides the original conjunction even when
    // the sorted size shortcut declines it.
    let kind = pair(var_term(LVar::new("n", LSort::Node, 7)), atom.clone());
    let eqs = [
        forward(large_guard(leaf, 16_385), atom),
        forward(var_term(x), kind),
    ];
    assert!(handle().match_eqs(&ordinary(&eqs)).unwrap().is_empty());
    assert!(handle()
        .match_eqs_skolemize_both(&eqs, &vars)
        .unwrap()
        .is_empty());
}

#[test]
fn raw_reassociation_and_shared_subject_variables_preserve_a_match() {
    let h = handle();
    let x = LVar::new("x", LSort::Msg, 1);
    let y = LVar::new("y", LSort::Msg, 2);
    let atom = pub_term("fixed");
    let repeated = pair(var_term(y), var_term(y));
    let raw = |args: Vec<_>| Term::App(FunSym::Ac(AcSym::Union), args.into());
    let eqs = [forward(
        raw(vec![atom.clone(), raw(vec![var_term(x), atom.clone()])]),
        raw(vec![atom.clone(), atom, repeated.clone()]),
    )];
    let expected = vec![vec![(x, repeated)]];
    assert_eq!(h.match_eqs(&ordinary(&eqs)).unwrap(), expected);
    assert_eq!(
        h.match_eqs_skolemize_both(&eqs, &[(x.name, x.idx)].into_iter().collect())
            .unwrap(),
        expected
    );
}
