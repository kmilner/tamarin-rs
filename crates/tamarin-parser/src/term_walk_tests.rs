use super::*;
use crate::ast::{BinOp, VarSpec};
use tamarin_term::lterm::LSort;

#[test]
fn equality_distinguishes_shallow_fields_and_child_order() {
    // Independent recursive reference, used only on small trees.
    fn equal(a: &Term, b: &Term) -> bool {
        let list = |xs: &[Term], ys: &[Term]| {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| equal(x, y))
        };
        match (a, b) {
            (Term::Var(x), Term::Var(y)) => x == y,
            (Term::PubLit(x), Term::PubLit(y))
            | (Term::FreshLit(x), Term::FreshLit(y))
            | (Term::NatLit(x), Term::NatLit(y)) => x == y,
            (Term::Number(x), Term::Number(y)) => x == y,
            (Term::NumberOne, Term::NumberOne)
            | (Term::NatOne, Term::NatOne)
            | (Term::DhNeutral, Term::DhNeutral) => true,
            (Term::App(f, xs), Term::App(g, ys)) => f == g && list(xs, ys),
            (Term::Pair(xs), Term::Pair(ys)) => list(xs, ys),
            (Term::AlgApp(f, x, y), Term::AlgApp(g, u, v)) => f == g && equal(x, u) && equal(y, v),
            (Term::BinOp(f, x, y), Term::BinOp(g, u, v)) => f == g && equal(x, u) && equal(y, v),
            (Term::Diff(x, y), Term::Diff(u, v)) => equal(x, u) && equal(y, v),
            (Term::PatMatch(x), Term::PatMatch(y)) => equal(x, y),
            _ => false,
        }
    }
    let mut terms = vec![Term::NumberOne, Term::NatOne, Term::DhNeutral];
    for i in 0..2 {
        terms.extend([
            Term::Var(VarSpec {
                name: format!("x{i}"),
                idx: i,
                sort: LSort::Msg,
                typ: None,
            }),
            Term::Number(i),
            Term::PubLit(i.to_string()),
            Term::FreshLit(i.to_string()),
            Term::NatLit(i.to_string()),
        ]);
    }
    for i in 0..3 {
        let a = terms[i].clone();
        let b = terms[i + 1].clone();
        for name in ["f", "g"] {
            for args in [
                vec![],
                vec![a.clone()],
                vec![a.clone(), b.clone()],
                vec![b.clone(), a.clone()],
            ] {
                terms.push(Term::App(name.into(), args.clone()));
                terms.push(Term::Pair(args));
            }
            terms.push(Term::AlgApp(
                name.into(),
                Box::new(a.clone()),
                Box::new(b.clone()),
            ));
        }
        for op in [BinOp::Exp, BinOp::Mult] {
            terms.push(Term::BinOp(op, Box::new(a.clone()), Box::new(b.clone())));
        }
        terms.push(Term::Diff(Box::new(a.clone()), Box::new(b)));
        terms.push(Term::PatMatch(Box::new(a)));
    }
    for a in &terms {
        for b in &terms {
            assert_eq!(a == b, equal(a, b));
        }
    }
}

#[test]
fn copy_preserves_every_term_shape_and_child_order() {
    let variable = Term::Var(VarSpec {
        name: "x".into(),
        idx: 3,
        sort: LSort::Msg,
        typ: Some("bytes".into()),
    });
    let term = Term::App(
        "f".into(),
        vec![
            variable,
            Term::PubLit("public".into()),
            Term::FreshLit("fresh".into()),
            Term::NatLit("natural".into()),
            Term::Number(42),
            Term::NumberOne,
            Term::NatOne,
            Term::DhNeutral,
            Term::AlgApp(
                "g".into(),
                Box::new(Term::Number(1)),
                Box::new(Term::Number(2)),
            ),
            Term::Pair(vec![Term::Number(3), Term::Number(4), Term::Number(5)]),
            Term::Diff(Box::new(Term::Number(6)), Box::new(Term::Number(7))),
            Term::BinOp(
                BinOp::Exp,
                Box::new(Term::Number(8)),
                Box::new(Term::Number(9)),
            ),
            Term::PatMatch(Box::new(Term::Number(10))),
            Term::Pair(vec![]),
            Term::App("empty".into(), vec![]),
        ],
    );
    assert_eq!(term.clone(), term);
    let mut numbers = Vec::new();
    term.visit(|t| {
        if let Term::Number(n) = t {
            numbers.push(*n);
        }
    });
    assert_eq!(numbers, [42, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    let mut mutated = term.clone();
    mutated.visit_mut(|t| {
        if let Term::Number(n) = t {
            *n = 99;
        }
        true
    });
    let mut numbers = Vec::new();
    mutated.visit(|t| {
        if let Term::Number(n) = t {
            numbers.push(*n);
        }
    });
    assert_eq!(numbers, [99; 11]);
}

#[test]
fn deep_term_lifecycle_uses_bounded_native_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut term = Term::Number(0);
        for i in 0..100_000 {
            term = match i % 5 {
                0 => Term::App("f".into(), vec![term]),
                1 => Term::Pair(vec![Term::Number(1), term]),
                2 => Term::Diff(Box::new(term), Box::new(Term::Number(2))),
                3 => Term::BinOp(BinOp::Exp, Box::new(Term::Number(3)), Box::new(term)),
                _ => Term::PatMatch(Box::new(term)),
            };
        }
        // An interrupted rewrite must also destroy the tree without
        // recursively unwinding its modified prefix.
        let mut visited = 0;
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut interrupted = term.clone();
            interrupted.visit_mut(|node| {
                visited += 1;
                assert!(visited < 50_000, "interrupted substitution");
                if let Term::Number(n) = node {
                    *n += 1;
                }
                true
            });
        }));
        assert!(failed.is_err());
        let mut copied = term.clone();
        assert!(copied == term);
        copied.visit_mut(|t| {
            if let Term::Number(n) = t {
                *n += 1;
            }
            true
        });
        assert!(copied != term);
        let mut replaced = term.clone();
        replaced.visit_mut(|t| {
            if matches!(t, Term::Number(0)) {
                *t = Term::Number(42);
                false
            } else {
                true
            }
        });
        drop(replaced);
        drop(copied);
        drop(term);
    });
}

#[test]
fn deep_term_debug_uses_guarded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut term = Term::NumberOne;
        for _ in 0..8192 {
            term = Term::PatMatch(Box::new(term));
        }
        assert!(format!("{term:?}").ends_with(&")".repeat(8192)));
        assert_eq!(format!("{term:#?}").matches("PatMatch(").count(), 8192);
    });
}

#[test]
fn replacement_subtrees_are_not_revisited() {
    let term = Term::App("f".into(), vec![Term::Number(1)]);
    let mut copied = term.clone();
    copied.visit_mut(|t| {
        if matches!(t, Term::Number(1)) {
            *t = term.clone();
            false
        } else {
            true
        }
    });
    assert_eq!(copied, Term::App("f".into(), vec![term]));
}
