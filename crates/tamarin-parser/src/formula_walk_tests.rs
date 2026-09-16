use super::*;
use crate::ast::{Atom, Term, VarSpec};
use tamarin_term::lterm::LSort;

fn binder() -> VarSpec {
    VarSpec {
        name: "x".into(),
        idx: 0,
        sort: LSort::Msg,
        typ: None,
    }
}

#[test]
fn formula_clone_preserves_shapes_and_binder_depths() {
    let mut formula = Formula::Atom(Atom::Eq(Term::Number(1), Term::Number(2)));
    for i in 0..7 {
        formula = match i {
            0 => Formula::Not(Box::new(formula)),
            1 => Formula::And(Box::new(formula), Box::new(Formula::False)),
            2 => Formula::Or(Box::new(formula), Box::new(Formula::True)),
            3 => Formula::Implies(Box::new(Formula::False), Box::new(formula)),
            4 => Formula::Iff(Box::new(formula), Box::new(Formula::True)),
            5 => Formula::Forall(vec![binder(), binder()], Box::new(formula)),
            _ => Formula::Exists(vec![], Box::new(formula)),
        };
    }
    assert_eq!(formula.clone(), formula);
    let mut order = Vec::new();
    formula.visit(|f| {
        if let Formula::False = f {
            order.push(false);
        }
        if let Formula::True = f {
            order.push(true);
        }
    });
    assert_eq!(order, [false, false, true, true]);
}

#[test]
fn proof_clone_preserves_case_order_and_goals() {
    let parent = crate::parser::Parser::new("", &[], false);
    let proof = crate::proof_tree::parse_proof_tree(
        "induction case left solve( P(x) @ i ) by sorry next case right SOLVED qed",
        &parent,
    )
    .unwrap();
    assert_eq!(proof.clone(), proof);
}

#[test]
fn branching_formula_and_proof_lifecycles() {
    tamarin_test_support::on_stack(256 * 1024, || {
        // A full binary tree crosses the cleanup batch boundary with both
        // children still branching, unlike a spine with leaf siblings.
        let mut formula = Formula::True;
        let mut proof = ParsedProofTree {
            method: ParsedMethod::SolvedLeaf,
            cases: Vec::new(),
        };
        for _ in 0..14 {
            formula = Formula::And(Box::new(formula.clone()), Box::new(formula));
            proof = ParsedProofTree {
                method: ParsedMethod::Simplify,
                cases: vec![("left".into(), proof.clone()), ("right".into(), proof)],
            };
        }
        let mut copy = formula.clone();
        let mut leaves = 0;
        copy.visit_mut(|node| {
            if matches!(node, Formula::True) {
                leaves += 1;
                *node = Formula::False;
            }
            true
        });
        assert_eq!(leaves, 1 << 14);
        assert_eq!(proof.clone(), proof);
        drop((formula, copy, proof));

        let wide = ParsedProofTree {
            method: ParsedMethod::Induction,
            cases: (0..65_536)
                .map(|i| {
                    (
                        i.to_string(),
                        ParsedProofTree {
                            method: ParsedMethod::SolvedLeaf,
                            cases: Vec::new(),
                        },
                    )
                })
                .collect(),
        };
        let copied = wide.clone();
        assert_eq!(copied, wide);
    });
}

#[test]
fn deep_formula_and_proof_lifecycles_use_bounded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut term = Term::NumberOne;
        for _ in 0..10_000 {
            term = Term::PatMatch(Box::new(term));
        }
        let mut formula = Formula::Atom(Atom::Eq(term, Term::NumberOne));
        let mut proof = ParsedProofTree {
            method: ParsedMethod::SolvedLeaf,
            cases: Vec::new(),
        };
        for i in 0..100_000 {
            formula = if i % 2 == 0 {
                Formula::And(Box::new(Formula::False), Box::new(formula))
            } else {
                Formula::Forall(vec![binder()], Box::new(formula))
            };
            proof = ParsedProofTree {
                method: ParsedMethod::Simplify,
                cases: vec![(String::new(), proof)],
            };
        }
        let mut copied = formula.clone();
        copied.visit_mut(|f| {
            if matches!(f, Formula::False) {
                *f = Formula::True;
            }
            true
        });
        let proof = ParsedProofTree {
            method: ParsedMethod::Induction,
            cases: vec![("left".into(), proof.clone()), ("right".into(), proof)],
        };
        drop(proof.clone());
        drop(proof);
        drop(copied);
        drop(formula);
    });
}

#[test]
fn deep_formula_equality_uses_a_bounded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut equal_left = Formula::False;
        let mut unequal_left = Formula::True;
        for _ in 0..32768 {
            equal_left = Formula::And(Box::new(equal_left), Box::new(Formula::True));
            unequal_left = Formula::And(Box::new(unequal_left), Box::new(Formula::True));
        }
        let equal_right = equal_left.clone();
        assert_eq!(equal_left, equal_right);
        assert_ne!(equal_left, unequal_left);
    });
}

#[test]
fn deep_formula_debug_and_proof_traits_use_guarded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut formula = Formula::True;
        let mut proof = ParsedProofTree {
            method: ParsedMethod::SolvedLeaf,
            cases: Vec::new(),
        };
        for _ in 0..8192 {
            formula = Formula::Not(Box::new(formula));
            proof = ParsedProofTree {
                method: ParsedMethod::Simplify,
                cases: vec![(String::new(), proof)],
            };
        }
        assert_eq!(proof, proof.clone());
        assert!(format!("{formula:?}").starts_with("Not("));
        assert_eq!(format!("{formula:#?}").matches("Not(").count(), 8192);
        assert!(format!("{proof:?}").starts_with("ParsedProofTree {"));
        assert_eq!(
            format!("{proof:#?}").matches("ParsedProofTree {").count(),
            8193
        );
    });
}
