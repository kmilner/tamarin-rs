use super::*;
use crate::ast::{Atom, Condition, Formula, ProcessComb, SapicAction, Term};

#[test]
fn process_clone_preserves_every_shape() {
    let process = Process::Comb {
        comb: ProcessComb::Cond(Condition::Formula(Formula::True)),
        left: Box::new(Process::Action {
            action: SapicAction::Delete(Term::Number(7)),
            body: Box::new(Process::Replication(Box::new(Process::Null))),
        }),
        right: Box::new(Process::AtAnnotation(
            Box::new(Process::Call {
                name: "P".into(),
                args: vec![Term::Number(9)],
            }),
            Term::Number(11),
        )),
    };
    assert_eq!(process.clone(), process);
}

#[test]
fn deep_branching_process_comparison_and_debug_use_bounded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut process = Process::Null;
        for _ in 0..8192 {
            process = Process::Comb {
                comb: ProcessComb::Parallel,
                left: Box::new(process),
                right: Box::new(Process::Null),
            };
        }
        let copy = process.clone();
        assert_eq!(process, copy);
        assert!(format!("{process:?}").starts_with("Comb {"));
        assert_eq!(format!("{process:#?}").matches("Comb {").count(), 8192);
    });
}

#[test]
fn deep_and_branching_process_lifecycles_use_bounded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut term = Term::NumberOne;
        for _ in 0..10_000 {
            term = Term::PatMatch(Box::new(term));
        }
        let mut formula = Formula::Atom(Atom::Eq(term, Term::NumberOne));
        for _ in 0..10_000 {
            formula = Formula::Not(Box::new(formula));
        }
        let mut process = Process::Comb {
            comb: ProcessComb::Cond(Condition::Formula(formula)),
            left: Box::new(Process::Null),
            right: Box::new(Process::Null),
        };
        for i in 0..100_000 {
            process = if i % 2 == 0 {
                Process::Replication(Box::new(process))
            } else {
                Process::Comb {
                    comb: ProcessComb::Parallel,
                    left: Box::new(Process::Null),
                    right: Box::new(process),
                }
            };
        }
        let copy = process.clone();
        drop((process, copy));

        let mut balanced = Process::Null;
        for _ in 0..14 {
            balanced = Process::Comb {
                comb: ProcessComb::Ndc,
                left: Box::new(balanced.clone()),
                right: Box::new(balanced),
            };
        }
        let copied = balanced.clone();
        assert_eq!(copied, balanced);
    });
}
