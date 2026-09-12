//! Bounded-stack cloning and destruction of surface processes.

use crate::ast::Process;

impl Process {
    #[inline]
    fn has_children(&self) -> bool {
        !matches!(self, Self::Null | Self::Call { .. })
    }

    #[inline]
    pub(crate) fn children(&self) -> impl DoubleEndedIterator<Item = &Self> {
        let children = match self {
            Self::Action { body, .. } | Self::Replication(body) | Self::AtAnnotation(body, _) => {
                [Some(body.as_ref()), None]
            }
            Self::Comb { left, right, .. } => [Some(left.as_ref()), Some(right.as_ref())],
            Self::Null | Self::Call { .. } => [None, None],
        };
        children.into_iter().flatten()
    }

    #[inline]
    fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Self> {
        let children = match self {
            Self::Action { body, .. } | Self::Replication(body) | Self::AtAnnotation(body, _) => {
                [Some(body.as_mut()), None]
            }
            Self::Comb { left, right, .. } => [Some(left.as_mut()), Some(right.as_mut())],
            Self::Null | Self::Call { .. } => [None, None],
        };
        children.into_iter().flatten()
    }

    #[inline]
    fn copy_shallow(&self) -> Self {
        match self {
            Self::Null => Self::Null,
            Self::Call { name, args } => Self::Call {
                name: name.clone(),
                args: args.clone(),
            },
            Self::Action { action, .. } => Self::Action {
                action: action.clone(),
                body: Box::new(Self::Null),
            },
            Self::Comb { comb, .. } => Self::Comb {
                comb: comb.clone(),
                left: Box::new(Self::Null),
                right: Box::new(Self::Null),
            },
            Self::Replication(_) => Self::Replication(Box::new(Self::Null)),
            Self::AtAnnotation(_, term) => Self::AtAnnotation(Box::new(Self::Null), term.clone()),
        }
    }

    // As for formulas, clear short batches in place, deferring deeper branches
    // to a heap worklist. The native call depth never depends on input depth.
    fn detach_children(&mut self, pending: &mut Vec<Self>, remaining: u8) {
        for child in self.children_mut() {
            if child.has_children() {
                if remaining == 0 {
                    pending.push(std::mem::replace(child, Self::Null));
                } else {
                    child.detach_children(pending, remaining - 1);
                    *child = Self::Null;
                }
            }
        }
    }

    fn drop_children(&mut self) {
        const BATCH_DEPTH: u8 = 8;
        let mut pending = Vec::new();
        self.detach_children(&mut pending, BATCH_DEPTH);
        while let Some(mut process) = pending.pop() {
            process.detach_children(&mut pending, BATCH_DEPTH);
        }
    }
}

impl Clone for Process {
    fn clone(&self) -> Self {
        let mut result = Self::Null;
        let mut pending = Vec::new();
        let mut next = Some((self, &mut result));
        while let Some((source, target)) = next.take().or_else(|| pending.pop()) {
            *target = source.copy_shallow();
            if source.children().all(|child| !child.has_children()) {
                for (source, target) in source.children().zip(target.children_mut()) {
                    *target = source.copy_shallow();
                }
                continue;
            }
            for pair in source.children().rev().zip(target.children_mut().rev()) {
                if let Some(previous) = next.replace(pair) {
                    pending.push(previous);
                }
            }
        }
        result
    }
}

impl Drop for Process {
    #[inline]
    fn drop(&mut self) {
        if self.has_children() && self.children().any(Self::has_children) {
            self.drop_children();
        }
    }
}

#[cfg(test)]
mod tests {
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
    fn deep_and_branching_process_lifecycles_use_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
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
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
