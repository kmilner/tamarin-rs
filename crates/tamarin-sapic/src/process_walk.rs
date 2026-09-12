//! Preorder traversal for SAPIC transformation passes.

use tamarin_theory::sapic::Process;

/// Visit parents before children, left before right. State changes are
/// inherited by children, with independent copies at branch points.
/// A false return prunes the current subtree; callbacks may replace a node.
pub(crate) fn walk_mut<A, V, S: Clone, E>(
    p: &mut Process<A, V>,
    state: S,
    mut visit: impl FnMut(&mut Process<A, V>, &mut S) -> Result<bool, E>,
) -> Result<(), E> {
    let mut pending = vec![(p, state)];
    while let Some((p, mut state)) = pending.pop() {
        if !visit(p, &mut state)? {
            continue;
        }
        match p {
            Process::Null(_) => {}
            Process::Action(_, _, body) => pending.push((body, state)),
            Process::Comb(_, _, left, right) => {
                pending.push((right, state.clone()));
                pending.push((left, state));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::annotation::ProcessAnnotation;
    use tamarin_term::lterm::{LVar, Name, NameTag};
    use tamarin_term::vterm::const_term;
    use tamarin_theory::sapic::{ProcessCombinator, SapicAction, SapicLVar};

    type Proc = Process<ProcessAnnotation<LVar>, SapicLVar>;

    #[test]
    fn deep_annotation_and_lowering_pipeline_and_lock_error_cleanup() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let ann = ProcessAnnotation::empty;
                let term = const_term(Name::new(NameTag::Pub, "s"));
                let mut p: Proc = Process::Null(ann());
                for _ in 0..100_000 {
                    p = Process::Action(
                        SapicAction::ChOut {
                            chan: None,
                            msg: term.clone(),
                        },
                        ann(),
                        Box::new(p).into(),
                    );
                }
                p = crate::translate::propagate_names(p);
                p = crate::secret_channels::annotate_secret_channels(p);
                p = crate::let_destructors::translate_let_destr(&Default::default(), p);
                p = crate::locks::annotate_locks(p).unwrap();
                // The left branch succeeds, then the right branch fails below a
                // lock. All of the retained input must be released on this stack.
                let bad = Process::Action(
                    SapicAction::Lock(term),
                    ann(),
                    Box::new(Process::Action(
                        SapicAction::Rep,
                        ann(),
                        Box::new(Process::Null(ann())).into(),
                    ))
                    .into(),
                );
                let tree = Process::Comb(
                    ProcessCombinator::Parallel,
                    ann(),
                    Box::new(p).into(),
                    Box::new(bad).into(),
                );
                assert!(crate::locks::annotate_locks(tree)
                    .unwrap_err()
                    .contains("replication"));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn walk_inherits_state_and_restores_sibling_scope() {
        let ann = ProcessAnnotation::empty;
        let mut p: Proc = Process::Comb(
            ProcessCombinator::Parallel,
            ann(),
            Box::new(Process::Action(
                SapicAction::Rep,
                ann(),
                Box::new(Process::Null(ann())).into(),
            ))
            .into(),
            Box::new(Process::Null(ann())).into(),
        );
        let mut seen = Vec::new();
        walk_mut(&mut p, 0, |_, depth| {
            seen.push(*depth);
            *depth += 1;
            Ok::<_, std::convert::Infallible>(true)
        })
        .unwrap();
        assert_eq!(seen, [0, 1, 2, 1]);
    }
}
