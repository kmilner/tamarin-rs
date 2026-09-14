// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.Locks` (`lib/sapic/src/Sapic/Locks.hs`) — the lock-annotation
//! pass.
//!
//! `annotateLocks` (Locks.hs:94-99) assigns each `lock` a fresh lock variable
//! (`freshLVar "lock" LSortMsg`, minted from a SINGLE fast fresh counter that
//! starts at 0 — `evalFreshT a 0`, Locks.hs:94-99, see line 99) and, via
//! `annotateEachClosestUnlock` (Locks.hs:34-59), matches that lock variable onto
//! each closest enclosing-scope `unlock` (and `insert`/`lookup`) that shares the
//! lock's term.
//!
//! The pass runs LAST in the annotation pipeline (sapic/src/Sapic.hs:55-61), after
//! `propagateNames` / `annotateSecretChannels` / `annotatePureStates`.
//!
//! NOTE on the fresh counter: HS `annotateLocks` runs in the *Fast* `FreshT`
//! monad (`evalFreshT a 0`), where `freshIdent _name = freshIdents 1` ignores the
//! name and returns the global counter (0, 1, 2, ...).  So the first lock gets
//! index 0 (`lock`), the second index 1 (`lock.1`), etc.  This counter is
//! independent of the per-name `renameUnique` counter.

use tamarin_utils::fresh::{FastFreshState, MonadFresh};

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::sapic::{Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm};

use crate::annotation::ProcessAnnotation;

type AnnotatedProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// `LocalException` (Locks.hs:28-28): thrown when `annotateEachClosestUnlock`
/// encounters a `Rep` (`WFRep`) or `Parallel` (`WFPar`) below a lock.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LockWfError {
    /// `WFRep` — replication below the lock.
    Rep,
    /// `WFPar` — parallel below the lock.
    Par,
}

/// `annotateEachClosestUnlock t v p` (Locks.hs:34-59): annotate the closest
/// occurrence of `unlock` (and `insert t _` / `lookup t _`) that has term `t`
/// with the variable `v`.  Errors on `Rep`/`Parallel` below the lock.
#[cfg(test)]
fn annotate_each_closest_unlock(
    t: &SapicTerm,
    v: &LVar,
    p: &mut AnnotatedProc,
) -> Result<(), LockWfError> {
    crate::process_walk::walk_mut(p, (), |node, _| {
        match node {
            Process::Action(ac, ann, _) => match ac {
                SapicAction::Unlock(other) if t == other => {
                    *ann = std::mem::take(ann).append(ProcessAnnotation::with_unlock(*v));
                    return Ok(false);
                }
                SapicAction::Insert(other, _) if t == other => {
                    *ann = std::mem::take(ann).append(ProcessAnnotation::with_unlock(*v));
                }
                SapicAction::Rep => return Err(LockWfError::Rep),
                _ => {}
            },
            Process::Comb(ProcessCombinator::Parallel, _, _, _) => return Err(LockWfError::Par),
            Process::Comb(ProcessCombinator::Lookup(other, _), ann, _, _) if t == other => {
                *ann = std::mem::take(ann).append(ProcessAnnotation::with_unlock(*v));
            }
            _ => {}
        }
        Ok(true)
    })
}

#[derive(Clone, Copy)]
struct LockBinding {
    // An outer scan runs before every inner scan, but the innermost matching
    // lock supplies the final annotation. Both orders matter.
    oldest: usize,
    latest: LVar,
}

#[derive(Default)]
struct ActiveLocks {
    terms: std::collections::BTreeMap<SapicTerm, LockBinding>,
    order: std::collections::BTreeSet<usize>,
    undo: Vec<(SapicTerm, Option<LockBinding>)>,
    checkpoints: usize,
}

impl ActiveLocks {
    fn replace(&mut self, term: SapicTerm, binding: Option<LockBinding>) -> Option<LockBinding> {
        let previous = match binding {
            Some(binding) => self.terms.insert(term, binding),
            None => self.terms.remove(&term),
        };
        if let Some(previous) = previous {
            self.order.remove(&previous.oldest);
        }
        if let Some(binding) = binding {
            self.order.insert(binding.oldest);
        }
        previous
    }

    fn set(&mut self, term: &SapicTerm, binding: Option<LockBinding>) {
        let previous = self.replace(term.clone(), binding);
        // Straight-line prefixes never need restoration. Retain history only
        // while a pending sibling can still observe the old scope.
        if self.checkpoints != 0 {
            self.undo.push((term.clone(), previous));
        }
    }

    fn restore(&mut self, len: usize) {
        while self.undo.len() > len {
            let (term, binding) = self.undo.pop().unwrap();
            self.replace(term, binding);
        }
    }
}

/// Annotate in one DFS, restoring the active lock scope at branch boundaries.
fn annotate_locks_go(
    fresh: &mut FastFreshState,
    mut p: AnnotatedProc,
) -> Result<AnnotatedProc, LockWfError> {
    enum Work<'a> {
        Visit(&'a mut AnnotatedProc),
        Restore(usize, bool),
    }
    let mut scope = ActiveLocks::default();
    let mut pending = vec![Work::Visit(&mut p)];
    let mut next_lock = 0;
    let mut error: Option<(usize, LockWfError)> = None;
    while let Some(work) = pending.pop() {
        let node = match work {
            Work::Restore(len, finished) => {
                scope.restore(len);
                if finished {
                    scope.checkpoints -= 1;
                }
                continue;
            }
            Work::Visit(node) => node,
        };
        // Once a lock has failed, only an earlier lock's pending branch can
        // take precedence. New locks in this subtree would all come later.
        if let Some((failed, _)) = &error
            && scope.order.first().is_none_or(|active| active >= failed)
        {
            continue;
        }
        let failure = match node {
            Process::Action(SapicAction::Rep, _, _) => Some(LockWfError::Rep),
            Process::Comb(ProcessCombinator::Parallel, _, _, _) => Some(LockWfError::Par),
            _ => None,
        };
        if let Some(failure) = failure
            && let Some(&oldest) = scope.order.first()
        {
            // DFS gives the first error for this lock. Keep the earliest lock
            // overall, matching the old outer-scan-before-inner-scan policy.
            error = Some((oldest, failure));
            continue;
        }
        match node {
            Process::Null(_) => {}
            Process::Action(ac, ann, body) => {
                match ac {
                    SapicAction::Lock(term) => {
                        let v = LVar {
                            name: "lock",
                            sort: LSort::Msg,
                            idx: fresh.fresh_ident(""),
                        };
                        let oldest = scope
                            .terms
                            .get(term)
                            .map_or(next_lock, |binding| binding.oldest);
                        next_lock += 1;
                        scope.set(term, Some(LockBinding { oldest, latest: v }));
                        *ann = std::mem::take(ann).append(ProcessAnnotation::with_lock(v));
                    }
                    SapicAction::Unlock(term) | SapicAction::Insert(term, _) => {
                        if let Some(binding) = scope.terms.get(term).copied() {
                            *ann = std::mem::take(ann)
                                .append(ProcessAnnotation::with_unlock(binding.latest));
                            if matches!(ac, SapicAction::Unlock(_)) {
                                let SapicAction::Unlock(term) = ac else {
                                    unreachable!()
                                };
                                // One unlock terminates every same-term outer scan.
                                scope.set(term, None);
                            }
                        }
                    }
                    _ => {}
                }
                pending.push(Work::Visit(body));
            }
            Process::Comb(comb, ann, left, right) => {
                if let ProcessCombinator::Lookup(term, _) = comb
                    && let Some(binding) = scope.terms.get(term)
                {
                    *ann =
                        std::mem::take(ann).append(ProcessAnnotation::with_unlock(binding.latest));
                }
                let checkpoint = scope.undo.len();
                scope.checkpoints += 1;
                pending.push(Work::Restore(checkpoint, true));
                pending.push(Work::Visit(right));
                pending.push(Work::Restore(checkpoint, false));
                pending.push(Work::Visit(left));
            }
        }
    }
    match error {
        Some((_, error)) => Err(error),
        None => Ok(p),
    }
}

/// `annotateLocks` (Locks.hs:94-99): run `annotateLocks'` with the fresh counter
/// seeded at 0.  On a wellformedness error (`Rep`/`Parallel` below a lock), HS
/// `throwM`s a `ProcessNotWellformed (WFLock tag)`; we surface it as an `Err`.
pub(crate) fn annotate_locks(p: AnnotatedProc) -> Result<AnnotatedProc, String> {
    let mut fresh = FastFreshState::nothing_used();
    annotate_locks_go(&mut fresh, p).map_err(|e| match e {
        LockWfError::Rep => {
            "process not well-formed: replication below a lock without a matching unlock"
                .to_string()
        }
        LockWfError::Par => {
            "process not well-formed: parallel below a lock without a matching unlock".to_string()
        }
    })
}

#[cfg(test)]
#[path = "locks_tests.rs"]
mod tests;
