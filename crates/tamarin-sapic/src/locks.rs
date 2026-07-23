// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, arcz, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic.hs, lib/sapic/src/Sapic/Locks.hs

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
//! The pass runs LAST in the annotation pipeline (Sapic.hs:55-61), after
//! `propagateNames` / `annotateSecretChannels` / `annotatePureStates`.
//!
//! NOTE on the fresh counter: HS `annotateLocks` runs in the *Fast* `FreshT`
//! monad (`evalFreshT a 0`), where `freshIdent _name = freshIdents 1` ignores the
//! name and returns the global counter (0, 1, 2, ...).  So the first lock gets
//! index 0 (`lock`), the second index 1 (`lock.1`), etc.  This counter is
//! independent of the per-name `renameUnique` counter.

use tamarin_utils::fresh::FastFreshState;

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::sapic::{Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm};

use crate::annotation::ProcessAnnotation;

type AnnotatedProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// `LocalException` (Locks.hs:28-28): thrown when `annotateEachClosestUnlock`
/// encounters a `Rep` (`WFRep`) or `Parallel` (`WFPar`) below a lock.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LockWfError {
    /// `WFRep` — replication below the lock.
    Rep,
    /// `WFPar` — parallel below the lock.
    Par,
}

/// `annotateEachClosestUnlock t v p` (Locks.hs:34-59): annotate the closest
/// occurrence of `unlock` (and `insert t _` / `lookup t _`) that has term `t`
/// with the variable `v`.  Errors on `Rep`/`Parallel` below the lock.
fn annotate_each_closest_unlock(
    t: &SapicTerm,
    v: &LVar,
    p: AnnotatedProc,
) -> Result<AnnotatedProc, LockWfError> {
    match p {
        // ProcessNull a' -> return $ ProcessNull a'
        Process::Null(a) => Ok(Process::Null(a)),
        Process::Action(ac, a, body) => match &ac {
            // (Unlock t') | t == t' -> annUnlock here, STOP (closest match).
            //              | otherwise -> recurse into body.
            SapicAction::Unlock(t_prime) if t == t_prime => {
                let a2 = a.append(ProcessAnnotation::with_unlock(v.clone()));
                Ok(Process::Action(ac, a2, body))
            }
            // (Insert t1 t2) | t1 == t -> annUnlock here AND recurse into body.
            //  (otherwise falls through to the generic action case below.)
            SapicAction::Insert(t1, _t2) if t1 == t => {
                let body2 = annotate_each_closest_unlock(t, v, *body)?;
                let a2 = a.append(ProcessAnnotation::with_unlock(v.clone()));
                Ok(Process::Action(ac, a2, Box::new(body2)))
            }
            // (Rep) -> Left WFRep
            SapicAction::Rep => Err(LockWfError::Rep),
            // generic action: recurse into body.
            _ => {
                let body2 = annotate_each_closest_unlock(t, v, *body)?;
                Ok(Process::Action(ac, a, Box::new(body2)))
            }
        },
        // (ProcessComb Parallel _ _ _) -> Left WFPar
        Process::Comb(ProcessCombinator::Parallel, _, _, _) => Err(LockWfError::Par),
        Process::Comb(c, a, pl, pr) => match &c {
            // (Lookup st vt) | st == t -> annUnlock here AND recurse into BOTH children.
            ProcessCombinator::Lookup(st, _vt) if st == t => {
                let pl2 = annotate_each_closest_unlock(t, v, *pl)?;
                let pr2 = annotate_each_closest_unlock(t, v, *pr)?;
                let a2 = a.append(ProcessAnnotation::with_unlock(v.clone()));
                Ok(Process::Comb(c, a2, Box::new(pl2), Box::new(pr2)))
            }
            // generic combinator: recurse into both children (no annotation).
            _ => {
                let pl2 = annotate_each_closest_unlock(t, v, *pl)?;
                let pr2 = annotate_each_closest_unlock(t, v, *pr)?;
                Ok(Process::Comb(c, a, Box::new(pl2), Box::new(pr2)))
            }
        },
    }
}

/// `annotateLocks'` (Locks.hs:74-91): at each `Lock t`, mint a fresh lock
/// variable, annotate the closest matching unlocks under it, then recurse.
fn annotate_locks_go(
    fresh: &mut FastFreshState,
    p: AnnotatedProc,
) -> Result<AnnotatedProc, LockWfError> {
    match p {
        // (Lock t) -> fresh v; annotateEachClosestUnlock t v body; recurse; annLock here.
        Process::Action(SapicAction::Lock(t), a, body) => {
            // freshLVar "lock" LSortMsg — fast counter, name ignored.
            let v = LVar {
                name: "lock",
                sort: LSort::Msg,
                idx: fresh.fresh_ident(),
            };
            let p1 = annotate_each_closest_unlock(&t, &v, *body)?;
            let p2 = annotate_locks_go(fresh, p1)?;
            let a2 = a.append(ProcessAnnotation::with_lock(v));
            Ok(Process::Action(SapicAction::Lock(t), a2, Box::new(p2)))
        }
        // (ProcessAction ac an p) -> recurse into body.
        Process::Action(ac, an, body) => {
            let p1 = annotate_locks_go(fresh, *body)?;
            Ok(Process::Action(ac, an, Box::new(p1)))
        }
        // (ProcessNull an) -> return as-is.
        Process::Null(an) => Ok(Process::Null(an)),
        // (ProcessComb comb an pl pr) -> recurse into both children.
        Process::Comb(comb, an, pl, pr) => {
            let pl2 = annotate_locks_go(fresh, *pl)?;
            let pr2 = annotate_locks_go(fresh, *pr)?;
            Ok(Process::Comb(comb, an, Box::new(pl2), Box::new(pr2)))
        }
    }
}

/// `annotateLocks` (Locks.hs:94-99): run `annotateLocks'` with the fresh counter
/// seeded at 0.  On a wellformedness error (`Rep`/`Parallel` below a lock), HS
/// `throwM`s a `ProcessNotWellformed (WFLock tag)`; we surface it as an `Err`.
pub fn annotate_locks(p: AnnotatedProc) -> Result<AnnotatedProc, String> {
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
mod tests {
    use super::*;
    use tamarin_term::lterm::{Name, NameTag};
    use tamarin_term::vterm::const_term;

    fn pub_const(s: &str) -> SapicTerm {
        const_term(Name::new(NameTag::Pub, s))
    }

    fn null() -> AnnotatedProc {
        Process::Null(ProcessAnnotation::empty())
    }

    fn lock(t: SapicTerm, body: AnnotatedProc) -> AnnotatedProc {
        Process::Action(
            SapicAction::Lock(t),
            ProcessAnnotation::empty(),
            Box::new(body),
        )
    }
    fn unlock(t: SapicTerm, body: AnnotatedProc) -> AnnotatedProc {
        Process::Action(
            SapicAction::Unlock(t),
            ProcessAnnotation::empty(),
            Box::new(body),
        )
    }

    #[test]
    fn lock_gets_index_zero_and_matches_unlock() {
        // lock 's'; unlock 's'; 0
        let p = lock(pub_const("s"), unlock(pub_const("s"), null()));
        let out = annotate_locks(p).unwrap();
        // The lock annotation carries `lock` with idx 0.
        if let Process::Action(SapicAction::Lock(_), a, body) = out {
            let lv = a.lock.expect("lock annotated");
            assert_eq!(lv.0.name, "lock");
            assert_eq!(lv.0.idx, 0);
            assert_eq!(lv.0.sort, LSort::Msg);
            // ...and the matching unlock carries the SAME lock variable as unlock.
            if let Process::Action(SapicAction::Unlock(_), ua, _) = *body {
                let uv = ua.unlock.expect("unlock annotated");
                assert_eq!(uv.0.idx, 0);
            } else {
                panic!("expected unlock under lock");
            }
        } else {
            panic!("expected lock action");
        }
    }

    #[test]
    fn two_locks_get_indices_zero_and_one() {
        // lock 'a'; unlock 'a'; lock 'b'; unlock 'b'; 0
        let p = lock(
            pub_const("a"),
            unlock(
                pub_const("a"),
                lock(pub_const("b"), unlock(pub_const("b"), null())),
            ),
        );
        let out = annotate_locks(p).unwrap();
        // outer lock idx 0
        let Process::Action(SapicAction::Lock(_), a0, body0) = out else {
            panic!()
        };
        assert_eq!(a0.lock.unwrap().0.idx, 0);
        // the inner lock gets idx 1
        let Process::Action(SapicAction::Unlock(_), _, body1) = *body0 else {
            panic!()
        };
        let Process::Action(SapicAction::Lock(_), a1, _) = *body1 else {
            panic!()
        };
        assert_eq!(a1.lock.unwrap().0.idx, 1);
    }

    #[test]
    fn insert_matching_term_annotated_as_unlock() {
        // lock 's'; insert 's','v'; 0 — Insert with t1 == lock term is annotated
        // as an unlock (HS Locks.hs:45-48) AND recursion continues into the body.
        let p = lock(
            pub_const("s"),
            Process::Action(
                SapicAction::Insert(pub_const("s"), pub_const("v")),
                ProcessAnnotation::empty(),
                Box::new(null()),
            ),
        );
        let out = annotate_locks(p).unwrap();
        let Process::Action(SapicAction::Lock(_), _, body) = out else {
            panic!()
        };
        let Process::Action(SapicAction::Insert(_, _), ia, _) = *body else {
            panic!()
        };
        assert_eq!(ia.unlock.expect("insert annotated as unlock").0.idx, 0);
    }

    #[test]
    fn parallel_below_lock_errors() {
        // lock 's'; ( 0 | 0 )  — WFPar
        let par = Process::Comb(
            ProcessCombinator::Parallel,
            ProcessAnnotation::empty(),
            Box::new(null()),
            Box::new(null()),
        );
        let p = lock(pub_const("s"), par);
        assert!(annotate_locks(p).is_err());
    }

    #[test]
    fn unmatched_term_unlock_not_annotated() {
        // lock 's'; unlock 'other'; 0 — different term, unlock NOT annotated,
        // recursion continues into body.
        let p = lock(pub_const("s"), unlock(pub_const("other"), null()));
        let out = annotate_locks(p).unwrap();
        let Process::Action(SapicAction::Lock(_), _, body) = out else {
            panic!()
        };
        let Process::Action(SapicAction::Unlock(_), ua, _) = *body else {
            panic!()
        };
        assert!(ua.unlock.is_none());
    }
}
