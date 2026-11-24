// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Sapic.Locks` (`lib/sapic/src/Sapic/Locks.hs`) — the lock-annotation
//! pass.
//!
//! `annotateLocks` (Locks.hs) assigns each `lock` a fresh lock variable
//! (`freshLVar "lock" LSortMsg`, minted from a SINGLE fast fresh counter that
//! starts after reserved source/equation variables named `lock`) and, via
//! `annotateEachClosestUnlock` (Locks.hs), matches that lock variable onto
//! each closest enclosing-scope `unlock` (and `insert`/`lookup`) that shares the
//! lock's term.
//!
//! The pass runs LAST in the annotation pipeline (sapic/src/Sapic.hs), after
//! `propagateNames` / `annotateSecretChannels` / `annotatePureStates`.
//!
//! NOTE on the fresh counter: HS `annotateLocks` runs in the *Fast* `FreshT`
//! monad, where `freshIdent _name = freshIdents 1` ignores the name and
//! returns the global counter. Without reserved lock variables the first
//! lock gets index 0, the second index 1, etc. This counter is
//! independent of the per-name `renameUnique` counter.

use tamarin_utils::fresh::{FastFreshState, MonadFresh};

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::sapic::{Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm};

use crate::annotation::ProcessAnnotation;
use crate::exceptions::{process_not_wellformed, WfError, WfLockTag};

type AnnotatedProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// `annotateEachClosestUnlock t v p` (Locks.hs): annotate the closest
/// occurrence of `unlock` (and `insert t _` / `lookup t _`) that has term `t`
/// with the variable `v`.  Errors (HS `LocalException`) on `Rep`/`Parallel`
/// below the lock.
///
/// Annotates `p` in place: on an error the caller reports `p`, which it
/// renders without annotations, so a partial annotation does not show.
fn annotate_each_closest_unlock(
    t: &SapicTerm,
    v: &LVar,
    p: &mut AnnotatedProc,
) -> Result<(), WfLockTag> {
    let ann_unlock = |a: &mut ProcessAnnotation<LVar>| {
        *a = std::mem::take(a).append(ProcessAnnotation::with_unlock(*v));
    };
    match p {
        // ProcessNull a' -> return $ ProcessNull a'
        Process::Null(_) => Ok(()),
        Process::Action(ac, a, body) => match ac {
            // (Unlock t') | t == t' -> annUnlock here, STOP (closest match).
            //              | otherwise -> recurse into body.
            SapicAction::Unlock(t_prime) if t == t_prime => {
                ann_unlock(a);
                Ok(())
            }
            // (Insert t1 t2) | t1 == t -> annUnlock here AND recurse into body.
            //  (otherwise falls through to the generic action case below.)
            SapicAction::Insert(t1, _t2) if t1 == t => {
                annotate_each_closest_unlock(t, v, body)?;
                ann_unlock(a);
                Ok(())
            }
            // (Rep) -> Left WFRep
            SapicAction::Rep => Err(WfLockTag::Rep),
            // generic action: recurse into body.
            _ => annotate_each_closest_unlock(t, v, body),
        },
        // (ProcessComb Parallel _ _ _) -> Left WFPar
        Process::Comb(ProcessCombinator::Parallel, _, _, _) => Err(WfLockTag::Par),
        Process::Comb(c, a, pl, pr) => {
            annotate_each_closest_unlock(t, v, pl)?;
            annotate_each_closest_unlock(t, v, pr)?;
            // (Lookup st vt) | st == t -> annUnlock here AND recurse into
            // BOTH children; a generic combinator only recurses.
            if matches!(c, ProcessCombinator::Lookup(st, _) if st == t) {
                ann_unlock(a);
            }
            Ok(())
        }
    }
}

/// `annotateLocks'` (Locks.hs): at each `Lock t`, mint a fresh lock
/// variable, annotate the closest matching unlocks under it, then recurse.
/// A `LocalException` becomes `ProcessNotWellformed (WFLock tag) (Just p)`
/// over the lock's body (`annotateEachClosestUnlock'`).
fn annotate_locks_go(
    fresh: &mut FastFreshState,
    p: AnnotatedProc,
) -> Result<AnnotatedProc, String> {
    match p {
        // (Lock t) -> fresh v; annotateEachClosestUnlock t v body; recurse; annLock here.
        Process::Action(SapicAction::Lock(t), a, mut body) => {
            // freshLVar "lock" LSortMsg — fast counter, name ignored.
            let v = LVar {
                name: "lock",
                sort: LSort::Msg,
                idx: fresh.fresh_ident(""),
            };
            annotate_each_closest_unlock(&t, &v, &mut body)
                .map_err(|tag| process_not_wellformed(&WfError::Lock(tag), &body))?;
            let p2 = annotate_locks_go(fresh, *body)?;
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

/// `annotateLocks` (Locks.hs): run `annotateLocks'` with the fresh counter
/// seeded at 0.  On a wellformedness error (`Rep`/`Parallel` below a lock), HS
/// `throwM`s a `ProcessNotWellformed (WFLock tag)`; we surface it as an `Err`.
pub(crate) fn annotate_locks(p: AnnotatedProc) -> Result<AnnotatedProc, String> {
    let reserved: Vec<_> = crate::annotation::translation_vars(&p)
        .into_iter()
        .filter(|v| v.name == "lock")
        .collect();
    let mut fresh = tamarin_term::lterm::avoid(&reserved);
    annotate_locks_go(&mut fresh, p)
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
        // as an unlock (HS Locks.hs) AND recursion continues into the body.
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

    /// `WFRep` and `WFPar` are different tags upstream (`prettyWFLockTag`,
    /// Sapic/Exceptions.hs). They select different wording in the
    /// `ProcessNotWellformed` error that upstream throws. The two arms must
    /// therefore not collapse into one error. A lock whose scope stays open is
    /// the only way to reach either tag. `annotate_locks` must refuse the
    /// process in both cases.
    #[test]
    fn parallel_and_replication_below_lock_error_distinctly() {
        // lock 's'; ( 0 | 0 )  — WFPar
        let par = Process::Comb(
            ProcessCombinator::Parallel,
            ProcessAnnotation::empty(),
            Box::new(null()),
            Box::new(null()),
        );
        // lock 's'; ! 0  — WFRep
        let rep = Process::Action(
            SapicAction::Rep,
            ProcessAnnotation::empty(),
            Box::new(null()),
        );
        for (body, want) in [
            (
                par,
                "Process not well-formed: Process contains lock that extends over \
                 a parallel which is not allowed.\n  0 | 0",
            ),
            (
                rep,
                "Process not well-formed: Process contains lock that extends over \
                 replication which is not allowed.\n  !(0)",
            ),
        ] {
            let p = lock(pub_const("s"), body);
            assert_eq!(annotate_locks(p).unwrap_err(), want);
        }
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
