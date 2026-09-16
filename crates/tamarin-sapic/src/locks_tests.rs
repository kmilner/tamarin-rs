// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
        Box::new(body).into(),
    )
}
fn unlock(t: SapicTerm, body: AnnotatedProc) -> AnnotatedProc {
    Process::Action(
        SapicAction::Unlock(t),
        ProcessAnnotation::empty(),
        Box::new(body).into(),
    )
}

fn reference(mut p: AnnotatedProc) -> Result<AnnotatedProc, LockWfError> {
    let mut fresh = FastFreshState::nothing_used();
    crate::process_walk::walk_mut(&mut p, (), |node, _| {
        if let Process::Action(SapicAction::Lock(t), ann, body) = node {
            let v = LVar::new("lock", LSort::Msg, fresh.fresh_ident(""));
            annotate_each_closest_unlock(t, &v, body)?;
            *ann = std::mem::take(ann).append(ProcessAnnotation::with_lock(v));
        }
        Ok(true)
    })?;
    Ok(p)
}

#[test]
fn lock_scope_matches_separate_scans_and_outer_error_precedence() {
    fn generated(seed: &mut u64, depth: usize) -> AnnotatedProc {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let choice = (*seed >> 32) % 10;
        let term = pub_const(if *seed & 1 == 0 { "a" } else { "b" });
        let ann = ProcessAnnotation {
            else_branch: false,
            ..ProcessAnnotation::with_unlock(LVar::new("old", LSort::Msg, 99))
        };
        if depth == 0 || choice == 0 {
            return Process::Null(ann);
        }
        let left = Box::new(generated(seed, depth - 1)).into();
        let ac = match choice {
            1 => SapicAction::Lock(term),
            2 => SapicAction::Unlock(term),
            3 => SapicAction::Insert(term.clone(), term),
            4 => SapicAction::Rep,
            5..=8 => {
                let comb = match choice {
                    5 => ProcessCombinator::Parallel,
                    6 => ProcessCombinator::Ndc,
                    7 => ProcessCombinator::Lookup(
                        term,
                        SapicLVar::untyped(LVar::new("x", LSort::Msg, 0)),
                    ),
                    _ => ProcessCombinator::CondEq(term.clone(), term),
                };
                return Process::Comb(comb, ann, left, Box::new(generated(seed, depth - 1)).into());
            }
            _ => SapicAction::ChOut {
                chan: None,
                msg: term,
            },
        };
        Process::Action(ac, ann, left)
    }
    let mut seed = 78129;
    for _ in 0..1024 {
        let p = generated(&mut seed, 7);
        assert_eq!(
            annotate_locks_go(&mut FastFreshState::nothing_used(), p.clone()),
            reference(p)
        );
    }
    let p = lock(
        pub_const("a"),
        Process::Comb(
            ProcessCombinator::CondEq(pub_const("a"), pub_const("b")),
            ProcessAnnotation::empty(),
            Box::new(unlock(
                pub_const("a"),
                lock(
                    pub_const("b"),
                    Process::Comb(
                        ProcessCombinator::Parallel,
                        ProcessAnnotation::empty(),
                        Box::new(null()).into(),
                        Box::new(null()).into(),
                    ),
                ),
            ))
            .into(),
            Box::new(Process::Action(
                SapicAction::Rep,
                ProcessAnnotation::empty(),
                Box::new(null()).into(),
            ))
            .into(),
        ),
    );
    assert_eq!(reference(p.clone()).unwrap_err(), LockWfError::Rep);
    assert_eq!(
        annotate_locks_go(&mut FastFreshState::nothing_used(), p).unwrap_err(),
        LockWfError::Rep
    );
}

#[test]
fn deep_distinct_locks_match_in_reverse_order_on_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let depth = 8192;
        let mut p = null();
        let terms: Vec<_> = (0..depth).map(|i| pub_const(&format!("s{i}"))).collect();
        for term in &terms {
            p = unlock(term.clone(), p);
        }
        for term in terms.iter().rev() {
            p = lock(term.clone(), p);
        }
        let p = annotate_locks(p).unwrap();
        let mut current = &p;
        for i in 0..depth {
            let Process::Action(_, ann, body) = current else {
                panic!("missing lock")
            };
            assert_eq!(ann.lock.as_ref().unwrap().0.idx, i as u64);
            current = body;
        }
        for i in (0..depth).rev() {
            let Process::Action(_, ann, body) = current else {
                panic!("missing unlock")
            };
            assert_eq!(ann.unlock.as_ref().unwrap().0.idx, i as u64);
            current = body;
        }
        assert!(matches!(current, Process::Null(_)));
    });
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
        if let Process::Action(SapicAction::Unlock(_), ua, _) = body.into_inner() {
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
    let Process::Action(SapicAction::Unlock(_), _, body1) = body0.into_inner() else {
        panic!()
    };
    let Process::Action(SapicAction::Lock(_), a1, _) = body1.into_inner() else {
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
            Box::new(null()).into(),
        ),
    );
    let out = annotate_locks(p).unwrap();
    let Process::Action(SapicAction::Lock(_), _, body) = out else {
        panic!()
    };
    let Process::Action(SapicAction::Insert(_, _), ia, _) = body.into_inner() else {
        panic!()
    };
    assert_eq!(ia.unlock.expect("insert annotated as unlock").0.idx, 0);
}

/// `WFRep` and `WFPar` are different tags upstream (`prettyWFLockTag`,
/// Sapic/Exceptions.hs:32-34). They select different wording in the
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
        Box::new(null()).into(),
        Box::new(null()).into(),
    );
    // lock 's'; ! 0  — WFRep
    let rep = Process::Action(
        SapicAction::Rep,
        ProcessAnnotation::empty(),
        Box::new(null()).into(),
    );
    for (body, want) in [(par, LockWfError::Par), (rep, LockWfError::Rep)] {
        let p = lock(pub_const("s"), body);
        let mut fresh = FastFreshState::nothing_used();
        assert_eq!(annotate_locks_go(&mut fresh, p.clone()).unwrap_err(), want);
        assert!(annotate_locks(p).is_err());
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
    let Process::Action(SapicAction::Unlock(_), ua, _) = body.into_inner() else {
        panic!()
    };
    assert!(ua.unlock.is_none());
}
