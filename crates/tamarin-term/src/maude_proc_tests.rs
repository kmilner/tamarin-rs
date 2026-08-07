// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::lterm::{LSort, LVar};
use crate::maude_sig::pair_maude_sig;
use crate::vterm::Lit;

fn maude_path() -> Option<String> {
    // Honour an env override; otherwise look for `maude` on PATH.
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return Some(p);
    }
    let candidates = ["/usr/local/bin/maude", "/usr/bin/maude", "maude"];
    for c in &candidates {
        if std::path::Path::new(c).exists() {
            return Some((*c).to_string());
        }
    }
    None
}

#[test]
fn spawn_and_reduce_pair() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
    // Reduce a public-name constant — should normalise to itself.
    let v = LVar::new("x", LSort::Msg, 0);
    let t: LNTerm = crate::term::Term::Lit(Lit::Var(v));
    let r = h.reduce(&t).expect("reduce");
    // Round-trip should give back `x`.
    assert_eq!(t, r);
}

#[test]
fn unify_two_vars() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let tx: LNTerm = crate::term::Term::Lit(Lit::Var(x));
    let ty: LNTerm = crate::term::Term::Lit(Lit::Var(y));
    let unifiers = h.unify(&[Equal { lhs: tx, rhs: ty }]).expect("unify");
    // Two free variables of the same sort have a single mgu (a renaming).
    assert!(!unifiers.is_empty());
}

#[test]
fn unify_xor_terms_ac() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let sig = crate::maude_sig::xor_maude_sig();
    let h = MaudeHandle::start(&path, sig).expect("start");
    // x XOR a =? b XOR y — has multiple AC unifiers.
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let a = LVar::new("a", LSort::Msg, 0);
    let b = LVar::new("b", LSort::Msg, 0);
    let lhs = crate::term::f_app_ac(
        crate::function_symbols::AcSym::Xor,
        vec![
            crate::term::Term::Lit(Lit::Var(x)),
            crate::term::Term::Lit(Lit::Var(a)),
        ],
    );
    let rhs = crate::term::f_app_ac(
        crate::function_symbols::AcSym::Xor,
        vec![
            crate::term::Term::Lit(Lit::Var(b)),
            crate::term::Term::Lit(Lit::Var(y)),
        ],
    );
    let res = h.unify(&[Equal { lhs, rhs }]).expect("unify xor");
    // AC unification of XOR is non-trivial — Maude returns multiple
    // unifiers. We just assert we got at least one.
    assert!(!res.is_empty(), "expected at least one AC unifier");
}

/// Verifies our Maude bridge correctly narrows sorts.
/// Pub is a subsort of Msg in Maude's order-sorted theory, so unifying
/// x:Msg with y:Pub should narrow x → ?:Pub.
#[test]
fn unify_narrows_msg_var_to_pub() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
    let x_msg = LVar::new("x", LSort::Msg, 0);
    let y_pub = LVar::new("y", LSort::Pub, 0);
    let tx: LNTerm = crate::term::Term::Lit(Lit::Var(x_msg));
    let ty: LNTerm = crate::term::Term::Lit(Lit::Var(y_pub));
    let unifiers = h.unify(&[Equal { lhs: tx, rhs: ty }]).expect("unify");
    assert_eq!(unifiers.len(), 1);
    // Both vars should be bound to a fresh variable of sort Pub.
    for (v, t) in &unifiers[0] {
        if let crate::term::Term::Lit(Lit::Var(lv)) = t {
            assert_eq!(
                lv.sort,
                LSort::Pub,
                "expected narrowing to Pub, got {:?} → {:?}",
                v,
                lv
            );
        }
    }
}

/// Verifies our bridge correctly rejects sort-incompatible unifications:
/// `pk(_)` is Msg-typed and cannot unify with a Pub-sorted variable
/// (Pub ⊂ Msg, but `pk(_)` is not Pub).
#[test]
fn unify_pub_var_with_pk_msg_term_fails() {
    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    use crate::function_symbols::{Constructability, FunSym, NoEqSym, Privacy, UserDefinedSym};
    let pk_sym = NoEqSym::new(
        b"pk".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let sig = pair_maude_sig().add_fun_sym(UserDefinedSym::NoEqUser(pk_sym));
    let h = MaudeHandle::start(&path, sig).expect("start");
    let a_pub = LVar::new("A", LSort::Pub, 0);
    let ltka = LVar::new("ltkA", LSort::Fresh, 0);
    let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
    let pk_term = crate::term::Term::App(FunSym::NoEq(pk_sym), vec![mk(ltka)].into());
    let us = h
        .unify(&[Equal {
            lhs: mk(a_pub),
            rhs: pk_term,
        }])
        .expect("unify");
    assert!(us.is_empty(), "expected no unifier for Pub ↔ pk(Fresh)");
}

#[test]
fn reduce_pair_fst_snd() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    // pair_dest_maude_sig has fst/snd as destructors with rules.
    let sig = crate::maude_sig::pair_maude_sig();
    let h = MaudeHandle::start(&path, sig).expect("start");
    // Reduce a simple variable — should be itself.
    let x = LVar::new("x", LSort::Msg, 0);
    let t: LNTerm = crate::term::Term::Lit(Lit::Var(x));
    assert_eq!(h.reduce(&t).expect("reduce"), t);
}

#[test]
fn pool_acquire_release_size() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let pool = MaudePool::new(
        &path,
        pair_maude_sig(),
        3,
        Arc::new(SharedMaudeCaches::default()),
    )
    .expect("pool");
    assert_eq!(pool.size(), 3);
    // Acquire all three, then release them; second round should
    // still succeed (handles must have been returned).
    {
        let _a = pool.acquire();
        let _b = pool.acquire();
        let _c = pool.acquire();
    }
    let a = pool.acquire();
    let b = pool.acquire();
    let c = pool.acquire();
    drop(a);
    drop(b);
    drop(c);
}

/// Sequential acquire/release never grows the pool past its eager first
/// member: each release returns the warm member to `free`, so the next
/// acquire reuses it (LIFO) instead of spawning a lazy one.  `size()`
/// keeps reporting the TARGET, while `spawned()` stays at 1.
#[test]
fn pool_sequential_reuse_stays_at_one_spawned() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let pool = MaudePool::new(
        &path,
        pair_maude_sig(),
        4,
        Arc::new(SharedMaudeCaches::default()),
    )
    .expect("pool");
    assert_eq!(pool.size(), 4);
    assert_eq!(pool.spawned(), 1, "new() spawns exactly one member eagerly");
    for _ in 0..6 {
        let g = pool.acquire();
        drop(g);
    }
    assert_eq!(
        pool.spawned(),
        1,
        "sequential acquire/release reuses the warm member; no lazy spawns"
    );
    assert_eq!(pool.size(), 4, "size() still reports the target");
}

#[test]
fn pool_parallel_reduce_returns_correct_results() {
    use std::sync::Arc;
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let pool = Arc::new(
        MaudePool::new(
            &path,
            pair_maude_sig(),
            2,
            Arc::new(SharedMaudeCaches::default()),
        )
        .expect("pool"),
    );
    let mut handles = Vec::new();
    for i in 0u64..6 {
        let pool = pool.clone();
        handles.push(std::thread::spawn(move || {
            let h = pool.acquire();
            let x = LVar::new("x", LSort::Msg, i);
            let t: LNTerm = crate::term::Term::Lit(Lit::Var(x));
            h.reduce(&t).expect("reduce")
        }));
    }
    for (i, h) in handles.into_iter().enumerate() {
        let r = h.join().expect("thread");
        // round-trip: x:Msg.i reduces to itself
        let x = LVar::new("x", LSort::Msg, i as u64);
        let expected: LNTerm = crate::term::Term::Lit(Lit::Var(x));
        assert_eq!(r, expected);
    }
}

#[test]
fn pool_blocks_when_exhausted() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let pool = std::sync::Arc::new(
        MaudePool::new(
            &path,
            pair_maude_sig(),
            1,
            Arc::new(SharedMaudeCaches::default()),
        )
        .expect("pool"),
    );
    let g = pool.acquire();
    // Spawn a thread that should block on acquire() until we drop g.
    let pool_c = pool.clone();
    let (tx, rx) = std::sync::mpsc::channel();
    let t = std::thread::spawn(move || {
        let _h = pool_c.acquire();
        tx.send(()).unwrap();
    });
    // Initially the worker should be blocked (no message yet).
    assert!(rx
        .recv_timeout(std::time::Duration::from_millis(100))
        .is_err());
    drop(g);
    // After releasing, the worker should wake up promptly.
    rx.recv_timeout(std::time::Duration::from_secs(5))
        .expect("worker should unblock");
    t.join().unwrap();
}

/// Two handles on one `SharedMaudeCaches`: a `reduce` computed on
/// handle A is a shared-cache hit on handle B, eliding B's subprocess
/// round-trip entirely.  `norm_count` bumps only on a real round-trip
/// (`reduce` returns before the bump on the cache-hit, no-reducible,
/// and native normal-form fast paths), so B's count staying at 0
/// proves the hit.  The XOR signature has an AC operator (blocking the
/// no-reducible fast path) and `x XOR x` has duplicate args — non-NF
/// per `invalid_xor`, blocking the native NF fast path — so A's reduce
/// genuinely goes to Maude.
#[test]
fn shared_caches_elide_round_trip_across_handles() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let sig = crate::maude_sig::xor_maude_sig();
    let caches = Arc::new(SharedMaudeCaches::default());
    let a =
        MaudeHandle::start_with_caches(&path, sig.clone(), Arc::clone(&caches)).expect("start a");
    let b = MaudeHandle::start_with_caches(&path, sig, Arc::clone(&caches)).expect("start b");
    let x = LVar::new("x", LSort::Msg, 0);
    let t = crate::term::f_app_ac(
        crate::function_symbols::AcSym::Xor,
        vec![
            crate::term::Term::Lit(Lit::Var(x)),
            crate::term::Term::Lit(Lit::Var(x)),
        ],
    );
    let ra = a.reduce(&t).expect("reduce on a");
    assert_eq!(
        a.stats().norm_count,
        1,
        "handle A performed the real round-trip"
    );
    let rb = b.reduce(&t).expect("reduce on b");
    assert_eq!(rb, ra, "shared hit returns the value A computed");
    assert_eq!(
        b.stats().norm_count,
        0,
        "B's reduce was a shared-cache hit — no IPC round-trip"
    );
}

/// Native normal-form fast path on an AC signature: an already-normal
/// XOR term is certified by `nf_via_haskell` and returned unchanged
/// with NO Maude round-trip (`norm_count` stays 0), while a reducible
/// term (duplicate XOR args) fails the NF check and still round-trips
/// to Maude's reduced result.
#[test]
fn reduce_nf_fast_path_on_ac_signature() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let h = MaudeHandle::start(&path, crate::maude_sig::xor_maude_sig()).expect("start");
    let mk =
        |name: &str| -> LNTerm { crate::term::Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0))) };
    let nf = crate::term::f_app_ac(crate::function_symbols::AcSym::Xor, vec![mk("x"), mk("y")]);
    let r = h.reduce(&nf).expect("reduce NF term");
    assert_eq!(r, nf, "normal-form term comes back unchanged");
    assert_eq!(
        h.stats().norm_count,
        0,
        "NF-certified reduce took the native path — no IPC round-trip"
    );
    // `x XOR x` has duplicate args (`invalid_xor`) — not NF; the real
    // round-trip runs and Maude cancels the pair to `zero`.
    let red = crate::term::f_app_ac(crate::function_symbols::AcSym::Xor, vec![mk("x"), mk("x")]);
    let r2 = h.reduce(&red).expect("reduce reducible term");
    assert_eq!(
        h.stats().norm_count,
        1,
        "reducible term performed the real round-trip"
    );
    let zero: LNTerm = crate::term::f_app_no_eq(crate::function_symbols::zero_sym(), vec![]);
    assert_eq!(r2, zero, "x XOR x reduces to zero");
}

// Pattern multiset `codeOther ++ <a,b>` (codeOther is the only pattern
// var) must AC-match subject `code2 ++ x ++ <a,b>` by binding
// `codeOther -> code2 ++ x`, matching HS's Maude matchAction.
#[test]
fn match_eqs_const_subject_mset_var_to_submultiset() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    use crate::function_symbols::{
        AcSym, Constructability, FunSym, NoEqSym, Privacy, UserDefinedSym,
    };
    let pair_sym = NoEqSym::new(
        b"pair".to_vec(),
        2,
        Privacy::Public,
        Constructability::Constructor,
    );
    let sig = crate::maude_sig::mset_maude_sig().add_fun_sym(UserDefinedSym::NoEqUser(pair_sym));
    let h = MaudeHandle::start(&path, sig).expect("start");
    let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
    // ground "pair" payload a,b -> use public name constants
    let a = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Pub,
        "a",
    )));
    let b = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Pub,
        "b",
    )));
    let payload = crate::term::Term::App(FunSym::NoEq(pair_sym), vec![a, b].into());
    // pattern var codeOther:Msg idx 89 (the universal-bound var)
    let code_other = LVar::new("codeOther", LSort::Msg, 89);
    let pat = crate::term::f_app_ac(AcSym::Union, vec![mk(code_other), payload.clone()]);
    // subject: code2:Msg, x:Msg (free system vars, skolemized by the fn)
    let code2 = LVar::new("code2", LSort::Msg, 8);
    let xv = LVar::new("x", LSort::Msg, 9);
    let subj = crate::term::f_app_ac(AcSym::Union, vec![mk(code2), mk(xv), payload.clone()]);
    let mut pattern_vars = std::collections::BTreeSet::new();
    pattern_vars.insert(("codeOther".to_string(), 89u64));
    let res = h
        .match_eqs_const_subject(
            &[Equal {
                lhs: pat,
                rhs: subj,
            }],
            &pattern_vars,
        )
        .expect("match");
    eprintln!("[REPRO] match result count = {}", res.len());
    for m in &res {
        for (lv, lt) in m {
            eprintln!("[REPRO]   {}#{} -> {:?}", lv.name, lv.idx, lt);
        }
    }
    assert!(
        !res.is_empty(),
        "expected codeOther to AC-match a 2-element sub-multiset"
    );
}

// HS's `impliedFormulas` runs `skolemizeGuarded` over the WHOLE clause
// (`System.hs:1111-1145, see line 1122`): every FREE (non-universal) LVar of the guard
// pattern becomes a Maude *constant*; only universal-bound vars stay
// bindable. `match_eqs_const_subject` over-matches such guards (treats
// free vars as Maude variables); `match_eqs_skolemize_both` treats them
// as distinct constants, matching HS's `skolemizeGuarded`-then-match.
//
// Mirrors the real STS_MAC_fix2 `AcceptedR` guard match (sent as
// per-argument equations, one for each fact position).  The guard
// pattern has ONE universal-bound var `kpartner` and several FREE
// system vars (`ekI`,`ekR`) that, after a prior guard's binding,
// occupy positions whose subject counterparts are DIFFERENT free
// system vars (`x`,`tid`).  Two equations:
//   eq1:  exp(g, ekI)  <=?  exp(g, x)     (pattern free ekI vs x)
//   eq2:  exp(g, ekR)  <=?  exp(g, tid)   (pattern free ekR vs tid)
// With `match_eqs_const_subject` the pattern's `ekI`,`ekR` are Maude
// VARIABLES, so Maude binds `ekI->x`, `ekR->tid` and the match
// SUCCEEDS — the spurious match that fired `gfalse` one step early.
// With `match_eqs_skolemize_both` every free var is a distinct
// CONSTANT, so `exp(g,c_ekI)` != `exp(g,c_x)` and the match FAILS,
// exactly as HS's `skolemizeGuarded`-then-`matchAction` does.
#[test]
fn impl_guard_match_skolemizes_pattern_free_vars() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    use crate::function_symbols::{exp_sym, FunSym};
    let sig = crate::maude_sig::dh_maude_sig();
    let h = MaudeHandle::start(&path, sig).expect("start");
    let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
    let g = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Pub,
        "g",
    )));
    let exp = |base: LNTerm, e: LNTerm| {
        crate::term::Term::App(FunSym::NoEq(exp_sym()), vec![base, e].into())
    };
    // free (non-universal) system vars — NONE of these is in
    // `pattern_vars`, so HS skolemizes them all to constants.
    let ek_i = LVar::new("ekI", LSort::Fresh, 0);
    let ek_r = LVar::new("ekR", LSort::Fresh, 0);
    let xv = LVar::new("x", LSort::Fresh, 21);
    let tid = LVar::new("tid", LSort::Fresh, 15);
    let eqs = vec![
        Equal {
            lhs: exp(g.clone(), mk(ek_i)),
            rhs: exp(g.clone(), mk(xv)),
        },
        Equal {
            lhs: exp(g.clone(), mk(ek_r)),
            rhs: exp(g.clone(), mk(tid)),
        },
    ];
    // No universal-bound vars in these positions.
    let pattern_vars: std::collections::BTreeSet<(String, u64)> = std::collections::BTreeSet::new();
    // const_subject OVER-MATCHES: the pattern's free `ekI`,`ekR` are
    // Maude variables binding to x,tid.
    let over = h.match_eqs_const_subject(&eqs, &pattern_vars).expect("m1");
    eprintln!(
        "[REPRO] const_subject matches = {} (over-match expected: >=1)",
        over.len()
    );
    assert!(
        !over.is_empty(),
        "sanity: const_subject is expected to OVER-match here (the bug)"
    );
    // skolemize_both: ekI,ekR,x,tid are distinct constants, so neither
    // equation can be satisfied → NO match, matching HS.
    let fixed = h.match_eqs_skolemize_both(&eqs, &pattern_vars).expect("m2");
    eprintln!(
        "[REPRO] skolemize_both matches = {} (HS-faithful: 0)",
        fixed.len()
    );
    assert!(
        fixed.is_empty(),
        "skolemize_both must NOT over-match: pattern-side free system \
             vars (ekI,ekR) are CONSTANTS and cannot bind to the subject's \
             different free vars (x,tid); got {:?}",
        fixed
    );
}

/// Directional regression for the `match_eqs` / `compare_term_subs`
/// flipped-`Equal`-convention bug.
///
/// HS `compareTermSubs t1 t2` (`Subsumption.hs:37-45`) returns `GT`
/// when `t1` is strictly MORE SPECIFIC than `t2`, `LT` when more
/// general. With `t1 = h(x)` (general) and `t2 = h(a)` (ground,
/// specific):
///   - arm A = `t1 matchWith t2` = subject h(x) vs pattern h(a):
///     h(x)'s free var sits in the SUBJECT (ground) slot, h(a) is
///     the pattern with no vars ⇒ No match (empty).
///   - arm B = `t2 matchWith t1` = subject h(a) vs pattern h(x):
///     x --> a ⇒ matches.
///   - check [] (_:_) = LT ⇒ `compareTermSubs(h(x),h(a)) = Just LT`
///     and symmetrically `compareTermSubs(h(a),h(x)) = Just GT`.
///
/// Pins the directionality: arm A (`t1` matchWith `t2`) uses `Equal { lhs:
/// t1, rhs: t2 }` (RS `Equal`'s HS-faithful subject,pattern order), not
/// the pattern,subject order used by the `const_subject` sibling.
#[test]
fn compare_term_subs_direction_matches_hs() {
    let path = match maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    use crate::function_symbols::{Constructability, FunSym, NoEqSym, Privacy, UserDefinedSym};
    let h_sym = NoEqSym::new(
        b"h".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let sig = pair_maude_sig().add_fun_sym(UserDefinedSym::NoEqUser(h_sym));
    let hnd = MaudeHandle::start(&path, sig).expect("start");
    let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
    let x = LVar::new("x", LSort::Msg, 0);
    let a = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Pub,
        "a",
    )));
    let t_gen = crate::term::Term::App(FunSym::NoEq(h_sym), vec![mk(x)].into()); // h(x) general
    let t_spec = crate::term::Term::App(FunSym::NoEq(h_sym), vec![a].into()); // h(a) specific
                                                                              // general vs specific => general is LESS specific => Less.
    assert_eq!(
        crate::subsumption::compare_term_subs(&hnd, &t_gen, &t_spec).expect("cmp"),
        Some(std::cmp::Ordering::Less),
        "h(x) is more general than h(a); HS compareTermSubs gives Less"
    );
    // specific vs general => specific is MORE specific => Greater.
    assert_eq!(
        crate::subsumption::compare_term_subs(&hnd, &t_spec, &t_gen).expect("cmp"),
        Some(std::cmp::Ordering::Greater),
        "h(a) is more specific than h(x); HS compareTermSubs gives Greater"
    );
    // Identical (modulo renaming) terms compare Equal (invariant).
    let y = LVar::new("y", LSort::Msg, 1);
    let t_gen2 = crate::term::Term::App(FunSym::NoEq(h_sym), vec![mk(y)].into());
    assert_eq!(
        crate::subsumption::compare_term_subs(&hnd, &t_gen, &t_gen2).expect("cmp"),
        Some(std::cmp::Ordering::Equal),
        "h(x) and h(y) are equal modulo renaming => Equal"
    );
}
