// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::lterm::{LSort, LVar};
use crate::maude_sig::pair_maude_sig;
use crate::vterm::Lit;

use tamarin_test_support::require_maude_path;

#[cfg(feature = "lean-unification")]
#[test]
fn native_matching_and_reduction_check_declarations_before_returning_an_identity() {
    let native = |reference| {
        let mut h = MaudeHandle::start_with_backend(
            "/nonexistent/maude",
            pair_maude_sig(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        h.set_reference(reference);
        h
    };
    let a = crate::lterm::pub_term("a");
    let undeclared = crate::builtin::emap(a.clone(), a.clone());
    let nat = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Nat,
        "n",
    )));
    // Each request starts a fresh session because unsupported errors are sticky.
    for reference in [false, true] {
        for term in [&undeclared, &nat] {
            let query = [Equal::new(term.clone(), term.clone())];
            for result in [
                native(reference).reduce(term).map(|_| ()),
                native(reference).match_eqs(&query).map(|_| ()),
                native(reference).first_match_eqs(&query).map(|_| ()),
                native(reference).has_match_eqs(&query).map(|_| ()),
                native(reference).unify(&query).map(|_| ()),
                native(reference).unifiable(&query).map(|_| ()),
                native(reference)
                    .match_eqs_skolemize_both(&query, &Default::default())
                    .map(|_| ()),
            ] {
                assert!(matches!(result, Err(MaudeError::UnsupportedOperation(_))));
            }
        }
    }

    // Lists are declared at TOP, including pairs of different widths.
    let packed = crate::term::f_app_list;
    let query = [Equal::new(packed(vec![a]), packed(vec![]))];
    assert!(!native(false).has_match_eqs(&query).unwrap());
}

#[test]
fn maude_reply_witnesses_avoid_full_width_caller_indices() {
    use crate::maude_types::MaudeLit::{FreshVar, MaudeVar};
    use crate::term::Term;

    let mut ctx = ConvCtx::new();
    let mut domains = Vec::new();
    for idx in [0, 2, u64::MAX] {
        let v = LVar::new("x", LSort::Msg, idx);
        let Term::Lit(MaudeVar(id, sort)) =
            lterm_to_mterm_global(&Term::Lit(Lit::Var(v)), &mut ctx)
        else {
            panic!("expected variable")
        };
        domains.push((sort, id));
    }
    let w = Term::Lit(FreshVar(1, LSort::Msg));
    let z = Term::Lit(FreshVar(2, LSort::Msg));
    let reply = vec![(domains[0], w.clone()), (domains[1], z), (domains[2], w)];
    let result = msubst_to_lnsubst_with_avoid(&reply, &mut ctx, u64::MAX).unwrap();
    let images: Vec<_> = result.iter().map(|(_, t)| t.clone()).collect();
    let witness = |idx| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, idx)));
    assert_eq!(images, vec![witness(1), witness(3), witness(1)]);
}

#[test]
fn variable_sort_order_is_independent_of_history() {
    let Some(path) = require_maude_path() else {
        return;
    };
    for enable_nat in [false, true] {
        let mut sig = crate::maude_sig::minimal_maude_sig(false);
        sig.enable_mset = true;
        sig.enable_nat = enable_nat;
        let first = MaudeHandle::start(&path, sig.clone()).unwrap();
        let second = MaudeHandle::start(&path, sig).unwrap();
        // Even with identical name order, creating Fresh's variable symbol
        // before Pub's (versus the reverse) used to change the unifiers.
        first
            .inner
            .lock()
            .execute(b"parse in MSG : x0:Fresh .\n", 1)
            .unwrap();
        second
            .inner
            .lock()
            .execute(b"parse in MSG : x0:Pub .\n", 1)
            .unwrap();
        if enable_nat {
            second
                .inner
                .lock()
                .execute(b"parse in MSG : x0:TamNat .\n", 1)
                .unwrap();
        }
        let cmd = b"unify in MSG : tammun(x0:Fresh,x1:Pub,x2:Msg) =? tammun(x3:Msg,x4:Msg) .\n";
        let expected = first.inner.lock().execute(cmd, 5).unwrap();
        assert!(expected
            .windows(b"Unifier 10".len())
            .any(|w| w == b"Unifier 10"));
        assert_eq!(second.inner.lock().execute(cmd, 5).unwrap(), expected);
    }
}

#[test]
fn variable_order_is_independent_of_history_beyond_2000_names() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let mut sig = crate::maude_sig::xor_maude_sig();
    sig.enable_mset = true;
    let fresh = MaudeHandle::start(&path, sig.clone()).unwrap();
    let used = MaudeHandle::start(&path, sig).unwrap();
    // Generate # and % names before extending the input-name range.
    for cmd in [
        "unify in MSG : tamxor(x0:Msg,x1:Msg) =? tamxor(x2:Msg,x3:Msg) .\n",
        "get variants in MSG : tamxor(x0:Msg,x1:Msg) .\n",
    ] {
        used.inner.lock().execute(cmd.as_bytes(), 4).unwrap();
    }
    for base in [0, 2048, 8192] {
        let [a, b, c, d] = [base, base + 1, base + 2, base + 3];
        // A query whose text first mentions the new names in reverse order.
        let reverse =
            format!("parse in MSG : cons(x{d}:Msg,cons(x{c}:Msg,cons(x{b}:Msg,x{a}:Msg))) .\n");
        used.inner
            .lock()
            .execute(reverse.as_bytes(), d + 1)
            .unwrap();
        for (cmd, success_marker) in [
            (format!("unify in MSG : tamxor(x{a}:Msg,x{b}:Msg) =? tamxor(x{c}:Msg,x{d}:Msg) .\n"), "Unifier 1"),
            (format!("unify in MSG : tammun(x{a}:Fresh,x{b}:Msg,x{c}:Msg,p(0)) =? tammun(x{d}:Msg,x{}:Msg) .\n", d + 1), "Unifier 1"),
            (format!("get variants in MSG : tamxor(x{b}:Msg,x{a}:Msg) .\n"), "Variant 1"),
            (format!("match in MSG : tammun(x{a}:Msg,x{b}:Msg) <=? tammun(p(0),p(1),p(2)) .\n"), "Matcher 1"),
            (format!("reduce in MSG : tamxor(x{b}:Msg,x{a}:Msg,x{b}:Msg) .\n"), "result Msg:"),
        ] {
            let expected = fresh.inner.lock().execute(cmd.as_bytes(), d + 2).unwrap();
            let actual = used.inner.lock().execute(cmd.as_bytes(), d + 2).unwrap();
            assert!(
                String::from_utf8_lossy(&expected).contains(success_marker),
                "{cmd}: {}",
                String::from_utf8_lossy(&expected)
            );
            assert_eq!(actual, expected, "{cmd}");
        }
    }
}

#[test]
fn variable_order_cache_hits_and_restarts() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = crate::maude_sig::xor_maude_sig();
    let caches = Arc::new(SharedMaudeCaches::default());
    let first = MaudeHandle::start_with_caches(&path, sig.clone(), caches.clone()).unwrap();
    let second = MaudeHandle::start_with_caches(&path, sig, caches).unwrap();
    let cmd = b"unify in MSG : tamxor(x2048:Msg,x2049:Msg) =? tamxor(x2050:Msg,x2051:Msg) .\n";
    let expected = first.execute_memo(cmd, 2052, Asked::Unify, |_| {}).unwrap();
    assert_eq!(
        second
            .execute_memo(cmd, 2052, Asked::Unify, |_| {})
            .unwrap(),
        expected
    );
    assert_eq!(
        second.inner.lock().ordered_variables,
        1,
        "cache hits do no registration"
    );
    let reverse = b"parse in MSG : cons(x2051:Msg,cons(x2050:Msg,cons(x2049:Msg,x2048:Msg))) .\n";
    second.inner.lock().execute(reverse, 2052).unwrap();
    assert_eq!(second.inner.lock().execute(cmd, 2052).unwrap(), expected);
    assert_eq!(second.inner.lock().ordered_variables, 4096);
    {
        let mut reaper = second.child.lock().unwrap();
        reaper.kill_and_wait();
        reaper.restart = true;
    }
    // A cache hit can still bypass a dead child. The first real exchange must
    // re-register names even though the old child had the same watermark.
    assert_eq!(
        second
            .execute_memo(cmd, 2052, Asked::Unify, |_| {})
            .unwrap(),
        expected
    );
    second.inner.lock().execute(reverse, 2052).unwrap();
    assert_eq!(second.inner.lock().execute(cmd, 2052).unwrap(), expected);
}

#[test]
fn variable_registration_grows_only_as_needed() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let h = MaudeHandle::start(&path, crate::maude_sig::minimal_maude_sig(false)).unwrap();
    let mut inner = h.inner.lock();
    inner.execute(b"reduce in MSG : p(0) .\n", 0).unwrap();
    assert_eq!(inner.ordered_variables, 1, "only the sort initializer's x0");
    for (required, expected) in [(1, 1), (2, 2), (3, 4), (4, 4), (5, 8), (2, 8)] {
        let cmd = format!("reduce in MSG : x{}:Msg .\n", required - 1);
        let reply = inner.execute(cmd.as_bytes(), required).unwrap();
        assert!(String::from_utf8_lossy(&reply).contains(&format!("x{}:Msg", required - 1)));
        assert_eq!(inner.ordered_variables, expected);
    }
}

/// `fst(pair(a, b))` over [`pair_maude_sig`].  The pairing signature really
/// rewrites this term. The subprocess test explicitly selects Maude, since
/// the Lean pairing backend can also reduce it without IPC.
fn reducible_fst_pair(a: &str, b: &str) -> LNTerm {
    use crate::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
    let mk = |n: &str| -> LNTerm {
        crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
            crate::lterm::NameTag::Pub,
            n,
        )))
    };
    let pair = NoEqSym::new(
        b"pair".to_vec(),
        2,
        Privacy::Public,
        Constructability::Constructor,
    );
    let fst = NoEqSym::new(
        b"fst".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let inner = crate::term::Term::App(FunSym::NoEq(pair), vec![mk(a), mk(b)].into());
    crate::term::Term::App(FunSym::NoEq(fst), vec![inner].into())
}

/// The whole bridge on one query.  `pp_theory` produces a module that Maude
/// accepts.  `pp_mterm` produces a `reduce` command that Maude understands.
/// The reply parses back into the LNTerm that the `fst`/`pair` rewrite rule
/// yields.
///
/// `norm_count` shows that the test really consulted the subprocess.
/// `reduce` can answer some terms from a fast path, and a single variable is
/// one such term.  A test that used such a term would assert `t == t` and
/// would talk to nothing.
#[test]
fn spawn_and_reduce_pair() {
    let path = match require_maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let h = MaudeHandle::start_with_backend(&path, pair_maude_sig(), AlgebraBackend::Maude)
        .expect("start");
    let r = h.reduce(&reducible_fst_pair("a", "b")).expect("reduce");
    let a: LNTerm = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Pub,
        "a",
    )));
    assert_eq!(r, a, "fst(pair('a','b')) reduces to 'a'");
    assert_eq!(h.stats().norm_count, 1, "the reduce really went to Maude");
}

/// `Reduction` runs over the FAST `FreshT` (Reduction.hs with the
/// re-export at Control/Monad/Fresh.hs), so the handle's single counter
/// answers both class methods: `freshIdent` ignores the name and draws one
/// (Control/Monad/Fresh/Class.hs), and `freshIdents k` reserves `k` and
/// returns the first.
#[test]
fn maude_handle_fresh_idents_is_reserve_idxs() {
    let path = match require_maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
    let mut m = &h;
    assert_eq!(m.fresh_ident("x"), 0);
    assert_eq!(m.fresh_ident("y"), 1);
    assert_eq!(m.fresh_idents(4), 2);
    // The draws all came from the one counter that `reserve_idxs` advances.
    assert_eq!(h.fresh_counter_peek(), 6);
    assert_eq!(h.reserve_idxs(1), 6);
}

#[test]
fn unify_two_vars() {
    let path = match require_maude_path() {
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
    // Two free variables of the same sort have exactly one mgu, and that mgu
    // is a renaming.  Maude maps both variables onto one Maude-introduced Msg
    // variable, and `unify`'s hint supplies the name.  Maude does not map one
    // input variable onto the other.
    assert_eq!(unifiers.len(), 1);
    let mut bound: Vec<(&str, u64, LNTerm)> = unifiers[0]
        .iter()
        .map(|(v, t)| (v.name, v.idx, t.clone()))
        .collect();
    bound.sort_by_key(|(n, i, _)| (*n, *i));
    let witness = bound[0].2.clone();
    assert_eq!(bound, vec![("x", 0, witness.clone()), ("y", 0, witness)]);
    let crate::term::Term::Lit(Lit::Var(w)) = &bound[0].2 else {
        panic!("expected a variable witness, got {:?}", bound[0].2);
    };
    assert_eq!(w.sort, LSort::Msg);
    assert!(w.idx > 0, "the witness is fresh, not one of the inputs");
}

#[test]
fn unify_xor_terms_ac() {
    let path = match require_maude_path() {
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
    // Maude 3.5.1 enumerates a complete set of 7 unifiers here.  CI pins that
    // version.  See `.github/workflows/ci.yml`.  The test compares the count,
    // and not just that the set is not empty.  The count catches a reply
    // parser that drops or duplicates solutions.  It also catches a
    // conversion context whose variable numbering changes the enumeration.
    // The port names the Maude-side variables in the order it meets them,
    // and Maude's AC search is sensitive to those names.
    assert_eq!(res.len(), 7, "unifiers: {res:#?}");
    for u in &res {
        let mut names: Vec<(&str, u64)> = u.iter().map(|(v, _)| (v.name, v.idx)).collect();
        names.sort();
        assert_eq!(
            names,
            vec![("a", 0), ("b", 0), ("x", 0), ("y", 0)],
            "every unifier binds all four input variables"
        );
    }
}

/// Verifies our Maude bridge correctly narrows sorts.
/// Pub is a subsort of Msg in Maude's order-sorted theory, so unifying
/// x:Msg with y:Pub should narrow x → ?:Pub.
#[test]
fn unify_narrows_msg_var_to_pub() {
    let path = match require_maude_path() {
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
    // The single unifier binds both variables, and it binds each one to a
    // variable of the narrower sort (`Pub`).  This includes `x`, which the
    // test declares as `Msg`.  The test asserts this over the whole
    // substitution, and not inside a shape guard.  A binding that comes back
    // as something other than a variable therefore fails the test.  The test
    // does not skip it.  An empty substitution also cannot pass vacuously.
    assert_eq!(unifiers[0].len(), 2);
    let mut got: Vec<(&str, LSort)> = unifiers[0]
        .iter()
        .map(|(v, t)| match t {
            crate::term::Term::Lit(Lit::Var(lv)) => (v.name, lv.sort),
            other => panic!("{}.{} bound to a non-variable {other}", v.name, v.idx),
        })
        .collect();
    got.sort();
    assert_eq!(got, vec![("x", LSort::Pub), ("y", LSort::Pub)]);
}

/// Verifies our bridge correctly rejects sort-incompatible unifications:
/// `pk(_)` is Msg-typed and cannot unify with a Pub-sorted variable
/// (Pub ⊂ Msg, but `pk(_)` is not Pub).
#[test]
fn unify_pub_var_with_pk_msg_term_fails() {
    let path = match require_maude_path() {
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

/// The pool spawns its lazy members only when the test holds several guards
/// at once.  `new` starts one member eagerly.  Each acquire that finds `free`
/// empty spawns another member, until the pool reaches its target.  When the
/// test releases all the guards, the members return to the pool.  A second
/// round of the same size therefore reuses those members and spawns no more.
#[test]
fn pool_acquire_release_size() {
    let path = match require_maude_path() {
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
    let pool = Arc::new(pool);
    assert_eq!(pool.size(), 3);
    assert_eq!(pool.spawned(), 1, "new() spawns exactly one member eagerly");
    {
        let _a = pool
            .try_take_idle_owned()
            .expect("the eager worker is idle");
        assert!(pool.try_take_idle_owned().is_none());
        assert_eq!(pool.spawned(), 1, "proof admission must not start Maude");
        let _b = pool.acquire();
        let owned = pool.try_acquire_ready().unwrap();
        assert!(pool.try_acquire().is_none(), "owned leases occupy a slot");
        assert_eq!(pool.spawned(), 3, "three concurrent guards, three members");
        std::thread::spawn(move || drop(owned)).join().unwrap();
        assert!(pool.try_acquire().is_some(), "worker returned its process");
    }
    // Second round.  The pool reuses the three released members.  Each one is
    // a live subprocess that still answers a query.
    let guards = [pool.acquire(), pool.acquire(), pool.acquire()];
    assert_eq!(
        pool.spawned(),
        3,
        "released members were returned, not lost"
    );
    for g in &guards {
        assert_eq!(
            g.reduce(&reducible_fst_pair("a", "b")).expect("reduce"),
            crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
                crate::lterm::NameTag::Pub,
                "a",
            )))
        );
    }
    drop(guards);
    assert_eq!(pool.size(), 3, "size() still reports the target");

    // A retired entry on top of the stack cannot hide the two warm entries
    // underneath it or be admitted to an idle-only fork.
    pool.acquire().kill_subprocess();
    let _first = pool.try_take_idle_owned().unwrap();
    let _second = pool.try_take_idle_owned().unwrap();
    assert!(pool.try_take_idle_owned().is_none());
    let restarted = pool.try_acquire_ready().unwrap();
    assert!(restarted.child.lock().unwrap().child.is_some());
}

#[test]
fn admission_replaces_an_idle_process_that_exited_on_its_own() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let pool = Arc::new(MaudePool::new(&path, pair_maude_sig(), 1, Default::default()).unwrap());
    let worker = pool.acquire();
    worker
        .handle()
        .inner
        .lock()
        .write_line(b"quit .\n")
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    while matches!(worker.child.lock().unwrap().is_running(), Ok(true)) {
        assert!(std::time::Instant::now() < deadline, "Maude did not exit");
        std::thread::yield_now();
    }
    drop(worker);
    assert!(pool.try_take_idle_owned().is_none());
    // Both paths that can hand out a dead process restart it first.
    pool.acquire()
        .variants(&reducible_fst_pair("blocking", "b"))
        .unwrap();
    pool.acquire().kill_subprocess();
    pool.try_acquire_ready()
        .unwrap()
        .variants(&reducible_fst_pair("new", "b"))
        .unwrap();
}

#[cfg(unix)]
#[test]
fn probing_an_exited_wrapper_preserves_descendant_cleanup() {
    use std::{io::Read, sync::mpsc, time::Duration};

    let mut wrapper = Command::new("sh");
    tamarin_utils::process::isolate_process_group(&mut wrapper);
    let mut child = wrapper
        .args(["-c", "sleep 5 & echo x"])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    stdout.read_exact(&mut [0; 2]).unwrap(); // the descendant now holds stdout
    let mut reaper = MaudeChildReaper {
        child: Some(child),
        restart: false,
    };
    let deadline = std::time::Instant::now() + Duration::from_secs(2);
    while matches!(reaper.is_running(), Ok(true)) {
        assert!(std::time::Instant::now() < deadline, "wrapper did not exit");
        std::thread::yield_now();
    }
    reaper.invalidate();
    let (closed, eof) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = closed.send(stdout.read(&mut [0]));
    });
    assert_eq!(
        eof.recv_timeout(Duration::from_secs(2)).unwrap().unwrap(),
        0
    );
}

#[test]
fn failed_exchange_leaves_the_primary_available_for_the_next_request() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let primary = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    assert!(primary.inner.lock().execute(b"quit .\n", 0).is_err());
    primary.variants(&reducible_fst_pair("next", "b")).unwrap();
}

/// Sequential acquire/release never grows the pool past its eager first
/// member: each release returns the warm member to `free`, so the next
/// acquire reuses it (LIFO) instead of spawning a lazy one.  `size()`
/// keeps reporting the TARGET, while `spawned()` stays at 1.
#[test]
fn pool_sequential_reuse_stays_at_one_spawned() {
    let path = match require_maude_path() {
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

/// A panic during an exchange leaves the pooled handle ready to restart its
/// process before the next query. A panic outside an exchange reuses the
/// healthy process.
#[test]
fn pool_recovers_after_a_panicking_exchange() {
    let path = match require_maude_path() {
        Some(p) => p,
        None => {
            eprintln!("skipping: no maude");
            return;
        }
    };
    let pool = MaudePool::new_with_backend(
        &path,
        pair_maude_sig(),
        1,
        Arc::new(SharedMaudeCaches::default()),
        AlgebraBackend::Maude,
    )
    .expect("pool");
    let old_pid = {
        let h = pool.acquire();
        h.child.lock().unwrap().child.as_ref().unwrap().id()
    };
    let panicked = std::thread::scope(|s| {
        s.spawn(|| {
            let h = pool.acquire();
            h.handle().inner.lock().with_cancellation::<()>(|inner| {
                inner.initialize()?;
                inner.write_line(b"show modules .\n")?;
                panic!("abandon an exchange before reading its reply");
            })
        })
        .join()
        .is_err()
    });
    assert!(panicked);
    assert_eq!(pool.spawned(), 1, "the pool keeps its member");
    let h = pool.acquire();
    assert!(h.child.lock().unwrap().child.is_none());
    let r = h.reduce(&reducible_fst_pair("a", "b")).expect("reduce");
    assert_eq!(
        r,
        crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
            crate::lterm::NameTag::Pub,
            "a"
        )))
    );
    let new_pid = h.child.lock().unwrap().child.as_ref().unwrap().id();
    assert_ne!(old_pid, new_pid, "the interrupted process was replaced");
    drop(h);

    let panicked = std::thread::scope(|s| {
        s.spawn(|| {
            let _h = pool.acquire();
            panic!("panic outside any Maude call");
        })
        .join()
        .is_err()
    });
    assert!(panicked);
    assert_eq!(pool.spawned(), 1, "a healthy handle goes back to the pool");
    let h = pool.acquire();
    assert_eq!(
        new_pid,
        h.child.lock().unwrap().child.as_ref().unwrap().id()
    );
    h.reduce(&reducible_fst_pair("healthy", "b"))
        .expect("healthy process still answers");
    // A transport failure remains visible to its borrower. Its successor
    // must still be able to issue a fresh query on the same pool slot.
    h.kill_subprocess();
    assert!(h.variants(&reducible_fst_pair("dead", "b")).is_err());
    drop(h);
    pool.acquire()
        .variants(&reducible_fst_pair("restored", "b"))
        .expect("replacement Maude");
    pool.warn_spawn_failed(&MaudeError::Cancelled);
    assert!(!pool.spawn_warned.load(Ordering::Relaxed));
}

/// Six threads share a two-member pool.  Each thread gets its own answer
/// back.  The term of each query differs from the terms of the other
/// queries.  A handle that leaked another thread's reply therefore returns
/// the wrong constant, and does not merely race.  Two causes of such a leak
/// are interleaved writes on one subprocess and a guard that the pool assigns
/// twice.  Each query is a real round trip.  `fst(pair(..))` rewrites,
/// so `reduce` cannot answer it locally.
#[test]
fn pool_parallel_reduce_returns_correct_results() {
    let path = match require_maude_path() {
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
            // Each query set gets a private cache.  A shared reduce cache
            // would let one thread's answer satisfy another thread's query
            // without IPC.
            Arc::new(SharedMaudeCaches::default()),
        )
        .expect("pool"),
    );
    let names: Vec<String> = (0..6).map(|i| format!("a{i}")).collect();
    let mut handles = Vec::new();
    for name in names.clone() {
        let pool = pool.clone();
        handles.push(std::thread::spawn(move || {
            let h = pool.acquire();
            h.reduce(&reducible_fst_pair(&name, "b")).expect("reduce")
        }));
    }
    for (name, h) in names.iter().zip(handles) {
        let r = h.join().expect("thread");
        let expected: LNTerm = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
            crate::lterm::NameTag::Pub,
            name.as_str(),
        )));
        assert_eq!(r, expected, "fst(pair('{name}','b'))");
    }
}

#[test]
fn pool_blocks_when_exhausted() {
    let path = match require_maude_path() {
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
    let path = match require_maude_path() {
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
    let path = match require_maude_path() {
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
fn match_eqs_skolemize_both_mset_var_to_submultiset() {
    let path = match require_maude_path() {
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
    pattern_vars.insert(("codeOther", 89u64));
    let res = h
        .match_eqs_skolemize_both(
            &[Equal {
                lhs: pat,
                rhs: subj,
            }],
            &pattern_vars,
        )
        .expect("match");
    // The one matcher binds the sole pattern variable to the remainder of the
    // subject multiset.  That remainder is `code2 ++ x`.  These are the two
    // elements that the ground `<a,b>` of the pattern does not consume.  The
    // test compares the binding itself, and not just that the result is not
    // empty.  A matcher that bound `codeOther` to a single element, and not
    // to a sub-multiset, would also give a result that is not empty.
    assert_eq!(res.len(), 1, "matchers: {res:#?}");
    let binding: Vec<(&str, u64, LNTerm)> = res[0]
        .iter()
        .map(|(v, t)| (v.name, v.idx, t.clone()))
        .collect();
    let rest = crate::term::f_app_ac(AcSym::Union, vec![mk(code2), mk(xv)]);
    assert_eq!(binding, vec![("codeOther", 89, rest)]);
}

// HS's `impliedFormulas` runs `skolemizeGuarded` over the WHOLE clause
// (`System.hs`): every FREE (non-universal) LVar of the guard
// pattern becomes a Maude *constant*; only universal-bound vars stay
// bindable.  `match_eqs_skolemize_both` treats those free vars as
// distinct constants, matching HS's `skolemizeGuarded`-then-match.
//
// Mirrors the real STS_MAC_fix2 `AcceptedR` guard match (sent as
// per-argument equations, one for each fact position).  The guard
// pattern has ONE universal-bound var `kpartner` and several FREE
// system vars (`ekI`,`ekR`) that, after a prior guard's binding,
// occupy positions whose subject counterparts are DIFFERENT free
// system vars (`x`,`tid`).  Two equations:
//   eq1:  exp(g, ekI)  <=?  exp(g, x)     (pattern free ekI vs x)
//   eq2:  exp(g, ekR)  <=?  exp(g, tid)   (pattern free ekR vs tid)
// Skolemizing the subject side alone would leave the pattern's
// `ekI`,`ekR` as Maude VARIABLES, so Maude would bind `ekI->x`,
// `ekR->tid` and the match would SUCCEED — a spurious match that fires
// `gfalse` one step early.  Skolemizing both sides makes every free var
// a distinct CONSTANT, so `exp(g,c_ekI)` != `exp(g,c_x)` and the match
// FAILS, exactly as HS's `skolemizeGuarded`-then-`matchAction` does.
#[test]
fn impl_guard_match_skolemizes_pattern_free_vars() {
    let path = match require_maude_path() {
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
    let pattern_vars: std::collections::BTreeSet<(&'static str, u64)> =
        std::collections::BTreeSet::new();
    // skolemize_both: ekI,ekR,x,tid are distinct constants, so neither
    // equation can be satisfied → NO match, matching HS.
    let fixed = h.match_eqs_skolemize_both(&eqs, &pattern_vars).expect("m2");
    assert!(
        fixed.is_empty(),
        "skolemize_both must NOT over-match: pattern-side free system \
             vars (ekI,ekR) are CONSTANTS and cannot bind to the subject's \
             different free vars (x,tid); got {:?}",
        fixed
    );
}

/// Directional regression for the `match_eqs` `Equal` convention.
///
/// HS `matchWith t p = DelayedMatches [(t, p)]` (Term/Rewriting/Definitions.hs)
/// is `(subject, pattern)`, and `compareTermSubs t1 t2` (Subsumption.hs)
/// relies on that order: with `t1 = h(x)` (general) and `t2 = h(a)` (ground,
/// specific):
///   - `t1 matchWith t2` = subject h(x) vs pattern h(a): h(x)'s free var
///     sits in the SUBJECT (ground) slot, h(a) is the pattern with no vars
///     ⇒ No match (empty).
///   - `t2 matchWith t1` = subject h(a) vs pattern h(x): x --> a ⇒ matches.
///
/// Pins the directionality: `t matchWith p` is `Equal { lhs: t, rhs: p }`
/// (RS `Equal`'s HS-faithful subject,pattern order), not the
/// pattern,subject order used by `match_eqs_skolemize_both`.
#[test]
fn match_eqs_direction_matches_hs() {
    let path = match require_maude_path() {
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
    let matches = |subject: &LNTerm, pattern: &LNTerm| {
        hnd.match_eqs(&[Equal {
            lhs: subject.clone(),
            rhs: pattern.clone(),
        }])
        .expect("match")
    };
    // subject h(x), pattern h(a): the subject is ground to the matcher, so
    // nothing binds and there is no match.
    assert!(
        matches(&t_gen, &t_spec).is_empty(),
        "h(x) matchWith h(a) must not match: the subject's var cannot bind"
    );
    // subject h(a), pattern h(x): x --> a.
    assert!(
        !matches(&t_spec, &t_gen).is_empty(),
        "h(a) matchWith h(x) must match with x --> a"
    );
    // Terms equal modulo renaming match in both directions.
    let y = LVar::new("y", LSort::Msg, 1);
    let t_gen2 = crate::term::Term::App(FunSym::NoEq(h_sym), vec![mk(y)].into());
    assert!(!matches(&t_gen, &t_gen2).is_empty());
    assert!(!matches(&t_gen2, &t_gen).is_empty());
}

#[test]
fn cancellation_restarts_maude_before_a_concurrent_request_reuses_it() {
    let Some(path) = require_maude_path() else {
        return;
    };
    check_cancellation_restart(&path);
}

#[cfg(unix)]
#[test]
fn cancellation_restarts_maude_through_a_wrapper_with_inherited_pipes() {
    use std::os::unix::fs::PermissionsExt;
    let Some(path) = require_maude_path() else {
        return;
    };
    let temp = tempfile::tempdir().unwrap();
    let wrapper = temp.path().join("maude-wrapper");
    let quoted = path.replace("'", "'\"'\"'");
    std::fs::write(
        &wrapper,
        format!("#!/bin/sh\nexec 3<&0\n'{quoted}' \"$@\" <&3 &\nwait\n"),
    )
    .unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
    check_cancellation_restart(wrapper.to_str().unwrap());
}

fn check_cancellation_restart(path: &str) {
    use std::sync::mpsc;
    use std::time::Duration;
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    // A concurrent test can fork while the wrapper script is still open for
    // writing. Its child holds that descriptor until it execs (ETXTBSY).
    let handle = loop {
        match MaudeHandle::start_with_backend(path, pair_maude_sig(), AlgebraBackend::Maude) {
            Err(error) if error.to_string().contains("Text file busy") => {
                std::thread::sleep(Duration::from_millis(10));
            }
            started => break started.unwrap(),
        }
    };
    let old_pid = handle.child.lock().unwrap().child.as_ref().unwrap().id();
    handle
        .inner
        .lock()
        .execute(
            b"fmod CANCEL is sort S . op spin : -> S . eq spin = spin . endfm\n",
            0,
        )
        .unwrap();
    let token = CancellationToken::default();
    let owner_token = token.clone();
    let owner_handle = handle.clone();
    let (started_tx, started_rx) = mpsc::channel();
    let (done_tx, done_rx) = mpsc::channel();
    let owner = std::thread::spawn(move || {
        let _guard = CancellationGuard::new(Some(owner_token));
        let result = owner_handle.inner.lock().with_cancellation(|inner| {
            started_tx.send(()).unwrap();
            inner.execute_raw(b"reduce in CANCEL : spin .\n")
        });
        done_tx
            .send(matches!(result, Err(MaudeError::Cancelled)))
            .unwrap();
    });
    started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
    let other_handle = handle.clone();
    let other =
        std::thread::spawn(move || other_handle.reduce(&reducible_fst_pair("after_cancel", "b")));
    token.cancel();
    assert!(done_rx.recv_timeout(Duration::from_secs(5)).unwrap());
    owner.join().unwrap();
    let actual = other.join().unwrap().unwrap();
    let fresh =
        MaudeHandle::start_with_backend(path, pair_maude_sig(), AlgebraBackend::Maude).unwrap();
    assert_eq!(
        actual,
        fresh
            .reduce(&reducible_fst_pair("after_cancel", "b"))
            .unwrap()
    );
    let new_pid = handle.child.lock().unwrap().child.as_ref().unwrap().id();
    assert_ne!(old_pid, new_pid, "cancelled connection must be replaced");
    // A late repeat cancellation cannot kill the replacement subprocess.
    token.cancel();
    assert_eq!(
        handle.reduce(&reducible_fst_pair("next", "b")).unwrap(),
        fresh.reduce(&reducible_fst_pair("next", "b")).unwrap()
    );
}

#[test]
fn cancelling_a_maude_lock_waiter_does_not_interrupt_the_owner() {
    use std::sync::mpsc;
    use std::time::Duration;
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let lock = handle.inner.lock();
    let token = CancellationToken::default();
    let waiter_token = token.clone();
    let waiter_handle = handle.clone();
    let (done_tx, done_rx) = mpsc::channel();
    let waiter = std::thread::spawn(move || {
        let _guard = CancellationGuard::new(Some(waiter_token));
        done_tx
            .send(matches!(
                waiter_handle.reduce(&reducible_fst_pair("waiter", "b")),
                Err(MaudeError::Cancelled)
            ))
            .unwrap();
    });
    token.cancel();
    assert!(done_rx.recv_timeout(Duration::from_secs(5)).unwrap());
    waiter.join().unwrap();
    assert!(handle
        .child
        .lock()
        .unwrap()
        .child
        .as_mut()
        .unwrap()
        .try_wait()
        .unwrap()
        .is_none());
    drop(lock);
    assert!(handle.reduce(&reducible_fst_pair("owner", "b")).is_ok());
}

#[test]
fn deferred_cancellation_before_initialize_preserves_recovery() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle =
        MaudeHandle::start_with_backend(&path, pair_maude_sig(), AlgebraBackend::Maude).unwrap();
    let old_pid = handle.child.lock().unwrap().child.as_ref().unwrap().id();
    let token = CancellationToken::default();
    {
        let _guard = CancellationGuard::new(Some(token.clone()));
        let result = handle.inner.lock().with_cancellation(|inner| {
            // /kill signals after callback registration, but its deferred
            // cleanup has not run when initialize checks cancellation.
            token.request_cancel();
            inner.initialize()
        });
        assert!(matches!(result, Err(MaudeError::Cancelled)));
    }
    let fresh =
        MaudeHandle::start_with_backend(&path, pair_maude_sig(), AlgebraBackend::Maude).unwrap();
    assert_eq!(
        handle.reduce(&reducible_fst_pair("retry", "b")).unwrap(),
        fresh.reduce(&reducible_fst_pair("retry", "b")).unwrap()
    );
    let new_pid = handle.child.lock().unwrap().child.as_ref().unwrap().id();
    assert_ne!(old_pid, new_pid);
    // Even cleanup delayed until after the replacement is in use must not
    // kill it or make a subsequent request inherit the old cancellation.
    token.cancel();
    assert_eq!(
        handle.reduce(&reducible_fst_pair("next", "b")).unwrap(),
        fresh.reduce(&reducible_fst_pair("next", "b")).unwrap()
    );
    assert_eq!(
        new_pid,
        handle.child.lock().unwrap().child.as_ref().unwrap().id()
    );
}

#[test]
fn panicking_exchange_cannot_leave_a_reply_for_the_next_request() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle =
        MaudeHandle::start_with_backend(&path, pair_maude_sig(), AlgebraBackend::Maude).unwrap();
    let old_pid = handle.child.lock().unwrap().child.as_ref().unwrap().id();
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        handle.inner.lock().with_cancellation::<()>(|inner| {
            inner.initialize()?;
            inner.write_line(b"show modules .\n")?;
            panic!("abandon an exchange before reading its reply");
        })
    }));
    assert!(panic.is_err());
    assert!(handle.child.lock().unwrap().child.is_none());
    let result = handle
        .reduce(&reducible_fst_pair("after_panic", "b"))
        .expect("restart after panic");
    assert_eq!(
        result,
        crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(
            crate::lterm::NameTag::Pub,
            "after_panic"
        )))
    );
    let new_pid = handle.child.lock().unwrap().child.as_ref().unwrap().id();
    assert_ne!(old_pid, new_pid, "the interrupted process was replaced");
}

/// Proof search leases pool members with the calls that never wait
/// (`try_take_idle_owned`, `try_acquire_ready`). A native-only member has
/// no process to find running or to start: it is ready as it is, and
/// leasing it must not ask the session for a Maude exchange.
#[cfg(feature = "lean-unification")]
#[test]
fn a_native_only_pool_leases_ready_members_without_a_process() {
    let pool = Arc::new(
        MaudePool::new_with_backend(
            "/nonexistent/maude",
            pair_maude_sig(),
            2,
            Arc::new(SharedMaudeCaches::default()),
            AlgebraBackend::NativeOnly,
        )
        .unwrap(),
    );
    let first = pool
        .try_take_idle_owned()
        .expect("the first member is idle");
    let second = pool.try_acquire_ready().expect("a second member is made");
    assert!(pool.try_acquire_ready().is_none());
    assert!(pool.try_take_idle_owned().is_none());
    assert_eq!(pool.spawned(), 2);
    let term = reducible_fst_pair("a", "b");
    let reduced = first.reduce(&term).unwrap();
    assert_eq!(second.reduce(&term).unwrap(), reduced);
    drop(first);
    let again = pool.try_acquire_ready().expect("the returned member");
    assert_eq!(again.reduce(&term).unwrap(), reduced);
    assert_eq!(pool.try_acquire().map(|_| ()), None);
    again.check_backend_status().unwrap();
}

/// The session latch takes a failure only from a live job. A job whose
/// request is cancelled gets a cancellation and leaves the session intact,
/// whatever it ran into: its result is discarded at the job boundary.
#[test]
fn a_cancelled_job_latches_no_failure() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationScope, CancellationToken};
    let caches = Arc::new(SharedMaudeCaches::default());
    let request = CancellationToken::default();
    let job = CancellationScope::new(Some(request.clone()));
    {
        let _guard = CancellationGuard::new(Some(job.token()));
        request.request_cancel();
        let error = caches.fail(|| NativeFailure::Unsupported("matching"));
        assert!(matches!(error, MaudeError::Cancelled), "{error:?}");
    }
    assert!(caches.native_failure.get().is_none());
    let error = caches.fail(|| NativeFailure::Unsupported("matching"));
    assert!(matches!(
        error,
        MaudeError::UnsupportedOperation("matching")
    ));
    // The first failure stays the session's.
    let error = caches.fail(|| NativeFailure::Absorbed("later".into()));
    assert!(matches!(
        error,
        MaudeError::UnsupportedOperation("matching")
    ));
}

/// A parallel job that its caller may still discard holds its own failure.
/// The job fails from then on, its peers and the session do not, and the
/// session takes the failure over when the job's result is used.
#[test]
fn a_job_holds_its_failure_until_its_result_is_used() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationScope, CancellationToken};
    let caches = Arc::new(SharedMaudeCaches::default());
    let request = CancellationToken::default();
    let map = CancellationScope::new(Some(request.clone()));
    let used = CancellationScope::job(Some(map.token()));
    let discarded = CancellationScope::job(Some(map.token()));
    let peer = CancellationScope::job(Some(map.token()));
    {
        let _guard = CancellationGuard::new(Some(discarded.token()));
        let error = caches.fail(|| NativeFailure::Unsupported("matching"));
        assert!(matches!(
            error,
            MaudeError::UnsupportedOperation("matching")
        ));
        assert!(matches!(
            job_status(),
            Err(MaudeError::UnsupportedOperation("matching"))
        ));
    }
    {
        let _guard = CancellationGuard::new(Some(used.token()));
        job_status().unwrap();
        let error = caches.fail(|| NativeFailure::Absorbed("boom".into()));
        assert!(error.to_string().contains("boom"), "{error}");
        // The first failure stays the job's, and its nested work fails too.
        let error = caches.fail(|| NativeFailure::Absorbed("later".into()));
        assert!(error.to_string().contains("boom"), "{error}");
        let nested = CancellationScope::new(Some(used.token()));
        let _nested = CancellationGuard::new(Some(nested.token()));
        let error = job_status().unwrap_err().to_string();
        assert!(error.contains("boom"), "{error}");
    }
    {
        let _guard = CancellationGuard::new(Some(peer.token()));
        job_status().unwrap();
    }
    {
        let _guard = CancellationGuard::new(Some(request.clone()));
        job_status().unwrap();
    }
    job_status().unwrap();
    assert!(caches.native_failure.get().is_none());

    // The map hands on the failures of the jobs whose results it returns.
    drop(discarded);
    map.token().inherit(used.token().own_failure().unwrap());
    let latched = caches.native_failure.get().unwrap().error().to_string();
    assert!(latched.contains("boom"), "{latched}");
    // From then on a job gets the session's failure.
    let _guard = CancellationGuard::new(Some(peer.token()));
    let error = caches.fail(|| NativeFailure::Unsupported("matching"));
    assert!(error.to_string().contains("boom"), "{error}");
    assert!(peer.token().own_failure().is_none());
}

/// A failed job may have gone on with a placeholder, so nothing it computes
/// afterwards may reach the memos that other jobs read. Its backend calls
/// fail on entry. The exchange below the entry points, which has no such
/// check, still answers, and stores nothing.
#[test]
fn a_failed_job_writes_to_no_memo_of_a_maude_session() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationScope};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = crate::maude_sig::xor_maude_sig();
    let handle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let peer = handle.clone();
    let var = |name: &'static str| crate::term::Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let xor = |l: LNTerm, r: LNTerm| {
        crate::term::f_app_ac(crate::function_symbols::AcSym::Xor, vec![l, r])
    };
    let eqs = [Equal {
        lhs: xor(var("x"), var("a")),
        rhs: xor(var("b"), var("y")),
    }];
    // x + x + a reduces to a.
    let term = xor(xor(var("x"), var("x")), var("a"));
    let command = || {
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(&term, &mut ctx);
        let mut cmd = b"reduce ".to_vec();
        pp_mterm_into(&mt, &mut cmd);
        cmd.extend_from_slice(b" .\n");
        (cmd, ctx.variable_bound())
    };
    let stored = |handle: &MaudeHandle| {
        let caches = &handle.caches;
        (
            caches.reduce.lock().unwrap().len(),
            caches.unifiable.lock().unwrap().len(),
            caches.reply.lock().unwrap().len(),
        )
    };

    let job = CancellationScope::job(None);
    {
        let _guard = CancellationGuard::new(Some(job.token()));
        assert!(handle.absorb(Err(MaudeError::Other("boom".into())), || true));
        for error in [
            handle.reduce(&term).unwrap_err(),
            handle.unifiable(&eqs).unwrap_err(),
            handle.unify(&eqs).unwrap_err(),
            handle.has_match_eqs(&eqs).unwrap_err(),
            handle.check_backend_status().unwrap_err(),
        ] {
            assert!(error.to_string().contains("boom"), "{error}");
        }
        let (cmd, bound) = command();
        handle
            .execute_memo(&cmd, bound, Asked::Reduce, |_| {})
            .unwrap();
        assert_eq!(stored(&handle), (0, 0, 0));
    }
    // The session is intact, and intact work fills the memos.
    peer.check_backend_status().unwrap();
    handle.check_backend_status().unwrap();
    assert_eq!(peer.reduce(&term).unwrap(), var("a"));
    assert!(peer.unifiable(&eqs).unwrap());
    let (cmd, bound) = command();
    peer.execute_memo(&cmd, bound, Asked::Reduce, |_| {})
        .unwrap();
    let (reduced, unifiable, replies) = stored(&peer);
    assert_eq!((reduced, unifiable), (1, 1));
    assert!(replies >= 2, "{replies}");

    // The job's result is used after all.
    tamarin_utils::cancellation::inherit_failure(job.token().own_failure().unwrap());
    let latched = peer.check_backend_status().unwrap_err().to_string();
    assert!(latched.contains("boom"), "{latched}");
}

/// The same for the memos of a native-only session: the helpers below the
/// entry points answer a failed job and keep the answer out of the session.
#[cfg(feature = "lean-unification")]
#[test]
fn a_failed_job_writes_to_no_memo_of_a_native_session() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationScope};
    let sig = crate::maude_sig::xor_maude_sig();
    let handle =
        MaudeHandle::start_with_backend("/nonexistent/maude", sig, AlgebraBackend::NativeOnly)
            .unwrap();
    let peer = handle.clone();
    let var = |name: &'static str| crate::term::Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let xor = |l: LNTerm, r: LNTerm| {
        crate::term::f_app_ac(crate::function_symbols::AcSym::Xor, vec![l, r])
    };
    let eqs = [Equal {
        lhs: xor(var("x"), var("a")),
        rhs: xor(var("b"), var("y")),
    }];
    let term = xor(xor(var("x"), var("x")), var("a"));
    let stored = |handle: &MaudeHandle| {
        let caches = &handle.caches;
        [
            caches.reduce.lock().unwrap().len(),
            caches.unifiable.lock().unwrap().len(),
            caches.proved_unify.lock().unwrap().answers.len(),
            caches.total_match.lock().unwrap().len(),
            caches.has_match.lock().unwrap().len(),
            caches.variant_checks.lock().unwrap().len(),
            caches.unify_replies.size().0,
            caches.unify_replies.existence_replies(),
            usize::from(caches.reduction_table.lock().unwrap().is_some()),
        ]
    };
    let below_the_entry_points = |handle: &MaudeHandle| {
        // Each decision comes before the family that would answer it.
        assert!(handle.proved_unifiable(&eqs).unwrap());
        assert!(handle
            .proved_has_match(&eqs, Bindable::All, "matching")
            .unwrap());
        assert!(handle.total_match(&eqs, Bindable::All).unwrap().is_some());
        assert!(handle.reduction_table().unwrap().is_some());
        assert_eq!(handle.proved_reduce(&term).unwrap().0, var("a"));
    };

    let job = CancellationScope::job(None);
    {
        let _guard = CancellationGuard::new(Some(job.token()));
        assert!(handle.absorb(Err(MaudeError::Other("boom".into())), || true));
        for error in [
            handle.reduce(&term).unwrap_err(),
            handle.unifiable(&eqs).unwrap_err(),
            handle.unify(&eqs).unwrap_err(),
            handle.has_match_eqs(&eqs).unwrap_err(),
            handle.variants(&term).unwrap_err(),
        ] {
            assert!(error.to_string().contains("boom"), "{error}");
        }
        below_the_entry_points(&handle);
        assert_eq!(stored(&handle), [0; 9]);
    }
    peer.check_backend_status().unwrap();
    below_the_entry_points(&peer);
    assert_eq!(peer.reduce(&term).unwrap(), var("a"));
    assert!(!peer.unify(&eqs).unwrap().is_empty());
    assert!(!peer.variants(&term).unwrap().is_empty());
    let filled = stored(&peer);
    assert!(filled.iter().all(|entries| *entries > 0), "{filled:?}");
    peer.check_backend_status().unwrap();
}

/// Callers without an error channel absorb a backend error and continue
/// with a placeholder. The session latch must then fail every handle, while
/// a cancellation (or an error seen by an already cancelled request) is not
/// a backend failure.
#[test]
fn absorbed_backend_errors_latch_and_cancellation_does_not() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle =
        MaudeHandle::start_with_backend(&path, pair_maude_sig(), AlgebraBackend::Maude).unwrap();
    let clone = handle.clone();
    handle.check_backend_status().unwrap();

    assert_eq!(handle.absorb(Ok(1), || 2), 1);
    assert_eq!(handle.absorb(Err(MaudeError::Cancelled), || 2), 2);
    {
        let token = CancellationToken::default();
        token.request_cancel();
        let _guard = CancellationGuard::new(Some(token));
        handle.record_failure(&MaudeError::Other("collateral".into()));
    }
    clone.check_backend_status().unwrap();

    assert_eq!(
        handle.absorb(Err(MaudeError::Other("boom".into())), || 2),
        2
    );
    let latched = clone.check_backend_status().unwrap_err().to_string();
    assert!(latched.contains("boom"), "{latched}");
    // The first failure is the one reported.
    handle.record_failure(&MaudeError::Other("later".into()));
    let latched = handle.check_backend_status().unwrap_err().to_string();
    assert!(latched.contains("boom"), "{latched}");
}

/// The normal-form predicate has no error channel: with the backend gone its
/// AC match cannot be answered, and the placeholder must not go unnoticed.
#[test]
fn a_failed_normal_form_match_latches_the_session() {
    use crate::function_symbols::{AcSym, FunSym};
    use crate::term::Term;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = crate::maude_sig::xor_maude_sig();
    let handle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |name: &'static str| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let xor = |args: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::Xor), args.into());
    let lhs = xor(vec![var("x"), var("y")]);
    let subject = xor(vec![var("a"), var("b")]);
    handle.kill_subprocess();
    let answer = handle.absorb(
        handle.has_match_eqs(&[Equal {
            lhs: subject,
            rhs: lhs,
        }]),
        || false,
    );
    assert!(!answer);
    assert!(handle.check_backend_status().is_err());
}

/// Native-only uses a family of a Rust variant solver only after the Lean
/// certificate checker accepted it.
#[cfg(feature = "lean-unification")]
mod variant_check {
    use super::*;
    use crate::algebra_provenance::{Command, Origin};
    use crate::builtin::{fst, pair};
    use crate::lean_unification::Substitutions;
    use crate::term::{f_app_list, Term};

    fn var(name: &'static str, idx: u64) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)))
    }

    fn native(sig: MaudeSig) -> MaudeHandle {
        MaudeHandle::start_with_backend("/nonexistent/maude", sig, AlgebraBackend::NativeOnly)
            .unwrap()
    }

    fn tampered(sig: MaudeSig, tamper: fn(&mut Substitutions)) -> MaudeHandle {
        let mut h = native(sig);
        h.set_variant_check(0, Some(tamper));
        h
    }

    fn refusal(result: Result<Substitutions, MaudeError>) -> String {
        match result {
            Err(MaudeError::NativeFailure(reason)) => reason,
            other => panic!("expected a refused family, got {other:?}"),
        }
    }

    /// fst(x) and x: the identity and x := pair(y, z).
    fn projection() -> LNTerm {
        f_app_list(vec![fst(var("x", 0)), var("x", 0)])
    }

    #[test]
    fn an_accepted_family_counts_as_proved_and_is_checked_once() {
        let query = projection();
        let h = native(pair_maude_sig());
        let proposed = h.variants(&query).unwrap();
        assert_eq!(proposed.len(), 2, "{proposed:?}");
        let seen = h.provenance();
        assert_eq!(seen.fresh(Command::Variants, Origin::Proved), 1);
        assert_eq!(seen.total(Command::Variants), 1);
        // The verdict on the same query and family comes from the memo, also
        // through another handle of the session.
        assert_eq!(h.variants(&query).unwrap(), proposed);
        assert_eq!(
            h.with_fresh_counter_from(40).variants(&query).unwrap(),
            proposed
        );
        let seen = h.provenance();
        assert_eq!(seen.fresh(Command::Variants, Origin::Proved), 1);
        assert_eq!(seen.cached(Command::Variants, Origin::Proved), 2);
        assert_eq!(seen.total(Command::Variants), 3);
        assert_eq!(h.caches.variant_checks.lock().unwrap().len(), 1);
        h.check_backend_status().unwrap();
    }

    #[test]
    fn a_range_variable_spelled_like_a_query_variable_is_still_fresh() {
        // y := pair(x, z) for the query (fst(y), x): the x of the image is a
        // fresh variable, not the x of the query, which keeps itself.
        fn respell(family: &mut Substitutions) {
            use crate::lterm::HasFrees;
            let x = LVar::new("x", LSort::Msg, 0);
            for member in family.iter_mut() {
                member.retain(|(key, _)| *key != x);
                for (_, image) in member.iter_mut() {
                    if let Term::App(_, children) = &*image
                        && let Term::Lit(Lit::Var(first)) = children[0]
                    {
                        *image = image
                            .clone()
                            .map_free(&mut |v| if v == first { x } else { v });
                    }
                }
            }
        }
        let query = f_app_list(vec![fst(var("y", 1)), var("x", 0)]);
        let h = tampered(pair_maude_sig(), respell);
        let family = h.variants(&query).unwrap();
        let x = LVar::new("x", LSort::Msg, 0);
        assert!(
            family.iter().flatten().any(|(key, image)| {
                *key != x
                    && !matches!(image, Term::Lit(_))
                    && crate::lterm::frees(image).contains(&x)
            }),
            "{family:?}"
        );
        assert_eq!(
            h.provenance().fresh(Command::Variants, Origin::Proved),
            1,
            "{family:?}"
        );
    }

    #[test]
    fn a_corrupted_family_is_rejected_with_its_reason_and_fails_the_session() {
        let query = projection();
        // Without the instance x := pair(y, z) a narrowing successor of the
        // identity is uncovered; without the identity nothing covers the query.
        fn keep_identity(family: &mut Substitutions) {
            family.retain(|member| {
                member
                    .iter()
                    .all(|(_, image)| matches!(image, Term::Lit(_)))
            });
            assert_eq!(family.len(), 1);
        }
        fn drop_identity(family: &mut Substitutions) {
            family.retain(|member| {
                member
                    .iter()
                    .any(|(_, image)| !matches!(image, Term::Lit(_)))
            });
            assert_eq!(family.len(), 1);
        }
        // A reducible image is not a variant at all.
        fn reducible(family: &mut Substitutions) {
            let last = family.len() - 1;
            let x = LVar::new("x", LSort::Msg, 0);
            let w = |i| Term::Lit(Lit::Var(LVar::new("w", LSort::Msg, i)));
            family[last] = vec![(x, fst(pair(w(7), w(8))))];
        }
        for (tamper, expected) in [
            (
                keep_identity as fn(&mut Substitutions),
                "member 0 is not covered (reason 3)",
            ),
            (drop_identity, "no member subsumes the query (reason 2"),
            (reducible, "member 1 is not normal (reason 1)"),
        ] {
            let h = tampered(pair_maude_sig(), tamper);
            let reason = refusal(h.variants(&query));
            assert!(reason.contains("rejected"), "{reason}");
            assert!(reason.contains(expected), "{reason}");
            // The rejected family is not counted as an answer and not stored,
            // and the session cannot publish a result any more.
            assert_eq!(h.provenance().total(Command::Variants), 0);
            assert!(h.caches.variant_checks.lock().unwrap().is_empty());
            assert!(h.check_backend_status().is_err());
            assert!(h.variants(&query).is_err());
        }
    }

    /// `f(g(x)) -> x` with `g(a) -> b` is not confluent, so the certifier
    /// does not accept the table. The checker still accepts the family of
    /// the projection, and that it is complete rests on the theory premise.
    #[test]
    fn an_accepted_family_on_an_uncertified_table_counts_as_assumed() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        use crate::rewriting::RRule;
        use crate::subterm_rule::rrule_to_ctxt_st_rule;
        use crate::term::f_app_no_eq;
        let sym = |name: &[u8], arity| {
            NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
        };
        let (f, g, a, b) = (sym(b"f", 1), sym(b"g", 1), sym(b"a", 0), sym(b"b", 0));
        let x = var("x", 0);
        let mut sig = pair_maude_sig();
        sig.st_fun_syms.extend([f, g, a, b]);
        for rule in [
            RRule::new(f_app_no_eq(f, vec![f_app_no_eq(g, vec![x.clone()])]), x),
            RRule::new(
                f_app_no_eq(g, vec![f_app_no_eq(a, vec![])]),
                f_app_no_eq(b, vec![]),
            ),
        ] {
            sig.st_rules.insert(rrule_to_ctxt_st_rule(&rule).unwrap());
        }
        let sig = sig.refresh();
        let query = projection();
        let h = MaudeHandle::start_for_tamarin_theory(
            "/nonexistent/maude",
            sig.clone(),
            AlgebraBackend::NativeOnly,
            Arc::new(SharedMaudeCaches::default()),
        )
        .unwrap();
        let proposed = h.variants(&query).unwrap();
        assert_eq!(proposed.len(), 2, "{proposed:?}");
        assert_eq!(h.variants(&query).unwrap(), proposed);
        let seen = h.provenance();
        assert_eq!(seen.fresh(Command::Variants, Origin::Assumed), 1);
        assert_eq!(seen.cached(Command::Variants, Origin::Assumed), 1);
        assert_eq!(seen.fresh(Command::Variants, Origin::Proved), 0);
        assert_eq!(seen.total(Command::Variants), 2);
        assert!(!h
            .caches
            .reduction_table
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .as_ref()
            .unwrap()
            .certified());
        h.check_backend_status().unwrap();
    }

    /// fst(fst(x)): the identity, x := pair(y, z) and x := pair(pair(y, z), w).
    fn nested_projection() -> LNTerm {
        fst(fst(var("x", 0)))
    }

    /// The charge of a family, as the checker's work bound counts it.
    fn charge(h: &MaudeHandle, query: &LNTerm, family: &Substitutions) -> u64 {
        let table = h.reduction_table().unwrap().unwrap();
        table.variant_check_charge(query, family).unwrap().unwrap()
    }

    #[test]
    fn an_undecided_check_fails_the_session_instead_of_using_the_rust_family() {
        // The work bound counts the positions that are not variables in the
        // normalized observations of each member, in the order of the
        // family: here fst(fst(x)) for the identity, fst(y) for the next
        // member and none for the last, so three in all.
        let query = nested_projection();
        let unbounded = {
            let mut h = native(pair_maude_sig());
            h.set_variant_check(0, None);
            h
        };
        let family = unbounded.variants(&query).unwrap();
        assert_eq!(family.len(), 3, "{family:?}");
        assert_eq!(charge(&unbounded, &query, &family), 3);
        // A bound that the family does not fit in stops the check out of
        // budget, on the first member or after it.
        for work in [1, 2] {
            let mut h = native(pair_maude_sig());
            h.set_variant_check(work, None);
            let reason = refusal(h.variants(&query));
            assert!(reason.contains("variants not certified"), "{reason}");
            assert!(reason.contains("out of budget"), "{reason}");
            assert!(reason.contains(&format!("work bound {work} ")), "{reason}");
            assert_eq!(h.provenance().total(Command::Variants), 0);
            assert!(h.caches.variant_checks.lock().unwrap().is_empty());
            assert!(h.check_backend_status().is_err());
            assert!(h.variants(&query).is_err());
        }
        // The bound that the family just fits in changes nothing.
        let mut h = native(pair_maude_sig());
        h.set_variant_check(3, None);
        assert_eq!(h.variants(&query).unwrap(), family);
        assert_eq!(h.provenance().fresh(Command::Variants, Origin::Proved), 1);
        h.check_backend_status().unwrap();
    }
}

const SPIN_MODULE: &[u8] = b"fmod CANCEL is sort S . op spin : -> S . eq spin = spin . endfm\n";
const SPIN: &[u8] = b"reduce in CANCEL : spin .\n";

fn child_pid(handle: &MaudeHandle) -> Option<u32> {
    handle.child.lock().unwrap().child.as_ref().map(Child::id)
}

/// `try_map_until` on a pool of its own, so that jobs that meet at a barrier
/// each have a worker whatever the size of the global pool.
fn map_until<I, T>(
    items: Vec<I>,
    work: impl Fn(I) -> Result<T, MaudeError> + Sync + Send + 'static,
    stop: impl Fn(&T) -> bool + Sync + Send + 'static,
) -> Result<Vec<T>, MaudeError>
where
    I: Send + 'static,
    T: Send + 'static,
{
    let token = tamarin_utils::cancellation::current();
    rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap()
        .install(move || {
            let _guard = tamarin_utils::cancellation::CancellationGuard::new(token);
            tamarin_utils::parallel::try_map_until(items, work, stop)
        })
}

#[test]
fn an_earlier_job_takes_the_process_from_a_later_one_stuck_in_maude() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let old_pid = child_pid(&handle);
    let holding = std::sync::Arc::new(std::sync::Barrier::new(2));
    let shared = handle.clone();
    let results = map_until(
        vec![0, 1],
        move |index| -> Result<Vec<u8>, MaudeError> {
            if index == 1 {
                // The replacement process has no CANCEL module, so the
                // repeated command returns at once.
                let mut inner = shared.lock_inner()?;
                holding.wait();
                inner.execute(SPIN, 0)
            } else {
                holding.wait();
                shared
                    .reduce(&reducible_fst_pair("earlier", "b"))
                    .map(|_| Vec::new())
            }
        },
        |_| false,
    )
    .unwrap();
    assert_eq!(results.len(), 2);
    assert_ne!(
        old_pid,
        child_pid(&handle),
        "the stuck process was replaced"
    );
}

#[test]
fn a_later_job_waits_for_an_earlier_one_in_maude() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let old_pid = child_pid(&handle);
    let holding = std::sync::Arc::new(std::sync::Barrier::new(2));
    let token = CancellationToken::default();
    let shared = handle.clone();
    let request = token.clone();
    let map = std::thread::spawn(move || {
        let _guard = CancellationGuard::new(Some(request));
        map_until(
            vec![0, 1],
            move |index| -> Result<(), MaudeError> {
                if index == 0 {
                    let mut inner = shared.lock_inner()?;
                    holding.wait();
                    inner.execute(SPIN, 0).map(|_| ())
                } else {
                    holding.wait();
                    shared.reduce(&reducible_fst_pair("later", "b")).map(|_| ())
                }
            },
            |_| false,
        )
    });
    std::thread::sleep(handle.turn.interrupt_after() * 4);
    assert!(!map.is_finished());
    assert_eq!(
        old_pid,
        child_pid(&handle),
        "the earlier job kept its process"
    );
    token.cancel();
    assert!(matches!(map.join().unwrap(), Err(MaudeError::Cancelled)));
}

#[test]
fn an_interrupted_job_stays_away_while_the_earlier_one_keeps_working() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    // Every replacement process can spin as well.
    *handle.turn.preamble.lock().unwrap() = SPIN_MODULE.to_vec();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let holding = std::sync::Arc::new(std::sync::Barrier::new(2));
    let shared = handle.clone();
    let patience = handle.turn.interrupt_after();
    let results = map_until(
        vec![0, 1],
        move |index| -> Result<std::time::Duration, MaudeError> {
            if index == 1 {
                let mut inner = shared.lock_inner()?;
                holding.wait();
                inner.execute(SPIN, 0).map(|_| Default::default())
            } else {
                holding.wait();
                let started = std::time::Instant::now();
                // Long enough for the spinning job to come back more than once.
                while started.elapsed() < patience * 6 {
                    drop(shared.lock_inner()?);
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
                let mut waited = std::time::Duration::ZERO;
                for _ in 0..3 {
                    std::thread::sleep(patience / 4);
                    let before = std::time::Instant::now();
                    drop(shared.lock_inner()?);
                    waited += before.elapsed();
                }
                Ok(waited)
            }
        },
        |_| true,
    )
    .unwrap();
    // Without backing off, each of the three late locks waits out a fresh spin.
    assert!(results[0] < patience, "waited {:?}", results[0]);
}

// Run a map on its own thread and report whether it finished unaided.
/// Whether `map` returns by itself in good time. One that does not is
/// cancelled; if even that does not end it, its thread is left behind with
/// the process killed, so that the test fails instead of hanging.
fn finishes<T: Send + 'static>(
    handle: &MaudeHandle,
    map: impl FnOnce() -> Result<T, MaudeError> + Send + 'static,
) -> bool {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let token = CancellationToken::default();
    let request = token.clone();
    let map = std::thread::spawn(move || {
        let _guard = CancellationGuard::new(Some(request));
        map()
    });
    let ends_within = |limit: std::time::Duration| {
        let deadline = std::time::Instant::now() + limit;
        while !map.is_finished() && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        map.is_finished()
    };
    let finished = ends_within(handle.turn.interrupt_after() * 40);
    token.cancel();
    if ends_within(std::time::Duration::from_secs(10)) {
        let _ = map.join().unwrap();
    } else {
        handle.kill_subprocess();
    }
    finished
}

#[test]
fn an_interrupted_job_takes_the_process_back_from_a_later_one() {
    use std::sync::{mpsc, Arc, Barrier, Mutex};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let holding = Arc::new(Barrier::new(2));
    let (first_done, after_first) = mpsc::channel::<()>();
    let (first_done, after_first) = (Mutex::new(first_done), Mutex::new(after_first));
    let shared = handle.clone();
    assert!(finishes(&handle, move || {
        map_until(
            vec![0, 1, 2],
            move |index| -> Result<(), MaudeError> {
                match index {
                    0 => {
                        holding.wait();
                        shared.reduce(&reducible_fst_pair("earlier", "b"))?;
                        first_done.lock().unwrap().send(()).unwrap();
                    }
                    // Interrupted by the first job.
                    1 => {
                        let mut inner = shared.lock_inner()?;
                        holding.wait();
                        inner.execute(SPIN, 0)?;
                    }
                    // Takes the process while the second job stays away.
                    _ => {
                        after_first.lock().unwrap().recv().unwrap();
                        let mut inner = shared.lock_inner()?;
                        inner.execute(SPIN_MODULE, 0)?;
                        inner.execute(SPIN, 0)?;
                    }
                }
                Ok(())
            },
            |_| false,
        )
    }));
}

#[test]
fn a_cut_job_that_was_interrupted_does_not_wait_for_the_process() {
    use std::sync::{mpsc, Arc, Barrier, Mutex};
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let holding = Arc::new(Barrier::new(2));
    let (first_done, after_first) = mpsc::channel::<()>();
    let (taken, is_taken) = mpsc::channel::<()>();
    let (first_done, is_taken) = (Mutex::new(first_done), Mutex::new(is_taken));
    // A job outside every map has no rank, so no job can interrupt it.
    let stop_outsider = CancellationToken::default();
    let (outsider_handle, request) = (handle.clone(), stop_outsider.clone());
    let outsider = std::thread::spawn(move || -> Result<(), MaudeError> {
        let _guard = CancellationGuard::new(Some(request));
        let _ = after_first.recv_timeout(std::time::Duration::from_secs(5));
        let mut inner = outsider_handle.lock_inner()?;
        taken.send(()).unwrap();
        inner.execute(SPIN_MODULE, 0)?;
        inner.execute(SPIN, 0).map(|_| ())
    });
    let shared = handle.clone();
    // The first job ends the map while the interrupted second one is
    // waiting to take the process back from the outsider.
    assert!(finishes(&handle, move || {
        map_until(
            vec![0, 1],
            move |index| -> Result<bool, MaudeError> {
                if index == 1 {
                    let mut inner = shared.lock_inner()?;
                    holding.wait();
                    return inner.execute(SPIN, 0).map(|_| false);
                }
                holding.wait();
                shared.reduce(&reducible_fst_pair("earlier", "b"))?;
                first_done.lock().unwrap().send(()).unwrap();
                is_taken
                    .lock()
                    .unwrap()
                    .recv_timeout(std::time::Duration::from_secs(5))
                    .unwrap();
                Ok(true)
            },
            |solved| *solved,
        )
    }));
    stop_outsider.cancel();
    assert!(matches!(
        outsider.join().unwrap(),
        Err(MaudeError::Cancelled)
    ));
}

#[test]
fn the_interrupting_job_gets_the_process_before_a_later_waiter() {
    use std::sync::{Arc, Barrier, Mutex};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let holding = Arc::new(Barrier::new(3));
    let order = Arc::new(Mutex::new(Vec::new()));
    let (shared, served) = (handle.clone(), order.clone());
    map_until(
        vec![0, 1, 2],
        move |index| -> Result<(), MaudeError> {
            if index == 1 {
                let mut inner = shared.lock_inner()?;
                holding.wait();
                return inner.execute(SPIN, 0).map(|_| ());
            }
            holding.wait();
            if index == 0 {
                // The later job is already waiting when this one arrives.
                std::thread::sleep(std::time::Duration::from_millis(50));
            }
            shared.reduce(&reducible_fst_pair(&format!("job{index}"), "b"))?;
            served.lock().unwrap().push(index);
            Ok(())
        },
        |()| false,
    )
    .unwrap();
    assert_eq!(*order.lock().unwrap(), [0, 2]);
}

#[test]
fn a_waiting_builder_uses_the_rank_an_earlier_job_lends_it() {
    use std::sync::{mpsc, Arc, Barrier, Mutex};
    use tamarin_utils::parallel::SharedOnce;
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    handle.inner.lock().execute(SPIN_MODULE, 0).unwrap();
    let value = Arc::new(SharedOnce::<LNTerm>::default());
    let holding = Arc::new(Barrier::new(2));
    let (building, is_building) = mpsc::channel::<()>();
    let (building, is_building) = (Mutex::new(building), Mutex::new(is_building));
    let shared = handle.clone();
    assert!(finishes(&handle, move || {
        map_until(
            vec![0, 1, 2],
            move |index| -> Result<(), MaudeError> {
                let build = || shared.reduce(&reducible_fst_pair("built", "b"));
                match index {
                    // Needs the value only once the last job is already
                    // waiting for the process to build it.
                    0 => {
                        is_building.lock().unwrap().recv().unwrap();
                        std::thread::sleep(std::time::Duration::from_millis(50));
                        value.get_or_try_init(build)?;
                    }
                    1 => {
                        let mut inner = shared.lock_inner()?;
                        holding.wait();
                        inner.execute(SPIN, 0)?;
                    }
                    _ => {
                        holding.wait();
                        value.get_or_try_init(|| {
                            building.lock().unwrap().send(()).unwrap();
                            build()
                        })?;
                    }
                }
                Ok(())
            },
            |()| false,
        )
    }));
}

#[test]
fn a_cancelled_job_gets_no_cached_reply() {
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let term = reducible_fst_pair("cached", "b");
    handle.reduce(&term).unwrap();
    handle.variants(&term).unwrap();
    let token = CancellationToken::default();
    token.cancel();
    let _guard = CancellationGuard::new(Some(token));
    assert!(matches!(handle.reduce(&term), Err(MaudeError::Cancelled)));
    assert!(matches!(handle.variants(&term), Err(MaudeError::Cancelled)));
}
