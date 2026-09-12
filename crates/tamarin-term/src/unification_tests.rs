// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::builtin::{msg_var, pair, pk};
use crate::lterm::LNTerm;

#[test]
fn unify_two_distinct_variables() {
    let x: LNTerm = msg_var("x", 0);
    let y: LNTerm = msg_var("y", 0);
    let s = unify_lnterm_no_ac(vec![Equal::new(x.clone(), y)]).unwrap();
    // HS `unifyRaw` orients a var-var pair of the same sort by `Ord LVar`
    // (Unification.hs:276).  The index and the sort are equal here, so the
    // comparison falls to the name.  `unifyRaw` therefore eliminates the later
    // name, and that name becomes the key.  A check that the substitution is
    // not empty accepts either orientation.
    assert_eq!(
        s.to_list(),
        vec![(crate::lterm::LVar::new("y", LSort::Msg, 0), x)]
    );
}

#[test]
fn unify_var_with_term() {
    let x: LNTerm = msg_var("x", 0);
    let p: LNTerm = pair(msg_var("a", 0), msg_var("b", 0));
    let s = unify_lnterm_no_ac(vec![Equal::new(x.clone(), p.clone())]).unwrap();
    assert_eq!(apply_vterm(&s, x), p);
}

#[test]
fn unify_fails_on_constructor_mismatch() {
    // pair(x,y) vs pk(x): can't unify, different constructors.
    let lhs: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
    let rhs: LNTerm = pk(msg_var("z", 0));
    assert!(unify_lnterm_no_ac(vec![Equal::new(lhs, rhs)]).is_err());
}

#[test]
fn unify_occurs_check() {
    // x = pair(x, y) — should fail (x occurs in RHS).
    let x: LNTerm = msg_var("x", 0);
    let rhs: LNTerm = pair(x.clone(), msg_var("y", 0));
    assert!(unify_lnterm_no_ac(vec![Equal::new(x, rhs)]).is_err());
}

#[test]
fn match_pattern_variable_against_constant_term() {
    // Match: term=pair(a,b), pattern=pair(x,y).
    let t: LNTerm = pair(msg_var("a", 0), msg_var("b", 0));
    let p: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
    let problem = Match::match_with(t, p);
    let s = solve_match_lterm_no_ac(&|n| crate::lterm::sort_of_name(n), problem).unwrap();
    // Each pattern variable is the key.  Each key maps to the subject term at
    // its own argument position.  A count of the bindings alone does not see a
    // swap of the two.
    assert_eq!(
        s.to_list(),
        vec![
            (crate::lterm::LVar::new("x", LSort::Msg, 0), msg_var("a", 0)),
            (crate::lterm::LVar::new("y", LSort::Msg, 0), msg_var("b", 0)),
        ]
    );
}

#[test]
fn match_fails_on_different_arity() {
    let t: LNTerm = pk(msg_var("a", 0));
    let p: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
    let problem = Match::match_with(t, p);
    assert!(solve_match_lterm_no_ac(&|n| crate::lterm::sort_of_name(n), problem).is_none());
}

// -------------------------------------------------------------------
// HS `unifyRaw` AC/C arms (Unification.hs:299-308): the AC arm fires
// only when BOTH sides are AC apps with the SAME symbol; otherwise the
// pair falls through to `_ -> mzero` (no unifier).  These pin that the AC
// arm delays/NeedsAC only for same-symbol AC apps on both sides.
// -------------------------------------------------------------------
use crate::builtin::{mult, union};

#[test]
fn factored_unify_distinct_ac_symbols_is_no_unifier() {
    // mult(a,b) vs union(c,d): different AC symbols → HS `mzero`.
    let lhs: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let rhs: LNTerm = union(msg_var("c", 0), msg_var("d", 0));
    assert!(
        unify_lnterm_factored(vec![Equal::new(lhs, rhs)]).is_none(),
        "different AC symbols (mult vs union) must yield no unifier, \
                 not a residual shipped to Maude"
    );
}

#[test]
fn factored_unify_ac_vs_non_ac_is_no_unifier() {
    // mult(a,b) vs pk(x): AC-vs-NoEq → falls through to HS `_ -> mzero`.
    let lhs: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let rhs: LNTerm = pk(msg_var("x", 0));
    assert!(
        unify_lnterm_factored(vec![Equal::new(lhs, rhs)]).is_none(),
        "AC vs non-AC must yield no unifier (HS mzero), not a residual"
    );
}

#[test]
fn factored_unify_same_ac_symbol_delays_residual() {
    // mult(a,b) vs mult(c,d): same AC symbol → HS `tell [Equal l r]`,
    // i.e. a single residual delayed for Maude, with an empty local subst.
    let lhs: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let rhs: LNTerm = mult(msg_var("c", 0), msg_var("d", 0));
    let (subst, residuals) = unify_lnterm_factored(vec![Equal::new(lhs, rhs)])
        .expect("same AC symbol must delay (Some), not fail");
    assert!(subst.is_empty(), "no non-AC bindings");
    assert_eq!(
        residuals.len(),
        1,
        "exactly one AC equation delayed for Maude"
    );
}

#[test]
fn no_ac_distinct_ac_symbols_is_no_unifier_not_needs_ac() {
    // HS no-AC path: a guard failure → Nothing → [] (no unifier).
    let lhs: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let rhs: LNTerm = union(msg_var("c", 0), msg_var("d", 0));
    match unify_lnterm_no_ac(vec![Equal::new(lhs, rhs)]) {
        Err(UnifyError::NoUnifier) => {}
        other => panic!("expected NoUnifier (HS mzero), got {:?}", other),
    }
}

#[test]
fn no_ac_ac_vs_non_ac_is_no_unifier_not_needs_ac() {
    let lhs: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let rhs: LNTerm = pk(msg_var("x", 0));
    match unify_lnterm_no_ac(vec![Equal::new(lhs, rhs)]) {
        Err(UnifyError::NoUnifier) => {}
        other => panic!("expected NoUnifier (HS mzero), got {:?}", other),
    }
}

#[test]
fn no_ac_same_ac_symbol_is_needs_ac() {
    // Same AC symbol → HS `tell` → no-AC `solve (Just _)` "AC symbol
    // found" error, surfaced here as NeedsAC.
    let lhs: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let rhs: LNTerm = mult(msg_var("c", 0), msg_var("d", 0));
    match unify_lnterm_no_ac(vec![Equal::new(lhs, rhs)]) {
        Err(UnifyError::NeedsAC) => {}
        other => panic!("expected NeedsAC (HS AC symbol found), got {:?}", other),
    }
}

// -------------------------------------------------------------------
// `solve_match_lterm` 3-way outcome (HS `solveMatchLTerm`,
// Unification.hs:219-239).  These pin the exact distinction that
// eliminates the LAK06 (28 879→0) / NAXOS / CRxor surplus Maude
// `match`es: an AC-/C-headed subterm only forces a Maude fallback
// when it appears AC-vs-AC; under a variable pattern, or facing a
// variable subject, it resolves natively (Matched / NoMatcher).
// -------------------------------------------------------------------
fn sn(n: &crate::lterm::Name) -> LSort {
    crate::lterm::sort_of_name(n)
}

#[test]
fn match_ac_subterm_under_var_pattern_is_matched_no_maude() {
    // pattern = x (var), subject = mult(a,b) (AC-headed).  HS
    // `matchRaw` checks `(_, Lit (Var vp))` FIRST → binds, no AC.
    let t: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let p: LNTerm = msg_var("x", 0);
    match solve_match_lterm(&sn, Match::match_with(t, p)) {
        MatchOutcome::Matched(s) => assert_eq!(s.len(), 1),
        o => panic!(
            "expected Matched, got {:?}",
            match o {
                MatchOutcome::NoMatcher => "NoMatcher",
                _ => "NeedsAc",
            }
        ),
    }
}

#[test]
fn match_ac_pattern_vs_var_subject_is_no_matcher_not_needs_ac() {
    // pattern = mult(a,b) (AC), subject = x (var).  Subject is a Lit
    // Var, NOT an FApp(AC) — HS reaches `_ -> NoMatcher`, not the
    // AC arm (which needs BOTH sides AC-headed).  This is the exact
    // LAK06 shape (`Xor(..)` pattern vs `k.0` var subject): the AC-headed
    // pattern facing a var subject is NoMatcher, never a Maude fallback.
    let t: LNTerm = msg_var("x", 0);
    let p: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    match solve_match_lterm(&sn, Match::match_with(t, p)) {
        MatchOutcome::NoMatcher => {}
        MatchOutcome::Matched(_) => panic!("expected NoMatcher, got Matched"),
        MatchOutcome::NeedsAc => panic!("expected NoMatcher, got NeedsAc"),
    }
}

#[test]
fn match_same_ac_symbol_both_sides_is_needs_ac() {
    // mult(a,b) vs mult(c,d): genuine AC-vs-AC → HS `ACProblem`.
    let t: LNTerm = mult(msg_var("a", 0), msg_var("b", 0));
    let p: LNTerm = mult(msg_var("c", 0), msg_var("d", 0));
    match solve_match_lterm(&sn, Match::match_with(t, p)) {
        MatchOutcome::NeedsAc => {}
        MatchOutcome::Matched(_) => panic!("expected NeedsAc, got Matched"),
        MatchOutcome::NoMatcher => panic!("expected NeedsAc, got NoMatcher"),
    }
}

#[test]
fn match_ac_subterm_under_noeq_with_clash_is_no_matcher() {
    // pk(mult(a,b)) vs pk(x): the AC subterm faces a var PATTERN →
    // bound natively → Matched (no Maude), proving the AC op deep in
    // the subject doesn't force a fallback when the pattern is a var.
    let t: LNTerm = pk(mult(msg_var("a", 0), msg_var("b", 0)));
    let p: LNTerm = pk(msg_var("x", 0));
    match solve_match_lterm(&sn, Match::match_with(t, p)) {
        MatchOutcome::Matched(s) => assert_eq!(s.len(), 1),
        _ => panic!("expected Matched"),
    }
    // ...but pk(x) vs pair(a,b): head clash → NoMatcher, no Maude.
    let t2: LNTerm = pk(msg_var("x", 0));
    let p2: LNTerm = pair(msg_var("a", 0), msg_var("b", 0));
    assert!(matches!(
        solve_match_lterm(&sn, Match::match_with(t2, p2)),
        MatchOutcome::NoMatcher
    ));
}

#[test]
fn deep_native_unification_and_matching_grow_the_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut left = msg_var("x", 0);
            let mut right = msg_var("y", 1);
            for _ in 0..8192 {
                left = pk(left);
                right = pk(right);
            }
            let sigma = unify_lnterm_no_ac(vec![Equal {
                lhs: left.clone(),
                rhs: right.clone(),
            }])
            .unwrap();
            assert_eq!(
                apply_vterm(&sigma, left.clone()),
                apply_vterm(&sigma, right.clone())
            );
            let problem = Match::match_with(left.clone(), right.clone());
            let matched = solve_match_lterm_no_ac(&crate::lterm::sort_of_name, problem).unwrap();
            assert_eq!(apply_vterm(&matched, right), left);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_unification_reuses_substitution_but_refreshes_after_sibling_bindings() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut left: LNTerm = msg_var("x", 0);
            let mut right: LNTerm = msg_var("y", 1);
            for _ in 0..8192 {
                left = crate::builtin::hash(left);
                right = crate::builtin::hash(right);
            }
            let eqs = vec![
                Equal::new(msg_var("unrelated", 3), msg_var("unrelated", 2)),
                Equal::new(pair(msg_var("y", 1), left), pair(msg_var("x", 0), right)),
            ];
            let subst = unify_lnterm_no_ac(eqs.clone()).unwrap();
            for eq in eqs {
                assert_eq!(apply_vterm(&subst, eq.lhs), apply_vterm(&subst, eq.rhs));
            }
            // A newly bound first argument must be visible to its right sibling.
            assert!(unify_lnterm_no_ac(vec![Equal::new(
                pair(msg_var("x", 0), msg_var("x", 0)),
                pair(crate::lterm::pub_term("a"), crate::lterm::pub_term("b")),
            )])
            .is_err());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn unification_matches_indexed_worklist_reference() {
    use crate::function_symbols::{AcSym, CSym};
    use crate::term::{f_app_ac, f_app_c};
    fn next(seed: &mut u64) -> usize {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (*seed >> 32) as usize
    }
    fn term(seed: &mut u64, depth: usize) -> LNTerm {
        let n = next(seed);
        if depth == 0 {
            return if n.is_multiple_of(7) {
                crate::lterm::pub_term("a")
            } else {
                crate::vterm::var_term(LVar::new(
                    "x",
                    [LSort::Msg, LSort::Pub, LSort::Fresh, LSort::Nat][n % 4],
                    (n % 7) as u64,
                ))
            };
        }
        let a = term(seed, depth - 1);
        match n % 7 {
            0 => pair(a, term(seed, depth - 1)),
            1 => crate::builtin::hash(a),
            2 => f_app_ac(AcSym::Mult, vec![a, term(seed, depth - 1)]),
            3 => f_app_c(CSym::EMap, vec![a, term(seed, depth - 1)]),
            4 => f_app_ac(AcSym::NatPlus, vec![a, term(seed, depth - 1)]),
            _ => a,
        }
    }
    for seed in 0..5000 {
        let mut state = seed + 1;
        let eqs: Vec<_> = (0..1 + seed % 5)
            .map(|_| Equal::new(term(&mut state, 3), term(&mut state, 3)))
            .collect();
        assert_eq!(
            format!("{:?}", unify_lnterm_no_ac(eqs.clone())),
            format!("{:?}", reference::unify_lnterm_no_ac(eqs.clone())),
            "case {seed}"
        );
        assert_eq!(
            unify_lnterm_factored(eqs.clone()),
            reference::unify_lnterm_factored(eqs),
            "case {seed}"
        );
    }
    // Mostly successful problems exercise dependency removal, alias propagation,
    // and idempotent images more deeply than arbitrary conflicting equations.
    for seed in 0..1000 {
        let mut state = seed + 17;
        let mut eqs = Vec::new();
        for i in 0..16 {
            let a = msg_var("x", (next(&mut state) % 8) as u64);
            let b = msg_var("x", (next(&mut state) % 8) as u64);
            let image = if i % 2 == 0 {
                pair(a, b)
            } else {
                crate::builtin::hash(a)
            };
            eqs.push(Equal::new(msg_var("image", i), image));
        }
        for i in 0..8 {
            eqs.push(Equal::new(msg_var("x", i), msg_var("x", (i + 1) % 8)));
        }
        eqs.push(Equal::new(
            msg_var("x", 0),
            crate::lterm::pub_term("anchor"),
        ));
        assert_eq!(
            unify_lnterm_factored(eqs.clone()),
            reference::unify_lnterm_factored(eqs),
            "dependent case {seed}"
        );
    }
}

#[test]
fn deep_unification_with_a_binding_at_every_level() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut l = msg_var("last", 0);
            let mut r = l.clone();
            for i in 0..8192 {
                l = pair(msg_var("a", i), l);
                r = pair(msg_var("b", i), r);
            }
            let result = unify_lnterm_no_ac(vec![Equal::new(l.clone(), r.clone())]).unwrap();
            assert_eq!(result.len(), 8192);
            assert_eq!(apply_vterm(&result, l), apply_vterm(&result, r));
            // Changing a previously referenced image must update every dependent key.
            let x = msg_var("x", 0);
            let y = msg_var("y", 0);
            let z = msg_var("z", 0);
            let eqs = vec![
                Equal::new(x.clone(), pair(y.clone(), z.clone())),
                Equal::new(y.clone(), z.clone()),
                Equal::new(z, crate::lterm::pub_term("a")),
            ];
            assert_eq!(
                unify_lnterm_factored(eqs.clone()),
                reference::unify_lnterm_factored(eqs)
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_binding_images_and_occurs_failures_use_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let x = msg_var("x", 0);
            let y = msg_var("y", 1);
            let mut image = y.clone();
            for _ in 0..8192 {
                image = crate::builtin::hash(image);
            }
            for (lhs, rhs) in [(x.clone(), image.clone()), (image.clone(), x.clone())] {
                let eqs = vec![Equal::new(lhs, rhs)];
                let subst = unify_lnterm_no_ac(eqs.clone()).unwrap();
                assert_eq!(subst.len(), 1);
                assert_eq!(apply_vterm(&subst, x.clone()), image);
                let (factored, residuals) = unify_lnterm_factored(eqs).unwrap();
                assert_eq!(factored, subst);
                assert!(residuals.is_empty());
            }
            let cycle = vec![Equal::new(y, image)];
            assert!(matches!(
                unify_lnterm_no_ac(cycle.clone()),
                Err(UnifyError::NoUnifier)
            ));
            assert!(unify_lnterm_factored(cycle).is_none());
        })
        .unwrap()
        .join()
        .unwrap();
}
