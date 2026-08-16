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
    // HS `unifyRaw` orients same-sort var-var by `Ord LVar` (Unification.hs:276):
    // idx and sort tie here, so the later NAME is eliminated and becomes the
    // KEY.  A non-empty check alone accepts either orientation.
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
    // Each PATTERN variable is the key, bound to the subject at its own
    // argument position — a bare count is blind to a swap.
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
