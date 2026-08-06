// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, beschmi, rsasse, PhilipLukertWork, and other
//   minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Unification.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs

//! Port of `Term.Unification` from `lib/term/src/Term/Unification.hs`.
//!
//! Tamarin performs unification in two phases: free unification with
//! delayed AC equations, then ships the AC equations off to Maude. This
//! file ports both of those:
//!
//! * The HS-faithful factored path (`unify_lterm_factored` /
//!   `unify_raw_factored`, mirroring `unifyLTermFactored`) solves the
//!   non-AC fragment and collects the residual AC/C equations into a
//!   delayed list — `tell [Equal l r]` in the HS writer monad. Callers
//!   (`maude_proc.rs`, `equation_store.rs`) ship those residuals to Maude,
//!   exactly as HS does via `unifyViaMaude`. This is the primary path used
//!   in solving.
//! * The standalone non-AC helpers (`unify_lterm_no_ac` /
//!   `solve_match_lterm_no_ac`) bail with `NeedsAC` / `None` on AC input;
//!   they exist for callers that have no Maude bridge to fall back on.
//!
//! Matching follows the same split.

use std::collections::BTreeMap;
use std::sync::atomic::AtomicU64;

use crate::function_symbols::FunSym;
use crate::lterm::{sort_compare, sort_of_lterm, LSort, LTerm, LVar, Name};
use crate::rewriting::{Equal, Match};
use crate::subst::{apply_vterm, apply_vterm_map, Subst};
use crate::term::Term;
use crate::vterm::Lit;

#[derive(Debug)]
pub enum UnifyError {
    NoUnifier,
    /// AC equation encountered — unsupported without Maude.
    NeedsAC,
}

/// `unifyLTermNoAC` — non-AC unification. Returns a single most-general
/// unifier or `Err(UnifyError::NoUnifier)` / `Err(UnifyError::NeedsAC)`.
///
/// Two LVars with incomparable sorts yield `Err(UnifyError::NoUnifier)`;
/// when one sort is broader it becomes the elimination key. No witnesses
/// are minted (cf. HS `unifyRaw`).
pub fn unify_lterm_no_ac<C, F>(
    sort_of_const: &F,
    eqs: Vec<Equal<LTerm<C>>>,
) -> Result<Subst<C, LVar>, UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let mut acc: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    for Equal { lhs, rhs } in eqs {
        unify_raw(sort_of_const, &mut acc, lhs, rhs)?;
    }
    Ok(Subst::from_map(acc))
}

/// Convenience: `unifyLNTermNoAC`.
pub fn unify_lnterm_no_ac(
    eqs: Vec<Equal<crate::lterm::LNTerm>>,
) -> Result<Subst<Name, LVar>, UnifyError> {
    unify_lterm_no_ac(&|n: &Name| crate::lterm::sort_of_name(n), eqs)
}

/// Variant accepting a shared atomic counter for parity with the
/// Maude-backed unifier call sites.  The AC-free unification logic mints
/// no fresh witnesses, so the counter is deliberately ignored; the
/// parameter exists only so callers can use the same signature whether or
/// not they route through Maude.  Do NOT assume the counter is threaded.
pub fn unify_lnterm_no_ac_with_counter(
    eqs: Vec<Equal<crate::lterm::LNTerm>>,
    _counter: &AtomicU64,
) -> Result<Subst<Name, LVar>, UnifyError> {
    unify_lnterm_no_ac(eqs)
}

/// `unifiableLNTermsNoAC`: shorthand for "is there a unifier?".
///
/// Intentionally retained for parity with HS `unifiableLNTermsNoAC`; no
/// current Rust caller in the prover.
pub fn unifiable_lnterms_no_ac(a: crate::lterm::LNTerm, b: crate::lterm::LNTerm) -> bool {
    unify_lnterm_no_ac(vec![Equal::new(a, b)]).is_ok()
}

/// AC/C/nat delay decision, the sole point where `unify_raw` and
/// `unify_raw_factored` diverge.  With a `delayed` sink present (the
/// factored path) HS does `tell [Equal l r]`, so we push the residual
/// equation and succeed; without one (the no-AC path) HS's
/// `unifyLTermFactoredNoAC` (Unification.hs:160-164) hits
/// `error "No AC unification, but AC symbol found."`, surfaced as `NeedsAC`.
fn delay_or_needs_ac<C: Clone>(
    delayed: Option<&mut Vec<Equal<LTerm<C>>>>,
    l: &LTerm<C>,
    r: &LTerm<C>,
) -> Result<(), UnifyError> {
    match delayed {
        Some(d) => {
            d.push(Equal {
                lhs: l.clone(),
                rhs: r.clone(),
            });
            Ok(())
        }
        None => Err(UnifyError::NeedsAC),
    }
}

/// Shared body of `unify_raw` (no-AC) and `unify_raw_factored` (AC via a
/// delayed writer).  Mirrors Haskell's `unifyRaw` (Unification.hs:230-280).
/// Every non-AC arm is identical between the two callers; the only
/// behavioural fork is at the three AC/C/nat delay points, gated on
/// whether `delayed` is `Some` (push the residual, cf. HS `tell`) or `None`
/// (return `NeedsAC`).
///
/// Var-var orientation is Haskell-faithful (Unification.hs:240-246):
///   same-sort   → if vl < vr then elim vr l else elim vl r  (LARGER-idx
///                 becomes KEY, smaller-idx the value)
///   vl ⊇ vr     → elim vl r   (broader becomes KEY)
///   otherwise   → elim vr l   (broader becomes KEY)
/// This is the orientation `restrict stableVars` (Sources.hs:113-137, see line 123) and
/// `applySource` (Sources.hs:336-350) depend on: stable pattern vars (small
/// idx) stay on the value side so they never become keys and are dropped by
/// the post-saturate key-filter.
fn unify_raw_impl<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    mut delayed: Option<&mut Vec<Equal<LTerm<C>>>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    // Apply the accumulator by borrowing it directly — avoids cloning
    // the whole map into a `Subst` on every recursion (hot path).
    let l = apply_vterm_map(&*acc, lhs);
    let r = apply_vterm_map(&*acc, rhs);

    match (&l, &r) {
        (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) if vl == vr => Ok(()),
        (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) => {
            use std::cmp::Ordering;
            match sort_compare(vl.sort, vr.sort) {
                Some(Ordering::Equal) => {
                    // Haskell `unifyRaw` (Unification.hs:235-243, see line 241):
                    //   `if vl < vr then elim vr l else elim vl r`
                    // Larger-idx becomes KEY, smaller-idx becomes value.
                    let (key, val) = if vl < vr {
                        (*vr, Term::Lit(Lit::Var(*vl)))
                    } else {
                        (*vl, Term::Lit(Lit::Var(*vr)))
                    };
                    eliminate(sort_of_const, acc, key, val)
                }
                Some(Ordering::Greater) => {
                    // vl > vr (vl is broader) → bind vl to vr.
                    eliminate(sort_of_const, acc, *vl, Term::Lit(Lit::Var(*vr)))
                }
                Some(Ordering::Less) => {
                    // vl < vr (vr is broader) → bind vr to vl.
                    eliminate(sort_of_const, acc, *vr, Term::Lit(Lit::Var(*vl)))
                }
                None => Err(UnifyError::NoUnifier),
            }
        }
        (Term::Lit(Lit::Var(vl)), _) => eliminate(sort_of_const, acc, *vl, r.clone()),
        (_, Term::Lit(Lit::Var(vr))) => eliminate(sort_of_const, acc, *vr, l.clone()),
        (Term::Lit(Lit::Con(cl)), Term::Lit(Lit::Con(cr))) => {
            if cl == cr {
                Ok(())
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        (Term::App(FunSym::NoEq(lf), la), Term::App(FunSym::NoEq(rf), ra))
            if lf == rf && la.len() == ra.len() =>
        {
            for (a, b) in la.iter().cloned().zip(ra.iter().cloned()) {
                unify_raw_impl(sort_of_const, acc, delayed.as_deref_mut(), a, b)?;
            }
            Ok(())
        }
        (Term::App(FunSym::List, la), Term::App(FunSym::List, ra)) if la.len() == ra.len() => {
            for (a, b) in la.iter().cloned().zip(ra.iter().cloned()) {
                unify_raw_impl(sort_of_const, acc, delayed.as_deref_mut(), a, b)?;
            }
            Ok(())
        }
        // Special cases for builtin naturals (Unification.hs:251-256):
        // a nullary NoEq vs a NatPlus sum unifies only when the nullary
        // symbol is `natOne`; otherwise no unifier.  When it is natOne,
        // Haskell `tell`s the equation for Maude (delay-or-NeedsAC).
        (
            Term::App(FunSym::NoEq(lf), la),
            Term::App(FunSym::Ac(crate::function_symbols::AcSym::NatPlus), _),
        ) if la.is_empty() => {
            if *lf == crate::function_symbols::nat_one_sym() {
                delay_or_needs_ac(delayed.as_deref_mut(), &l, &r)
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        (
            Term::App(FunSym::Ac(crate::function_symbols::AcSym::NatPlus), _),
            Term::App(FunSym::NoEq(rf), ra),
        ) if ra.is_empty() => {
            if *rf == crate::function_symbols::nat_one_sym() {
                delay_or_needs_ac(delayed.as_deref_mut(), &l, &r)
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        // Haskell `unifyRaw` (Unification.hs:265-270): the AC/C arms fire ONLY
        // when BOTH sides are AC (resp. C) apps and the symbols (and, for C,
        // the arity) match — at which point HS does `tell [Equal l r]`.  A
        // symbol/arity mismatch fails the `guard` (→ `Nothing`, i.e. no
        // unifier), and any AC-vs-non-AC (or C-vs-non-C) pairing falls through
        // to HS `_ -> mzero` (line 273); both map to `NoUnifier`.
        (Term::App(FunSym::Ac(la), _), Term::App(FunSym::Ac(ra), _)) => {
            if la == ra {
                delay_or_needs_ac(delayed.as_deref_mut(), &l, &r)
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        // C arm (Unification.hs:268-270): both sides C, same symbol AND arity.
        (Term::App(FunSym::C(ls), largs), Term::App(FunSym::C(rs), rargs)) => {
            if ls == rs && largs.len() == rargs.len() {
                delay_or_needs_ac(delayed, &l, &r)
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        // Everything else (incl. AC-vs-non-AC, C-vs-non-C) → HS `_ -> mzero`.
        _ => Err(UnifyError::NoUnifier),
    }
}

fn unify_raw<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    unify_raw_impl(sort_of_const, acc, None, lhs, rhs)
}

/// Haskell-faithful factored unification: same as `unify_raw` but
/// **pushes AC/C equations to a delayed list** instead of returning
/// `NeedsAC`.  Mirrors Haskell's `unifyRaw` (Unification.hs:230-280)
/// which uses `tell [Equal l r]` from a writer monad to delay AC.
fn unify_raw_factored<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    delayed: &mut Vec<Equal<LTerm<C>>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    unify_raw_impl(sort_of_const, acc, Some(delayed), lhs, rhs)
}

/// `unifyLTermFactored` port (Unification.hs:107-120).  Returns the
/// non-AC substitution and the residual AC equations (already with
/// the non-AC subst applied).  Callers ship the residuals to Maude.
///
/// Returns `None` if the non-AC fragment is unsatisfiable.
pub fn unify_lterm_factored<C, F>(
    sort_of_const: &F,
    eqs: Vec<Equal<LTerm<C>>>,
) -> Option<(Subst<C, LVar>, Vec<Equal<LTerm<C>>>)>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let mut acc: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    let mut delayed: Vec<Equal<LTerm<C>>> = Vec::new();
    for Equal { lhs, rhs } in eqs {
        match unify_raw_factored(sort_of_const, &mut acc, &mut delayed, lhs, rhs) {
            Ok(()) => {}
            Err(UnifyError::NoUnifier) => return None,
            // unify_raw_factored delays AC/C to `delayed` and never
            // surfaces NeedsAC; make the invariant explicit.
            Err(UnifyError::NeedsAC) => unreachable!("unify_raw_factored delays AC"),
        }
    }
    let subst = Subst::from_map(acc);
    // Apply the freshly-built subst to the delayed residuals so Maude
    // sees the most-refined form (mirrors Haskell's
    // `map (applyVTerm subst <$>) leqs`).
    let delayed = delayed
        .into_iter()
        .map(|Equal { lhs, rhs }| Equal {
            lhs: apply_vterm(&subst, lhs),
            rhs: apply_vterm(&subst, rhs),
        })
        .collect();
    Some((subst, delayed))
}

/// Convenience for `LNTerm`s.
pub fn unify_lnterm_factored(
    eqs: Vec<Equal<crate::lterm::LNTerm>>,
) -> Option<(Subst<Name, LVar>, Vec<Equal<crate::lterm::LNTerm>>)> {
    unify_lterm_factored(&|n: &Name| crate::lterm::sort_of_name(n), eqs)
}

fn eliminate<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    v: LVar,
    t: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    if crate::vterm::occurs_vterm(&v, &t) {
        return Err(UnifyError::NoUnifier);
    }
    if !sort_geq_lterm(sort_of_const, &v, &t) {
        return Err(UnifyError::NoUnifier);
    }
    // Substitute `v ~> t` through the existing accumulator in place, mutating
    // each value rather than rebuilding the whole map with cloned keys.
    let mut single = BTreeMap::new();
    single.insert(v, t.clone());
    for ts in acc.values_mut() {
        let cur = std::mem::replace(ts, Term::Lit(Lit::Var(v)));
        *ts = apply_vterm_map(&single, cur);
    }
    acc.insert(v, t);
    Ok(())
}

fn sort_geq_lterm<C, F: Fn(&C) -> LSort>(sort_of_const: &F, v: &LVar, t: &LTerm<C>) -> bool {
    let s_t = sort_of_lterm(t, |c| sort_of_const(c));
    let s_v = v.sort;
    if s_v == s_t {
        return true;
    }
    if s_v == LSort::Node || s_t == LSort::Node {
        return false;
    }
    matches!(
        sort_compare(s_v, s_t),
        Some(std::cmp::Ordering::Equal | std::cmp::Ordering::Greater)
    )
}

// =============================================================================
// Free matching (no AC).
// =============================================================================

/// `solveMatchLNTermNoAC`: solve a matching problem in the AC-free
/// fragment. Returns the resulting substitution or `None` if either no
/// matcher exists or an AC equation is encountered.
pub fn solve_match_lterm_no_ac<C, F>(
    sort_of_const: &F,
    problem: Match<LTerm<C>>,
) -> Option<Subst<C, LVar>>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let pairs = problem.flatten()?;
    let mut mapping: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    for (term, pattern) in pairs {
        match_raw(sort_of_const, &mut mapping, term, pattern).ok()?;
    }
    Some(Subst::from_map(mapping))
}

/// Outcome of the native matcher, mirroring HS `solveMatchLTerm`'s
/// 3-way `case runState (runExceptT match)` split
/// (`Term/Unification.hs:209-214`):
///
/// * `NoMatcher`   ⇒ `Left NoMatcher`  ⇒ HS returns `[]` *without* any
///   Maude round-trip.  (The pattern structurally cannot match the
///   subject — e.g. constant clash, arity mismatch, sort clash, or a
///   pattern var already bound to a different subject.)
/// * `Matched(s)`  ⇒ `Right ()`        ⇒ HS returns `[substFromMap …]`
///   natively, no Maude.
/// * `NeedsAC`     ⇒ `Left ACProblem`  ⇒ HS calls `matchViaMaude` on the
///   *whole* original problem.
///
/// The crucial distinction over `solve_match_lterm_no_ac` (which folds
/// `NoMatcher` and `NeedsAC` together into `None`) is that callers must
/// only fall back to Maude on `NeedsAC` — a `NoMatcher` is a definitive
/// "no match" answer that HS never sends to Maude.  Conflating the two
/// makes the Rust port issue a Maude `match` for every structurally
/// failing match attempt, which is exactly the surplus `match in MSG`
/// flood observed on LAK06/Scott (`matchToGoal`, `Sources.hs:355-384, see line 381,414`).
pub enum MatchOutcome<C> {
    NoMatcher,
    Matched(Subst<C, LVar>),
    NeedsAc,
}

/// HS-faithful `solveMatchLTerm` (`Term/Unification.hs:196-216`): run the
/// native `matchRaw` matcher over all delayed pairs and report the 3-way
/// outcome so the caller can decide whether a Maude AC fallback is
/// actually warranted (only on `NeedsAc`).
///
/// `matchRaw` raises `ACProblem` (here `NeedsAC`) the *instant* it sees an
/// AC-/C-headed pair on BOTH sides; a variable pattern facing an
/// AC-headed subject is bound natively (HS `matchRaw` checks the
/// `(_, Lit (Var vp))` arm first, `Unification.hs:316-350, see line 317`) — so a `tamxor`
/// buried under a variable pattern never triggers a Maude call.
pub fn solve_match_lterm<C, F>(sort_of_const: &F, problem: Match<LTerm<C>>) -> MatchOutcome<C>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    // HS `flattenMatch matchProblem` ⇒ `Nothing` means a non-flattenable
    // problem (`MatchFailure`), treated as `[]` — i.e. NoMatcher.
    let pairs = match problem.flatten() {
        Some(p) => p,
        None => return MatchOutcome::NoMatcher,
    };
    let mut mapping: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    for (term, pattern) in pairs {
        match match_raw(sort_of_const, &mut mapping, term, pattern) {
            Ok(()) => {}
            Err(UnifyError::NeedsAC) => return MatchOutcome::NeedsAc,
            Err(UnifyError::NoUnifier) => return MatchOutcome::NoMatcher,
        }
    }
    MatchOutcome::Matched(Subst::from_map(mapping))
}

fn match_raw<C, F>(
    sort_of_const: &F,
    mapping: &mut BTreeMap<LVar, LTerm<C>>,
    t: LTerm<C>,
    p: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    match p {
        Term::Lit(Lit::Var(vp)) => {
            if let Some(existing) = mapping.get(&vp) {
                if existing == &t {
                    return Ok(());
                }
                return Err(UnifyError::NoUnifier);
            }
            if !sort_geq_lterm(sort_of_const, &vp, &t) {
                return Err(UnifyError::NoUnifier);
            }
            mapping.insert(vp, t);
            Ok(())
        }
        Term::Lit(Lit::Con(cp)) => match t {
            Term::Lit(Lit::Con(ct)) if ct == cp => Ok(()),
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::NoEq(pf), pargs) => match t {
            Term::App(FunSym::NoEq(tf), targs) if tf == pf && targs.len() == pargs.len() => {
                for (a, b) in targs.iter().cloned().zip(pargs.iter().cloned()) {
                    match_raw(sort_of_const, mapping, a, b)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::List, pargs) => match t {
            Term::App(FunSym::List, targs) if targs.len() == pargs.len() => {
                for (a, b) in targs.iter().cloned().zip(pargs.iter().cloned()) {
                    match_raw(sort_of_const, mapping, a, b)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::NoUnifier),
        },
        // HS `(FApp (AC _) _, FApp (AC _) _) -> throwError ACProblem` and
        // `(FApp (C _) _, FApp (C _) _) -> throwError ACProblem`
        // (Unification.hs:333-334): the AC/C arm fires ONLY when BOTH the
        // subject `t` AND the pattern `p` are AC-/C-headed.  An AC-/C-headed
        // PATTERN facing a variable / constant / NoEq / List / differently-
        // headed subject is NOT an AC problem — HS falls to the final
        // `_ -> throwError NoMatcher` arm (Unification.hs:316-350, see line 337).  (An
        // AC-/C-headed PATTERN alone is not enough — the subject must be
        // AC-/C-headed too, otherwise this would ship non-AC structural
        // mismatches to Maude.)
        // NB: HS does NOT require the AC (resp. C) symbols to match here —
        // `Mult`-vs-`Union` is still `ACProblem` (Maude then resolves it,
        // typically to no match).  So the guard is purely "both AC" / "both
        // C", not "same symbol".
        Term::App(FunSym::Ac(_), _) => match t {
            Term::App(FunSym::Ac(_), _) => Err(UnifyError::NeedsAC),
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::C(_), _) => match t {
            Term::App(FunSym::C(_), _) => Err(UnifyError::NeedsAC),
            _ => Err(UnifyError::NoUnifier),
        },
    }
}

#[cfg(test)]
#[path = "unification_tests.rs"]
mod tests;

// =============================================================================
// Haskell-faithfulness invariants
// =============================================================================
//
// These tests pin subtle term-layer semantic choices whose violation is
// easy to miss.  The cost of getting
// any of these wrong is a silent divergence — the wrong unifier "works"
// in the logical sense (produces equivalent equality classes) but the
// SHAPE of the result differs, which downstream code can implicitly
// depend on.
//
// If any of these tests fails, STOP and investigate before chasing a
// downstream symptom — the root is here at the term layer.
//
// References to Haskell source are checked-in as of the May 2026 port
// state; line numbers may drift but the contracts shouldn't.
#[cfg(test)]
#[path = "unification_haskell_invariants_tests.rs"]
mod haskell_invariants_tests;
