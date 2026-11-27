// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Unification` from `lib/term/src/Term/Unification.hs`.
//!
//! Tamarin performs unification in two phases: free unification with
//! delayed AC equations, then ships the AC equations off to Maude. This
//! file ports both of those:
//!
//! `unify_lterm_factored` (HS `unifyLTermFactored`) solves the non-AC
//! fragment and returns the residual AC/C equations, which callers
//! (`maude_proc.rs`, `equation_store.rs`) send to Maude as HS does via
//! `unifyViaMaude`.
//!
//! Matching (`solve_match_lterm`) reports `NeedsAc` for the caller to send
//! to Maude.

use std::collections::BTreeMap;

use crate::function_symbols::FunSym;
use crate::lterm::{sort_compare, sort_of_lterm, LSort, LTerm, LVar, Name};
use crate::rewriting::{Equal, Match};
use crate::subst::{apply_vterm, apply_vterm_map, Subst};
use crate::term::Term;
use crate::vterm::Lit;

#[derive(Debug)]
pub enum UnifyError {
    NoUnifier,
    /// The native matcher met an AC/C problem (HS `ACProblem`).
    NeedsAC,
}

/// Haskell's `unifyRaw` (Unification.hs): solve the non-AC fragment into
/// `acc` and delay each AC/C/nat pair to `delayed` (HS `tell [Equal l r]`).
///
/// Var-var orientation is Haskell-faithful (Unification.hs):
///   same-sort   → if vl < vr then elim vr l else elim vl r  (LARGER-idx
///                 becomes KEY, smaller-idx the value)
///   vl ⊇ vr     → elim vl r   (broader becomes KEY)
///   otherwise   → elim vr l   (broader becomes KEY)
/// This is the orientation `restrict stableVars` (Sources.hs) and
/// `applySource` (Sources.hs) depend on: stable pattern vars (small
/// idx) stay on the value side so they never become keys and are dropped by
/// the post-saturate key-filter.
fn unify_raw<C, F>(
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
                    // Haskell `unifyRaw` (Unification.hs):
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
                unify_raw(sort_of_const, acc, delayed, a, b)?;
            }
            Ok(())
        }
        (Term::App(FunSym::List, la), Term::App(FunSym::List, ra)) if la.len() == ra.len() => {
            for (a, b) in la.iter().cloned().zip(ra.iter().cloned()) {
                unify_raw(sort_of_const, acc, delayed, a, b)?;
            }
            Ok(())
        }
        // Special cases for builtin naturals (Unification.hs):
        // a nullary NoEq vs a NatPlus sum unifies only when the nullary
        // symbol is `natOne`; otherwise no unifier.  When it is natOne,
        // Haskell `tell`s the equation for Maude.
        (
            Term::App(FunSym::NoEq(lf), la),
            Term::App(FunSym::Ac(crate::function_symbols::AcSym::NatPlus), _),
        ) if la.is_empty() => {
            if lf.is_nat_one_sym() {
                delay(delayed, l.clone(), r.clone())
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        (
            Term::App(FunSym::Ac(crate::function_symbols::AcSym::NatPlus), _),
            Term::App(FunSym::NoEq(rf), ra),
        ) if ra.is_empty() => {
            if rf.is_nat_one_sym() {
                delay(delayed, l.clone(), r.clone())
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        // Haskell `unifyRaw` (Unification.hs): the AC/C arms fire ONLY
        // when BOTH sides are AC (resp. C) apps and the symbols (and, for C,
        // the arity) match — at which point HS does `tell [Equal l r]`.  A
        // symbol/arity mismatch fails the `guard` (→ `Nothing`, i.e. no
        // unifier), and any AC-vs-non-AC (or C-vs-non-C) pairing falls through
        // to HS `_ -> mzero`; both map to `NoUnifier`.
        (Term::App(FunSym::Ac(la), _), Term::App(FunSym::Ac(ra), _)) => {
            if la == ra {
                delay(delayed, l.clone(), r.clone())
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        // C arm (Unification.hs): both sides C, same symbol AND arity.
        (Term::App(FunSym::C(ls), largs), Term::App(FunSym::C(rs), rargs)) => {
            if ls == rs && largs.len() == rargs.len() {
                delay(delayed, l.clone(), r.clone())
            } else {
                Err(UnifyError::NoUnifier)
            }
        }
        // Everything else (incl. AC-vs-non-AC, C-vs-non-C) → HS `_ -> mzero`.
        _ => Err(UnifyError::NoUnifier),
    }
}

fn delay<C>(
    delayed: &mut Vec<Equal<LTerm<C>>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
) -> Result<(), UnifyError> {
    delayed.push(Equal { lhs, rhs });
    Ok(())
}

/// `unifyLTermFactored` port (Unification.hs).  Returns the
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
        unify_raw(sort_of_const, &mut acc, &mut delayed, lhs, rhs).ok()?;
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

/// Outcome of the native matcher (HS `solveMatchLTerm`, Unification.hs):
/// `NoMatcher` and `Matched` are final; only `NeedsAc` (HS `ACProblem`)
/// warrants a Maude `match` of the whole problem.
pub enum MatchOutcome<C> {
    NoMatcher,
    Matched(Subst<C, LVar>),
    NeedsAc,
}

/// HS `solveMatchLTerm` (Unification.hs) without the Maude fallback: run
/// `matchRaw` over all pairs and report the 3-way outcome.
///
/// `bindable` stands in for HS skolemisation (`skolemizeTerm`, Guarded.hs):
/// a pattern variable it rejects is a skolem constant and matches only
/// itself. Pass `&|_| true` when every pattern variable is bindable.
pub fn solve_match_lterm<C, F, B>(
    sort_of_const: &F,
    bindable: &B,
    problem: Match<LTerm<C>>,
) -> MatchOutcome<C>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
    B: Fn(&LVar) -> bool,
{
    // HS `flattenMatch matchProblem` ⇒ `Nothing` means a non-flattenable
    // problem (`MatchFailure`), treated as `[]` — i.e. NoMatcher.
    let pairs = match problem.flatten() {
        Some(p) => p,
        None => return MatchOutcome::NoMatcher,
    };
    let mut mapping: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    for (term, pattern) in pairs {
        match match_raw(sort_of_const, bindable, &mut mapping, term, pattern) {
            Ok(()) => {}
            Err(UnifyError::NeedsAC) => return MatchOutcome::NeedsAc,
            Err(UnifyError::NoUnifier) => return MatchOutcome::NoMatcher,
        }
    }
    MatchOutcome::Matched(Subst::from_map(mapping))
}

fn match_raw<C, F, B>(
    sort_of_const: &F,
    bindable: &B,
    mapping: &mut BTreeMap<LVar, LTerm<C>>,
    t: LTerm<C>,
    p: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
    B: Fn(&LVar) -> bool,
{
    match p {
        // A skolemised variable is a constant: HS `(Lit (Con ct), Lit (Con cp))`.
        Term::Lit(Lit::Var(vp)) if !bindable(&vp) => match t {
            Term::Lit(Lit::Var(vt)) if vt == vp => Ok(()),
            _ => Err(UnifyError::NoUnifier),
        },
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
                    match_raw(sort_of_const, bindable, mapping, a, b)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::List, pargs) => match t {
            Term::App(FunSym::List, targs) if targs.len() == pargs.len() => {
                for (a, b) in targs.iter().cloned().zip(pargs.iter().cloned()) {
                    match_raw(sort_of_const, bindable, mapping, a, b)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::NoUnifier),
        },
        // HS `ACProblem` needs both sides AC- (or C-) headed, with any
        // symbols; every other pairing is `NoMatcher`.
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
// easy to miss.  The cost of getting any of these wrong is a silent
// divergence — the wrong unifier "works" in the logical sense (produces
// equivalent equality classes) but the SHAPE of the result differs, which
// downstream code can implicitly depend on.
//
// If any of these tests fails, STOP and investigate before chasing a
// downstream symptom — the root is here at the term layer.
#[cfg(test)]
#[path = "unification_haskell_invariants_tests.rs"]
mod haskell_invariants_tests;
