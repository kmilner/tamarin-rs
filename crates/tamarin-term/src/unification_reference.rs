// Test-only indexed worklist implementation, retained as an independent
// semantic oracle for the ordinary-workload unifier.
#![allow(dead_code)]
// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::AtomicU64;

use crate::function_symbols::FunSym;
use crate::lterm::{sort_compare, sort_of_lterm, LSort, LTerm, LVar, Name};
use crate::rewriting::Equal;
use crate::subst::{apply_vterm, apply_vterm_map, Subst};
use crate::term::Term;
use crate::vterm::Lit;

#[derive(Debug)]
pub enum UnifyError {
    NoUnifier,
    /// AC equation encountered — unsupported without Maude.
    NeedsAC,
}

/// Idempotent images and their reverse variable dependencies. Extending the
/// substitution touches only images that actually mention the eliminated key.
struct Unifier<C> {
    images: BTreeMap<LVar, LTerm<C>>,
    users: BTreeMap<LVar, BTreeSet<LVar>>,
}
impl<C: Ord + Clone> Unifier<C> {
    fn new() -> Self {
        Self {
            images: BTreeMap::new(),
            users: BTreeMap::new(),
        }
    }
    fn head(&self, t: LTerm<C>) -> LTerm<C> {
        let t = match &t {
            Term::Lit(Lit::Var(v)) => self.images.get(v).cloned().unwrap_or(t),
            _ => t,
        };
        // AC/C classification and residuals require normalized arguments.
        // Free constructors can defer substitution until their children are visited.
        if matches!(t, Term::App(FunSym::Ac(_) | FunSym::C(_), _)) {
            apply_vterm_map(&self.images, t)
        } else {
            t
        }
    }
    fn variables(t: &LTerm<C>) -> BTreeSet<LVar> {
        let mut vars = BTreeSet::new();
        t.for_each_lit(|l| {
            if let Lit::Var(v) = l {
                vars.insert(*v);
            }
        });
        vars
    }
    fn insert(&mut self, key: LVar, term: LTerm<C>) {
        for v in Self::variables(&term) {
            self.users.entry(v).or_default().insert(key);
        }
        self.images.insert(key, term);
    }
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
    let mut acc = Unifier::new();
    for Equal { lhs, rhs } in eqs {
        unify_raw(sort_of_const, &mut acc, lhs, rhs)?;
    }
    Ok(Subst::from_map(acc.images))
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

/// AC/C/nat delay decision, the sole point where `unify_raw` and
/// `unify_raw_factored` diverge.  With a `delayed` sink present (the
/// factored path) HS does `tell [Equal l r]`, so we push the residual
/// equation and succeed; without one (the no-AC path) HS's
/// `unifyLTermFactoredNoAC` (Unification.hs:176-187) hits
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
/// delayed writer).  Mirrors Haskell's `unifyRaw` (Unification.hs:259-308).
/// Every non-AC arm is identical between the two callers; the only
/// behavioural fork is at the three AC/C/nat delay points, gated on
/// whether `delayed` is `Some` (push the residual, cf. HS `tell`) or `None`
/// (return `NeedsAC`).
///
/// Var-var orientation is Haskell-faithful (Unification.hs:273-281):
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
    acc: &mut Unifier<C>,
    mut delayed: Option<&mut Vec<Equal<LTerm<C>>>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let mut pending = Vec::new();
    let mut next = Some((lhs, rhs));
    while let Some((lhs, rhs)) = next.take().or_else(|| pending.pop()) {
        let l = acc.head(lhs);
        let r = acc.head(rhs);

        match (&l, &r) {
            (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) if vl == vr => Ok(()),
            (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) => {
                use std::cmp::Ordering;
                match sort_compare(vl.sort, vr.sort) {
                    Some(Ordering::Equal) => {
                        // Haskell `unifyRaw` (Unification.hs:273-281, see line 276):
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
                let mut children = la.iter().cloned().zip(ra.iter().cloned());
                next = children.next();
                pending.extend(children.rev());
                Ok(())
            }
            (Term::App(FunSym::List, la), Term::App(FunSym::List, ra)) if la.len() == ra.len() => {
                let mut children = la.iter().cloned().zip(ra.iter().cloned());
                next = children.next();
                pending.extend(children.rev());
                Ok(())
            }
            // Special cases for builtin naturals (Unification.hs:286-291):
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
            // Haskell `unifyRaw` (Unification.hs:299-305): the AC/C arms fire ONLY
            // when BOTH sides are AC (resp. C) apps and the symbols (and, for C,
            // the arity) match — at which point HS does `tell [Equal l r]`.  A
            // symbol/arity mismatch fails the `guard` (→ `Nothing`, i.e. no
            // unifier), and any AC-vs-non-AC (or C-vs-non-C) pairing falls through
            // to HS `_ -> mzero` (line 308); both map to `NoUnifier`.
            (Term::App(FunSym::Ac(la), _), Term::App(FunSym::Ac(ra), _)) => {
                if la == ra {
                    delay_or_needs_ac(delayed.as_deref_mut(), &l, &r)
                } else {
                    Err(UnifyError::NoUnifier)
                }
            }
            // C arm (Unification.hs:303-305): both sides C, same symbol AND arity.
            (Term::App(FunSym::C(ls), largs), Term::App(FunSym::C(rs), rargs)) => {
                if ls == rs && largs.len() == rargs.len() {
                    delay_or_needs_ac(delayed.as_deref_mut(), &l, &r)
                } else {
                    Err(UnifyError::NoUnifier)
                }
            }
            // Everything else (incl. AC-vs-non-AC, C-vs-non-C) → HS `_ -> mzero`.
            _ => Err(UnifyError::NoUnifier),
        }?;
    }
    Ok(())
}

fn unify_raw<C, F>(
    sort_of_const: &F,
    acc: &mut Unifier<C>,
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
/// `NeedsAC`.  Mirrors Haskell's `unifyRaw` (Unification.hs:259-308)
/// which uses `tell [Equal l r]` from a writer monad to delay AC.
fn unify_raw_factored<C, F>(
    sort_of_const: &F,
    acc: &mut Unifier<C>,
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

/// `unifyLTermFactored` port (Unification.hs:120-133).  Returns the
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
    let mut acc = Unifier::new();
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
    let subst = Subst::from_map(acc.images);
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
    acc: &mut Unifier<C>,
    v: LVar,
    t: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let t = apply_vterm_map(&acc.images, t);
    if crate::vterm::occurs_vterm(&v, &t) {
        return Err(UnifyError::NoUnifier);
    }
    if !sort_geq_lterm(sort_of_const, &v, &t) {
        return Err(UnifyError::NoUnifier);
    }
    let mut single = BTreeMap::new();
    single.insert(v, t.clone());
    if let Some(users) = acc.users.remove(&v) {
        for key in users {
            let old = acc.images.remove(&key).unwrap();
            for var in Unifier::variables(&old) {
                if let Some(users) = acc.users.get_mut(&var) {
                    users.remove(&key);
                    if users.is_empty() {
                        acc.users.remove(&var);
                    }
                }
            }
            acc.insert(key, apply_vterm_map(&single, old));
        }
    }
    debug_assert!(!acc.images.contains_key(&v));
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
