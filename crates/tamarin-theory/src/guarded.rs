// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Constraint.System.Guarded` — the guarded-fragment
//! representation Tamarin's solver consumes, and `formulaToGuarded`, the
//! conversion into it from a lemma or restriction formula.
//!
//! A guarded formula is one where every quantified variable is bound
//! by an action or equality atom that fires before it's referenced.
//! The check is polarity-aware: `not (Ex x. P(x) @ #i)` becomes
//! equivalent to `All x #i. P(x) @ #i ==> ⊥` and so on.
//!
//! The conversion INPUT is [`crate::formula::LNFormula`]; the OUTPUT
//! [`Guarded`] carries the same atoms over [`BLNTerm`] (HS `BLTerm`,
//! LTerm.hs:484), the term whose variable leaves are `BVar`s: `Bound(n)`
//! is a De Bruijn index into the enclosing binder list — `Bound(0)` is the
//! innermost binder, `Bound(k-1)` the outermost — and `Free(v)` an unbound
//! `LVar`.

use std::collections::BTreeSet;

use crate::atom::{fold_atom, map_atom, Atom, ProtoAtom};
use crate::fact::Fact;
use crate::formula::{lift_free, BLNTerm, Quantifier};
use crate::tools::equation_store::LNSubst;
use tamarin_parser::ast as p;
use tamarin_term::lterm::{frees, BVar, HasFrees, LNTerm, LSort, LVar};
use tamarin_term::term::{f_app, map_lits, Term};
use tamarin_term::vterm::{var_term, Lit};
use tamarin_utils::cow::{cow_map_arc, cow_map_vec, cow_pair};
use tamarin_utils::fresh::MonadFresh;

// =============================================================================
// Guarded data type
// =============================================================================

/// HS-faithful `LNGuarded = Guarded (String, LSort) Name LVar`
/// (Guarded.hs:121-129,:391): the three parameters are fixed here because the
/// prover instantiates them at exactly that one type.
///
/// A binder carries a name and a sort; its identity is the position it holds
/// in the `GGuarded` binder list.  A variable leaf inside an atom is either
/// `BVar::Bound(n)` — a De Bruijn index into that list — or `BVar::Free(v)`.
///
/// The derived `Eq`/`Ord`/`Hash` are HS's own (`deriving (Eq, Ord, …)`,
/// Guarded.hs:129).  `Hash` reads exactly the fields `PartialEq` compares, the
/// consistency the implied-formula dedup's hash prefilter relies on
/// (`insert_implied_formulas_pass`, constraint/solver/simplify.rs).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Guarded {
    /// One atomic predicate (may contain Bound vars only when nested under
    /// a sufficient number of `GGuarded` binders).
    Atom(Atom<BLNTerm>),
    /// Disjunction of guarded sub-formulas.
    Disj(std::sync::Arc<[Guarded]>),
    /// Conjunction of guarded sub-formulas.
    Conj(std::sync::Arc<[Guarded]>),
    /// `qua xs. as ⇒ gf` (when `qua = All`) or `qua xs. as ∧ gf`
    /// (when `qua = Ex`). The `as` are the *guard* atoms, all
    /// quantified `xs` must be bound by them.
    GGuarded {
        qua: Quantifier,
        vars: std::sync::Arc<[(String, LSort)]>,
        guards: std::sync::Arc<[Atom<BLNTerm>]>,
        body: std::sync::Arc<Guarded>,
    },
}

/// Shared empty child slice for the boolean atoms `gtrue`/`gfalse` — cloning
/// it is a refcount bump rather than a per-call allocation.  The empty `Conj`
/// (`gtrue`) and empty `Disj` (`gfalse`) each clone their own static so the two
/// hot constants never contend on a single cache line.
static EMPTY_CONJ: std::sync::OnceLock<std::sync::Arc<[Guarded]>> = std::sync::OnceLock::new();
static EMPTY_DISJ: std::sync::OnceLock<std::sync::Arc<[Guarded]>> = std::sync::OnceLock::new();

/// Boolean atom helper.
pub fn gtrue() -> Guarded {
    Guarded::Conj(
        EMPTY_CONJ
            .get_or_init(|| std::sync::Arc::from(Vec::new()))
            .clone(),
    )
}
pub fn gfalse() -> Guarded {
    Guarded::Disj(
        EMPTY_DISJ
            .get_or_init(|| std::sync::Arc::from(Vec::new()))
            .clone(),
    )
}
pub fn gtf(b: bool) -> Guarded {
    if b {
        gtrue()
    } else {
        gfalse()
    }
}

/// Content-membership test for the `Arc`-wrapped formula stores
/// (`System::formulas` / `solved_formulas` / `lemmas` /
/// `sources_lemma_universals`).  The per-element `Arc` is transparent:
/// the comparison dereferences to the underlying `Guarded` value (via
/// `Arc`'s `Deref`), so this is identical to a plain
/// `Vec<Guarded>::contains` — content equality, never pointer identity.
pub fn stores_contains(store: &[std::sync::Arc<Guarded>], g: &Guarded) -> bool {
    store.iter().any(|f| f.as_ref() == g)
}

/// `True` iff the guarded formula can be reduced by the constraint
/// solver's `insertFormula` decomposition rules. Mirrors
/// `Theory.Constraint.Solver.Reduction.reducibleFormula`.
pub fn reducible_formula(fm: &Guarded) -> bool {
    match fm {
        Guarded::Atom(_) => true,
        Guarded::Conj(_) => true,
        Guarded::GGuarded {
            qua: Quantifier::Ex,
            ..
        } => true,
        Guarded::GGuarded {
            qua: Quantifier::All,
            vars,
            guards,
            body,
        } if vars.is_empty() && guards.len() == 1 => {
            let body_is_false = matches!(&**body, Guarded::Disj(v) if v.is_empty());
            body_is_false
                && matches!(
                    &guards[0],
                    ProtoAtom::Less(_, _) | ProtoAtom::Subterm(_, _) | ProtoAtom::Last(_),
                )
        }
        _ => false,
    }
}

/// Smart `Conj` — recursively flatten nested `Conj`s and short-circuit.
/// HS-faithful: mirrors Haskell `gconj` (Guarded.hs), whose helper
/// `flatten (GConj conj) = concatMap flatten $ getConj conj`
/// recursively unwraps every level of nested conjunction.  Must flatten
/// EVERY level (not just one): a binary-And chain parsed as
/// `Conj(Conj(Conj(a, b), c), d)` must collapse to a single 4-item Conj,
/// else the runtime sees a 2-item Conj and mismatches HS's
/// case-enumeration shape.
pub fn gconj(items: Vec<Guarded>) -> Guarded {
    fn flatten(item: Guarded, out: &mut Vec<Guarded>) -> bool {
        // returns true if gfalse encountered (absorbs)
        match item {
            Guarded::Conj(inner) => {
                for x in inner.iter() {
                    if flatten(x.clone(), out) {
                        return true;
                    }
                }
                false
            }
            x if x == gfalse() => true,
            x => {
                out.push(x);
                false
            }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) {
            return gfalse();
        }
    }
    // HS-faithful: mirror `gconj`'s `nub` BEFORE the `[gf] -> gf`
    // singleton unwrap, so the result is a fixpoint of `gconj` itself:
    // `gconj [a, a]` must be `a`, not the non-normal singleton `Conj [a]`
    // that only a second application would unwrap.  `normalise_guarded_cow`
    // relies on this one-pass idempotence.
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) {
            deduped.push(x);
        }
    }
    if deduped.len() == 1 {
        return deduped.into_iter().next().unwrap();
    }
    Guarded::Conj(deduped.into())
}

/// Smart `Disj` — flatten one level, short-circuit on `gtrue`, drop
/// `gfalse` items.  Mirrors Haskell's `gdisj` which treats `Disj` as a
/// set semantically: True absorbs, False is the unit.  Without dropping
/// gfalse items, partial_atom_valuation can turn `Disj([Eq(j,i),
/// Less(i,j)])` into `Disj([gfalse, gfalse])` (when j<i is known via
/// the order graph) and we'd split a 2-case Disj goal whose branches
/// both close — Haskell collapses this to `gfalse` directly.
pub fn gdisj(items: Vec<Guarded>) -> Guarded {
    // Recursively flatten nested `Disj`s. HS-faithful: mirrors Haskell
    // `gdisj` (Guarded.hs:426-437) whose helper
    // `flatten (GDisj disj) = concatMap flatten $ getDisj disj`
    // recursively unwraps every level. Must flatten EVERY level (not just
    // one): a 5-way `∨` parsed as a binary `Or` chain
    // (`Disj(Disj(Disj(Disj(a, b), c), d), e)`) must collapse to a single
    // 5-alt Disj goal, else the runtime sees a 2-alt Disj and mismatches
    // the case-enumeration of skeleton proofs like YubiSecure
    // slightly_weaker_invariant.
    fn flatten(item: Guarded, out: &mut Vec<Guarded>) -> bool {
        // returns true if gtrue encountered (absorbs)
        match item {
            Guarded::Disj(inner) => {
                for x in inner.iter() {
                    if flatten(x.clone(), out) {
                        return true;
                    }
                }
                false
            }
            x if x == gtrue() => true,
            x if x == gfalse() => false,
            x => {
                out.push(x);
                false
            }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) {
            return gtrue();
        }
    }
    // HS-faithful: the `[gf] -> gf` singleton unwrap matches the FLATTENED,
    // non-nubbed list (Guarded.hs:426-437, see line 428); `nub` is applied only in the
    // otherwise branch (`GDisj $ Disj $ nub gfs`, Guarded.hs:426-437, see line 434).  So a
    // flattened list like `[a,a]` is not a singleton and yields
    // `Disj (nub [a,a]) = Disj [a]`, NOT bare `a`.  (Note: this `out`
    // already has `gfalse` items dropped — see flatten above — so the
    // empty case below collapses an all-`gfalse` disjunction to `gfalse`.)
    if out.len() == 1 {
        return out.into_iter().next().unwrap();
    }
    // Mirror Haskell `gdisj`'s `nub gfs` (Guarded.hs:426-437, see line 434).
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) {
            deduped.push(x);
        }
    }
    if deduped.is_empty() {
        gfalse()
    } else {
        Guarded::Disj(deduped.into())
    }
}

/// Smart `GGuarded(Ex, ...)` — direct port of Haskell's `gex`:
/// ```text
///   gex []  as  gf                = gconj (map GAto as ++ [gf])
///   gex _   _   gf | gf == gfalse = gfalse
///   gex ss  as  gf                = GGuarded Ex ss as gf
/// ```
pub fn gex(vars: Vec<(String, LSort)>, guards: Vec<Atom<BLNTerm>>, body: Guarded) -> Guarded {
    if vars.is_empty() {
        let mut items: Vec<Guarded> = guards.into_iter().map(Guarded::Atom).collect();
        items.push(body);
        return gconj(items);
    }
    if body == gfalse() {
        return gfalse();
    }
    Guarded::GGuarded {
        qua: Quantifier::Ex,
        vars: vars.into(),
        guards: guards.into(),
        body: std::sync::Arc::new(body),
    }
}

/// Smart `GGuarded(All, ...)` — direct port of Haskell's `gall`:
/// ```text
///   gall _   []   gf              = gf
///   gall _   _    gf | gf == gtrue = gtrue
///   gall ss  atos gf              = GGuarded All ss atos gf
/// ```
pub fn gall(vars: Vec<(String, LSort)>, guards: Vec<Atom<BLNTerm>>, body: Guarded) -> Guarded {
    if guards.is_empty() {
        return body;
    }
    if body == gtrue() {
        return gtrue();
    }
    Guarded::GGuarded {
        qua: Quantifier::All,
        vars: vars.into(),
        guards: guards.into(),
        body: std::sync::Arc::new(body),
    }
}

/// Walk a guarded formula and replace atoms whose truth value the
/// caller's `valuation` returns `Some(_)`. Mirrors Haskell's
/// `Theory.Constraint.System.Guarded.simplifyGuardedOrReturn`
/// (Guarded.hs:665-698).
///
/// Cases:
/// - `Atom a` becomes `gtrue`/`gfalse` if the valuation is decided;
///   otherwise unchanged.
/// - `Conj` / `Disj` recurse and re-build via `gconj` / `gdisj` so
///   short-circuits collapse the right way.
/// - `GGuarded(All, [], guards, body)`: if any guard is False the
///   whole universal is True; otherwise drop guards that evaluate to
///   True and keep only the unknown ones, then recurse on the body.
/// - Guarded quantifiers with bound vars are left intact — the body
///   gets simplified once the quantifier is gone (matches Haskell).
pub fn simplify_guarded_with(
    fm: &Guarded,
    valuation: &dyn Fn(&Atom<LNTerm>) -> Option<bool>,
) -> Guarded {
    // HS `simplifyGuardedOrReturn` calls `valuation =<< unbindAtom ato`
    // (Guarded.hs:679), which is `Nothing` whenever any `Bound` leaf is
    // present.
    let eval = |a: &Atom<BLNTerm>| -> Option<bool> { unbind_atom(a).and_then(|la| valuation(&la)) };
    match fm {
        Guarded::Atom(a) => match eval(a) {
            Some(true) => gtrue(),
            Some(false) => gfalse(),
            None => fm.clone(),
        },
        Guarded::Disj(items) => {
            let simplified: Vec<_> = items
                .iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gdisj(simplified)
        }
        Guarded::Conj(items) => {
            let simplified: Vec<_> = items
                .iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gconj(simplified)
        }
        Guarded::GGuarded {
            qua: Quantifier::All,
            vars,
            guards,
            body,
        } if vars.is_empty() => {
            let evals: Vec<Option<bool>> = guards.iter().map(eval).collect();
            // Any False guard → universal vacuously holds.
            if evals.iter().any(|v| v == &Some(false)) {
                return gtrue();
            }
            // Keep only the Unknown guards — True guards are vacuous.
            let kept: Vec<Atom<BLNTerm>> = guards
                .iter()
                .zip(&evals)
                .filter(|(_, v)| v.is_none())
                .map(|(a, _)| a.clone())
                .collect();
            let body_s = simplify_guarded_with(body, valuation);
            // HS-faithful: `simp` builds the universal via `gall [] (...) (simp
            // gf)` (Guarded.hs:665-698, see line 689).  `gall` collapses to the body when the
            // kept guards are empty AND collapses the whole universal to
            // `gtrue` when the simplified body is `gtrue` (Guarded.hs:449-453, see line 452),
            // regardless of whether guards remain.  Building `GGuarded`
            // directly would leave a non-canonical `GGuarded{All,[],kept,
            // gtrue}` where Haskell produces `gtrue`.
            gall(vars.to_vec(), kept, body_s)
        }
        // Quantifiers with bound vars stay as-is — Haskell delays
        // simplification past the binder.
        Guarded::GGuarded { .. } => fm.clone(),
    }
}

// =============================================================================
// Errors
// =============================================================================

#[derive(Debug, Clone)]
pub struct GuardError {
    pub message: String,
    /// The sub-formula at the point of failure — HS's `f0` in
    /// `convert polarity f0@(Qua qua0 _ _)` (Guarded.hs:499), the innermost
    /// quantifier whose guard check failed.  Callers quote it above the
    /// whole formula, as HS's `ppError` does (Guarded.hs:477-479):
    ///   ```text
    ///   <error_text>
    ///     "<sub_formula>"
    ///   in the formula
    ///     "<full_formula>"
    ///   ```
    /// Its enclosing binders are already opened, so it prints on its own
    /// through [`crate::pretty_formula::lnformula_doc`].  `None` for a
    /// failure outside a quantifier.
    pub subject_formula: Option<crate::formula::LNFormula>,
    /// The quoted variable names of HS `noUnguardedVars` (Guarded.hs:507-514),
    /// which builds its message with `fsep` over one `Doc` per name.  Empty
    /// for every other failure, whose message is a single `text`.
    pub unguarded_vars: Vec<String>,
}

impl GuardError {
    /// The message as the `Doc` HS throws (Guarded.hs:507-514 and
    /// Guarded.hs:561-563).
    /// The unguarded-variable list is an `fsep`, so it wraps at the width
    /// and nesting the caller renders it at; every other message is one
    /// `text` on a single line.
    pub fn message_doc(&self) -> crate::pretty_hpj::Doc {
        use crate::pretty_hpj::{fsep, punctuate, Doc};
        if self.unguarded_vars.is_empty() {
            return Doc::text(&self.message);
        }
        let mut parts = vec![Doc::text("unguarded variable(s)")];
        parts.extend(punctuate(
            Doc::text(","),
            self.unguarded_vars.iter().map(Doc::text).collect(),
        ));
        parts.extend(["in", "the", "subformula"].into_iter().map(Doc::text));
        fsep(parts)
    }
}

impl std::fmt::Display for GuardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for GuardError {}

fn err(msg: impl Into<String>) -> GuardError {
    GuardError {
        message: msg.into(),
        subject_formula: None,
        unguarded_vars: Vec::new(),
    }
}

// =============================================================================
// Substitutions of bound for free and vice versa (Guarded.hs:289-352)
// =============================================================================

/// HS `bvarToLVar` (Guarded.hs:322-327): read an atom of a locally-nameless
/// formula whose binders are all opened as an atom over plain `LVar`s.  A
/// surviving `Bound` index is HS's `boundError`.
pub fn bvar_to_lvar(a: &Atom<BLNTerm>) -> Atom<LNTerm> {
    map_atom(a, &mut |t| {
        map_lits(t, &mut |l| match l {
            Lit::Con(c) => Lit::Con(*c),
            Lit::Var(BVar::Free(v)) => Lit::Var(*v),
            Lit::Var(BVar::Bound(i)) => panic!("bvarToLVar: left-over bound variable '{i}'"),
        })
    })
}

/// HS `bTermToLTerm` (Guarded.hs:335-338): read a term of a locally-nameless
/// formula whose binders are all opened as a term over plain `LVar`s.  A
/// surviving `Bound` index is HS's `boundError`.
pub fn bterm_to_lterm(t: &BLNTerm) -> LNTerm {
    map_lits(t, &mut |l| match l {
        Lit::Con(c) => Lit::Con(*c),
        Lit::Var(BVar::Free(v)) => Lit::Var(*v),
        Lit::Var(BVar::Bound(i)) => panic!("bvarToLVar: left-over bound variable '{i}'"),
    })
}

/// HS `unbindAtom` (Guarded.hs:351-352): the atom over plain `LVar`s when it
/// carries no `Bound` leaf, `None` otherwise.
pub fn unbind_atom(a: &Atom<BLNTerm>) -> Option<Atom<LNTerm>> {
    fn has_bound(t: &BLNTerm) -> bool {
        match t {
            Term::Lit(Lit::Var(BVar::Bound(_))) => true,
            Term::Lit(_) => false,
            Term::App(_, args) => args.iter().any(has_bound),
        }
    }
    let mut bound = false;
    fold_atom(a, &mut |t| bound |= has_bound(t));
    if bound {
        None
    } else {
        Some(bvar_to_lvar(a))
    }
}

/// Lift an atom over plain `LVar`s into the locally-nameless one, every
/// variable free.  HS `fmap (fmapTerm (fmap Free))` (Guarded.hs:378),
/// [`crate::formula::lift_free`] per term.
pub fn lift_free_atom(a: &Atom<LNTerm>) -> Atom<BLNTerm> {
    map_atom(a, &mut lift_free)
}

/// HS `substFreeAtom` (Guarded.hs:308-317): replace every free variable in
/// `dom(s)` by the De Bruijn index `s` gives it.  `fmap (fmapTerm (fmap …))`
/// rebuilds each application through `fApp`, so an AC or `C` argument list is
/// re-sorted under `Bound i < Free x` (LTerm.hs:476-478, Raw.hs:119-134).
pub fn subst_free_atom(s: &[(LVar, u64)], a: &Atom<BLNTerm>) -> Atom<BLNTerm> {
    subst_free_atom_at(s, 0, a)
}

fn subst_free_atom_at(s: &[(LVar, u64)], depth: u64, a: &Atom<BLNTerm>) -> Atom<BLNTerm> {
    map_atom(a, &mut |t| {
        map_lits(t, &mut |l| match l {
            Lit::Var(BVar::Free(x)) => match s.iter().find(|(v, _)| v == x) {
                Some((_, i)) => Lit::Var(BVar::Bound(i + depth)),
                None => l.clone(),
            },
            _ => l.clone(),
        })
    })
}

/// HS `substFree` (Guarded.hs:319-320): [`subst_free_atom`] at every atom,
/// with the index shifted by the number of binders crossed.
pub fn subst_free(s: &[(LVar, u64)], g: &Guarded) -> Guarded {
    map_guarded_atoms(g, &mut |j, a| subst_free_atom_at(s, j, a))
}

/// HS `substBoundAtom` (Guarded.hs:289-296): replace every bound index in
/// `dom(s)` by the free variable `s` gives it, rebuilding through `fApp` as
/// [`subst_free_atom`] does.
pub fn subst_bound_atom(s: &[(u64, LVar)], a: &Atom<BLNTerm>) -> Atom<BLNTerm> {
    subst_bound_atom_at(s, 0, a)
}

fn subst_bound_atom_at(s: &[(u64, LVar)], depth: u64, a: &Atom<BLNTerm>) -> Atom<BLNTerm> {
    map_atom(a, &mut |t| {
        map_lits(t, &mut |l| match l {
            Lit::Var(BVar::Bound(n)) => {
                match s.iter().find(|(i, _)| i.checked_add(depth) == Some(*n)) {
                    Some((_, v)) => Lit::Var(BVar::Free(*v)),
                    None => l.clone(),
                }
            }
            _ => l.clone(),
        })
    })
}

/// HS `substBound` (Guarded.hs:301-302): [`subst_bound_atom`] at every atom,
/// with the index shifted by the number of binders crossed.
pub fn subst_bound(s: &[(u64, LVar)], g: &Guarded) -> Guarded {
    map_guarded_atoms(g, &mut |j, a| subst_bound_atom_at(s, j, a))
}

/// Port of HS `mapGuardedAtoms :: (Integer -> a -> b) -> LGuarded a ->
/// LGuarded b`: the single depth-tracking recursor shared by every eager
/// per-atom rewrite over `Guarded`.  `f` receives the scope depth (number
/// of binders crossed) and each atom; the rebuilt tree preserves structure,
/// quantifier blocks, and traversal order.  Guards of a `GGuarded` are
/// mapped — and the body recursed — at `depth + vars.len()`, so an atom
/// under `n` binders is always handed `depth == n`.
fn map_guarded_atoms<F: FnMut(u64, &Atom<BLNTerm>) -> Atom<BLNTerm>>(
    g: &Guarded,
    f: &mut F,
) -> Guarded {
    fn rec<F: FnMut(u64, &Atom<BLNTerm>) -> Atom<BLNTerm>>(
        g: &Guarded,
        depth: u64,
        f: &mut F,
    ) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(f(depth, a)),
            Guarded::Disj(items) => Guarded::Disj(items.iter().map(|i| rec(i, depth, f)).collect()),
            Guarded::Conj(items) => Guarded::Conj(items.iter().map(|i| rec(i, depth, f)).collect()),
            Guarded::GGuarded {
                qua,
                vars,
                guards,
                body,
            } => {
                let new_depth = depth + vars.len() as u64;
                Guarded::GGuarded {
                    qua: *qua,
                    vars: vars.clone(),
                    guards: guards.iter().map(|a| f(new_depth, a)).collect(),
                    body: std::sync::Arc::new(rec(body, new_depth, f)),
                }
            }
        }
    }
    rec(g, 0, f)
}

/// Returns `true` if the formula is "safety": closed (no free vars)
/// and contains no existential quantifier in its guarded form.  HS
/// `isSafetyFormula` (Guarded.hs:154-165).
pub fn is_safety_formula(g: &Guarded) -> bool {
    fn no_existential(g: &Guarded) -> bool {
        match g {
            Guarded::Atom(_) => true,
            Guarded::GGuarded {
                qua: Quantifier::Ex,
                ..
            } => false,
            Guarded::GGuarded {
                qua: Quantifier::All,
                body,
                ..
            } => no_existential(body),
            Guarded::Disj(inner) => inner.iter().all(no_existential),
            Guarded::Conj(inner) => inner.iter().all(no_existential),
        }
    }
    is_closed(g) && no_existential(g)
}

/// Is `g` closed (no free variables)?  HS `null (frees [gf0])`
/// (Guarded.hs:156).
pub fn is_closed(g: &Guarded) -> bool {
    let mut any = false;
    g.for_each_free(&mut |_| any = true);
    !any
}

/// Find the maximum variable idx used in a guarded formula. Used
/// to allocate fresh indices without collisions.
pub fn max_var_idx(g: &Guarded) -> u64 {
    let mut m = 0u64;
    g.for_each_free(&mut |v| {
        if v.idx > m {
            m = v.idx;
        }
    });
    m
}

/// Is every AC and `C` argument list in `g` sorted?
///
/// [`map_lits`] rebuilds each application through `f_app`, which sorts those
/// two argument lists (Raw.hs:119-134) and leaves every other one alone, so a
/// formula equals its identity map exactly when it is already in that form.
/// [`insert_formula`](crate::constraint::solver::reduction::Reduction::insert_formula)
/// checks it with `debug_assert!` at the store boundary.
pub fn is_ac_canonical(g: &Guarded) -> bool {
    map_guarded_atoms(g, &mut |_, a| {
        map_atom(a, &mut |t| map_lits(t, &mut |l| l.clone()))
    }) == *g
}

// =============================================================================
// Opening and closing (Guarded.hs:358-384)
// =============================================================================

/// Build the substitution HS `closeGuarded` uses: `s = zip (reverse vs) [0..]`
/// (Guarded.hs:382).  Given `vs = [v0, …, v_{k-1}]` (outer→inner lexical
/// order), returns `[(v_{k-1}, 0), …, (v_0, k-1)]`.
fn close_subst(vs: &[LVar]) -> Vec<(LVar, u64)> {
    let k = vs.len();
    vs.iter()
        .enumerate()
        .rev()
        .map(|(i, v)| (*v, (k - 1 - i) as u64))
        .collect()
}

/// Build the substitution HS `openGuarded` uses: `subst xs = zip [0..]
/// (reverse xs)` (Guarded.hs:372).  Given `xs = [x0, …, x_{k-1}]` (binder
/// lexical order), returns `[(0, x_{k-1}), …, (k-1, x_0)]`.
fn open_subst(xs: &[LVar]) -> Vec<(u64, LVar)> {
    xs.iter()
        .rev()
        .enumerate()
        .map(|(i, v)| (i as u64, *v))
        .collect()
}

/// HS `openGuarded` (Guarded.hs:364-373): `Some((qua, xs, ats, gf))` for a
/// `GGuarded`, `None` for every other shape.  One variable is drawn per binder
/// through `fresh_ident` (HS `freshLVar n s`, LTerm.hs:301-302), and both the
/// guards and the body get this binder's De Bruijn indices replaced by the
/// drawn variables.  Each guard is then read over plain variables
/// ([`bvar_to_lvar`]); the body keeps the indices of the binders inside it,
/// which the next `open_guarded` draws.
pub fn open_guarded(
    g: &Guarded,
    fresh: &mut dyn MonadFresh,
) -> Option<(Quantifier, Vec<LVar>, Vec<Atom<LNTerm>>, Guarded)> {
    let Guarded::GGuarded {
        qua,
        vars,
        guards,
        body,
    } = g
    else {
        return None;
    };
    // HS `xs <- mapM (\(n,s) -> freshLVar n s) vs`.
    let xs: Vec<LVar> = vars
        .iter()
        .map(|(n, s)| LVar::new(n, *s, fresh.fresh_ident(n)))
        .collect();
    let s = open_subst(&xs);
    let ats: Vec<Atom<LNTerm>> = guards
        .iter()
        .map(|a| bvar_to_lvar(&subst_bound_atom(&s, a)))
        .collect();
    Some((*qua, xs, ats, subst_bound(&s, body)))
}

/// HS `closeGuarded` (Guarded.hs:376-384): bind `xs` in `atoms` and `body`,
/// then build the quantifier through its smart constructor.  Each binder keeps
/// only its name and sort (`vs' = map (lvarName &&& lvarSort) vs`).
pub fn close_guarded(
    qua: Quantifier,
    xs: Vec<LVar>,
    atoms: Vec<Atom<LNTerm>>,
    body: Guarded,
) -> Guarded {
    let s = close_subst(&xs);
    let new_guards: Vec<Atom<BLNTerm>> = atoms
        .iter()
        .map(|a| subst_free_atom(&s, &lift_free_atom(a)))
        .collect();
    let new_body = subst_free(&s, &body);
    let vs: Vec<(String, LSort)> = xs.iter().map(|v| (v.name.to_string(), v.sort)).collect();
    match qua {
        Quantifier::Ex => gex(vs, new_guards, new_body),
        Quantifier::All => gall(vs, new_guards, new_body),
    }
}

/// Compute which of `xs` are NOT bound by any of `atoms`, as POSITIONS in
/// `xs`. Mirrors Haskell's `remainingUnguarded` (Guarded.hs:523-533), whose
/// `ug0 \\ frees ...` likewise preserves the prefix order of the survivors.
/// Positions rather than variables so the caller can name each survivor from
/// the parallel freshened prefix (see [`unguarded_error`]).
///
/// The working set is a `[LVar]` and `\\`/`intersect` use `Eq LVar`
/// (LTerm.hs:541-542) — name, sort and index together.  So under
/// `All x. ... ==> All x.1 z. <x.1,z> = x`, the guard covers the binders `x.1`
/// and `z` even though its right-hand side mentions the *outer* `x`, which is
/// a different variable.
///
/// HS sorts the atoms with `sortGAtoms` (Guarded.hs:193-194), a stable
/// partition placing actions before equalities.
fn remaining_unguarded(xs: &[LVar], atoms: &[Atom<LNTerm>]) -> Vec<usize> {
    let mut sorted_atoms: Vec<&Atom<LNTerm>> = atoms.iter().collect();
    sorted_atoms.sort_by_key(|a| if a.is_action() { 0 } else { 1 });
    let mut unguarded: BTreeSet<LVar> = xs.iter().copied().collect();
    for atom in &sorted_atoms {
        match atom {
            // HS `frees (a, fa)` over `GAction a fa`: every variable of the
            // timepoint and of the fact.
            ProtoAtom::Action(t, fact) => {
                for v in frees(&(t.clone(), fact.clone())) {
                    unguarded.remove(&v);
                }
            }
            ProtoAtom::EqE(s, t) => {
                let sv = frees(s);
                let tv = frees(t);
                let s_covered = sv.iter().all(|k| !unguarded.contains(k));
                let t_covered = tv.iter().all(|k| !unguarded.contains(k));
                if s_covered {
                    for k in tv {
                        unguarded.remove(&k);
                    }
                } else if t_covered {
                    for k in sv {
                        unguarded.remove(&k);
                    }
                }
            }
            _ => {}
        }
    }
    xs.iter()
        .enumerate()
        .filter(|(_, v)| unguarded.contains(v))
        .map(|(i, _)| i)
        .collect()
}

/// Render HS `noUnguardedVars` (Guarded.hs:507-514) for the survivors at
/// `positions` of the quantifier prefix.  The names come from `freshened` —
/// the prefix as `openFormulaPrefix` renamed it — so a binder shadowing an
/// already-opened one is reported as `x.1`, not `x`.
fn unguarded_error(positions: &[usize], freshened: &[LVar]) -> GuardError {
    // HS: `map (quotes . text . show) unguarded` (Guarded.hs:507-514, see line 511)
    // over `[LVar]`, whose `show` is the EXPLICIT `instance Show LVar`
    // (LTerm.hs:550-557) that `Display for LVar` ports.
    let names: Vec<String> = positions
        .iter()
        .map(|&i| format!("'{}'", freshened[i]))
        .collect();
    let mut e = err(format!(
        "unguarded variable(s) {} in the subformula",
        names.join(", ")
    ));
    e.unguarded_vars = names;
    e
}

// =============================================================================
// Normal form of a stored formula
// =============================================================================

/// Rebuild a guarded formula bottom-up through the `gconj`/`gdisj` smart
/// constructors, restoring the normal form that formula conversion
/// (`convert`) establishes at creation: flattened, duplicate-free
/// connectives.  Port of HS `normaliseGuarded` (150f5eba).
/// NOTE: disjunctions are normalised CONSTRUCTOR-PRESERVING at every
/// level (`normalise_disj_list`), not via the full `gdisj`: a singleton
/// disjunction wrapping a conjunction is load-bearing for the S_∀
/// saturation dedup — `insert_formula` STORES disjunctions (formula +
/// `Goal::Disj` twin) but DECOMPOSES bare conjunctions without storing
/// them, so unwrapping the singleton turns a storable, dedupable derived
/// instance into one that re-fires every simplifier iteration (livelock
/// on ake/bilinear/TAK1_eCK_like.spthy).  Conjunctions use the full
/// `gconj` (their singleton unwrap is harmless because conjunctions are
/// decomposed on insertion anyway); this requires `gconj` to be
/// idempotent — see the note on `gconj`.
///
/// Copy-on-write: returns `None` when normalisation leaves `g` structurally
/// unchanged (so an owning caller can reuse `g` by move with zero
/// allocation), `Some(rebuilt)` otherwise.  Mirrors the `subst_guarded_cow`
/// convention (recursion returns `None` when all children are unchanged).
pub fn normalise_guarded_cow(g: &Guarded) -> Option<Guarded> {
    match g {
        // An atom carries no connectives to flatten → always unchanged.
        Guarded::Atom(_) => None,
        Guarded::Disj(items) => normalise_disj_list_cow(items).map(|v| Guarded::Disj(v.into())),
        Guarded::Conj(items) => {
            // Normalise children first (COW), then re-run the `gconj`
            // smart-constructor step (flatten nested Conj / absorb gfalse /
            // dedup / singleton-unwrap).  When no child changed AND `gconj`
            // is a structural no-op on the (already-normalised) children, the
            // whole node is unchanged.  Otherwise the rebuild is exactly
            // `gconj(children)`.
            let mapped = cow_map_vec(items, normalise_guarded_cow);
            let children: &[Guarded] = mapped.as_deref().unwrap_or(&items[..]);
            if mapped.is_none() && gconj_is_structural_noop(children) {
                None
            } else {
                Some(gconj(children.to_vec()))
            }
        }
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } =>
        // Only `body` can change; qua/vars/guards are cloned verbatim.
        {
            normalise_guarded_cow(body).map(|b| Guarded::GGuarded {
                qua: *qua,
                vars: vars.clone(),
                guards: guards.clone(),
                body: std::sync::Arc::new(b),
            })
        }
    }
}

/// `gconj(items) == Guarded::Conj(items)` — i.e. the `gconj` smart
/// constructor is a structural no-op on this (already child-normalised)
/// list.  True iff none of `gconj`'s transformations fire: no nested-`Conj`
/// child to flatten (including an empty `Conj` = `gtrue`, which `gconj`
/// drops), no `gfalse` (`Disj([])`) child to absorb, no duplicate to `nub`,
/// and length != 1 (which would singleton-unwrap).  Keep in exact lock-step
/// with `gconj`.
fn gconj_is_structural_noop(items: &[Guarded]) -> bool {
    if items.len() == 1 {
        return false;
    }
    for (i, x) in items.iter().enumerate() {
        if matches!(x, Guarded::Conj(_)) {
            return false; // flatten (incl. empty Conj = gtrue drop)
        }
        if matches!(x, Guarded::Disj(v) if v.is_empty()) {
            return false; // gfalse absorption
        }
        if items[..i].contains(x) {
            return false; // nub drops a duplicate
        }
    }
    true
}

/// Normalise the disjunct list of a stored disjunction WITHOUT changing
/// its constructor: each disjunct normalised, nested disjunctions
/// flattened one level, duplicates dropped — but no singleton unwrap and
/// no truth-value absorption, so a `Guarded::Disj` formula and its
/// `Goal::Disj` twin (same payload, different wrapper) stay in LOCKSTEP.
/// Port of HS `normaliseDisjList` (150f5eba); see that commit for why
/// full `gdisj` here desynchronises the twin stores (gcm livelock).
pub fn normalise_disj_list(items: &[Guarded]) -> Vec<Guarded> {
    normalise_disj_list_cow(items).unwrap_or_else(|| items.to_vec())
}

/// Copy-on-write variant of [`normalise_disj_list`]: `None` when the
/// constructor-preserving normalisation leaves the disjunct list unchanged
/// (every disjunct normalises in place, none is a nested `Disj` to flatten,
/// no duplicate to drop), `Some(rebuilt)` otherwise.  BYTE-IDENTICAL to
/// `normalise_disj_list(items)` in the `Some` case.
fn normalise_disj_list_cow(items: &[Guarded]) -> Option<Vec<Guarded>> {
    // Normalise each disjunct (COW); `children` is the normalised list — the
    // originals when `mapped` is `None` (all disjuncts unchanged).
    let mapped = cow_map_vec(items, normalise_guarded_cow);
    let children: &[Guarded] = mapped.as_deref().unwrap_or(items);
    if mapped.is_none() && disj_flatten_is_structural_noop(children) {
        None
    } else {
        Some(flatten_dedup_disj(children))
    }
}

/// `flatten_dedup_disj(items) == items` — the constructor-preserving disjunct
/// normalisation (one-level flatten of a nested `Disj`, then `nub`) is a
/// no-op.  True iff no disjunct is itself a `Disj` (any `Disj` has its wrapper
/// spliced away) and there is no duplicate.  Lock-step with
/// `flatten_dedup_disj`.
fn disj_flatten_is_structural_noop(items: &[Guarded]) -> bool {
    for (i, x) in items.iter().enumerate() {
        if matches!(x, Guarded::Disj(_)) {
            return false; // one-level flatten removes the Disj wrapper
        }
        if items[..i].contains(x) {
            return false; // nub drops a duplicate
        }
    }
    true
}

/// One-level flatten of nested `Disj`s + duplicate drop over an
/// already-normalised disjunct list.  This is the outer-loop body of
/// `normalise_disj_list` factored out so it runs on the COW-normalised
/// children; BYTE-IDENTICAL to that original loop (same push/dedup order).
fn flatten_dedup_disj(children: &[Guarded]) -> Vec<Guarded> {
    fn push(g: Guarded, out: &mut Vec<Guarded>) {
        if !out.contains(&g) {
            out.push(g);
        }
    }
    let mut out: Vec<Guarded> = Vec::new();
    for it in children {
        match it {
            Guarded::Disj(ds) => {
                for d in ds.iter() {
                    push(d.clone(), &mut out);
                }
            }
            g => push(g.clone(), &mut out),
        }
    }
    out
}

/// Normalise a formula for storage in the constraint system: full
/// smart-constructor normal form, except that a TOP-LEVEL disjunction
/// keeps its `Disj` constructor (via the constructor-preserving
/// `normalise_disj_list_cow`) so it stays in lockstep with its `Goal::Disj`
/// twin.  Port of HS `normaliseStoredFormula` (150f5eba).
///
/// Copy-on-write: `None` when unchanged, `Some(rebuilt)` otherwise.
pub fn normalise_stored_formula_cow(g: &Guarded) -> Option<Guarded> {
    match g {
        Guarded::Disj(items) => normalise_disj_list_cow(items).map(|v| Guarded::Disj(v.into())),
        _ => normalise_guarded_cow(g),
    }
}

/// Owned fast path for [`normalise_stored_formula_cow`]: consumes `g`,
/// returning it by MOVE (zero allocation) when normalisation is a no-op, else
/// the rebuilt tree.  For callers that own their input and immediately
/// reassign it.
pub fn normalise_stored_formula_owned(g: Guarded) -> Guarded {
    match normalise_stored_formula_cow(&g) {
        Some(n) => n,
        None => g,
    }
}

// =============================================================================
// Conversion to a guarded formula
// =============================================================================

/// HS `formulaToGuarded` (Guarded.hs:471-479): the whole traversal runs
/// inside one `Precise.FreshT` seeded with `avoidPrecise fmOrig`, so every
/// quantifier prefix it opens draws its binders from a single supply.
pub fn formula_to_guarded(f: &crate::formula::LNFormula) -> Result<Guarded, GuardError> {
    let mut fresh = crate::formula::avoid_precise_lnformula(f);
    convert(false, f, &mut fresh)
}

/// [`formula_to_guarded`] on a parser-AST formula, closed by
/// [`crate::formula::from_parser`] and stripped of its sugar by
/// [`crate::formula::to_lnformula`].  Both steps report a [`GuardError`], so
/// a caller that cannot build the internal formula still renders the same
/// block a guardedness failure renders.
///
/// Callers: the `--parse-only` open renderers (`pretty_theory.rs`,
/// `is_safety_formula_parsed` among them), and the disjunction arm of
/// `elaborate::goal_from_parsed`, which reads a stored goal's disjuncts
/// against the theory's signature.
pub fn formula_to_guarded_parsed(
    f: &p::Formula,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Result<Guarded, GuardError> {
    let syn = crate::formula::from_parser(f, sig).map_err(|e| err(e.message))?;
    let plain = crate::formula::to_lnformula(&syn).ok_or_else(|| err("unexpanded predicate"))?;
    formula_to_guarded(&plain)
}

/// HS `convert` (Guarded.hs:481-505,565-566).  `polarity` is the implicit
/// negation the conversion carries: at `True` the guarded formula returned
/// is equivalent to the negation of `f`.
fn convert(
    polarity: bool,
    f: &crate::formula::LNFormula,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    use crate::formula::{open_formula_prefix, Connective, ProtoFormula, Quantifier};
    match f {
        ProtoFormula::Tf(b) => Ok(gtf(polarity != *b)),
        ProtoFormula::Atom(a) => {
            if polarity {
                Ok(gnot_atom(a))
            } else {
                Ok(Guarded::Atom(a.clone()))
            }
        }
        ProtoFormula::Not(g) => convert(!polarity, g, fresh),
        ProtoFormula::Conn(Connective::And, a, b) => {
            let sub = vec![convert(polarity, a, fresh)?, convert(polarity, b, fresh)?];
            Ok(if polarity { gdisj(sub) } else { gconj(sub) })
        }
        ProtoFormula::Conn(Connective::Or, a, b) => {
            let sub = vec![convert(polarity, a, fresh)?, convert(polarity, b, fresh)?];
            Ok(if polarity { gconj(sub) } else { gdisj(sub) })
        }
        ProtoFormula::Conn(Connective::Imp, a, b) => {
            // p ⇒ q is ¬p ∨ q.
            let nag = convert(!polarity, a, fresh)?;
            let cag = convert(polarity, b, fresh)?;
            let sub = vec![nag, cag];
            Ok(if polarity { gconj(sub) } else { gdisj(sub) })
        }
        // p ↔ q is (p ⇒ q) ∧ (q ⇒ p), and HS conjoins the two arms at both
        // polarities (Guarded.hs:565-566).
        ProtoFormula::Conn(Connective::Iff, a, b) => {
            let lhs = ProtoFormula::Conn(Connective::Imp, a.clone(), b.clone());
            let rhs = ProtoFormula::Conn(Connective::Imp, b.clone(), a.clone());
            Ok(gconj(vec![
                convert(polarity, &lhs, fresh)?,
                convert(polarity, &rhs, fresh)?,
            ]))
        }
        // The quantifier decides whether the body must be a top-level
        // implication (`convAll`) or a conjunction (`convEx`); the polarity
        // decides which quantifier the guarded formula carries and which
        // polarity the sub-formulas take (Guarded.hs:499-505).  The whole
        // prefix of like quantifiers is opened at once, each binder drawn
        // fresh and substituted into the body, so the guard check and the
        // diagnostic name the binders HS names.
        ProtoFormula::Qua(qua0, _, _) => {
            let (xs, _, body) = open_formula_prefix(f, fresh);
            let result = match qua0 {
                Quantifier::All => {
                    let out_qua = if polarity {
                        Quantifier::Ex
                    } else {
                        Quantifier::All
                    };
                    convert_all(&xs, &body, polarity, out_qua, fresh)
                }
                Quantifier::Ex => {
                    let out_qua = if polarity {
                        Quantifier::All
                    } else {
                        Quantifier::Ex
                    };
                    convert_ex(&xs, &body, polarity, out_qua, fresh)
                }
            };
            // Both throws of this arm quote `ppFormula f0`, the quantifier
            // sub-formula they were reached through (Guarded.hs:513, :562),
            // and the exception carries that quote out unchanged — so the
            // innermost quantifier is the one named, which the guard below
            // reproduces by setting the field once.
            result.map_err(|mut e| {
                if e.subject_formula.is_none() {
                    e.subject_formula = Some(f.clone());
                }
                e
            })
        }
    }
}

/// HS `convEx` (Guarded.hs:535-543): the body is a conjunction whose action
/// and equality atoms guard the prefix.
fn convert_ex(
    xs: &[LVar],
    body: &crate::formula::LNFormula,
    polarity: bool,
    out_qua: Quantifier,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    let (atoms, others) = split_conj_actions_eqs(body);
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded, xs));
    }
    let mut converted = Vec::with_capacity(others.len());
    for f in &others {
        converted.push(convert(polarity, f, fresh)?);
    }
    let body_guarded = if polarity {
        gdisj(converted)
    } else {
        gconj(converted)
    };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}

/// HS `convAll` (Guarded.hs:546-563): the body is an implication whose
/// antecedent guards the prefix.
fn convert_all(
    xs: &[LVar],
    body: &crate::formula::LNFormula,
    polarity: bool,
    out_qua: Quantifier,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    use crate::formula::{Connective, ProtoFormula};
    let ProtoFormula::Conn(Connective::Imp, ante, succ) = body else {
        return Err(err("universal quantifier without toplevel implication"));
    };
    let (atoms, ante_others) = split_conj_actions_eqs(ante);
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded, xs));
    }
    let mut sub = Vec::with_capacity(ante_others.len() + 1);
    for f in &ante_others {
        sub.push(convert(!polarity, f, fresh)?);
    }
    sub.push(convert(polarity, succ, fresh)?);
    let body_guarded = if polarity { gconj(sub) } else { gdisj(sub) };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}

/// HS `conjActionsEqs` (Guarded.hs:516-519): split a conjunction into the
/// action and equality atoms that can guard a binder and the sub-formulas
/// that cannot.  Each guarding atom is read over plain variables
/// ([`bvar_to_lvar`], HS `Left $ bvarToLVar a`, Guarded.hs:517-518), which is
/// what [`remaining_unguarded`] and [`close_guarded`] take.
fn split_conj_actions_eqs(
    f: &crate::formula::LNFormula,
) -> (Vec<Atom<LNTerm>>, Vec<crate::formula::LNFormula>) {
    use crate::formula::{Connective, ProtoFormula};
    fn rec(
        f: &crate::formula::LNFormula,
        atoms: &mut Vec<Atom<LNTerm>>,
        others: &mut Vec<crate::formula::LNFormula>,
    ) {
        match f {
            ProtoFormula::Conn(Connective::And, a, b) => {
                rec(a, atoms, others);
                rec(b, atoms, others);
            }
            ProtoFormula::Atom(a @ (ProtoAtom::Action(_, _) | ProtoAtom::EqE(_, _))) => {
                atoms.push(bvar_to_lvar(a))
            }
            other => others.push(other.clone()),
        }
    }
    let mut atoms = Vec::new();
    let mut others = Vec::new();
    rec(f, &mut atoms, &mut others);
    (atoms, others)
}

// =============================================================================
// Negate atoms (`gnotAtom` in Haskell)
// =============================================================================

/// `gnotAtom` — port of Haskell `Theory.Constraint.System.Guarded.gnotAtom`
/// (lib/theory/src/Theory/Constraint/System/Guarded.hs:410-412):
///
/// ```text
/// gnotAtom a = GGuarded All [] [a] gfalse
/// ```
///
/// Uniformly negates every atom by wrapping it in a universal
/// guarded ⊥: "for all traces in which `a` holds, ⊥" ≡ ¬a. This
/// is the right encoding for Less/Eq/Action/Last/Subterm alike,
/// independent of the term sort.
///
/// Do NOT decompose ¬EqE / ¬Less into `gdisj [Less, Less]`, nor encode
/// ¬Action as `gex [] [a] gfalse` (those belong only to
/// `toInductionHypothesis`, which DOES decompose Less for induction): the
/// disjunction form is semantically wrong for term-sort EqE since Less is
/// undefined between Msg/Fresh/Pub terms, and the Ex form is semantically
/// False rather than ¬Action.  See `Guarded.hs:410-412` vs
/// `Guarded.hs:618`.
fn gnot_atom(a: &Atom<BLNTerm>) -> Guarded {
    Guarded::GGuarded {
        qua: Quantifier::All,
        vars: Vec::new().into(),
        guards: vec![a.clone()].into(),
        body: std::sync::Arc::new(gfalse()),
    }
}

// =============================================================================
// Substitution of free variables
// =============================================================================

/// Copy-on-write application of an [`LNSubst`] to a locally-nameless term.
/// HS `apply subst = (`bindTerm` applyBLLit)` with
/// `applyBLLit (Var (Free v)) = maybe (lit l) (fmapTerm (fmap Free)) (imageOf subst v)`
/// (SubstVFree.hs:297-302): a `Bound` leaf is left alone and every rebuilt
/// application goes through `fApp`, so AC and `C` argument lists re-sort.
///
/// `None` when the substitution touches no leaf, so the caller can reuse its
/// input.  A domain hit always changes the leaf, because a `Subst` drops the
/// `x ~> x` mappings as it is built (SubstVFree.hs:163-165).
fn subst_blnterm_cow(t: &BLNTerm, s: &LNSubst) -> Option<BLNTerm> {
    match t {
        Term::Lit(Lit::Var(BVar::Free(v))) => s.image_of(v).map(lift_free),
        Term::Lit(_) => None,
        Term::App(sym, args) => {
            cow_map_vec(&args[..], |a| subst_blnterm_cow(a, s)).map(|new| f_app(*sym, new))
        }
    }
}

fn subst_gatom_cow(a: &Atom<BLNTerm>, s: &LNSubst) -> Option<Atom<BLNTerm>> {
    match a {
        ProtoAtom::EqE(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| ProtoAtom::EqE(a, b)),
        ProtoAtom::Less(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| ProtoAtom::Less(a, b)),
        ProtoAtom::Subterm(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| ProtoAtom::Subterm(a, b)),
        ProtoAtom::Action(t, f) => cow_pair(t, subst_blnterm_cow(t, s), f, subst_gfact_cow(f, s))
            .map(|(t, f)| ProtoAtom::Action(t, f)),
        ProtoAtom::Last(t) => subst_blnterm_cow(t, s).map(ProtoAtom::Last),
        ProtoAtom::Syntactic(_) => None,
    }
}

fn subst_gpair_cow(x: &BLNTerm, y: &BLNTerm, s: &LNSubst) -> Option<(BLNTerm, BLNTerm)> {
    cow_pair(x, subst_blnterm_cow(x, s), y, subst_blnterm_cow(y, s))
}

fn subst_gfact_cow(f: &Fact<BLNTerm>, s: &LNSubst) -> Option<Fact<BLNTerm>> {
    cow_map_arc(&f.terms, |a| subst_blnterm_cow(a, s)).map(|terms| f.with_terms(terms))
}

/// Apply an [`LNSubst`] to a guarded formula: each free leaf in the domain
/// takes its image, guards and body alike.  A `Bound` leaf is positional and
/// carries no variable identity, so a binder cannot capture an image variable.
///
/// HS `instance Apply LNSubst LNGuarded`: `apply subst = mapGuardedAtoms
/// (const $ apply subst)` (Guarded.hs:393-394).
pub fn subst_guarded(g: &Guarded, s: &LNSubst) -> Guarded {
    if s.is_empty() {
        return g.clone();
    }
    subst_guarded_cow(g, s).unwrap_or_else(|| g.clone())
}

/// Copy-on-write core of [`subst_guarded`]: returns `None` when the
/// substitution touches no free leaf anywhere in `g`, so a caller can reuse
/// `g` instead of deep-rebuilding the whole connective tree.  One level up
/// from `subst_blnterm_cow`, mirroring its shape; every `Some(_)` is
/// byte-identical to the eager rebuild (changed children rebuilt, unchanged
/// children cloned, in positional order).
pub fn subst_guarded_cow(g: &Guarded, s: &LNSubst) -> Option<Guarded> {
    match g {
        Guarded::Atom(a) => subst_gatom_cow(a, s).map(Guarded::Atom),
        Guarded::Disj(items) => cow_map_arc(items, |i| subst_guarded_cow(i, s)).map(Guarded::Disj),
        Guarded::Conj(items) => cow_map_arc(items, |i| subst_guarded_cow(i, s)).map(Guarded::Conj),
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => cow_pair(
            guards,
            cow_map_arc(guards, |a| subst_gatom_cow(a, s)),
            &**body,
            subst_guarded_cow(body, s),
        )
        .map(|(guards, body)| Guarded::GGuarded {
            qua: *qua,
            vars: vars.clone(),
            guards,
            body: std::sync::Arc::new(body),
        }),
    }
}

/// Rewrite every Maude-witness LVar named `x` (any idx) to its canonical
/// `idx == 0` form.  Used to dedup implied formulas in
/// `insertImpliedFormulas` where Maude unification mints a fresh witness
/// per call: two structurally-identical derivations from the same
/// (restriction, action-node) pair would otherwise have different witness
/// idx and bypass `Vec::contains`, causing solved_formulas to grow without
/// bound and the simplify loop to never converge.
///
/// We touch ONLY witness vars (name == "x"), canonicalising their idx to 0
/// while preserving name and sort — every other LVar (real protocol vars,
/// distinct named fresh values) keeps its identity, so the dedup doesn't
/// over-merge legitimately-distinct implications.
///
/// Copy-on-write: returns `None` when `g` carries no `x`-named witness var
/// with a non-zero idx (the common case — [`collect_witness_vars`] finds
/// nothing) OR when the witness substitution touches no leaf
/// (`subst_guarded_cow` returns `None`), so a caller can reuse `g` by
/// move/borrow instead of cloning.
pub fn normalize_witness_lvars_cow(g: &Guarded) -> Option<Guarded> {
    let subst = collect_witness_vars(g);
    if subst.is_empty() {
        return None;
    }
    subst_guarded_cow(g, &subst)
}

/// The `x`-named free leaves of `g`, each mapped to its own `idx == 0` form.
///
/// The witness set is exactly the free-leaf set `HasFrees` enumerates
/// (guards + body, all atom variants).  Keying by the whole `LVar` gives two
/// leaves that share a name and an index but differ in sort their own
/// canonical images, so visitation order is irrelevant to the result.
fn collect_witness_vars(g: &Guarded) -> LNSubst {
    let mut out: std::collections::BTreeMap<LVar, LNTerm> = std::collections::BTreeMap::new();
    g.for_each_free(&mut |v| {
        if v.name == "x" {
            out.insert(*v, var_term(LVar::new(v.name, v.sort, 0)));
        }
    });
    LNSubst::from_map(out)
}

// =============================================================================
// Free variables
// =============================================================================

/// HS `instance HasFrees (Guarded (String, LSort) c LVar)`
/// (Guarded.hs:272-276): `foldFrees f = foldMap (foldFrees f)` over the
/// `Foldable` instance (Guarded.hs:259-263) and `mapFrees f =
/// traverseGuarded (mapFrees f)` — atoms in tree order, `GGuarded` guards
/// before body, the binder list left alone.
///
/// The `monotone` flag is ignored: `traverseGuarded` rebuilds every term with
/// `traverseTerm`, which is `fApp`-based unconditionally
/// (Guarded.hs:265-268, Raw.hs:210-213), unlike `mapFrees` for a bare `Term`
/// (LTerm.hs:788-791).  So a rename re-sorts every AC and `C` argument list
/// under the mapped variables, whichever map mode the caller asked for.
impl HasFrees for Guarded {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        match self {
            Guarded::Atom(a) => fold_atom(a, &mut |t| t.for_each_free(f)),
            Guarded::Disj(xs) | Guarded::Conj(xs) => {
                for x in xs.iter() {
                    x.for_each_free(f);
                }
            }
            Guarded::GGuarded { guards, body, .. } => {
                for a in guards.iter() {
                    fold_atom(a, &mut |t| t.for_each_free(f));
                }
                body.for_each_free(f);
            }
        }
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, _monotone: bool) -> Self {
        map_guarded_atoms(&self, &mut |_d, a| {
            map_atom(a, &mut |t| {
                map_lits(t, &mut |l| match l {
                    Lit::Var(BVar::Free(v)) => Lit::Var(BVar::Free(f(*v))),
                    other => other.clone(),
                })
            })
        })
    }
}

// =============================================================================
// Top-level negation — port of Haskell's `gnot`.
// =============================================================================

/// `gnot`: structural negation of a guarded formula.
///   - `Atom a`        → `gnot_atom a`
///   - `Disj xs`       → `Conj (map gnot xs)`
///   - `Conj xs`       → `Disj (map gnot xs)`
///   - `All vs gs. gf` → `Ex vs. (gs ∧ ¬gf)` (i.e. `gs ∧ ¬gf` is the new body)
///   - `Ex vs gs. gf`  → `All vs. (gs ⇒ ¬gf)`
pub fn gnot(g: &Guarded) -> Guarded {
    match g {
        Guarded::Atom(a) => gnot_atom(a),
        Guarded::Disj(xs) => gconj(xs.iter().map(gnot).collect()),
        Guarded::Conj(xs) => gdisj(xs.iter().map(gnot).collect()),
        // Use the smart constructors `gex`/`gall` (NOT direct
        // GGuarded build) so that empty-quantifier collapses fire:
        // - `gnot(GGuarded(All, [], [Less i j], gfalse))` (== ¬(i<j))
        //   goes through `gex [] [Less i j] gtrue` → `gconj([Less i j, gtrue])`
        //   → `Less i j` (the atom), not a stale `GGuarded(Ex, [], [Less i j], gtrue)`.
        // Without this collapse, `to_induction_hypothesis` sees the body
        // as nested GGuarded and produces extra `¬(Less)` disjuncts in
        // the IH instead of collapsing them down — leading to a much
        // larger Disj at goal-split time. Mirrors Haskell:
        //   go (GGuarded All ss as gf) = gex  ss as (go gf)
        //   go (GGuarded Ex  ss as gf) = gall ss as (go gf)
        Guarded::GGuarded {
            qua: Quantifier::All,
            vars,
            guards,
            body,
        } => gex(vars.to_vec(), guards.to_vec(), gnot(body)),
        Guarded::GGuarded {
            qua: Quantifier::Ex,
            vars,
            guards,
            body,
        } => gall(vars.to_vec(), guards.to_vec(), gnot(body)),
    }
}

// =============================================================================
// Induction — port of `Theory.Constraint.System.Guarded.ginduct`
// =============================================================================

/// `satisfiedByEmptyTrace`: does the formula hold under the empty
/// trace (no actions)? Returns `Err` for atoms outside the scope of a
/// quantifier (formula is not doubly guarded).
pub fn satisfied_by_empty_trace(g: &Guarded) -> Result<bool, String> {
    match g {
        Guarded::Atom(_) => Err("atom outside the scope of a quantifier".to_string()),
        Guarded::Disj(xs) => {
            let mut any = false;
            for x in xs.iter() {
                if satisfied_by_empty_trace(x)? {
                    any = true;
                }
            }
            Ok(any)
        }
        Guarded::Conj(xs) => {
            // HS `liftM and . sequence . getConj` (Guarded.hs:588-594, see line 593):
            // `sequence` forces ALL conjuncts (failing if any is `Left`)
            // BEFORE reducing with `and`.  So we must evaluate every
            // conjunct and propagate any error rather than short-circuiting
            // on the first `Ok(false)`.
            let mut all = true;
            for x in xs.iter() {
                if !satisfied_by_empty_trace(x)? {
                    all = false;
                }
            }
            Ok(all)
        }
        Guarded::GGuarded { qua, .. } => Ok(matches!(qua, Quantifier::All)),
    }
}

/// Does the formula contain at least one action atom (anywhere)?
/// `containsAction` from Haskell's `ginduct`.
pub fn contains_action(g: &Guarded) -> bool {
    match g {
        // Haskell `containsAction = foldGuarded (const True) ...`
        // (Guarded.hs:636-637): the bare-atom handler is `const True`, so
        // EVERY atom (Action/Eq/Less/Last/Subterm) yields True — not
        // only Action atoms.
        Guarded::Atom(_) => true,
        Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().any(contains_action),
        Guarded::GGuarded { guards, body, .. } => {
            // Haskell `Guarded.hs:636-637`: `\_ _ as body -> not (null as) || body`.
            !guards.is_empty() || contains_action(body)
        }
    }
}

/// `toInductionHypothesis`: rewrite a doubly guarded formula into its
/// induction hypothesis form. Errors out on non-last-free formulas.
pub fn to_induction_hypothesis(g: &Guarded) -> Result<Guarded, String> {
    match g {
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => {
            if guards.iter().any(Atom::is_last) {
                return Err("formula not last-free".to_string());
            }
            let body2 = to_induction_hypothesis(body)?;
            // Emit `Last(v)` for every node-sorted bound variable.
            // Mirrors Haskell's
            //   lastAtos = [ Last (varTerm (Bound j))
            //              | (j, (_, LSortNode)) <- zip [0..] (reverse ss) ]
            // Haskell `reverse ss` (Guarded.hs:613-616, see line 615) — node-sorted binders
            // emitted in REVERSE quantifier order.  For `∀ k #i #j`, ss
            // reversed = [#j, #i, k] → lastAtos = [Last(#j), Last(#i)].
            // Without `.rev()`, our disj order is [#i, #j] (matches HS
            // case_2 first), inverting `case_1`/`case_2` labels for the
            // `last`-disjunction split and breaking proof-tree shape diff.
            // HS `lastAtos = do (j, (_, LSortNode)) <- zip [0..] (reverse ss);
            //                   return $ Last (varTerm (Bound j))`.
            // Iterate vars inner-to-outer (rev), filter to node-sorted,
            // assign DeBruijn `j = 0, 1, ...` in that order.
            let last_atos: Vec<Guarded> = vars
                .iter()
                .rev()
                .enumerate()
                .filter(|(_, v)| v.1 == LSort::Node)
                .map(|(j, _)| Guarded::Atom(ProtoAtom::Last(var_term(BVar::Bound(j as u64)))))
                .collect();
            match qua {
                Quantifier::All => {
                    // gex ss as (gconj (map gnotAtom lastAtos ++ [gf']))
                    let mut items: Vec<Guarded> = last_atos.iter().map(gnot).collect();
                    items.push(body2);
                    Ok(gex(vars.to_vec(), guards.to_vec(), gconj(items)))
                }
                Quantifier::Ex => {
                    // gall ss as (gdisj (map GAto lastAtos ++ [gf']))
                    let mut items = last_atos;
                    items.push(body2);
                    Ok(gall(vars.to_vec(), guards.to_vec(), gdisj(items)))
                }
            }
        }
        Guarded::Atom(ProtoAtom::Less(i, j)) => Ok(Guarded::Disj(
            vec![
                Guarded::Atom(ProtoAtom::EqE(i.clone(), j.clone())),
                Guarded::Atom(ProtoAtom::Less(j.clone(), i.clone())),
            ]
            .into(),
        )),
        Guarded::Atom(ProtoAtom::Last(_)) => Err("formula not last-free".to_string()),
        Guarded::Atom(a) => Ok(gnot_atom(a)),
        Guarded::Disj(xs) => {
            let xs2 = xs
                .iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gconj(xs2))
        }
        Guarded::Conj(xs) => {
            let xs2 = xs
                .iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gdisj(xs2))
        }
    }
}

/// `ginduct`: try to prove `g` by induction over the trace. Returns
/// `(base_case, step_case)` formulas.
///
/// - `base_case`: `gtrue`/`gfalse` depending on whether the empty
///   trace satisfies `g`.
/// - `step_case`: `g ∧ induction_hypothesis(g)`.
pub fn ginduct(g: &Guarded) -> Result<(Guarded, Guarded), String> {
    if !is_closed(g) {
        return Err("formula not closed".to_string());
    }
    if !contains_action(g) {
        return Err("formula contains no action atom".to_string());
    }
    let base = satisfied_by_empty_trace(g)?;
    let gf_ih = to_induction_hypothesis(g)?;
    let base_case = gtf(base);
    let step_case = gconj(vec![g.clone(), gf_ih]);
    Ok((base_case, step_case))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "guarded_tests.rs"]
mod tests;
