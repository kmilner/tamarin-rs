// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Substitution.SubstVFree` from
//! `lib/term/src/Term/Substitution/SubstVFree.hs`.
//!
//! We model a substitution as a `BTreeMap<V, VTerm<C, V>>` and apply it via
//! [`apply_vterm`], which preserves AC normal form by routing through the
//! smart constructors in [`crate::term`].  The locally-nameless counterparts
//! [`apply_bvterm`] and [`apply_bvar`] apply one to a term whose variables
//! are [`BVar`]s.
//!
//! The Haskell `Apply` typeclass is [`crate::apply`]; the `LSubst`/`LNSubst`
//! aliases live in later modules that depend on `LTerm`.

use std::collections::BTreeMap;

use crate::apply::Apply;
use crate::lterm::{BVar, HasFrees, LVar};
use crate::term::{bind_lits, map_lits, Term};
use crate::vterm::{Lit, VTerm};

/// A substitution mapping variables of type `V` to terms of type
/// `VTerm<C, V>`. The Haskell newtype is kept transparent here — callers
/// usually want to inspect or build the mapping.
///
/// HS `newtype Subst c v = Subst { sMap :: Map v (VTerm c v) }` derives
/// `Eq`/`Ord` over the one map field (SubstVFree.hs:85-86); `BTreeMap`'s `Ord`
/// compares ascending entries, as `Data.Map`'s does.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Subst<C, V> {
    map: BTreeMap<V, VTerm<C, V>>,
}

impl<C, V> Default for Subst<C, V> {
    fn default() -> Self {
        Subst {
            map: BTreeMap::new(),
        }
    }
}

impl<C, V> Subst<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    pub fn empty() -> Self {
        Subst::default()
    }

    /// `substFromList`: drop trivial `x ~> x` mappings, then build.
    pub fn from_list(pairs: impl IntoIterator<Item = (V, VTerm<C, V>)>) -> Self {
        let mut m = BTreeMap::new();
        for (v, t) in pairs {
            if !equal_to_var(&t, &v) {
                m.insert(v, t);
            }
        }
        Subst { map: m }
    }

    /// `substFromMap`: drop trivial `x ~> x` mappings.
    pub fn from_map(mut m: BTreeMap<V, VTerm<C, V>>) -> Self {
        m.retain(|v, t| !equal_to_var(t, v));
        Subst { map: m }
    }

    /// Take the underlying mapping out of the (invariant-checked) `Subst`.
    /// Crate-internal: lets pure re-tagging conversions (`free_to_fresh_raw`
    /// and the `compose_vfresh` no-range-var collapse) move/clone the map
    /// wholesale instead of round-tripping through `to_list`/`from_list`.
    pub(crate) fn into_map(self) -> BTreeMap<V, VTerm<C, V>> {
        self.map
    }

    pub fn dom(&self) -> impl Iterator<Item = &V> {
        self.map.keys()
    }
    pub fn range(&self) -> impl Iterator<Item = &VTerm<C, V>> {
        self.map.values()
    }
    /// Borrowing iterator over the `(var, term)` mappings in domain (key)
    /// order.  The non-cloning counterpart of [`to_list`]: callers that only
    /// need to read `v.idx` / walk the term avoid cloning every entry.
    pub fn iter(&self) -> impl Iterator<Item = (&V, &VTerm<C, V>)> {
        self.map.iter()
    }
    pub fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> {
        self.map.get(v)
    }
    pub fn to_list(&self) -> Vec<(V, VTerm<C, V>)> {
        self.map
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// `restrict vars`: keep only mappings whose key is in `vars`.
    pub fn restrict(&self, vars: &[V]) -> Self
    where
        V: PartialEq,
    {
        let map = self
            .map
            .iter()
            .filter(|(v, _)| vars.contains(v))
            .map(|(v, t)| (v.clone(), t.clone()))
            .collect();
        Subst { map }
    }

    /// `mapRange f`: rewrite every range element with `f`, dropping any
    /// resulting trivial `x ~> x` entries.
    pub fn map_range<F: FnMut(VTerm<C, V>) -> VTerm<C, V>>(&self, mut f: F) -> Self {
        let map = self
            .map
            .iter()
            .filter_map(|(v, t)| {
                let t2 = f(t.clone());
                if equal_to_var(&t2, v) {
                    None
                } else {
                    Some((v.clone(), t2))
                }
            })
            .collect();
        Subst { map }
    }

    /// `applySubst self other` = apply `self` to the range of `other`.
    pub fn apply_subst(&self, other: &Self) -> Self {
        other.map_range(|t| apply_vterm(self, t))
    }

    /// `compose s1 s2` = `s1 . s2`. Effect: applying the result is the same
    /// as applying `s2` then `s1`.
    pub fn compose(&self, other: &Self) -> Self {
        let mut composed = self.apply_subst(other).map;
        // Add bindings from `self` whose domain is not already in `other`.
        for (v, t) in &self.map {
            if !other.map.contains_key(v) {
                composed.insert(v.clone(), t.clone());
            }
        }
        Subst { map: composed }
    }
}

/// `instance Ord c => HasFrees (LSubst c)` (SubstVFree.hs:259-264).
///
/// The walk is the `M.Map` instance (LTerm.hs:905-909): each entry's key
/// before its value, in ascending key order.  The map rebuilds every entry as
/// a pair — key then value (LTerm.hs:855-860) — and goes back through
/// `substFromList`, which drops any binding the map turned into `x ~> x`.
impl<C: Ord + Clone> HasFrees for Subst<C, LVar> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for (v, t) in self.map.iter() {
            v.for_each_free(f);
            t.for_each_free(f);
        }
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        let mut pairs = Vec::with_capacity(self.map.len());
        for (v, t) in self.map {
            let v = v.map_free_with(f, monotone);
            let t = t.map_free_with(f, monotone);
            pairs.push((v, t));
        }
        Subst::from_list(pairs)
    }
}

/// Whether `t` is just the literal variable `v`.
fn equal_to_var<C, V: PartialEq>(t: &VTerm<C, V>, v: &V) -> bool {
    matches!(t, Term::Lit(Lit::Var(w)) if w == v)
}

/// `applyVTerm`: substitute through a whole term, re-AC-normalising.
pub fn apply_vterm<C: Ord + Clone, V: Ord + Clone>(s: &Subst<C, V>, t: VTerm<C, V>) -> VTerm<C, V> {
    t.apply(s)
}

/// `applyVTerm` with change detection: `Some(new_term)` only when `s` actually
/// changes `t`, and `None` when `t` is left structurally unchanged.  The
/// borrowing, non-cloning counterpart of [`apply_vterm`] — callers reuse the
/// original `t` on `None` instead of cloning it and deep-comparing against the
/// applied result.
pub fn apply_vterm_changed<C: Ord + Clone, V: Ord + Clone>(
    s: &Subst<C, V>,
    t: &VTerm<C, V>,
) -> Option<VTerm<C, V>> {
    t.apply_changed(s)
}

/// `applyVTerm` against a raw substitution map — the entry point the
/// unification accumulator and the variant-subst walks use, where the mapping
/// exists only as a `BTreeMap`.
pub fn apply_vterm_map<C: Ord + Clone, V: Ord + Clone>(
    map: &BTreeMap<V, VTerm<C, V>>,
    t: VTerm<C, V>,
) -> VTerm<C, V> {
    t.apply(map)
}

/// HS's overlappable `Apply s (BVar v)` (SubstVFree.hs:293-295): a bound De
/// Bruijn index is left alone, and a free variable is rewritten by the
/// `Apply s v` instance the caller passes in — `Apply (Subst c v) v`
/// (SubstVFree.hs:279-285) for a plain variable, `Apply (Subst Name LVar)
/// SapicLVar` (Theory/Sapic/Term.hs:115-117) for a variable that carries a
/// type tag the rewrite preserves.
pub fn apply_bvar<V>(v: &BVar<V>, apply_free: &mut dyn FnMut(&V) -> V) -> BVar<V> {
    match v {
        BVar::Bound(i) => BVar::Bound(*i),
        BVar::Free(v) => BVar::Free(apply_free(v)),
    }
}

/// HS's overlapping `Apply (Subst c v) (VTerm c (BVar v))`
/// (SubstVFree.hs:297-302): replace every free literal in the substitution's
/// domain by its image, lifted back into `BVar` form with `fmapTerm (fmap
/// Free)`.  A bound index is not in the domain, so a binder cannot capture an
/// image variable.  The rebuild goes through [`crate::term::f_app`], as HS's `bindTerm`
/// (Term/Term/Raw.hs:219-221) does, so AC argument lists are flattened and
/// re-sorted under the images.
pub fn apply_bvterm<C: Ord + Clone, V: Ord + Clone>(
    s: &Subst<C, V>,
    t: &VTerm<C, BVar<V>>,
) -> VTerm<C, BVar<V>> {
    bind_lits(t, &mut |literal| match literal {
        Lit::Var(BVar::Free(v)) => match s.image_of(v) {
            Some(image) => map_lits(image, &mut |l| match l {
                Lit::Con(c) => Lit::Con(c.clone()),
                Lit::Var(w) => Lit::Var(BVar::Free(w.clone())),
            }),
            None => Term::Lit(literal.clone()),
        },
        _ => Term::Lit(literal.clone()),
    })
}

/// Pass-invariant hashed lookup view over a [`Subst`].
///
/// [`apply_vterm_map`] pays a `BTreeMap` descent per `Lit::Var`
/// leaf — `LVar`-style keys compare idx-then-sort-then-name, so each probe
/// is ~log n pointer-chasing node hops of multi-field compares.
/// Whole-system passes (`subst_system_once`, `rename_precise_system`
/// Phase 2) apply ONE fixed substitution to every term of every
/// node/goal/edge/subterm-constraint, so they build this `FxHash` view once
/// per pass and pay a single hash probe per leaf instead.
///
/// Value-identity: the view borrows the same `(var, term)` entries as the
/// backing `BTreeMap` (`Hash`/`Eq` on `V` agree with the map's key
/// equality), and [`Self::apply_changed`] runs the same [`Apply`] instance
/// as [`apply_vterm_map`] does, down to the `None`-when-unchanged
/// convention — only the leaf-probe container differs, which is invisible
/// to callers.  The view is consumed by keyed `get` only (never iterated),
/// so the hash order cannot reach output.
///
/// Memory: a pass-local of `subst.len()` borrowed pointer pairs, dropped
/// with the pass — no persistence, no growth across steps.
pub struct SubstView<'a, C, V> {
    map: tamarin_utils::FastMap<&'a V, &'a VTerm<C, V>>,
}

impl<'a, C, V> SubstView<'a, C, V>
where
    C: Ord + Clone,
    V: Ord + Clone + std::hash::Hash,
{
    /// Build the view for one whole-system pass over `s`.
    pub fn new(s: &'a Subst<C, V>) -> Self {
        let mut map =
            tamarin_utils::FastMap::with_capacity_and_hasher(s.map.len(), Default::default());
        for (k, t) in s.map.iter() {
            map.insert(k, t);
        }
        SubstView { map }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Keyed image probe — the hashed counterpart of [`Subst::image_of`].
    pub fn image_of(&self, v: &V) -> Option<&'a VTerm<C, V>> {
        self.map.get(v).copied()
    }

    /// [`apply_vterm`] against the view: same empty-map fast path, same
    /// reuse-original-on-unchanged behaviour, byte-identical output.
    pub fn apply(&self, t: VTerm<C, V>) -> VTerm<C, V> {
        t.apply(self)
    }

    /// [`apply_vterm_changed`] against the view: same `Some`-iff-rebuilt
    /// convention; only the per-leaf probe container differs.
    pub fn apply_changed(&self, t: &VTerm<C, V>) -> Option<VTerm<C, V>> {
        t.apply_changed(self)
    }
}

#[cfg(test)]
#[path = "subst_tests.rs"]
mod tests;
