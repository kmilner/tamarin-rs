// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rkunnema, beschmi, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Substitution/SubstVFree.hs

//! Port of `Term.Substitution.SubstVFree` (the *generic* part — no LTerm
//! dependency yet) from `lib/term/src/Term/Substitution/SubstVFree.hs`.
//!
//! We model a substitution as a `BTreeMap<V, VTerm<C, V>>` and apply it via
//! [`apply_vterm`], which preserves AC normal form by routing through the
//! smart constructors in [`crate::term`].
//!
//! The Haskell `Apply` typeclass and the `LSubst`/`LNSubst` aliases live in
//! later modules that depend on `LTerm`.

use std::collections::BTreeMap;

use tamarin_utils::cow::cow_map_vec;

use crate::function_symbols::FunSym;
use crate::term::{f_app_ac, f_app_c, f_app_list, f_app_no_eq, lit, Term};
use crate::vterm::{Lit, VTerm};

/// A substitution mapping variables of type `V` to terms of type
/// `VTerm<C, V>`. The Haskell newtype is kept transparent here — callers
/// usually want to inspect or build the mapping.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    pub fn from_map(m: BTreeMap<V, VTerm<C, V>>) -> Self {
        let m = m.into_iter().filter(|(v, t)| !equal_to_var(t, v)).collect();
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

/// Whether `t` is just the literal variable `v`.
fn equal_to_var<C, V: PartialEq>(t: &VTerm<C, V>, v: &V) -> bool {
    matches!(t, Term::Lit(Lit::Var(w)) if w == v)
}

/// `applyLit`: substitute a single literal.
///
/// Intentionally retained: faithful HS port of `applyLit` (SubstVFree.hs); no
/// caller yet (the hot substitution path uses [`apply_vterm_map`]).
pub fn apply_lit<C: Ord + Clone, V: Ord + Clone>(s: &Subst<C, V>, l: &Lit<C, V>) -> VTerm<C, V> {
    match l {
        Lit::Var(v) => match s.map.get(v) {
            Some(t) => t.clone(),
            None => lit(Lit::Var(v.clone())),
        },
        Lit::Con(c) => lit(Lit::Con(c.clone())),
    }
}

/// `applyVTerm`: substitute through a whole term, re-AC-normalising.
pub fn apply_vterm<C: Ord + Clone, V: Ord + Clone>(s: &Subst<C, V>, t: VTerm<C, V>) -> VTerm<C, V> {
    apply_vterm_map(&s.map, t)
}

/// `applyVTerm` with change detection: returns `Some(new_term)` only when
/// `s` actually changes `t`, and `None` when `t` is left structurally
/// unchanged.  The borrowing, non-cloning counterpart of [`apply_vterm`] —
/// callers reuse the original `t` on `None` instead of cloning it and
/// deep-comparing against the applied result.  Thin single-term wrapper over
/// [`apply_vterm_map_changed`], sharing its exact `None`-when-unchanged
/// convention (empty/absent binding ⇒ `None`).
pub fn apply_vterm_changed<C: Ord + Clone, V: Ord + Clone>(
    s: &Subst<C, V>,
    t: &VTerm<C, V>,
) -> Option<VTerm<C, V>> {
    apply_vterm_map_changed(&s.map, t)
}

/// `applyVTerm` against a raw substitution map — the borrowing
/// counterpart of [`apply_vterm`], producing byte-identical output.
///
/// Two short-circuits mirror Haskell's `applyVTerm` (SubstVFree.hs) so we
/// only allocate on the part of the term the substitution actually touches:
///
/// 1. **Empty-map fast path:** an empty substitution is the identity, so we
///    return `t` untouched (it is already AC-normal).
/// 2. **Unchanged-subterm sharing:** [`apply_vterm_map_changed`] returns
///    `None` when the substitution leaves a subterm structurally unchanged;
///    in that case we reuse the original `Arc<[_]>` instead of rebuilding and
///    re-AC-sorting it.  This is sound because an unchanged term is already in
///    AC-normal form, and the resulting *value* is identical to the
///    full-rebuild path (only the `Arc` identity differs, which is invisible
///    to callers and to `--prove` output).
///
/// Without these, applying the (idempotent) eq-store substitution across the
/// whole constraint system on every solver step reallocated and re-sorted
/// every node even when nothing changed — the dominant allocator in the
/// alloc-bound theories (DH/classic/xor).
pub fn apply_vterm_map<C: Ord + Clone, V: Ord + Clone>(
    map: &BTreeMap<V, VTerm<C, V>>,
    t: VTerm<C, V>,
) -> VTerm<C, V> {
    if map.is_empty() {
        return t;
    }
    match apply_vterm_map_changed(map, &t) {
        Some(changed) => changed,
        None => t,
    }
}

/// Apply `map` to `t`, returning `Some(new_term)` only when the substitution
/// actually changes `t`, and `None` when `t` is left structurally unchanged.
///
/// Callers reuse the original term (sharing its `Arc`) on `None`.  An `App`
/// node is rebuilt — and re-AC-normalised through the smart constructors,
/// exactly as the non-sharing path did — only when at least one child changed.
fn apply_vterm_map_changed<C: Ord + Clone, V: Ord + Clone>(
    map: &BTreeMap<V, VTerm<C, V>>,
    t: &VTerm<C, V>,
) -> Option<VTerm<C, V>> {
    match t {
        Term::Lit(l) => apply_lit_map_changed(map, l),
        Term::App(fsym, args) => {
            // COW-rebuild the argument vector: the shared `cow_map_vec` helper
            // clones only the unchanged prefix on the first change and returns
            // `None` when every child is left structurally unchanged.
            cow_map_vec(&args[..], |a| apply_vterm_map_changed(map, a)).map(|mapped| match fsym {
                FunSym::Ac(o) => f_app_ac(*o, mapped),
                FunSym::C(o) => f_app_c(*o, mapped),
                FunSym::NoEq(o) => f_app_no_eq(*o, mapped),
                FunSym::List => f_app_list(mapped),
            })
        }
    }
}

/// `applyLit` against a raw map, returning `Some` only when the literal is a
/// domain variable (and thus replaced).  The borrowing counterpart of
/// [`apply_lit`] used by the sharing recursion above.
///
/// `from_map`/`from_list` drop trivial `x ~> x` entries and the unification
/// accumulator never inserts one, so a found binding is always a genuine
/// change — making `Some`/`None` here exactly track "did the term change".
fn apply_lit_map_changed<C: Ord + Clone, V: Ord + Clone>(
    map: &BTreeMap<V, VTerm<C, V>>,
    l: &Lit<C, V>,
) -> Option<VTerm<C, V>> {
    match l {
        Lit::Var(v) => map.get(v).cloned(),
        Lit::Con(_) => None,
    }
}

/// Pass-invariant hashed lookup view over a [`Subst`].
///
/// [`apply_vterm_map_changed`] pays a `BTreeMap` descent per `Lit::Var`
/// leaf — `LVar`-style keys compare idx-then-sort-then-name, so each probe
/// is ~log n pointer-chasing node hops of multi-field compares.
/// Whole-system passes (`subst_system_once`, `rename_precise_system`
/// Phase 2) apply ONE fixed substitution to every term of every
/// node/goal/edge/subterm-constraint, so they build this `FxHash` view once
/// per pass and pay a single hash probe per leaf instead.
///
/// Value-identity: the view borrows the same `(var, term)` entries as the
/// backing `BTreeMap` (`Hash`/`Eq` on `V` agree with the map's key
/// equality), and [`Self::apply_changed`] mirrors
/// [`apply_vterm_map_changed`]'s recursion and `None`-when-unchanged
/// convention exactly — only the leaf-probe container differs, which is
/// invisible to callers.  The view is consumed by keyed `get` only (never
/// iterated), so the hash order cannot reach output.
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

    /// [`apply_vterm_map`] against the view: same empty-map fast path, same
    /// reuse-original-on-unchanged behaviour, byte-identical output.
    pub fn apply(&self, t: VTerm<C, V>) -> VTerm<C, V> {
        if self.map.is_empty() {
            return t;
        }
        match self.apply_changed(&t) {
            Some(changed) => changed,
            None => t,
        }
    }

    /// [`apply_vterm_map_changed`] against the view: identical recursion,
    /// identical `Some`-iff-rebuilt convention; only the per-leaf probe
    /// container differs.
    pub fn apply_changed(&self, t: &VTerm<C, V>) -> Option<VTerm<C, V>> {
        match t {
            Term::Lit(Lit::Var(v)) => self.map.get(v).map(|img| (*img).clone()),
            Term::Lit(Lit::Con(_)) => None,
            Term::App(fsym, args) => {
                cow_map_vec(&args[..], |a| self.apply_changed(a)).map(|mapped| match fsym {
                    FunSym::Ac(o) => f_app_ac(*o, mapped),
                    FunSym::C(o) => f_app_c(*o, mapped),
                    FunSym::NoEq(o) => f_app_no_eq(*o, mapped),
                    FunSym::List => f_app_list(mapped),
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{pair_sym, AcSym};
    use crate::term::{f_app_ac, f_app_no_eq};
    use crate::vterm::{const_term, var_term};

    type C = u32;
    type V = &'static str;

    #[test]
    fn empty_substitution_is_identity() {
        let s: Subst<C, V> = Subst::empty();
        let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), const_term(1)]);
        assert_eq!(apply_vterm(&s, t.clone()), t);
    }

    #[test]
    fn from_list_drops_trivial() {
        let s: Subst<C, V> = Subst::from_list(vec![("x", var_term("x")), ("y", const_term(1))]);
        // `x ~> x` is dropped, only `y ~> 1` remains.
        assert_eq!(s.dom().copied().collect::<Vec<_>>(), vec!["y"]);
    }

    #[test]
    fn apply_replaces_variables() {
        let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(7))]);
        let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("y")]);
        let out = apply_vterm(&s, t);
        assert_eq!(
            out,
            f_app_no_eq(pair_sym(), vec![const_term(7), var_term("y")])
        );
    }

    #[test]
    fn apply_preserves_ac_normalization() {
        // mult(x, 3) with {x ~> 1} should become mult(1, 3) — sorted.
        let t: VTerm<C, V> = f_app_ac(AcSym::Mult, vec![var_term("x"), const_term(3)]);
        let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
        let out = apply_vterm(&s, t);
        // Substitution may reorder; arguments must be sorted.
        if let Term::App(_, ts) = out {
            assert_eq!(&*ts, &[const_term(1), const_term(3)][..]);
        } else {
            panic!("expected AC application");
        }
    }

    /// `SubstView` is a pure probe-container swap: `apply_changed`/`apply`
    /// must agree with the `BTreeMap` path on every term shape — hit,
    /// miss, nested rebuild, AC re-normalisation, and the
    /// `None`-when-unchanged convention.
    #[test]
    fn subst_view_matches_btree_apply() {
        let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(7)), ("y", var_term("z"))]);
        let view = SubstView::new(&s);
        let terms: Vec<VTerm<C, V>> = vec![
            var_term("x"),                                               // hit (leaf)
            var_term("w"),                                               // miss (leaf)
            const_term(3),                                               // constant
            f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("w")]), // partial rebuild
            f_app_no_eq(pair_sym(), vec![var_term("w"), const_term(1)]), // unchanged app
            f_app_ac(AcSym::Mult, vec![var_term("y"), const_term(0)]),   // AC re-sort
        ];
        for t in terms {
            assert_eq!(view.apply_changed(&t), apply_vterm_changed(&s, &t));
            assert_eq!(view.apply(t.clone()), apply_vterm(&s, t));
        }
        assert_eq!(view.image_of(&"x"), s.image_of(&"x"));
        assert_eq!(view.image_of(&"w"), s.image_of(&"w"));
    }

    #[test]
    fn compose_applies_right_then_left() {
        // `compose s1 s2` applied to t == s1(s2(t)) (Haskell convention:
        // s1 *after* s2).
        // s1 = {x ~> y}, s2 = {y ~> 1}.
        let s1: Subst<C, V> = Subst::from_list(vec![("x", var_term("y"))]);
        let s2: Subst<C, V> = Subst::from_list(vec![("y", const_term(1))]);
        let composed = s1.compose(&s2);
        let t: VTerm<C, V> = var_term("x");
        // composed(x) = s1(s2(x)) = s1(x) = y.
        assert_eq!(apply_vterm(&composed, t), var_term("y"));
        // And for y: s2(y) = 1, s1(1) = 1.
        let t: VTerm<C, V> = var_term("y");
        assert_eq!(apply_vterm(&composed, t), const_term(1));
    }

    #[test]
    fn restrict_filters_domain() {
        let s: Subst<C, V> = Subst::from_list(vec![
            ("x", const_term(1)),
            ("y", const_term(2)),
            ("z", const_term(3)),
        ]);
        let r = s.restrict(&["x", "z"]);
        let dom: Vec<&V> = r.dom().collect();
        assert_eq!(dom, vec![&"x", &"z"]);
    }

    // =============================================================================
    // Haskell-faithfulness invariants
    // =============================================================================
    //
    // These tests pin semantic choices that were easy to miss.  See
    // `unification::haskell_invariants` for the rationale section.

    /// `restrict` is a PURE KEY-FILTER (no chain-chase).
    ///
    /// Haskell `Theory.Tools.EquationStore.restrict` calls
    /// `Subst.restrict` (SubstVFree.hs:160-161):
    /// ```haskell
    /// restrict :: IsVar v => [v] -> Subst c v -> Subst c v
    /// restrict vs (Subst smap) = Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)
    /// ```
    /// Nothing else.  No chain-chase.
    ///
    /// Do NOT chain-chase values to a fixed point before filtering:
    /// collapsing `t.1 → e_A_1 → blind(...)` into `t.1 → blind(...)`
    /// directly prevents Haskell-faithful `restrict` from dropping the
    /// binding (since `t.1` is stable), causing foo_eligibility's `A_1`
    /// case to be dropped at runtime via refineSubst-contradictory.
    #[test]
    fn restrict_does_not_chain_chase() {
        // Build a subst with a chain: y → z, z → 1.
        // If restrict ⊇ {y}: should keep `y → z` LITERALLY, not collapse
        // to `y → 1`.  The dangling z is fine — Haskell falls back to
        // identity for unbound vars.
        let s: Subst<C, V> = Subst::from_list(vec![("y", var_term("z")), ("z", const_term(1))]);
        let r = s.restrict(&["y"]);
        // y must map to z (the var), NOT to 1 (the chain-chased value).
        assert_eq!(
            r.image_of(&"y"),
            Some(&var_term("z")),
            "restrict must NOT chain-chase: y → z stays as y → z, \
                    not y → 1.  Chain-chase here breaks foo_eligibility \
                    (see project_rust_foo_eligibility_saturate_overspec.md)."
        );
        // z is filtered out entirely.
        assert_eq!(r.image_of(&"z"), None);
    }

    /// `restrict stableVars` empties the subst when no key is stable.
    ///
    /// This is the exact foo_eligibility shape: Haskell's pre-restrict
    /// subst has keys like `m.19` and `sk.28` (rule-internal vars,
    /// large idx), and stableVars are `{#i, t.1, t.2}` (lemma vars,
    /// small idx).  Post-restrict: empty subst.
    #[test]
    fn restrict_empties_subst_when_no_key_is_stable() {
        // "Rule-internal" keys binding to whatever values.
        let s: Subst<C, V> = Subst::from_list(vec![
            ("m", const_term(19)),  // m.19 in spirit
            ("sk", const_term(28)), // sk.28 in spirit
        ]);
        // "Stable" vars: don't overlap.
        let r = s.restrict(&["t", "i"]);
        assert!(
            r.is_empty(),
            "When no key is in stable set, restrict produces empty subst. \
                 This is what enables foo_eligibility's clean runtime bind."
        );
    }

    /// `compose s1 s2` applies right-then-left.
    ///
    /// Haskell `SubstVFree.compose` (mirrors Robinson):
    /// applying `s1 ∘ s2` to a term is `s1 (s2 t)`.
    ///
    /// If we get this backwards, downstream code that composes the
    /// freshly-built subst with the running eq-store gets the wrong
    /// effective substitution (and the proof state silently drifts).
    #[test]
    fn compose_direction_is_right_then_left() {
        // s1 = {x → 1}; s2 = {y → x}.
        // compose(s1, s2) means "apply s2 first, then s1".
        // (s1 . s2)(y) = s1(s2(y)) = s1(x) = 1.
        let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
        let s2: Subst<C, V> = Subst::from_list(vec![("y", var_term("x"))]);
        let composed = s1.compose(&s2);
        assert_eq!(
            apply_vterm(&composed, var_term("y")),
            const_term(1),
            "compose(s1, s2) applied to y must equal s1(s2(y)) = 1, \
                    NOT s2(s1(y)) = y.  If this fails, the direction is \
                    reversed and eq-store subst composition is silently \
                    wrong."
        );
    }

    /// `compose` preserves `s1`'s domain when `s2` doesn't bind it.
    ///
    /// `compose(s1, s2)` should include bindings from s1 that aren't
    /// shadowed by s2.  Specifically: s1 = {x → 1}, s2 = {y → 2};
    /// composed should have BOTH x → 1 and y → 2.
    #[test]
    fn compose_merges_disjoint_domains() {
        let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
        let s2: Subst<C, V> = Subst::from_list(vec![("y", const_term(2))]);
        let composed = s1.compose(&s2);
        assert_eq!(composed.image_of(&"x"), Some(&const_term(1)));
        assert_eq!(composed.image_of(&"y"), Some(&const_term(2)));
    }

    /// `compose` `s1` shadows `s2` for overlapping domain.
    ///
    /// If both bind `x`, the s1 binding wins in the final compose
    /// because compose iterates s2's bindings first (applying s1 into
    /// their values), then adds s1's own bindings that s2 doesn't
    /// already bind.  But our Rust impl `compose` adds *s1*'s own
    /// binding for x ONLY IF s2 doesn't have x.  Let's check what we
    /// actually do, then PIN it.
    #[test]
    fn compose_overlapping_domain_s2_takes_precedence_via_apply_subst() {
        // s1 = {x → 1}; s2 = {x → 99}.
        // compose first applies s1 to s2's range (no x in range, so
        // s2 unchanged); then adds s1's bindings whose domain isn't in
        // s2.  s2 has x, so s1's x → 1 is DROPPED.  Result: {x → 99}.
        //
        // This matches Haskell's `compose s1 s2` semantics: when s2
        // already binds v, s1's v-binding is shadowed by s2's.  Applying
        // composed to v gives s2(v) = 99.
        let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
        let s2: Subst<C, V> = Subst::from_list(vec![("x", const_term(99))]);
        let composed = s1.compose(&s2);
        assert_eq!(
            composed.image_of(&"x"),
            Some(&const_term(99)),
            "compose: s2's binding wins when domains overlap and \
                    s1 doesn't transform s2's value."
        );
        assert_eq!(apply_vterm(&composed, var_term("x")), const_term(99));
    }

    /// `apply_subst` rewrites the RANGE of `other` only.
    ///
    /// `s1.apply_subst(s2)` rewrites every VALUE in s2 by applying s1.
    /// It does NOT touch s2's keys (which would change the domain).
    /// This is a building block of `compose`; getting it wrong
    /// silently corrupts every composition.
    #[test]
    fn apply_subst_rewrites_range_only_not_keys() {
        // s1 = {x → 1}; s2 = {y → x}.
        // s1.apply_subst(s2) = {y → 1}.  Key y unchanged, range x → 1.
        let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
        let s2: Subst<C, V> = Subst::from_list(vec![("y", var_term("x"))]);
        let result = s1.apply_subst(&s2);
        assert_eq!(
            result.image_of(&"y"),
            Some(&const_term(1)),
            "apply_subst rewrites s2's range"
        );
        assert_eq!(
            result.image_of(&"x"),
            None,
            "apply_subst must NOT add new keys"
        );
    }
}
