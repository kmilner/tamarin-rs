// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Substitution.SubstVFresh` from
//! `lib/term/src/Term/Substitution/SubstVFresh.hs`.
//!
//! Substitutions whose range variables are considered fresh — such
//! substitutions cannot be applied directly; the caller must first convert
//! them to a regular `Subst` by re-naming away from existing free vars.

use std::collections::BTreeMap;

use tamarin_utils::fresh::FastFreshState;

use crate::bind::Bindings;
use crate::lterm::{HasFrees, LVar, Name};
use crate::term::{Term, TermSize};
use crate::vterm::{Lit, VTerm};

// `PartialOrd` / `Ord` derived to mirror Haskell's `deriving (Ord, ..)` on
// `SubstVFresh c v` (SubstVFresh.hs).  Haskell's `S.toList` in `performSplit`
// returns substitutions in sorted order; we need the same canonical
// ordering so split-case enumeration matches Haskell (e.g. KAS2_eCK
// Resp_1 variant `c1 = aenc(x, pk(~lkR))` comes before the trivial
// one, giving `split_case_1` = the meaningful variant).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubstVFresh<C, V> {
    map: BTreeMap<V, VTerm<C, V>>,
}

impl<C, V> Default for SubstVFresh<C, V> {
    fn default() -> Self {
        SubstVFresh {
            map: BTreeMap::new(),
        }
    }
}

pub type LSubstVFresh<C> = SubstVFresh<C, LVar>;
pub type LNSubstVFresh = SubstVFresh<Name, LVar>;

impl<C, V> SubstVFresh<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    pub fn empty() -> Self {
        SubstVFresh::default()
    }

    /// `substFromListVFresh`: build directly from a mapping list (no
    /// trivial-mapping filtering, unlike free-variable `Subst`).
    pub fn from_list(pairs: impl IntoIterator<Item = (V, VTerm<C, V>)>) -> Self {
        SubstVFresh {
            map: pairs.into_iter().collect(),
        }
    }

    /// `restrictVFresh`: drop entries whose key is not in `vars`.
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
        SubstVFresh { map }
    }

    pub fn dom(&self) -> impl Iterator<Item = &V> {
        self.map.keys()
    }
    pub fn range(&self) -> impl Iterator<Item = &VTerm<C, V>> {
        self.map.values()
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
    /// Borrowing view over the (key, image) pairs in domain order, avoiding
    /// the per-entry clones of `to_list` when callers only need to read.
    pub fn iter(&self) -> impl Iterator<Item = (&V, &VTerm<C, V>)> {
        self.map.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
}

/// `instance HasFrees (SubstVFresh n LVar)` (SubstVFresh.hs).
///
/// The range variables of a `SubstVFresh` count as fresh, so both methods see
/// the DOMAIN keys only: the walk is `foldFrees f . M.keys . svMap`, and the
/// map rewrites each key and carries its image over untouched, rebuilding
/// through `substFromListVFresh` (which keeps every entry, including one the
/// map turned into `x ~> x`).
impl<C: Ord + Clone> HasFrees for SubstVFresh<C, LVar> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for v in self.map.keys() {
            v.for_each_free(f);
        }
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        let mut pairs = Vec::with_capacity(self.map.len());
        for (v, t) in self.map {
            pairs.push((v.map_free_with(f, monotone), t));
        }
        SubstVFresh::from_list(pairs)
    }
}

impl<C: Ord + Clone> LSubstVFresh<C> {
    /// `dropNameHintsLNSubstVFresh` (EquationStore.hs): the canonical
    /// form used as the split-case sort key. Renames every RANGE variable to a
    /// fresh variable with an EMPTY name hint, sort preserved, indices assigned
    /// 0,1,2,… in order of first appearance across the range terms (visited in
    /// domain-key order) — mirrors HS `renameDropNamehint` applied to
    /// `map snd (substToListVFresh s)`. Domain keys are kept unchanged. Two
    /// substitutions that are α-equivalent in their range map to the same
    /// canonical form, so a stable `sort_by_cached_key(drop_name_hints)`
    /// (= HS `sortOnMemo dropNameHintsLNSubstVFresh`) orders the split cases
    /// structurally, independent of the fresh-allocation counter.
    pub fn drop_name_hints(&self) -> Self {
        let mut bindings = Bindings::new();
        let mut fresh = FastFreshState::nothing_used();
        let renamed: Vec<(LVar, VTerm<C, LVar>)> = self
            .map
            .iter()
            .map(|(k, t)| {
                let t = t
                    .clone()
                    .map_free(&mut |v| bindings.import_drop_namehint(&v, &mut fresh));
                (*k, t)
            })
            .collect();
        Self::from_list(renamed)
    }

    /// `varsRangeVFresh`: every variable that appears in any range term.
    pub fn vars_range(&self) -> Vec<LVar> {
        // Collect vars from every range term by reference (no clone of the
        // terms, no intermediate `f_app_list` bundle), then sort+dedup to
        // mirror `vars_vterm`'s set semantics.
        let mut out: Vec<LVar> = Vec::new();
        for t in self.range() {
            out.extend(crate::vterm::vars_vterm_in_order(t));
        }
        out.sort();
        out.dedup();
        out
    }

    /// `isRenamedVar`: the binding for `v` is just a sort-preserving
    /// rename, and the target variable doesn't appear elsewhere.
    pub fn is_renamed_var(&self, v: &LVar) -> bool {
        let Some(t) = self.image_of(v) else {
            return false;
        };
        let Term::Lit(Lit::Var(target)) = t else {
            return false;
        };
        if target.sort != v.sort {
            return false;
        }
        // target must not appear in any other range entry.  Borrow each
        // range term and scan in place (short-circuiting), avoiding the
        // per-key clone of every other range term + `f_app_list` bundle.
        self.map
            .iter()
            .filter(|(w, _)| *w != v)
            .all(|(_, t)| !crate::vterm::occurs_vterm(target, t))
    }

    /// `isRenaming`: every entry is a rename.
    ///
    /// Equivalent to `self.map.keys().all(|v| self.is_renamed_var(v))` but
    /// computed in a single pass (the naive form is O(n^2): each
    /// `is_renamed_var` re-scans every other range entry).  A substitution is
    /// a renaming iff every binding maps to a sort-preserving variable and no
    /// two distinct keys map to the same target variable (i.e. no target var
    /// occurs in any other entry).
    pub fn is_renaming(&self) -> bool {
        let mut targets: std::collections::BTreeSet<&LVar> = std::collections::BTreeSet::new();
        for (v, t) in self.map.iter() {
            let Term::Lit(Lit::Var(target)) = t else {
                return false;
            };
            if target.sort != v.sort {
                return false;
            }
            // A duplicate target means this target var also appears in another
            // entry, so that entry's `is_renamed_var` would have failed.
            if !targets.insert(target) {
                return false;
            }
        }
        true
    }

    /// `removeRenamings`: drop every entry that's just a rename.
    pub fn remove_renamings(&self) -> Self {
        let map = self
            .map
            .iter()
            .filter(|(v, _)| !self.is_renamed_var(v))
            .map(|(v, t)| (*v, t.clone()))
            .collect();
        SubstVFresh { map }
    }

    /// `extendWithRenaming vs s`: extends `s` with renamings (with fresh
    /// variables) for the variables in `vs` that are not already in
    /// `dom s`.  Mirrors HS `Term.Substitution.SubstVFresh.extendWithRenaming`
    /// (SubstVFresh.hs).
    ///
    /// The new renamings use uniformly-shifted fresh idxs starting above
    /// `varsRangeVFresh self` (HS: `renameFreshAvoiding s2 (varsRangeVFresh s)`).
    /// The shift = freshStart - min(idx of vs_new); applied to each var in
    /// vs_new uniformly, preserving relative ordering — mirrors HS's
    /// `rename` semantics (LTerm.hs).
    pub fn extend_with_renaming(&self, vs: &[LVar]) -> Self {
        // Domain probes go straight to the map (`image_of` = `BTreeMap::get`)
        // and the first-appearance dedup uses a hash `seen` set: both are
        // membership-only, so neither needs the ordered `BTreeSet` builds the
        // eager version materialised per call.  `vs_new` carries the order.
        let mut vs_new: Vec<LVar> = Vec::new();
        let mut seen: tamarin_utils::FastSet<LVar> = Default::default();
        for v in vs {
            if self.image_of(v).is_some() {
                continue;
            }
            if seen.insert(*v) {
                vs_new.push(*v);
            }
        }
        if vs_new.is_empty() {
            return self.clone();
        }
        // Fresh state: `evalFreshAvoiding (varsRangeVFresh s)` =
        //   succ . maxIdx . vars (or 0 if empty).  Only the max idx is
        //   consumed, so fold it over the range terms directly instead of
        //   materialising the sorted/deduped `vars_range` list (dedup and
        //   order are irrelevant to a max).
        let mut avoid_max: Option<u64> = None;
        for t in self.range() {
            use crate::lterm::HasFrees;
            t.for_each_free(&mut |v: &LVar| {
                avoid_max = Some(avoid_max.map_or(v.idx, |m| m.max(v.idx)));
            });
        }
        let fresh_start: u64 = avoid_max.map(|m| m + 1).unwrap_or(0);
        // HS's `rename`: minVar, maxVar; freshStart from monad; shift =
        // freshStart - minVar; new idx = old idx + shift (signed).
        let vs_min: u64 = vs_new.iter().map(|v| v.idx).min().unwrap();
        // Signed math because shift may go negative when fresh_start < vs_min
        // (e.g., self is empty so fresh_start=0 but vs_min > 0).  This is
        // a faithful translation of HS's Integer math.
        let shift: i128 = fresh_start as i128 - vs_min as i128;
        let new_entries: Vec<(LVar, VTerm<C, LVar>)> = vs_new
            .iter()
            .map(|v| {
                let new_idx = shifted_idx(v.idx, shift);
                let v_new = LVar {
                    name: v.name,
                    sort: v.sort,
                    idx: new_idx,
                };
                (*v, Term::Lit(Lit::Var(v_new)))
            })
            .collect();
        // `from_list(to_list() ++ new_entries)` would rebuild the whole map from
        // a Vec; the keys are disjoint (`vs_new` excludes `dom self`), so
        // cloning the map and inserting the new entries yields the identical
        // BTreeMap without the intermediate Vec + re-sort.
        let mut map = self.map.clone();
        for (v, t) in new_entries {
            map.insert(v, t);
        }
        SubstVFresh { map }
    }

    /// HS `freshToFreeAvoidingFast` (Term/Substitution.hs): shift every
    /// range variable uniformly so the smallest lands on `fresh_start`
    /// (`succ . maxIdx` of the avoided set), keeping their relative order.
    pub fn fresh_to_free_uniform_shift(&self, fresh_start: u64) -> crate::subst::Subst<C, LVar> {
        use crate::subst::Subst;
        // Collect ALL distinct range vars in insertion order.
        let range_vars: Vec<LVar> = distinct_range_vars(self.range());
        if range_vars.is_empty() {
            // No range vars to rename — just downgrade (through `from_list`,
            // which drops trivial `x ~> x` mappings exactly as before).
            return Subst::from_list(self.iter().map(|(v, t)| (*v, t.clone())));
        }
        // HS: `evalFreshAvoiding t` initial counter = succ . maxIdx . frees t,
        // precomputed by the caller and handed in as `fresh_start`.
        let min_idx = range_vars.iter().map(|v| v.idx).min().unwrap();
        let shift: i128 = fresh_start as i128 - min_idx as i128;
        // Lookup-only rename table: keyed by LVar (interned name, sort, idx),
        // probed once per var occurrence in the range walk below — a hash map
        // beats per-occurrence BTree descents and is never iterated.
        let mut rename: tamarin_utils::FastMap<LVar, LVar> = Default::default();
        for old in &range_vars {
            let new_idx = shifted_idx(old.idx, shift);
            let new = LVar {
                name: old.name,
                sort: old.sort,
                idx: new_idx,
            };
            rename.insert(*old, new);
        }
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::with_capacity(self.len());
        // Borrow the entries in place; `map_free_monotone` takes only a shallow
        // clone and reuses any unchanged subtree.
        for (v, t) in self.iter() {
            let renamed = t
                .clone()
                .map_free_monotone(&mut |v| rename.get(&v).copied().unwrap_or(v));
            pairs.push((*v, renamed));
        }
        Subst::from_list(pairs)
    }

    /// HS `freshToFree` (Term/Substitution.hs), drawing indices from
    /// `alloc_idxs`; the same algorithm as [`Self::fresh_to_free_avoiding`].
    pub fn fresh_to_free<F: FnMut(u64) -> u64>(
        &self,
        alloc_idxs: F,
    ) -> crate::subst::Subst<C, LVar> {
        // Every range var is treated as a witness and gets renamed.
        self.fresh_to_free_avoiding(alloc_idxs)
    }

    /// HS `freshToFreeAvoiding s t = freshToFree s `evalFreshAvoiding` t`
    /// (Term/Substitution.hs): rename every range variable, in order of
    /// image size, with `alloc_idxs` seeded above `t`.
    pub fn fresh_to_free_avoiding<F: FnMut(u64) -> u64>(
        &self,
        mut alloc_idxs: F,
    ) -> crate::subst::Subst<C, LVar> {
        use crate::subst::Subst;
        // HS (Term/Substitution.hs):
        //
        //   freshToFree subst = (`evalBindT` noBindings) $ do
        //       let slist = sortOn (size . snd) $ substToListVFresh subst
        //       substFromList <$> mapM convertMapping slist
        //     where
        //       convertMapping (lv,t) = (lv,) <$> mapFrees (Arbitrary importVar) t
        //         where
        //           importVar v = importBinding (\s i -> LVar s (lvarSort v) i) v (namehint v)
        //           namehint v  = case viewTerm t of
        //               Lit (Var _) -> lvarName lv -- keep name of oldvar
        //               _           -> lvarName v
        //
        // Every range variable is renamed; one binding per range variable.
        let mut slist: Vec<(LVar, VTerm<C, LVar>)> = self.to_list();
        slist.sort_by_key(|(_, t)| t.size());
        let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::with_capacity(slist.len());
        for (lv, t) in slist.into_iter() {
            let outer_is_singleton_var = matches!(&t, Term::Lit(Lit::Var(_)));
            let renamed = t.map_free(&mut |v| {
                *rename.entry(v).or_insert_with(|| LVar {
                    name: if outer_is_singleton_var {
                        lv.name
                    } else {
                        v.name
                    },
                    sort: v.sort,
                    idx: alloc_idxs(1),
                })
            });
            pairs.push((lv, renamed));
        }
        Subst::from_list(pairs)
    }
}

/// Apply HS's `rename` shift to a single var index: `old + shift` in
/// signed (HS Integer) math, saturating-clamped back into `u64`.  Shared
/// by `extend_with_renaming` and `fresh_to_free_uniform_shift` so the
/// load-bearing clamp can't drift between the two call sites.
fn shifted_idx(idx: u64, shift: i128) -> u64 {
    let new_idx_signed: i128 = idx as i128 + shift;
    if new_idx_signed < 0 {
        0
    } else if new_idx_signed > u64::MAX as i128 {
        u64::MAX
    } else {
        new_idx_signed as u64
    }
}

/// `freeToFreshRaw`: re-tag a free `Subst`'s entries as a `SubstVFresh`.
/// Mirrors HS `Term.Substitution.freeToFreshRaw` (Term/Substitution.hs):
/// considers all variables in the range as fresh.  No structural change —
/// just a type-level reinterpretation, so the owned map moves across
/// wholesale (`SubstVFresh::from_list` does no trivial-drop; a
/// `from_list(to_list)` round-trip would rebuild the identical map from clones).
pub fn free_to_fresh_raw<C: Ord + Clone>(s: crate::subst::Subst<C, LVar>) -> LSubstVFresh<C> {
    LSubstVFresh { map: s.into_map() }
}

/// Collect all distinct range vars in first-appearance order.
///
/// Walks the given range terms (each expanded via `vars_vterm`, whose per-term
/// order is preserved) and keeps only the first occurrence of each var, guarded
/// by a `seen` set.  Shared by `fresh_to_free_uniform_shift` and
/// `compose_vfresh`, which differ only in which subst's range is walked.
/// The `seen` set is membership-only (`out` carries the byte-visible order),
/// so a hash set replaces the per-occurrence BTree insert.
fn distinct_range_vars<'a, C: 'a>(range: impl Iterator<Item = &'a VTerm<C, LVar>>) -> Vec<LVar> {
    let mut out: Vec<LVar> = Vec::new();
    let mut seen: tamarin_utils::FastSet<LVar> = Default::default();
    for t in range {
        for v in crate::vterm::vars_vterm(t) {
            if seen.insert(v) {
                out.push(v);
            }
        }
    }
    out
}

/// `composeVFresh s1 s2`: composes the fresh substitution `s1` with the
/// free substitution `s2`.  Mirrors HS `Term.Substitution.composeVFresh`
/// (Term/Substitution.hs):
///
/// ```haskell
/// composeVFresh s1_0 s2 =
///     freeToFreshRaw (s1 `compose` s2)
///   where
///     s1 = freshToFreeAvoidingFast
///             (extendWithRenaming (varsRange s2) s1_0)
///             (s2, s1_0)
/// ```
///
pub fn compose_vfresh<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> LSubstVFresh<C>
where
    C: Ord + Clone,
{
    // varsRange s2: vars in s2's range
    let vs_in_range_s2: Vec<LVar> = distinct_range_vars(s2.range());
    let extended = s1_0.extend_with_renaming(&vs_in_range_s2);
    // `frees (s2, s1_0)`: `frees s2` walks s2's domain and range, but
    // `frees` of a `SubstVFresh` reads its domain keys only
    // (SubstVFresh.hs).  Only the maximum index is needed.
    let mut max_idx: Option<u64> = None;
    let mut bump = |idx: u64| {
        max_idx = Some(max_idx.map_or(idx, |m| m.max(idx)));
    };
    // s2's domain
    for v in s2.dom() {
        bump(v.idx);
    }
    for t in s2.range() {
        use crate::lterm::HasFrees;
        t.for_each_free(&mut |v: &LVar| bump(v.idx));
    }
    for v in s1_0.dom() {
        bump(v.idx);
    }
    let fresh_start: u64 = max_idx.map(|m| m + 1).unwrap_or(0);
    let s1 = extended.fresh_to_free_uniform_shift(fresh_start);
    let composed = s1.compose(s2);
    free_to_fresh_raw(composed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::pair_sym;
    use crate::lterm::{LSort, LVar, Name};
    use crate::term::f_app_no_eq;
    use crate::vterm::var_term;

    type C = Name;

    fn lv(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }

    /// `instance HasFrees (SubstVFresh n LVar)` (SubstVFresh.hs):
    /// `foldFrees f . M.keys . svMap` sees the domain only, and `mapFrees`
    /// rewrites the key of each entry while carrying its image over as it is.
    #[test]
    fn subst_vfresh_folds_domain_only_and_leaves_the_range() {
        use crate::lterm::frees_list;
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("r", 5))),
            (lv("y", 1), var_term(lv("s", 6))),
        ]);
        assert_eq!(frees_list(&s), vec![lv("x", 0), lv("y", 1)]);
        let mapped = s.map_free(&mut |w| LVar::new(w.name, w.sort, w.idx + 10));
        assert_eq!(
            mapped.to_list(),
            vec![
                (lv("x", 10), var_term(lv("r", 5))),
                (lv("y", 11), var_term(lv("s", 6))),
            ]
        );
    }

    #[test]
    fn restrict_filters_keys() {
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
            (lv("x", 1), var_term(lv("z", 0))),
        ]);
        let r = s.restrict(&[lv("x", 0)]);
        // The kept key is the listed one, and its image stays intact.  A
        // check of the length alone also passes if the filter keeps the
        // opposite set of keys.
        assert_eq!(r.image_of(&lv("x", 0)), Some(&var_term(lv("y", 0))));
        assert_eq!(r.image_of(&lv("x", 1)), None);
        assert_eq!(r.len(), 1);
    }

    #[test]
    fn renaming_detection() {
        // `x ~> y` — straightforward rename; should be detected as such
        // when no other entry mentions `y`.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![(lv("x", 0), var_term(lv("y", 0)))]);
        assert!(s.is_renamed_var(&lv("x", 0)));
        assert!(s.is_renaming());
        assert!(s.remove_renamings().is_empty());

        // After adding a second entry that mentions `y`, `x ~> y` is no
        // longer a clean rename.  `is_renaming` gives the same answer.  It
        // uses its own single-pass check for duplicate targets, so it needs
        // its own negative case.
        let s2: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
            (lv("z", 0), var_term(lv("y", 0))),
        ]);
        assert!(!s2.is_renamed_var(&lv("x", 0)));
        assert!(!s2.is_renaming(), "duplicate target var is not a renaming");

        // A binding that changes the sort is not a rename either.  This
        // holds even when its target is unique.
        let s3: LSubstVFresh<C> = SubstVFresh::from_list(vec![(
            lv("x", 0),
            var_term(LVar::new("k", LSort::Fresh, 0)),
        )]);
        assert!(!s3.is_renamed_var(&lv("x", 0)));
        assert!(!s3.is_renaming(), "Msg ~> Fresh widens the sort");
        assert_eq!(s3.remove_renamings().len(), 1);
    }

    #[test]
    fn fresh_to_free_renames_every_range_var() {
        // HS has no "preserve" concept: every range var is renamed
        // unconditionally (Term/Substitution.hs) — the result must NOT
        // keep its identity.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![(lv("x", 0), var_term(lv("y", 5)))]);
        // Allocator hands out a fixed, clearly-distinct fresh idx.
        let free = s.fresh_to_free_avoiding(|_| 99);
        let img = free.image_of(&lv("x", 0)).expect("x.0 must be mapped");
        match img {
            Term::Lit(Lit::Var(v)) => {
                // Renamed to the freshly-allocated idx, NOT the original y.5.
                assert_eq!(v.idx, 99);
                assert_ne!(*v, lv("y", 5));
            }
            other => panic!("expected a renamed var, got {other:?}"),
        }
    }

    #[test]
    fn extend_with_renaming_shifts_the_new_vars_uniformly_above_the_range() {
        // HS (SubstVFresh.hs):
        //   extendWithRenaming vs0 s = substFromListVFresh $
        //     substToListVFresh s
        //       ++ substToListVFresh (renameFreshAvoiding s2 (varsRangeVFresh s))
        //     where s2 = substFromListVFresh [(v, lit (Var v)) | v <- vs ]
        //           vs = vs0 \\ domVFresh s
        // `renameFreshAvoiding s t = renameFresh s \`evalFreshAvoiding\` t`
        // (SubstVFresh.hs).  `renameFresh` (SubstVFresh.hs)
        // hands the whole range list to `rename` (LTerm.hs).  `rename`
        // takes one `freshStart - minVarIdx` shift.  It then applies
        // `incVar shift (LVar n so i) = LVar n so (i+shift)` to every var.
        // The name and the sort do not change, and the relative spacing stays
        // the same.  The avoid set is `varsRangeVFresh s`.  So
        // `freshStart = avoid = maybe 0 (succ . snd) . boundsVarIdx`
        // (LTerm.hs) reads the range vars, never the domain keys.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![(lv("a", 9), var_term(lv("w", 4)))]);
        let q = LVar::new("q", LSort::Fresh, 6);
        // `vs0 \\ domVFresh s` removes `a.9`.  The map in
        // `substFromListVFresh` collapses the repeated `p.2`.
        let out = s.extend_with_renaming(&[lv("a", 9), lv("p", 2), q, lv("p", 2)]);
        // freshStart = succ 4 = 5.  This value comes from the range var `w.4`,
        // not from the domain key `a.9`.  minVarIdx over {p.2, q.6} = 2, so
        // the single shift is +3.  The four-wide gap survives.  A dense repack
        // would answer `p.5` / `q.6` instead.
        assert_eq!(out.image_of(&lv("p", 2)), Some(&var_term(lv("p", 5))));
        assert_eq!(
            out.image_of(&q),
            Some(&var_term(LVar::new("q", LSort::Fresh, 9))),
            "`incVar` keeps the name and the sort"
        );
        // `extend_with_renaming` appends the existing mapping without any
        // change.  It does not rename that mapping again.
        assert_eq!(out.image_of(&lv("a", 9)), Some(&var_term(lv("w", 4))));
        assert_eq!(out.len(), 3);

        // Every requested var is already in `dom s`.  Then `vs` is empty, `s2`
        // is empty, and the result is `s` itself.
        assert_eq!(s.extend_with_renaming(&[lv("a", 9)]), s);

        // There is nothing to avoid.  Then `boundsVarIdx` is `Nothing` and
        // `avoid = 0`.  The shift is negative, so the renamings land at the
        // bottom.  They keep their spacing.
        let empty: LSubstVFresh<C> = SubstVFresh::empty();
        let out2 = empty.extend_with_renaming(&[lv("x", 3), lv("y", 7)]);
        assert_eq!(out2.image_of(&lv("x", 3)), Some(&var_term(lv("x", 0))));
        assert_eq!(out2.image_of(&lv("y", 7)), Some(&var_term(lv("y", 4))));
    }

    #[test]
    fn fresh_to_free_uniform_shift_rebases_the_range_and_drops_trivial_mappings() {
        // HS `freshToFreeAvoidingFast` (Term/Substitution.hs):
        //   freshToFreeAvoidingFast s t =
        //       substFromList . renameMappings . substToListVFresh $ s
        //     where renameMappings l =
        //             zip (map fst l) (rename (map snd l) `evalFreshAvoiding` t)
        // `rename` runs over the range list as a whole (LTerm.hs).  So
        // one shift `freshStart - minVarIdx` applies to all the entries.
        // `freshStart` is `avoid t`.  The caller passes it here as
        // `fresh_start`.  `substFromList` then drops trivial `x ~> x` mappings
        // (SubstVFree.hs).
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("a", 0), var_term(lv("y", 2))),
            (
                lv("a", 1),
                f_app_no_eq(pair_sym(), vec![var_term(lv("z", 5)), var_term(lv("y", 2))]),
            ),
            (lv("b", 10), var_term(lv("b", 2))),
        ]);
        let free = s.fresh_to_free_uniform_shift(10);
        // minVarIdx over the whole range = 2, so every range var moves by +8.
        // The spacing between y and z survives.  A per-entry allocation or a
        // dense allocation would put `z` next to `y`.  The two `y.2`
        // occurrences stay shared.
        assert_eq!(free.image_of(&lv("a", 0)), Some(&var_term(lv("y", 10))));
        assert_eq!(
            free.image_of(&lv("a", 1)),
            Some(&f_app_no_eq(
                pair_sym(),
                vec![var_term(lv("z", 13)), var_term(lv("y", 10))]
            ))
        );
        // `b.10 ~> b.2` shifts onto its own key, so `substFromList` drops it.
        assert_eq!(free.image_of(&lv("b", 10)), None);
        assert_eq!(free.len(), 2);

        // There are no range vars at all.  Then `rename` is the identity,
        // because `boundsVarIdx` is `Nothing`.  The conversion is only a
        // downgrade.
        let name = Name::new(crate::lterm::NameTag::Pub, "n");
        let konst: LSubstVFresh<C> =
            SubstVFresh::from_list(vec![(lv("c", 0), crate::vterm::const_term(name))]);
        let free2 = konst.fresh_to_free_uniform_shift(10);
        assert_eq!(
            free2.image_of(&lv("c", 0)),
            Some(&crate::vterm::const_term(name))
        );
    }

    #[test]
    fn compose_vfresh_avoid_set_reads_s1_domain_keys_not_its_range() {
        use crate::subst::Subst;
        // HS `composeVFresh s1_0 s2 = freeToFreshRaw (s1 `compose` s2)` where
        //   s1 = freshToFreeAvoidingFast
        //          (extendWithRenaming (varsRange s2) s1_0) (s2, s1_0)
        // (Term/Substitution.hs).  `evalFreshAvoiding` takes
        // `frees (s2,s1_0)`.  For a `SubstVFresh`, `frees` is
        // `foldFrees f = foldFrees f . M.keys . svMap`
        // (SubstVFresh.hs).  It reads the domain keys only.  So the
        // range witnesses of `s1_0` must not enter the avoid set.
        let s1_0: LSubstVFresh<C> =
            SubstVFresh::from_list(vec![(lv("k", 0), var_term(lv("m", 1000)))]);
        let s2: Subst<C, LVar> = Subst::from_list(vec![(lv("u", 0), var_term(lv("v", 3)))]);
        // A hand-run of the pipeline.  `extendWithRenaming [v.3] s1_0` avoids
        // `varsRangeVFresh s1_0 = {m.1000}`.  So freshStart = 1001 and
        // `v.3 ~> v.1001`.  Then `freshToFreeAvoidingFast` avoids
        // `frees (s2,s1_0)`, which is the idxs {u.0, v.3} ∪ {k.0}.  So
        // freshStart = 4, minVarIdx = 1000 and shift = -996.  That gives
        // `s1 = {k.0 ~> m.4, v.3 ~> v.5}`.  The composition with s2 rewrites
        // `u.0 ~> v.5` and keeps both bindings of s1.  A `frees s1_0` that
        // walked the range would be wrong.  It would make freshStart 1001, and
        // the witnesses would land at m.1001 / v.1002.
        let out = compose_vfresh(&s1_0, &s2);
        assert_eq!(out.image_of(&lv("u", 0)), Some(&var_term(lv("v", 5))));
        assert_eq!(out.image_of(&lv("k", 0)), Some(&var_term(lv("m", 4))));
        assert_eq!(out.image_of(&lv("v", 3)), Some(&var_term(lv("v", 5))));
        assert_eq!(out.len(), 3);

        // The empty-`s1_0` shape.  The call
        // `extendWithRenaming [v.3] ∅` avoids nothing, so freshStart is 0.  It
        // answers `v.3 ~> v.0`.  `freshToFreeAvoidingFast` then avoids
        // `frees (s2,∅)`, so freshStart is 4 and minVarIdx is 0.  That gives
        // `s1 = {v.3 ~> v.4}`, and the composition is
        // `{u.0 ~> v.4, v.3 ~> v.4}`.
        let empty: LSubstVFresh<C> = SubstVFresh::empty();
        let want: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("u", 0), var_term(lv("v", 4))),
            (lv("v", 3), var_term(lv("v", 4))),
        ]);
        assert_eq!(compose_vfresh(&empty, &s2), want);
    }
}
