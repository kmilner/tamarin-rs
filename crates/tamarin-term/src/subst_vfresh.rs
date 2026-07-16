//! Port of `Term.Substitution.SubstVFresh` from
//! `lib/term/src/Term/Substitution/SubstVFresh.hs`.
//!
//! Substitutions whose range variables are considered fresh — such
//! substitutions cannot be applied directly; the caller must first convert
//! them to a regular `Subst` by re-naming away from existing free vars.

use std::collections::BTreeMap;

use crate::lterm::{LVar, Name};
use crate::vterm::{Lit, VTerm};
use crate::term::{Term, TermSize};

// `PartialOrd` / `Ord` derived to mirror Haskell's `deriving (Ord, ..)` on
// `SubstVFresh c v` (SubstVFresh.hs:79-80).  Haskell's `S.toList` in `performSplit`
// returns substitutions in sorted order; we need the same canonical
// ordering so split-case enumeration matches Haskell (e.g. KAS2_eCK
// Resp_1 variant `c1 = aenc(x, pk(~lkR))` comes before the trivial
// one, giving `split_case_1` = the meaningful variant).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubstVFresh<C, V> {
    map: BTreeMap<V, VTerm<C, V>>,
}

impl<C, V> Default for SubstVFresh<C, V> {
    fn default() -> Self { SubstVFresh { map: BTreeMap::new() } }
}

pub type LSubstVFresh<C> = SubstVFresh<C, LVar>;
pub type LNSubstVFresh = SubstVFresh<Name, LVar>;

impl<C, V> SubstVFresh<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    pub fn empty() -> Self { SubstVFresh::default() }

    /// `substFromListVFresh`: build directly from a mapping list (no
    /// trivial-mapping filtering, unlike free-variable `Subst`).
    pub fn from_list(pairs: impl IntoIterator<Item = (V, VTerm<C, V>)>) -> Self {
        SubstVFresh { map: pairs.into_iter().collect() }
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

    /// `mapRangeVFresh`: rewrite the range elements; result variables are
    /// considered fresh.
    ///
    /// Intentionally retained for parity with HS `mapRangeVFresh`; no current
    /// Rust caller (the live `Subst::map_range` is the distinct free-subst
    /// variant).
    pub fn map_range<F: FnMut(VTerm<C, V>) -> VTerm<C, V>>(&self, mut f: F) -> Self {
        let map = self.map.iter().map(|(v, t)| (v.clone(), f(t.clone()))).collect();
        SubstVFresh { map }
    }

    pub fn dom(&self) -> impl Iterator<Item = &V> { self.map.keys() }
    pub fn range(&self) -> impl Iterator<Item = &VTerm<C, V>> { self.map.values() }
    pub fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> { self.map.get(v) }
    pub fn to_list(&self) -> Vec<(V, VTerm<C, V>)> {
        self.map.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    /// Borrowing view over the (key, image) pairs in domain order, avoiding
    /// the per-entry clones of `to_list` when callers only need to read.
    pub fn iter(&self) -> impl Iterator<Item = (&V, &VTerm<C, V>)> {
        self.map.iter()
    }
    pub fn is_empty(&self) -> bool { self.map.is_empty() }
    pub fn len(&self) -> usize { self.map.len() }
}

/// Rename every variable in `t` to a canonical fresh variable (empty name
/// hint, sort preserved), assigning indices 0,1,2,… in order of FIRST
/// appearance, threading `bindings`/`counter` so repeated occurrences (and
/// later range terms in the same substitution) reuse earlier assignments.
/// Left-to-right depth-first traversal mirrors HS `mapFrees`/`HasFrees`.
fn rename_term_drop_hint<C: Ord + Clone>(
    t: &VTerm<C, LVar>,
    bindings: &mut BTreeMap<LVar, LVar>,
    counter: &mut u64,
) -> VTerm<C, LVar> {
    match t {
        Term::Lit(Lit::Con(c)) => Term::Lit(Lit::Con(c.clone())),
        Term::Lit(Lit::Var(v)) => {
            let nv = match bindings.get(v) {
                Some(nv) => nv.clone(),
                None => {
                    let nv = LVar { name: "", sort: v.sort, idx: *counter };
                    *counter += 1;
                    bindings.insert(v.clone(), nv.clone());
                    nv
                }
            };
            Term::Lit(Lit::Var(nv))
        }
        Term::App(sym, args) => {
            let new_args: Vec<VTerm<C, LVar>> = args
                .iter()
                .map(|a| rename_term_drop_hint(a, bindings, counter))
                .collect();
            // Route through the AC/C-sorting smart constructor, matching
            // HS `mapFrees f@(Arbitrary _) (FApp o l) = fApp o <$> ...`
            // (LTerm.hs:733-734).  Renaming assigns fresh idxs by first
            // appearance, so an AC/C arg list sorted under the OLD vars
            // can become unsorted under the new ones; `fApp` re-sorts.
            crate::term::f_app(sym.clone(), new_args)
        }
    }
}

impl<C: Ord + Clone> LSubstVFresh<C> {
    /// `dropNameHintsLNSubstVFresh` (EquationStore.hs:143-147): the canonical
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
        let mut bindings: BTreeMap<LVar, LVar> = BTreeMap::new();
        let mut counter: u64 = 0;
        let renamed: Vec<(LVar, VTerm<C, LVar>)> = self
            .map
            .iter()
            .map(|(k, t)| (k.clone(), rename_term_drop_hint(t, &mut bindings, &mut counter)))
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
        let Some(t) = self.image_of(v) else { return false; };
        let Term::Lit(Lit::Var(target)) = t else { return false; };
        if target.sort != v.sort { return false; }
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
            let Term::Lit(Lit::Var(target)) = t else { return false; };
            if target.sort != v.sort { return false; }
            // A duplicate target means this target var also appears in another
            // entry, so that entry's `is_renamed_var` would have failed.
            if !targets.insert(target) { return false; }
        }
        true
    }

    /// `removeRenamings`: drop every entry that's just a rename.
    pub fn remove_renamings(&self) -> Self {
        let map = self
            .map
            .iter()
            .filter(|(v, _)| !self.is_renamed_var(v))
            .map(|(v, t)| (v.clone(), t.clone()))
            .collect();
        SubstVFresh { map }
    }

    /// `extendWithRenaming vs s`: extends `s` with renamings (with fresh
    /// variables) for the variables in `vs` that are not already in
    /// `dom s`.  Mirrors HS `Term.Substitution.SubstVFresh.extendWithRenaming`
    /// (SubstVFresh.hs:115-121).
    ///
    /// The new renamings use uniformly-shifted fresh idxs starting above
    /// `varsRangeVFresh self` (HS: `renameFreshAvoiding s2 (varsRangeVFresh s)`).
    /// The shift = freshStart - min(idx of vs_new); applied to each var in
    /// vs_new uniformly, preserving relative ordering — mirrors HS's
    /// `rename` semantics (LTerm.hs:607-614).
    pub fn extend_with_renaming(&self, vs: &[LVar]) -> Self {
        // Domain probes go straight to the map (`image_of` = `BTreeMap::get`)
        // and the first-appearance dedup uses a hash `seen` set: both are
        // membership-only, so neither needs the ordered `BTreeSet` builds the
        // eager version materialised per call.  `vs_new` carries the order.
        let mut vs_new: Vec<LVar> = Vec::new();
        let mut seen: tamarin_utils::FastSet<LVar> = Default::default();
        for v in vs {
            if self.image_of(v).is_some() { continue; }
            if seen.insert(v.clone()) {
                vs_new.push(v.clone());
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
        let new_entries: Vec<(LVar, VTerm<C, LVar>)> = vs_new.iter()
            .map(|v| {
                let new_idx = shifted_idx(v.idx, shift);
                let v_new = LVar {
                    name: v.name,
                    sort: v.sort,
                    idx: new_idx,
                };
                (v.clone(), Term::Lit(Lit::Var(v_new)))
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

    /// HS-faithful `freshToFreeAvoidingFast`:  rename all range vars
    /// uniformly via HS's `rename` shift (freshStart - minVar), where
    /// `freshStart` = `succ . maxIdx . avoid` and `minVar`/`maxVar` are
    /// across the bundled range terms.  Mirrors
    /// `Term.Substitution.freshToFreeAvoidingFast` (Substitution.hs:77-92).
    ///
    /// Differs from `fresh_to_free_avoiding` (preserve-set form): this one
    /// uses HS's UNIFORM SHIFT (preserving relative ordering of range-var
    /// idxs) rather than dense-packed sequential allocation.  Required for
    /// `compose_vfresh` to produce structurally-equivalent SubstVFresh
    /// shapes per variant.
    ///
    /// `fresh_start` is the precomputed `succ . maxIdx . frees(avoid)`: the
    /// single value the rename actually needs from the avoid set (its max
    /// idx + 1), passed directly so the avoid collection is never materialised.
    pub fn fresh_to_free_uniform_shift(&self, fresh_start: u64)
        -> crate::subst::Subst<C, LVar>
    {
        use crate::subst::Subst;
        // Collect ALL distinct range vars in insertion order.
        let range_vars: Vec<LVar> = distinct_range_vars(self.range());
        if range_vars.is_empty() {
            // No range vars to rename — just downgrade (through `from_list`,
            // which drops trivial `x ~> x` mappings exactly as before).
            return Subst::from_list(self.iter().map(|(v, t)| (v.clone(), t.clone())));
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
            rename.insert(old.clone(), new);
        }
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::with_capacity(self.len());
        // Borrowing walk: the rename rebuilds every range term anyway, so read
        // the entries in place (`iter`) rather than cloning them up front with
        // `to_list`.
        for (v, t) in self.iter() {
            let renamed = rename_lvars_in_vterm(t, &rename);
            pairs.push((v.clone(), renamed));
        }
        Subst::from_list(pairs)
    }

    /// `freshToFree`: convert this VFresh substitution to a free `Subst`
    /// by renaming each range variable to a fresh LVar using indices
    /// obtained from `alloc_idxs` (a MonadFresh substitute — typically
    /// wrapping `MaudeHandle::reserve_idxs`).  Implements the
    /// `freshToFree`/`freshToFreeAvoiding` algorithm
    /// (Substitution.hs:54-72): sort by image size + per-binding name
    /// hints + `importBinding` caching.  (The uniform-shift
    /// `freshToFreeAvoidingFast` at Substitution.hs:77-81 is instead
    /// implemented by `fresh_to_free_uniform_shift`.)
    ///
    /// The reduction layer composes the result into the eq-store's
    /// free substitution so the picked variant's bindings propagate
    /// to rule terms during the next `substSystem` pass.
    pub fn fresh_to_free<F: FnMut(u64) -> u64>(
        &self,
        alloc_idxs: F,
    ) -> crate::subst::Subst<C, LVar> {
        // Every range var is treated as a witness and gets renamed.
        self.fresh_to_free_avoiding(alloc_idxs)
    }

    /// `freshToFreeAvoiding`: convert VFresh → free subst.
    ///
    /// Mirrors Haskell `freshToFreeAvoiding s t = freshToFree s
    /// \`evalFreshAvoiding\` t` (Substitution.hs:71-72, built on
    /// `freshToFree` at 54-66): sorts entries by image size and applies
    /// the per-binding name-hint rule.  It renames every range var
    /// unconditionally (HS has no "preserve" concept — `evalFreshAvoiding`
    /// only seeds the fresh counter above `t`'s max idx, it never skips a
    /// variable).
    pub fn fresh_to_free_avoiding<F: FnMut(u64) -> u64>(
        &self,
        mut alloc_idxs: F,
    ) -> crate::subst::Subst<C, LVar> {
        use crate::subst::Subst;
        // HS has NO preserve concept in ANY freshToFree* variant:
        //   - `freshToFree` (Substitution.hs:54-66) imports EVERY range
        //     var to a brand-new fresh var via `importBinding`;
        //   - `freshToFreeAvoiding` (:69-71) is just
        //     `freshToFree s \`evalFreshAvoiding\` t` — `evalFreshAvoiding`
        //     only SEEDS the fresh counter above t's max idx, it never
        //     skips a variable;
        //   - `freshToFreeAvoidingFast` (:74-81) renames all range vars
        //     via `rename ... \`evalFreshAvoiding\` t` — same.
        // We therefore rename every range var unconditionally.  HS maintains
        // the invariant that VFresh ranges are pure-fresh (composeVFresh's
        // `extendWithRenaming`, Substitution.hs:40-47), so keeping a range
        // var's identity would be unsound: it could fuse a Maude witness with
        // an unrelated live system var that happens to share (name, sort, idx).
        // HS-faithful port (Substitution.hs:54-66):
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
        // Two key behaviours:
        // 1. Sort by image size (singletons first) — gives single-var
        //    images the chance to claim the fresh slot first.
        // 2. Name hint: for a singleton-Var image `(lv, ~x.K)`, name the
        //    fresh from the DOMAIN var's name (`lvarName lv`).  For an
        //    App image like `(lv, h(...))`, the inner vars keep their
        //    ORIGINAL names (`lvarName v`).
        //
        // `evalBindT noBindings` caches rename decisions per VFresh
        // range var: the first binding to claim a range var sets its
        // name+idx; subsequent uses reuse the cached fresh.  This is
        // what makes `~k → ~x.11` followed by `~k.1 → ~x.11` produce a
        // SHARED renamed var (both → ~k.<new>), folding the alpha-
        // equivalence into the free subst.

        // Step 0: sort entries by size of image (smaller first).
        // HS's `sortOn (size . snd)` — stable sort by size, via the
        // `TermSize` trait (term.rs) which encodes HS's `Term.size`.
        let mut slist: Vec<(LVar, VTerm<C, LVar>)> = self.to_list();
        slist.sort_by_key(|(_, t)| t.size());

        // Step 1: cache binding map (range var → new var), built
        // incrementally as we walk substs in sorted order.
        let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();

        // Step 2: process each (lv, t) and rename inner vars per HS
        // semantics.  When t is a singleton Var, use lv's name as hint;
        // otherwise use the inner var's name.
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::with_capacity(slist.len());
        for (lv, t) in slist.into_iter() {
            // Determine the namehint mode based on the OUTER term shape.
            let outer_is_singleton_var = matches!(&t, Term::Lit(Lit::Var(_)));
            let renamed = rename_lvars_with_hint(&t, &mut rename, &mut alloc_idxs,
                outer_is_singleton_var, &lv);
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
    if new_idx_signed < 0 { 0 }
    else if new_idx_signed > u64::MAX as i128 { u64::MAX }
    else { new_idx_signed as u64 }
}

/// Walk a VTerm, renaming each var via the rename map.  If a var
/// isn't yet in the rename map, allocate a fresh idx for it and
/// record the binding.  `outer_is_singleton_var` + `lv` together
/// implement HS's `namehint v = if (Lit (Var _) == t) then lvarName lv
/// else lvarName v` rule (Substitution.hs:64-66).
fn rename_lvars_with_hint<C: Ord + Clone, F: FnMut(u64) -> u64>(
    t: &VTerm<C, LVar>,
    rename: &mut BTreeMap<LVar, LVar>,
    alloc_idxs: &mut F,
    outer_is_singleton_var: bool,
    lv: &LVar,
) -> VTerm<C, LVar> {
    match t {
        Term::Lit(Lit::Var(v)) => {
            if let Some(new) = rename.get(v).cloned() {
                Term::Lit(Lit::Var(new))
            } else {
                // Allocate a fresh idx; name hint depends on outer
                // term shape.
                let idx = alloc_idxs(1);
                let name = if outer_is_singleton_var {
                    lv.name
                } else {
                    v.name
                };
                let new = LVar { name, sort: v.sort, idx };
                rename.insert(v.clone(), new.clone());
                Term::Lit(Lit::Var(new))
            }
        }
        Term::Lit(Lit::Con(c)) => Term::Lit(Lit::Con(c.clone())),
        Term::App(f, args) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| rename_lvars_with_hint(a, rename, alloc_idxs,
                    outer_is_singleton_var, lv))
                .collect();
            // Route through the smart constructor so AC/C argument lists
            // are re-sorted: freshToFree allocates a brand-new, non-
            // monotone idx per range var, so children that were sorted
            // under the old vars are no longer canonical under the new
            // ones.  HS does the same via `mapFrees (Arbitrary _)
            // (FApp o l) = fApp o <$> ...` (LTerm.hs).  (The sibling
            // `rename_lvars_in_vterm` stays raw — it mirrors HS's
            // Monotone `unsafefApp` path under a uniform, order-
            // preserving shift, where re-sorting is unnecessary.)
            crate::term::f_app(f.clone(), new_args)
        }
    }
}

/// `freeToFreshRaw`: re-tag a free `Subst`'s entries as a `SubstVFresh`.
/// Mirrors HS `Term.Substitution.freeToFreshRaw` (Substitution.hs:84-85):
/// considers all variables in the range as fresh.  No structural change —
/// just a type-level reinterpretation, so the owned map moves across
/// wholesale (`SubstVFresh::from_list` does no trivial-drop; a
/// `from_list(to_list)` round-trip would rebuild the identical map from clones).
pub fn free_to_fresh_raw<C: Ord + Clone>(s: crate::subst::Subst<C, LVar>)
    -> LSubstVFresh<C>
{
    LSubstVFresh { map: s.into_map() }
}

/// `composeVFresh s1_0 s2` (Substitution.hs:41-47).  Dispatches to a
/// closed-form fast path for the dominant `s1_0 = ∅` shape and otherwise runs
/// the full 4-stage pipeline in [`compose_vfresh_general`].
///
/// Every locally-solved `unify` runs `flattenUnif` as `[∅ composeVFresh m]`
/// (maude_proc.rs local fast paths), so `s1_0` is empty by construction there;
/// the AC-arm and rule-variant call sites pass a non-empty `s1_0` and take the
/// general path unchanged.
pub fn compose_vfresh<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> LSubstVFresh<C>
where
    C: Ord + Clone,
{
    if s1_0.is_empty() {
        let fast = compose_vfresh_empty_s1(s2);
        // Differential guard during bring-up: the fast path must be VALUE-
        // identical to the general composition (witness idxs feed
        // `Ord LNSubstVFresh` and split-case ordering).  Only compiled in
        // debug builds; the full 402-file byte gate is the release check.
        #[cfg(debug_assertions)]
        {
            let slow = compose_vfresh_general(s1_0, s2);
            debug_assert!(
                fast == slow,
                "compose_vfresh empty-s1 fast path diverged from general composition",
            );
        }
        return fast;
    }
    compose_vfresh_general(s1_0, s2)
}

/// Closed-form `composeVFresh ∅ s2`.
///
/// For an empty `s1_0` the general pipeline's four intermediate structures
/// collapse to a single uniform, order-preserving range-var rename.  Deriving
/// it from the code (Substitution.hs:41-47):
///
///  * `extendWithRenaming (varsRange s2) ∅` renames every distinct range var
///    `w` of `s2` down by `vs_min = min idx of varsRange s2` (its avoid set is
///    empty ⇒ `freshStart = 0`);
///  * `freshToFreeAvoidingFast _ (s2, ∅)` then shifts every range var up by
///    `fresh_start = maxIdx(frees s2) + 1` (the shifted-down vars have min idx
///    0, so `shift = fresh_start`).  `frees ∅ = keys ∅ = {}`, so the avoid set
///    is exactly `frees s2` (its domain and range vars).
///
/// The two shifts fold to one uniform delta `> 0`, so `w' = LVar{w.name,
/// w.sort, w.idx - vs_min + maxIdx(frees s2) + 1}` for each range var `w`, with
/// `w'.idx > maxIdx(frees s2) ≥` every domain key idx.  Hence:
///
///  * `s1 = {w -> Var(w') | w ∈ varsRange s2}` (nothing dropped: `w' ≠ w`);
///  * `s1 `compose` s2` = `{k -> s2[k][w↦w'] | (k,_) ∈ s2}` (the `map_range`
///    trivial-drop is vacuous — `w'.idx > k.idx` — but is still applied for
///    definitional parity) `∪ {w -> Var(w') | w ∈ varsRange s2, w ∉ dom s2}`;
///  * `freeToFreshRaw` re-tags without dropping.
///
/// The per-mapping term walk reuses `apply_vterm_map` — the exact primitive
/// `Subst::compose` calls — so AC re-sorting and sharing are byte-identical.
fn compose_vfresh_empty_s1<C>(s2: &crate::subst::Subst<C, LVar>) -> LSubstVFresh<C>
where
    C: Ord + Clone,
{
    // Distinct range vars of s2 (varsRange s2), plus the max idx over all of
    // s2's free vars (its avoid set; frees s2 walks BOTH domain and range).
    // The `seen` set is membership-only (`range_vars` carries the order).
    let mut range_vars: Vec<LVar> = Vec::new();
    let mut seen: tamarin_utils::FastSet<LVar> = Default::default();
    let mut max_idx: Option<u64> = None;
    for v in s2.dom() {
        max_idx = Some(max_idx.map_or(v.idx, |m| m.max(v.idx)));
    }
    for t in s2.range() {
        for v in crate::vterm::vars_vterm(t) {
            max_idx = Some(max_idx.map_or(v.idx, |m| m.max(v.idx)));
            if seen.insert(v.clone()) {
                range_vars.push(v);
            }
        }
    }
    // No range vars ⇒ nothing to rename: extendWithRenaming is a no-op and
    // freshToFreeAvoidingFast is the identity, so composeVFresh collapses to
    // `freeToFreshRaw s2` — a pure re-tag, so clone the map wholesale
    // (`SubstVFresh::from_list` does no trivial-drop; the entries are
    // identical to the `from_list(to_list)` round-trip).
    if range_vars.is_empty() {
        return SubstVFresh { map: s2.clone().into_map() };
    }
    let vs_min: u64 = range_vars.iter().map(|v| v.idx).min().unwrap();
    // `fresh_start` = succ . maxIdx . frees s2 (= maxIdx over dom+range + 1).
    let fresh_start: u64 = max_idx.unwrap() + 1;
    // Fold the two order-preserving shifts (down by vs_min, up by fresh_start)
    // through the shared `shifted_idx` at each step so the load-bearing clamp
    // cannot drift from the general path.  Step 1 never clamps (result ≤ idx),
    // so this equals a single positive uniform shift `fresh_start - vs_min`.
    let mut s1_map: BTreeMap<LVar, VTerm<C, LVar>> = BTreeMap::new();
    for w in &range_vars {
        let down = shifted_idx(w.idx, -(vs_min as i128));
        let up = shifted_idx(down, fresh_start as i128);
        let w_prime = LVar { name: w.name, sort: w.sort, idx: up };
        s1_map.insert(w.clone(), Term::Lit(Lit::Var(w_prime)));
    }
    let mut out: Vec<(LVar, VTerm<C, LVar>)> = Vec::new();
    // `s1 `compose` s2` first arm = `s2.map_range(|t| apply_vterm(s1, t))`:
    // rename every range var through the mapping, dropping trivial results
    // exactly as `map_range` does.
    for (v, t) in s2.iter() {
        let t2 = crate::subst::apply_vterm_map(&s1_map, t.clone());
        if !matches!(&t2, Term::Lit(Lit::Var(w)) if w == v) {
            out.push((v.clone(), t2));
        }
    }
    // `compose`'s second arm: s1's own bindings whose domain s2 does not
    // rebind, added unconditionally (w' ≠ w, so never trivial anyway).
    // Probe s2's map directly (`image_of` = `BTreeMap::get`) instead of
    // materialising a domain set for a handful of membership tests.
    for w in &range_vars {
        if s2.image_of(w).is_none() {
            // `s1_map[w]` exists for every range var by construction.
            out.push((w.clone(), s1_map[w].clone()));
        }
    }
    LSubstVFresh::from_list(out)
}

/// Collect all distinct range vars in first-appearance order.
///
/// Walks the given range terms (each expanded via `vars_vterm`, whose per-term
/// order is preserved) and keeps only the first occurrence of each var, guarded
/// by a `seen` set.  Shared by `fresh_to_free_uniform_shift` and
/// `compose_vfresh_general`, which differ only in which subst's range is walked.
/// The `seen` set is membership-only (`out` carries the byte-visible order),
/// so a hash set replaces the per-occurrence BTree insert.
fn distinct_range_vars<'a, C: 'a>(
    range: impl Iterator<Item = &'a VTerm<C, LVar>>,
) -> Vec<LVar> {
    let mut out: Vec<LVar> = Vec::new();
    let mut seen: tamarin_utils::FastSet<LVar> = Default::default();
    for t in range {
        for v in crate::vterm::vars_vterm(t) {
            if seen.insert(v.clone()) {
                out.push(v);
            }
        }
    }
    out
}

/// `composeVFresh s1 s2`: composes the fresh substitution `s1` with the
/// free substitution `s2`.  Mirrors HS `Term.Substitution.composeVFresh`
/// (Substitution.hs:41-47):
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
/// Pipeline per variant:
/// 1. `extendWithRenaming (varsRange s2) s1_0` — add renaming entries
///    for s2's range vars not already in s1_0's domain.  Renamings get
///    uniform-shifted fresh idxs above `varsRangeVFresh s1_0`.
/// 2. `freshToFreeAvoidingFast _ (s2, s1_0)` — uniformly shift all range
///    vars above max idx in (s2, s1_0).  Convert to free `Subst`.
/// 3. `s1 \`compose\` s2` — Robinson compose.
/// 4. `freeToFreshRaw` — re-tag range as fresh.
///
/// This is what HS uses per-variant in `variantsProtoRule`
/// (RuleVariants.hs:74-77).  Without this pipeline, two variants whose
/// Maude-back-conversion shapes happen to collide will end up with
/// structurally-identical range vars and collapse at `perform_split`.
fn compose_vfresh_general<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> LSubstVFresh<C>
where
    C: Ord + Clone,
{
    // varsRange s2: vars in s2's range
    let vs_in_range_s2: Vec<LVar> = distinct_range_vars(s2.range());
    let extended = s1_0.extend_with_renaming(&vs_in_range_s2);
    // Avoid set for freshToFreeAvoidingFast: `evalFreshAvoiding (s2, s1_0)`
    // (Substitution.hs:47) = `frees (s2, s1_0)` = `frees s2 <> frees s1_0`.
    //
    // `frees s2` (s2 :: free LNSubst) walks BOTH domain and range.
    // `frees s1_0` (s1_0 :: LNSubstVFresh) uses `foldFrees (SubstVFresh n
    // LVar) = foldFrees f . M.keys` (SubstVFresh.hs:197) — i.e. ONLY the
    // DOMAIN KEYS, NOT the range (witnesses).  Including s1_0's range here
    // would over-count the avoid set and inflate the re-based witnesses
    // (Responder_secrecy: the Setup_Key `~k` variant witnesses at ~k.30/42
    // vs HS's ~k.11/12/15, rotating the 3-way split via `Ord LNSubstVFresh`).
    // `freshToFreeAvoidingFast` only consults the avoid set for its max idx
    // (`succ . maxIdx`), so fold that max directly over the same three sources
    // instead of materialising a BTreeSet + Vec.  Dedup/order are irrelevant
    // to a max, so the resulting `fresh_start` matches the same-value
    // computation via a max fold, without materialising a set/list.
    let mut max_idx: Option<u64> = None;
    let mut bump = |idx: u64| { max_idx = Some(max_idx.map_or(idx, |m| m.max(idx))); };
    // s2's domain
    for v in s2.dom() { bump(v.idx); }
    // s2's range vars — visited in place (`for_each_free`); `vars_vterm`'s
    // per-term sort/dedup Vec is irrelevant to a max.
    for t in s2.range() {
        use crate::lterm::HasFrees;
        t.for_each_free(&mut |v: &LVar| bump(v.idx));
    }
    // s1_0's domain keys ONLY (HS-faithful: frees of a SubstVFresh = keys).
    for v in s1_0.dom() { bump(v.idx); }
    let fresh_start: u64 = max_idx.map(|m| m + 1).unwrap_or(0);
    let s1 = extended.fresh_to_free_uniform_shift(fresh_start);
    let composed = s1.compose(s2);
    free_to_fresh_raw(composed)
}

/// Walk a VTerm, applying a LVar→LVar rename.
fn rename_lvars_in_vterm<C: Clone>(
    t: &VTerm<C, LVar>,
    rename: &tamarin_utils::FastMap<LVar, LVar>,
) -> VTerm<C, LVar> {
    match t {
        Term::Lit(Lit::Var(v)) => {
            let new = rename.get(v).cloned().unwrap_or_else(|| v.clone());
            Term::Lit(Lit::Var(new))
        }
        Term::Lit(other) => Term::Lit(other.clone()),
        Term::App(f, args) => Term::App(
            f.clone(),
            args.iter().map(|a| rename_lvars_in_vterm(a, rename)).collect(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{LSort, LVar, Name};
    use crate::vterm::var_term;

    type C = Name;

    fn lv(name: &str, idx: u64) -> LVar { LVar::new(name, LSort::Msg, idx) }

    #[test]
    fn empty_substitution() {
        let s: LSubstVFresh<C> = SubstVFresh::empty();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn restrict_filters_keys() {
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
            (lv("x", 1), var_term(lv("z", 0))),
        ]);
        let r = s.restrict(&[lv("x", 0)]);
        assert_eq!(r.len(), 1);
    }

    #[test]
    fn renaming_detection() {
        // `x ~> y` — straightforward rename; should be detected as such
        // when no other entry mentions `y`.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
        ]);
        assert!(s.is_renamed_var(&lv("x", 0)));
        assert!(s.is_renaming());

        // After adding a second entry that mentions `y`, `x ~> y` is no
        // longer a clean rename.
        let s2: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
            (lv("z", 0), var_term(lv("y", 0))),
        ]);
        assert!(!s2.is_renamed_var(&lv("x", 0)));
    }

    #[test]
    fn fresh_to_free_renames_every_range_var() {
        // HS has no "preserve" concept: every range var is renamed
        // unconditionally (Substitution.hs:54-72) — the result must NOT
        // keep its identity.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 5))),
        ]);
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
}
