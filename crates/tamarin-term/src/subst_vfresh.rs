// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Substitution.SubstVFresh` from
//! `lib/term/src/Term/Substitution/SubstVFresh.hs`.
//!
//! Substitutions whose range variables are considered fresh — such
//! substitutions cannot be applied directly; the caller must first convert
//! them to a regular `Subst` by re-naming away from existing free vars.

use std::collections::{BTreeMap, BTreeSet};

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
    /// `map snd (substToListVFresh s)`. Domain keys are kept unchanged.
    /// The traversal uses the stored order of AC and commutative children.
    /// Renaming range variables can change that order, so α-equivalent
    /// substitutions can have different split-case sort keys.
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
    /// `rename` semantics (LTerm.hs). If the shift exceeds u64 the
    /// allocator uses unoccupied indices in the same relative order.
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
        // The usual shift needs only the maximum. Collect the occupied
        // indices only if the full shift cannot be represented.
        let mut avoid_max: Option<u64> = None;
        for t in self.range() {
            use crate::lterm::HasFrees;
            t.for_each_free(&mut |v: &LVar| {
                avoid_max = Some(avoid_max.map_or(v.idx, |m| m.max(v.idx)));
            });
        }
        let indices = IndexRenaming::avoiding(&vs_new, avoid_max, || {
            distinct_range_vars(self.range())
                .into_iter()
                .map(|v| v.idx)
                .collect()
        });
        let mut map = self.map.clone();
        for v in vs_new {
            map.insert(v, Term::Lit(Lit::Var(indices.rename(v))));
        }
        SubstVFresh { map }
    }

    /// Shift every range index by the same offset so the minimum lands at
    /// `fresh_start`. Returns `None` if that uniform shift cannot fit in u64.
    /// Callers with the actual finite scope can use `fresh_to_free_avoiding_vars`.
    pub fn fresh_to_free_uniform_shift(
        &self,
        fresh_start: u64,
    ) -> Option<crate::subst::Subst<C, LVar>> {
        let vars = distinct_range_vars(self.range());
        let indices = IndexRenaming::uniform(&vars, Some(fresh_start))?;
        Some(self.rename_range(&indices))
    }

    /// Freshen all images together, preserving the upstream uniform shift
    /// whenever it fits. At the index boundary the full scope identifies
    /// unused indices which can be assigned in increasing order.
    pub fn fresh_to_free_avoiding_vars(&self, avoid: &[LVar]) -> crate::subst::Subst<C, LVar> {
        let vars = distinct_range_vars(self.range());
        let indices = IndexRenaming::avoiding(&vars, avoid.iter().map(|v| v.idx).max(), || {
            avoid.iter().map(|v| v.idx).collect()
        });
        self.rename_range(&indices)
    }

    fn rename_range(&self, indices: &IndexRenaming) -> crate::subst::Subst<C, LVar> {
        crate::subst::Subst::from_list(
            self.iter()
                .map(|(v, t)| (*v, t.clone().map_free_monotone(&mut |w| indices.rename(w)))),
        )
    }

    /// `freshToFree`: convert this VFresh substitution to a free `Subst`
    /// by renaming each range variable to a fresh LVar using indices
    /// obtained from `alloc_idxs` (a MonadFresh substitute — typically
    /// wrapping `MaudeHandle::reserve_idxs`).  Implements the
    /// `freshToFree`/`freshToFreeAvoiding` algorithm
    /// (Term/Substitution.hs): sort by image size + per-binding name
    /// hints + `importBinding` caching.  (The uniform-shift
    /// `freshToFreeAvoidingFast` at Term/Substitution.hs is instead
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
    /// \`evalFreshAvoiding\` t` (Term/Substitution.hs, built on
    /// `freshToFree`): sorts entries by image size and applies
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
        //   - `freshToFree` (Term/Substitution.hs) imports EVERY range
        //     var to a brand-new fresh var via `importBinding`;
        //   - `freshToFreeAvoiding` is just
        //     `freshToFree s \`evalFreshAvoiding\` t` — `evalFreshAvoiding`
        //     only SEEDS the fresh counter above t's max idx, it never
        //     skips a variable;
        //   - `freshToFreeAvoidingFast` renames all range vars
        //     via `rename ... \`evalFreshAvoiding\` t` — same.
        // We therefore rename every range var unconditionally.  HS maintains
        // the invariant that VFresh ranges are pure-fresh (composeVFresh's
        // `extendWithRenaming`, Term/Substitution.hs), so keeping a range
        // var's identity would be unsound: it could fuse a Maude witness with
        // an unrelated live system var that happens to share (name, sort, idx).
        // HS-faithful port (Term/Substitution.hs):
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

/// Both representations preserve the order of source indices, including ties
/// between variables of different names or sorts at the same index.
enum IndexRenaming {
    Uniform { min: u64, start: u64 },
    Sparse(BTreeMap<u64, u64>),
}

impl IndexRenaming {
    fn uniform(vars: &[LVar], start: Option<u64>) -> Option<Self> {
        let Some(first) = vars.first() else {
            return Some(Self::Uniform { min: 0, start: 0 });
        };
        let (min, max) = vars.iter().fold((first.idx, first.idx), |(min, max), v| {
            (min.min(v.idx), max.max(v.idx))
        });
        let start = start?;
        start.checked_add(max - min)?;
        Some(Self::Uniform { min, start })
    }

    fn avoiding(
        vars: &[LVar],
        avoid_max: Option<u64>,
        occupied: impl FnOnce() -> BTreeSet<u64>,
    ) -> Self {
        let start = avoid_max.map_or(Some(0), |m| m.checked_add(1));
        if let Some(shift) = Self::uniform(vars, start) {
            return shift;
        }
        let used = occupied();
        let sources: BTreeSet<_> = vars.iter().map(|v| v.idx).collect();
        let mut free = (0..=u64::MAX).filter(|i| !used.contains(i));
        // Both sets fit in addressable memory, so together they contain
        // fewer than 2^64 indices. Each new source consumes one free index.
        Self::Sparse(
            sources
                .into_iter()
                .map(|i| {
                    (
                        i,
                        free.next()
                            .expect("finite witness scope exhausted all u64 indices"),
                    )
                })
                .collect(),
        )
    }

    fn rename(&self, v: LVar) -> LVar {
        let idx = match self {
            Self::Uniform { min, start } => start + (v.idx - min),
            Self::Sparse(map) => map[&v.idx],
        };
        LVar { idx, ..v }
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

/// `composeVFresh s1_0 s2` (Term/Substitution.hs).  Dispatches to a
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
        // Differential guard: the fast path must be VALUE-identical to the
        // general composition (witness idxs feed `Ord LNSubstVFresh` and
        // split-case ordering).  Only compiled in debug builds; the
        // full-corpus byte gate is the release check.
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
/// The two rebasing steps in the general pipeline collapse to a single
/// order-preserving rename of the range variables of `s2`. The occupied
/// indices come from the domain and range of `s2`. When the uniform shift
/// overflows, ranking the original indices gives the same assignment as
/// ranking them after subtracting their minimum. Applying the rename to
/// each image and retaining its bindings outside the domain of `s2` gives
/// the same substitution as the general composition.
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
            if seen.insert(v) {
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
        return SubstVFresh {
            map: s2.clone().into_map(),
        };
    }
    let indices = IndexRenaming::avoiding(&range_vars, max_idx, || {
        s2.dom().chain(range_vars.iter()).map(|v| v.idx).collect()
    });
    let mut s1_map: BTreeMap<LVar, VTerm<C, LVar>> = BTreeMap::new();
    for w in &range_vars {
        let w_prime = indices.rename(*w);
        s1_map.insert(*w, Term::Lit(Lit::Var(w_prime)));
    }
    let mut out: Vec<(LVar, VTerm<C, LVar>)> = Vec::new();
    // `s1 `compose` s2` first arm = `s2.map_range(|t| apply_vterm(s1, t))`:
    // rename every range var through the mapping, dropping trivial results
    // exactly as `map_range` does.
    for (v, t) in s2.iter() {
        let t2 = crate::subst::apply_vterm_map(&s1_map, t.clone());
        if !matches!(&t2, Term::Lit(Lit::Var(w)) if w == v) {
            out.push((*v, t2));
        }
    }
    // `compose`'s second arm: s1's own bindings whose domain s2 does not
    // rebind, added unconditionally (w' ≠ w, so never trivial anyway).
    // Probe s2's map directly (`image_of` = `BTreeMap::get`) instead of
    // materialising a domain set for a handful of membership tests.
    for w in &range_vars {
        if s2.image_of(w).is_none() {
            // `s1_map[w]` exists for every range var by construction.
            out.push((*w, s1_map[w].clone()));
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
/// (RuleVariants.hs).  Without this pipeline, two variants whose
/// Maude-back-conversion shapes happen to collide will end up with
/// structurally-identical range vars and collapse at `perform_split`.
fn compose_vfresh_general<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> LSubstVFresh<C>
where
    C: Ord + Clone,
{
    compose_vfresh_renaming(s1_0, s2).0
}

/// [`compose_vfresh`], together with the name it gave each range variable of
/// `s1_0`. The composition renames those variables by index alone, so the
/// second component is an injective map.
pub fn compose_vfresh_traced<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> (LSubstVFresh<C>, BTreeMap<LVar, LVar>)
where
    C: Ord + Clone,
{
    if s1_0.is_empty() {
        return (compose_vfresh(s1_0, s2), BTreeMap::new());
    }
    let (composed, indices) = compose_vfresh_renaming(s1_0, s2);
    let renamed = distinct_range_vars(s1_0.range())
        .into_iter()
        .map(|v| (v, indices.rename(v)))
        .collect();
    (composed, renamed)
}

fn compose_vfresh_renaming<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> (LSubstVFresh<C>, IndexRenaming)
where
    C: Ord + Clone,
{
    // varsRange s2: vars in s2's range
    let vs_in_range_s2: Vec<LVar> = distinct_range_vars(s2.range());
    let extended = s1_0.extend_with_renaming(&vs_in_range_s2);
    // Avoid set for freshToFreeAvoidingFast: `evalFreshAvoiding (s2, s1_0)`
    // (Term/Substitution.hs) = `frees (s2, s1_0)` = `frees s2 <> frees s1_0`.
    //
    // `frees s2` (s2 :: free LNSubst) walks BOTH domain and range.
    // `frees s1_0` (s1_0 :: LNSubstVFresh) uses `foldFrees (SubstVFresh n
    // LVar) = foldFrees f . M.keys` (SubstVFresh.hs) — i.e. ONLY the
    // DOMAIN KEYS, NOT the range (witnesses).  Including s1_0's range here
    // would over-count the avoid set and inflate the re-based witnesses
    // (Responder_secrecy: the Setup_Key `~k` variant witnesses at ~k.30/42
    // vs HS's ~k.11/12/15, rotating the 3-way split via `Ord LNSubstVFresh`).
    let occupied = || {
        s2.dom()
            .chain(s1_0.dom())
            .chain(vs_in_range_s2.iter())
            .map(|v| v.idx)
    };
    let vars = distinct_range_vars(extended.range());
    let indices = IndexRenaming::avoiding(&vars, occupied().max(), || occupied().collect());
    let s1 = extended.rename_range(&indices);
    let composed = s1.compose(s2);
    (free_to_fresh_raw(composed), indices)
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
    fn explicit_identity_binding_preserves_nonground_input_correlation() {
        use crate::function_symbols::AcSym;
        use crate::lterm::pub_term;
        use crate::subst::apply_vterm;
        use crate::term::f_app_ac;

        // Ordinary {x -> y+a} solves x=y+a. VFresh treats every stored
        // range variable as a witness, so y must have its own stored entry.
        // This is the boundary example proved in Lean's SpecAudit.lean.
        let x = lv("x", 0);
        // Equal numeric indices must still preserve the full identities.
        let y = lv("y", 0);
        let lhs = var_term(x);
        let rhs = f_app_ac(AcSym::Union, vec![var_term(y), pub_term("a")]);
        let naive = SubstVFresh::from_list([(x, rhs.clone())]);
        let closed = SubstVFresh::from_list([(x, rhs.clone()), (y, var_term(y))]);
        assert_eq!(closed.image_of(&y), Some(&var_term(y)));
        assert_eq!(closed.remove_renamings(), closed);

        for decoded in [
            naive.fresh_to_free_avoiding(|_| 20),
            naive.fresh_to_free_uniform_shift(20).unwrap(),
        ] {
            assert_ne!(
                apply_vterm(&decoded, lhs.clone()),
                apply_vterm(&decoded, rhs.clone())
            );
        }
        for decoded in [
            closed.fresh_to_free_avoiding(|_| 20),
            closed.fresh_to_free_uniform_shift(20).unwrap(),
        ] {
            assert_eq!(
                apply_vterm(&decoded, lhs.clone()),
                apply_vterm(&decoded, rhs.clone())
            );
            assert_ne!(decoded.image_of(&y), Some(&var_term(y)));
            // An unrelated caller variable is untouched.
            assert_eq!(
                apply_vterm(&decoded, var_term(lv("caller", 10))),
                var_term(lv("caller", 10))
            );
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
    fn checked_uniform_shift_preserves_distinct_slots_at_the_last_index() {
        let pair = |x, y| f_app_no_eq(pair_sym(), vec![var_term(x), var_term(y)]);
        let key = lv("k", 7);
        let x = lv("w", 0);
        let y = lv("w", 1);
        let s = LSubstVFresh::<C>::from_list([(key, pair(x, y)), (lv("k", 8), var_term(x))]);
        assert!(s.fresh_to_free_uniform_shift(u64::MAX).is_none());
        let exact = s.fresh_to_free_uniform_shift(u64::MAX - 1).unwrap();
        assert_eq!(
            exact.image_of(&key),
            Some(&pair(lv("w", u64::MAX - 1), lv("w", u64::MAX)))
        );
        let avoid = [lv("w", 0), lv("w", 2), lv("w", u64::MAX)];
        let sparse = s.fresh_to_free_avoiding_vars(&avoid);
        assert_eq!(sparse.image_of(&key), Some(&pair(lv("w", 1), lv("w", 3))));
        assert_eq!(sparse.image_of(&lv("k", 8)), Some(&var_term(lv("w", 1))));
        let ground = LSubstVFresh::<C>::empty();
        assert!(ground
            .fresh_to_free_uniform_shift(u64::MAX)
            .unwrap()
            .is_empty());
    }

    #[test]
    fn sparse_rebasing_preserves_variable_order_sharing_and_sort() {
        let indices = [0, 1, 2, u64::MAX - 2, u64::MAX - 1, u64::MAX];
        for source_mask in 1..64 {
            let vars: Vec<_> = indices
                .iter()
                .enumerate()
                .filter(|(i, _)| source_mask & (1 << i) != 0)
                .flat_map(|(_, idx)| {
                    [
                        lv("x", *idx),
                        lv("y", *idx),
                        LVar::new("x", LSort::Fresh, *idx),
                    ]
                })
                .collect();
            for avoid_mask in 0..64 {
                let occupied: BTreeSet<_> = indices
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| avoid_mask & (1 << i) != 0)
                    .map(|(_, i)| *i)
                    .collect();
                let rebase =
                    IndexRenaming::avoiding(&vars, occupied.last().copied(), || occupied.clone());
                for &v in &vars {
                    let new = rebase.rename(v);
                    assert_eq!((v.name, v.sort), (new.name, new.sort));
                    assert!(!occupied.contains(&new.idx));
                    for &w in &vars {
                        assert_eq!(v.cmp(&w), new.cmp(&rebase.rename(w)));
                    }
                }
            }
        }
    }

    #[test]
    fn both_composition_paths_avoid_occupied_indices_at_max() {
        let x = lv("w", 0);
        let y = lv("w", 1);
        let k = lv("k", u64::MAX);
        let pair = |x, y| f_app_no_eq(pair_sym(), vec![var_term(x), var_term(y)]);
        let s2 = crate::subst::Subst::<C, LVar>::from_list([(k, pair(x, y))]);
        let empty = LSubstVFresh::empty();
        let actual = compose_vfresh(&empty, &s2);
        assert_eq!(actual, compose_vfresh_general(&empty, &s2));
        assert_eq!(actual.image_of(&k), Some(&pair(lv("w", 2), lv("w", 3))));
        assert_eq!(actual.image_of(&x), Some(&var_term(lv("w", 2))));
        assert_eq!(actual.image_of(&y), Some(&var_term(lv("w", 3))));

        // Both extension and final freshening now encounter an occupied MAX.
        let original = LSubstVFresh::from_list([(lv("z", 2), var_term(lv("w", u64::MAX)))]);
        let actual = compose_vfresh(&original, &s2);
        assert_eq!(actual.image_of(&k), Some(&pair(lv("w", 3), lv("w", 4))));
        assert_eq!(actual.image_of(&lv("z", 2)), Some(&var_term(lv("w", 5))));
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
        let free = s.fresh_to_free_uniform_shift(10).unwrap();
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
        let free2 = konst.fresh_to_free_uniform_shift(10).unwrap();
        assert_eq!(
            free2.image_of(&lv("c", 0)),
            Some(&crate::vterm::const_term(name))
        );
    }

    #[test]
    fn compose_vfresh_general_avoid_set_reads_s1_domain_keys_not_its_range() {
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

        // This is the empty-`s1_0` shape that the closed form exists for.
        // Here it runs through the general pipeline.  The call
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
        assert_eq!(compose_vfresh_general(&empty, &s2), want);
        // The fast path that `compose_vfresh` dispatches to must give the same
        // value.  It must do so in every build, not only under
        // `debug_assertions`.
        assert_eq!(compose_vfresh(&empty, &s2), want);
    }
}
