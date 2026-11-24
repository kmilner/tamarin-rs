// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.EquationStore`.
//!
//! The equation store represents a (constrained) disjunction of
//! substitutions. Semantically:
//!
//! ```text
//! EqStore sigma_free
//!         [ [sigma_i1, ..., sigma_ik_i] | i ∈ 1..l ]
//! ```
//!
//! denotes
//!
//! ```text
//!     /\_i (x_i = sigma_free(x_i))
//!  /\ /\_i (sigma_i1 ∨ … ∨ sigma_ik_i)
//! ```
//!
//! where each `sigma_ij` is a *fresh-range* substitution (its
//! variables are existentially quantified).
//!
//! The Maude-backed operations are `add_eqs`, `apply_eq_store`, `simp` and
//! `simp_disjunction`.

use std::collections::BTreeSet;

use std::cmp::Ordering;

use tamarin_term::lterm::{sort_compare, HasFrees, LNTerm, LSort, LVar, Name};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::subst::Subst;
use tamarin_term::subst_vfresh::SubstVFresh;
use tamarin_term::term::Term;
use tamarin_term::vterm::{var_term, Lit};

/// Index of a disjunction in the equation store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SplitId(pub i64);

impl SplitId {
    pub fn succ(self) -> Self {
        SplitId(self.0 + 1)
    }
}

/// Convenient alias for the substitution type the solver uses on the
/// "free" (currently-fixed) part of the equation store.
pub type LNSubst = Subst<Name, LVar>;

/// Convenient alias for the fresh-range substitutions stored in
/// disjunctions.
pub type LNSubstVFresh = SubstVFresh<Name, LVar>;

/// The domain/range pairs of `s` with the mapping for `v` dropped,
/// in `to_list` order. Shared head of the `simp_abstract_*` /
/// `simp_identify` passes, which each rebuild a disjunct's substs
/// after removing the abstracted domain key and appending their own
/// pass-specific mappings.
fn without_key(s: &LNSubstVFresh, v: &LVar) -> Vec<(LVar, LNTerm)> {
    s.to_list().into_iter().filter(|(x, _)| x != v).collect()
}

/// One entry in the disjunctive part of the store: a `SplitId`
/// alongside the set of substitutions making up that disjunction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EqDisj {
    pub split_id: SplitId,
    pub substs: Vec<LNSubstVFresh>,
}

/// One element of HS's `_eqsConj :: Conj (SplitId, S.Set LNSubstVFresh)`
/// (EquationStore.hs), walked through the pair instance
/// (LTerm.hs).  The `SplitId` half contributes nothing and maps to
/// itself (EquationStore.hs); the substitutions follow in ascending
/// `Ord` order, which is the `S.toList` of the HS set (LTerm.hs); the
/// port stores the disjunction as an insertion-ordered `Vec`, so the walk
/// sorts a list of references to reach that order.  Each substitution then
/// exposes its domain keys alone (SubstVFresh.hs), which keeps the
/// witness indices of the ranges.
///
/// Arbitrary maps re-sort and deduplicate the result, matching HS's
/// `S.fromList` rebuild (LTerm.hs). Monotone maps preserve the existing
/// set order and cannot introduce duplicates.
impl HasFrees for EqDisj {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        let mut substs: Vec<&LNSubstVFresh> = self.substs.iter().collect();
        substs.sort();
        for s in substs {
            s.for_each_free(f);
        }
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        let mut substs = self.substs.map_free_with(f, monotone);
        if !monotone {
            substs.sort();
            substs.dedup();
        }
        EqDisj {
            split_id: self.split_id,
            substs,
        }
    }
}

/// `orderedSubsts = sortOnMemo dropNameHintsLNSubstVFresh . S.toList`
/// (EquationStore.hs): a disjunction's cases in canonical split
/// order, shared by `perform_split` and `pretty_system::pp_disj` (HS
/// `ppDisj`). The plain sort is `S.toList`; the stable re-sort by
/// `drop_name_hints` makes the order independent of witness indices.
pub(crate) fn ordered_substs(substs: &[LNSubstVFresh]) -> Vec<&LNSubstVFresh> {
    let mut out: Vec<&LNSubstVFresh> = substs.iter().collect();
    out.sort();
    out.sort_by_cached_key(|s| s.drop_name_hints());
    out
}

/// `EqStore`. Mirrors Haskell's `EqStore { _eqsSubst, _eqsConj,
/// _eqsNextSplitId }`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EquationStore {
    /// "Free" substitution — currently-fixed bindings of the global
    /// variables. Composes with everything else.
    pub subst: LNSubst,
    /// Conjunction of disjunctions.
    pub conj: Vec<EqDisj>,
    pub next_split: SplitId,
}

/// `instance HasFrees EqStore` (EquationStore.hs): the free
/// substitution, then the conjunction of disjunctions in list order
/// (LTerm.hs).  `next_split` is a `SplitId`, whose instance folds to
/// nothing and maps to itself (EquationStore.hs).
impl HasFrees for EquationStore {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.subst.for_each_free(f);
        self.conj.for_each_free(f);
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        EquationStore {
            subst: self.subst.map_free_with(f, monotone),
            conj: self.conj.map_free_with(f, monotone),
            next_split: self.next_split,
        }
    }
}

impl Default for EquationStore {
    fn default() -> Self {
        Self::empty()
    }
}

impl EquationStore {
    pub fn empty() -> Self {
        EquationStore {
            subst: LNSubst::empty(),
            conj: Vec::new(),
            next_split: SplitId(0),
        }
    }

    /// `True` iff the store is contradictory (i.e. contains an empty
    /// disjunction).
    pub fn is_false(&self) -> bool {
        self.conj.iter().any(|d| d.substs.is_empty())
    }

    /// The conjunction representing logical false (split id `-1` and
    /// an empty disjunction).
    pub fn false_conj() -> Vec<EqDisj> {
        vec![EqDisj {
            split_id: SplitId(-1),
            substs: Vec::new(),
        }]
    }

    /// Set the store to logical false. Returns the modified store.
    pub fn set_false(mut self) -> Self {
        self.conj = Self::false_conj();
        self
    }

    /// Add a new disjunction to the front of the conjunction. Returns
    /// the resulting store and the new split id.
    pub fn add_disj(&mut self, substs: Vec<LNSubstVFresh>) -> SplitId {
        let id = self.next_split;
        // HS stores the disjunction as a `Set`: sort and deduplicate.
        let mut substs = substs;
        substs.sort();
        substs.dedup();
        self.conj.insert(
            0,
            EqDisj {
                split_id: id,
                substs,
            },
        );
        self.next_split = id.succ();
        id
    }

    /// Sorted list of split-ids by disjunction size (ascending).
    /// Mirrors Haskell's `splits`.
    pub fn splits(&self) -> Vec<SplitId> {
        let mut indexed: Vec<(SplitId, usize)> = self
            .conj
            .iter()
            .map(|d| (d.split_id, d.substs.len()))
            .collect();
        indexed.sort_by_key(|(_, sz)| *sz);
        // HS's `nub` is a no-op: split ids in `conj` are unique.
        indexed.into_iter().map(|(id, _)| id).collect()
    }

    /// Number of cases for a given split id.
    pub fn split_size(&self, id: SplitId) -> Option<usize> {
        self.conj
            .iter()
            .find(|d| d.split_id == id)
            .map(|d| d.substs.len())
    }

    pub fn split_exists(&self, id: SplitId) -> bool {
        self.split_size(id).is_some()
    }

    /// `removePermutations` (EquationStore.hs, #883): inside the disjunction
    /// `split_id`, drop substitutions that are equal to a kept one up to a
    /// permutation of the images of `v1` and `v2` (modulo a renaming of msg
    /// vars).  Used when solving a KU goal against an AC-constructor rule,
    /// where the two premise variables are interchangeable.
    pub fn remove_permutations(
        mut self,
        maude: &tamarin_term::maude_proc::MaudeHandle,
        split_id: SplitId,
        v1: &LVar,
        v2: &LVar,
    ) -> Result<Self, AddEqsError> {
        // `filter (not . isPerm s)`, propagating a Maude failure.
        fn drop_perms_of(
            maude: &tamarin_term::maude_proc::MaudeHandle,
            lhs: &PermLhs<'_>,
            substs: Vec<LNSubstVFresh>,
        ) -> Result<Vec<LNSubstVFresh>, AddEqsError> {
            let mut out = Vec::with_capacity(substs.len());
            for x in substs {
                if !is_perm_subst(maude, lhs, &x)? {
                    out.push(x);
                }
            }
            Ok(out)
        }
        for disj in self.conj.iter_mut().filter(|d| d.split_id == split_id) {
            // HS walks `S.toList substs` (sorted) and rebuilds via
            // `S.fromList`; mirror with an explicit sort on both ends.
            let mut rest: Vec<LNSubstVFresh> = std::mem::take(&mut disj.substs);
            rest.sort();
            rest.dedup();
            // `removePerm r (s:rest) = removePerm (s : filter (not . isPerm s) r)
            //                                     (filter (not . isPerm s) rest)`
            let mut kept: Vec<LNSubstVFresh> = Vec::new();
            while !rest.is_empty() {
                let s = rest.remove(0);
                // Everything `isPerm s` derives from `s` alone is shared by
                // both passes and by every candidate they test.
                let lhs = PermLhs::new(v1, v2, &s);
                kept = drop_perms_of(maude, &lhs, kept)?;
                rest = drop_perms_of(maude, &lhs, rest)?;
                kept.push(s);
            }
            kept.sort();
            kept.dedup();
            disj.substs = kept;
        }
        Ok(self)
    }

    /// Perform a case-split on the given disjunction, returning one
    /// fresh `EquationStore` per case.
    ///
    /// Returns `None` if no disjunction with `id` exists.
    pub fn perform_split(&self, id: SplitId) -> Option<Vec<EquationStore>> {
        let pos = self.conj.iter().position(|d| d.split_id == id)?;
        let disj = &self.conj[pos];
        // `mkNewEqStore before after <$> orderedSubsts disj`
        let sorted_substs = ordered_substs(&disj.substs);
        let mut out = Vec::with_capacity(sorted_substs.len());
        for subst in sorted_substs {
            let mut new_store = self.clone();
            new_store.conj.remove(pos);
            new_store.add_disj(vec![subst.clone()]);
            out.push(new_store);
        }
        Some(out)
    }

    /// `addEqs` (EquationStore.hs): unify `eqs` under the free substitution
    /// and record the result. Returns the split id of the new disjunction
    /// when the unifier is not unique.
    pub fn add_eqs(
        &mut self,
        maude: &tamarin_term::maude_proc::MaudeHandle,
        eqs: &[tamarin_term::rewriting::Equal<LNTerm>],
    ) -> Result<Option<SplitId>, AddEqsError> {
        use tamarin_term::rewriting::Equal;
        use tamarin_term::subst::apply_vterm;
        let eqs: Vec<Equal<LNTerm>> = eqs
            .iter()
            .map(|e| Equal {
                lhs: apply_vterm(&self.subst, e.lhs.clone()),
                rhs: apply_vterm(&self.subst, e.rhs.clone()),
            })
            .collect();
        // `unifyLNTermFactored` (Unification.hs): the free part comes from
        // the local unifier, and only the AC residuals go to Maude.
        let Some((subst, residuals)) = tamarin_term::unification::unify_lnterm_factored(eqs) else {
            self.conj = Self::false_conj();
            return Ok(None);
        };
        let unifiers = if residuals.is_empty() {
            vec![Vec::new()]
        } else {
            maude
                .unify(&residuals)
                .map_err(|e| AddEqsError::Maude(format!("{}", e)))?
        };
        match unifiers.as_slice() {
            [] => {
                self.conj = Self::false_conj();
                Ok(None)
            }
            [u] if u.is_empty() => {
                self.apply_eq_store(maude, &subst)?;
                Ok(None)
            }
            _ => {
                self.apply_eq_store(maude, &subst)?;
                let substs = unifiers.into_iter().map(LNSubstVFresh::from_list).collect();
                Ok(Some(self.add_disj(substs)))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum AddEqsError {
    Maude(String),
}

impl std::fmt::Display for AddEqsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddEqsError::Maude(s) => write!(f, "Maude error: {}", s),
        }
    }
}
impl std::error::Error for AddEqsError {}

fn subst_domain_range_overlap(asubst: &LNSubst) -> bool {
    let mut dom_range_overlap = false;
    {
        use tamarin_term::lterm::HasFrees;
        for t in asubst.range() {
            t.for_each_free(&mut |v| {
                if !dom_range_overlap && asubst.image_of(v).is_some() {
                    dom_range_overlap = true;
                }
            });
            if dom_range_overlap {
                break;
            }
        }
    }
    dom_range_overlap
}

// =============================================================================
// Rule variants
// =============================================================================

impl EquationStore {
    /// `addRuleVariants disj store` — extends the store's conjunction
    /// with the given precomputed AC variants (a disjunction of
    /// fresh-range substitutions). Mirrors Haskell's `addRuleVariants`.
    /// Errors if the variants share variables with the free
    /// substitution's domain (Haskell `error`'s here).
    pub fn add_rule_variants(
        &mut self,
        variants: Vec<LNSubstVFresh>,
    ) -> Result<SplitId, &'static str> {
        // Domain-disjointness check: free-subst domain must not
        // overlap with any variant's domain.
        let free_dom: BTreeSet<LVar> = self.subst.dom().copied().collect();
        for v in &variants {
            if v.dom().any(|x| free_dom.contains(x)) {
                return Err("addRuleVariants: nonempty intersection between domain \
                     of variants and free substitution");
            }
        }
        Ok(self.add_disj(variants))
    }
}

// =============================================================================
// Simplification
// =============================================================================

/// The result of one `foreachDisj` pass on a disjunction: the factor to
/// apply to the store, and the disjunction to put in its place (`None`
/// drops it).
type DisjStep = Option<(LNSubst, Option<Vec<LNSubstVFresh>>)>;

impl EquationStore {
    /// Restore HS's `Set` invariant on every disjunction: sorted, no
    /// duplicates.
    pub fn sort_disj_substs(&mut self) {
        for d in self.conj.iter_mut() {
            d.substs.sort();
            d.substs.dedup();
        }
    }

    /// `simpEmptyDisj`: if any disjunction is empty (and the store
    /// isn't already the canonical false-conjunction), collapse the
    /// whole store to `false`.
    pub fn simp_empty_disj(&mut self) -> bool {
        let already_false_canonical = self.conj.len() == 1
            && self.conj[0].split_id == SplitId(-1)
            && self.conj[0].substs.is_empty();
        let has_empty_disj = self.conj.iter().any(|d| d.substs.is_empty());
        if has_empty_disj && !already_false_canonical {
            self.conj = Self::false_conj();
            true
        } else {
            false
        }
    }

    /// `simpRemoveRenamings`: drop variable-renaming entries from
    /// every fresh-range substitution. Returns true if any subst was
    /// modified.
    pub fn simp_remove_renamings(&mut self) -> bool {
        let mut changed = false;
        for d in self.conj.iter_mut() {
            for s in d.substs.iter_mut() {
                // `remove_renamings` drops exactly the entries `v` for which
                // `is_renamed_var(v)` holds, so the domain count changes iff at
                // least one such entry exists.  Gate the allocation on that
                // cheap pre-check (the common case has no renamings).
                if s.dom().any(|v| s.is_renamed_var(v)) {
                    *s = s.remove_renamings();
                    changed = true;
                }
            }
        }
        changed
    }

    /// `simpMinimize`: dedupe substitutions within a disjunction; if a
    /// disjunction contains the empty subst (i.e. a tautology), reduce
    /// it to just that. Also drops substs flagged contradictory by
    /// `is_contr`.
    pub fn simp_minimize<F: Fn(&LNSubstVFresh) -> bool>(&mut self, is_contr: F) -> bool {
        let mut changed = false;
        let empty = LNSubstVFresh::empty();
        for d in self.conj.iter_mut() {
            // Fast path: a strictly ascending disjunction (as `simp` keeps
            // them) has no duplicate; leave it alone unless it holds the
            // empty or a contradictory substitution.
            let sorted = d.substs.windows(2).all(|w| w[0] < w[1]);
            let needs_special = d.substs.iter().any(|s| s == &empty || is_contr(s));
            if sorted && !needs_special {
                continue;
            }
            // Dedup while preserving first occurrences, by reference: nothing
            // is cloned unless the disj changes.
            let mut seen: Vec<&LNSubstVFresh> = if sorted {
                d.substs.iter().collect()
            } else {
                let mut distinct: BTreeSet<&LNSubstVFresh> = BTreeSet::new();
                // `insert` returns `false` if the element was already present.
                d.substs.iter().filter(|s| distinct.insert(*s)).collect()
            };
            // `minimize`: the empty substitution subsumes the rest;
            // otherwise drop the contradictory ones.
            if needs_special {
                if seen.iter().any(|s| **s == empty) {
                    seen = vec![&empty];
                } else {
                    seen.retain(|s| !is_contr(s));
                }
            }
            // `seen` keeps the order of `d.substs` (and `[empty]` has length
            // 1 only if `d.substs` was already `[empty]`), so an unchanged
            // length means an unchanged disj.
            if seen.len() != d.substs.len() {
                d.substs = seen.into_iter().cloned().collect();
                changed = true;
            }
        }
        changed
    }

    /// `simp` (EquationStore.hs): run the `simp1` passes to a fixpoint.
    /// `is_contr` is `simpMinimize`'s contradiction predicate, given the free
    /// substitution as it stood at the start of the round.
    pub fn simp<F: Fn(&LNSubst, &LNSubstVFresh) -> bool>(
        mut self,
        maude: &MaudeHandle,
        is_contr: F,
    ) -> Result<Self, AddEqsError> {
        // `foreachDisj` passes look at the first substitution of a
        // disjunction in `Set` order, so keep every disjunction sorted.
        self.sort_disj_substs();
        let passes: [fn(&MaudeHandle, &LNSubst, &[LNSubstVFresh]) -> DisjStep; 5] = [
            simp_singleton,
            simp_abstract_sorted_var,
            simp_identify,
            simp_abstract_fun,
            simp_abstract_name,
        ];
        loop {
            if self.is_false() {
                return Ok(self);
            }
            let mut changed = false;
            let subst_snapshot = self.subst.clone();
            if self.simp_minimize(|s| is_contr(&subst_snapshot, s)) {
                changed = true;
                self.sort_disj_substs();
            }
            if self.simp_remove_renamings() {
                changed = true;
                self.sort_disj_substs();
            }
            changed |= self.simp_empty_disj();
            for pass in passes {
                if self.foreach_disj(maude, pass)? {
                    changed = true;
                    self.sort_disj_substs();
                }
            }
            if !changed {
                return Ok(self);
            }
        }
    }

    /// `foreachDisj` (EquationStore.hs): run `pass` on each disjunction
    /// in turn until it fires, then replace that disjunction and apply the
    /// factor to the store.
    fn foreach_disj(
        &mut self,
        maude: &MaudeHandle,
        pass: fn(&MaudeHandle, &LNSubst, &[LNSubstVFresh]) -> DisjStep,
    ) -> Result<bool, AddEqsError> {
        for idx in 0..self.conj.len() {
            let Some((factor, replacement)) = pass(maude, &self.subst, &self.conj[idx].substs)
            else {
                continue;
            };
            match replacement {
                Some(substs) => self.conj[idx].substs = substs,
                None => {
                    self.conj.remove(idx);
                }
            }
            self.apply_factor_or_compose(&factor, maude)?;
            return Ok(true);
        }
        Ok(false)
    }

    /// Compose `factor` into the free substitution, re-unifying remaining
    /// disjs via `apply_eq_store` when its domain/range precondition holds.
    /// Otherwise compose directly.
    fn apply_factor_or_compose(
        &mut self,
        factor: &LNSubst,
        maude: &MaudeHandle,
    ) -> Result<(), AddEqsError> {
        if subst_domain_range_overlap(factor) {
            self.subst = factor.compose(&self.subst);
            Ok(())
        } else {
            self.apply_eq_store(maude, factor)
        }
    }

    /// `simpDisjunction` (EquationStore.hs): simplify a lone disjunction,
    /// returning the factored free substitution and the residual
    /// disjunction (`None` when it simplified away).
    pub fn simp_disjunction<F: Fn(&LNSubst, &LNSubstVFresh) -> bool>(
        maude: &MaudeHandle,
        is_contr: F,
        substs: Vec<LNSubstVFresh>,
    ) -> Result<(LNSubst, Option<Vec<LNSubstVFresh>>), AddEqsError> {
        let mut store = EquationStore::empty();
        store.add_disj(substs);
        let store = store.simp(maude, is_contr)?;
        let EquationStore { subst, conj, .. } = store;
        Ok(match <[EqDisj; 1]>::try_from(conj) {
            Ok([d]) => (subst, Some(d.substs)),
            Err(conj) if conj.is_empty() => (subst, None),
            Err(conj) => panic!(
                "simplifyDisjunction: imposible, unexpected conjunction `{:?}'",
                conj
            ),
        })
    }

    /// `applyEqStore` (EquationStore.hs): compose `asubst` into the free
    /// substitution, then re-unify every disjunction substitution against the
    /// new free substitution (`applyBound`). A substitution may split into
    /// several or vanish. Errors if `asubst`'s domain and range overlap, as
    /// Haskell does.
    pub fn apply_eq_store(
        &mut self,
        maude: &MaudeHandle,
        asubst: &LNSubst,
    ) -> Result<(), AddEqsError> {
        use tamarin_term::rewriting::Equal;
        use tamarin_term::subst::apply_vterm;
        if subst_domain_range_overlap(asubst) {
            return Err(AddEqsError::Maude(
                "applyEqStore: dom and vrange not disjoint".into(),
            ));
        }
        let new_subst = asubst.compose(&self.subst);
        // `varsRange newsubst`, the shared half of every `restrictVFresh` and
        // avoidance set below.
        let mut range_vars: tamarin_utils::FastSet<LVar> = Default::default();
        let mut range_max: u64 = 0;
        for t in new_subst.range() {
            t.for_each_free(&mut |v| {
                range_max = range_max.max(v.idx);
                range_vars.insert(*v);
            });
        }
        let mut new_conj: Vec<EqDisj> = Vec::with_capacity(self.conj.len());
        for d in &self.conj {
            let mut new_substs: Vec<LNSubstVFresh> = Vec::new();
            for s in &d.substs {
                if s.is_empty() {
                    new_substs.push(s.clone());
                    continue;
                }
                let dom: tamarin_utils::FastSet<LVar> = s.dom().copied().collect();
                // `renameAvoiding (map snd slist) (domVFresh s ++ varsRange
                // newsubst)`: one uniform shift of the whole range list.
                let avoid_max = dom.iter().map(|v| v.idx).fold(range_max, u64::max);
                let mut fresh = tamarin_utils::fresh::FastFreshState::seeded(avoid_max + 1);
                let ran =
                    tamarin_term::lterm::rename(s.range().cloned().collect::<Vec<_>>(), &mut fresh);
                let eqs: Vec<Equal<LNTerm>> = s
                    .dom()
                    .zip(ran)
                    .map(|(lv, t)| Equal {
                        lhs: apply_vterm(&new_subst, var_term(*lv)),
                        rhs: t,
                    })
                    .collect();
                // Each variant unifies on its own counter seeded at the same
                // avoidance set, as HS's `evalFreshAvoiding`; the session
                // counter is left alone.
                let unifiers = maude
                    .with_fresh_counter_from(avoid_max)
                    .unify(&eqs)
                    .map_err(|e| AddEqsError::Maude(format!("{}", e)))?;
                // `restrictVFresh (varsRange newsubst ++ domVFresh s)`. The
                // range terms are kept as Maude returns them, unnormalised.
                new_substs.extend(unifiers.into_iter().map(|u| {
                    LNSubstVFresh::from_list(
                        u.into_iter()
                            .filter(|(v, _)| range_vars.contains(v) || dom.contains(v)),
                    )
                }));
            }
            // `S.fromList`: a structural set, never deduplicated modulo
            // alpha-renaming of the witnesses.
            new_substs.sort();
            new_substs.dedup();
            new_conj.push(EqDisj {
                split_id: d.split_id,
                substs: new_substs,
            });
        }
        self.conj = new_conj;
        self.subst = new_subst;
        Ok(())
    }
}

/// `simpSingleton` (EquationStore.hs): fold a singleton disjunction into the
/// free substitution via `freshToFree`.
fn simp_singleton(maude: &MaudeHandle, free: &LNSubst, substs: &[LNSubstVFresh]) -> DisjStep {
    let [s] = substs else {
        return None;
    };
    if s.is_empty() {
        return Some((LNSubst::empty(), None));
    }
    // Rust-only floor: HS draws `freshToFree`'s variables from the
    // `runReduction` counter, which is always above the free
    // substitution's range (earlier folds drew those), while this counter is
    // re-seeded from `avoid sys`, which counts only VFresh domain keys. Raise
    // it above the free range so a fold cannot reuse an earlier fold's
    // variable. Do not floor above the sibling disjunctions' witnesses: HS's
    // counter is not above those either, and `applyEqStore` renames them
    // apart.
    let mut floor = 0u64;
    for t in free.range() {
        t.for_each_free(&mut |w: &LVar| floor = floor.max(w.idx));
    }
    if floor > 0 {
        maude.ensure_above(floor);
    }
    Some((s.fresh_to_free_avoiding(|n| maude.reserve_idxs(n)), None))
}

/// `simpAbstractSortedVar` (EquationStore.hs): if every substitution maps
/// `v` to a variable of the same sort `s`, strictly below `v`'s sort, factor
/// out `{v -> y}` for a fresh `y` of sort `s`.
fn simp_abstract_sorted_var(
    maude: &MaudeHandle,
    _free: &LNSubst,
    substs: &[LNSubstVFresh],
) -> DisjStep {
    let (first, others) = substs.split_first()?;
    let (v, lvs) = first.iter().find_map(|(v, t)| {
        let Term::Lit(Lit::Var(lx)) = t else {
            return None;
        };
        if sort_compare(v.sort, lx.sort) != Some(Ordering::Greater) {
            return None;
        }
        let mut lvs = vec![*lx];
        for other in others {
            match other.image_of(v) {
                Some(Term::Lit(Lit::Var(ly))) if ly.sort == lx.sort => lvs.push(*ly),
                _ => return None,
            }
        }
        Some((*v, lvs))
    })?;
    let fv = LVar {
        name: v.name,
        sort: lvs[0].sort,
        idx: maude.reserve_idxs(1),
    };
    let substs = substs
        .iter()
        .zip(&lvs)
        .map(|(s, lv)| {
            let mut kept = without_key(s, &v);
            kept.push((fv, var_term(*lv)));
            LNSubstVFresh::from_list(kept)
        })
        .collect();
    Some((LNSubst::from_list(vec![(v, var_term(fv))]), Some(substs)))
}

/// `simpIdentify` (EquationStore.hs): if every substitution maps `v` and
/// `v'` to the same term, factor out `{vremove -> vkeep}`, keeping the
/// variable of the smaller sort.
fn simp_identify(_maude: &MaudeHandle, _free: &LNSubst, substs: &[LNSubstVFresh]) -> DisjStep {
    let (first, others) = substs.split_first()?;
    let entries: Vec<(&LVar, &LNTerm)> = first.iter().collect();
    let (v, v2) = entries
        .iter()
        .enumerate()
        .flat_map(|(i, (v, t))| {
            entries[i + 1..]
                .iter()
                .filter(move |(v2, t2)| t == t2 && v < v2)
                .map(move |(v2, _)| (**v, **v2))
        })
        .find(|(v, v2)| {
            others.iter().all(|s| {
                let i1 = s.image_of(v);
                i1.is_some() && i1 == s.image_of(v2)
            })
        })?;
    let (keep, remove) = match sort_compare(v.sort, v2.sort) {
        Some(Ordering::Greater) => (v2, v),
        Some(_) => (v, v2),
        None => panic!(
            "EquationStore.simpIdentify: impossible, variables with incomparable sorts: {:?} and {:?}",
            v, v2
        ),
    };
    let substs = substs
        .iter()
        .map(|s| LNSubstVFresh::from_list(without_key(s, &keep)))
        .collect();
    Some((
        LNSubst::from_list(vec![(remove, var_term(keep))]),
        Some(substs),
    ))
}

/// `simpAbstractFun` (EquationStore.hs): if every substitution maps `v` to
/// an application of the same symbol `o`, factor out `{v -> o(x1, .., xk)}`
/// for fresh `xi`. An AC symbol applied at differing arities is split into
/// its first argument and the rest.
fn simp_abstract_fun(maude: &MaudeHandle, _free: &LNSubst, substs: &[LNSubstVFresh]) -> DisjStep {
    let (first, others) = substs.split_first()?;
    let (v, op, argss) = first.iter().find_map(|(v, t)| {
        let Term::App(op, args) = t else {
            return None;
        };
        let mut argss = vec![args.to_vec()];
        for other in others {
            match other.image_of(v) {
                Some(Term::App(o2, a2)) if o2 == op => argss.push(a2.to_vec()),
                _ => return None,
            }
        }
        Some((*v, *op, argss))
    })?;
    let fresh_x = || LVar {
        name: "x",
        sort: LSort::Msg,
        idx: maude.reserve_idxs(1),
    };
    let arity = argss[0].len();
    let (fvars, mappings): (Vec<LVar>, Vec<Vec<LNTerm>>) =
        if !op.is_ac() || argss.iter().all(|a| a.len() == arity) {
            ((0..arity).map(|_| fresh_x()).collect(), argss)
        } else {
            let fvars = vec![fresh_x(), fresh_x()];
            let mappings = argss
                .into_iter()
                .map(|args| match args.as_slice() {
                    [] => panic!("simpAbstract: impossible, AC symbols must have arity >= 2."),
                    [a1, a2] => vec![a1.clone(), a2.clone()],
                    // HS abstracts left to right, without using AC.
                    [a1, rest @ ..] => vec![a1.clone(), Term::App(op, rest.to_vec().into())],
                })
                .collect();
            (fvars, mappings)
        };
    let substs = substs
        .iter()
        .zip(&mappings)
        .map(|(s, args)| {
            let mut kept = without_key(s, &v);
            kept.extend(fvars.iter().copied().zip(args.iter().cloned()));
            LNSubstVFresh::from_list(kept)
        })
        .collect();
    let factor = Term::App(op, fvars.iter().map(|fv| var_term(*fv)).collect());
    Some((LNSubst::from_list(vec![(v, factor)]), Some(substs)))
}

/// `simpAbstractName` (EquationStore.hs): if every substitution maps `v` to
/// the same name, factor out `{v -> n}`.
fn simp_abstract_name(_maude: &MaudeHandle, _free: &LNSubst, substs: &[LNSubstVFresh]) -> DisjStep {
    let (v, n) = substs.first()?.iter().find(|(v, t)| {
        matches!(t, Term::Lit(Lit::Con(_))) && substs.iter().all(|s| s.image_of(v) == Some(*t))
    })?;
    let substs = substs
        .iter()
        .map(|s| LNSubstVFresh::from_list(without_key(s, v)))
        .collect();
    Some((LNSubst::from_list(vec![(*v, n.clone())]), Some(substs)))
}

/// `isPerm` (inside `removePermutations`, EquationStore.hs): `s2` is a
/// permutation of `s1` — either literally with the images of `v1`/`v2`
/// swapped and every other binding shared, or equal up to a renaming of
/// msg variables (with and without the swap).  Everything that depends on
/// `s1` alone comes from `lhs`.
fn is_perm_subst(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    lhs: &PermLhs<'_>,
    s2: &LNSubstVFresh,
) -> Result<bool, AddEqsError> {
    let (v1, v2, s1) = (lhs.v1, lhs.v2, lhs.s1);
    if s1.len() != s2.len() {
        return Ok(false);
    }
    // Swapped-images branch: every binding outside {v1,v2} shared, and
    // the v1/v2 images exchanged.  HS binds the four images lazily behind
    // `&&`, so `t12`/`t21` are demanded only once `t11 == t22` holds — and
    // none of them are demanded when a binding is unshared.
    //
    // `others_shared` also holds when neither `v1` nor `v2` is in the domain,
    // and the panics below then abort the prover — faithful, since HS's
    // `fromMaybe (error ...)` images are demanded under the same condition
    // (EquationStore.hs).
    let others_shared = s1
        .iter()
        .all(|(x, t)| x == v1 || x == v2 || s2.image_of(x).is_some_and(|u| u == t));
    if others_shared {
        let t11 = s1
            .image_of(v1)
            .unwrap_or_else(|| panic!("Missing image for v1: {:?} in subst1: {:?}", v1, s1));
        let t22 = s2
            .image_of(v2)
            .unwrap_or_else(|| panic!("Missing image for v2: {:?} in subst2: {:?}", v2, s2));
        if t11 == t22 {
            let t12 = s1
                .image_of(v2)
                .unwrap_or_else(|| panic!("Missing image for v2: {:?} in subst1: {:?}", v2, s1));
            let t21 = s2
                .image_of(v1)
                .unwrap_or_else(|| panic!("Missing image for v1: {:?} in subst2: {:?}", v1, s2));
            if t12 == t21 {
                return Ok(true);
            }
        }
    }
    let renamed2 = lhs.rename_images(s2);
    Ok(
        equal_subst_up_to_renaming(maude, &lhs.subst1_permuted, &renamed2)?
            || equal_subst_up_to_renaming(maude, &lhs.subst1_fixed, &renamed2)?,
    )
}

/// The `s1`-only half of `equalUpToRenaming` (inside `removePermutations`,
/// EquationStore.hs): the two `filter (not . isPerm s)` passes of one
/// `removePerm` step share it across every candidate they test.
struct PermLhs<'a> {
    v1: &'a LVar,
    v2: &'a LVar,
    s1: &'a LNSubstVFresh,
    /// `subst1''`.
    subst1_fixed: Vec<(LVar, LNTerm)>,
    /// `subst1''` under `permute`.
    subst1_permuted: Vec<(LVar, LNTerm)>,
    /// `([v1,v2],subst1'')`, the avoidance context of the renaming.
    avoid_ctx: LNTerm,
}

impl<'a> PermLhs<'a> {
    /// Fix `s1`'s non-msg range variables, build the `permute`d variant, and
    /// pack the avoidance context.
    ///
    /// HS's `substFixing` covers the ranges of BOTH substitutions at once;
    /// splitting it per substitution leaves every image unchanged, because
    /// the constant is a function of the variable alone and `apply_vterm`
    /// consults bindings only for the variables a term contains.
    fn new(v1: &'a LVar, v2: &'a LVar, s1: &'a LNSubstVFresh) -> Self {
        use tamarin_term::subst::apply_vterm;
        use tamarin_term::term::f_app_list;
        use tamarin_term::vterm::var_term;

        let fixing = subst_fixing(s1.range());
        let subst1_fixed: Vec<(LVar, LNTerm)> = s1
            .to_list()
            .into_iter()
            .map(|(v, t)| (v, apply_vterm(&fixing, t)))
            .collect();

        // `permute`: swap the v1/v2 DOMAIN keys.  `substFixing` rewrites
        // images only, so applying it before the swap gives the same
        // key-to-image association as HS's swap-then-fix order.
        let subst1_permuted: Vec<(LVar, LNTerm)> =
            LNSubstVFresh::from_list(subst1_fixed.iter().map(|(v, t)| {
                let key = if v == v1 {
                    *v2
                } else if v == v2 {
                    *v1
                } else {
                    *v
                };
                (key, t.clone())
            }))
            .to_list();

        // `renameAvoidingIgnoring`'s avoidance context `([v1,v2],subst1'')`
        // is built from the UNPERMUTED `s1`, which yields the same renaming
        // as the permuted one: `avoid` reads only the largest variable index
        // of the context, `permute` is a bijection on the domain keys that
        // leaves the images untouched, and both `v1` and `v2` are in the
        // context either way.
        let avoid_ctx: LNTerm = f_app_list(
            [var_term(*v1), var_term(*v2)]
                .into_iter()
                .chain(subst1_fixed.iter().map(|(v, _)| var_term(*v)))
                .chain(subst1_fixed.iter().map(|(_, t)| t.clone()))
                .collect(),
        );

        PermLhs {
            v1,
            v2,
            s1,
            subst1_fixed,
            subst1_permuted,
            avoid_ctx,
        }
    }

    /// `renameAvoidingIgnoring (map snd subst2''') ([v1,v2],subst1'')
    ///  (map fst subst2''')` = `map snd subst2''`: fix `s2`'s non-msg range
    /// variables, then rename its image terms — coherently, keeping the
    /// domain keys — avoiding everything in `([v1,v2], subst1'')`.  Terms are
    /// packed into an `fAppList` so one shift renames all images
    /// consistently.
    fn rename_images(&self, s2: &LNSubstVFresh) -> Vec<LNTerm> {
        use tamarin_term::lterm::rename_avoiding_ignoring;
        use tamarin_term::subst::apply_vterm;
        use tamarin_term::term::{f_app_list, Term};

        let fixing = subst_fixing(s2.range());
        let keys2: Vec<LVar> = s2.dom().copied().collect();
        let packed2: LNTerm = f_app_list(
            s2.range()
                .map(|t| apply_vterm(&fixing, t.clone()))
                .collect(),
        );
        match rename_avoiding_ignoring(packed2, &self.avoid_ctx, &keys2) {
            Term::App(tamarin_term::function_symbols::FunSym::List, args) => args.to_vec(),
            other => vec![other],
        }
    }
}

/// `substFixing` for one substitution's range: every non-msg variable
/// occurring in `images` is fixed to a distinctive constant, so the matcher
/// cannot absorb it into a renaming.
fn subst_fixing<'a>(images: impl Iterator<Item = &'a LNTerm>) -> LNSubst {
    use tamarin_term::lterm::{frees, LSort, Name, NameTag};
    use tamarin_term::vterm::const_term;

    let constant = |v: &LVar| -> LNTerm {
        let sort_show = match v.sort {
            LSort::Pub => "LSortPub",
            LSort::Fresh => "LSortFresh",
            LSort::Msg => "LSortMsg",
            LSort::Node => "LSortNode",
            LSort::Nat => "LSortNat",
        };
        let tag = if v.sort == LSort::Fresh {
            NameTag::Fresh
        } else {
            NameTag::Pub
        };
        const_term(Name::new(
            tag,
            format!("constVar_{}_{}_{}", sort_show, v.idx, v.name),
        ))
    };
    Subst::from_list(
        images
            .flat_map(frees)
            .filter(|v| v.sort != LSort::Msg)
            .map(|v| (v, constant(&v))),
    )
}

/// `equalUpToRenaming` (inside `removePermutations`, EquationStore.hs):
/// after fixing all non-msg range variables of both substitutions to
/// per-variable constants and renaming `s2`'s images avoiding `s1`'s,
/// `renamed2` matches the given `subst1''` — plain or `permute`d — as one
/// joint AC matching problem with a nonempty matcher set.
fn equal_subst_up_to_renaming(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    subst1_fixed: &[(LVar, LNTerm)],
    renamed2: &[LNTerm],
) -> Result<bool, AddEqsError> {
    use tamarin_term::rewriting::Equal;
    use tamarin_term::vterm::is_ground_vterm;

    // A ground pattern binds nothing, so the joint problem is unsolvable as
    // soon as one of them differs from its subject: `match` works modulo the
    // module's AC/C axioms alone, and RS keeps AC/C terms flattened+sorted at
    // construction, so that is structural `==` — the same argument
    // `match_eqs`' all-ground short-circuit rests on.  `substFixing` freezes
    // every non-msg range variable to an index-bearing constant, which leaves
    // most candidate pairs differing in a ground position.
    if subst1_fixed
        .iter()
        .zip(renamed2)
        .any(|((_, t1), t2)| is_ground_vterm(t2) && t1 != t2)
    {
        return Ok(false);
    }

    // `matchers = solveMatchLNTerm (mconcat matchs)`: one joint matching
    // problem, term = s1 image, pattern = renamed s2 image.
    let eqs: Vec<Equal<LNTerm>> = subst1_fixed
        .iter()
        .zip(renamed2)
        .map(|((_, t1), t2)| Equal {
            lhs: t1.clone(),
            rhs: t2.clone(),
        })
        .collect();
    maude
        .match_eqs(&eqs)
        .map(|sols| !sols.is_empty())
        .map_err(|e| AddEqsError::Maude(format!("remove_permutations: {}", e)))
}

#[cfg(test)]
#[path = "equation_store_tests.rs"]
mod tests;
