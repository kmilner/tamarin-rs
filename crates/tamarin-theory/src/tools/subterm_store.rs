// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.SubtermStore`.
//!
//! The subterm store accumulates `t1 << t2` constraints during proof
//! search, propagating them and detecting contradictions. This module
//! holds the store data type plus the pieces the solver calls directly:
//! constraint accumulation (`add`/`add_neg`), `conjoin` (HS
//! `conjoinSubtermStores`), the subterm-cycle check `has_subterm_cycle`
//! (HS `hasSubtermCycle`, the CR-rule S_chain test), and the
//! `elem_not_below_reducible` predicate (HS `Term.elemNotBelowReducible`),
//! the `isTrueFalse` classifier and the `splitSubterm` decomposition both
//! solver passes drive.  The simplification passes that depend on
//! AC-unification — `simpSubtermStore` and `simpSplitNegSt` — are ported in
//! `constraint::solver::simplify` rather than here.

use tamarin_term::apply::Apply;
use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::{HasFrees, LNTerm, LVar};
use tamarin_term::term::Term;
use tamarin_utils::cow::cow_pair;
use tamarin_utils::FastSet;

use crate::apply::SystemSubst;

/// One stored subterm constraint: `small ⊏ big`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubtermConstraint {
    pub small: LNTerm,
    pub big: LNTerm,
    /// Whether this constraint has already been propagated.
    pub propagated: bool,
}

impl SubtermConstraint {
    /// The pair HS stores in `_posSubterms` / `_solvedSubterms`
    /// (`S.Set (LNTerm, LNTerm)`, SubtermStore.hs).  `propagated` is
    /// port-only and outside it, so every comparison that has to be as fine
    /// as HS's — and no finer — goes through this pair.
    pub fn hs_pair(&self) -> (&LNTerm, &LNTerm) {
        (&self.small, &self.big)
    }
}

/// HS reaches a stored constraint through `Apply LNSubst SubtermStore`
/// (SubtermStore.hs) and the pair instance (SubstVFree.hs):
/// the small side then the big one.  `propagated` is not part of the HS value
/// and is carried over unchanged.
impl Apply<SystemSubst<'_>> for SubtermConstraint {
    fn apply_changed(&self, subst: &SystemSubst<'_>) -> Option<Self> {
        cow_pair(
            &self.small,
            self.small.apply_changed(subst),
            &self.big,
            self.big.apply_changed(subst),
        )
        .map(|(small, big)| SubtermConstraint {
            small,
            big,
            propagated: self.propagated,
        })
    }
}

/// One element of the `_posSubterms` / `_solvedSubterms` sets, which HS holds
/// as `S.Set (LNTerm, LNTerm)` (SubtermStore.hs), so the walk is the
/// pair instance (LTerm.hs): the small side then the big one.
/// `propagated` is not part of the HS value and is carried over unchanged.
impl HasFrees for SubtermConstraint {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.small.for_each_free(f);
        self.big.for_each_free(f);
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        SubtermConstraint {
            small: self.small.map_free_with(f, monotone),
            big: self.big.map_free_with(f, monotone),
            propagated: self.propagated,
        }
    }
}

/// An always-sorted, deduplicated set of `(LNTerm, LNTerm)` pairs, standing in
/// for a Haskell `S.Set (LNTerm, LNTerm)`.  Membership and the
/// `neg_subterms \ old_neg_subterms` change-detection `binary_search` it, which
/// is only correct while it stays sorted, so the backing `Vec` is private and
/// there is no `push` / `&mut Vec` / `iter_mut` accessor.  Every mutator
/// (`insert`, `remove_at`, `rebuild_from`) re-establishes the sorted-unique
/// invariant, making an unsorted state unconstructible; reads go through the
/// slice `Deref`.  The sorted-unique invariant is what makes the derived,
/// position-sensitive `PartialEq`/`Ord` agree with HS's `S.Set` equality and
/// order on the same pairs.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SortedPairSet {
    inner: Vec<(LNTerm, LNTerm)>,
}

impl SortedPairSet {
    /// Collect any iterator into the set, establishing the sorted-unique
    /// invariant (sort + dedup); the resulting set is independent of input
    /// order.
    pub fn rebuild_from<I: IntoIterator<Item = (LNTerm, LNTerm)>>(iter: I) -> Self {
        let mut inner: Vec<(LNTerm, LNTerm)> = iter.into_iter().collect();
        inner.sort();
        inner.dedup();
        SortedPairSet { inner }
    }

    /// Insert `pair` at its sorted position; returns true iff it was newly
    /// added (already-present pairs leave the set unchanged).
    pub fn insert(&mut self, pair: (LNTerm, LNTerm)) -> bool {
        match self.inner.binary_search(&pair) {
            Ok(_) => false,
            Err(pos) => {
                self.inner.insert(pos, pair);
                true
            }
        }
    }

    /// Remove the element at `pos` (a position obtained from a `binary_search`
    /// on this set); removing at a sorted position keeps the remaining elements
    /// sorted.
    pub fn remove_at(&mut self, pos: usize) -> (LNTerm, LNTerm) {
        self.inner.remove(pos)
    }
}

impl std::ops::Deref for SortedPairSet {
    type Target = [(LNTerm, LNTerm)];
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl IntoIterator for SortedPairSet {
    type Item = (LNTerm, LNTerm);
    type IntoIter = std::vec::IntoIter<(LNTerm, LNTerm)>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a> IntoIterator for &'a SortedPairSet {
    type Item = &'a (LNTerm, LNTerm);
    type IntoIter = std::slice::Iter<'a, (LNTerm, LNTerm)>;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

/// Subterm store. Mirrors HS's 5-field `SubtermStore`
/// (SubtermStore.hs):
///   negSubterms / posSubterms / solvedSubterms / isContradictory /
///   oldNegSubterms.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SubtermStore {
    pub subterms: Vec<SubtermConstraint>,
    pub solved_subterms: Vec<SubtermConstraint>,
    /// Whether the store has been determined contradictory.
    pub contradictory: bool,
    /// Negative subterm constraints `¬(small ⊏ big)` — HS `_negSubterms`
    /// (S.Set, so kept sorted by the LNTerm pair Ord for HS-faithful
    /// `S.toList` iteration order).
    pub neg_subterms: SortedPairSet,
    /// Copy of `neg_subterms` that is NOT changed by apply/HasFrees/
    /// add_neg — HS `_oldNegSubterms` (SubtermStore.hs).  Only the
    /// `simpSplitNegSt` pass updates it; the set difference
    /// `neg_subterms \ old_neg_subterms` is the change-detection
    /// mechanism deciding which negative subterms get (re-)split.
    pub old_neg_subterms: SortedPairSet,
}

impl SubtermStore {
    /// Compare in HS's derived `Ord SubtermStore` order: `_negSubterms`,
    /// `_posSubterms`, `_solvedSubterms`, `_isContradictory`, then
    /// `_oldNegSubterms` (SubtermStore.hs).
    ///
    /// The port-only `propagated` marker is deliberately absent from this
    /// comparison because HS stores only `(LNTerm, LNTerm)` pairs.  Keep this
    /// as a named, crate-local operation rather than implementing Rust's
    /// [`Ord`]: derived [`PartialEq`] does include the marker, so the HS order
    /// is intentionally coarser than Rust equality.
    ///
    /// PRECONDITION: comparing the Vec-backed pair lists in element order is
    /// faithful to HS's `Set` comparison only when both stores hold their
    /// `hs_pair`s sorted and deduplicated — i.e. after
    /// `norm_sys_for_compare`'s normalisation, the only context this is
    /// called from.
    pub(crate) fn cmp_hs(&self, other: &Self) -> std::cmp::Ordering {
        fn cmp_pairs(a: &[SubtermConstraint], b: &[SubtermConstraint]) -> std::cmp::Ordering {
            a.iter()
                .map(|c| c.hs_pair())
                .cmp(b.iter().map(|c| c.hs_pair()))
        }
        self.neg_subterms
            .cmp(&other.neg_subterms)
            .then_with(|| cmp_pairs(&self.subterms, &other.subterms))
            .then_with(|| cmp_pairs(&self.solved_subterms, &other.solved_subterms))
            .then_with(|| self.contradictory.cmp(&other.contradictory))
            .then_with(|| self.old_neg_subterms.cmp(&other.old_neg_subterms))
    }

    pub fn empty() -> Self {
        Self::default()
    }

    /// Record a new `small << big` constraint.
    pub fn add(&mut self, small: LNTerm, big: LNTerm) {
        self.subterms.push(SubtermConstraint {
            small,
            big,
            propagated: false,
        });
    }

    /// `addNegSubterm` (SubtermStore.hs): set-insert into
    /// negSubterms.  Sorted insert keeps HS `S.toList` iteration order.
    /// Returns true if the pair was newly added.
    pub fn add_neg(&mut self, small: LNTerm, big: LNTerm) -> bool {
        self.neg_subterms.insert((small, big))
    }

    pub fn is_false(&self) -> bool {
        self.contradictory
    }

    /// `conjoinSubtermStores` — HS-faithful port of
    /// `Theory.Tools.SubtermStore.conjoinSubtermStores` (SubtermStore.hs):
    /// ```haskell
    /// conjoinSubtermStores (SubtermStore a1 b1 c1 d1 e1) (SubtermStore a2 b2 c2 d2 e2)
    ///   = SubtermStore (a1 `S.union` a2) (b1 `S.union` b2)
    ///                  (c1 `S.union` c2) (d1 || d2) (e1 `S.union` e2)
    /// ```
    /// All five HS fields union per HS semantics: neg/pos/solved set-union,
    /// `isContradictory` OR, `oldNegSubterms` set-union.
    pub fn conjoin(&mut self, other: &SubtermStore) {
        for st in &other.subterms {
            if !self
                .subterms
                .iter()
                .any(|own| own.hs_pair() == st.hs_pair())
            {
                self.subterms.push(st.clone());
            }
        }
        for st in &other.solved_subterms {
            if !self
                .solved_subterms
                .iter()
                .any(|own| own.hs_pair() == st.hs_pair())
            {
                self.solved_subterms.push(st.clone());
            }
        }
        self.contradictory = self.contradictory || other.contradictory;
        for (s, t) in other.neg_subterms.iter() {
            self.add_neg(s.clone(), t.clone());
        }
        for p in other.old_neg_subterms.iter() {
            self.old_neg_subterms.insert(p.clone());
        }
    }
}

/// `instance HasFrees SubtermStore` (SubtermStore.hs): the negative
/// subterms, then the positive ones, then the solved ones.  `contradictory`
/// and `old_neg_subterms` are carried over by `pure` — HS states at
/// SubtermStore.hs that `oldNegSubterms` is the copy `apply`/`HasFrees`
/// leave alone.
///
/// HS holds all three walked fields as `S.Set (LNTerm, LNTerm)`, so its fold
/// sees them in ascending pair order (LTerm.hs).  `neg_subterms` is
/// stored sorted, and the walk sorts references to the two `Vec`-backed
/// fields by `(small, big)`.  The map rebuilds `neg_subterms` through
/// [`SortedPairSet::rebuild_from`], which is the `S.fromList` of the HS set
/// map (LTerm.hs); it rewrites `subterms` and `solved_subterms` where
/// they stand, because the port keeps those two in insertion order and the
/// subterm-store pane prints them in it (`pretty_system::pretty_subterm_store`).
impl HasFrees for SubtermStore {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for p in self.neg_subterms.iter() {
            p.for_each_free(f);
        }
        for c in sorted_by_pair(&self.subterms) {
            c.for_each_free(f);
        }
        for c in sorted_by_pair(&self.solved_subterms) {
            c.for_each_free(f);
        }
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        let neg_subterms = SortedPairSet::rebuild_from(
            self.neg_subterms
                .into_iter()
                .map(|p| p.map_free_with(&mut *f, monotone)),
        );
        let subterms = self.subterms.map_free_with(f, monotone);
        let solved_subterms = self.solved_subterms.map_free_with(f, monotone);
        SubtermStore {
            subterms,
            solved_subterms,
            contradictory: self.contradictory,
            neg_subterms,
            old_neg_subterms: self.old_neg_subterms,
        }
    }
}

/// The constraints of `cs` ordered by `(small, big)`, the order HS's
/// `S.Set (LNTerm, LNTerm)` enumerates the same pairs in
/// (SubtermStore.hs).  `SubtermConstraint` carries a `propagated`
/// marker that is not part of that pair, so the sort reads
/// [`SubtermConstraint::hs_pair`].
fn sorted_by_pair(cs: &[SubtermConstraint]) -> Vec<&SubtermConstraint> {
    let mut out: Vec<&SubtermConstraint> = cs.iter().collect();
    out.sort_by(|a, b| a.hs_pair().cmp(&b.hs_pair()));
    out
}

/// `elemNotBelowReducible reducible inner outer` — port of Haskell's
/// `Term.Term.elemNotBelowReducible` (`Term/Term.hs`).  True iff
/// `inner` occurs syntactically in `outer` and never below a
/// reducible function symbol.
///
/// Used by `has_subterm_cycle` and (indirectly) by the subterm-store
/// simplification.  The "below reducible" exception is sound under
/// the equational theory: once you cross a reducible head, the
/// subterm could disappear under rewriting.
pub fn elem_not_below_reducible(
    reducible: &FastSet<FunSym>,
    inner: &LNTerm,
    outer: &LNTerm,
) -> bool {
    if inner == outer {
        return true;
    }
    match outer {
        Term::App(sym, args) => {
            if reducible.contains(sym) {
                return false;
            }
            args.iter()
                .any(|a| elem_not_below_reducible(reducible, inner, a))
        }
        _ => false,
    }
}

/// `processACSubterm f (small, big)` — HS SubtermStore.hs.
/// Returns `Err(false)` / `Err(true)` for the trivially-false /
/// trivially-true reductions, or `Ok((nSmall, nBig))` for the
/// terms with common AC children removed (both re-wrapped under `f`).
pub fn process_ac_subterm(
    f: tamarin_term::function_symbols::AcSym,
    small: &LNTerm,
    big: &LNTerm,
) -> Result<(LNTerm, LNTerm), bool> {
    use tamarin_term::lterm::flattened_ac_terms;
    use tamarin_term::term::f_app_ac;
    let mut l_small: Vec<LNTerm> = flattened_ac_terms(f, small).into_iter().cloned().collect();
    let mut l_big: Vec<LNTerm> = flattened_ac_terms(f, big).into_iter().cloned().collect();
    l_small.sort();
    l_big.sort();
    // removeSame over the two sorted lists.
    let mut s_rem: Vec<LNTerm> = Vec::new();
    let mut b_rem: Vec<LNTerm> = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;
    while i < l_small.len() && j < l_big.len() {
        match l_small[i].cmp(&l_big[j]) {
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
            std::cmp::Ordering::Less => {
                s_rem.push(l_small[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                b_rem.push(l_big[j].clone());
                j += 1;
            }
        }
    }
    while i < l_small.len() {
        s_rem.push(l_small[i].clone());
        i += 1;
    }
    while j < l_big.len() {
        b_rem.push(l_big[j].clone());
        j += 1;
    }
    // case lists of (_, []) -> Right False; ([], _) -> Right True; ...
    if b_rem.is_empty() {
        return Err(false);
    }
    if s_rem.is_empty() {
        return Err(true);
    }
    Ok((f_app_ac(f, s_rem), f_app_ac(f, b_rem)))
}

/// One leaf of [`split_subterm`] — direct port of HS `SubtermSplit`
/// (SubtermStore.hs).  The disjunction-over-list ordering in
/// `solveSubterm` (`SubtermSplit{i}` case names) depends on the
/// constructor order being preserved, so the variants and their
/// `Ord` (derived) must follow HS exactly:
/// `SubtermD < NatSubtermD < EqualD < ACNewVarD < TrueD`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum SubtermSplit {
    SubtermD(LNTerm, LNTerm),
    NatSubtermD(LNTerm, LNTerm),
    EqualD(LNTerm, LNTerm),
    /// `((small+newVar, big), newVar)` — HS `ACNewVarD`.
    AcNewVarD(LNTerm, LNTerm, LVar),
    TrueD,
}

/// `step` of HS `splitSubterm` (SubtermStore.hs).  Allocates a
/// fresh `newVar` for the AC-recurse arm via `mk_fresh` (a closure
/// mirroring `MonadFresh`'s `freshLVar "newVar" (sortOfLNTerm big)`).
/// Returns `None` when `(small, big)` cannot be decomposed further, or
/// `Some(set)` — sorted and deduped, mirroring HS's `S.Set SubtermSplit`.
pub fn subterm_step(
    reducible: &FastSet<FunSym>,
    small: &LNTerm,
    big: &LNTerm,
    mk_fresh: &mut dyn FnMut(tamarin_term::lterm::LSort) -> LVar,
) -> Option<Vec<SubtermSplit>> {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::{flattened_ac_terms, is_msg_var, sort_of_lnterm, LSort};
    use tamarin_term::term::f_app_ac;
    use tamarin_term::vterm::{var_term, Lit};
    // isTrueFalse arms (SubtermStore.hs).
    match is_true_false(reducible, small, big) {
        Some(true) => return Some(vec![SubtermSplit::TrueD]),
        Some(false) => return Some(vec![]),
        None => {}
    }
    // CR-rule S_nat delayed (SubtermStore.hs).
    let small_nat_or_msg = sort_of_lnterm(small) == LSort::Nat || is_msg_var(small);
    if small_nat_or_msg && sort_of_lnterm(big) == LSort::Nat {
        return match process_ac_subterm(AcSym::NatPlus, small, big) {
            Ok((s, t)) => Some(vec![SubtermSplit::NatSubtermD(s, t)]),
            // HS errors here: the preceding classification must catch it.
            Err(_) => {
                debug_assert!(false, "is_true_false missed a reducible Nat subterm");
                None
            }
        };
    }
    let mut out: Vec<SubtermSplit> = match big {
        // variable big: do not recurse further (SubtermStore.hs).
        Term::Lit(Lit::Var(_)) => return None,
        // AC big, non-reducible head: S_subterm-ac-recurse
        // (SubtermStore.hs).
        Term::App(FunSym::Ac(f), _) if !reducible.contains(&FunSym::Ac(*f)) => {
            let f = *f;
            let big_flat: Vec<LNTerm> = flattened_ac_terms(f, big).into_iter().cloned().collect();
            let big_norm = f_app_ac(f, big_flat.clone());
            match process_ac_subterm(f, small, &big_norm) {
                // HS errors here: the preceding classification must catch it.
                Err(_) => {
                    debug_assert!(false, "is_true_false missed a reducible AC subterm");
                    return None;
                }
                Ok((n_small, n_big)) => {
                    let new_var = mk_fresh(sort_of_lnterm(big));
                    let small_plus = f_app_ac(f, vec![n_small, var_term(new_var)]);
                    let mut out: Vec<SubtermSplit> = Vec::with_capacity(1 + big_flat.len());
                    out.push(SubtermSplit::AcNewVarD(small_plus, n_big, new_var));
                    // map (curry SubtermD small) (flattenedACTerms f big)
                    for child in big_flat {
                        out.push(SubtermSplit::SubtermD(small.clone(), child));
                    }
                    out
                }
            }
        }
        // NoEq big, non-reducible head: S_subterm-recurse
        // (SubtermStore.hs), whose leaves come from `eqOrSubterm`
        // (SubtermStore.hs).
        Term::App(fs @ FunSym::NoEq(_), ts) if !reducible.contains(fs) => {
            let mut out: Vec<SubtermSplit> = Vec::with_capacity(2 * ts.len());
            for ti in ts.iter() {
                out.push(SubtermSplit::SubtermD(small.clone(), ti.clone()));
                out.push(SubtermSplit::EqualD(small.clone(), ti.clone()));
            }
            out
        }
        // C (commutative but not associative, SubtermStore.hs), List
        // (SubtermStore.hs), and any reducible head (SubtermStore.hs).
        _ => return None,
    };
    // HS builds each arm as an `S.Set`.
    out.sort();
    out.dedup();
    Some(out)
}

/// `splitSubterm reducible noRecurse (small, big)` — HS
/// SubtermStore.hs.  Returns the sorted-deduped leaf list (HS
/// `S.toList`) whose disjunction is equivalent to `small ⊏ big`: an empty
/// list for a trivially false subterm, `[TrueD]` for a trivially true one.
///
/// `recurse` is HS's `noRecurse` inverted: `false` takes HS's `singleStep`
/// (one `step`, used by `solveSubterm` and `simpSplitPosSt`), `true` takes
/// HS's `recurse`, which re-`step`s every `SubtermD` leaf until it stops
/// decomposing (used by `simpSplitNegSt`).  `mk_fresh` allocates the
/// AC-recurse arm's fresh vars, mirroring `MonadFresh`.
pub fn split_subterm(
    reducible: &FastSet<FunSym>,
    recurse: bool,
    small: &LNTerm,
    big: &LNTerm,
    mk_fresh: &mut dyn FnMut(tamarin_term::lterm::LSort) -> LVar,
) -> Vec<SubtermSplit> {
    let mut out: Vec<SubtermSplit> = Vec::new();
    if recurse {
        recurse_subterm(reducible, small, big, mk_fresh, &mut out);
    } else {
        // singleStep (SubtermStore.hs):
        //   fromMaybe (S.singleton (SubtermD st)) <$> step st
        match subterm_step(reducible, small, big, mk_fresh) {
            Some(v) => out = v,
            None => out.push(SubtermSplit::SubtermD(small.clone(), big.clone())),
        }
    }
    // Mirror `S.toList`: sort + dedup by the derived Ord.
    out.sort();
    out.dedup();
    out
}

/// HS `recurse` (SubtermStore.hs): re-`step` every `SubtermD`
/// entry, keep every other leaf as it is, and stop where `step` returns
/// `Nothing`.  Entries are visited in `S.toList` order, which
/// [`subterm_step`] already produces.
fn recurse_subterm(
    reducible: &FastSet<FunSym>,
    small: &LNTerm,
    big: &LNTerm,
    mk_fresh: &mut dyn FnMut(tamarin_term::lterm::LSort) -> LVar,
    out: &mut Vec<SubtermSplit>,
) {
    match subterm_step(reducible, small, big, mk_fresh) {
        Some(entries) => {
            for e in entries {
                match e {
                    SubtermSplit::SubtermD(s, t) => {
                        recurse_subterm(reducible, &s, &t, mk_fresh, out)
                    }
                    other => out.push(other),
                }
            }
        }
        None => out.push(SubtermSplit::SubtermD(small.clone(), big.clone())),
    }
}

/// `isTrueFalse reducible Nothing (small, big)` (SubtermStore.hs):
/// `Some(true)` / `Some(false)` for a trivially true / false subterm
/// relation, `None` when it depends on the substitution. The guards follow
/// HS's equation order; a matching Nat guard is the whole answer.
pub fn is_true_false(reducible: &FastSet<FunSym>, small: &LNTerm, big: &LNTerm) -> Option<bool> {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::{
        flattened_ac_terms, is_fresh_var, is_msg_var, is_pub_var, sort_of_lnterm, LSort,
    };
    use tamarin_term::vterm::Lit;
    let small_nat_or_msg_var = sort_of_lnterm(small) == LSort::Nat || is_msg_var(small);
    if sort_of_lnterm(big) == LSort::Nat {
        let small_flat = flattened_ac_terms(AcSym::NatPlus, small);
        let only_ones = small_flat.iter().all(|t| tamarin_term::term::is_nat_one(t));
        if only_ones && small_flat.len() < flattened_ac_terms(AcSym::NatPlus, big).len() {
            return Some(true);
        }
        // CR-rule S_nat (delayed).
        if small_nat_or_msg_var {
            return process_ac_subterm(AcSym::NatPlus, small, big).err();
        }
    }
    // `big redElem small` covers `small == big`.
    if elem_not_below_reducible(reducible, big, small) {
        return Some(false);
    }
    if elem_not_below_reducible(reducible, small, big) {
        return Some(true);
    }
    match big {
        // Nothing can be a strict subterm of a constant.
        Term::Lit(Lit::Con(_)) => Some(false),
        // CR-rule S_invalid.
        Term::Lit(Lit::Var(_))
            if is_pub_var(big)
                || is_fresh_var(big)
                || (!small_nat_or_msg_var && sort_of_lnterm(big) == LSort::Nat) =>
        {
            Some(false)
        }
        // CR-rule S_subterm-ac-recurse.
        Term::App(FunSym::Ac(ac_sym), _) if !reducible.contains(&FunSym::Ac(*ac_sym)) => {
            process_ac_subterm(*ac_sym, small, big).err()
        }
        _ => None,
    }
}

/// Collector companion to [`elem_not_below_reducible`], specialised for the
/// case where `inner` is a **Fresh-sort variable leaf**.
///
/// For a `Var` `inner`, `elem_not_below_reducible`'s `inner == outer` base case
/// can only fire at a `Var` leaf (a var is a `Lit`, never an `App`), so the
/// predicate reduces to "`inner` occurs in `outer` on a root-to-leaf path never
/// crossing a reducible-headed `App`" — a property of `outer` and the var
/// alone, INDEPENDENT of which fresh var is queried.  This walk collects, in a
/// single pass over `t`, EVERY Fresh-sort variable `v` for which
/// `elem_not_below_reducible(reducible, Lit(Var(v)), t)` holds.  Callers that
/// would otherwise probe `t` once per candidate fresh var (see
/// `enforce_fresh_ordering_pass`) precompute this set once and replace the walk
/// with a hash-membership test.  The three arms mirror
/// `elem_not_below_reducible` exactly: cross a reducible head ⇒ stop; other
/// `App` ⇒ recurse args; a Fresh `Var` leaf ⇒ collect it; anything else ⇒
/// contributes nothing.
pub fn collect_fresh_vars_not_below_reducible(
    reducible: &FastSet<FunSym>,
    t: &LNTerm,
    out: &mut FastSet<tamarin_term::lterm::LVar>,
) {
    use tamarin_term::lterm::LSort;
    use tamarin_term::vterm::Lit;
    match t {
        Term::App(sym, args) => {
            if reducible.contains(sym) {
                return;
            }
            for a in args.iter() {
                collect_fresh_vars_not_below_reducible(reducible, a, out);
            }
        }
        Term::Lit(Lit::Var(v)) if v.sort == LSort::Fresh => {
            out.insert(*v);
        }
        _ => {}
    }
}

/// `hasSubtermCycle` — port of Haskell's
/// `Theory.Tools.SubtermStore.hasSubtermCycle` (`SubtermStore.hs`).
///
/// Detects a cycle `t0 ⊏ x0, ..., tn ⊏ xn = t0 ⊏ x0` in the positive
/// subterm dag, where each next edge `(t_i+1, x_i+1)` follows from
/// `elem_not_below_reducible reducible x_i t_i+1`.
///
/// Returns `true` if any such cycle exists.  The DFS uses (entry,
/// parent-set) tracking to avoid revisiting already-finished nodes
/// while still detecting back-edges into the current recursion
/// stack.
pub fn has_subterm_cycle(reducible: &FastSet<FunSym>, store: &SubtermStore) -> bool {
    let dag: Vec<(LNTerm, LNTerm)> = store
        .subterms
        .iter()
        .map(|c| (c.small.clone(), c.big.clone()))
        .collect();
    has_subterm_cycle_in_dag(reducible, &dag)
}

/// [`has_subterm_cycle`] after hypothetically adding one active positive
/// subterm: the `hasSubtermCycle (insertSubterm st sst)` probe of
/// `isTrueFalse`, over a store projection the caller already holds.
pub(crate) fn has_subterm_cycle_with_pairs(
    reducible: &FastSet<FunSym>,
    pairs: &[(LNTerm, LNTerm)],
    extra: (&LNTerm, &LNTerm),
) -> bool {
    let mut dag = Vec::with_capacity(pairs.len() + 1);
    dag.extend_from_slice(pairs);
    if !dag.iter().any(|(s, t)| s == extra.0 && t == extra.1) {
        dag.push((extra.0.clone(), extra.1.clone()));
    }
    has_subterm_cycle_in_dag(reducible, &dag)
}

fn has_subterm_cycle_in_dag(reducible: &FastSet<FunSym>, dag: &[(LNTerm, LNTerm)]) -> bool {
    if dag.is_empty() {
        return false;
    }
    let mut visited: std::collections::BTreeSet<(LNTerm, LNTerm)> =
        std::collections::BTreeSet::new();
    for edge in dag {
        let mut parents = std::collections::BTreeSet::new();
        if find_loop(reducible, dag, edge, &mut parents, &mut visited).is_none() {
            return true;
        }
    }
    false
}

/// DFS helper: returns `None` on a detected back-edge (cycle),
/// `Some(())` otherwise.  Marks the edge as visited on completion.
fn find_loop(
    reducible: &FastSet<FunSym>,
    dag: &[(LNTerm, LNTerm)],
    x: &(LNTerm, LNTerm),
    parents: &mut std::collections::BTreeSet<(LNTerm, LNTerm)>,
    visited: &mut std::collections::BTreeSet<(LNTerm, LNTerm)>,
) -> Option<()> {
    if parents.contains(x) {
        return None;
    }
    if visited.contains(x) {
        return Some(());
    }
    parents.insert(x.clone());
    // Successors: edges (e, e') in the dag such that `x.1` (the big
    // side of x's subterm) appears in `e` not below a reducible head.
    // `dag` is immutable for the whole walk, so filtering lazily visits the
    // same edges in the same order as HS's `next` list snapshot.
    for n in dag
        .iter()
        .filter(|e| elem_not_below_reducible(reducible, &x.1, &e.0))
    {
        find_loop(reducible, dag, n, parents, visited)?;
    }
    parents.remove(x);
    visited.insert(x.clone());
    Some(())
}

// `fAppNatOne = fAppNoEq natOneSym []` — the surface form of `%1`.
fn nat_one_term() -> LNTerm {
    tamarin_term::term::f_app_no_eq(tamarin_term::function_symbols::nat_one_sym(), vec![])
}

// Vertex = (Bool sign, LVar var).  We use `(bool, LVar)` directly.
type Vertex = (bool, LVar);

/// `inf = maxBound `div` 2` — large sentinel, avoid overflow in `ik + kj`.
const NAT_INF: i64 = i64::MAX / 4;

/// Steps 1–8 of [`nat_subterm_equalities`]: a satisfying solution of the
/// nat-subterm UTVPI system, with the graph it solves.
struct NatSolution {
    vertices: Vec<Vertex>,
    vertex_to_int: std::collections::BTreeMap<Vertex, usize>,
    edges: Vec<((Vertex, Vertex), i64)>,
    sol: Vec<i64>,
}

/// Whether the nat-subterm `relation` is satisfiable, i.e.
/// [`nat_subterm_equalities`] returns `Some`, without deriving equalities.
pub(crate) fn nat_subterms_consistent(relation: &[(LNTerm, LNTerm)]) -> bool {
    nat_solution(relation).is_some()
}

/// Solve steps 1–8 of [`nat_subterm_equalities`]; `None` when unsatisfiable.
fn nat_solution(relation: &[(LNTerm, LNTerm)]) -> Option<NatSolution> {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::{flattened_ac_terms, get_var, LSort};

    // `formatEdge` (SubtermStore.hs).
    // For each `(small, big)`:
    //   - flatten both sides as NatPlus AC-summands;
    //   - extract `getVars = mapMaybe getVar . filter (/= fAppNatOne)`;
    //   - `countOnes = length . filter (== fAppNatOne)`;
    //   - 1 var total → 1 edge; 2 vars total → 2 edges; else → no edges.
    // Returns a list of `((from, to), weight)`.
    fn format_edge(st: &(LNTerm, LNTerm)) -> Vec<((Vertex, Vertex), i64)> {
        let (a, b) = st;
        let one = nat_one_term();
        // `flattened_ac_terms` borrows out of `a`/`b`, so the summands are
        // inspected in place — no per-summand clone.
        let l_flat: Vec<&LNTerm> = flattened_ac_terms(AcSym::NatPlus, a);
        let r_flat: Vec<&LNTerm> = flattened_ac_terms(AcSym::NatPlus, b);
        // Upstream #958: do not silently discard non-natural summands or
        // encode message variables as natural-number ordering vertices.
        if !l_flat
            .iter()
            .chain(&r_flat)
            .all(|t| **t == one || matches!(get_var(t), Some(v) if v.sort == LSort::Nat))
        {
            return Vec::new();
        }
        let l_vars: Vec<LVar> = l_flat
            .iter()
            .copied()
            .filter(|t| *t != &one)
            .filter_map(|t| get_var(t).copied())
            .collect();
        let r_vars: Vec<LVar> = r_flat
            .iter()
            .copied()
            .filter(|t| *t != &one)
            .filter_map(|t| get_var(t).copied())
            .collect();
        let l_ones = l_flat.iter().filter(|t| ***t == one).count() as i64;
        let r_ones = r_flat.iter().filter(|t| ***t == one).count() as i64;
        let total_vars = l_vars.len() + r_vars.len();
        if total_vars == 1 {
            let d: i64 = 2 * (r_ones - l_ones - 1);
            // `from = head $ map (True,) (getVars l) ++ map (False,) (getVars r)`
            let from: Vertex = if let Some(v) = l_vars.first() {
                (true, *v)
            } else {
                // Must exist because total_vars == 1
                (false, r_vars[0])
            };
            let to: Vertex = (!from.0, from.1);
            vec![((from, to), d)]
        } else if total_vars == 2 {
            let d: i64 = r_ones - l_ones - 1;
            // `froms = map (True,) (getVars l) ++ map (False,) (getVars r)`
            let mut froms: Vec<Vertex> = Vec::with_capacity(2);
            for v in &l_vars {
                froms.push((true, *v));
            }
            for v in &r_vars {
                froms.push((false, *v));
            }
            // `tos = map (first not) (reverse froms)`; `froms` and `tos` both
            // hold exactly the two vars, so zipping pairs them positionally.
            let tos: Vec<Vertex> = froms.iter().rev().map(|(s, v)| (!s, *v)).collect();
            froms
                .into_iter()
                .zip(tos)
                .map(|(f, t)| ((f, t), d))
                .collect()
        } else {
            Vec::new()
        }
    }

    // ---- realEdges + vertex set ------------------------------------------
    let mut real_edges: Vec<((Vertex, Vertex), i64)> = Vec::new();
    for st in relation {
        real_edges.extend(format_edge(st));
    }

    // `vertices = S.toList $ S.fromList $ concatMap ...` (SubtermStore.hs)
    // BTreeSet for deterministic ordering matching HS Set semantics.
    let mut vertex_set: std::collections::BTreeSet<Vertex> = std::collections::BTreeSet::new();
    for ((a, b), _) in &real_edges {
        vertex_set.insert(*a);
        vertex_set.insert(*b);
    }
    let vertices: Vec<Vertex> = vertex_set.into_iter().collect();
    let n = vertices.len();

    // `vertexToInt v = lookup v $ zip vertices [0..]` (SubtermStore.hs)
    let vertex_to_int: std::collections::BTreeMap<Vertex, usize> =
        vertices.iter().enumerate().map(|(i, v)| (*v, i)).collect();
    let vti = |v: &Vertex| -> usize { vertex_to_int[v] };

    // `oneEdges = map ... $ filter fst vertices` (SubtermStore.hs) —
    // self-loops `(False, x) → (True, x)` with weight -2 for every
    // `(True, x)` vertex.
    let mut one_edges: Vec<((Vertex, Vertex), i64)> = Vec::new();
    for v in &vertices {
        if v.0 {
            one_edges.push((((false, v.1), (true, v.1)), -2));
        }
    }

    // `rawEdges = realEdges ++ oneEdges` (SubtermStore.hs)
    let mut raw_edges: Vec<((Vertex, Vertex), i64)> = Vec::new();
    raw_edges.extend(real_edges.iter().copied());
    raw_edges.extend(one_edges.iter().copied());

    let inf = NAT_INF;

    // ---- Floyd-Warshall (SubtermStore.hs) -----------------------
    // 2-D matrix flattened to a Vec<i64> of length n*n.
    let mut fw: Vec<i64> = vec![inf; n * n];
    for ((from, to), w) in &raw_edges {
        // HS overwrites duplicate edges (last write wins); we mirror that
        // by simple assignment (no min).
        fw[vti(from) * n + vti(to)] = *w;
    }
    for i in 0..n {
        fw[i * n + i] = 0;
    }
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                let ik = fw[i * n + k];
                let kj = fw[k * n + j];
                if ik < inf && kj < inf {
                    let cand = ik + kj;
                    if cand < fw[i * n + j] {
                        fw[i * n + j] = cand;
                    }
                }
            }
        }
    }

    // ---- tightenedEdges (SubtermStore.hs) -----------------------
    // For each `(True, x)` vertex `v`: let `d = fw(v, ~v)`.
    // HS: `if even d && d < inf/2 then Nothing else Just ((v, ~v), d - 1)`.
    // i.e. add the tightened edge unless `d` is reachable AND even.
    let mut tightened_edges: Vec<((Vertex, Vertex), i64)> = Vec::new();
    for v in &vertices {
        if !v.0 {
            continue;
        }
        let nv: Vertex = (false, v.1);
        let d = fw[vti(v) * n + vti(&nv)];
        let reachable = d < inf / 2;
        let is_even = d.rem_euclid(2) == 0;
        if reachable && is_even {
            continue;
        }
        tightened_edges.push(((*v, nv), d - 1));
    }

    // `edges = rawEdges ++ tightenedEdges` (SubtermStore.hs)
    let mut edges: Vec<((Vertex, Vertex), i64)> = raw_edges.clone();
    edges.extend(tightened_edges);

    // ---- Bellman-Ford (SubtermStore.hs) -------------------------
    // Solution init = 0 for all vertices; relax `|V|` times.
    let mut sol: Vec<i64> = vec![0; n];
    for _ in 0..n {
        for ((from, to), w) in &edges {
            let df = sol[vti(from)];
            let dt = sol[vti(to)];
            // Guard against +inf overflow.
            if df < inf / 2 {
                let cand = w + df;
                if cand < dt {
                    sol[vti(to)] = cand;
                }
            }
        }
    }
    // `solvable`: no edge can be further relaxed.
    let solvable = edges.iter().all(|((from, to), w)| {
        let df = sol[vti(from)];
        let dt = sol[vti(to)];
        if df >= inf / 2 {
            return true;
        }
        w + df >= dt
    });
    if !solvable {
        return None;
    }

    Some(NatSolution {
        vertices,
        vertex_to_int,
        edges,
        sol,
    })
}

/// `natSubtermEqualities` — UTVPI-based cycle detection and equality
/// derivation on the nat-subterm fragment of the constraint graph.
///
/// HS source: `Theory.Tools.SubtermStore.natSubtermEqualities`
/// (SubtermStore.hs) — the algorithm itself.
///
/// HS caller: `simpNatCycles` (SubtermStore.hs) inside
/// `simpSubtermStore` (SubtermStore.hs).
///
/// Returns:
///   - `None` ⇒ the UTVPI system is unsatisfiable (= the posSubterm
///     graph has a negative cycle), so the subterm store is
///     contradictory.
///   - `Some(eqs)` ⇒ list of `(l, r)` LNTerm pairs to emit as
///     positive equalities (`EqE l r`).  `eqs` may be empty (no
///     equalities implied) without indicating contradiction.
///
/// Algorithm (mirrors HS line-by-line):
///   1. Vertex encoding: `(Bool, LVar)` — `True` = positive sign,
///      `False` = negative sign.  Vertices come from the set of
///      variables that appear in nat-subterm edges.
///   2. `formatEdge`: each nat-subterm `s ⊏ t` (with `isNatSubterm`)
///      becomes either:
///      Edge weight `d = 2 * (countOnes(r) - countOnes(l) - 1)`, and:
///        - 1 var total → 1 edge.
///        - 2 vars total → 2 edges (symmetric).
///   3. `oneEdges`: self-loop `(False, x) → (True, x)` with weight
///      `-2` for every `(True, x)` vertex.
///   4. `rawEdges = realEdges ++ oneEdges`.
///   5. Floyd-Warshall closure on `rawEdges`.
///   6. `tightenedEdges`: for `(True, x)` vertex `v`, if
///      `distFW(v, ~v)` is reachable and odd, add edge
///      `(v, ~v, distFW(v, ~v) - 1)`.  (Reachable+even ⇒ skip.)
///   7. `edges = rawEdges ++ tightenedEdges`.
///   8. Bellman-Ford on `edges` from a 0-init solution.  Unsat iff
///      after `|V|` relax rounds, some edge `(u, v, w)` satisfies
///      `w + dist(u) < dist(v)` — i.e. a relaxable edge remains.
///   9. `slackEdges`: edges where `w + dist(u) == dist(v)` (tight).
///  10. SCCs of `slackEdges` (Kosaraju on the directed slack graph).
///  11. For each SCC, pick the vertex with smallest `dist`; emit
///      `x = y + n` equalities for all OTHER `True`-tagged vertices
///      in the SCC (HS filters `filter fst sccs` then `delete x`).
///  12. For variables that appear in BOTH `True` and `False` in the
///      same SCC, emit absolute `x = N` equalities, where
///      `N = (dist(False, v) - dist(True, v)) / 2`.
pub(crate) fn nat_subterm_equalities(
    relation: &[(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)],
) -> Option<Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>> {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::term::f_app_ac;

    let NatSolution {
        vertices,
        vertex_to_int,
        edges,
        sol,
    } = nat_solution(relation)?;
    let n = vertices.len();
    if n == 0 {
        return Some(Vec::new());
    }
    let vti = |v: &Vertex| -> usize { vertex_to_int[v] };
    let inf = NAT_INF;

    // ---- slackEdges (SubtermStore.hs) ---------------------------
    let slack_edges: Vec<(Vertex, Vertex)> = edges
        .iter()
        .filter(|((from, to), w)| {
            let df = sol[vti(from)];
            let dt = sol[vti(to)];
            if df >= inf / 2 {
                return false;
            }
            w + df == dt
        })
        .map(|((from, to), _)| (*from, *to))
        .collect();

    // ---- SCC of slackEdges (SubtermStore.hs) -------------------
    // Successor lists indexed by the dense vertex numbers `0..n`, each in
    // slack-edge order.
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (from, to) in &slack_edges {
        succ[vti(from)].push(vti(to));
    }
    // Tarjan's SCC algorithm (deterministic, single-pass).
    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut indices: Vec<Option<usize>> = vec![None; n];
    let mut lowlinks: Vec<usize> = vec![0; n];
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    // Iterative Tarjan to avoid deep recursion stacks.
    fn strongconnect(
        v: usize,
        succ: &[Vec<usize>],
        index_counter: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut Vec<bool>,
        indices: &mut Vec<Option<usize>>,
        lowlinks: &mut Vec<usize>,
        sccs: &mut Vec<Vec<usize>>,
    ) {
        // Work-stack-based simulation
        let mut work: Vec<(usize, usize)> = vec![(v, 0)];
        while let Some(&(node, pi)) = work.last() {
            if pi == 0 {
                indices[node] = Some(*index_counter);
                lowlinks[node] = *index_counter;
                *index_counter += 1;
                stack.push(node);
                on_stack[node] = true;
            }
            // Borrowed, not cloned: `succ` outlives the whole walk and the
            // only mutation below is to `work`/`lowlinks`/`stack`.
            let neighbours: &[usize] = &succ[node];
            if pi < neighbours.len() {
                let w = neighbours[pi];
                work.last_mut().unwrap().1 += 1;
                if indices[w].is_none() {
                    work.push((w, 0));
                    continue;
                } else if on_stack[w] {
                    lowlinks[node] = lowlinks[node].min(indices[w].unwrap());
                }
            } else {
                if lowlinks[node] == indices[node].unwrap() {
                    let mut comp: Vec<usize> = Vec::new();
                    loop {
                        let w = stack.pop().unwrap();
                        on_stack[w] = false;
                        comp.push(w);
                        if w == node {
                            break;
                        }
                    }
                    sccs.push(comp);
                }
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    lowlinks[parent] = lowlinks[parent].min(lowlinks[node]);
                }
            }
        }
    }

    for v_i in 0..n {
        if indices[v_i].is_none() {
            strongconnect(
                v_i,
                &succ,
                &mut index_counter,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut sccs,
            );
        }
    }

    // ---- equalities (SubtermStore.hs) ---------------------------
    // For each SCC: pick the vertex with smallest dist (`getValue`).
    // For `(True, x)` vertices in the SCC (other than the smallest),
    // emit `x = smallest_var + (dist(this) - dist(smallest)) * 1`.
    //
    // Note: HS uses `foldr1` which respects HS Set iteration order on
    // the SCC.  We use BTreeSet ordering on `Vertex` for the same
    // determinism — the HS ordering of `(Bool, LVar)` is
    // `Bool > Bool` first (False < True), then LVar order — Rust's
    // derived Ord on `(bool, LVar)` matches.
    //
    // `addN y n`: `varTerm y + n * fAppNatOne`.
    fn add_n(y: &LVar, n: i64) -> LNTerm {
        let var_term: LNTerm = Term::Lit(tamarin_term::vterm::Lit::Var(*y));
        if n == 0 {
            return var_term;
        }
        // `iterate (++: fAppNatOne) (varTerm y) !! n` — right-fold:
        // `varTerm y + 1 + 1 + ... + 1` (n times).
        let one = nat_one_term();
        let mut ones: Vec<LNTerm> = Vec::with_capacity(n as usize);
        for _ in 0..n {
            ones.push(one.clone());
        }
        // f_app_ac flattens/sorts; we want one big NatPlus call.
        let mut args = vec![var_term];
        args.extend(ones);
        f_app_ac(AcSym::NatPlus, args)
    }
    // `termN n`: `1 + 1 + ... + 1` (n ones), as in HS `termN`.
    fn term_n(n: i64) -> LNTerm {
        debug_assert!(n > 0);
        let one = nat_one_term();
        if n == 1 {
            return one;
        }
        let mut args: Vec<LNTerm> = Vec::with_capacity(n as usize);
        for _ in 0..n {
            args.push(one.clone());
        }
        f_app_ac(AcSym::NatPlus, args)
    }

    let get_value = |v: &Vertex| -> i64 { sol[vti(v)] };

    let mut equalities: Vec<(LNTerm, LNTerm)> = Vec::new();

    // Sort SCCs canonically (by their member set) for determinism.
    // HS `graphFromEdges` returns SCCs in reverse-postorder over the
    // original vertex order; the equality output is then folded by
    // `concatMap` over the SCC list in that same order.  We sort by
    // first member's vertex index to match HS BTreeSet semantics —
    // though equality output is deduplicated downstream, ordering
    // affects the emit sequence.
    let mut scc_vertices: Vec<Vec<Vertex>> = sccs
        .iter()
        .map(|comp| {
            let mut s: Vec<Vertex> = comp.iter().map(|i| vertices[*i]).collect();
            s.sort();
            s
        })
        .collect();
    scc_vertices.sort();

    for scc in &scc_vertices {
        // `smallest = foldr1 (\x y -> if getValue x < getValue y then x else y)`
        // HS `foldr1` walks right-to-left and ties go to the rightmost.
        let mut smallest: Vertex = scc[scc.len() - 1];
        for v in scc.iter().rev().skip(1) {
            if get_value(v) < get_value(&smallest) {
                smallest = *v;
            }
        }
        // `filter fst scc` — keep only True-tagged vertices.
        let positives: Vec<Vertex> = scc.iter().filter(|v| v.0).copied().collect();
        // `delete smallest positives` — remove if present.
        let mut ys: Vec<Vertex> = Vec::new();
        let mut removed = false;
        for v in positives {
            if !removed && v == smallest {
                removed = true;
                continue;
            }
            ys.push(v);
        }
        for y in &ys {
            // `buildEq x y = Equal (varTerm (snd x)) (addN (snd y) (getValue y - getValue x))`
            // i.e. lhs is `varTerm smallest.var`, rhs is `varTerm y.var + (gv(y)-gv(smallest))`.
            let lhs_var = &smallest.1;
            let rhs_var = &y.1;
            let n = get_value(y) - get_value(&smallest);
            let lhs: LNTerm = Term::Lit(tamarin_term::vterm::Lit::Var(*lhs_var));
            let rhs: LNTerm = add_n(rhs_var, n);
            equalities.push((lhs, rhs));
        }

        // Absolute equalities: variables that appear with BOTH signs in
        // this SCC (`duplicates = concatMap ((\xs -> xs \\ S.toList (S.fromList xs)) . map snd) sccs`,
        // SubtermStore.hs).
        // Implementation: list ALL `snd` from the SCC; build the
        // multiset; the variables that appear more than once are the
        // duplicates.  We mirror HS's `xs \\ S.toList (S.fromList xs)` —
        // i.e. take each var and remove one copy of its first occurrence.
        let snds: Vec<LVar> = scc.iter().map(|v| v.1).collect();
        let mut seen: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        let mut dups: Vec<LVar> = Vec::new();
        for v in &snds {
            if !seen.insert(*v) {
                dups.push(*v);
            }
        }
        for v in &dups {
            let neg_v: Vertex = (false, *v);
            let pos_v: Vertex = (true, *v);
            let val = (get_value(&neg_v) - get_value(&pos_v)) / 2;
            if val <= 0 {
                // HS `termN` precondition `n > 0`; if `val ≤ 0` the absolute
                // equality is degenerate (= 0 ones is not representable as a
                // NatPlus term).  Skip — this case shouldn't arise under a
                // sat solution (`getValue (False,v) ≥ getValue (True,v) + 2`
                // is enforced by the `oneEdges`).  Defensive.
                continue;
            }
            let lhs: LNTerm = Term::Lit(tamarin_term::vterm::Lit::Var(*v));
            let rhs: LNTerm = term_n(val);
            equalities.push((lhs, rhs));
        }
    }

    Some(equalities)
}

/// HS `isTrueFalse reducible (Just sst)` (SubtermStore.hs): the
/// store-independent checks, then store membership, then the relation's
/// consistency after hypothetically inserting it into the positive store.
/// Built once per pass; the active positive projection is computed on first use.
pub(crate) struct StoreValuation<'a> {
    reducible: &'a FastSet<FunSym>,
    store: &'a SubtermStore,
    active: std::cell::OnceCell<Vec<(LNTerm, LNTerm)>>,
    active_nat_inconsistent: std::cell::OnceCell<bool>,
}

impl<'a> StoreValuation<'a> {
    pub(crate) fn new(reducible: &'a FastSet<FunSym>, store: &'a SubtermStore) -> Self {
        Self {
            reducible,
            store,
            active: std::cell::OnceCell::new(),
            active_nat_inconsistent: std::cell::OnceCell::new(),
        }
    }

    pub(crate) fn is_true_false(&self, small: &LNTerm, big: &LNTerm) -> Option<bool> {
        use tamarin_term::lterm::{is_msg_var, sort_of_lnterm, LSort};
        if let Some(verdict) = is_true_false(self.reducible, small, big) {
            return Some(verdict);
        }
        let is_inside = self
            .store
            .subterms
            .iter()
            .chain(self.store.solved_subterms.iter())
            .any(|c| &c.small == small && &c.big == big);
        let is_negated_inside = self
            .store
            .neg_subterms
            .iter()
            .any(|(s, t)| s == small && t == big);
        if is_inside != is_negated_inside {
            return Some(is_inside);
        }
        let active = self.active.get_or_init(|| {
            self.store
                .subterms
                .iter()
                .map(|c| (c.small.clone(), c.big.clone()))
                .collect()
        });
        if has_subterm_cycle_with_pairs(self.reducible, active, (small, big)) {
            return Some(false);
        }
        // A pair that is not natural-number shaped adds no ordering edge, so
        // only the store's own consistency can reject it.
        let natural = (sort_of_lnterm(small) == LSort::Nat || is_msg_var(small))
            && sort_of_lnterm(big) == LSort::Nat;
        let nat_inconsistent = *self
            .active_nat_inconsistent
            .get_or_init(|| !nat_subterms_consistent(active))
            || natural && {
                let mut relation = active.clone();
                if !relation.iter().any(|(s, t)| s == small && t == big) {
                    relation.push((small.clone(), big.clone()));
                }
                !nat_subterms_consistent(&relation)
            };
        nat_inconsistent.then_some(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::{pair_sym, NoEqSym};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_no_eq, Term};
    use tamarin_term::vterm::Lit;

    fn var(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
    }

    /// `h(t)` is the stand-in reducible head.  `h` is reducible only when
    /// [`reducible`] below puts it in the set.
    fn h(t: LNTerm) -> LNTerm {
        f_app_no_eq(hash_sym(), vec![t])
    }

    fn hash_sym() -> NoEqSym {
        tamarin_term::builtin::hash_sym()
    }

    /// `<a, b>` is always irreducible, so it never stops the walk.
    fn pair(a: LNTerm, b: LNTerm) -> LNTerm {
        tamarin_term::term::f_app(FunSym::NoEq(pair_sym()), vec![a, b])
    }

    /// The reducible set that contains `h` alone.
    fn reducible_h() -> FastSet<FunSym> {
        [FunSym::NoEq(hash_sym())].into_iter().collect()
    }

    fn nat_var(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Nat, 0)))
    }

    /// `%x %+ %y %+ ...` — the AC smart constructor collapses a singleton.
    fn nat_plus(args: Vec<LNTerm>) -> LNTerm {
        tamarin_term::term::f_app_ac(tamarin_term::function_symbols::AcSym::NatPlus, args)
    }

    fn nat_one() -> LNTerm {
        f_app_no_eq(tamarin_term::function_symbols::nat_one_sym(), vec![])
    }

    /// The AC-recurse arm is the only one that draws, and no test below
    /// reaches it.
    fn no_fresh(_sort: LSort) -> LVar {
        LVar::new("newVar", LSort::Msg, 0)
    }

    /// CR-rule S_nat (SubtermStore.hs) hands `NatSubtermD` the pair
    /// `processACSubterm NatPlus` returns, i.e. with the summands both sides
    /// share removed: `%x %+ %1 ⊏ %y %+ %1` becomes the leaf `%x ⊏ %y`.
    /// Keeping the original pair leaves the shared `%1` on both sides, and
    /// `simpSplitNegSt` then stores — and renders — the unreduced goal.
    #[test]
    fn recursive_split_reduces_a_nat_subterm_leaf() {
        let none: FastSet<FunSym> = FastSet::default();
        let x = nat_var("x");
        let y = nat_var("y");
        let small = nat_plus(vec![x.clone(), nat_one()]);
        let big = nat_plus(vec![y.clone(), nat_one()]);
        let mut mk_fresh = no_fresh;
        assert_eq!(
            split_subterm(&none, true, &small, &big, &mut mk_fresh),
            vec![SubtermSplit::NatSubtermD(x, y)]
        );
    }

    /// `splitSubterm` returns `S.toList` of a `S.Set SubtermSplit`
    /// (SubtermStore.hs), so the leaves come out in the derived
    /// constructor order — every `SubtermD` before every `EqualD` — and not
    /// in the order `eqOrSubterm` (SubtermStore.hs) pushed them per
    /// argument.
    #[test]
    fn recursive_split_lists_its_leaves_in_set_order() {
        let none: FastSet<FunSym> = FastSet::default();
        let x = var("x");
        let a = var("a");
        let b = var("b");
        let mut mk_fresh = no_fresh;
        let leaves = split_subterm(&none, true, &x, &pair(b.clone(), a.clone()), &mut mk_fresh);
        assert_eq!(
            leaves,
            vec![
                SubtermSplit::SubtermD(x.clone(), a.clone()),
                SubtermSplit::SubtermD(x.clone(), b.clone()),
                SubtermSplit::EqualD(x.clone(), a),
                SubtermSplit::EqualD(x, b),
            ]
        );
    }

    /// A store starts consistent and empty.  `add` records the constraint as
    /// not propagated.  The propagation pass selects constraints by that
    /// flag.  An `add` that marks them propagated therefore discards every
    /// new `t1 ⊏ t2` without a message.
    #[test]
    fn add_records_an_unpropagated_constraint() {
        let s = SubtermStore::empty();
        assert!(!s.is_false());
        assert!(s.subterms.is_empty());

        let mut s = s;
        s.add(var("x"), var("y"));
        assert_eq!(s.subterms.len(), 1);
        assert_eq!(s.subterms[0].small, var("x"));
        assert_eq!(s.subterms[0].big, var("y"));
        assert!(!s.subterms[0].propagated);
    }

    /// `elemNotBelowReducible` (Term/Term.hs) counts an occurrence in
    /// `outer` only along a path that never crosses a reducible head.  The
    /// `inner == outer` base case applies before the function looks at the
    /// head.
    #[test]
    fn elem_not_below_reducible_stops_at_a_reducible_head() {
        let none: FastSet<FunSym> = FastSet::default();
        let x = var("x");
        let y = var("y");
        // The first assertion is the identity case.  The second is an
        // occurrence under an irreducible head.
        assert!(elem_not_below_reducible(&none, &x, &x));
        assert!(elem_not_below_reducible(
            &none,
            &x,
            &pair(x.clone(), y.clone())
        ));
        // This term does not occur at all.
        assert!(!elem_not_below_reducible(&none, &x, &y));
        // A Lit `outer` that is not `inner` has no arguments to recurse into.
        assert!(!elem_not_below_reducible(&reducible_h(), &x, &y));
        // The term is the same, but now the head is reducible.  A rewrite can
        // make the occurrence disappear, so the occurrence does not count.
        assert!(elem_not_below_reducible(&none, &x, &h(x.clone())));
        assert!(!elem_not_below_reducible(&reducible_h(), &x, &h(x.clone())));
        // The block applies to one position, not to the complete term.  `x`
        // under `h` does not count.  `y` beside it still counts.
        let mixed = pair(h(x.clone()), y.clone());
        assert!(!elem_not_below_reducible(&reducible_h(), &x, &mixed));
        assert!(elem_not_below_reducible(&reducible_h(), &y, &mixed));
        // The identity base case applies even when the head is reducible.
        assert!(elem_not_below_reducible(
            &reducible_h(),
            &h(x.clone()),
            &h(x)
        ));
    }

    /// `hasSubtermCycle` (SubtermStore.hs) is the contradiction test
    /// for the CR-rule S_chain.  An edge `(t, x)` reaches `(t', x')` when `x`
    /// occurs in `t'` and not below a reducible head.  One edge pair can
    /// therefore be a cycle or not, according to the reducible set.
    #[test]
    fn has_subterm_cycle_follows_only_irreducible_occurrences() {
        let none: FastSet<FunSym> = FastSet::default();
        let store = |edges: &[(LNTerm, LNTerm)]| {
            let mut s = SubtermStore::empty();
            for (small, big) in edges {
                s.add(small.clone(), big.clone());
            }
            s
        };
        let (a, b, c) = (var("a"), var("b"), var("c"));

        // There are no constraints, so there is nothing to cycle through.
        assert!(!has_subterm_cycle(&none, &SubtermStore::empty()));
        // Here a ⊏ b and b ⊏ a.  Each edge's big side is the other edge's
        // small side.
        assert!(has_subterm_cycle(
            &none,
            &store(&[(a.clone(), b.clone()), (b.clone(), a.clone())])
        ));
        // Disjoint edges never reach each other.
        assert!(!has_subterm_cycle(
            &none,
            &store(&[(a.clone(), b.clone()), (c.clone(), var("d"))])
        ));
        // This is the same two-edge shape.  The back edge's small side wraps
        // `b` under `h`.  The shape is a cycle while `h` rewrites nothing.
        // It is not a cycle when `h` is reducible, because a rewrite can
        // remove the occurrence.
        let via_h = store(&[(a.clone(), b.clone()), (h(b), a)]);
        assert!(has_subterm_cycle(&none, &via_h));
        assert!(!has_subterm_cycle(&reducible_h(), &via_h));
    }

    /// `isTrueFalse reducible (Just sst)` decides a relation from store
    /// membership, and rejects one whose hypothetical insertion closes a cycle.
    #[test]
    fn store_valuation_uses_membership_and_hypothetical_cycles() {
        let none: FastSet<FunSym> = FastSet::default();
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let mut store = SubtermStore::empty();
        store.add(a.clone(), b.clone());
        store.add_neg(c.clone(), b.clone());
        let valuation = StoreValuation::new(&none, &store);
        assert_eq!(valuation.is_true_false(&a, &b), Some(true));
        assert_eq!(valuation.is_true_false(&c, &b), Some(false));
        // b ⊏ a would close a ⊏ b ⊏ a.
        assert_eq!(valuation.is_true_false(&b, &a), Some(false));
        assert_eq!(valuation.is_true_false(&a, &c), None);
    }

    /// [`SortedPairSet`] takes the place of HS's `S.Set (LNTerm, LNTerm)`.
    /// The `neg_subterms \ old_neg_subterms` change detection calls
    /// `binary_search` on it.  The sorted-unique invariant must therefore
    /// hold for every insertion order.  `insert` must also report whether the
    /// pair is new.  That boolean is `add_neg`'s "this negative subterm is
    /// new" answer.
    #[test]
    fn sorted_pair_set_keeps_the_hs_set_invariant() {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let mut s = SortedPairSet::default();
        // The test inserts the pairs in descending order.  The set must come
        // out in ascending order.
        assert!(s.insert((c.clone(), a.clone())));
        assert!(s.insert((b.clone(), a.clone())));
        assert!(s.insert((a.clone(), b.clone())));
        assert!(!s.insert((b.clone(), a.clone())), "duplicates are no-ops");
        assert_eq!(s.len(), 3);
        assert!(s.windows(2).all(|w| w[0] < w[1]), "sorted: {:?}", &*s);
        // This is the lookup that `add_neg` and the change detection perform.
        assert!(s.binary_search(&(b.clone(), a.clone())).is_ok());
        // `rebuild_from` builds the same set from the opposite order.
        assert_eq!(
            SortedPairSet::rebuild_from(vec![
                (a.clone(), b.clone()),
                (b.clone(), a.clone()),
                (c.clone(), a.clone()),
                (a.clone(), b.clone()),
            ]),
            s
        );
        // A removal at a position found by the search leaves the rest sorted.
        let pos = s.binary_search(&(b.clone(), a.clone())).unwrap();
        assert_eq!(s.remove_at(pos), (b, a.clone()));
        assert_eq!(s.len(), 2);
        assert!(s.windows(2).all(|w| w[0] < w[1]));
        assert!(s.binary_search(&(c, a)).is_ok());
    }

    /// `conjoinSubtermStores` (SubtermStore.hs) unions all five HS
    /// fields.  These are the positive, solved, negative and old-negative
    /// sets, plus an OR on the contradiction flag.  A merge of two branches
    /// loses constraints without a message if the code drops any one of them.
    #[test]
    fn conjoin_unions_every_hs_field() {
        let (a, b, c) = (var("a"), var("b"), var("c"));
        let solved = |small: LNTerm, big: LNTerm| SubtermConstraint {
            small,
            big,
            propagated: true,
        };

        let mut left = SubtermStore::empty();
        left.add(a.clone(), b.clone());
        left.solved_subterms.push(solved(a.clone(), c.clone()));
        left.add_neg(a.clone(), b.clone());
        left.old_neg_subterms.insert((a.clone(), b.clone()));

        let mut right = SubtermStore::empty();
        // The right store has one positive constraint that the left store also
        // has, and one new one.  The union must not duplicate the shared one.
        right.subterms.push(SubtermConstraint {
            small: a.clone(),
            big: b.clone(),
            propagated: true,
        });
        right.add(b.clone(), c.clone());
        right.solved_subterms.push(solved(b.clone(), c.clone()));
        right.add_neg(c.clone(), a.clone());
        right.old_neg_subterms.insert((c.clone(), a.clone()));
        right.contradictory = true;

        left.conjoin(&right);
        assert_eq!(
            left.subterms
                .iter()
                .map(|s| (s.small.clone(), s.big.clone()))
                .collect::<Vec<_>>(),
            vec![(a.clone(), b.clone()), (b.clone(), c.clone())],
            "positive subterms union WITHOUT duplicating the shared one"
        );
        assert_eq!(
            left.solved_subterms,
            vec![solved(a.clone(), c.clone()), solved(b.clone(), c.clone())]
        );
        assert!(left.is_false(), "isContradictory is an OR");
        // Both set-valued fields union, and both stay sorted.
        for set in [&left.neg_subterms, &left.old_neg_subterms] {
            assert_eq!(set.len(), 2);
            assert!(set.windows(2).all(|w| w[0] < w[1]), "sorted: {:?}", &**set);
            assert!(set.binary_search(&(a.clone(), b.clone())).is_ok());
            assert!(set.binary_search(&(c.clone(), a.clone())).is_ok());
        }
    }

    // =========================================================================
    // HasFrees instances
    // =========================================================================

    use tamarin_term::lterm::frees_list;

    /// A message variable named `x` distinguished by its index, so `Ord`
    /// follows the index (LTerm.hs) and a walk order is readable off
    /// the indices alone.
    fn xv(idx: u64) -> LVar {
        LVar::new("x", LSort::Msg, idx)
    }

    fn xt(idx: u64) -> LNTerm {
        Term::Lit(Lit::Var(xv(idx)))
    }

    fn cst(small: u64, big: u64, propagated: bool) -> SubtermConstraint {
        SubtermConstraint {
            small: xt(small),
            big: xt(big),
            propagated,
        }
    }

    /// Add 100 to the index of every variable the map reaches.  The rename is
    /// injective, so a field the map leaves alone keeps its own indices.
    fn shifted<T: HasFrees>(t: T) -> T {
        t.map_free(&mut |v: LVar| LVar::new(v.name, v.sort, v.idx + 100))
    }

    /// A store whose every constraint carries its own variables, with the
    /// positive and solved constraints pushed in the reverse of their
    /// `(small, big)` order.
    fn walk_store() -> SubtermStore {
        SubtermStore {
            subterms: vec![cst(6, 7, true), cst(2, 3, false)],
            solved_subterms: vec![cst(9, 10, false), cst(4, 5, true)],
            contradictory: true,
            neg_subterms: SortedPairSet::rebuild_from(vec![(xt(11), xt(12))]),
            old_neg_subterms: SortedPairSet::rebuild_from(vec![(xt(13), xt(14))]),
        }
    }

    /// The port's element of the positive and solved subterm sets walks the
    /// small side before the big one (LTerm.hs) and carries its
    /// `propagated` marker through the map.
    #[test]
    fn subterm_constraint_visits_small_then_big_and_keeps_propagated() {
        let c = cst(1, 2, true);
        assert_eq!(frees_list(&c), vec![xv(1), xv(2)]);
        assert_eq!(shifted(c), cst(101, 102, true));
    }

    /// `instance HasFrees SubtermStore`'s fold (SubtermStore.hs): the
    /// negative subterms first — before the positive ones that hold smaller
    /// variables — then the positive and the solved ones, each in `(small,
    /// big)` order rather than the insertion order the fixture stores.
    #[test]
    fn subterm_store_walks_negative_subterms_first_and_each_field_sorted() {
        assert_eq!(
            frees_list(&walk_store()),
            vec![
                xv(11),
                xv(12),
                xv(2),
                xv(3),
                xv(6),
                xv(7),
                xv(4),
                xv(5),
                xv(9),
                xv(10),
            ]
        );
    }

    /// The map (SubtermStore.hs) rewrites the three walked fields and
    /// carries `contradictory` and `old_neg_subterms` over untouched.  The two
    /// `Vec`-backed fields keep their insertion order and their `propagated`
    /// markers; `neg_subterms` goes back through `SortedPairSet::rebuild_from`.
    #[test]
    fn subterm_store_map_keeps_storage_order_and_the_untouched_fields() {
        let mapped = shifted(walk_store());
        assert_eq!(
            mapped.subterms,
            vec![cst(106, 107, true), cst(102, 103, false)]
        );
        assert_eq!(
            mapped.solved_subterms,
            vec![cst(109, 110, false), cst(104, 105, true)]
        );
        assert_eq!(
            &*mapped.neg_subterms,
            &[(xt(111), xt(112))],
            "the negative subterms are remapped"
        );
        assert_eq!(
            &*mapped.old_neg_subterms,
            &[(xt(13), xt(14))],
            "oldNegSubterms is carried over by `pure`"
        );
        assert!(mapped.contradictory);
    }

    /// HS derives `Ord SubtermStore` over `_negSubterms`, `_posSubterms`,
    /// `_solvedSubterms`, `_isContradictory`, `_oldNegSubterms`
    /// (SubtermStore.hs).  The port declares `subterms` first and
    /// `neg_subterms` fourth, so a pair whose negative and positive sets
    /// disagree in opposite directions settles on the negative one.
    #[test]
    fn subterm_store_hs_comparison_follows_the_hs_field_order() {
        let store = |neg: u64, pos: u64| SubtermStore {
            subterms: vec![cst(pos, pos + 1, false)],
            neg_subterms: SortedPairSet::rebuild_from(vec![(xt(neg), xt(neg + 1))]),
            ..SubtermStore::empty()
        };
        assert_eq!(
            store(20, 31).cmp_hs(&store(22, 30)),
            std::cmp::Ordering::Less
        );
    }

    /// `propagated` is port-only: HS holds the positive and solved sets as
    /// `S.Set (LNTerm, LNTerm)` (SubtermStore.hs), so two stores that
    /// differ only in that marker compare equal.
    #[test]
    fn subterm_store_hs_comparison_ignores_the_propagated_marker() {
        let store = |propagated: bool| SubtermStore {
            subterms: vec![cst(2, 3, propagated)],
            solved_subterms: vec![cst(4, 5, propagated)],
            ..SubtermStore::empty()
        };
        let plain = store(false);
        let propagated = store(true);
        assert_ne!(plain, propagated, "Rust equality includes the marker");
        assert_eq!(plain.cmp_hs(&propagated), std::cmp::Ordering::Equal);
    }
}
