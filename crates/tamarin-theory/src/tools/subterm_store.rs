// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Tools.SubtermStore`.
//!
//! The subterm store accumulates `t1 << t2` constraints during proof
//! search, propagating them and detecting contradictions. This module
//! holds the store data type plus the pieces the solver calls directly:
//! constraint accumulation (`add`/`add_neg`), `conjoin` (HS
//! `conjoinSubtermStores`), the subterm-cycle check `has_subterm_cycle`
//! (HS `hasSubtermCycle`, the CR-rule S_chain test), and the
//! `elem_not_below_reducible` predicate (HS `Term.elemNotBelowReducible`).
//! The simplification passes that depend on AC-unification —
//! `simpSubtermStore`, `simpSplitNegSt`, and the recursive `splitSubterm`
//! — are ported in `constraint::solver::simplify` rather than here.

use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::{HasFrees, LNTerm, LVar};
use tamarin_term::term::Term;
use tamarin_utils::FastSet;

/// One stored subterm constraint: `small ⊏ big`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubtermConstraint {
    pub small: LNTerm,
    pub big: LNTerm,
    /// Whether this constraint has already been propagated.
    pub propagated: bool,
}

/// One element of the `_posSubterms` / `_solvedSubterms` sets, which HS holds
/// as `S.Set (LNTerm, LNTerm)` (SubtermStore.hs:90-96), so the walk is the
/// pair instance (LTerm.hs:855-860): the small side then the big one.
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
/// slice `Deref`.  Derives mirror `SubtermStore`'s so it slots into the derived
/// impls (order-sensitive `PartialEq` is exact because the set is always sorted).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
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
/// (SubtermStore.hs:90-96):
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
    /// add_neg — HS `_oldNegSubterms` (SubtermStore.hs:90-97, see line 95).  Only the
    /// `simpSplitNegSt` pass updates it; the set difference
    /// `neg_subterms \ old_neg_subterms` is the change-detection
    /// mechanism deciding which negative subterms get (re-)split.
    pub old_neg_subterms: SortedPairSet,
}

impl SubtermStore {
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

    /// `addNegSubterm` (SubtermStore.hs:125-126): set-insert into
    /// negSubterms.  Sorted insert keeps HS `S.toList` iteration order.
    /// Returns true if the pair was newly added.
    pub fn add_neg(&mut self, small: LNTerm, big: LNTerm) -> bool {
        self.neg_subterms.insert((small, big))
    }

    pub fn is_false(&self) -> bool {
        self.contradictory
    }

    /// `conjoinSubtermStores` — HS-faithful port of
    /// `Theory.Tools.SubtermStore.conjoinSubtermStores` (SubtermStore.hs:108-110):
    /// ```haskell
    /// conjoinSubtermStores (SubtermStore a1 b1 c1 d1 e1) (SubtermStore a2 b2 c2 d2 e2)
    ///   = SubtermStore (a1 `S.union` a2) (b1 `S.union` b2)
    ///                  (c1 `S.union` c2) (d1 || d2) (e1 `S.union` e2)
    /// ```
    /// All five HS fields union per HS semantics: neg/pos/solved set-union,
    /// `isContradictory` OR, `oldNegSubterms` set-union.
    pub fn conjoin(&mut self, other: &SubtermStore) {
        for st in &other.subterms {
            if !self.subterms.contains(st) {
                self.subterms.push(st.clone());
            }
        }
        for st in &other.solved_subterms {
            if !self.solved_subterms.contains(st) {
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

/// `instance HasFrees SubtermStore` (SubtermStore.hs:546-557): the negative
/// subterms, then the positive ones, then the solved ones.  `contradictory`
/// and `old_neg_subterms` are carried over by `pure` — HS states at
/// SubtermStore.hs:95 that `oldNegSubterms` is the copy `apply`/`HasFrees`
/// leave alone.
///
/// HS holds all three walked fields as `S.Set (LNTerm, LNTerm)`, so its fold
/// sees them in ascending pair order (LTerm.hs:898-901).  `neg_subterms` is
/// stored sorted, and the walk sorts references to the two `Vec`-backed
/// fields by `(small, big)`.  The map rebuilds `neg_subterms` through
/// [`SortedPairSet::rebuild_from`], which is the `S.fromList` of the HS set
/// map (LTerm.hs:903); it rewrites `subterms` and `solved_subterms` where
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
/// (SubtermStore.hs:90-96).  `SubtermConstraint` carries a `propagated`
/// marker that is not part of that pair and so is no `Ord` key.
fn sorted_by_pair(cs: &[SubtermConstraint]) -> Vec<&SubtermConstraint> {
    let mut out: Vec<&SubtermConstraint> = cs.iter().collect();
    out.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    out
}

/// `elemNotBelowReducible reducible inner outer` — port of Haskell's
/// `Term.Term.elemNotBelowReducible` (`Term/Term.hs:273-279`).  True iff
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
/// `Theory.Tools.SubtermStore.hasSubtermCycle` (`SubtermStore.hs:223-244`).
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
    // Build the dag from positive subterms — every active (small, big)
    // constraint is an edge in the dependency dag.
    let dag: Vec<(LNTerm, LNTerm)> = store
        .subterms
        .iter()
        .map(|c| (c.small.clone(), c.big.clone()))
        .collect();
    if dag.is_empty() {
        return false;
    }
    let mut visited: std::collections::BTreeSet<(LNTerm, LNTerm)> =
        std::collections::BTreeSet::new();
    for edge in &dag {
        let mut parents = std::collections::BTreeSet::new();
        if find_loop(reducible, &dag, edge, &mut parents, &mut visited).is_none() {
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

    /// `elemNotBelowReducible` (Term/Term.hs:273-279) counts an occurrence in
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

    /// `hasSubtermCycle` (SubtermStore.hs:223-244) is the contradiction test
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

    /// `conjoinSubtermStores` (SubtermStore.hs:108-110) unions all five HS
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
        right.add(a.clone(), b.clone());
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
    /// follows the index (LTerm.hs:546-548) and a walk order is readable off
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
    /// small side before the big one (LTerm.hs:855-860) and carries its
    /// `propagated` marker through the map.
    #[test]
    fn subterm_constraint_visits_small_then_big_and_keeps_propagated() {
        let c = cst(1, 2, true);
        assert_eq!(frees_list(&c), vec![xv(1), xv(2)]);
        assert_eq!(shifted(c), cst(101, 102, true));
    }

    /// `instance HasFrees SubtermStore`'s fold (SubtermStore.hs:548-549): the
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

    /// The map (SubtermStore.hs:552-557) rewrites the three walked fields and
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
}
