// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.LTerm.renamePrecise` applied to a `System`.
//!
//! Haskell `cleanup` (ProofMethod.hs):
//! ```haskell
//! cleanup s = L.set sSubst emptySubst (Precise.evalFresh (renamePrecise s) Precise.nothingUsed)
//! ```
//!
//! `renamePrecise` walks every free `LVar` in a value in a deterministic
//! traversal order and rebinds each *unique* `LVar` to a freshly-allocated
//! `LVar` keyed by name. The result is canonical for two values that differ
//! only by variable indices. `process` (ProofMethod.hs) relies on that
//! canonical form when it `removeRedundantCases`-collapses variant-divergent
//! case maps and when the `Simplify` method compares `sys' /= cleanup sys`;
//! note `M.fromListWith (error "case names not unique")` there *errors* on a
//! duplicate case name rather than deduping.

use tamarin_term::apply::Apply;
use tamarin_term::bind::Bindings;
use tamarin_term::lterm::{LNTerm, LVar};
use tamarin_term::subst::Subst;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;
use tamarin_utils::fresh::PreciseFreshState;

use crate::constraint::constraints::Goal;
use crate::constraint::system::System;
use crate::guarded::{subst_guarded_cow, Guarded};

/// Canonicalise the free `LVar`s of `sys` so that two systems differing
/// only by variable numbering compare equal.
///
/// Mirrors Haskell's `renamePrecise` over the `System` record.
pub fn rename_precise_system(sys: &mut System) {
    // Rewrites every free LVar through a deterministic alpha-rename;
    // the resulting max-var-idx is almost always smaller.  The full
    // cache is invalidated after Phase 1, and only when some binding is
    // a genuine remap (`bindings.changed()`): an all-identity rename leaves
    // every value byte-identical — Phase 2 then only re-sorts fields and
    // dedups EQUAL values (the HS `S.fromList` effects), neither of
    // which can change the max free-var idx, so the cache stays exact.
    // The node-component cache is invalidated ONLY on the real node
    // rewrite in Phase 2 step 1: an all-identity NODE rename (a weaker
    // condition, snapshotted as `nodes_identity` below) already leaves
    // the nodes byte-identical even when later fields are remapped.
    let mut fresh = PreciseFreshState::nothing_used();
    let mut bindings = Bindings::new();

    // ----------------------------------------------------------------------
    // Phase 1 — walk every free LVar in `instance HasFrees System`'s order so
    // the import-binding map is populated independent of how we apply later.
    //
    // The walk MUST match HS's, because `bindings.import` allocates per-name
    // idxs in VISIT order: formulas are visited before goals, so a free LVar
    // shared between a formula and a goal `Disj` is bound to the same fresh
    // idx HS assigns it, and the `Vec`-backed fields are visited in their
    // `Data.Set` / `Data.Map` order rather than in insertion order.
    // ----------------------------------------------------------------------
    let mut nodes_identity = false;
    sys.for_each_free_with_node_boundary(
        &mut (&mut bindings, &mut fresh, &mut nodes_identity),
        |state, v| {
            state.0.import(v, state.1);
        },
        |state| *state.2 = !state.0.changed(),
    );

    // ----------------------------------------------------------------------
    // Phase 2 — apply the renaming map.
    //
    // For LVar-only fields we look up directly. For term-bearing fields we
    // build a `Subst` (LVar → Var-term) and apply via `apply_vterm`; the
    // guarded formulas take the same `Subst`.
    // ----------------------------------------------------------------------

    // `bindings.changed()` covers EVERY field (Phase 1 walks them all), so a
    // false value proves the whole rename is the identity — see the
    // invalidation note at the top of this function.
    let any_remap = bindings.changed();
    if any_remap {
        sys.invalidate_max_var_idx_cache();
        // Whole-system alpha-rename: no inherited verified-no-op verdict
        // survives a domain/range rename.  The Phase-2
        // eq-store rewrite (via `eq_store_mut`) already bumps `subst_stamp`;
        // clear the marker explicitly too.
        sys.clear_subst_marker();
    }

    let term_subst: Subst<tamarin_term::lterm::Name, LVar> = Subst::from_list(
        bindings
            .iter()
            .map(|(old, new)| (old, Term::Lit(Lit::Var(new)))),
    );
    // A `Disj` goal's alternatives are renamed one pass each, with no
    // fixpoint and no re-normalisation: the rename is a bijection on
    // variables, so one pass reaches every leaf and cannot make two
    // alternatives equal.
    let disj = |alts: &[Guarded]| -> Option<Vec<Guarded>> {
        tamarin_utils::cow::cow_map_vec(alts, |g| subst_guarded_cow(g, &term_subst))
    };
    // Phase 2 applies this ONE fixed variable-to-variable substitution to
    // every node, goal, edge and stored term, which is what the pass's hashed
    // leaf view is for.  The cached-bloom fact fast path is off: the domain is
    // every free variable of the system, so it could only ever skip a
    // variable-free fact.
    let pass = crate::apply::SystemSubst::new(&term_subst, false, &disj);

    // `from_list` above drops identity `x ~> x` entries, so the substitution
    // rewrites a variable exactly where the binding map remaps it.
    let map_var = |v: LVar| -> LVar { bindings.get(&v).unwrap_or(v) };

    // 1. Nodes — id + rule.
    //
    // HS-faithful: `mapFrees (M.Map NodeId RuleACInst)`
    // = `fmap M.fromList . mapFrees f . M.toList` (Term/LTerm.hs:905-914, see line 914).
    // `M.fromList` builds a Map keyed by Ord NodeId, so post-rename the
    // entries land in ascending NEW NodeId order.  Without this sort,
    // RS's `Vec<(NodeId, _)>` keeps the pre-rename insertion order — which
    // diverges from HS for any downstream consumer that walks `sys.nodes`
    // in storage order rather than re-sorting (most do their own sort, but
    // some iterate directly).  Mirror HS by sorting here.
    //
    // Identity fast path: when the node rename is the identity
    // (`nodes_identity`), the substitution binds no node id and no rule
    // variable, so the per-rule walk would rewrite nothing.  The only
    // remaining effect is the ascending-NodeId re-sort; if `sys.nodes` is
    // already so sorted the whole step is a no-op and the `Arc` stays shared
    // with the parent (no deep clone, no rebuild), and — since the nodes are
    // byte-identical — the node-component max cache stays valid.
    if nodes_identity {
        // `is_sorted` by NodeId (O(n)); `windows` sidesteps any is_sorted_by
        // API-version dependency.  A stable `sort_by(NodeId)` over an
        // already-non-decreasing Vec is a no-op, so the sort may be skipped.
        let already_sorted = sys.nodes.windows(2).all(|w| w[0].0 <= w[1].0);
        if !already_sorted {
            // Identity rename ⇒ the (id, rule) multiset is unchanged; only the
            // HS `M.fromList` ascending-NodeId storage order needs restoring.
            // Node-component max is unchanged, so its cache stays valid.
            let mut nodes = std::sync::Arc::unwrap_or_clone(std::mem::take(
                &mut sys.content_mut_untracked().nodes,
            ));
            nodes.sort_by_key(|a| a.0);
            sys.content_mut_untracked().nodes = std::sync::Arc::new(nodes);
        }
    } else {
        // Real rename: node var idxs are remapped (almost always lower), so
        // the node-component max can drop — invalidate its cache here (the
        // one site that actually rewrites nodes).
        sys.invalidate_node_max_cache();
        let nodes =
            std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.content_mut_untracked().nodes));
        let mut renamed: Vec<(
            crate::constraint::constraints::NodeId,
            crate::rule::RuleACInst,
        )> = nodes
            .into_iter()
            .map(|(id, rule)| (id.apply(&pass), rule.apply(&pass)))
            .collect();
        renamed.sort_by_key(|a| a.0);
        sys.content_mut_untracked().nodes = std::sync::Arc::new(renamed);
    }

    // 2. Edges.
    for e in sys.content_mut_untracked().edges.iter_mut() {
        if let Some(new_edge) = e.apply_changed(&pass) {
            *e = new_edge;
        }
    }
    // Dedup after rename — sort + dedup (matches subst_system).
    let mut tmp: Vec<_> = std::mem::take(&mut sys.content_mut_untracked().edges);
    tmp.sort();
    tmp.dedup();
    sys.content_mut_untracked().edges = tmp;

    // 3. Last atom.
    if let Some(la) = sys.content_mut_untracked().last_atom.take() {
        sys.content_mut_untracked().last_atom = Some(la.apply(&pass));
    }

    // 4. Less atoms.
    //
    // HS-faithful dedup post-rename: HS's `sLessAtoms :: Set LessAtom`
    // is reconstructed via `S.map (apply subst)` on every rewrite,
    // collapsing duplicates whose images coincide.  Mirror by deduping
    // after the in-place rename.  See `subst_system_once`'s comment for
    // detailed rationale.
    // HS `mapFrees (S.Set LessAtom)`: sort + dedup post-rename
    // (Term/LTerm.hs:898-903, see line 903 `fmap S.fromList . mapFrees f . S.toList`).
    let mut new_less: Vec<crate::constraint::constraints::LessAtom> =
        Vec::with_capacity(sys.less_atoms.len());
    for la in std::mem::take(&mut sys.content_mut_untracked().less_atoms) {
        new_less.push(la.apply(&pass));
    }
    // Sort + dedup (O(n log n)), matching HS's `S.fromList` over the renamed
    // set rather than an O(n^2) membership scan.
    new_less.sort();
    new_less.dedup();
    sys.content_mut_untracked().less_atoms = new_less;

    // 5. Goals — per-variant rewrite.
    let goals =
        std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.content_mut_untracked().goals));
    let mut new_goals: Vec<(Goal, crate::constraint::system::GoalStatus)> = goals
        .into_iter()
        .map(|(g, st)| (g.apply(&pass), st))
        .collect();
    // HS-faithful: `mapFrees (M.Map Goal GoalStatus)`
    // = `fmap M.fromList . mapFrees f . M.toList` (Term/LTerm.hs:905-914, see line 914).
    // `M.fromList` builds a Map keyed by Ord Goal, so post-rename the
    // entries land in ascending NEW Goal order.
    //
    // Sort + dedup (O(n log n)) instead of an O(n^2) membership scan.  The
    // dedup key is the goal alone, ignoring the status: `M.fromList` builds
    // a `Map Goal GoalStatus`, which collapses entries sharing a goal.
    new_goals.sort_by(|a, b| a.0.cmp(&b.0));
    new_goals.dedup_by(|a, b| a.0 == b.0);
    sys.content_mut_untracked().goals = std::sync::Arc::new(new_goals);

    // 6. Formulas / solved / lemmas — via the same rename `Subst`.
    //
    // HS-faithful: `_sFormulas` / `_sSolvedFormulas` / `_sLemmas` are
    // `S.Set LNGuarded`. `mapFrees (S.Set a) = fmap S.fromList . mapFrees
    // f . S.toList` (Term/LTerm.hs:898-903, see line 903) — rebuilds the set after mapping,
    // so post-rename entries are sorted by NEW Ord Guarded AND
    // collision-deduped.  Mirror by sorting+deduping after the in-place
    // rename: post-rename two formulas that became equal collapse.
    let sort_dedup_guarded = |v: &mut Vec<std::sync::Arc<crate::guarded::Guarded>>| {
        // COW: only the formulas whose leaves actually change are rebuilt;
        // `Some(nf)` is byte-identical to the eager `subst_guarded`, and a
        // no-effect (identity) rename leaves `*f` untouched.  The
        // sort+dedup below runs even when the COW loop rebuilt nothing —
        // HS's `S.fromList` rebuild happens under an identity rename too,
        // and intervening passes may have left the Vec unsorted.
        for f in v.iter_mut() {
            if let Some(nf) = subst_guarded_cow(f, &term_subst) {
                *f = std::sync::Arc::new(nf);
            }
        }
        v.sort();
        v.dedup();
    };
    sort_dedup_guarded(sys.formulas_mut_untracked());
    sort_dedup_guarded(sys.solved_formulas_mut_untracked());
    sort_dedup_guarded(&mut sys.content_mut_untracked().lemmas);

    // 7. eq_store — rewrite the subst (dom + range) and the conj.
    let old_subst = std::mem::replace(
        &mut sys.eq_store_mut().subst,
        crate::tools::equation_store::LNSubst::empty(),
    );
    let pairs: Vec<(LVar, LNTerm)> = old_subst
        .to_list()
        .into_iter()
        .map(|(k, v)| (map_var(k), v.apply(&pass)))
        .collect();
    sys.eq_store_mut().subst = Subst::from_list(pairs);

    // HS-faithful: `HasFrees (SubstVFresh n LVar)` only maps DOMAIN
    // (keys), NOT values.  From Term.Substitution.SubstVFresh.hs:196-202:
    //
    //   instance HasFrees (SubstVFresh n LVar) where
    //       foldFrees f = foldFrees f . M.keys . svMap
    //       foldFreesOcc _ _ = const mempty
    //       mapFrees f =
    //           (substFromListVFresh <$>) . traverse mapDomain
    //                                     . substToListVFresh
    //         where mapDomain (v, t) = (,t) <$> mapFrees f v
    //
    // So renamePrecise renames variant subst KEYS but PRESERVES the
    // witness idxs in VALUES.  This preserves the variant witness idxs at
    // perform_split time — which is what gives HS the sort-discriminating
    // idx differences across variants.
    for d in sys.eq_store_mut().conj.iter_mut() {
        for s in d.substs.iter_mut() {
            let pairs: Vec<(LVar, LNTerm)> = s
                .to_list()
                .into_iter()
                .map(|(k, v)| (map_var(k), v)) // keep VALUE unchanged
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }
    // HS-faithful: `mapFrees` over the eqsConj's `S.Set LNSubstVFresh`
    // is `fmap S.fromList . mapFrees f . S.toList` (HasFrees (S.Set a)),
    // so after renaming the domain KEYS the set is re-collected via
    // `S.fromList` — RE-SORTING (and deduping) by `Ord LNSubstVFresh`.
    // Renaming keys is NOT order-preserving (it is a precise remap, not a
    // monotone shift), so without this re-sort RS's `Vec`-backed disj is
    // left in a stale order relative to the new keys.  The raw Set order
    // is what `prettyEqStore` (`ppDisj`'s `S.toList substs`) renders on
    // the web sequent pages, and it is masked in batch `--prove` output
    // only because `performSplit` re-canonicalises the case order.
    // Mirrors the identical `S.fromList` re-sort the subterm-store block
    // below already performs for `mapFrees (S.Set SubtermD)`.
    sys.eq_store_mut().sort_disj_substs();

    // 8. Subterm store.
    //
    // HS-faithful: `_sSubtermStore` summands are `S.Set` (SubtermStore.hs
    // `Set SubtermD` for both pos and neg).  `mapFrees (S.Set a) =
    // fmap S.fromList . mapFrees f . S.toList` — sort + dedup post-rename.
    for c in sys.subterm_store_mut().subterms.iter_mut() {
        if let Some(nc) = c.apply_changed(&pass) {
            *c = nc;
        }
    }
    sys.subterm_store_mut()
        .subterms
        .sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    sys.subterm_store_mut()
        .subterms
        .dedup_by(|a, b| (&a.small, &a.big) == (&b.small, &b.big));
    for c in sys.subterm_store_mut().solved_subterms.iter_mut() {
        if let Some(nc) = c.apply_changed(&pass) {
            *c = nc;
        }
    }
    sys.subterm_store_mut()
        .solved_subterms
        .sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    sys.subterm_store_mut()
        .solved_subterms
        .dedup_by(|a, b| (&a.small, &a.big) == (&b.small, &b.big));
    // negSubterms are mapped too; oldNegSubterms are NOT (HS mapFrees
    // keeps `oldNegSt` with `pure` — SubtermStore.hs:550-555).  Take the set
    // out, map each pair, then `rebuild_from` re-establishes the sorted-unique
    // set invariant on the rewritten pairs.
    let mapped: Vec<(LNTerm, LNTerm)> = std::mem::take(&mut sys.subterm_store_mut().neg_subterms)
        .into_iter()
        .map(|pair| pair.apply(&pass))
        .collect();
    sys.subterm_store_mut().neg_subterms =
        crate::tools::subterm_store::SortedPairSet::rebuild_from(mapped);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};

    fn node(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Node, idx)
    }

    use crate::constraint::constraints::{LessAtom, Reason};

    fn less_sys(i_a: u64, i_b: u64) -> System {
        let mut sys = System::empty();
        sys.content_mut().less_atoms.push(LessAtom::new(
            node("i", i_a),
            node("i", i_b),
            Reason::Fresh,
        ));
        sys
    }

    #[test]
    fn rename_leaves_a_variable_free_system_untouched() {
        let mut sys = System::empty();
        rename_precise_system(&mut sys);
        assert_eq!(sys, System::empty());
    }

    #[test]
    fn variable_free_system_still_rebuilds_set_backed_fields() {
        use crate::guarded::{gfalse, gtrue};

        let mut sys = System::empty();
        sys.content_mut().formulas = vec![
            std::sync::Arc::new(gtrue()),
            std::sync::Arc::new(gfalse()),
            std::sync::Arc::new(gtrue()),
        ];

        rename_precise_system(&mut sys);

        assert_eq!(
            sys.formulas
                .iter()
                .map(|formula| formula.as_ref().clone())
                .collect::<Vec<_>>(),
            vec![gfalse(), gtrue()]
        );
    }

    /// Two systems that differ only in their node-id indices must compare
    /// equal after the rename.  A second pass must change nothing.  The test
    /// needs both halves.  Without them the canonical form that `process` and
    /// `Simplify` compare against is not a fixpoint.
    #[test]
    fn rename_normalises_node_ids() {
        let mut a = less_sys(0, 5);
        let mut b = less_sys(7, 99);
        rename_precise_system(&mut a);
        rename_precise_system(&mut b);
        assert_eq!(a, b);
        // The rename must not collapse distinct source vars onto one name.
        assert_ne!(a.less_atoms[0].smaller, a.less_atoms[0].larger);
        // The rename is idempotent.  A second rename of a canonical system
        // changes nothing.
        let once = a.clone();
        rename_precise_system(&mut a);
        assert_eq!(a, once);
    }

    #[test]
    fn a_rest_only_rename_keeps_the_nodes_shared() {
        let mut sys = less_sys(7, 8);
        let nodes = std::sync::Arc::clone(&sys.nodes);
        rename_precise_system(&mut sys);
        assert!(std::sync::Arc::ptr_eq(&nodes, &sys.nodes));
    }
}
