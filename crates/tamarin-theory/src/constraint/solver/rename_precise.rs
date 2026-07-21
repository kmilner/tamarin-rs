// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, PhilipLukertWork, rkunnema, felixlinker, beschmi, jdreier,
//   racoucho1u, rsasse, yavivanov, robert.kunnemann@cased.de, xaDxelA,
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Substitution/SubstVFree.hs,
//   lib/term/src/Term/Substitution/SubstVFresh.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Constraints.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Model/Atom.hs,
//   lib/theory/src/Theory/Tools/EquationStore.hs,
//   lib/theory/src/Theory/Tools/SubtermStore.hs

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
//!
//! In Rust we don't have a single `mapFrees` typeclass that covers `System`,
//! so we walk each field by hand. The walk-order mirrors
//! `Reduction::subst_system_once` so any future cross-checks stay aligned.

use tamarin_term::lterm::{HasFrees, LVar, LNTerm};
use tamarin_term::subst::Subst;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;
use tamarin_utils::fresh::PreciseFreshState;

use crate::constraint::constraints::Goal;
use crate::constraint::system::System;
use crate::guarded::{subst_guarded_cow, VarSubst};

/// Canonicalise the free `LVar`s of `sys` so that two systems differing
/// only by variable numbering compare equal.
///
/// Mirrors Haskell's `renamePrecise` over the `System` record.
pub fn rename_precise_system(sys: &mut System) {
    // Rewrites every free LVar through a deterministic alpha-rename;
    // the resulting max-var-idx is almost always smaller.  The full
    // cache is invalidated after Phase 1, and only when some binding is
    // a genuine remap (`state.changed`): an all-identity rename leaves
    // every value byte-identical — Phase 2 then only re-sorts fields and
    // dedups EQUAL values (the HS `S.fromList` effects), neither of
    // which can change the max free-var idx, so the cache stays exact.
    // The node-component cache is invalidated ONLY on the real node
    // rewrite in Phase 2 step 1: an all-identity NODE rename (a weaker
    // condition, snapshotted as `nodes_identity` below) already leaves
    // the nodes byte-identical even when later fields are remapped.
    let mut state = RenameState::new();

    // ----------------------------------------------------------------------
    // Phase 1 — walk every free LVar in deterministic traversal order so the
    // import-binding map is populated independent of how we apply later.
    //
    // HS-faithful order — matches `instance HasFrees System` field walk
    // (System.hs:383-397 declaration order, traversed by foldFrees):
    //   sNodes → sEdges → sLessAtoms → sLastAtom → sSubtermStore →
    //   sEqStore → sFormulas → sSolvedFormulas → sLemmas → sGoals
    //
    // This MUST match HS's renamePrecise to keep per-name idx assignment
    // in lockstep: formulas must be visited before goals so that a free
    // LVar shared between a formula and a goal Disj is bound to the same
    // fresh idx HS would assign, otherwise the two become distinct LVars.
    // ----------------------------------------------------------------------

    // HS-faithful: HS's `instance HasFrees (Map k v)` uses
    // `M.foldrWithKey` which walks the map keyed by `Ord k` ascending
    // (Term/LTerm.hs:829-836).  Rust's `sys.nodes` is a `Vec<(NodeId,
    // RuleACInst)>` in insertion order — that order is NOT the same as
    // NodeId-ascending.  Without this sort, the walk visits a newly-grafted
    // source-case Gen_Step (high pre-rename idx but inserted last) AFTER
    // pre-existing Check nodes — yet then `state.import` allocates per-name
    // counters in *visit* order, so the newly-grafted Gen_Step gets the
    // FIRST fresh "vr" slot if walked first / LAST if walked last.  For
    // Helper_Loop_and_success this controls whether vr.0 ends up Check
    // (HS pattern) or Gen_Step (the unsorted-walk pattern), which in turn flips
    // impliedFormulas' sysActions iteration order and the Disj goal-nrs.
    let mut nodes_sorted: Vec<&(crate::constraint::constraints::NodeId, crate::rule::RuleACInst)>
        = sys.nodes.iter().collect();
    nodes_sorted.sort_by(|a, b| a.0.cmp(&b.0));
    for (id, rule) in nodes_sorted {
        state.import(id);
        rule.for_each_free(&mut |v| { state.import(v); });
    }
    // Nodes are the FIRST field walked, so `!state.changed` here means every
    // node var (ids + rule vars) was bound to its own idx — the node rename
    // is the identity.  Snapshotted before any later field can flip the flag,
    // enabling the Phase 2 step-1 identity fast path.
    let nodes_identity = !state.changed;
    // HS-faithful: `instance HasFrees (S.Set a)` (Term/LTerm.hs:824-827)
    // walks the set via `foldMap (foldFrees f)` — i.e. ascending Ord
    // order.  HS's `_sEdges` / `_sLessAtoms` / `_sSubtermStore` fields
    // are `S.Set` (System.hs:385-388 + SubtermStore.hs:546-548) and HS
    // visits them sorted by their derived `Ord`.  RS's `Vec` is in
    // insertion order, which DIVERGES from HS for `requiresKU`-driven
    // Less-atom inserts whose new vk-LVars get appended later but sort
    // earlier by `(smaller, larger)` than older atoms.  Sort copies here
    // ONLY for the rename-precise walk so the per-name "vk" counter
    // assigns canonical idxs in HS Set-order — matching HS's
    // `evalFresh ... nothingUsed`-canonicalised numbering exactly —
    // without touching the live `less_atoms` / `edges` Vec used
    // elsewhere.
    let mut edges_sorted: Vec<&crate::constraint::constraints::Edge>
        = sys.edges.iter().collect();
    edges_sorted.sort();
    for e in edges_sorted {
        state.import(&e.src.0);
        state.import(&e.tgt.0);
    }
    let mut less_sorted: Vec<&crate::constraint::constraints::LessAtom>
        = sys.less_atoms.iter().collect();
    less_sorted.sort();
    for la in less_sorted {
        state.import(&la.smaller);
        state.import(&la.larger);
    }
    if let Some(la) = &sys.last_atom { state.import(la); }
    // HS `HasFrees SubtermStore` (SubtermStore.hs:546-548) walks
    // `negSt <> st <> solvedSt`; each summand is a `S.Set` — sorted.
    // `neg_subterms` (negSt) must be visited FIRST to match HS order.
    // HS `neg_subterms` is `S.Set (LNTerm, LNTerm)` — sorted by pair Ord.
    let mut neg_sorted: Vec<&(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>
        = sys.subterm_store.neg_subterms.iter().collect();
    neg_sorted.sort();
    for (s, b) in neg_sorted {
        s.for_each_free(&mut |v| { state.import(v); });
        b.for_each_free(&mut |v| { state.import(v); });
    }
    // SubtermConstraint isn't `Ord` in RS so sort by `(small, big)`
    // which mirrors HS's derived ordering on the analogous field pair.
    let mut sub_sorted: Vec<&crate::tools::subterm_store::SubtermConstraint>
        = sys.subterm_store.subterms.iter().collect();
    sub_sorted.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    for c in sub_sorted {
        c.small.for_each_free(&mut |v| { state.import(v); });
        c.big.for_each_free(&mut |v| { state.import(v); });
    }
    let mut solved_sorted: Vec<&crate::tools::subterm_store::SubtermConstraint>
        = sys.subterm_store.solved_subterms.iter().collect();
    solved_sorted.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    for c in solved_sorted {
        c.small.for_each_free(&mut |v| { state.import(v); });
        c.big.for_each_free(&mut |v| { state.import(v); });
    }
    // eq_store.subst: visit keys (dom) and values (range).  RS's
    // `Subst` is `BTreeMap`-backed, so the borrowing `iter()` already
    // yields pairs in ascending-key order — matches HS's `HasFrees
    // (LSubst c) = foldFrees f . sMap` walking `M.Map LVar Term`
    // ascending (SubstVFree.hs:220-221, see line 221).
    for (k, t) in sys.eq_store.subst.iter() {
        state.import(k);
        t.for_each_free(&mut |v| { state.import(v); });
    }
    // eq_store.conj: HS-faithful `HasFrees (SubstVFresh n LVar)` only
    // walks DOMAIN (keys), NOT values (SubstVFresh.hs:196-202).  This
    // preserves the witness idxs in values — crucial for
    // sort-discriminating across variants at perform_split.
    //
    // The outer container `Conj (SplitId, S.Set LNSubstVFresh)`
    // (EquationStore.hs:116-121, see line 118) is a `Conj`-list (insertion order — match
    // with RS's `Vec<EqDisj>`).  The INNER `S.Set LNSubstVFresh` is Ord
    // ascending — sort to match.
    for d in &sys.eq_store.conj {
        let mut substs_sorted: Vec<&tamarin_term::subst_vfresh::SubstVFresh<tamarin_term::lterm::Name, LVar>>
            = d.substs.iter().collect();
        substs_sorted.sort();
        for s in substs_sorted {
            // Borrowing `dom()` walks the same BTreeMap keys in the same
            // ascending order as `to_list()`, without cloning every
            // (key, range-term) pair only to discard it.
            for k in s.dom() {
                state.import(k);
                // Note: value vars NOT imported (HS-faithful).
            }
        }
    }
    // HS-faithful: `_sFormulas` / `_sSolvedFormulas` / `_sLemmas` are
    // `S.Set LNGuarded` (System.hs:390-392), walked via `HasFrees (S.Set
    // a) = foldMap (foldFrees f)` in Ord-ascending.  RS's
    // `Vec<Guarded>` is in insertion order — sort via the existing
    // `cmp_guarded` helper (guarded.rs:67) which mirrors HS's derived
    // `Ord Guarded` (Guarded.hs:121-129).
    let mut formulas_sorted: Vec<&crate::guarded::Guarded>
        = sys.formulas.iter().map(|f| f.as_ref()).collect();
    formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in formulas_sorted { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    let mut solved_formulas_sorted: Vec<&crate::guarded::Guarded>
        = sys.solved_formulas.iter().map(|f| f.as_ref()).collect();
    solved_formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in solved_formulas_sorted { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    let mut lemmas_sorted: Vec<&crate::guarded::Guarded>
        = sys.lemmas.iter().map(|f| f.as_ref()).collect();
    lemmas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in lemmas_sorted { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    // HS-faithful: `_sGoals` is `M.Map Goal GoalStatus` (System.hs:383-401, see line 393),
    // walked via `HasFrees (M.Map k v) = M.foldrWithKey combine`
    // (Term/LTerm.hs:829-836) in ascending key order (`Ord Goal`).
    // `goal_cmp` matches HS's derived `Ord Goal`
    // (System/Constraints.hs:156-168); see
    // `goal_cmp_tag_order_matches_haskell_declaration` test in goals.rs.
    let mut goals_sorted: Vec<&(Goal, crate::constraint::system::GoalStatus)>
        = sys.goals.iter().collect();
    goals_sorted.sort_by(|a, b|
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    for (g, _) in goals_sorted {
        goal_for_each_free(g, &mut |v| { state.import(v); });
    }

    // ----------------------------------------------------------------------
    // Phase 2 — apply the renaming map.
    //
    // For LVar-only fields we look up directly. For term-bearing fields we
    // build a `Subst` (LVar → Var-term) and apply via `apply_vterm`. For
    // guarded formulas we use the parser-level `VarSubst`.
    // ----------------------------------------------------------------------

    // `state.changed` covers EVERY field (Phase 1 walks them all), so a
    // false value proves the whole rename is the identity — see the
    // invalidation note at the top of this function.
    let any_remap = state.changed;
    let map = state.into_map();
    if map.is_empty() { return; }
    if any_remap {
        sys.invalidate_max_var_idx_cache();
        // Whole-system alpha-rename: no inherited verified-no-op verdict
        // survives a domain/range rename.  The Phase-2
        // eq-store rewrite (via `eq_store_mut`) already bumps `subst_stamp`;
        // clear the marker explicitly too.
        sys.clear_subst_marker();
    }

    let term_subst: Subst<tamarin_term::lterm::Name, LVar> = Subst::from_list(
        map.iter().map(|(old, new)| {
            (old.0.clone(), Term::Lit(Lit::Var(new.clone())))
        }),
    );
    // Hashed leaf-lookup view over the pass-invariant rename subst
    // (`SubstView`): Phase 2 applies this ONE fixed var→var substitution to
    // every goal/eq-store/subterm-store term, so a single FxHash probe per
    // `Lit::Var` leaf replaces the `BTreeMap` descent — identical lookups,
    // byte-identical output.  (`from_list` above already drops identity
    // `x ~> x` entries, so the view's hit set matches the map's exactly.)
    let term_view = tamarin_term::subst::SubstView::new(&term_subst);
    let formula_subst: VarSubst = map.iter().map(|(old, new)| {
        let sort = lvar_sort_to_sort_hint(new.sort);
        (
            // `old.0.name` is an interned `&'static str` — zero-alloc key.
            (old.0.name, old.0.idx),
            tamarin_parser::ast::Term::Var(tamarin_parser::ast::VarSpec {
                name: new.name.to_string(),
                idx: new.idx,
                sort,
                typ: None,
            }),
        )
    }).collect();

    let map_var = |v: LVar| -> LVar {
        map.get(&v).cloned().unwrap_or(v)
    };

    // 1. Nodes — id + rule.
    //
    // HS-faithful: `mapFrees (M.Map NodeId RuleACInst)`
    // = `fmap M.fromList . mapFrees f . M.toList` (Term/LTerm.hs:832-838, see line 836).
    // `M.fromList` builds a Map keyed by Ord NodeId, so post-rename the
    // entries land in ascending NEW NodeId order.  Without this sort,
    // RS's `Vec<(NodeId, _)>` keeps the pre-rename insertion order — which
    // diverges from HS for any downstream consumer that walks `sys.nodes`
    // in storage order rather than re-sorting (most do their own sort, but
    // some iterate directly).  Mirror HS by sorting here.
    //
    // Identity fast path: when the node rename is the identity
    // (`nodes_identity`), `map_var` maps every node id + rule var to itself,
    // so the per-rule `map_free` re-walk is a value no-op.  `map_free` is the
    // non-monotone (`Arbitrary`) map, which AC-re-sorts on rebuild, but a
    // stored node term is always `f_app`-normal (every term is built through
    // `f_app`; the monotone paths preserve normal form), so re-sorting under
    // an identity var-map reproduces the same normal form.  The only
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
            let mut nodes = std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.content_mut_untracked().nodes));
            nodes.sort_by(|a, b| a.0.cmp(&b.0));
            sys.content_mut_untracked().nodes = std::sync::Arc::new(nodes);
        }
    } else {
        // Real rename: node var idxs are remapped (almost always lower), so
        // the node-component max can drop — invalidate its cache here (the
        // one site that actually rewrites nodes).
        sys.invalidate_node_max_cache();
        let nodes = std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.content_mut_untracked().nodes));
        let mut renamed: Vec<(crate::constraint::constraints::NodeId, crate::rule::RuleACInst)>
            = nodes.into_iter().map(|(id, rule)| {
                let new_id = map_var(id);
                let new_rule = rule.map_free(&mut |v| map_var(v));
                (new_id, new_rule)
            }).collect();
        renamed.sort_by(|a, b| a.0.cmp(&b.0));
        sys.content_mut_untracked().nodes = std::sync::Arc::new(renamed);
    }

    // 2. Edges.
    for e in sys.content_mut_untracked().edges.iter_mut() {
        e.src.0 = map_var(e.src.0.clone());
        e.tgt.0 = map_var(e.tgt.0.clone());
    }
    // Dedup after rename — sort + dedup (matches subst_system).
    let mut tmp: Vec<_> = std::mem::take(&mut sys.content_mut_untracked().edges);
    tmp.sort();
    tmp.dedup();
    sys.content_mut_untracked().edges = tmp;

    // 3. Last atom.
    if let Some(la) = sys.content_mut_untracked().last_atom.take() {
        sys.content_mut_untracked().last_atom = Some(map_var(la));
    }

    // 4. Less atoms.
    //
    // HS-faithful dedup post-rename: HS's `sLessAtoms :: Set LessAtom`
    // is reconstructed via `S.map (apply subst)` on every rewrite,
    // collapsing duplicates whose images coincide.  Mirror by deduping
    // after the in-place rename.  See `subst_system_once`'s comment for
    // detailed rationale.
    // HS `mapFrees (S.Set LessAtom)`: sort + dedup post-rename
    // (Term/LTerm.hs:825-830, see line 827 `fmap S.fromList . mapFrees f . S.toList`).
    let mut new_less: Vec<crate::constraint::constraints::LessAtom>
        = Vec::with_capacity(sys.less_atoms.len());
    for la in std::mem::take(&mut sys.content_mut_untracked().less_atoms) {
        let mut la = la;
        la.smaller = map_var(la.smaller.clone());
        la.larger  = map_var(la.larger.clone());
        new_less.push(la);
    }
    // Sort + dedup (O(n log n)), matching HS's `S.fromList` over the renamed
    // set rather than an O(n^2) membership scan.
    new_less.sort();
    new_less.dedup();
    sys.content_mut_untracked().less_atoms = new_less;

    // 5. Goals — per-variant rewrite.
    let goals = std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.content_mut_untracked().goals));
    let apply_term = |t: LNTerm| -> LNTerm {
        term_view.apply(t)
    };
    let apply_fact = |fa: crate::fact::LNFact| -> crate::fact::LNFact {
        // Var→var rename is a frees-changing rebuild:
        // recompute the bloom from the renamed terms — NEVER copy `fa`'s.
        let terms: Vec<LNTerm> = fa.terms.iter().cloned().map(&apply_term).collect();
        // Computing constructor — recomputes the bloom from the renamed terms
        // internally (never copies `fa`'s stale bloom).
        crate::fact::Fact::fresh_annotated(fa.tag, fa.annotations, terms)
    };
    let mut new_goals: Vec<(Goal, crate::constraint::system::GoalStatus)> =
        Vec::with_capacity(goals.len());
    for (g, st) in goals {
        let g2 = match g {
            Goal::Action(i, fa) => Goal::Action(map_var(i), apply_fact(fa)),
            Goal::Premise(p, fa) => Goal::Premise((map_var(p.0), p.1), apply_fact(fa)),
            Goal::Chain(c, p) => Goal::Chain(
                (map_var(c.0), c.1),
                (map_var(p.0), p.1),
            ),
            Goal::Disj(d) => {
                // COW: an identity rename (or one that touches no Disj leaf)
                // reuses the owned `g` with zero rebuild; `Some` is byte-
                // identical to the eager `subst_guarded`.
                let items: Vec<crate::guarded::Guarded> = d.0.into_iter()
                    .map(|g| subst_guarded_cow(&g, &formula_subst).unwrap_or(g))
                    .collect();
                Goal::Disj(crate::constraint::constraints::Disj(items))
            }
            Goal::Split(s) => Goal::Split(s),
            Goal::Subterm((s, t)) => Goal::Subterm((apply_term(s), apply_term(t))),
        };
        new_goals.push((g2, st));
    }
    // HS-faithful: `mapFrees (M.Map Goal GoalStatus)`
    // = `fmap M.fromList . mapFrees f . M.toList` (Term/LTerm.hs:832-838, see line 836).
    // `M.fromList` builds a Map keyed by Ord Goal, so post-rename the
    // entries land in ascending NEW Goal order.
    //
    // Sort + dedup (O(n log n)) instead of an O(n^2) membership scan. We
    // dedup on structural `Goal` equality (plain `==`) — NOT on
    // `goal_cmp == Equal`, because `goal_cmp` orders
    // Disj goals by len + canonical string and would over-collapse.
    new_goals.sort_by(|a, b|
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    new_goals.dedup_by(|a, b| a.0 == b.0);
    sys.content_mut_untracked().goals = std::sync::Arc::new(new_goals);

    // 6. Formulas / solved / lemmas — via parser-level VarSubst.
    //
    // HS-faithful: `_sFormulas` / `_sSolvedFormulas` / `_sLemmas` are
    // `S.Set LNGuarded`. `mapFrees (S.Set a) = fmap S.fromList . mapFrees
    // f . S.toList` (Term/LTerm.hs:825-830, see line 827) — rebuilds the set after mapping,
    // so post-rename entries are sorted by NEW Ord Guarded AND
    // collision-deduped.  Mirror by sorting+deduping after the in-place
    // rename: post-rename two formulas that became equal collapse.
    if !formula_subst.is_empty() {
        let sort_dedup_guarded = |v: &mut Vec<std::sync::Arc<crate::guarded::Guarded>>, sub: &VarSubst| {
            // COW: only the formulas whose leaves actually change are rebuilt;
            // `Some(nf)` is byte-identical to the eager `subst_guarded`, and a
            // no-effect (identity) rename leaves `*f` untouched.  The
            // sort+dedup below stays UNCONDITIONAL — HS's `S.fromList` rebuild
            // runs even under an identity rename, and intervening passes may
            // have left the Vec unsorted.
            for f in v.iter_mut() {
                if let Some(nf) = subst_guarded_cow(f, sub) { *f = std::sync::Arc::new(nf); }
            }
            v.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
            v.dedup_by(|a, b| crate::guarded::cmp_guarded(a, b)
                == std::cmp::Ordering::Equal);
        };
        sort_dedup_guarded(sys.formulas_mut_untracked(), &formula_subst);
        sort_dedup_guarded(sys.solved_formulas_mut_untracked(), &formula_subst);
        sort_dedup_guarded(&mut sys.content_mut_untracked().lemmas, &formula_subst);
    }

    // 7. eq_store — rewrite the subst (dom + range) and the conj.
    let old_subst = std::mem::replace(
        &mut sys.eq_store_mut().subst,
        crate::tools::equation_store::LNSubst::empty(),
    );
    let pairs: Vec<(LVar, LNTerm)> = old_subst.to_list().into_iter()
        .map(|(k, v)| (map_var(k), apply_term(v)))
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
            let pairs: Vec<(LVar, LNTerm)> = s.to_list().into_iter()
                .map(|(k, v)| (map_var(k), v))  // keep VALUE unchanged
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
        c.small = apply_term(c.small.clone());
        c.big = apply_term(c.big.clone());
    }
    sys.subterm_store_mut().subterms.sort_by(|a, b|
        (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    sys.subterm_store_mut().subterms.dedup_by(|a, b|
        (&a.small, &a.big) == (&b.small, &b.big));
    for c in sys.subterm_store_mut().solved_subterms.iter_mut() {
        c.small = apply_term(c.small.clone());
        c.big = apply_term(c.big.clone());
    }
    sys.subterm_store_mut().solved_subterms.sort_by(|a, b|
        (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    sys.subterm_store_mut().solved_subterms.dedup_by(|a, b|
        (&a.small, &a.big) == (&b.small, &b.big));
    // negSubterms are mapped too; oldNegSubterms are NOT (HS mapFrees
    // keeps `oldNegSt` with `pure` — SubtermStore.hs:550-555).  Take the set
    // out, map each pair, then `rebuild_from` re-establishes the sorted-unique
    // set invariant on the rewritten pairs.
    let mapped: Vec<(LNTerm, LNTerm)> =
        std::mem::take(&mut sys.subterm_store_mut().neg_subterms)
            .into_iter()
            .map(|(s, t)| (apply_term(s), apply_term(t)))
            .collect();
    sys.subterm_store_mut().neg_subterms =
        crate::tools::subterm_store::SortedPairSet::rebuild_from(mapped);
}

// =============================================================================
// Helpers
// =============================================================================

/// Rename-map key wrapping the original `LVar`.
///
/// `Hash` delegates to `LVar`'s content-based derive, so two vars with equal
/// *content* always hash to the same bucket even when their interned name
/// pointers differ (a rare non-canonical literal name vs the pooled copy) —
/// this is what keeps the dedup correct and the `--prove` output byte-identical.
/// Only `Eq` is optimised: `lvar_fast_eq` short-circuits on the interned name
/// POINTER, skipping the byte-wise `str` compare that dominated `import`'s
/// confirming-eq self time, and falls back to the exact content compare when
/// the pointers differ — so the equality RELATION is exactly `LVar`'s.
#[derive(Clone)]
struct VarKey(LVar);

impl PartialEq for VarKey {
    #[inline]
    fn eq(&self, other: &Self) -> bool { lvar_fast_eq(&self.0, &other.0) }
}
impl Eq for VarKey {}
impl std::hash::Hash for VarKey {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.0.hash(state) }
}
// Lets `contains_key`/`get` probe by `&LVar` (no clone) yet run the fast eq.
// The probe hashes via `LVar`'s derive (identical to `VarKey::hash`), so the
// probe lands in the same bucket the owned key was stored in.
impl hashbrown::Equivalent<VarKey> for LVar {
    #[inline]
    fn equivalent(&self, key: &VarKey) -> bool { lvar_fast_eq(self, &key.0) }
}

/// Exactly `LVar`'s content equality, faster: interned names share one
/// canonical pointer (intern guarantees content-equal ⇒ pointer-equal), so a
/// pointer+len match confirms the name without the byte compare; anything else
/// falls back to the full content compare, so the relation is unchanged.
#[inline]
fn lvar_fast_eq(a: &LVar, b: &LVar) -> bool {
    // Destructure without `..` so a new `LVar` field forces an equality decision
    // here, keeping this fast path in step with `LVar`'s derived Eq.
    let LVar { name: a_name, sort: a_sort, idx: a_idx } = a;
    let LVar { name: b_name, sort: b_sort, idx: b_idx } = b;
    // idx (u64) first — most discriminating, cheapest — then sort, so a
    // hash-collision mismatch is rejected before the name is touched.
    if a_idx != b_idx || a_sort != b_sort {
        return false;
    }
    (std::ptr::eq(a_name.as_ptr(), b_name.as_ptr()) && a_name.len() == b_name.len())
        || a_name == b_name
}

/// The rename map: keyed by `VarKey` (content hash, fast pointer eq), hashed
/// with the same `FxBuildHasher` as `FastMap`.  Iteration order is never
/// observed — `into_map` feeds only `Subst::from_list` (a re-sorted `BTreeMap`)
/// and a distinct-key `VarSubst` applied by lookup.
type RenameMap = hashbrown::HashMap<VarKey, LVar, rustc_hash::FxBuildHasher>;

struct RenameState {
    fresh: PreciseFreshState,
    map: RenameMap,
    /// Set the first time a var is bound to a DIFFERENT idx than its
    /// original.  `import` always preserves name+sort, so a fresh binding
    /// is the identity exactly when its allocated idx equals the original;
    /// `!changed` after a field's walk means the rename is the identity over
    /// every var seen so far (used for the nodes-first fast path).
    changed: bool,
}

impl RenameState {
    fn new() -> Self {
        RenameState {
            fresh: PreciseFreshState::nothing_used(),
            map: RenameMap::default(),
            changed: false,
        }
    }
    /// `importBinding`: idempotent — first call for `v` allocates a fresh
    /// LVar keyed by `v.name`; later calls return the same binding.
    fn import(&mut self, v: &LVar) {
        // Probe by `&LVar` (no clone) via `VarKey`'s `Equivalent` impl, whose
        // `eq` short-circuits on the interned name POINTER — skipping the
        // byte-wise `str` compare that dominated `import`'s confirming-eq self
        // time (`equal_same_length` in the profile) — with a content fallback
        // that keeps the equality RELATION exactly `LVar`'s.  The hash is still
        // content-based (see `VarKey`), so equal-content vars — even with
        // different name pointers — dedup into one slot: output is identical.
        if self.map.contains_key(v) { return; }
        let idx = self.fresh.fresh_ident(v.name);
        // Record whether this first binding remaps the idx (name+sort are
        // always preserved), so an all-identity prefix leaves `changed` false.
        if idx != v.idx { self.changed = true; }
        // First occurrence only (rare): materialise the owned key.
        self.map.insert(VarKey(v.clone()), LVar { name: v.name, sort: v.sort, idx });
    }
    fn into_map(self) -> RenameMap { self.map }
}

fn lvar_sort_to_sort_hint(s: tamarin_term::lterm::LSort) -> tamarin_parser::ast::SortHint {
    use tamarin_term::lterm::LSort;
    use tamarin_parser::ast::SortHint;
    match s {
        LSort::Msg => SortHint::Msg,
        LSort::Pub => SortHint::Pub,
        LSort::Fresh => SortHint::Fresh,
        LSort::Node => SortHint::Node,
        LSort::Nat => SortHint::Nat,
    }
}

fn goal_for_each_free(g: &Goal, f: &mut dyn FnMut(&LVar)) {
    match g {
        Goal::Action(i, fa) => {
            f(i);
            fa.for_each_free(f);
        }
        Goal::Premise(p, fa) => {
            f(&p.0);
            fa.for_each_free(f);
        }
        Goal::Chain(c, p) => {
            f(&c.0);
            f(&p.0);
        }
        Goal::Disj(d) => {
            for item in &d.0 { guarded_for_each_free(item, f); }
        }
        Goal::Split(_) => {}
        Goal::Subterm((a, b)) => {
            a.for_each_free(f);
            b.for_each_free(f);
        }
    }
}

/// Walk every free `LVar` of a `Guarded` formula. With DeBruijn bindings,
/// `BVar::Bound` leaves carry no LVar identity and are auto-skipped; only
/// `BVar::Free` leaves get visited.
fn guarded_for_each_free(g: &crate::guarded::Guarded, f: &mut dyn FnMut(&LVar)) {
    use crate::guarded::Guarded;
    match g {
        Guarded::Atom(a) => atom_for_each_free(a, f),
        Guarded::Disj(xs) | Guarded::Conj(xs) => {
            for x in xs { guarded_for_each_free(x, f); }
        }
        Guarded::GGuarded { guards, body, .. } => {
            for a in guards { atom_for_each_free(a, f); }
            guarded_for_each_free(body, f);
        }
    }
}

fn atom_for_each_free(a: &crate::guarded::GAtom, f: &mut dyn FnMut(&LVar)) {
    use crate::guarded::GAtom;
    match a {
        GAtom::Eq(x, y) | GAtom::Less(x, y)
        | GAtom::LessMset(x, y) | GAtom::Subterm(x, y) => {
            term_for_each_free(x, f);
            term_for_each_free(y, f);
        }
        GAtom::Action(fa, t) => {
            // HS `Traversable ProtoAtom` visits the timepoint BEFORE the
            // fact: `traverse f (Action i fa) = Action <$> f i <*> traverse f fa`
            // (Atom.hs).  renamePrecise allocates fresh per-name indices
            // in visit order, so the timepoint must be walked first to
            // match HS's idx assignment.
            term_for_each_free(t, f);
            for arg in &fa.args { term_for_each_free(arg, f); }
        }
        GAtom::Last(t) => term_for_each_free(t, f),
        GAtom::Pred(fa) => { for arg in &fa.args { term_for_each_free(arg, f); } }
    }
}

fn term_for_each_free(t: &crate::guarded::GTerm, f: &mut dyn FnMut(&LVar)) {
    use crate::guarded::{GTerm, BVar};
    match t {
        GTerm::Var(BVar::Free(v)) => {
            let sort = parser_sort_to_lsort(v.sort);
            f(&LVar { name: tamarin_term::intern::intern_str(v.name.as_str()), sort, idx: v.idx });
        }
        GTerm::Var(BVar::Bound(_)) => {}
        GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne | GTerm::DhNeutral => {}
        GTerm::App(_, args) | GTerm::Pair(args) => {
            for a in args.iter() { term_for_each_free(a, f); }
        }
        GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
            term_for_each_free(a, f);
            term_for_each_free(b, f);
        }
        GTerm::PatMatch(t) => term_for_each_free(t, f),
    }
}

/// Thin wrapper over the shared `sort_hint_to_lsort_opt` mapping (`sources`),
/// resolving `Untagged` to `LSort::Msg`.
fn parser_sort_to_lsort(s: tamarin_parser::ast::SortHint) -> tamarin_term::lterm::LSort {
    super::sources::sort_hint_to_lsort_opt(&s).unwrap_or(tamarin_term::lterm::LSort::Msg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};

    fn node(name: &str, idx: u64) -> LVar { LVar::new(name, LSort::Node, idx) }

    #[test]
    fn rename_idempotent_on_empty_system() {
        let mut sys = System::empty();
        rename_precise_system(&mut sys);
        assert_eq!(sys, System::empty());
    }

    #[test]
    fn rename_normalises_node_ids() {
        // Two systems that differ only by node-id indices should compare
        // equal after rename_precise_system.
        use crate::constraint::constraints::{LessAtom, Reason};

        let mk_sys = |i_a: u64, i_b: u64| -> System {
            let mut sys = System::empty();
            sys.content_mut().less_atoms.push(LessAtom::new(
                node("i", i_a), node("i", i_b), Reason::Fresh,
            ));
            sys
        };
        let mut a = mk_sys(0, 5);
        let mut b = mk_sys(7, 99);
        rename_precise_system(&mut a);
        rename_precise_system(&mut b);
        assert_eq!(a.less_atoms[0].smaller, b.less_atoms[0].smaller);
        assert_eq!(a.less_atoms[0].larger,  b.less_atoms[0].larger);
        // The two distinct node names should still differ.
        assert_ne!(a.less_atoms[0].smaller, a.less_atoms[0].larger);
    }
}
