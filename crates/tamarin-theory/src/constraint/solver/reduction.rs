// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.Solver.Reduction`.
//!
//! Haskell's `Reduction` is `StateT System (FreshT (DisjT (Reader
//! ProofContext)))`. The port models it as a struct holding the mutable
//! `System`, the `ProofContext` and its own fresh counter
//! (`Reduction::maude`); a split returns its branches explicitly. See
//! `constraint/solver/BRANCHING.md` for the branch-state and fresh-counter
//! invariants.

use crate::constraint::constraints::{Disj, Edge, Goal, LessAtom, NodeId};
use crate::constraint::solver::context::ProofContext;
use crate::constraint::system::System;
use crate::guarded::{bterm_to_lterm, Guarded};
use crate::rule::RuleACInst;
use tamarin_term::apply::Apply;
use tamarin_term::lterm::{blterm_node_id, lterm_node_id};

/// Haskell `setNodes` groups by the final node ID, retaining input order
/// within each group. Substitution supplies nodes in their old-ID order so
/// the lowest old ID remains the survivor when several IDs become equal.
struct GroupedNodes {
    nodes: Vec<(NodeId, RuleACInst)>,
    equalities: Vec<tamarin_term::rewriting::Equal<RuleACInst>>,
}

fn group_node_rules(mut nodes: Vec<(NodeId, RuleACInst)>) -> GroupedNodes {
    nodes.sort_by_key(|(id, _)| *id);
    let mut grouped = GroupedNodes {
        nodes: Vec::with_capacity(nodes.len()),
        equalities: Vec::new(),
    };
    for (id, rule) in nodes {
        match grouped.nodes.last() {
            Some((previous, keep)) if *previous == id => {
                grouped.equalities.push(tamarin_term::rewriting::Equal {
                    lhs: keep.clone(),
                    rhs: rule,
                });
            }
            _ => grouped.nodes.push((id, rule)),
        }
    }
    grouped
}

/// A reduction step takes a `System` and produces zero or more new
/// systems. We keep it simple: explicit input/output rather than a
/// monad transformer stack.
pub struct Reduction<'ctx> {
    pub ctx: &'ctx ProofContext,
    pub sys: System,
    /// Per-Reduction MaudeHandle: shares Maude's process state with
    /// `ctx.maude` but carries its own `fresh_counter` initialised from
    /// `bounds_max(&sys) + 1` at Reduction creation.  Mirrors Haskell's
    /// `runReduction m ctx sys (avoid sys)` — each runReduction call gets
    /// its own FreshState that advances within the call but doesn't leak
    /// across Reductions.  Use `self.maude` for any fresh-idx allocation
    /// inside Reduction methods (so witness allocation patterns match HS).
    pub maude: tamarin_term::maude_proc::MaudeHandle,
    /// Whether the system has been mutated since the last
    /// `whileChanging` checkpoint.
    pub changed: ChangeIndicator,
}

/// `ChangeIndicator` mirrors the `True`/`False` flag the Haskell
/// `whenChanged` / `whileChanging` combinators thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChangeIndicator {
    Changed,
    Unchanged,
}

impl ChangeIndicator {
    pub fn or(self, other: Self) -> Self {
        if self == ChangeIndicator::Changed || other == ChangeIndicator::Changed {
            ChangeIndicator::Changed
        } else {
            ChangeIndicator::Unchanged
        }
    }
}

thread_local! {
    /// Source-wide `avoid th` floor for nested refinement reductions
    /// (`refineSource`, Sources.hs). It covers all source cases, including
    /// variables absent from the case currently being simplified. A scoped
    /// guard restores it after refinement; zero means no additional floor.
    static REFINE_FLOOR: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Set the source-precompute fresh-counter floor, returning the previous
/// value (for RAII restore).  See [`REFINE_FLOOR`].
pub fn set_refine_floor(floor: u64) -> u64 {
    REFINE_FLOOR.with(|c| {
        let old = c.get();
        c.set(floor);
        old
    })
}

/// Current source-precompute fresh-counter floor (`avoid th`, 0 if unset).
pub fn refine_floor() -> u64 {
    REFINE_FLOOR.with(|c| c.get())
}

impl<'ctx> Reduction<'ctx> {
    /// A reduction seeded from `avoid sys` (Haskell `runReduction m ctx sys
    /// (avoid sys)`), lifted to the source-precompute floor when one is set.
    pub fn new(ctx: &'ctx ProofContext, sys: System) -> Self {
        Self::new_inheriting(ctx, sys, 0)
    }

    /// Like [`new`](Self::new) but continues an enclosing Reduction's fresh
    /// counter: the next draw is `max(avoid sys, floor + 1, inherit_next)`.
    ///
    /// Haskell's `Reduction = StateT System (FreshT (DisjT ...))` has one
    /// fresh counter per `runReduction`; the port runs sub-computations in
    /// child Reductions, and reseeding a child from `avoid sys` alone would
    /// rewind past draws whose variables never reached the system.
    /// `inherit_next` is the parent's `maude.fresh_counter_peek()` at the
    /// fork. The floor is `avoid th` of the source being refined
    /// (`refineSource`, Sources.hs), carried by [`REFINE_FLOOR`]; 0 means
    /// none.
    pub fn new_inheriting(ctx: &'ctx ProofContext, sys: System, inherit_next: u64) -> Self {
        let floor = refine_floor();
        let next = avoid_fresh_state(&sys)
            .max(if floor == 0 {
                0
            } else {
                floor.saturating_add(1)
            })
            .max(inherit_next);
        let maude = ctx.maude.with_fresh_counter_next(next);
        // Keep the shared handle above this Reduction's start, so an allocator
        // drawing from `ctx.maude` directly cannot collide with it.
        if next > 0 {
            ctx.maude.ensure_above(next - 1);
        }
        Reduction {
            ctx,
            sys,
            maude,
            changed: ChangeIndicator::Unchanged,
        }
    }

    /// Mark the system contradictory, the port's stand-in for Haskell's
    /// `contradictoryIf` / `mzero`: `gfalse` in the formulas (reported by
    /// `contradictions` as `FormulasFalse`) and a false equation store (the
    /// case filter in `exec_proof_method` drops such cases, as `mzero`
    /// would). Raises `changed` only if a marker toggled.
    pub fn mark_contradictory(&mut self) {
        let bot = crate::guarded::gfalse();
        let added_bot = self.sys.insert_open_formula(bot);
        let flipped_eq = self.set_eq_store_false();
        if added_bot || flipped_eq {
            self.changed = ChangeIndicator::Changed;
        }
    }

    /// Flip `eq_store` to its `is_false` (mzero-proxy) state: take the
    /// store out of its `Arc`, invalidate the max-var-idx cache, and
    /// reinstall the `set_false()` result. Returns `true` iff it actually
    /// flipped (the store was not already false). Callers decide whether
    /// the flip also implies a `self.changed` bump.
    fn set_eq_store_false(&mut self) -> bool {
        if !self.sys.eq_store().is_false() {
            let s = std::sync::Arc::unwrap_or_clone(self.sys.take_eq_store());
            self.sys.invalidate_max_var_idx_cache();
            self.sys.set_eq_store(std::sync::Arc::new(s.set_false()));
            true
        } else {
            false
        }
    }

    /// `insertEdges [(c, faConc, faPrem, p)]` (Reduction.hs) with both facts
    /// read from the endpoint nodes; see [`insert_edge_with_facts`](Self::insert_edge_with_facts).
    pub fn insert_edge(&mut self, e: Edge) -> Result<SystemOutcome, crate::prove::ProveError> {
        // HS `nodeConcFact` / `nodePremFact` (System.hs) fail unless both
        // endpoints are system nodes with the indexed facts.
        let fact = |node, conc: bool, idx: usize| {
            let (_, rule) = self
                .sys
                .nodes
                .iter()
                .find(|(n, _)| n == node)
                .expect("edge endpoint must be a system node");
            let facts = if conc {
                &rule.conclusions
            } else {
                &rule.premises
            };
            facts
                .get(idx)
                .cloned()
                .expect("edge endpoint fact index must exist")
        };
        let fa_conc = fact(&e.src.0, true, e.src.1 .0);
        let fa_prem = fact(&e.tgt.0, false, e.tgt.1 .0);
        self.insert_edge_with_facts(e, &fa_conc, &fa_prem)
    }

    /// `insertEdges [(c, faConc, faPrem, p)]` (Reduction.hs) with the facts
    /// in hand: `solveFactEqs SplitNow`, then `modM sEdges` in every
    /// resulting branch. The premise's fact need not come from a node (the
    /// abstract goal of `solvePremise`). On unification failure it mirrors
    /// `noContradictoryEqStore` via `mark_contradictory`, and the edge is
    /// never added.
    pub fn insert_edge_with_facts(
        &mut self,
        e: Edge,
        fa_conc: &crate::fact::LNFact,
        fa_prem: &crate::fact::LNFact,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        let res = if fa_conc != fa_prem {
            self.solve_fact_eqs(
                SplitStrategy::SplitNow,
                &[tamarin_term::rewriting::Equal {
                    lhs: fa_conc.clone(),
                    rhs: fa_prem.clone(),
                }],
            )?
        } else {
            SystemOutcome::Linear
        };
        Ok(match res {
            SystemOutcome::Contradictory => {
                self.mark_contradictory();
                SystemOutcome::Contradictory
            }
            SystemOutcome::Linear => {
                let before = self.sys.edges.len();
                self.sys.add_edge(e);
                if self.sys.edges.len() != before {
                    self.changed = ChangeIndicator::Changed;
                }
                SystemOutcome::Linear
            }
            SystemOutcome::Cases(mut arms) => {
                for arm in &mut arms {
                    arm.sys.add_edge(e.clone());
                }
                SystemOutcome::Cases(arms)
            }
        })
    }

    /// `insertLast` (Reduction.hs): set the last atom, or equate `i` with
    /// the existing one by `solveNodeIdEqs`.
    pub fn insert_last(
        &mut self,
        i: crate::constraint::constraints::NodeId,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        match self.sys.last_atom {
            None => {
                // Pure ADD (last_atom None→Some): the max can only rise
                // by this node id — bump instead of invalidating.
                self.sys.bump_cache_lvar(&i);
                self.sys.set_last_atom(Some(i));
                self.changed = ChangeIndicator::Changed;
                Ok(SystemOutcome::Linear)
            }
            Some(j) if j == i => Ok(SystemOutcome::Linear),
            Some(j) => {
                let res =
                    self.solve_node_id_eqs(&[tamarin_term::rewriting::Equal { lhs: i, rhs: j }]);
                let res = res?;
                if matches!(res, SystemOutcome::Contradictory) {
                    self.mark_contradictory();
                } else {
                    self.changed = ChangeIndicator::Changed;
                }
                Ok(res)
            }
        }
    }

    /// `substSystem` (Reduction.hs): apply the equation store's
    /// substitution to every part of the system.
    pub fn subst_system(&mut self) -> Result<(), crate::prove::ProveError> {
        // Only the node-ID phase runs to a fixed point. Applying the rest
        // of the system between its rounds can merge goals prematurely,
        // before a colliding rule contributes its message equalities.
        // A pass that raised no signal is a no-op at its (content, subst)
        // stamps; while both stamps are unchanged, skip the pass entirely.
        if self.sys.subst_marker_matches() {
            return Ok(());
        }
        if !self.subst_system_once()? {
            self.sys.record_subst_marker();
        }
        Ok(())
    }

    /// Haskell's substNodeIds settles colliding node labels and their rule
    /// equalities before any goal, formula or rule body is substituted. In
    /// particular, do not collapse aliased KU goals under an intermediate
    /// substitution: a rule equality may still change their message terms.
    fn subst_node_ids(&mut self) -> Result<bool, crate::prove::ProveError> {
        let mut changed = false;
        loop {
            let subst = self.sys.eq_store().subst.clone();
            let no_disj = |_: &[Guarded]| None;
            let pass = crate::apply::SystemSubst::new(&subst, false, &no_disj);
            let mut nodes = std::sync::Arc::unwrap_or_clone(std::mem::take(
                &mut self.sys.content_mut_untracked().nodes,
            ));
            // `substNodeIds` (Reduction.hs) reads nodes in ID order. Stable
            // grouping then retains the lowest original ID's rule on collision.
            nodes.sort_by_key(|a| a.0);
            // `substNodes` settles ID collisions and solves equalities between
            // the un-substituted rules before substituting their bodies.
            // An ID rename or collision invalidates both max caches; sorting
            // alone leaves their values and bounds unchanged.
            let mut nodes_value_changed = false;
            let renamed = nodes
                .into_iter()
                .map(|(id, rule)| {
                    let new_id = match id.apply_changed(&pass) {
                        Some(v) => {
                            nodes_value_changed = true;
                            v
                        }
                        None => id,
                    };
                    (new_id, rule)
                })
                .collect();
            let GroupedNodes {
                nodes: new_nodes,
                equalities: rule_eqs,
            } = group_node_rules(renamed);
            let collided = !rule_eqs.is_empty();
            if nodes_value_changed || collided {
                self.sys.invalidate_max_var_idx_cache();
                self.sys.invalidate_node_max_cache();
            }
            self.sys.content_mut_untracked().nodes = std::sync::Arc::new(new_nodes);
            // The shared solver validates rule/fact shapes and batches all
            // conclusions, then premises, then actions. SplitLater leaves
            // branching to the ordinary equality-goal continuation.
            if collided
                && matches!(
                    self.solve_rule_eqs(SplitStrategy::SplitLater, &rule_eqs)?,
                    SystemOutcome::Contradictory
                )
            {
                // Substitution callers also detect failure through gfalse;
                // solve_rule_eqs itself maintains the equation-store marker.
                self.mark_contradictory();
            }
            changed |= nodes_value_changed || collided;
            if self.sys.eq_store().is_false() || !collided {
                return Ok(changed);
            }
            // Each continuing round removed at least one node, so this loop is
            // bounded by the original node count, not an arbitrary iteration cap.
        }
    }

    /// One complete substSystem operation, with a node-ID fixed point followed
    /// by one substitution of the remaining fields.
    /// Returns `true` iff this pass raised ANY change signal (value, order,
    /// collision, rule-eq, or KU re-insert).  `subst_system` sets the
    /// verified-identity skip marker only after a pass that returns `false`.
    fn subst_system_once(&mut self) -> Result<bool, crate::prove::ProveError> {
        if self.sys.eq_store().subst.is_empty() {
            return Ok(false);
        }
        let node_ids_changed = self.subst_node_ids()?;
        if self.sys.eq_store().is_false() {
            return Ok(true);
        }
        let subst = self.sys.eq_store().subst.clone();
        // A section invalidates the max-var caches only when it changed a
        // value: re-sorting or deduplicating equal values cannot change the
        // maximum.
        // `substGoals` (Reduction.hs) substitutes DisjG bodies; normalising
        // the alternatives keeps the goal key equal to the stored GDisj's.
        let disj = |alts: &[Guarded]| -> Option<Vec<Guarded>> {
            let mapped = tamarin_utils::cow::cow_map_vec(alts, |alt| {
                crate::guarded::subst_guarded_cow(alt, &subst)
            });
            let children: &[Guarded] = mapped.as_deref().unwrap_or(alts);
            match crate::guarded::normalise_disj_list_cow(children) {
                Some(normalised) => Some(normalised),
                None => mapped,
            }
        };
        // `subst` is non-empty here, so the domain bloom is non-zero and the
        // `u64::MAX` default fact bloom always descends.
        let pass = crate::apply::SystemSubst::new(&subst, true, &disj);
        // Node IDs and their collision equalities have already converged.
        let mut nodes_value_changed = node_ids_changed;
        let mut new_nodes = std::sync::Arc::unwrap_or_clone(std::mem::take(
            &mut self.sys.content_mut_untracked().nodes,
        ));
        // Then `M.map . apply` over the surviving rules. The facts are not
        // normalised, as in Haskell: normalising would erase the non-normal
        // shapes that source matching and `has_non_normal_terms` read.
        for (_, rule) in new_nodes.iter_mut() {
            if let Some(new_rule) = rule.apply_changed(&pass) {
                nodes_value_changed = true;
                *rule = new_rule;
            }
        }
        // subst_system rewrites node terms (and may merge colliding node
        // ids) — the node max can DROP, so invalidate the node component
        // too, not just the full cache.  Conditional: an identity pass
        // (no id renamed, no collision, every rule COW-unchanged) leaves
        // the node multiset value-identical, so both caches stay exact.
        if nodes_value_changed {
            self.sys.invalidate_max_var_idx_cache();
            self.sys.invalidate_node_max_cache();
        }
        self.sys.content_mut_untracked().nodes = std::sync::Arc::new(new_nodes);
        // 2. Edges: rewrite both endpoints' node ids.  Track value
        // changes for the conditional cache invalidation — the sort +
        // dedup below only reorder / drop EQUAL values, which cannot
        // change the max free-var idx.
        let mut edges_value_changed = false;
        for e in self.sys.content_mut_untracked().edges.iter_mut() {
            if let Some(new_edge) = e.apply_changed(&pass) {
                edges_value_changed = true;
                *e = new_edge;
            }
        }
        // Full (non-adjacent) dedup: see comment in
        // simplify::apply_node_eqs.  Vec::dedup() only removes
        // adjacent duplicates; after var-rename the duplicates may
        // be scattered, so we must sort first.
        let mut tmp: Vec<_> = std::mem::take(&mut self.sys.content_mut_untracked().edges);
        tmp.sort();
        tmp.dedup();
        if edges_value_changed {
            self.sys.invalidate_max_var_idx_cache();
        }
        self.sys.content_mut_untracked().edges = tmp;
        // 3. Last-atom.
        let mut last_atom_changed = false;
        if let Some(last) = self.sys.content_mut_untracked().last_atom.take() {
            let new_last = match last.apply_changed(&pass) {
                Some(v) => {
                    last_atom_changed = true;
                    self.sys.invalidate_max_var_idx_cache();
                    v
                }
                None => last,
            };
            self.sys.content_mut_untracked().last_atom = Some(new_last);
        }
        // 4. Substitute and deduplicate less atoms, matching `substLessAtoms`
        // and `S.map (apply subst)` (Reduction.hs, SubstVFree.hs).
        let mut new_less: Vec<crate::constraint::constraints::LessAtom> =
            Vec::with_capacity(self.sys.less_atoms.len());
        // `LessAtom::Eq` ignores the reason. Keep the first occurrence of
        // each endpoint pair, preserving insertion order.
        let mut seen_less: tamarin_utils::FastSet<(
            crate::constraint::constraints::NodeId,
            crate::constraint::constraints::NodeId,
        )> = tamarin_utils::FastSet::default();
        // Change bit for the conditional cache invalidation — the dedup
        // drops only atoms whose image EQUALS a kept one, so an
        // all-identity rewrite cannot change the max free-var idx.
        let mut less_value_changed = false;
        for la in std::mem::take(&mut self.sys.content_mut_untracked().less_atoms) {
            let la = match la.apply_changed(&pass) {
                Some(n) => {
                    less_value_changed = true;
                    n
                }
                None => la,
            };
            if seen_less.insert((la.smaller, la.larger)) {
                new_less.push(la);
            }
        }
        if less_value_changed {
            self.sys.invalidate_max_var_idx_cache();
        }
        self.sys.content_mut_untracked().less_atoms = new_less;
        // 5. Rewrite goal free variables. Equal goals retain their first
        // position and combine solved/looping flags and the minimum age.
        // A changed KU action can allocate while only part of the goal map
        // is installed. Reserve against the complete system before that rebuild.
        let needs_reinsert = |goal: &Goal| {
            let Goal::Action(_, fact) = goal else {
                return false;
            };
            fact.tag == crate::fact::FactTag::Ku
                && fact.terms.first().is_some_and(|term| {
                    (tamarin_term::lterm::is_msg_var(term) || is_product_or_union(term))
                        && term.apply_changed(&pass).is_some_and(|new| new != *term)
                })
        };
        let reinserts_actions = self.sys.goals.iter().any(|(goal, _)| needs_reinsert(goal));
        if reinserts_actions {
            self.maude.ensure_above(bounds_max(&self.sys));
            self.sys.invalidate_max_var_idx_cache();
        }
        let mut goals = std::sync::Arc::unwrap_or_clone(std::mem::take(
            &mut self.sys.content_mut_untracked().goals,
        ));
        // `substGoals` (Reduction.hs) traverses Goal-Ord order. Reinserted
        // KU message-variable goals receive fresh goal numbers, so this
        // traversal order determines their relative ages.
        goals.sort_by(|(g1, _), (g2, _)| g1.cmp(g2));
        // Mirror node-fact handling above: apply the eq-store
        // substitution to each goal term with no Maude normalization.
        // HS's `substGoals` applies subst via the `Apply` instance and
        // does NOT normalise; `normDG` runs only inside impliedOrInitial
        // (System.hs).
        // Track semantic changes separately from rebuilding the goal map.
        let mut goals_value_changed = false;
        // `substGoals` (Reduction.hs) re-inserts a KU action whose
        // message variable, product or union changed, so `insertAction`
        // decomposes it again.
        let mut had_insert_action = false;
        for (g, st) in goals {
            // Haskell re-inserts changed KU terms even when the old goal
            // was solved. A later equality can change the required knowledge
            // again; retaining its solved status also loses an insertion age.
            // Status-only changes cannot trigger this path, preserving the
            // verified-identity skip's goals_mut status-flip carve-out.
            let needs_reinsert = reinserts_actions && needs_reinsert(&g);
            let action_node = match &g {
                Goal::Action(i, _) => Some(*i),
                _ => None,
            };
            let g2 = match g.apply_changed(&pass) {
                Some(n) => {
                    goals_value_changed = true;
                    n
                }
                None => g,
            };
            if needs_reinsert {
                // HS deliberately re-inserts at the original node: only the
                // fact is substituted in `insertAction i (apply subst fa)`.
                // The next substitution pass merges renamed node aliases.
                if let (Some(i), Goal::Action(_, fa)) = (action_node, &g2) {
                    had_insert_action = true;
                    self.insert_goal(Goal::Action(i, fa.clone()));
                }
            } else {
                // `M.insertWith combineGoalStatus` (Reduction.hs): goals the
                // substitution makes equal merge their statuses (solved and
                // looping ORed, the smaller number kept). Rebuilt in one
                // pass in Goal order, as HS's forM over M.toList.
                self.sys.bump_cache_goal(&g2);
                let new_goals =
                    std::sync::Arc::make_mut(&mut self.sys.content_mut_untracked().goals);
                if let Some(i) = new_goals.iter().position(|(k, _)| *k == g2) {
                    // A status merge that changes a kept
                    // goal's status is a real System mutation with no term
                    // signal.  Flag it so the "zero change" verdict is exact.
                    goals_value_changed |= new_goals[i].1.merge_from(&st);
                } else {
                    new_goals.push((g2, st));
                }
            }
        }
        if goals_value_changed && !reinserts_actions {
            self.sys.invalidate_max_var_idx_cache();
        }
        // `substFormulas`, `substSolvedFormulas`, `substLemmas`.
        let mut formulas_value_changed =
            subst_stored_formulas(self.sys.formulas_mut_untracked(), &subst);
        formulas_value_changed |=
            subst_stored_formulas(self.sys.solved_formulas_mut_untracked(), &subst);
        formulas_value_changed |=
            subst_stored_formulas(&mut self.sys.content_mut_untracked().lemmas, &subst);
        if formulas_value_changed {
            self.sys.invalidate_max_var_idx_cache();
            self.changed = ChangeIndicator::Changed;
        }
        // `instance Apply LNSubst SubtermStore` (SubtermStore.hs): the
        // positive, negative and solved subterms, not the old negative ones,
        // and without normalising. A rebuilt term is compared by value, since
        // an AC re-sort can rebuild an equal term.
        let mut changed_sst = false;
        let mut apply_constraints =
            |cs: Vec<crate::tools::subterm_store::SubtermConstraint>| -> Vec<_> {
                cs.into_iter()
                    .map(|c| match c.apply_changed(&pass) {
                        Some(nc) => {
                            if nc != c {
                                changed_sst = true;
                            }
                            nc
                        }
                        None => c,
                    })
                    .collect()
            };
        let new_subs =
            apply_constraints(std::mem::take(&mut self.sys.subterm_store_mut().subterms));
        let new_solved = apply_constraints(std::mem::take(
            &mut self.sys.subterm_store_mut().solved_subterms,
        ));
        // negSubterms (HS field `a`) get substituted too; oldNegSubterms
        // (field `e`) do NOT — this is what re-arms the simpSplitNegSt
        // change-detection (`negSubterms \ oldNegSubterms`) after a
        // substitution alters a stored negative subterm.
        let new_negs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)> =
            std::mem::take(&mut self.sys.subterm_store_mut().neg_subterms)
                .into_iter()
                .map(|pair| match pair.apply_changed(&pass) {
                    Some(np) => {
                        if np != pair {
                            changed_sst = true;
                        }
                        np
                    }
                    None => pair,
                })
                .collect();
        self.sys.subterm_store_mut().subterms = new_subs;
        self.sys.subterm_store_mut().solved_subterms = new_solved;
        // `rebuild_from` sorts AND dedups, establishing the sorted-unique set
        // invariant on the rewritten pairs — the substitution can collapse two
        // distinct stored pairs onto the same value.
        self.sys.subterm_store_mut().neg_subterms =
            crate::tools::subterm_store::SortedPairSet::rebuild_from(new_negs);
        if changed_sst {
            self.sys.invalidate_max_var_idx_cache();
            self.changed = ChangeIndicator::Changed;
        }
        // `self.changed` alone does not cover node/edge/less/goal/last-atom
        // rewrites, so OR every section's signal.
        let raised = nodes_value_changed
            || edges_value_changed
            || last_atom_changed
            || less_value_changed
            || goals_value_changed
            || formulas_value_changed
            || changed_sst
            || had_insert_action;
        if raised {
            self.sys.bump_content_stamp();
        }
        Ok(raised)
    }

    /// `solveRuleConstraints` (Reduction.hs): add the rule's variants as a
    /// new disjunction, insert its `SplitG` goal and simplify the store. A
    /// `None` or empty `substs` is a no-op. Returns `true` when the store
    /// became false (`noContradictoryEqStore`), so the caller drops the
    /// branch.
    pub fn solve_rule_constraints(
        &mut self,
        substs: Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>,
    ) -> Result<bool, crate::prove::ProveError> {
        let substs = match substs {
            Some(v) if !v.is_empty() => v,
            _ => return Ok(false),
        };
        // Haskell `addRuleVariants` errors if domain of variants
        // intersects with eq-store free subst — that case isn't
        // supported there either. We don't enforce it; the worst case
        // is a redundant SplitG entry that simplify will discharge.
        let id = self.sys.eq_store_mut().add_disj(substs);
        // `insertGoal (SplitG splitId)` comes before `simp` and always
        // advances the goal number, even when simp folds a singleton variant
        // disjunction into the substitution and orphans the goal.
        self.insert_goal(Goal::Split(id));
        {
            let maude = self.maude.clone();
            let store = std::sync::Arc::unwrap_or_clone(self.sys.take_eq_store());
            self.sys.invalidate_max_var_idx_cache();
            self.sys
                .set_eq_store(std::sync::Arc::new(store.simp(&maude, |_, _| false)?));
            // eq_store simp can rewrite/drop subst entries → max may lower.
            self.sys.invalidate_max_var_idx_cache();
            // The orphaned SplitG goal stays until the next
            // `removeSolvedSplitGoals`, and no `substSystem` runs here: the
            // simplifier's next iteration re-keys goals and nodes, as in HS.
        }
        self.changed = ChangeIndicator::Changed;
        Ok(self.sys.eq_store().is_false())
    }

    /// Insert a `<` atom.
    pub fn insert_less(&mut self, l: LessAtom) {
        let before = self.sys.less_atoms.len();
        self.sys.add_less(l);
        if self.sys.less_atoms.len() != before {
            self.changed = ChangeIndicator::Changed;
        }
    }

    /// Add a new goal.
    pub fn insert_goal(&mut self, g: Goal) {
        self.insert_goal_with_loop_flag(g, false);
    }

    /// Add a new goal with an explicit loop-breaker flag, matching
    /// Haskell's `insertGoal goal isLoopBreaker`. The flag controls
    /// `gsLoopBreaker` in the resulting status — used by the smart
    /// ranker to deprioritise premises that would otherwise loop.
    pub fn insert_goal_with_loop_flag(&mut self, g: Goal, looping: bool) {
        // HS insertAction checks membership before inserting ANY action.
        if matches!(&g, Goal::Action(_, _)) && self.sys.goals.iter().any(|(old, _)| old == &g) {
            return;
        }
        // `insertAction` (Reduction.hs): `KU` of a pair, inverse, product
        // or union inserts the outer goal, then a `KU` goal per component at
        // a fresh node ordered before it.
        if let Goal::Action(node_id, fa) = &g
            && fa.tag == crate::fact::FactTag::Ku
            && let Some(top) = fa.terms.first()
            && let Some(sub_terms) = ku_decomp_subterms(top)
        {
            let outer_node = *node_id;
            // HS-faithful order (Reduction.hs):
            //   insertGoal goal False                     -- outer FIRST
            //   requiresKU m1 *> requiresKU m2 ...        -- sub-goals after
            let before = self.sys.goals.len();
            self.sys.add_goal_with_loop_flag(g.clone(), looping);
            if self.sys.goals.len() != before {
                self.changed = ChangeIndicator::Changed;
            }
            for sub in sub_terms {
                let sub_node = self.fresh_lvar("vk", tamarin_term::lterm::LSort::Node);
                // requiresKU draws from the enclosing FreshT counter, which
                // also reserves variables no longer visible in this system.
                let sub_fa = crate::fact::ku_fact(sub);
                self.insert_goal_with_loop_flag(Goal::Action(sub_node, sub_fa), looping);
                self.insert_less(crate::constraint::constraints::LessAtom::new(
                    sub_node,
                    outer_node,
                    crate::constraint::constraints::Reason::Adversary,
                ));
            }
            return;
        }
        let before = self.sys.goals.len();
        self.sys.add_goal_with_loop_flag(g, looping);
        if self.sys.goals.len() != before {
            self.changed = ChangeIndicator::Changed;
        }
    }

    /// Compute a fresh-var baseline — the max var idx across all vars in
    /// nodes' rules, stored & solved formulas, lemmas, edges, less-atoms,
    /// subterm store, goals and the eq-store substitution (everything
    /// folded by `bounds_max`/`bounds_max_uncached`, which already includes
    /// `formulas.chain(solved_formulas).chain(lemmas)` via `max_var_idx`).
    ///
    /// Returns the plain max — no extra headroom is added. Used by `Ex`
    /// decomposition to pick fresh var indices.
    pub fn fresh_var_baseline(&self) -> u64 {
        bounds_max(&self.sys)
    }

    /// HS `insertAtom` (Reduction.hs):
    ///
    /// - `EqE(x, y)`     → `solveTermEqs SplitNow`
    /// - `Less(i, j)`    → `insertLess` with the `Formula` reason
    /// - `Last(t)`       → `insertLast`
    /// - `Action(t, fa)` → `insertAction`
    /// - `Subterm(s, b)` → `insertSubterm`
    /// - `Syntactic(_)`  → nothing
    ///
    /// HS reads the three timepoints with `ltermNodeId'`, which errors on any other sort; the
    /// total [`lterm_node_id`] answers `None` there and the atom is dropped.
    pub fn insert_atom(
        &mut self,
        a: &crate::atom::Atom<tamarin_term::lterm::LNTerm>,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        use crate::atom::ProtoAtom;
        match a {
            ProtoAtom::EqE(x, y) => {
                match self.solve_term_eqs(
                    SplitStrategy::SplitNow,
                    &[tamarin_term::rewriting::Equal::new(x.clone(), y.clone())],
                )? {
                    SystemOutcome::Contradictory => {
                        self.mark_contradictory();
                        return Ok(SystemOutcome::Contradictory);
                    }
                    SystemOutcome::Linear => {}
                    SystemOutcome::Cases(arms) => {
                        self.changed = ChangeIndicator::Changed;
                        return Ok(SystemOutcome::Cases(arms));
                    }
                }
                self.changed = ChangeIndicator::Changed;
            }
            ProtoAtom::Less(i, j) => {
                let (Some(ni), Some(nj)) = (lterm_node_id(i), lterm_node_id(j)) else {
                    return Ok(SystemOutcome::Linear);
                };
                // Normalise through the eq-store substitution so any
                // earlier node-id merges propagate to this fresh atom.
                let ni = normalise_node_id(ni, &self.sys.eq_store().subst);
                let nj = normalise_node_id(nj, &self.sys.eq_store().subst);
                self.insert_less(crate::constraint::constraints::LessAtom::new(
                    ni,
                    nj,
                    crate::constraint::constraints::Reason::Formula,
                ));
            }
            ProtoAtom::Last(t) => {
                let Some(n) = lterm_node_id(t) else {
                    return Ok(SystemOutcome::Linear);
                };
                // HS-faithful insertLast (Reduction.hs).
                if let SystemOutcome::Cases(arms) = self.insert_last(n)? {
                    return Ok(SystemOutcome::Cases(arms));
                }
            }
            ProtoAtom::Action(t, fact) => {
                let Some(n) = lterm_node_id(t) else {
                    return Ok(SystemOutcome::Linear);
                };
                self.insert_goal(Goal::Action(n, fact.clone()));
            }
            ProtoAtom::Subterm(s, b) => {
                // Pure ADD (`SubtermStore::add` is a plain push, no
                // removal): the max can only rise by the two new terms —
                // bump both sides instead of invalidating.
                self.sys.bump_cache_term(s);
                self.sys.bump_cache_term(b);
                self.sys.subterm_store_mut().add(s.clone(), b.clone());
                self.changed = ChangeIndicator::Changed;
            }
            // HS `Syntactic _ -> return ()` (Reduction.hs): the sugar
            // carries no constraint.  `to_lnformula` refuses a formula that
            // still holds one (formula.rs), so no atom of a guarded formula
            // reaches this arm.
            ProtoAtom::Syntactic(_) => {}
        }
        Ok(SystemOutcome::Linear)
    }

    /// HS `insertFormula` (Reduction.hs): normalise `g`, then insert it
    /// with `mark` set.
    pub fn insert_formula(
        &mut self,
        g: Guarded,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        // Normalise at the insertion boundary so the stored-formula state
        // is ALWAYS in `normalise_stored_formula_cow` normal form — the dedup
        // checks inside `insert_formula_inner` compare against the
        // (post-substitution, normalised) stored sets.  Port of HS
        // insertFormula entry normalisation (150f5eba).
        let g = crate::guarded::normalise_stored_formula_owned(g);
        // Every path into the store builds its atoms through `fApp`, so the
        // AC and `C` argument lists arrive flat and sorted; a formula that
        // reached here another way would compare unequal to its own rebuild
        // and re-fire a discharged implied-formula disjunction.
        debug_assert!(
            crate::guarded::is_ac_canonical(&g),
            "a stored formula holds an argument list `fApp` would order differently: {g:?}"
        );
        self.insert_formula_inner(g, true)
    }

    /// Insert top-level formulas in order, distributing the remaining work
    /// over every equality branch.
    pub(crate) fn insert_formulas(
        &mut self,
        formulas: &[Guarded],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        let formulas = formulas
            .iter()
            .cloned()
            .map(crate::guarded::normalise_stored_formula_owned)
            .collect::<Vec<_>>();
        self.insert_formula_sequence(&formulas, true)
    }

    /// Insert a sequence with the same top-level marking policy, distributing
    /// the remaining formulas over every branch as soon as a split occurs.
    fn insert_formula_sequence(
        &mut self,
        formulas: &[Guarded],
        mark: bool,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        let Some((first, rest)) = formulas.split_first() else {
            return Ok(SystemOutcome::Linear);
        };
        Ok(match self.insert_formula_inner(first.clone(), mark)? {
            SystemOutcome::Linear => self.insert_formula_sequence(rest, mark)?,
            SystemOutcome::Contradictory => SystemOutcome::Contradictory,
            SystemOutcome::Cases(arms) => {
                self.continue_in_arms(arms, |branch| branch.insert_formula_sequence(rest, mark))?
            }
        })
    }

    /// HS `insertFormula`'s `insert mark` (Reduction.hs): reduce `g` by the
    /// CR-rules S_∧, S_∃, S_{¬,⋖}, S_{¬,last} and the negated node-equality
    /// and subterm rules, store a disjunction with its `DisjG` goal, and
    /// keep any other universal for saturation. Only a top-level formula
    /// (`mark`) is recorded as solved, except an existential, which always
    /// is so it is not opened twice.
    fn insert_formula_inner(
        &mut self,
        g: Guarded,
        mark: bool,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        use crate::atom::ProtoAtom;
        if crate::guarded::stores_contains(&self.sys.formulas, &g)
            || crate::guarded::stores_contains(&self.sys.solved_formulas, &g)
        {
            return Ok(SystemOutcome::Linear);
        }
        // Every rule but an unmarked atom and an already-known negative
        // subterm changes the system.
        let changed_before = self.changed;
        if !matches!(g, Guarded::Atom(_)) || mark {
            self.changed = ChangeIndicator::Changed;
        }
        match &g {
            Guarded::Conj(items) => {
                let items = items.to_vec();
                self.mark_as_solved(mark, g);
                self.insert_formula_sequence(&items, false)
            }
            Guarded::Disj(items) => {
                // The entry guard already excludes `g` from `formulas`.
                let goal = Goal::Disj(Disj::new(items.to_vec()));
                self.sys.push_open_formula_normalized_absent(g);
                self.insert_goal(goal);
                Ok(SystemOutcome::Linear)
            }
            Guarded::Atom(ga) => {
                // After markAsSolved, so every branch of an equality split
                // inherits the solved formula.
                let atom = crate::guarded::bvar_to_lvar(ga);
                self.mark_as_solved(mark, g);
                self.insert_atom(&atom)
            }
            Guarded::GGuarded {
                qua: crate::formula::Quantifier::Ex,
                vars,
                ..
            } => {
                self.sys.push_solved_formula_normalized_absent(g.clone());
                // `xs <- mapM (uncurry freshLVar) ss`: the binders take
                // consecutive indices in their lexical order.
                let base = self.fresh_idxs(vars.len() as u64);
                let mut fresh = tamarin_utils::fresh::FastFreshState::seeded(base);
                let (_, _xs, ats, opened_body) =
                    crate::guarded::open_guarded(&g, &mut fresh).expect("Ex arm matched GGuarded");
                // `gconj (map GAto as ++ [gf])` over the opened guards.
                let mut items: Vec<Guarded> = ats
                    .iter()
                    .map(|a| Guarded::Atom(crate::guarded::lift_free_atom(a)))
                    .collect();
                items.push(opened_body);
                self.insert_formula_inner(crate::guarded::gconj(items), false)
            }
            Guarded::GGuarded {
                qua: crate::formula::Quantifier::All,
                vars,
                guards,
                body,
            } if vars.is_empty() && guards.len() == 1 && **body == crate::guarded::gfalse() => {
                let both_nodes = |i: &crate::formula::BLNTerm, j: &crate::formula::BLNTerm| {
                    blterm_node_id(i).is_some() && blterm_node_id(j).is_some()
                };
                let guard = &guards[0];
                let reducible = match guard {
                    ProtoAtom::Less(i, j) | ProtoAtom::EqE(i, j) => both_nodes(i, j),
                    ProtoAtom::Last(_) | ProtoAtom::Subterm(..) => true,
                    _ => false,
                };
                if !reducible {
                    self.sys.push_open_formula_normalized_absent(g);
                    return Ok(SystemOutcome::Linear);
                }
                self.mark_as_solved(mark, g.clone());
                let alternatives = match guard {
                    // ¬(i ⋖ j) ⇒ i = j ∨ j ⋖ i
                    ProtoAtom::Less(i, j) => [
                        ProtoAtom::EqE(i.clone(), j.clone()),
                        ProtoAtom::Less(j.clone(), i.clone()),
                    ],
                    // ¬(i = j) on nodes ⇒ i ⋖ j ∨ j ⋖ i
                    ProtoAtom::EqE(i, j) => [
                        ProtoAtom::Less(i.clone(), j.clone()),
                        ProtoAtom::Less(j.clone(), i.clone()),
                    ],
                    // ¬last(i) ⇒ j ⋖ i ∨ i ⋖ j for the last node j, drawing
                    // `j <- freshLVar "last"` and `insertLast j` if unset.
                    ProtoAtom::Last(i) => {
                        let j = self.sys.last_atom.unwrap_or_else(|| {
                            let j = self.fresh_lvar("last", tamarin_term::lterm::LSort::Node);
                            self.sys.bump_cache_lvar(&j);
                            self.sys.set_last_atom(Some(j));
                            j
                        });
                        let j: crate::formula::BLNTerm =
                            tamarin_term::vterm::var_term(tamarin_term::lterm::BVar::Free(j));
                        [
                            ProtoAtom::Less(j.clone(), i.clone()),
                            ProtoAtom::Less(i.clone(), j),
                        ]
                    }
                    // ¬(s ⊏ b) ⇒ `insertNegSubterm`: consumed into the
                    // subterm store, never stored as a formula.
                    ProtoAtom::Subterm(s, b) => {
                        self.sys.invalidate_max_var_idx_cache();
                        if !self
                            .sys
                            .subterm_store_mut()
                            .add_neg(bterm_to_lterm(s), bterm_to_lterm(b))
                        {
                            self.changed = changed_before;
                        }
                        return Ok(SystemOutcome::Linear);
                    }
                    _ => unreachable!("only reducible guards reach here"),
                };
                let d =
                    crate::guarded::gdisj(alternatives.into_iter().map(Guarded::Atom).collect());
                self.insert_formula_inner(d, false)
            }
            // Other universals are stored for saturation.
            Guarded::GGuarded { .. } => {
                self.sys.push_open_formula_normalized_absent(g);
                Ok(SystemOutcome::Linear)
            }
        }
    }

    /// `markAsSolved = when mark $ modM sSolvedFormulas (S.insert fm)`.
    fn mark_as_solved(&mut self, mark: bool, g: Guarded) {
        if mark {
            self.sys.push_solved_formula_normalized_absent(g);
        }
    }

    /// Mark a goal as solved (if present). Mirrors
    /// `markGoalAsSolved`.
    pub fn mark_goal_as_solved(&mut self, g: &Goal) {
        // Mirrors Haskell `markGoalAsSolved` (Reduction.hs):
        //   ActionG / Premise(non-KD) / Split / Subterm → updateStatus
        //   Premise(KD) / Chain                          → DELETE
        //   Disj → move formula to solved_formulas + updateStatus
        let should_delete = match g {
            Goal::Chain(_, _) => true,
            Goal::Premise(_, fa) => matches!(fa.tag, crate::fact::FactTag::Kd),
            _ => false,
        };
        if should_delete {
            let before = self.sys.goals.len();
            self.sys.invalidate_max_var_idx_cache();
            self.sys.goals_mut().retain(|(eg, _)| eg != g);
            if self.sys.goals.len() != before {
                self.changed = ChangeIndicator::Changed;
            }
            return;
        }
        // Disjunction goals also move the formula from formulas →
        // solved_formulas (Haskell `markGoalAsSolved` DisjG branch).
        if let Goal::Disj(d) = g {
            use crate::guarded::Guarded;
            let f = Guarded::Disj(d.0.clone().into());
            let pos = self.sys.formulas.iter().position(|x| **x == f);
            if let Some(idx) = pos {
                self.sys.invalidate_max_var_idx_cache();
                self.sys.formulas_mut().remove(idx);
                if !crate::guarded::stores_contains(&self.sys.solved_formulas, &f) {
                    self.sys.insert_solved_formula(f);
                }
                self.changed = ChangeIndicator::Changed;
            }
        }
        for (existing, status) in self.sys.goals_mut().iter_mut() {
            if existing == g && !status.solved {
                status.solved = true;
                self.changed = ChangeIndicator::Changed;
                break;
            }
        }
    }

    /// `removeSolvedSplitGoals` (Reduction.hs): drop every `SplitG` goal
    /// whose split no longer exists in the equation store, solved or not.
    pub fn remove_solved_split_goals(&mut self) {
        use crate::constraint::constraints::Goal as G;
        let valid: std::collections::BTreeSet<_> = self
            .sys
            .eq_store()
            .conj
            .iter()
            .map(|d| d.split_id)
            .collect();
        let before = self.sys.goals.len();
        self.sys.invalidate_max_var_idx_cache();
        self.sys.goals_mut().retain(|(g, _status)| match g {
            // HS-faithful: drop the goal whenever the split_id no
            // longer backs an eq-store disjunction (ignore solved
            // flag).
            G::Split(id) => valid.contains(id),
            _ => true,
        });
        if self.sys.goals.len() != before {
            self.changed = ChangeIndicator::Changed;
        }
    }
}

// =============================================================================
// Equality solving — bridges into the equation store
// =============================================================================

/// Whether to perform a case-split immediately or defer it as a goal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SplitStrategy {
    SplitNow,
    SplitLater,
}

/// `IsACConstructor` (Reduction.hs, #883): whether the equality being solved
/// involves an AC-constructor rule (carrying the rule's two premise
/// variables) or not.  Used to remove redundant AC-permutation unifiers
/// before a `SplitNow` split.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsAcConstructor {
    AcConstructor(tamarin_term::lterm::LVar, tamarin_term::lterm::LVar),
    OtherRule,
}

/// HS `getKUVars` applied to the first two premises of the rule
/// `solveAction` just labelled the node with — the
/// `ACConstructor (head prems) (prems!!1)` tag it hands to `solveFactEqs`
/// (Goals.hs; `getKUVars`, Goals.hs).
///
/// `removePermutations` may only drop unifier arms that permute the rule's
/// OWN `KU` premise variables, so the two variables must come from `KU(x)`
/// premises and nowhere else.  HS forces `head prems` / `prems !! 1` lazily
/// and `error`s on any other premise shape; RS reads the same two slots and
/// answers `OtherRule` instead, which leaves every unifier arm in place.
fn ku_vars(rule: &crate::rule::RuleACInst) -> IsAcConstructor {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let ku_var = |f: &crate::fact::LNFact| match &*f.terms {
        [Term::Lit(Lit::Var(v))] if f.tag == crate::fact::FactTag::Ku => Some(*v),
        _ => None,
    };
    match (
        rule.premises.first().and_then(ku_var),
        rule.premises.get(1).and_then(ku_var),
    ) {
        (Some(v1), Some(v2)) => IsAcConstructor::AcConstructor(v1, v2),
        _ => IsAcConstructor::OtherRule,
    }
}

/// `flatten` from HS `solveListEqs` (Reduction.hs): a list equality
/// becomes one equality per position, `zipWith Equal l r`, appended to `out`.
/// Positions beyond the shorter list are dropped, so a caller that owes HS's
/// `contradictoryIf (not $ all evalEqual $ map (fmap length) eqs)` checks the
/// lengths itself before calling.
fn flatten_list_eq<T: Clone>(
    lhs: &[T],
    rhs: &[T],
    out: &mut Vec<tamarin_term::rewriting::Equal<T>>,
) {
    for (a, b) in lhs.iter().zip(rhs.iter()) {
        out.push(tamarin_term::rewriting::Equal {
            lhs: a.clone(),
            rhs: b.clone(),
        });
    }
}

/// Outcome of an operation that can split complete systems.
#[derive(Debug)]
#[must_use = "every split branch must be continued or deliberately discarded"]
pub enum SystemOutcome {
    /// Single case — the same `Reduction` continues.
    Linear,
    /// Complete systems for every surviving case.
    Cases(Vec<SystemBranch>),
    /// The conjunction is contradictory in every case.
    Contradictory,
}

/// One complete branch of a split: its system and the FreshT counter its
/// continuation resumes from.
#[derive(Debug)]
pub struct SystemBranch {
    pub sys: System,
    pub counter: u64,
}

/// Resume `k` in every branch, in order, and collect the completed branches:
/// the continuation of a Haskell `DisjT` split. A `Linear` continuation
/// contributes its own system and counter, `Cases` its branches (any
/// number), `Contradictory` nothing.
pub(crate) fn continue_in_arms<'c>(
    ctx: &'c ProofContext,
    arms: Vec<SystemBranch>,
    mut k: impl FnMut(&mut Reduction<'c>) -> Result<SystemOutcome, crate::prove::ProveError>,
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    let mut completed = Vec::new();
    for arm in arms {
        let mut branch = Reduction::new_inheriting(ctx, arm.sys, arm.counter);
        match k(&mut branch)? {
            SystemOutcome::Linear => completed.push(branch.into_branch()),
            SystemOutcome::Cases(arms) => completed.extend(arms),
            SystemOutcome::Contradictory => {}
        }
    }
    Ok(completed)
}

impl<'ctx> Reduction<'ctx> {
    /// This reduction's state as a completed branch.
    pub(crate) fn into_branch(self) -> SystemBranch {
        SystemBranch {
            counter: self.maude.fresh_counter_peek(),
            sys: self.sys,
        }
    }

    /// The branches `outcome` leaves: this reduction itself when it is
    /// linear, none when contradictory.
    pub(crate) fn outcome_branches(self, outcome: SystemOutcome) -> Vec<SystemBranch> {
        match outcome {
            SystemOutcome::Linear => vec![self.into_branch()],
            SystemOutcome::Cases(arms) => arms,
            SystemOutcome::Contradictory => Vec::new(),
        }
    }

    /// [`continue_in_arms`], with the result normalized by
    /// [`finish_system_cases`](Self::finish_system_cases).
    pub(crate) fn continue_in_arms(
        &mut self,
        arms: Vec<SystemBranch>,
        k: impl FnMut(&mut Reduction<'ctx>) -> Result<SystemOutcome, crate::prove::ProveError>,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        let completed = continue_in_arms(self.ctx, arms, k)?;
        Ok(self.finish_system_cases(completed))
    }

    /// Normalize complete-system alternatives at a branching boundary.
    /// A singleton is a linear continuation, so adopt both its system and
    /// exact FreshT position in the caller. Thus every `Cases` returned by
    /// this helper contains at least two branches; source-error sentinels and
    /// other producers remain outside this invariant.
    pub(crate) fn finish_system_cases(&mut self, mut cases: Vec<SystemBranch>) -> SystemOutcome {
        match cases.len() {
            0 => SystemOutcome::Contradictory,
            1 => {
                let branch = cases.pop().unwrap();
                self.sys = branch.sys;
                self.maude.reset_counter_to(branch.counter);
                self.changed = ChangeIndicator::Changed;
                SystemOutcome::Linear
            }
            _ => SystemOutcome::Cases(cases),
        }
    }

    /// `solveTermEqs` — add a list of term equalities to the equation
    /// store, optionally splitting if the unifier produced more than
    /// one disjunct. Mirrors the Haskell function in
    /// `Theory.Constraint.Solver.Reduction`.
    #[track_caller]
    pub fn solve_term_eqs(
        &mut self,
        strategy: SplitStrategy,
        eqs: &[tamarin_term::rewriting::Equal<tamarin_term::lterm::LNTerm>],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        self.solve_term_eqs_ac(strategy, IsAcConstructor::OtherRule, eqs)
    }

    /// [`solve_term_eqs`](Self::solve_term_eqs) with the AC-constructor tag
    /// threaded through, so a `SplitNow` fan-out can drop unifier arms that
    /// only permute the rule's two `KU` premise variables.
    #[track_caller]
    fn solve_term_eqs_ac(
        &mut self,
        strategy: SplitStrategy,
        is_ac: IsAcConstructor,
        eqs: &[tamarin_term::rewriting::Equal<tamarin_term::lterm::LNTerm>],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        // Filter out trivially-equal equations.
        let pending: Vec<_> = eqs.iter().filter(|e| e.lhs != e.rhs).cloned().collect();
        if pending.is_empty() {
            return Ok(SystemOutcome::Linear);
        }

        // Take eq_store out of self, mutate it, put it back, then
        // borrow Maude — this avoids overlapping borrows of self.
        let maude = self.maude.clone();
        let split = self.sys.eq_store_mut().add_eqs(&maude, &pending)?;
        // Run simp with substCreatesNonNormalTerms as the is_contr
        // predicate.  Without it, SplitG variants that would
        // introduce non-normal terms (e.g. verify=sign(...)) aren't
        // filtered; Haskell uses this exact check.  Gated to non-
        // empty reducible signatures — pair-only theories never
        // produce non-normal subterms structurally so the check is
        // pure overhead.  See contradictions.rs::subst_creates_non_normal_terms.
        let has_reducible = !maude.maude_sig().reducible_fun_syms.is_empty();
        // HS's curried `substCreatesNonNormalTerms hnd se` (Reduction.hs):
        // one walk of the system, shared by every candidate substitution.
        // Signatures without reducible symbols skip it.
        let nf_checker = has_reducible.then(|| {
            crate::constraint::solver::contradictions::SubstNfChecker::new(&maude, &self.sys)
        });
        let store = std::sync::Arc::unwrap_or_clone(self.sys.take_eq_store());
        // Use `EquationStore::simp` so singleton SplitG disjunctions
        // get folded into `subst` via `simp_singleton`.  Haskell's `simp`
        // (EquationStore.hs) calls `simpSingleton` as part of the
        // main loop, so by the time the search sees the goal list, a
        // singleton variant subst is already in `subst`.
        let maude_alloc = maude.clone();
        // Closure-style helper: simp one EquationStore with the same
        // non-normal-terms predicate.  Reused for both
        // the no-split branch and the per-arm SplitNow loop below.
        // `nf_checker.is_some()` iff `has_reducible` (built via
        // `has_reducible.then(...)`), so the checker's presence IS the
        // reducible-symbol dispatch: `as_ref()` is `Some` exactly when
        // the non-normal-terms check must run.
        let do_simp = |s: crate::tools::equation_store::EquationStore| -> Result<
            crate::tools::equation_store::EquationStore,
            crate::prove::ProveError,
        > { simp_store(s, nf_checker.as_ref(), &maude_alloc) };

        match (split, strategy) {
            (Some(id), SplitStrategy::SplitNow) => {
                // `disjunctionOfList (performSplit eqs2 splitId)`, then
                // `simp` and `noContradictoryEqStore` in each arm
                // (Reduction.hs `solveTermEqs`). For an AC-constructor
                // equality, `removePermutations` (#883) first drops arms
                // that only permute the rule's two premise variables.
                let store = match is_ac {
                    IsAcConstructor::AcConstructor(v1, v2) => {
                        store.remove_permutations(&maude, id, &v1, &v2)?
                    }
                    IsAcConstructor::OtherRule => store,
                };
                let arms = store.perform_split(id).ok_or_else(|| {
                    crate::tools::equation_store::AddEqsError::Maude(format!(
                        "split id {:?} not found",
                        id
                    ))
                })?;
                let mut live_arms = simp_split_arms(&maude_alloc, arms, do_simp)?;
                if live_arms.is_empty() {
                    // All arms contradicted under per-arm simp.
                    // Install a false store so downstream is_false
                    // checks see it (mirrors HS noContradictoryEqStore
                    // firing mzero on every arm).
                    self.sys.invalidate_max_var_idx_cache();
                    self.sys.set_eq_store(std::sync::Arc::new(
                        crate::tools::equation_store::EquationStore::default().set_false(),
                    ));
                    return Ok(SystemOutcome::Contradictory);
                }
                self.changed = ChangeIndicator::Changed;
                if live_arms.len() == 1 {
                    // Single arm survived: install as the current
                    // eq_store and return Linear (no caller-side fork
                    // needed).
                    self.sys.invalidate_max_var_idx_cache();
                    let (store, counter) = live_arms.pop().unwrap();
                    self.sys.set_eq_store(std::sync::Arc::new(store));
                    self.maude.reset_counter_to(counter);
                    Ok(SystemOutcome::Linear)
                } else {
                    // Each arm is the pre-split system with its own store.
                    Ok(SystemOutcome::Cases(
                        live_arms
                            .into_iter()
                            .map(|(store, counter)| {
                                let mut sys = self.sys.clone();
                                sys.invalidate_max_var_idx_cache();
                                sys.set_eq_store(std::sync::Arc::new(store));
                                SystemBranch { sys, counter }
                            })
                            .collect(),
                    ))
                }
            }
            (Some(id), SplitStrategy::SplitLater) => {
                // No split fanout — simp once on the combined store.
                self.sys.invalidate_max_var_idx_cache();
                self.sys.set_eq_store(std::sync::Arc::new(do_simp(store)?));
                if self.sys.eq_store().is_false() {
                    return Ok(SystemOutcome::Contradictory);
                }
                self.insert_goal(crate::constraint::constraints::Goal::Split(id));
                self.changed = ChangeIndicator::Changed;
                Ok(SystemOutcome::Linear)
            }
            (None, _) => {
                // No split — simp once.
                self.sys.invalidate_max_var_idx_cache();
                self.sys.set_eq_store(std::sync::Arc::new(do_simp(store)?));
                if self.sys.eq_store().is_false() {
                    return Ok(SystemOutcome::Contradictory);
                }
                self.changed = ChangeIndicator::Changed;
                Ok(SystemOutcome::Linear)
            }
        }
    }

    /// `solveNodeIdEqs` — equalities between node-id variables.
    pub fn solve_node_id_eqs(
        &mut self,
        eqs: &[tamarin_term::rewriting::Equal<crate::constraint::constraints::NodeId>],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let term_eqs: Vec<tamarin_term::rewriting::Equal<tamarin_term::lterm::LNTerm>> = eqs
            .iter()
            .map(|e| tamarin_term::rewriting::Equal {
                lhs: Term::Lit(Lit::Var(e.lhs)),
                rhs: Term::Lit(Lit::Var(e.rhs)),
            })
            .collect();
        self.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs)
    }

    /// `solveFactEqs` (Reduction.hs): `contradictoryIf` on a tag or arity
    /// mismatch (which also marks the store false, the `mzero` proxy), then
    /// `solveTermEqs` over the argument lists.
    #[track_caller]
    pub fn solve_fact_eqs(
        &mut self,
        strategy: SplitStrategy,
        eqs: &[tamarin_term::rewriting::Equal<crate::fact::LNFact>],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        self.solve_fact_eqs_ac(strategy, IsAcConstructor::OtherRule, eqs)
    }

    /// [`solve_fact_eqs`](Self::solve_fact_eqs) with the AC-constructor tag
    /// forwarded to [`solve_term_eqs_ac`](Self::solve_term_eqs_ac).
    #[track_caller]
    fn solve_fact_eqs_ac(
        &mut self,
        strategy: SplitStrategy,
        is_ac: IsAcConstructor,
        eqs: &[tamarin_term::rewriting::Equal<crate::fact::LNFact>],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        for e in eqs {
            if e.lhs.tag != e.rhs.tag || e.lhs.terms.len() != e.rhs.terms.len() {
                // Set eq_store.is_false so the SolveGoal-arm mzero
                // proxy filter (the SolveGoal-arm eq_store.is_false()
                // case-drop in `exec_proof_method`, proof_method.rs)
                // sees the contradiction even if the caller `let _ = ...`s
                // our result.  Mirrors Haskell's `contradictoryIf`
                // (Reduction.hs) firing mzero on tag mismatch.
                self.set_eq_store_false();
                return Ok(SystemOutcome::Contradictory);
            }
        }
        let mut flat = Vec::new();
        for e in eqs {
            flatten_list_eq(&e.lhs.terms, &e.rhs.terms, &mut flat);
        }
        self.solve_term_eqs_ac(strategy, is_ac, &flat)
    }

    /// `solveRuleEqs` (Reduction.hs): `contradictoryIf` on differing rule
    /// infos (or fact-list lengths), then `solveFactEqs` over all
    /// conclusions, then all premises, then all actions.
    pub fn solve_rule_eqs(
        &mut self,
        strategy: SplitStrategy,
        eqs: &[tamarin_term::rewriting::Equal<RuleACInst>],
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        // Rule infos and all three fact-list lengths must match before the
        // lists are zipped. Otherwise an unmatched suffix would be ignored.
        for e in eqs {
            if e.lhs.info != e.rhs.info
                || e.lhs.conclusions.len() != e.rhs.conclusions.len()
                || e.lhs.premises.len() != e.rhs.premises.len()
                || e.lhs.actions.len() != e.rhs.actions.len()
            {
                self.set_eq_store_false();
                return Ok(SystemOutcome::Contradictory);
            }
        }
        // Haskell `solveRuleEqs` (Reduction.hs) feeds `solveFactEqs`
        // `map (fmap (get rConcs)) eqs ++ map (fmap (get rPrems)) eqs
        //  ++ map (fmap (get rActs)) eqs`, i.e. ALL conclusions across every
        // eq, THEN all premises, THEN all actions (a batch transpose, not a
        // per-eq conc/prem/act interleave).
        let mut conc_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> = Vec::new();
        let mut prem_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> = Vec::new();
        let mut act_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> = Vec::new();
        for e in eqs {
            flatten_list_eq(&e.lhs.conclusions, &e.rhs.conclusions, &mut conc_eqs);
            flatten_list_eq(&e.lhs.premises, &e.rhs.premises, &mut prem_eqs);
            flatten_list_eq(&e.lhs.actions, &e.rhs.actions, &mut act_eqs);
        }
        let mut fact_eqs: Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> =
            Vec::with_capacity(conc_eqs.len() + prem_eqs.len() + act_eqs.len());
        fact_eqs.append(&mut conc_eqs);
        fact_eqs.append(&mut prem_eqs);
        fact_eqs.append(&mut act_eqs);
        self.solve_fact_eqs(strategy, &fact_eqs)
    }

    /// `setNodes` (Reduction.hs): keep the first rule per node id and solve
    /// `solveRuleEqs SplitLater` between colliding rules. `nodes` is the
    /// complete node list.
    pub fn set_nodes(
        &mut self,
        nodes: Vec<(crate::constraint::constraints::NodeId, RuleACInst)>,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        let GroupedNodes {
            nodes: canonical,
            equalities: rule_eqs,
        } = group_node_rules(nodes);
        // Canonical node merge dedups colliding ids (dropping duplicate
        // rules) — node max can DROP, invalidate the node component too.
        self.sys.invalidate_max_var_idx_cache();
        self.sys.invalidate_node_max_cache();
        self.sys.content_mut_untracked().nodes = std::sync::Arc::new(canonical);
        if rule_eqs.is_empty() {
            return Ok(SystemOutcome::Linear);
        }
        self.changed = ChangeIndicator::Changed;
        self.solve_rule_eqs(SplitStrategy::SplitLater, &rule_eqs)
    }

    /// `conjoinSystem` (Reduction.hs): merge `sys`, typically an
    /// instantiated source case, into this system in Haskell's step order.
    pub fn conjoin_system(
        &mut self,
        sys: &System,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        // 1-3. joinSets: solved_formulas, lemmas, edges.  Use sets so
        // duplicates are collapsed (HasFrees-based dedup not needed —
        // syntactic equality is sufficient for these sets).
        for f in &sys.solved_formulas {
            self.sys.insert_solved_formula(f.clone());
        }
        for l in &sys.lemmas {
            if !crate::guarded::stores_contains(&self.sys.lemmas, l) {
                self.sys.invalidate_max_var_idx_cache();
                self.sys.lemmas_mut().push(l.clone());
            }
        }
        for e in &sys.edges {
            self.sys.add_edge(e.clone());
        }
        // 4. insertLast: HS-faithful (Reduction.hs + conjoinSystem
        // Reduction.hs `F.mapM_ insertLast $ get sLastAtom sys`).
        if let Some(case_last) = &sys.last_atom {
            match self.insert_last(*case_last) {
                Err(error) => return Err(error),
                Ok(SystemOutcome::Contradictory) => {
                    return Ok(SystemOutcome::Contradictory);
                }
                Ok(SystemOutcome::Linear | SystemOutcome::Cases(_)) => {}
            }
        }
        // 5. insertLess.
        for l in &sys.less_atoms {
            self.insert_less(l.clone());
        }
        // 6. insertGoalStatus for every non-split goal (split ids are not
        // valid here), in Goal order as HS's `M.toList`, so new goals are
        // numbered in that order.
        let mut conjoin_goals: Vec<&(
            crate::constraint::constraints::Goal,
            crate::constraint::system::GoalStatus,
        )> = sys.goals.iter().collect();
        conjoin_goals.sort_by(|a, b| a.0.cmp(&b.0));
        for (g, st) in conjoin_goals {
            if matches!(g, crate::constraint::constraints::Goal::Split(_)) {
                continue;
            }
            // HS `insertGoalStatus` runs `succ sNextGoalNr` on EVERY
            // non-split goal — even when the goal key already exists,
            // where `insertWith combineGoalStatus` keeps the smaller nr.
            // Route both the new and the already-present case through
            // `add_goal_with_loop_flag` so the counter advances
            // unconditionally, keeping RS's `next_goal_nr` (and the
            // goalNrRanking tie-break) aligned with HS on every conjoin
            // that hits a shared goal.
            // Then OR-in `solved` (combineGoalStatus) on the matching slot.
            self.sys.add_goal_with_loop_flag(g.clone(), st.looping);
            if st.solved
                && let Some((_, slot)) = self.sys.goals_mut().iter_mut().find(|(eg, _)| eg == g)
            {
                slot.solved = true;
            }
        }
        // 7. insertFormula, decomposing each formula by the CR-rules.
        let formulas = sys
            .formulas
            .iter()
            .map(|formula| formula.as_ref().clone())
            .collect::<Vec<_>>();
        match self.insert_formulas(&formulas)? {
            SystemOutcome::Linear => self.conjoin_system_tail(sys),
            SystemOutcome::Contradictory => Ok(SystemOutcome::Contradictory),
            SystemOutcome::Cases(inputs) => {
                let outcome =
                    self.continue_in_arms(inputs, |branch| branch.conjoin_system_tail(sys))?;
                if matches!(outcome, SystemOutcome::Contradictory) {
                    self.mark_contradictory();
                }
                Ok(outcome)
            }
        }
    }

    /// Continue `conjoinSystem` after its formula-decomposition step. Formula
    /// equality splits call this once per complete branch, so node merging,
    /// substitution solving, and substitution propagation cannot be lost or
    /// accidentally evaluated only against arm zero.
    fn conjoin_system_tail(
        &mut self,
        sys: &System,
    ) -> Result<SystemOutcome, crate::prove::ProveError> {
        // 8. setNodes (case_nodes ++ live_nodes).
        let mut all_nodes: Vec<_> = (*sys.nodes).clone();
        all_nodes.extend(self.sys.nodes.iter().cloned());
        match self.set_nodes(all_nodes) {
            Err(error) => return Err(error),
            Ok(SystemOutcome::Contradictory) => {
                return Ok(SystemOutcome::Contradictory);
            }
            Ok(SystemOutcome::Linear | SystemOutcome::Cases(_)) => {}
        }
        // 9. addDisj for each case conjDisjEq entry.  Track new split-ids.
        let mut new_split_ids: Vec<crate::tools::equation_store::SplitId> = Vec::new();
        for disj in &sys.eq_store().conj {
            let id = self.sys.eq_store_mut().add_disj(disj.substs.clone());
            new_split_ids.push(id);
        }
        // 10. conjoinSubtermStores — HS-faithful (SubtermStore.hs).
        // Mirrors HS `modM sSubtermStore (conjoinSubtermStores (get sSubtermStore sys))`
        // at Reduction.hs.
        self.sys.subterm_store_mut().conjoin(&sys.subterm_store);
        // 11. insertGoal(SplitG) for each new split-id.
        for id in new_split_ids {
            self.insert_goal(crate::constraint::constraints::Goal::Split(id));
        }
        // 12. solveSubstEqs SplitNow on case's flat subst, then
        // 13. substSystem, in every branch of the split.
        let case_subst_eqs: Vec<_> = sys
            .eq_store()
            .subst
            .to_list()
            .into_iter()
            .map(|(v, t)| tamarin_term::rewriting::Equal {
                lhs: tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)),
                rhs: t,
            })
            .collect();
        match self.solve_term_eqs(SplitStrategy::SplitNow, &case_subst_eqs)? {
            SystemOutcome::Contradictory => Ok(SystemOutcome::Contradictory),
            SystemOutcome::Linear => {
                self.subst_system()?;
                Ok(SystemOutcome::Linear)
            }
            SystemOutcome::Cases(arms) => {
                let outcome = self.continue_in_arms(arms, |arm| {
                    arm.subst_system()?;
                    Ok(if arm.sys.eq_store().is_false() {
                        SystemOutcome::Contradictory
                    } else {
                        SystemOutcome::Linear
                    })
                })?;
                if matches!(outcome, SystemOutcome::Contradictory) {
                    self.mark_contradictory();
                }
                Ok(outcome)
            }
        }
    }
}

// =============================================================================
// Helpers used by goal solving.
// =============================================================================

/// The `RuleACInst` of an `OpenProtoRule` (HS `someRuleACInst`,
/// Model/Rule.hs): its abstracted form, with reducible-headed subterms
/// replaced by fresh variables, when it has one.
pub(crate) fn canonical_rule_inst(o: &crate::theory::OpenProtoRule) -> RuleACInst {
    // Always prefer the abstracted rule (reducible-headed sub-terms
    // narrowed to fresh `z_i` vars) when present, falling back to the
    // raw rule otherwise.
    let src: &crate::rule::ProtoRuleE = o.abstracted_rule.as_ref().unwrap_or(&o.rule);
    crate::rule::Rule {
        info: crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: src.info.name,
            attributes: src.info.attributes.clone(),
            loop_breakers: o.loop_breakers.clone(),
        }),
        premises: src.premises.clone(),
        conclusions: src.conclusions.clone(),
        actions: src.actions.clone(),
        new_vars: src.new_vars.clone(),
    }
}

pub(crate) fn intr_rule_to_rule_ac_inst(ir: crate::rule::IntrRuleAC) -> RuleACInst {
    crate::rule::Rule {
        info: crate::rule::RuleInfo::Intr(ir.info),
        premises: ir.premises,
        conclusions: ir.conclusions,
        actions: ir.actions,
        new_vars: ir.new_vars,
    }
}

/// Build the implicit `Fresh` rule instance: `[] --[]-> [Fr(m)]`
/// with `m` as the new-vars. Mirrors Haskell's `mkFreshRuleAC`.
fn make_fresh_rule(m: tamarin_term::lterm::LNTerm) -> RuleACInst {
    let info = crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
        name: crate::rule::ProtoRuleName::Fresh,
        attributes: crate::rule::RuleAttributes::empty(),
        loop_breakers: Vec::new(),
    });
    let conc = crate::fact::fresh_fact(m.clone());
    crate::rule::Rule::new(info, vec![], vec![conc], vec![]).with_new_vars(vec![m])
}

/// HS `substFormulas`, `substSolvedFormulas` or `substLemmas`
/// (Reduction.hs), `S.map (normaliseStoredFormula . apply subst)`: apply the
/// substitution, re-normalise each changed formula, and drop the formulas
/// that became equal, keeping the first. Answers whether a value changed.
fn subst_stored_formulas(
    store: &mut Vec<std::sync::Arc<Guarded>>,
    subst: &crate::tools::equation_store::LNSubst,
) -> bool {
    let mut changed = false;
    for f in store.iter_mut() {
        let Some(cur) = crate::guarded::subst_guarded_cow(f, subst) else {
            continue;
        };
        let new_f = crate::guarded::normalise_stored_formula_owned(cur);
        if new_f != **f {
            *f = std::sync::Arc::new(new_f);
            changed = true;
        }
    }
    dedup_preserve_order(store);
    changed
}

/// Dedup a Vec in place while preserving the FIRST occurrence's position.
fn dedup_preserve_order<T: PartialEq + std::hash::Hash>(v: &mut Vec<T>) {
    let first = first_occurrences(v);
    let mut keep = first.iter();
    v.retain(|_| *keep.next().unwrap_or(&false));
}

/// For each item, whether it is the first of the items equal to it.
///
/// Long lists are grouped by hash and compared with `==` only within a
/// group, so the result is the same as comparing each item with every
/// earlier one, without the quadratic number of comparisons: formula lists
/// in long proof branches grow to thousands of entries, and the comparison
/// of two similar formulas walks deep into both.  Needs `Hash` to agree
/// with `PartialEq` (equal items hash equal), as derived `Hash` does.
pub(crate) fn first_occurrences<T: PartialEq + std::hash::Hash>(items: &[T]) -> Vec<bool> {
    // Short lists: compare directly. Formulas that differ usually differ
    // near the top, so each comparison stops early, while a hash walks the
    // whole formula (measured: UM_three_pass's lists stay below 24 and got
    // slower with hashing; OTPoverSMS_MA reaches lists of 4,000+).
    if items.len() <= 32 {
        return (0..items.len())
            .map(|i| !(0..i).any(|k| items[k] == items[i]))
            .collect();
    }
    let mut by_hash: tamarin_utils::FastMap<u64, Vec<usize>> = Default::default();
    items
        .iter()
        .enumerate()
        .map(|(i, x)| {
            let group = by_hash.entry(tamarin_utils::fx_hash_one(x)).or_default();
            let first = !group.iter().any(|&k| items[k] == *x);
            if first {
                group.push(i);
            }
            first
        })
        .collect()
}

/// HS `annotatePrems` (inside `solveAction`, Goals.hs): union `fa`'s
/// annotations into every premise and action of the intruder rule `ru`.
fn annotate_prems(ru: &RuleACInst, fa: &crate::fact::LNFact) -> RuleACInst {
    let annotate = |f: &crate::fact::LNFact| {
        let mut f = f.clone();
        f.annotations.extend(fa.annotations.iter().copied());
        f
    };
    let mut ru = ru.clone();
    ru.premises = ru.premises.iter().map(annotate).collect();
    ru.actions = ru.actions.iter().map(annotate).collect();
    ru
}

/// HS `mkISendRuleAC ann m` (Reduction.hs): `[KU(m)[ann]] --[K(m)]-> [In(m)]`,
/// where `ann` are the `In` premise's annotations and `K` is the protocol
/// fact `kLogFact`.
fn make_isend_rule(fa_in: &crate::fact::LNFact, m: tamarin_term::lterm::LNTerm) -> RuleACInst {
    let info = crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend);
    let mut prem = crate::fact::ku_fact(m.clone());
    prem.annotations = fa_in.annotations.clone();
    let act = crate::fact::k_log_fact(m.clone());
    let conc = crate::fact::in_fact(m);
    crate::rule::Rule::new(info, vec![prem], vec![conc], vec![act])
}

/// Apply an eq-store substitution to a node-id. Returns the new
/// representative if the subst maps `id` to a node-sort variable; else
/// the input unchanged.
fn normalise_node_id(
    id: crate::constraint::constraints::NodeId,
    subst: &crate::tools::equation_store::LNSubst,
) -> crate::constraint::constraints::NodeId {
    let id_term = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(id));
    let mapped = tamarin_term::subst::apply_vterm(subst, id_term);
    if let tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) = mapped {
        v
    } else {
        id
    }
}

/// `forbiddenEdge` — port of the chain-goal forbidden edge shapes.  RS has
/// no diff-mode proofs, so the HS `isDiffProof` split resolves to the
/// trace-mode branch (`isNDCRule`): no consecutive deconstruction rules for
/// NDC functions.
fn forbidden_edge(c_rule: &RuleACInst, p_rule: &RuleACInst) -> bool {
    use crate::rule::{
        get_remaining_rule_applications, is_d_emap_rule, is_d_exp_rule, is_d_pmult_rule,
        is_ndc_rule, rule_name_string,
    };
    if is_d_exp_rule(c_rule) && is_d_exp_rule(p_rule) {
        return true;
    }
    if is_d_pmult_rule(c_rule) && is_d_pmult_rule(p_rule) {
        return true;
    }
    if is_d_pmult_rule(c_rule) && is_d_emap_rule(p_rule) {
        return true;
    }
    let cn = rule_name_string(c_rule);
    let pn = rule_name_string(p_rule);
    if !cn.is_empty() && cn == pn && get_remaining_rule_applications(c_rule) == 1 {
        return true;
    }
    let c_ndc = is_ndc_rule(c_rule);
    c_ndc.is_some() && c_ndc == is_ndc_rule(p_rule)
}

/// `illegalCoerce` — port of the chain-goal illegal coerce check
/// (Goals.hs).  Returns `true` if `p_rule` is a Coerce rule and
/// the chain-conclusion's down-K message `mPrem` is a pair / inverse /
/// product (which N2 forbids).  Haskell tests the bare term `mPrem`
/// (`= case kFactView faConc of Just (DnK, m') -> m'`); the caller
/// passes the chain-conc KD fact, whose sole term is `mPrem`.
fn illegal_coerce(p_rule: &RuleACInst, fa_conc: &crate::fact::LNFact) -> bool {
    use crate::rule::is_coerce_rule_inst;
    if !is_coerce_rule_inst(p_rule) {
        return false;
    }
    if fa_conc.terms.len() != 1 {
        return false;
    }
    let t = &fa_conc.terms[0];
    tamarin_term::term::is_pair(t)
        || tamarin_term::term::is_inverse(t)
        || tamarin_term::term::is_product(t)
}

// Max-free-index walkers over the system's concrete types: HS
// `boundsVarIdx` restricted to the maximum, statically dispatched because
// `bounds_max` misses walk every node.
#[inline(always)]
pub(crate) fn bm_term(t: &tamarin_term::lterm::LNTerm, max: &mut u64) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => {
            if v.idx > *max {
                *max = v.idx;
            }
        }
        Term::Lit(Lit::Con(_)) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                bm_term(a, max);
            }
        }
    }
}

#[inline(always)]
pub(crate) fn bm_fact(fa: &crate::fact::LNFact, max: &mut u64) {
    // Per-fact cached max-var-idx fast-path: `Fact::fresh`/`fresh_annotated`
    // compute the EXACT max free-var idx of `fa.terms` in the same
    // `for_each_free` walk that builds the bloom (fact.rs `fact_fingerprints`),
    // and the value survives every unchanged pass.  On a cache hit fold that
    // single `u64` — a cached `0` (no frees, or a free var at idx 0) folds to
    // the same no-op the per-term descent performs.  The `u64::MAX` sentinel
    // (the no-`HasFrees` `Fact::new`/`map` constructors) falls back to the walk.
    match fa.max_var_cached() {
        Some(m) => {
            if m > *max {
                *max = m;
            }
        }
        None => {
            for t in fa.terms.iter() {
                bm_term(t, max);
            }
        }
    }
}

#[inline(always)]
fn bm_lvar(v: &tamarin_term::lterm::LVar, max: &mut u64) {
    if v.idx > *max {
        *max = v.idx;
    }
}

#[inline(always)]
pub(crate) fn bm_rule(r: &crate::rule::RuleACInst, max: &mut u64) {
    for f in &r.premises {
        bm_fact(f, max);
    }
    for f in &r.conclusions {
        bm_fact(f, max);
    }
    for f in &r.actions {
        bm_fact(f, max);
    }
    for t in &r.new_vars {
        bm_term(t, max);
    }
}

#[inline(always)]
pub(crate) fn bm_goal(g: &Goal, max: &mut u64) {
    match g {
        Goal::Action(i, fa) => {
            bm_lvar(i, max);
            bm_fact(fa, max);
        }
        Goal::Premise(p, fa) => {
            bm_lvar(&p.0, max);
            bm_fact(fa, max);
        }
        Goal::Chain(c, p) => {
            bm_lvar(&c.0, max);
            bm_lvar(&p.0, max);
        }
        Goal::Subterm((s, t)) => {
            bm_term(s, max);
            bm_term(t, max);
        }
        // A disjunction's variables are those of its stored formula.
        Goal::Disj(_) | Goal::Split(_) => {}
    }
}

/// The largest free variable index in the system (0 if none), through
/// the system's max-var cache.
pub fn bounds_max(sys: &System) -> u64 {
    if let Some(v) = sys.max_var_idx_cache.get() {
        return v;
    }
    // The node component is the dominant cost and survives the non-node
    // mutation sites (they clear only the full cache).
    let node_component = sys.node_max_cache.get().unwrap_or_else(|| {
        let nc = bounds_max_nodes(sys);
        sys.node_max_cache.set(Some(nc));
        nc
    });
    let v = node_component.max(bounds_max_rest(sys));
    sys.max_var_idx_cache.set(Some(v));
    v
}

/// HS `avoid` (LTerm.hs), `maybe 0 (succ . snd) . boundsVarIdx`: the next
/// index to draw, 0 when the system has no free variable.
pub fn avoid_fresh_state(sys: &System) -> u64 {
    let bm = bounds_max(sys);
    if bm > 0 || tamarin_term::lterm::bounds_var_idx(sys).is_some() {
        bm + 1
    } else {
        0
    }
}

/// Node-component of the max walk (the `sNodes` map: ids + rule frees).
/// This is the dominant cost of `bounds_max`, cached separately in
/// `System::node_max_cache` so the ~82 non-node mutation sites (which
/// clear only the full cache) don't force a re-walk of the node map.
pub fn bounds_max_nodes(sys: &System) -> u64 {
    let mut max = 0u64;
    for (id, rule) in sys.nodes.iter() {
        bm_lvar(id, &mut max);
        bm_rule(rule, &mut max);
    }
    max
}

/// Full-walk implementation of `bounds_max` — bypass for the cache.
/// Kept as the exact `max(nodes, rest)` full walk so the verify path
/// (`TAM_RS_VERIFY_BOUNDS_CACHE`) and the cache-disabled path stay
/// byte-faithful.
pub fn bounds_max_uncached(sys: &System) -> u64 {
    bounds_max_nodes(sys).max(bounds_max_rest(sys))
}

/// Non-node component of the max walk: edges / less / last / subterm
/// store / goals / formulas / eq-store.  Walked fresh on every
/// `bounds_max` miss (these fields are cheap relative to nodes and are
/// mutated by the majority of call sites, so caching them separately
/// would not pay off).
pub fn bounds_max_rest(sys: &System) -> u64 {
    let mut max = 0u64;
    for e in &sys.edges {
        bm_lvar(&e.src.0, &mut max);
        bm_lvar(&e.tgt.0, &mut max);
    }
    for l in &sys.less_atoms {
        bm_lvar(&l.smaller, &mut max);
        bm_lvar(&l.larger, &mut max);
    }
    if let Some(la) = &sys.last_atom {
        bm_lvar(la, &mut max);
    }
    // HS `HasFrees SubtermStore` folds `negSt <> st <> solvedSt`, not the
    // old negative subterms.
    for c in &sys.subterm_store.subterms {
        bm_term(&c.small, &mut max);
        bm_term(&c.big, &mut max);
    }
    for c in &sys.subterm_store.solved_subterms {
        bm_term(&c.small, &mut max);
        bm_term(&c.big, &mut max);
    }
    // HS `HasFrees SubtermStore` folds `negSt` too (and skips
    // `oldNegSubterms` — SubtermStore.hs).
    for (s, t) in &sys.subterm_store.neg_subterms {
        bm_term(s, &mut max);
        bm_term(t, &mut max);
    }
    for (g, _) in sys.goals.iter() {
        bm_goal(g, &mut max);
    }
    for f in sys
        .formulas
        .iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        let n = crate::guarded::max_var_idx(f);
        if n > max {
            max = n;
        }
    }
    for v in sys.eq_store().subst.dom() {
        if v.idx > max {
            max = v.idx;
        }
    }
    for t in sys.eq_store().subst.range() {
        bm_term(t, &mut max);
    }
    // HS `foldFrees` over a `SubstVFresh` visits only its keys
    // (SubstVFresh.hs): the range variables are fresh.
    for d in &sys.eq_store().conj {
        for s in &d.substs {
            for v in s.dom() {
                if v.idx > max {
                    max = v.idx;
                }
                // Range vars NOT counted (HS-faithful: foldFrees over keys).
            }
        }
    }
    max
}

/// HS `someRuleACInst = fmap extractInsts . rename` (Model/Rule.hs): one
/// index shift, drawn from the counter after lifting it above `avoid_max`,
/// renames the rule and the keys of its variant substitutions together.
/// The ranges count as fresh (SubstVFresh.hs) and are left as they are. A
/// pair without free variables draws nothing.
fn freshen_rule_with_constrs(
    rule: RuleACInst,
    constrs: Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>,
    avoid_max: u64,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> (
    RuleACInst,
    Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>,
) {
    let pair = (rule, constrs);
    if tamarin_term::lterm::bounds_var_idx(&pair).is_none() {
        return pair;
    }
    maude.ensure_above(avoid_max);
    tamarin_term::lterm::rename(pair, &mut &*maude)
}

/// simp one `EquationStore` with `EquationStore::simp`, drawing fresh
/// indices from the same `reserve_idxs` counter.  `Some(checker)` wires the
/// `substCreatesNonNormalTerms` predicate; `None` disables it
/// (`|_,_| false`), mirroring the `has_reducible` gate at the call sites.
/// Shared by `solve_term_eqs`'s `do_simp` and `solve_split_goal`'s
/// `simplify_picked`.
fn simp_store(
    store: crate::tools::equation_store::EquationStore,
    checker: Option<&crate::constraint::solver::contradictions::SubstNfChecker>,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<crate::tools::equation_store::EquationStore, crate::prove::ProveError> {
    Ok(match checker {
        Some(checker) => store.simp(maude, |fs, vfs| checker.check(fs, vfs))?,
        None => store.simp(maude, |_, _| false)?,
    })
}

/// Simplify each arm of an equation-store split. The arms fork DisjT below
/// FreshT, so each starts from the same counter; each live arm keeps the
/// counter its simplification left, contradictory arms are dropped, and the
/// shared counter ends at the highest one reached.
fn simp_split_arms(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    arms: Vec<crate::tools::equation_store::EquationStore>,
    simp: impl Fn(
        crate::tools::equation_store::EquationStore,
    ) -> Result<crate::tools::equation_store::EquationStore, crate::prove::ProveError>,
) -> Result<Vec<(crate::tools::equation_store::EquationStore, u64)>, crate::prove::ProveError> {
    let fork_base = maude.fresh_counter_peek();
    let mut high_water = fork_base;
    let mut live = Vec::new();
    for arm in arms {
        maude.reset_counter_to(fork_base);
        let simped = simp(arm)?;
        let counter = maude.fresh_counter_peek();
        high_water = high_water.max(counter);
        if !simped.is_false() {
            live.push((simped, counter));
        }
    }
    maude.ensure_above(high_water.saturating_sub(1));
    Ok(live)
}

/// Build `closeGuarded Ex [newVar] [EqE l r] gtrue` (HS Goals.hs `closeGuarded`).
/// `newVar` is the single existentially-bound variable; `l`/`r` are the
/// equation sides, free until `close_guarded` binds them.
fn close_guarded_ex_eq(
    new_var: &tamarin_term::lterm::LVar,
    s_plus: &tamarin_term::lterm::LNTerm,
    t: &tamarin_term::lterm::LNTerm,
) -> crate::guarded::Guarded {
    crate::guarded::close_guarded(
        crate::formula::Quantifier::Ex,
        vec![*new_var],
        vec![crate::atom::ProtoAtom::EqE(s_plus.clone(), t.clone())],
        crate::guarded::gtrue(),
    )
}

// =============================================================================
// Goal solving — concrete cases that don't need typed-rule unification
// =============================================================================

/// Outcome of `solve_*_goal` — mirrors the disjunctive branching of
/// the Haskell `Reduction` monad's case-split.
#[derive(Debug)]
pub enum GoalCases {
    /// One continuation tagged with a case name; `self.sys` was
    /// mutated in place.  Used for rule-instantiation goals whose
    /// candidate enumeration narrowed to exactly one rule — Haskell
    /// still prints `case <RuleName>` + `qed`.
    LinearNamed(String),
    /// Several continuations; each carries a case name plus the
    /// forked `System`. Case names match Haskell's `prettyProof`:
    /// rule-instantiation cases use the rule name; disjunction /
    /// other splits use `case_1`/`case_2`/...
    Cases(Vec<GoalBranch>),
    /// Dead branch — the goal is false.
    Contradictory,
}

/// One named branch of a goal solve, including the FreshT position from
/// which its simplify continuation must resume.
#[derive(Debug)]
pub struct GoalBranch {
    pub name: String,
    pub sys: System,
    pub counter: u64,
}

/// Name every branch of a goal solve's case `name`.
fn named_cases(name: &str, branches: Vec<SystemBranch>) -> impl Iterator<Item = GoalBranch> + '_ {
    branches.into_iter().map(move |b| GoalBranch {
        name: name.to_string(),
        sys: b.sys,
        counter: b.counter,
    })
}

/// True iff the term is an AC product (Mult) or union.
fn is_product_or_union(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    matches!(
        t,
        Term::App(FunSym::Ac(AcSym::Mult), _) | Term::App(FunSym::Ac(AcSym::Union), _)
    )
}

fn ku_decomp_subterms(t: &tamarin_term::lterm::LNTerm) -> Option<Vec<tamarin_term::lterm::LNTerm>> {
    use tamarin_term::function_symbols::{AcSym, FunSym, INV_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::NoEq(s), args) if s.name == b"pair" && args.len() == 2 => {
            Some(args.to_vec())
        }
        Term::App(FunSym::NoEq(s), args) if s.name == INV_SYM_STRING && args.len() == 1 => {
            Some(args.to_vec())
        }
        // `insertAction` (Reduction.hs) allocates fresh KU nodes in the
        // term-Ord order exposed by `viewTerm2`. Sort AC decomposition
        // terms to preserve that allocation order after substitution.
        Term::App(FunSym::Ac(AcSym::Mult | AcSym::Union), args) => {
            let mut v = args.to_vec();
            v.sort();
            Some(v)
        }
        _ => None,
    }
}

/// Default case-name fallback when callers don't provide a specific
/// name: `case_1`, `case_2`, ... (1-indexed, matching Haskell's
/// printer).
pub fn default_case_name(i: usize) -> String {
    format!("case_{}", i + 1)
}

/// HS `caseName mPrem` (Goals.hs `solveChain`) for a direct chain edge:
/// `showLitName` of a literal, `showFunSymName` of an application. `None`
/// unless `fa_conc` is a `KD` fact.
pub fn chain_direct_case_name(fa_conc: &crate::fact::LNFact) -> Option<String> {
    use crate::fact::FactTag;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    if !matches!(fa_conc.tag, FactTag::Kd) {
        return None;
    }
    let m = fa_conc.terms.first()?;
    Some(match m {
        Term::Lit(Lit::Var(v)) => {
            // Haskell `showLitName (Var (LVar v s i))`:
            //   body | null v   = show i
            //        | i == 0   = v
            //        | otherwise = show i ++ "_" ++ v
            let body = if v.name.is_empty() {
                v.idx.to_string()
            } else if v.idx == 0 {
                v.name.to_string()
            } else {
                format!("{}_{}", v.idx, v.name)
            };
            format!("Var_{}_{}", tamarin_term::lterm::sort_suffix(v.sort), body)
        }
        Term::Lit(Lit::Con(name)) => {
            // Haskell `showLitName` (LTerm.hs):
            //   Con (Name FreshName n) -> "Const_fresh_" ++ show n
            //   Con (Name PubName   n) -> "Const_pub_"   ++ show n
            // (`show n` = the raw NameId string, LTerm.hs).
            // showLitName has no Node/Nat/Abbrev arm (Haskell would crash); a
            // direct close on such a constant is not expected for KD
            // facts, so emit a stable shaped fallback for those.
            use tamarin_term::lterm::NameTag;
            match name.tag {
                NameTag::Fresh => format!("Const_fresh_{}", name.id.as_str()),
                NameTag::Pub => format!("Const_pub_{}", name.id.as_str()),
                NameTag::Node => format!("Const_node_{}", name.id.as_str()),
                NameTag::Nat => format!("Const_nat_{}", name.id.as_str()),
                NameTag::Abbrev => format!("Const_abbrev_{}", name.id.as_str()),
            }
        }
        // `showFunSymName` (Term.hs, #883 rendering): builtin AC/C symbols
        // print their `*SymString` names ("mun"/"mult"/"xor"/"tplus"/"em"),
        // user symbols their own name.
        Term::App(sym, _) => crate::intruder_rules::show_fun_sym_name(sym).into_owned(),
    })
}

/// Derive a Haskell-style case name for a rule-instantiation case.
/// Matches `Theory.Constraint.Solver.Reduction.casName` conventions:
/// protocol rules use their declared name, intruder constructors use
/// `c_<head>`, destructors use `d_<head>`, fresh-construction uses
/// `fresh`, coercion uses `coerce`, IRecv/ISend use their internal
/// names.
pub fn rule_case_name(rule: &crate::rule::RuleACInst) -> String {
    use crate::rule::{IntrRuleACInfo, ProtoRuleName, RuleInfo};
    match &rule.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Fresh => "Fresh".to_string(),
            ProtoRuleName::Stand(s) => s.to_string(),
        },
        RuleInfo::Intr(i) => match i {
            IntrRuleACInfo::ConstrRule { name, .. } => {
                // The constructor's stored name carries a leading
                // underscore (see `intruder_rules.rs`); strip it
                // here so the case label matches Haskell's printer:
                // `c_h` not `c__h`.
                let s = String::from_utf8_lossy(name);
                let trimmed = s.strip_prefix('_').unwrap_or(&s);
                format!("c_{}", trimmed)
            }
            IntrRuleACInfo::DestrRule { name, .. } => {
                let s = String::from_utf8_lossy(name);
                let trimmed = s.strip_prefix('_').unwrap_or(&s);
                format!("d_{}", trimmed)
            }
            IntrRuleACInfo::Coerce => "coerce".to_string(),
            IntrRuleACInfo::IRecv => "irecv".to_string(),
            IntrRuleACInfo::ISend => "isend".to_string(),
            // Built-in constructor rules render without the `c_` prefix —
            // Haskell `prettyIntrRuleACInfo` (Model/Rule.hs) emits "pub",
            // "nat", "fresh", reserving the `c` prefix for named user
            // constructors (ConstrRule name → 'c' : name).
            IntrRuleACInfo::PubConstr => "pub".to_string(),
            IntrRuleACInfo::NatConstr => "nat".to_string(),
            IntrRuleACInfo::FreshConstr => "fresh".to_string(),
            IntrRuleACInfo::IEquality => "iequality".to_string(),
        },
    }
}

impl<'ctx> Reduction<'ctx> {
    /// `solveDisjunction` (Goals.hs): one case `case_i` per alternative,
    /// inserting it with `insertFormula`. A lone alternative is still
    /// named `case_1`.
    pub(crate) fn solve_disj_goal(
        &mut self,
        disj: &Disj<Guarded>,
    ) -> Result<GoalCases, crate::prove::ProveError> {
        let alts = &disj.0;
        Ok(match alts.len() {
            0 => GoalCases::Contradictory,
            1 => {
                // Route through the decomposing inserter so atomic /
                // existential / disjunctive alternatives generate their
                // own sub-goals (Haskell `insertFormula`).  Raw-pushing
                // leaks Disj/Ex bodies past is_finished (see the
                // companion fix in `insert_implied_formulas_pass`).
                match self.insert_formula(alts[0].clone())? {
                    SystemOutcome::Linear => GoalCases::LinearNamed("case_1".to_string()),
                    SystemOutcome::Cases(arms) => {
                        GoalCases::Cases(named_cases("case_1", arms).collect())
                    }
                    SystemOutcome::Contradictory => GoalCases::Contradictory,
                }
            }
            _ => {
                let mut cases = Vec::with_capacity(alts.len());
                for (i, gfm) in alts.iter().enumerate() {
                    // HS FreshT-threading: each disjunct branch continues
                    // the enclosing thread (see `new_inheriting`).
                    let mut sub = Reduction::new_inheriting(
                        self.ctx,
                        self.sys.clone(),
                        self.maude.fresh_counter_peek(),
                    );
                    // Decompose the chosen alternative — see comment in
                    // singleton branch.  Mirrors Haskell `solveDisjunction`
                    // → `insertFormula alt`.
                    let outcome = sub.insert_formula(gfm.clone())?;
                    cases.extend(named_cases(
                        &default_case_name(i),
                        sub.outcome_branches(outcome),
                    ));
                }
                // A lone surviving alternative continues in place, as any
                // single Disj branch does in Haskell.
                self.finish_goal_cases(cases)
            }
        })
    }

    /// `exploitPrems` of `labelNodeId` (Reduction.hs): a `Fr` premise gets
    /// a fresh-rule supplier, an `In` premise an `ISend` supplier, a `KU`
    /// premise a `KU` action goal before `i`, and any other premise a
    /// premise goal.
    pub fn exploit_prems(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        rule: &RuleACInst,
    ) -> Result<(), crate::prove::ProveError> {
        // The premises as the rule states them; the next substSystem
        // substitutes them.
        let prems: Vec<(crate::rule::PremIdx, crate::fact::LNFact)> = rule
            .enumerate_premises()
            .map(|(p, f)| (p, f.clone()))
            .collect();
        // Loop-breaker premises (per Haskell `praciLoopBreakers`) are
        // those whose `PremIdx` was flagged at theory-load time by the
        // dataflow loop-breaker analysis.  Goals at these premises get
        // `looping=true`, so `isNonLoopBreakerProtoFactGoal` excludes
        // them and the smart ranker defers them.
        let breakers: std::collections::BTreeSet<crate::rule::PremIdx> = match &rule.info {
            crate::rule::RuleInfo::Proto(info) => info.loop_breakers.iter().copied().collect(),
            _ => std::collections::BTreeSet::new(),
        };
        for (idx, fa) in prems {
            self.exploit_one_prem(i, idx, &fa, breakers.contains(&idx))?;
        }
        Ok(())
    }

    fn exploit_one_prem(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        idx: crate::rule::PremIdx,
        fa: &crate::fact::LNFact,
        is_loop_breaker: bool,
    ) -> Result<(), crate::prove::ProveError> {
        use crate::fact::FactTag;
        match &fa.tag {
            FactTag::Fresh => {
                self.add_fresh_supplier_for(i, idx, fa)?;
            }
            FactTag::In => {
                self.add_isend_supplier_for(i, idx, fa)?;
            }
            FactTag::Ku => {
                self.add_ku_action_before(i, fa);
            }
            // Haskell `exploitPrem`'s `otherwise` branch: store the
            // premise goal for later (`insertGoal (PremiseG (i,v) fa)
            // (v `elem` breakers)`).  Covers Kd/Ded and every other tag.
            _ => {
                self.insert_goal_with_loop_flag(
                    Goal::Premise((*i, idx), fa.clone()),
                    is_loop_breaker,
                );
            }
        }
        Ok(())
    }

    /// `exploitPrem` of a `Fr(m)` premise (Reduction.hs): a fresh-rule
    /// node `[] --[]-> [Fr(m)]` with an edge to the premise, and, unless `m`
    /// is already fresh-sorted, `solveTermEqs SplitNow [m = ~n]` for a fresh
    /// `~n`.
    fn add_fresh_supplier_for(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        idx: crate::rule::PremIdx,
        fa: &crate::fact::LNFact,
    ) -> Result<(), crate::prove::ProveError> {
        let m = match fa.terms.first() {
            Some(t) => t.clone(),
            None => return Ok(()),
        };
        let j = self.fresh_lvar("vf", tamarin_term::lterm::LSort::Node);
        let rule = make_fresh_rule(m.clone());
        self.sys.add_node(j, rule);
        // A raw `S.insert` into sEdges, not insertEdges: no fact
        // unification between the supplier and the premise.
        self.sys.add_edge(crate::constraint::constraints::Edge {
            src: (j, crate::rule::ConcIdx(0)),
            tgt: (*i, idx),
        });
        // Haskell `unless (isFreshVar m)`: narrow m:Msg → ~n:Fresh
        // via solveTermEqs.  Only fires when m is not already Fresh-
        // sorted (free var or Fresh literal).
        let is_fresh_var_or_lit = {
            use tamarin_term::lterm::{LSort, NameTag};
            use tamarin_term::term::Term;
            use tamarin_term::vterm::Lit;
            match &m {
                Term::Lit(Lit::Var(v)) => v.sort == LSort::Fresh,
                Term::Lit(Lit::Con(n)) => matches!(n.tag, NameTag::Fresh),
                _ => false,
            }
        };
        if !is_fresh_var_or_lit {
            let n_var = self.fresh_lvar("n", tamarin_term::lterm::LSort::Fresh);
            let n_term = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(n_var));
            let eq = tamarin_term::rewriting::Equal {
                lhs: m,
                rhs: n_term,
            };
            // Haskell `void (solveTermEqs SplitNow [Equal m n])` —
            // `void` ignores ChangeIndicator but the monadic bind
            // propagates Contradictory via mzero on
            // `noContradictoryEqStore`. Silently swallowing this failure
            // breaks the mzero proxy for shapes like `Fr(pub_var)` where
            // the narrowing `pub_var = ~n:Fresh` is sort-incompatible.
            let res = self.solve_term_eqs(SplitStrategy::SplitNow, &[eq])?;
            if matches!(res, SystemOutcome::Contradictory) {
                self.mark_contradictory();
            }
            // HS-faithful (Reduction.hs): `exploitPrem FreshFact`
            // ends with `unless (isFreshVar m) $ void (solveTermEqs ...)`.
            // No `substSystem` call.  The eq-store update propagates at
            // the next simplifySystem's iter-start substSystem (Simplify.hs).
        }
        self.changed = ChangeIndicator::Changed;
        Ok(())
    }

    /// `exploitPrem` of an `In(m)` premise (Reduction.hs): an `ISend` node
    /// `[KU(m)] --[K(m)]-> [In(m)]` with an edge to the premise, then its
    /// own `KU(m)` premise exploited as a `KU` action goal.
    fn add_isend_supplier_for(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        idx: crate::rule::PremIdx,
        fa: &crate::fact::LNFact,
    ) -> Result<(), crate::prove::ProveError> {
        let m = match fa.terms.first() {
            Some(t) => t.clone(),
            None => return Ok(()),
        };
        let j = self.fresh_lvar("vf", tamarin_term::lterm::LSort::Node);
        let rule = make_isend_rule(fa, m);
        let ku = rule.premises[0].clone();
        self.sys.add_node(j, rule);
        // HS-faithful (Reduction.hs): `exploitPrem InFact` does a
        // RAW `modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))` —
        // NO `insertEdges` call and NO `solveFactEqs` unification.
        self.sys.add_edge(crate::constraint::constraints::Edge {
            src: (j, crate::rule::ConcIdx(0)),
            tgt: (*i, idx),
        });
        // `exploitPrems j ruKnows`: the ISend rule's (annotated) KU premise
        // becomes a KU action goal before `j`.
        self.add_ku_action_before(&j, &ku);
        self.changed = ChangeIndicator::Changed;
        Ok(())
    }

    /// Add a KU action goal at a fresh node before `i`.
    fn add_ku_action_before(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        fa: &crate::fact::LNFact,
    ) {
        let j = self.fresh_lvar("vk", tamarin_term::lterm::LSort::Node);
        self.insert_less(crate::constraint::constraints::LessAtom::new(
            j,
            *i,
            crate::constraint::constraints::Reason::Adversary,
        ));
        self.insert_goal(Goal::Action(j, fa.clone()));
    }

    /// HS `freshLVar name sort`: the next index of this reduction's fresh
    /// counter.
    pub(crate) fn fresh_lvar(
        &self,
        name: &str,
        sort: tamarin_term::lterm::LSort,
    ) -> tamarin_term::lterm::LVar {
        tamarin_term::lterm::LVar::new(name, sort, self.fresh_idxs(1))
    }

    /// `n` consecutive fresh indices (HS `freshIdents n`), returning the
    /// first. The counter is first lifted to `avoid sys`, which Haskell's
    /// threaded counter satisfies by construction; a system without free
    /// variables leaves it unlifted, as `avoid` is then 0.
    fn fresh_idxs(&self, n: u64) -> u64 {
        let avoid = avoid_fresh_state(&self.sys);
        if avoid > 0 {
            self.maude.ensure_above(avoid - 1);
        }
        self.maude.reserve_idxs(n)
    }

    /// Collapse a goal solver's branches: none is `Contradictory`; a single
    /// one is adopted in place, with its system and FreshT counter, as
    /// `LinearNamed`; more are returned as `Cases`.
    pub(crate) fn finish_goal_cases(&mut self, mut cases: Vec<GoalBranch>) -> GoalCases {
        if cases.is_empty() {
            return GoalCases::Contradictory;
        }
        if cases.len() == 1 {
            let branch = cases.pop().unwrap();
            self.sys = branch.sys;
            self.maude.reset_counter_to(branch.counter);
            self.changed = ChangeIndicator::Changed;
            return GoalCases::LinearNamed(branch.name);
        }
        self.changed = ChangeIndicator::Changed;
        GoalCases::Cases(cases)
    }

    /// `solveAction` (Goals.hs). If node `i` is labelled, unify `fa` with
    /// each of its actions unless `fa` is already one of them; otherwise
    /// label `i` with each non-silent rule and unify `fa` with each of the
    /// rule's actions. For a `KU` goal headed by an AC operator,
    /// `removePermutations` prunes arms that only permute the rule's `KU`
    /// premise variables.
    pub(crate) fn solve_action_goal(
        &mut self,
        i: &crate::constraint::constraints::NodeId,
        fa: &crate::fact::LNFact,
    ) -> Result<GoalCases, crate::prove::ProveError> {
        let existing = self
            .sys
            .nodes
            .iter()
            .find(|(nid, _)| nid == i)
            .map(|(_, ru)| ru.clone());
        Ok(match existing {
            Some(ru) => {
                // `Just ru -> do unless (fa `elem` rActs ru) ...; return ru`:
                // the case is named after the rule even when no
                // unification is needed.
                let rule_name = rule_case_name(&ru);
                if ru.actions.contains(fa) {
                    return Ok(GoalCases::LinearNamed(rule_name));
                }
                // Fork: one case per action of the existing rule
                // instance, unifying that action with `fa`. All cases
                // share the same rule name; proof_method.rs dedup will
                // append `_case_1`/`_case_2`/... if multiple cases.
                //
                let mut cases = Vec::new();
                // HS FreshT-threading: per pushed case, the branch's final
                // fresh counter (see `new_inheriting`).
                for act in &ru.actions {
                    let sys = self.sys.clone();
                    let mut sub =
                        Reduction::new_inheriting(self.ctx, sys, self.maude.fresh_counter_peek());
                    let res = sub.solve_fact_eqs(
                        SplitStrategy::SplitNow,
                        &[tamarin_term::rewriting::Equal {
                            lhs: fa.clone(),
                            rhs: act.clone(),
                        }],
                    )?;
                    // One case per unifier arm (Goals.hs).
                    cases.extend(named_cases(&rule_name, sub.outcome_branches(res)));
                }
                // Single-case adoption mutates `self.sys` in place and
                // signals the case-name for the printer (`case <name>` +
                // qed); simplify-pass callers ignore the return and look
                // at `self.sys`.  HS FreshT-threading — see the
                // candidate-loop single-case adoption below.
                self.finish_goal_cases(cases)
            }
            None => {
                // `labelNodeId i rules Nothing`, then one fork per action of
                // the chosen rule (`act <- disjunctionOfList (rActs ru)`).
                // For a `KU` goal headed by an AC operator, `getKUVars` of
                // the rule's first two premises lets the SplitNow fan-out
                // drop unifier arms that only permute them (#883).
                let avoid_max = bounds_max(&self.sys);
                self.maude.ensure_above(avoid_max);
                let fork_base = self.maude.fresh_counter_peek();
                let goal_ac_headed = matches!(fa.tag, crate::fact::FactTag::Ku)
                    && fa.terms.len() == 1
                    && matches!(
                        fa.terms[0],
                        tamarin_term::term::Term::App(
                            tamarin_term::function_symbols::FunSym::Ac(_),
                            _
                        )
                    );
                let matches_goal = |act: &crate::fact::LNFact| {
                    act.tag == fa.tag && act.terms.len() == fa.terms.len()
                };
                let mut cases: Vec<GoalBranch> = Vec::new();
                for rule in self.ctx.classified_rules.non_silent() {
                    // A rule with no action of the goal's shape dies in
                    // `solveFactEqs`; skip it before labelling.
                    if !rule.0.actions.iter().any(matches_goal) {
                        continue;
                    }
                    // `annotatePrems`: an annotated goal labels with intruder
                    // rules whose premises and actions carry its annotations.
                    let annotated;
                    let rule = if !fa.annotations.is_empty()
                        && matches!(rule.0.info, crate::rule::RuleInfo::Intr(_))
                    {
                        annotated = (annotate_prems(&rule.0, fa), rule.1.clone());
                        &annotated
                    } else {
                        rule
                    };
                    let Some((renamed, prefix)) =
                        self.label_node_id(*i, rule, None, avoid_max, fork_base, |_| true)?
                    else {
                        continue;
                    };
                    let case_name = rule_case_name(&renamed);
                    let fork_counter = prefix.maude.fresh_counter_peek();
                    let is_ac = if goal_ac_headed {
                        ku_vars(&renamed)
                    } else {
                        IsAcConstructor::OtherRule
                    };
                    for act in renamed.actions.iter().filter(|act| matches_goal(act)) {
                        let mut sub =
                            Reduction::new_inheriting(self.ctx, prefix.sys.clone(), fork_counter);
                        let res = sub.solve_fact_eqs_ac(
                            SplitStrategy::SplitNow,
                            is_ac,
                            &[tamarin_term::rewriting::Equal {
                                lhs: fa.clone(),
                                rhs: act.clone(),
                            }],
                        )?;
                        cases.extend(named_cases(&case_name, sub.outcome_branches(res)));
                    }
                }
                self.finish_goal_cases(cases)
            }
        })
    }

    /// HS `labelNodeId i rules parent` (Reduction.hs) for one rule of the
    /// caller's `disjunctionOfList rules`: import (rename) the rule, lower
    /// its budget below a same-named `parent`, solve its variant
    /// constraints, label `i` with it and exploit its premises. Sibling
    /// rules fork below FreshT, so every import starts from `fork_base`.
    /// `keep` rejects a renamed rule whose branch Haskell kills later.
    /// Returns the labelled rule and the branch, or `None` when the branch
    /// dies (including `noContradictoryEqStore` after the constraints).
    fn label_node_id(
        &mut self,
        i: crate::constraint::constraints::NodeId,
        (rule, constrs): &crate::constraint::solver::context::RuleWithConstrs,
        parent: Option<&RuleACInst>,
        avoid_max: u64,
        fork_base: u64,
        keep: impl FnOnce(&RuleACInst) -> bool,
    ) -> Result<Option<(RuleACInst, Reduction<'ctx>)>, crate::prove::ProveError> {
        self.maude.reset_counter_to(fork_base);
        let (mut ru, constrs) =
            freshen_rule_with_constrs(rule.clone(), constrs.clone(), avoid_max, &self.maude);
        if let Some(parent) = parent {
            let budget = crate::rule::get_remaining_rule_applications(parent);
            let name = crate::rule::rule_name_string(parent);
            if !name.is_empty() && name == crate::rule::rule_name_string(&ru) && budget > 1 {
                ru = crate::rule::set_remaining_rule_applications(ru, budget - 1);
            }
        }
        if !keep(&ru) {
            return Ok(None);
        }
        let mut sys = self.sys.clone();
        sys.add_node(i, ru.clone());
        let mut branch = Reduction::new_inheriting(self.ctx, sys, self.maude.fresh_counter_peek());
        if branch.solve_rule_constraints(constrs)? {
            return Ok(None);
        }
        branch.exploit_prems(&i, &ru)?;
        Ok(Some((ru, branch)))
    }

    /// `solvePremise` (Goals.hs).
    pub(crate) fn solve_premise_goal(
        &mut self,
        p: &crate::constraint::constraints::NodePrem,
        fa_prem: &crate::fact::LNFact,
    ) -> Result<GoalCases, crate::prove::ProveError> {
        // `solvePremise rules p faPrem | isKDFact faPrem`: an `IRecv` node
        // `[Out(t)] --> [KD(t)]` for a fresh message variable `t`, a chain
        // from it to `p`, and then `solvePremise` on its `Out(t)` premise.
        // The fresh `t` lets the Out premise unify with any protocol
        // output; `solveChain` later closes the chain.
        if matches!(fa_prem.tag, crate::fact::FactTag::Kd) {
            if fa_prem.terms.is_empty() {
                return Ok(GoalCases::Contradictory);
            }
            let i_learn = self.fresh_lvar("vl", tamarin_term::lterm::LSort::Node);
            let m_learn_var = self.fresh_lvar("t", tamarin_term::lterm::LSort::Msg);
            let m_learn = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(m_learn_var));
            let irecv_rule = crate::rule::Rule::new(
                crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv),
                vec![crate::fact::out_fact(m_learn.clone())],
                vec![crate::fact::kd_fact(m_learn.clone())],
                vec![],
            );
            self.sys.add_node(i_learn, irecv_rule);
            let c_learn: crate::constraint::constraints::NodeConc =
                (i_learn, crate::rule::ConcIdx(0));
            self.insert_goal(Goal::Chain(c_learn, *p));
            self.changed = ChangeIndicator::Changed;
            let p_learn: crate::constraint::constraints::NodePrem =
                (i_learn, crate::rule::PremIdx(0));
            let prem_learn = crate::fact::out_fact(m_learn);
            return self.solve_premise_goal(&p_learn, &prem_learn);
        }
        // `solvePremise (crProtocol ++ crConstruct)` (Goals.hs) through
        // `insertFreshNodeConc`: `i <- freshLVar "vr"` once, before the
        // rule disjunction, so every case shares the node id and imports its
        // rule from the post-`vr` counter; then one fork per conclusion.
        let rules = &self.ctx.classified_rules;
        let avoid_max = bounds_max(&self.sys);
        let new_node = self.fresh_lvar("vr", tamarin_term::lterm::LSort::Node);
        let fork_base = self.maude.fresh_counter_peek();
        let matches_prem = |fc: &crate::fact::LNFact| {
            fc.tag == fa_prem.tag && fc.terms.len() == fa_prem.terms.len()
        };
        let mut cases: Vec<GoalBranch> = Vec::new();
        for rule in rules.protocol.iter().chain(&rules.construct) {
            // A rule with no conclusion of the premise's shape dies in
            // `solveFactEqs`; skip it before labelling.
            if !rule.0.conclusions.iter().any(matches_prem) {
                continue;
            }
            let Some((renamed, label)) =
                self.label_node_id(new_node, rule, None, avoid_max, fork_base, |_| true)?
            else {
                continue;
            };
            let case_name = rule_case_name(&renamed);
            let label_counter = label.maude.fresh_counter_peek();
            for (c_idx, fa_conc) in renamed.enumerate_conclusions() {
                if !matches_prem(fa_conc) {
                    continue;
                }
                let mut sub = Reduction::new_inheriting(self.ctx, label.sys.clone(), label_counter);
                let res = sub.insert_edge_with_facts(
                    Edge {
                        src: (new_node, c_idx),
                        tgt: *p,
                    },
                    fa_conc,
                    fa_prem,
                )?;
                // `insertEdges` may split: one case per unifier arm, all
                // named after the rule (Goals.hs).
                cases.extend(named_cases(&case_name, sub.outcome_branches(res)));
            }
        }
        // HS FreshT-threading: single-case adoption carries the BRANCH's
        // counter (labelNodeId + insertEdges + per-arm subst draws) forward,
        // not the outer counter that only saw the freshen reservation.  See
        // `solve_action_goal`'s single-case adoption for the full rationale.
        // Case name reaches stdout, hence passed explicitly.
        Ok(self.finish_goal_cases(cases))
    }

    /// `solveChain` (Goals.hs), CR-rule *DG2_chain*: close the chain with a
    /// direct edge, or extend it by one destructor step (by the bespoke
    /// union destructors when the message is a multiset union). An open
    /// chain, whose message is a variable, is not extended.
    pub(crate) fn solve_chain_goal(
        &mut self,
        c: &crate::constraint::constraints::NodeConc,
        p: &crate::constraint::constraints::NodePrem,
    ) -> Result<GoalCases, crate::prove::ProveError> {
        let c_rule = match self.sys.node_rule_safe(&c.0) {
            Some(r) => r.clone(),
            None => return Ok(GoalCases::Contradictory),
        };
        let p_rule_opt = self.sys.node_rule_safe(&p.0).cloned();
        let fa_conc = match c_rule.lookup_conclusion(c.1) {
            Some(f) => f.clone(),
            None => return Ok(GoalCases::Contradictory),
        };

        let mut all_cases: Vec<GoalBranch> = Vec::new();
        // ---------------- Branch 1: direct edge ----------------
        if let Some(p_rule) = &p_rule_opt {
            let fa_prem_opt = p_rule.lookup_premise(p.1).cloned();
            if let Some(_fa_prem) = fa_prem_opt {
                // `illegalCoerce pRule mPrem` tests the chain conclusion's
                // KD message, which `illegal_coerce` reads from `fa_conc`.
                if !forbidden_edge(&c_rule, p_rule) && !illegal_coerce(p_rule, &fa_conc) {
                    // HS-faithful `insertEdges` (Reduction.hs):
                    // route through `insert_edge` so unification fires
                    // BEFORE the edge enters sEdges.  Mirrors HS's
                    // `solveFactEqs SplitNow` + `modM sEdges` order.
                    let sys_clone = self.sys.clone();
                    let mut sub = Reduction::new_inheriting(
                        self.ctx,
                        sys_clone,
                        self.maude.fresh_counter_peek(),
                    );
                    let res =
                        sub.insert_edge(crate::constraint::constraints::Edge { src: *c, tgt: *p })?;
                    // Haskell names a direct case by the chain conclusion's
                    // KD term (`caseName mPrem`, Goals.hs), one case per
                    // unifier arm of `insertEdges`.
                    let case_name =
                        chain_direct_case_name(&fa_conc).unwrap_or_else(|| rule_case_name(&c_rule));
                    all_cases.extend(named_cases(&case_name, sub.outcome_branches(res)));
                }
            }
        }

        // Extend by one destructor step, in saturation as well
        // (`contradictoryIf (isMsgVar m)` skips an open chain).
        let conc_term_is_msg_var = fa_conc
            .terms
            .first()
            .map(tamarin_term::lterm::is_msg_var)
            .unwrap_or(false);
        // A multiset union `KD(t1 ++ ... ++ tn)` uses the bespoke rules
        // `mkDUnionRule args arg_i`, whose premise is the message itself, so
        // there is no AC unification and one case per component.
        let funion_args: Option<Vec<tamarin_term::lterm::LNTerm>> = match fa_conc.terms.first() {
            Some(tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::Ac(
                    tamarin_term::function_symbols::AcSym::Union,
                ),
                args,
            )) if args.len() >= 2 => Some(args.to_vec()),
            _ => None,
        };
        if let Some(args) = funion_args {
            use tamarin_term::function_symbols::UNION_SYM_STRING;
            // HS `solveChain` union arm (Goals.hs): `i <- freshLVar "vr"`
            // is allocated ONCE, before `disjunctionOfList rus`, so every
            // union-decomposition case shares the same `#vr` id.
            let new_node = self.fresh_lvar("vr", tamarin_term::lterm::LSort::Node);
            let xy_union = tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::Ac(
                    tamarin_term::function_symbols::AcSym::Union,
                ),
                args.clone().into(),
            );
            let mut union_name = b"_".to_vec();
            union_name.extend_from_slice(UNION_SYM_STRING);
            for arg_i in &args {
                // Build HS `mkDUnionRule args arg_i`:
                //   Rule (DestrRule "_union" 0 True False [AC Union])
                //        [kdFact (Union args)] [kdFact arg_i] [] []
                let ir = crate::rule::IntrRuleAC::new(
                    crate::rule::IntrRuleACInfo::DestrRule {
                        name: union_name.clone(),
                        remaining_applications: 0,
                        rhs_is_proper_subterm: true,
                        rhs_is_constant: false,
                        funs: vec![tamarin_term::function_symbols::FunSym::Ac(
                            tamarin_term::function_symbols::AcSym::Union,
                        )],
                    },
                    vec![crate::fact::kd_fact(xy_union.clone())],
                    vec![crate::fact::kd_fact(arg_i.clone())],
                    vec![],
                );
                let ru_inst = intr_rule_to_rule_ac_inst(ir);
                // HS allocates a fresh LVar via `freshLVar "vr" LSortNode`
                // (Goals.hs) — no labelNodeId/exploitPrems wrapping
                // since the rule has no Fresh/IRecv premises.  The premise
                // is `KD(Union(args))` which exactly equals `faConc` by
                // construction, so `insertEdges chain_extend` does no
                // AC fanout.
                let mut sys_clone = self.sys.clone();
                sys_clone.add_node(new_node, ru_inst.clone());
                let sub =
                    Reduction::new_inheriting(self.ctx, sys_clone, self.maude.fresh_counter_peek());
                let Some(prem0) = ru_inst.premises.first() else {
                    continue;
                };
                let branches = sub.extend_and_mark(c, new_node, prem0, p)?;
                all_cases.extend(named_cases(&rule_case_name(&ru_inst), branches));
            }
            // HS short-circuits the generic destructor loop in the FUnion
            // arm (case-match on `viewTerm2`).  Mirror by skipping branch 2's
            // generic loop below.
            return Ok(self.finish_goal_cases(all_cases));
        }
        if !conc_term_is_msg_var {
            // `insertFreshNode (crDestruct rules) (Just cRule)` (Goals.hs):
            // `i <- freshLVar "vr"` once, then one labelled fork per
            // destructor, extended from its first premise.
            let avoid_max = bounds_max(&self.sys);
            let new_node = self.fresh_lvar("vr", tamarin_term::lterm::LSort::Node);
            let fork_base = self.maude.fresh_counter_peek();
            let ctx = self.ctx;
            for rule in &ctx.classified_rules.destruct {
                // `contradictoryIf (forbiddenEdge cRule ru)`, and a first
                // premise that cannot take `faConc`, kill the branch; check
                // both before labelling.
                let keep = |ru: &RuleACInst| {
                    ru.premises.first().is_some_and(|prem0| {
                        prem0.tag == fa_conc.tag && prem0.terms.len() == fa_conc.terms.len()
                    }) && !forbidden_edge(&c_rule, ru)
                        && !ru.conclusions.is_empty()
                };
                let Some((ru, sub)) =
                    self.label_node_id(new_node, rule, Some(&c_rule), avoid_max, fork_base, keep)?
                else {
                    continue;
                };
                if sub.sys.eq_store().is_false() {
                    continue;
                }
                // `extendAndMark` (Goals.hs). The chain continuation reads
                // the raw, unsubstituted conclusion of `ru`, as in Haskell,
                // where substSystem runs only at the next simplify iteration.
                let prem0 = ru.premises[0].clone();
                let branches = sub.extend_and_mark(c, new_node, &prem0, p)?;
                all_cases.extend(named_cases(&rule_case_name(&ru), branches));
            }
        }

        Ok(self.finish_goal_cases(all_cases))
    }

    /// HS `extendAndMark i ru v faPrem faConc` (Goals.hs `solveChain`)
    /// with `v = PremIdx 0`: `insertEdges [(c, faConc, faPrem, (i, v))]`,
    /// then in every resulting branch mark the premise goal solved and
    /// insert the chain from `(i, ConcIdx 0)` to `p`.
    fn extend_and_mark(
        mut self,
        c: &crate::constraint::constraints::NodeConc,
        i: crate::constraint::constraints::NodeId,
        fa_prem: &crate::fact::LNFact,
        p: &crate::constraint::constraints::NodePrem,
    ) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
        let v = crate::rule::PremIdx(0);
        let edge = self.insert_edge(Edge {
            src: *c,
            tgt: (i, v),
        })?;
        let ctx = self.ctx;
        continue_in_arms(ctx, self.outcome_branches(edge), |arm| {
            arm.mark_goal_as_solved(&Goal::Premise((i, v), fa_prem.clone()));
            arm.insert_goal(Goal::Chain((i, crate::rule::ConcIdx(0)), *p));
            Ok(SystemOutcome::Linear)
        })
    }

    /// `solveSubterm` (Goals.hs): move the subterm to the solved ones,
    /// split it with `splitSubterm`, and make one case `SubtermSplit<i>`
    /// per split.
    pub(crate) fn solve_subterm_goal(
        &mut self,
        st: &(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm),
    ) -> Result<GoalCases, crate::prove::ProveError> {
        use tamarin_term::function_symbols::AcSym;
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::f_app_ac;
        use tamarin_term::vterm::var_term;
        // modM posSubterms (delete st); modM solvedSubterms (insert st).
        let mut moved = false;
        self.sys.invalidate_max_var_idx_cache();
        self.sys.subterm_store_mut().subterms.retain(|c| {
            let keep = !(c.small == st.0 && c.big == st.1);
            if !keep {
                moved = true;
            }
            keep
        });
        if moved {
            self.sys.invalidate_max_var_idx_cache();
            if !self
                .sys
                .subterm_store
                .solved_subterms
                .iter()
                .any(|c| c.small == st.0 && c.big == st.1)
            {
                self.sys.subterm_store_mut().solved_subterms.push(
                    crate::tools::subterm_store::SubtermConstraint {
                        small: st.0.clone(),
                        big: st.1.clone(),
                        propagated: true,
                    },
                );
            }
            self.changed = ChangeIndicator::Changed;
        }

        // splitList <- splitSubterm reducible True st.  Fresh vars for the
        // AC-recurse arm come from the maude counter (HS `freshLVar`).
        use crate::tools::subterm_store::SubtermSplit;
        let reducible = self.maude.maude_sig().reducible_fun_syms_fast.clone();
        let split_list = {
            let mut mk_fresh = |sort: LSort| -> LVar { self.fresh_lvar("newVar", sort) };
            crate::tools::subterm_store::split_subterm(
                &reducible,
                false,
                &st.0,
                &st.1,
                &mut mk_fresh,
            )
        };

        // disjunctionOfList [] -> Contradictory.
        if split_list.is_empty() {
            self.sys.subterm_store_mut().contradictory = true;
            return Ok(GoalCases::Contradictory);
        }

        let base_sys = self.sys.clone();
        let mut cases: Vec<GoalBranch> = Vec::new();
        for (i, split) in split_list.iter().enumerate() {
            let case_name = format!("SubtermSplit{}", i + 1);
            // Fork the system; mutate per the split arm via a fresh
            // Reduction over the clone so insertFormula / addSubterm route
            // exactly as in HS.  `disjunctionOfList` forks the MonadFresh
            // state at the post-`splitSubterm` point: each branch starts
            // its fresh allocation above every var minted so far (incl. the
            // AC `newVar` from the split), so advance the per-branch
            // counter past the parent's current high-water mark.
            let mut sub = Reduction::new(self.ctx, base_sys.clone());
            sub.maude
                .ensure_above(self.maude.fresh_counter_peek().saturating_sub(1));
            let outcome = match split {
                SubtermSplit::TrueD => SystemOutcome::Linear,
                SubtermSplit::SubtermD(s, t) => {
                    sub.sys.invalidate_max_var_idx_cache();
                    sub.sys.subterm_store_mut().add(s.clone(), t.clone());
                    SystemOutcome::Linear
                }
                SubtermSplit::NatSubtermD(s, t) => {
                    // Upstream #958: every natural split becomes an equation,
                    // including splits with siblings. Refine a message-sorted
                    // smaller operand before putting it below NatPlus.
                    let new_var = sub.fresh_lvar("newVar", LSort::Nat);
                    let f = if tamarin_term::lterm::is_msg_var(s) {
                        let small_var = sub.fresh_lvar("small", LSort::Nat);
                        let small = var_term(small_var);
                        let s_plus =
                            f_app_ac(AcSym::NatPlus, vec![small.clone(), var_term(new_var)]);
                        crate::guarded::close_guarded(
                            crate::formula::Quantifier::Ex,
                            vec![small_var, new_var],
                            vec![
                                crate::atom::ProtoAtom::EqE(s.clone(), small),
                                crate::atom::ProtoAtom::EqE(s_plus, t.clone()),
                            ],
                            crate::guarded::gtrue(),
                        )
                    } else {
                        let s_plus = f_app_ac(AcSym::NatPlus, vec![s.clone(), var_term(new_var)]);
                        close_guarded_ex_eq(&new_var, &s_plus, t)
                    };
                    sub.insert_formula(f)?
                }
                SubtermSplit::EqualD(l, r) => {
                    // insertFormula $ GAto $ EqE (lTermToBTerm l) (lTermToBTerm r)
                    let atom = crate::atom::ProtoAtom::EqE(
                        crate::formula::lift_free(l),
                        crate::formula::lift_free(r),
                    );
                    sub.insert_formula(crate::guarded::Guarded::Atom(atom))?
                }
                SubtermSplit::AcNewVarD(small_plus, big, new_var) => {
                    // insertFormula $ closeGuarded Ex [newVar] [EqE smallPlus big] gtrue
                    let f = close_guarded_ex_eq(new_var, small_plus, big);
                    sub.insert_formula(f)?
                }
            };
            cases.extend(named_cases(&case_name, sub.outcome_branches(outcome)));
        }

        Ok(self.finish_goal_cases(cases))
    }

    /// `solveSplit` — perform a deferred equality-store split for
    /// `Goal::Split(id)`. Mirrors the relevant arm of Haskell's
    /// `solveGoal`: `splitAtPos` followed by replacing the eq-store
    /// and running `simp` so the singleton disjunction folds into the
    /// free substitution via `simpSingleton` + `applyEqStore`.
    pub(crate) fn solve_split_goal(
        &mut self,
        id: crate::tools::equation_store::SplitId,
    ) -> Result<GoalCases, crate::prove::ProveError> {
        let cases = match self.sys.eq_store().perform_split(id) {
            Some(cs) => cs,
            None => return Ok(GoalCases::Contradictory),
        };
        if cases.is_empty() {
            return Ok(GoalCases::Contradictory);
        }
        // `solveSplit` (Goals.hs) simplifies the chosen store with
        // `substCreatesNonNormalTerms` as the contradiction check, which
        // folds the chosen variant into the substitution.
        let maude = self.maude.clone();
        let has_reducible = !maude.maude_sig().reducible_fun_syms.is_empty();
        // One `maybeNonNormalTerms` walk of `self.sys`, shared across every
        // candidate probe below — HS's curried `substCheck` from Goals.hs
        // (`gets (substCreatesNonNormalTerms hnd)` captures the system once).
        // See `SubstNfChecker`.
        let nf_checker = has_reducible.then(|| {
            crate::constraint::solver::contradictions::SubstNfChecker::new(&maude, &self.sys)
        });
        // `nf_checker.is_some()` iff `has_reducible`, so `as_ref()` is
        // `Some` exactly when the non-normal-terms check must run.
        let simplify_picked = |store: crate::tools::equation_store::EquationStore| -> Result<
            crate::tools::equation_store::EquationStore,
            crate::prove::ProveError,
        > { simp_store(store, nf_checker.as_ref(), &maude) };
        if cases.len() == 1 {
            self.sys.invalidate_max_var_idx_cache();
            let store = simplify_picked(cases.into_iter().next().unwrap())?;
            if store.is_false() {
                self.mark_contradictory();
                return Ok(GoalCases::Contradictory);
            }
            self.sys.set_eq_store(std::sync::Arc::new(store));
            return Ok(GoalCases::LinearNamed("split".to_string()));
        }
        // `solveSplit` (Goals.hs) returns "split" for every alternative;
        // `distinguish` later numbers the siblings.
        let out = simp_split_arms(&maude, cases, simplify_picked)?
            .into_iter()
            .map(|(store, counter)| {
                let mut sys = self.sys.clone();
                sys.invalidate_max_var_idx_cache();
                sys.set_eq_store(std::sync::Arc::new(store));
                GoalBranch {
                    name: "split".to_string(),
                    sys,
                    counter,
                }
            })
            .collect();
        Ok(self.finish_goal_cases(out))
    }
}

#[cfg(test)]
#[path = "reduction_tests.rs"]
mod tests;
