// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Constraint.Solver.Sources`.
//!
//! Sources represent the big-step proofs computing the possible
//! sources of a fact in a constraint system. This module implements:
//!
//! - Precomputing source distinctions for every protocol rule's
//!   premises (`precompute_full_sources`, mirroring `precomputeSources`).
//! - Saturating sources with respect to each other
//!   (`saturate_sources_with_simp*`, mirroring `saturateSources`).
//! - Refining sources with source-assumption lemmas
//!   (`refine_with_source_asms`, mirroring `refineWithSourceAsms`).
//! - Solving a goal by application of a precomputed source
//!   (`solve_with_source_cases*` / `apply_source_case_*`).
//! - Removing redundant cases (`remove_redundant_cases`).
//!
//! Alongside the full machinery it also exposes the public data shapes
//! and the `IntegerParameters` config used by the rest of the solver.

use crate::constraint::system::System;
use tamarin_term::bind::Bindings;
use tamarin_term::lterm::frees;

// =============================================================================
// Precompute-mode marker
// =============================================================================
//
// `solve_premise_goal` reads this flag to decide between full
// `exploit_prems` (precompute) and `exploit_prems_supplier_only`
// (runtime).  Set from `precompute_full_sources` for the duration of
// the precomputation; cleared on exit.  Mirrors how Haskell's
// `precomputeSources` runs the reducer in a fixed mode that records
// every dangling premise, then `saturateSources` resolves them.

thread_local! {
    static IN_PRECOMPUTE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    // True while inside `initial_source_cases` (HS's `initialSource`'s
    // `runReduction instantiate`).  HS's initialSource uses `solveGoal`
    // from Goals.hs directly — bypassing `solveWithSource` —so initial
    // case computation never short-circuits via source-case dispatch.
    // Rust mirrors this by gating dispatch in `solve_premise_goal` on
    // `!in_initial_source_cases()`.  Saturate refinement
    // (`saturate_sources_with_simp_public`) does NOT set this flag, so
    // dispatch fires there exactly like HS's `solveAllSafeGoals`.
    static IN_INITIAL_SOURCE_CASES: std::cell::Cell<bool>
        = const { std::cell::Cell::new(false) };
}

/// The set of every node id in `sys` — the membership set used to keep only
/// edges wholly within the live sub-system (E.5).  Loop-invariant across arms,
/// so built once per `apply_source_case_*` call.
fn collect_node_ids(
    sys: &System,
) -> std::collections::BTreeSet<crate::constraint::constraints::NodeId> {
    sys.nodes.iter().map(|(n, _)| *n).collect()
}

/// Grafted-edge producer-conclusion ⇆ consumer-premise fact equalities.
/// Used by `conjoin_refine_arm`'s E.5 step: walk every edge in `sys`, skip
/// pre-existing LIVE-LIVE edges (both endpoints in `live_node_ids`), and emit
/// a fact `Equal` for each grafted edge whose conclusion/premise facts share
/// tag+arity but aren't already syntactically equal.  See the E.5 comments at
/// both call sites for the HS-faithfulness / live-edge-scoping rationale; only
/// the subsequent `solve_fact_eqs(strategy, …)` (SplitNow vs SplitLater)
/// differs between callers.
fn grafted_edge_eqs(
    sys: &System,
    live_node_ids: &std::collections::BTreeSet<crate::constraint::constraints::NodeId>,
) -> Vec<tamarin_term::rewriting::Equal<crate::fact::LNFact>> {
    // One id→rule index instead of two linear `sys.nodes` scans per edge;
    // `node_rule_map` keeps the FIRST entry per id, exactly like `find` did.
    let node_rule = sys.node_rule_map();
    sys.edges
        .iter()
        .filter_map(|e| {
            if live_node_ids.contains(&e.src.0) && live_node_ids.contains(&e.tgt.0) {
                return None;
            }
            let conc = node_rule
                .get(&e.src.0)?
                .conclusions
                .get(e.src.1 .0)
                .cloned()?;
            let prem = node_rule.get(&e.tgt.0)?.premises.get(e.tgt.1 .0).cloned()?;
            if conc.tag != prem.tag || conc.terms.len() != prem.terms.len() {
                return None;
            }
            if conc == prem {
                return None;
            }
            Some(tamarin_term::rewriting::Equal {
                lhs: conc,
                rhs: prem,
            })
        })
        .collect()
}

/// Build a fresh per-arm `Reduction` for a source-case DisjT fan-out: install
/// `arm_eq` into a clone of `template` (invalidating the cached max-var idx) and
/// wrap it in a new `Reduction`.  Mirrors HS's `DisjT` replication of the
/// Reduction continuation (Reduction.hs:742-744 `disjunctionOfList
/// performSplit`); shared by the action/premise fan-outs so the
/// clone-then-install sequence lives in exactly one place.
///
/// HS FreshT-threading (task #23, A(ii)): `inherit_next` is the fresh
/// counter at the fan-out point — `DisjT` sits BELOW `FreshT`
/// (Reduction.hs:115-118, see line 118), so every arm's continuation draws (substSystem
/// node-merge witness mints, later solves) start from an independent
/// COPY of that value, not from `bounds_max(arm_sys)` (which silently
/// rewinds past the step's transient draws).  Callers pass the forking
/// Reduction's `maude.fresh_counter_peek()`.  `new_inheriting` maxes
/// with `avoid_fresh_state` and the REFINE_FLOOR, so a floored refine
/// caller keeps its `avoid th` seed, and `inherit_next = 0` means no
/// inheritance — the fork starts detached from the caller's counter.
fn fork_arm_reduction<'c>(
    ctx: &'c crate::constraint::solver::context::ProofContext,
    template: &System,
    arm_eq: crate::tools::equation_store::EquationStore,
    inherit_next: u64,
) -> crate::constraint::solver::reduction::Reduction<'c> {
    use crate::constraint::solver::reduction::Reduction;
    let mut arm_sys = template.clone();
    arm_sys.invalidate_max_var_idx_cache();
    arm_sys.set_eq_store(std::sync::Arc::new(arm_eq));
    Reduction::new_inheriting(ctx, arm_sys, inherit_next)
}

/// E.5 nested fan-out: for each arm eq-store, fork a `Reduction` off `template`
/// (see [`fork_arm_reduction`]), run `subst_system`, and collect the surviving
/// (non-`false`-eq-store) systems into `out`, each paired with its
/// continuation counter (`inherit_next` + that arm's own substSystem
/// draws) for the post-E.5 close-chains/output continuation.  Shared
/// verbatim by the action and premise E.5 `Cases` arms.
fn subst_arms_into(
    ctx: &crate::constraint::solver::context::ProofContext,
    template: &System,
    arms: Vec<crate::tools::equation_store::EquationStore>,
    inherit_next: u64,
    out: &mut Vec<(System, u64)>,
) {
    for arm_eq in arms {
        let mut arm_red = fork_arm_reduction(ctx, template, arm_eq, inherit_next);
        arm_red.subst_system();
        if arm_red.sys.eq_store.is_false() {
            continue;
        }
        let arm_cont = arm_red.maude.fresh_counter_peek();
        out.push((arm_red.sys, arm_cont));
    }
}

pub fn in_precompute_mode() -> bool {
    IN_PRECOMPUTE.with(|c| c.get())
}

pub fn in_initial_source_cases() -> bool {
    IN_INITIAL_SOURCE_CASES.with(|c| c.get())
}

/// RAII guard: saves `IN_PRECOMPUTE` on entry, sets it true, and restores the
/// saved value on drop — early `return`s, `?`, and unwind alike.  `IN_PRECOMPUTE`
/// has no free setter, so flipping it requires holding this guard; a caught
/// panic above (`catch_unwind` in the oracle/deriv-check solvers) therefore
/// cannot leave the flag stuck true on a reused rayon worker.
#[must_use = "dropping this guard immediately ends the scope it protects"]
struct PrecomputeModeGuard(bool);
impl PrecomputeModeGuard {
    fn enter() -> Self {
        PrecomputeModeGuard(IN_PRECOMPUTE.with(|c| c.replace(true)))
    }
}
impl Drop for PrecomputeModeGuard {
    fn drop(&mut self) {
        IN_PRECOMPUTE.with(|c| c.set(self.0));
    }
}

/// RAII guard for `IN_INITIAL_SOURCE_CASES`, mirroring [`PrecomputeModeGuard`]:
/// saves the flag on entry, sets it true, and restores the saved value on drop.
/// The flag has no free setter, so it can only be flipped through this guard.
#[must_use = "dropping this guard immediately ends the scope it protects"]
struct InitialSourceCasesGuard(bool);
impl InitialSourceCasesGuard {
    fn enter() -> Self {
        InitialSourceCasesGuard(IN_INITIAL_SOURCE_CASES.with(|c| c.replace(true)))
    }
}
impl Drop for InitialSourceCasesGuard {
    fn drop(&mut self) {
        IN_INITIAL_SOURCE_CASES.with(|c| c.set(self.0));
    }
}

/// Solver-tuning parameters mirroring Haskell's `IntegerParameters`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerParameters {
    /// Maximum number of open destruction chains `solveAllSafeGoals` may
    /// solve during saturation before chain goals stop being safe (HS
    /// `paramOpenChainsLimit`, fed from `-c/--open-chains`).
    pub open_chains_limit: i64,
    /// Maximum saturation iterations during source refinement (HS
    /// `paramSaturationLimit`, fed from `-s/--saturation`).
    pub saturation_limit: i64,
    /// HS-shape field; the live trace gate is the process-global
    /// [`set_show_saturation_steps`] (the flag is toggled dynamically
    /// around the precompute-only forcing, which a value snapshotted at
    /// context construction couldn't express).
    pub show_saturation_steps: bool,
}

impl Default for IntegerParameters {
    fn default() -> Self {
        // Defaults match Haskell's `defaultTheoryLoadOptions`
        // (TheoryLoader.hs:244-245): openChain=10, saturation=5.
        IntegerParameters {
            open_chains_limit: 10,
            saturation_limit: 5,
            show_saturation_steps: false,
        }
    }
}

/// CLI overrides for [`IntegerParameters`] (HS threads `-c`/`-s` from
/// `TheoryLoadOptions` into every `closeRuleCache`; the port's contexts are
/// built in too many places to thread a value through each, so the CLI layer
/// stores the overrides process-globally and [`IntegerParameters::current`]
/// folds them over the defaults).  `-1` = unset; the CLI parser range-checks
/// the flags to `0..=i64::MAX` (cli.rs), so every real override is `>= 0`
/// and the `try_from` below cannot fail.
static CLI_OPEN_CHAINS_LIMIT: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(-1);
static CLI_SATURATION_LIMIT: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(-1);

/// Install the `-c/--open-chains` and `-s/--saturation` CLI values (`None`
/// leaves the HS default in force).  Called once per process by the CLI
/// entry points before any theory is loaded.
pub fn set_cli_solver_limits(open_chains: Option<u64>, saturation: Option<u64>) {
    use std::sync::atomic::Ordering;
    if let Some(c) = open_chains {
        let c = i64::try_from(c).expect("clap range-checks -c/--open-chains to 0..=i64::MAX");
        CLI_OPEN_CHAINS_LIMIT.store(c, Ordering::Relaxed);
    }
    if let Some(s) = saturation {
        let s = i64::try_from(s).expect("clap range-checks -s/--saturation to 0..=i64::MAX");
        CLI_SATURATION_LIMIT.store(s, Ordering::Relaxed);
    }
}

impl IntegerParameters {
    /// The parameters in force for this process: HS defaults with any CLI
    /// overrides applied.
    pub fn current() -> Self {
        use std::sync::atomic::Ordering;
        let mut p = IntegerParameters::default();
        let c = CLI_OPEN_CHAINS_LIMIT.load(Ordering::Relaxed);
        if c >= 0 {
            p.open_chains_limit = c;
        }
        let s = CLI_SATURATION_LIMIT.load(Ordering::Relaxed);
        if s >= 0 {
            p.saturation_limit = s;
        }
        p
    }
}

/// Number of unsolved-chain constraints in the system. Mirrors
/// `length . unsolvedChains` (System.hs:1601-1605), counting unsolved Chain
/// goals in one System. (Distinct from Haskell `unsolvedChainConstraints
/// :: Source -> [Int]` at Sources.hs:87-89, which maps over a Source's
/// cases.)
pub fn unsolved_chain_constraints(sys: &System) -> usize {
    use crate::constraint::constraints::Goal;
    sys.goals
        .iter()
        .filter(|(g, status)| !status.solved && matches!(g, Goal::Chain(_, _)))
        .count()
}

/// `Source` — one precomputed case distinction. The Haskell version
/// is `Source { _cdGoal :: Goal, _cdCases :: Disj (M.Map CaseName System) }`.
/// `cdCases` is a lazy thunk in HS; matched here by `cases_cell`, a
/// `OnceLock` that's filled on the first `cases(ctx)` call.  Trivial
/// protocols never force `KU(t:Fresh)`-style sources (HS's
/// `smartRanking.getMsgOneCase` pattern-matches on `FApp o _` before
/// touching `cdCases`, so Var-headed sources never trigger the thunk);
/// Rust matches by deferring `solve_action_goal` / `solve_premise_goal`
/// out of `precompute_full_sources` into the lazy initialiser.
pub struct Source {
    pub goal: crate::constraint::constraints::Goal,
    /// Lazy cases — wrapped in `Mutex<Option<…>>` for interior
    /// mutability.  `Mutex` (over `OnceLock`) lets `cases_set` /
    /// `cases_take` mutate the cell after initial materialisation,
    /// which `ProofContext::ensure_saturated`'s post-saturate writeback
    /// requires.
    /// Internally stores case names as `Vec<String>` — HS's
    /// `caseNames :: [String]` (the `caseNames` parameter of `solve` at
    /// Sources.hs:144-225, see line 175; `[String]` type at Sources.hs:144-225).  The list
    /// representation is critical for `combine`'s truncation rule
    /// `combine (n:_) _ = [n]` (Sources.hs:113-137, see line 137): without per-element
    /// boundaries, multi-step accumulated names can't be truncated
    /// to a single element across refineSource iters.  External
    /// callers using `cases_or_empty()` see
    /// the joined `String` (intercalated with "_"); saturate-internal
    /// code uses the `_list` variants that preserve list structure.
    pub(crate) cases_cell: std::sync::Mutex<Option<Vec<(Vec<String>, System)>>>,
    /// `true` iff case enumeration was truncated.  Search must not return
    /// `Verified` for any proof tree that consumed an incomplete
    /// source — the dropped cases could contain attack witnesses.
    /// Used to prevent wrong-VERIFIED on user-equation files where the
    /// destructor-chain explosion forces truncation.
    pub incomplete: bool,
}

impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Source")
            .field("goal", &self.goal)
            .field("cases", &self.cases_cell.lock().ok().as_deref())
            .field("incomplete", &self.incomplete)
            .finish()
    }
}

impl Clone for Source {
    fn clone(&self) -> Self {
        let v = self.cases_cell.lock().unwrap().clone();
        Source {
            goal: self.goal.clone(),
            cases_cell: std::sync::Mutex::new(v),
            incomplete: self.incomplete,
        }
    }
}

impl PartialEq for Source {
    fn eq(&self, other: &Self) -> bool {
        // Destructure without `..` so a new `Source` field forces an equality
        // decision here; all three fields participate.
        let Source {
            goal,
            cases_cell,
            incomplete,
        } = self;
        let Source {
            goal: other_goal,
            cases_cell: other_cases_cell,
            incomplete: other_incomplete,
        } = other;
        let a = cases_cell.lock().unwrap().clone();
        let b = other_cases_cell.lock().unwrap().clone();
        goal == other_goal && incomplete == other_incomplete && a == b
    }
}

impl Source {
    /// Build a Source whose cases will be computed lazily via
    /// `initial_source_cases(goal, ctx)` on the first `cases(ctx)`
    /// call.  Matches HS's `initialSource` (Sources.hs:97-110, see line 103) thunk.
    pub fn lazy(goal: crate::constraint::constraints::Goal) -> Self {
        Source {
            goal,
            cases_cell: std::sync::Mutex::new(None),
            incomplete: false,
        }
    }

    /// Build a Source with cases already computed.  Used by saturate
    /// internals that produce already-materialised case sets.
    ///
    /// Takes `Vec<(String, System)>`: each `String` becomes a
    /// single-element `Vec<String>` in the internal list
    /// representation.  Use [`Source::eager_list`] to pass an actual
    /// `Vec<(Vec<String>, System)>`.
    pub fn eager(
        goal: crate::constraint::constraints::Goal,
        cases: Vec<(String, System)>,
        incomplete: bool,
    ) -> Self {
        let list: Vec<(Vec<String>, System)> = cases
            .into_iter()
            .map(|(n, s)| (string_to_name_list(&n), s))
            .collect();
        Source {
            goal,
            cases_cell: std::sync::Mutex::new(Some(list)),
            incomplete,
        }
    }

    /// Build a Source with case-name LISTS already computed.  Used by
    /// saturate-internal code that preserves HS's `[String]` list
    /// structure across refineSource iters.
    pub fn eager_list(
        goal: crate::constraint::constraints::Goal,
        cases: Vec<(Vec<String>, System)>,
        incomplete: bool,
    ) -> Self {
        Source {
            goal,
            cases_cell: std::sync::Mutex::new(Some(cases)),
            incomplete,
        }
    }

    /// Materialise + return the cases.  `prove_lemma` runs
    /// `ProofContext::ensure_saturated` eagerly before any lemma proof
    /// starts, so the cached value is normally already populated.
    /// The defensive `ensure_saturated()` call below is idempotent
    /// (state machine returns immediately when Done) and handles
    /// odd code paths that bypass `prove_lemma` (tests, probes).
    ///
    /// Returns by-value (`Vec<…>`) rather than `&Vec<…>` because the
    /// cell is a `Mutex` and we can't hold the lock for the caller's
    /// lifetime.  Callers iterate the returned Vec normally.
    pub fn cases(
        &self,
        ctx: &crate::constraint::solver::context::ProofContext,
    ) -> Vec<(String, System)> {
        cases_list_to_string_list(self.cases_list(ctx))
    }

    /// HS-faithful: returns cases with name-LISTS preserved.  Use this
    /// when the per-element list structure matters for `combine`
    /// (`combine_case_names_list`) at refineSource boundaries.
    pub fn cases_list(
        &self,
        ctx: &crate::constraint::solver::context::ProofContext,
    ) -> Vec<(Vec<String>, System)> {
        ctx.ensure_saturated();
        let g = self.cases_cell.lock().unwrap();
        match &*g {
            Some(v) => v.clone(),
            None => {
                drop(g);
                let init_list = self.compute_cases(ctx);
                *self.cases_cell.lock().unwrap() = Some(init_list.clone());
                init_list
            }
        }
    }

    /// Compute this source's initial case set: `initial_source_cases`
    /// (HS's `initialSource` thunk body) with each joined case name split
    /// into the internal list representation.  Runs the goal-specific
    /// solvers, so callers must not hold the `cases_cell` lock across
    /// this call.
    fn compute_cases(
        &self,
        ctx: &crate::constraint::solver::context::ProofContext,
    ) -> Vec<(Vec<String>, System)> {
        initial_source_cases(&self.goal, ctx)
            .into_iter()
            .map(|(n, s)| (string_to_name_list(&n), s))
            .collect()
    }

    /// Force materialisation WITHOUT returning the cases: callers that
    /// only need the cell forced (e.g. to then read [`Source::cases_len`])
    /// skip [`Source::cases_list`]'s deep clone of every case `System`.
    /// The already-materialised path is a lock/check/unlock; the compute
    /// path mirrors `cases_list` exactly — `initial_source_cases` runs
    /// the goal-specific solvers, so it must not execute under the cell
    /// lock, and the unconditional re-lock/overwrite is deterministic
    /// because the computed value is.
    pub fn ensure_cases(&self, ctx: &crate::constraint::solver::context::ProofContext) {
        ctx.ensure_saturated();
        if self.cases_cell.lock().unwrap().is_some() {
            return;
        }
        let init_list = self.compute_cases(ctx);
        *self.cases_cell.lock().unwrap() = Some(init_list);
    }

    /// Read-only clone that returns `vec![]` when the cell hasn't
    /// been forced yet.  External-facing form (joined-String).
    pub fn cases_or_empty(&self) -> Vec<(String, System)> {
        cases_list_to_string_list(self.cases_or_empty_list())
    }

    /// HS-faithful: same as `cases_or_empty` but preserves the
    /// per-element list structure.
    pub fn cases_or_empty_list(&self) -> Vec<(Vec<String>, System)> {
        self.cases_cell.lock().unwrap().clone().unwrap_or_default()
    }

    /// Number of materialised cases — equal to `cases_or_empty().len()`
    /// but WITHOUT deep-cloning every case `System` to count them.
    /// Returns 0 when the cell hasn't been forced yet.  O(1).
    pub fn cases_len(&self) -> usize {
        self.cases_cell.lock().unwrap().as_ref().map_or(0, Vec::len)
    }

    /// The `n`-th materialised case's system — `cases_or_empty()[n].1`
    /// WITHOUT deep-cloning the cases either side of it.  Returns `None`
    /// when the cell hasn't been forced yet or `n` is past the end.
    pub fn case_system_at(&self, n: usize) -> Option<System> {
        let g = self.cases_cell.lock().unwrap();
        let (_, sys) = g.as_ref()?.get(n)?;
        Some(sys.clone())
    }

    /// Drain the materialised cases out of the cell, leaving it as
    /// `None`.  Used by saturate internals that re-build the cases
    /// list per iteration.  External-facing form (joined-String).
    pub fn cases_take(&self) -> Vec<(String, System)> {
        cases_list_to_string_list(self.cases_take_list())
    }

    /// HS-faithful: same as `cases_take` but preserves list structure.
    pub fn cases_take_list(&self) -> Vec<(Vec<String>, System)> {
        self.cases_cell.lock().unwrap().take().unwrap_or_default()
    }

    /// Replace the cases cell with a new value.  Used by saturate to
    /// install a refined case set, AND by `ensure_saturated`'s post-
    /// saturate writeback.  Takes `&self` (not `&mut`) so it works
    /// through immutable `ctx.full_sources` borrows.
    /// External-facing form: each `String` name is wrapped as a
    /// single-element list.
    pub fn cases_set(&self, cases: Vec<(String, System)>) {
        let list: Vec<(Vec<String>, System)> = cases
            .into_iter()
            .map(|(n, s)| (string_to_name_list(&n), s))
            .collect();
        *self.cases_cell.lock().unwrap() = Some(list);
    }

    /// HS-faithful: same as `cases_set` but takes the list form
    /// directly, preserving per-element boundaries.
    pub fn cases_set_list(&self, cases: Vec<(Vec<String>, System)>) {
        *self.cases_cell.lock().unwrap() = Some(cases);
    }
}

/// Convert `(Vec<String>, System)` case-list to the external
/// `(String, System)` form via HS's `intercalate "_"` join.
fn cases_list_to_string_list(list: Vec<(Vec<String>, System)>) -> Vec<(String, System)> {
    list.into_iter()
        .map(|(n, s)| (case_name_list_to_string(&n), s))
        .collect()
}

/// HS-faithful port of `initialSource ctxt restrictions goal`
/// (Sources.hs:97-110, see line 103).  Builds a fresh empty system with restrictions
/// injected, inserts `goal`, marks-as-solved (HS `solveGoal`-style),
/// then dispatches to the goal-specific solver.  The resulting cases
/// are normalised: subst applied, simplify run, contradictory cases
/// dropped, eq-store restricted to stable (= `frees (cdGoal th)`) vars.
/// Crate-internal exposure of [`initial_source_cases`] so
/// `ProofContext::ensure_saturated` can pre-populate each source's
/// cases before running saturate.
pub(crate) fn initial_source_cases_pub(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(String, System)> {
    initial_source_cases(goal, ctx)
}

fn initial_source_cases(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(String, System)> {
    // HS-faithful: `initialSource` calls `solveGoal` from Goals.hs
    // directly (NOT via `solveWithSource`), so initial case computation
    // never short-circuits through source-case dispatch.  The guard sets the
    // flag so `solve_premise_goal`'s dispatch skips during this call, and
    // restores the saved value when it drops at return.
    let _initial_guard = InitialSourceCasesGuard::enter();
    initial_source_cases_impl(goal, ctx)
}

fn initial_source_cases_impl(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(String, System)> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};

    let mut sys = System::empty();
    // HS-faithful (CloseRule.hs:422-426): source precomputation gets ONLY
    // safety restrictions.  Non-safety restrictions (e.g.
    // `Start_implies_Stop = All x #i. Start(x)@i ⇒ Ex #j. Stop(x)@j`)
    // would fire `insertImpliedFormulas` during saturate, spawning Stop
    // ActionG / node via `solveUniqueActions`, which would re-open B
    // premise → another Step → another A premise → another Start →
    // restriction fires again → Cyclic.  HS skips this entire chain by
    // filtering to safety formulas at `CloseRule.hs:425`.
    let safety_restrictions: Vec<_> = ctx
        .restrictions
        .iter()
        .filter(|r| crate::guarded::is_safety_formula(r))
        .cloned()
        .collect();
    sys.insert_lemmas(safety_restrictions.clone());
    let mut red = Reduction::new(ctx, sys);
    red.insert_goal(goal.clone());
    // HS-faithful: `solveGoal goal` (Goals.hs:201-213) marks the goal
    // BEFORE invoking the solver, since unification inside the solver
    // can rewrite the goal's fact terms.
    red.mark_goal_as_solved(goal);

    let outcome = match goal {
        Goal::Action(node, fa) => red.solve_action_goal(node, fa),
        Goal::Premise(prem, fa) => red.solve_premise_goal(prem, fa),
        _ => return Vec::new(),
    };

    // Same HS-faithful filter — safety only — for normalize_and_keep;
    // reuse the list computed above (identical filter over `ctx.restrictions`).
    let safety_only = safety_restrictions;
    let normalize_and_keep = |sys: System| -> Option<System> {
        let mut r = Reduction::new(ctx, sys);
        r.sys.insert_lemmas(safety_only.clone());
        r.subst_system();
        crate::constraint::solver::simplify::simplify_system(&mut r);
        if r.sys.eq_store.is_false() {
            return None;
        }
        if !crate::constraint::solver::contradictions::contradictions(ctx, &r.sys).is_empty() {
            return None;
        }
        let s = r.sys;
        // HS-faithful: `initialSource` (Sources.hs:105-119) does NOT restrict
        // the raw case's substitution — it returns `polish <$> runReduction
        // instantiate` verbatim, keeping every binding (e.g. a rule's internal
        // `lock`/`v` ⟼ goal-var bindings).  `restrict stableVars` is applied
        // ONLY by `refineSource` (Sources.hs:113-137, see line 123) on the SATURATED output,
        // which `refine_one_source` already mirrors.  Restricting the raw
        // case's subst here would drop its internal rule vars and so LOWER
        // `avoid th` — the fresh-var seed
        // `saturateSources` threads into `refineSource` (Sources.hs:113-137, see line 128
        // `fs = avoid th`).  With the seed one index short per dropped var, the
        // saturated source cases minted every grafted `#vr`/`~n` node id below
        // HS's.  Keeping the raw subst here makes `bounds_max` (RS's `avoid`)
        // match HS; the surviving internal bindings are dropped by the refine
        // output restrict anyway, so the rendered saturated case is unchanged
        // apart from the now-HS-aligned node numbering.
        Some(s)
    };
    match outcome {
        GoalCases::Linear => normalize_and_keep(red.sys)
            .map(|s| vec![("only".into(), s)])
            .unwrap_or_default(),
        GoalCases::LinearNamed(name) => normalize_and_keep(red.sys)
            .map(|s| vec![(name, s)])
            .unwrap_or_default(),
        GoalCases::Cases(systems) => systems
            .into_iter()
            .filter_map(|(name, s)| normalize_and_keep(s).map(|s| (name, s)))
            .collect(),
        GoalCases::Contradictory => Vec::new(),
    }
}

/// Build the structural unique-source map. For every conclusion fact
/// tag across the proof context's rules, count how many rules produce
/// it; each tag with exactly one producer yields a `UniqueSource`
/// recording the fact tag and the sole producing rule's name. The
/// result is sorted and deduplicated by fact tag.
///
/// This is a lightweight one-rule-one-source mapping, distinct from the
/// full case-distinction enumeration in `precompute_full_sources`. It is
/// stored on the `ProofContext` as `unique_sources`.
pub fn precompute_sources(
    _params: &IntegerParameters,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<UniqueSource> {
    use std::collections::BTreeMap;
    let mut counts: BTreeMap<crate::fact::FactTag, u32> = BTreeMap::new();
    for o in &ctx.rules {
        for c in &o.rule.conclusions {
            *counts.entry(c.tag).or_insert(0) += 1;
        }
    }
    let mut out = Vec::new();
    for o in &ctx.rules {
        for c in &o.rule.conclusions {
            if counts.get(&c.tag).copied() == Some(1) {
                out.push(UniqueSource {
                    fact_tag: c.tag,
                    rule_name: o.name().to_string(),
                });
            }
        }
    }
    // Dedup.
    out.sort_by_key(|a| a.fact_tag);
    out.dedup_by(|a, b| a.fact_tag == b.fact_tag);
    out
}

/// One structural unique-source entry: a fact tag whose only producer
/// is the named rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniqueSource {
    pub fact_tag: crate::fact::FactTag,
    pub rule_name: String,
}

/// `precomputeSources` (full).  Direct port of Haskell's
/// `Theory.Constraint.Solver.Sources.precomputeSources`, restricted
/// to *initial* sources (no saturation pass — we run one level of
/// case enumeration and rely on subsequent runtime expansion to
/// resolve any dangling subgoals).
///
/// For each non-special protocol-fact tag, build an abstract premise
/// goal `PremiseG (i, 0) (Fact tag (t1..tk))`, run `solve_premise_goal`
/// once on a fresh empty system, and collect the resulting cases.
/// The result is one `Source` per tag, with the goal as key and the
/// per-rule cases as the disjunction.
///
/// At runtime, `solve_premise_goal` consults this cache before
/// enumerating rules: the precomputed cases let the search graft a
/// pre-instantiated subsystem rather than re-deriving it every time.
pub fn precompute_full_sources(
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    use crate::constraint::constraints::Goal;
    use crate::fact::{fact_tag_arity, Fact, FactTag};
    use crate::rule::PremIdx;

    use std::collections::BTreeSet;
    let mut tags: BTreeSet<FactTag> = BTreeSet::new();
    for o in &ctx.rules {
        for fa in o.rule.premises.iter().chain(o.rule.conclusions.iter()) {
            if matches!(&fa.tag, FactTag::Proto(_, _, _)) {
                tags.insert(fa.tag);
            }
        }
    }

    // Lazy precompute (matches HS): emit Source structs whose `goal`
    // is set but whose `cases` are uncomputed.  When a consumer asks
    // for `src.cases(ctx)`, `initial_source_cases` runs at THAT
    // point — same as HS forcing a `cdCases` thunk.  For trivial
    // protocols where no consumer asks (e.g. `KU(t:Fresh)` source on
    // an existence lemma that hits the Recv→isend direct-enumeration
    // path), zero `[EXEC] solveGoal kind=Action fact=KUFact(...)`
    // lines fire — matching HS's output line-for-line.
    //
    // Saturation (`saturate_sources_with_simp_public`) is a separate
    // concern: it iterates `cases` and would defeat the laziness if
    // run here.  This precompute function does not run it; `context.rs`
    // invokes `saturate_sources_with_simp_public` separately.
    //
    // The guard drops at function return, restoring the saved `IN_PRECOMPUTE`
    // value; nothing between the final `out` build and the return reads the flag.
    let _precompute_guard = PrecomputeModeGuard::enter();
    let mut out: Vec<Source> = Vec::new();
    // -----------------------------------------------------------------
    // protoGoals — PremiseG for each proto-fact tag seen in the rules.
    // Mirrors Haskell's protoGoals branch of `precomputeSources`.
    // -----------------------------------------------------------------
    for tag in tags {
        let arity = fact_tag_arity(&tag);
        let goal_node = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
        let terms: Vec<tamarin_term::lterm::LNTerm> = (0..arity)
            .map(|i| {
                tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                    tamarin_term::lterm::LVar::new(
                        "t",
                        tamarin_term::lterm::LSort::Msg,
                        (i + 1) as u64,
                    ),
                ))
            })
            .collect();
        let abstract_fact = Fact::new(tag, terms);
        let goal = Goal::Premise((goal_node, PremIdx(0)), abstract_fact.clone());
        // HS-faithful: defer `initialSource`'s `solve_premise_goal`
        // call to `Source::cases(ctx)`'s first invocation.  No work
        // done here, no `[EXEC] solveGoal kind=Premise ...` line
        // emitted.  The trace fires when (and only when) a consumer
        // forces `cases(ctx)`.
        out.push(Source::lazy(goal));
    }

    // -----------------------------------------------------------------
    // msgGoals — ActionG for KU(t) over each non-trivial function
    // symbol head + a Fresh-sorted variable.  Mirrors Haskell's
    // `msgGoals = someKUGoal <$> absMsgFacts`.
    //
    // The cases produced by `solve_action_goal` for an abstract
    // `KU(t)` give the full enumeration of how the adversary derives
    // a term of that shape — including the recursive saturate-driven
    // chain.  At runtime, `solve_with_source_cases_action` (added
    // below) matches a live KU goal against these.
    // -----------------------------------------------------------------
    let goal_node = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let mut ku_patterns: Vec<tamarin_term::lterm::LNTerm> = Vec::new();
    // Per HS Sources.hs, `absMsgFacts` is `asum $ sortednub $ [..]`
    // i.e. the union of:
    //   (1) fresh-sorted singleton t.1
    //   (2) bilinear pairing em(t.1,t.2)  [if enableBP]
    //   (3) nat 1, nat t.1 %+ t.2          [if enableNat]
    //   (4) one fAppNoEq per non-implicit NoEq symbol of arity ≥ 1 OR Private
    // After `sortednub`, the list is sorted by `Ord LNTerm`.  Term Ord
    // tiebreaks first on the head FunSym; FunSym Ord is `NoEq < Ac < C`
    // (see FunctionSymbols.hs:113-117; mirrored by the `enum FunSym`
    // variant order in `function_symbols.rs`).  So C(EMap)-headed em(...) sorts
    // AFTER every NoEq-headed term — i.e. em ends up LAST in HS's
    // SAT-FINAL output for Chen_Kudla / Joux / RYY / Scott / TAK1.
    //
    // Honour that ordering here so the runtime sees sources in the
    // same order HS does — `solve_with_source_cases` consults
    // `ctx.full_sources` in iteration order, and a divergent order
    // alone is enough to swing rule-case picks (see Chen_Kudla:
    // `case Resp_1` vs `case Init_1` regression when em was inserted
    // 2nd instead of last).
    //
    // Strategy: push fresh first (sorts before any App), then all
    // NoEq fAppNoEq's via the `msig.fun_syms` BTreeSet iter (already
    // alphabetical by name), then C / AC symbols at the tail.
    //
    // Mirrors HS Sources.hs:
    //     return $ varTerm (LVar "t" LSortFresh 1)
    ku_patterns.push(tamarin_term::term::Term::Lit(
        tamarin_term::vterm::Lit::Var(tamarin_term::lterm::LVar::new(
            "t",
            tamarin_term::lterm::LSort::Fresh,
            1,
        )),
    ));
    let msig = ctx.maude.maude_sig();
    // Per-function-symbol applications.  Use Msg-sorted arg vars.
    // Mirrors Haskell `absMsgFacts` (Sources.hs):
    //     [ fAppNoEq o $ nMsgVars k
    //     | o@(_,(k,priv,_)) <- S.toList . noEqFunSyms $ msig
    //     , NoEq o `S.notMember` implicitFunSig
    //     , k > 0 || priv == Private ]
    // i.e. all NoEq symbols whose arity is ≥ 1 OR which are
    // Private, excluding the implicit `pair`/`inv`/`Mult`/`Union`
    // symbols (FunctionSymbols.hs:227-229, see line 228).  Includes both constructors
    // AND destructors (e.g. `adec`, `fst`, `snd`).
    //
    // HS uses `noEqFunSyms msig` which is the full NoEq set, including
    // reducible symbols (`adec`, `fst`, `snd`, ...).  Rust's
    // `irreducible_fun_syms` filters these out, so use `fun_syms`
    // instead to mirror HS.
    for sym in &msig.fun_syms {
        if let tamarin_term::function_symbols::FunSym::NoEq(noeq) = sym {
            // Skip HS `implicitFunSig` symbols: pair, inv.  (Mult and
            // Union are AC, not NoEq, so they're naturally excluded;
            // HS includes fst/snd/1, so they are not excluded here.)
            let name = String::from_utf8_lossy(noeq.name);
            if matches!(name.as_ref(), "pair" | "inv") {
                continue;
            }
            // HS arity gate: `k > 0 || priv == Private` —
            // include arity-≥1 symbols (regardless of priv/cons)
            // and arity-0 Private symbols; no Constructor-only filter.
            let private = matches!(
                noeq.privacy,
                tamarin_term::function_symbols::Privacy::Private
            );
            if noeq.arity == 0 && !private {
                continue;
            }
            let args: Vec<tamarin_term::lterm::LNTerm> = (0..noeq.arity)
                .map(|i| {
                    tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                        tamarin_term::lterm::LVar::new(
                            "t",
                            tamarin_term::lterm::LSort::Msg,
                            (i + 1) as u64,
                        ),
                    ))
                })
                .collect();
            ku_patterns.push(tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::NoEq(*noeq),
                args.into(),
            ));
        }
    }
    // Natural-numbers branch.  Mirrors HS Sources.hs:
    //     if enableNat msig then
    //       [ fAppNoEq natOneSym []
    //       , fAppAC NatPlus [varTerm (LVar "t" LSortNat 1), varTerm (LVar "t" LSortNat 2)] ]
    //       else []
    // AC-headed; sorts BEFORE C-headed em per FunSym Ord NoEq<Ac<C.
    if msig.enable_nat {
        ku_patterns.push(tamarin_term::term::f_app_no_eq(
            tamarin_term::function_symbols::nat_one_sym(),
            vec![],
        ));
        let nat_args: Vec<tamarin_term::lterm::LNTerm> = (1..=2u64)
            .map(|i| {
                tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                    tamarin_term::lterm::LVar::new("t", tamarin_term::lterm::LSort::Nat, i),
                ))
            })
            .collect();
        ku_patterns.push(tamarin_term::term::f_app_ac(
            tamarin_term::function_symbols::AcSym::NatPlus,
            nat_args,
        ));
    }
    // Bilinear pairing branch.  Mirrors HS Sources.hs:
    //     if enableBP msig then return $ fAppC EMap $ nMsgVars (2::Int) else []
    // C-headed; sortednub puts this LAST (after every NoEq + Ac term).
    // Without this, BP-theory targets (Chen_Kudla, TAK1, Joux, RYY,
    // Scott) miss the `KU(em(t.1,t.2))` source: HS emits 9 KU sources
    // for Chen_Kudla, and dropping this branch would leave RS with 8 —
    // exactly the `em` source missing.
    if msig.enable_bp {
        let args: Vec<tamarin_term::lterm::LNTerm> = (1..=2u64)
            .map(|i| {
                tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                    tamarin_term::lterm::LVar::new("t", tamarin_term::lterm::LSort::Msg, i),
                ))
            })
            .collect();
        ku_patterns.push(tamarin_term::term::f_app_c(
            tamarin_term::function_symbols::CSym::EMap,
            args,
        ));
    }
    for pat in ku_patterns {
        let ku_fact = crate::fact::ku_fact(pat.clone());
        let goal = Goal::Action(goal_node, ku_fact.clone());
        // HS-faithful lazy: defer `solve_action_goal` + normalisation
        // to `Source::cases(ctx)`.  No work done here.
        out.push(Source::lazy(goal));
    }

    out
}

/// Compute the source label that would identify a KU-action source
/// matching the given live `fa` (a KU fact with a single term).
/// Mirrors `source_label`'s KU arm — used at the runtime filterCases
/// step where we have the live fa (not the source).  Equivalent to
/// Haskell's full-`Source` equality (Sources.hs:217-218, signature 217,
/// body 218: `filterCases usedCase cds = filter (\x -> usedCase /= x) cds`)
/// under the precompute invariant: `precompute_full_sources` emits
/// at most one Source per distinct KU root symbol (mirroring
/// Haskell's `sortednub absMsgFacts`), and `refineSource` preserves
/// `cdGoal` through saturation — so label-equality identifies the
/// same Source that Haskell's structural `Eq` would.
fn ku_source_label_for_fa(fa: &crate::fact::LNFact) -> Option<String> {
    use crate::fact::FactTag;
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    if fa.tag != FactTag::Ku || fa.terms.len() != 1 {
        return None;
    }
    match &fa.terms[0] {
        Term::Lit(Lit::Var(v)) => Some(match v.sort {
            LSort::Fresh => "KU:fresh".to_string(),
            LSort::Pub => "KU:pub".to_string(),
            LSort::Nat => "KU:nat".to_string(),
            LSort::Node => "KU:node".to_string(),
            LSort::Msg => "KU:msg".to_string(),
        }),
        Term::App(tamarin_term::function_symbols::FunSym::NoEq(s), _) => {
            Some(format!("KU:{}", String::from_utf8_lossy(s.name)))
        }
        Term::App(tamarin_term::function_symbols::FunSym::Ac(_), _) => Some("KU:ac".to_string()),
        Term::App(tamarin_term::function_symbols::FunSym::C(_), _) => Some("KU:c".to_string()),
        Term::App(tamarin_term::function_symbols::FunSym::List, _) => Some("KU:list".to_string()),
        _ => None,
    }
}

/// HS-faithful idx bounds over a WHOLE precomputed `Source` for the
/// `matchToGoal` rename + `refineSource` seed:
///
/// * `.0` = `boundsVarIdx th0` MIN (`matchToGoal`, Sources.hs:268-317, see line 307,
///   under `instance HasFrees Source`, System.hs:1879-1889: `cdGoal`
///   pattern + ALL `cdCases`) — the rename's rebase origin.
/// * `.1` = the CASES-only MAX — feeds `fs = avoid th`
///   (Sources.hs:113-137, see line 128) where
///   `th = set cdGoal goalTerm (renamed th0)` (Sources.hs:268-317, see line 285,291):
///   `cdGoal` is the LIVE goal by then, so the pattern's frees don't
///   count; the caller maxes this (post-shift) with the live goal's
///   own max.
///
/// The two ends come from `src.goal` and the caller's case list rather than
/// from a `HasFrees` impl on `Source`, because a source's cases sit behind a
/// `Mutex` that only a `ProofContext` fills: `cases` must be the source's
/// materialised case list (`src.cases(ctx)`).
fn source_bounds(src: &Source, cases: &[(String, System)]) -> (Option<u64>, Option<u64>) {
    use tamarin_term::lterm::bounds_var_idx;
    let mut min: Option<u64> = bounds_var_idx(&src.goal).map(|(lo, _)| lo);
    let mut cases_max: Option<u64> = None;
    for (_, cs) in cases {
        if let Some((lo, hi)) = bounds_var_idx(cs) {
            min = Some(min.map_or(lo, |c| c.min(lo)));
            cases_max = Some(cases_max.map_or(hi, |c| c.max(hi)));
        }
    }
    (min, cases_max)
}

/// RAII scope for the runtime `refineSource` fresh-counter seed
/// (`fs = avoid th`, Sources.hs:113-137, see line 128): sets [`reduction::set_refine_floor`]
/// on construction and restores the previous floor on drop — early
/// `return`s and `continue`s included.  [`RefineFsScope::set`] pushes
/// `fs - 1` (so `Reduction::new` seeds the next draw at
/// `max(avoid sys, fs)`, mirroring HS's `runReduction proofStep ctxt se
/// fs`); [`RefineFsScope::floor`] pushes a raw floor and is used by the
/// disj-loop in `run_solve_all_safe_goals_disj_with_progress` (floor
/// `source_avoid`).
#[must_use = "dropping this guard immediately ends the scope it protects"]
struct RefineFsScope(u64);
impl RefineFsScope {
    /// Push a raw refine-floor, saving the previous one for restore.
    fn floor(floor: u64) -> Self {
        RefineFsScope(crate::constraint::solver::reduction::set_refine_floor(
            floor,
        ))
    }
    fn set(fs: u64) -> Self {
        Self::floor(fs.saturating_sub(1))
    }
}
impl Drop for RefineFsScope {
    fn drop(&mut self) {
        crate::constraint::solver::reduction::set_refine_floor(self.0);
    }
}

/// The largest free-var idx in `sys`, the collision floor a sub-case is
/// freshened above.  Its visited set is deliberately not `boundsVarIdx`'s
/// (LTerm.hs:672-675): the RANGES of the equation store's disjunctions count
/// here, where HS's `SubstVFresh` fold walks their domain keys alone
/// (SubstVFresh.hs:196-202), while a `Goal::Disj`'s formulas and the subterm
/// store's negative pairs do not count.  The value seeds `reserve_idxs`, so
/// every later draw of that counter moves with it.
fn system_max_idx(sys: &System) -> u64 {
    use crate::constraint::constraints::Goal;
    use std::cell::Cell;
    use tamarin_term::lterm::HasFrees;
    let max = Cell::new(0u64);
    let mut visit = |v: &tamarin_term::lterm::LVar| {
        let cur = max.get();
        if v.idx > cur {
            max.set(v.idx);
        }
    };
    for (id, ru) in sys.nodes.iter() {
        id.for_each_free(&mut visit);
        ru.for_each_free(&mut visit);
    }
    for e in &sys.edges {
        e.src.0.for_each_free(&mut visit);
        e.tgt.0.for_each_free(&mut visit);
    }
    for l in &sys.less_atoms {
        l.smaller.for_each_free(&mut visit);
        l.larger.for_each_free(&mut visit);
    }
    if let Some(la) = &sys.last_atom {
        la.for_each_free(&mut visit);
    }
    // Goals: walk node-ids and fact terms.
    for (g, _) in sys.goals.iter() {
        match g {
            Goal::Action(i, fa) => {
                i.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            Goal::Premise(p, fa) => {
                p.0.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            Goal::Chain(c, p) => {
                c.0.for_each_free(&mut visit);
                p.0.for_each_free(&mut visit);
            }
            Goal::Subterm((s, t)) => {
                s.for_each_free(&mut visit);
                t.for_each_free(&mut visit);
            }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }
    // Formulas (Guarded over parser AST) — use the explicit max helper.
    for f in sys
        .formulas
        .iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        let n = crate::guarded::max_var_idx(f);
        if n > max.get() {
            max.set(n);
        }
    }
    // Eq-store: domain + range vars must not collide with freshened sub-case
    // vars.  Without including these here, a sub-case freshened against an
    // outer system that has high-idx Maude witnesses in its eq-store
    // (e.g. from a prior solve_fact_eqs) can be assigned colliding idxs,
    // causing rule-var conflation.
    for (v, t) in sys.eq_store.subst.to_list() {
        if v.idx > max.get() {
            max.set(v.idx);
        }
        t.for_each_free(&mut visit);
    }
    for d in &sys.eq_store.conj {
        for s in &d.substs {
            for (v, t) in s.to_list() {
                if v.idx > max.get() {
                    max.set(v.idx);
                }
                t.for_each_free(&mut visit);
            }
        }
    }
    // Subterm-store: HS `instance HasFrees System` (System.hs:1833-1847)
    // folds over the subterm store too, so vars living only here must be
    // covered or a later freshen/reserve can collide with them.
    for sc in sys
        .subterm_store
        .subterms
        .iter()
        .chain(sys.subterm_store.solved_subterms.iter())
    {
        sc.small.for_each_free(&mut visit);
        sc.big.for_each_free(&mut visit);
    }
    max.get()
}

/// `refineWithSourceAsms` — direct port of Haskell's
/// `Theory.Constraint.Solver.Sources.refineWithSourceAsms`.
///
/// Takes the precomputed (saturated) source cases and a list of
/// `[sources]`-tagged lemma formulas, and prunes any case whose
/// system becomes contradictory once the assumptions are folded in.
/// Mirrors the Haskell flow:
///
/// ```text
///   for each (name, sys) in src.cases:
///     sys' = sys with assumptions added to formulas
///     re-simplify sys'
///     if simplifySystem produced a contradiction → drop the case
///     else → strip the assumptions back out (they were only added
///            for refinement) and keep
/// ```
///
/// Without this, the precomputed source cases include ones that
/// violate the user's typing/`[sources]` invariants — at runtime,
/// our search explores those spurious cases and reports false
/// counterexamples.
pub fn refine_with_source_asms(
    sources: Vec<Source>,
    assumptions: &[crate::guarded::Guarded],
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    if assumptions.is_empty() {
        return sources;
    }

    // Step 1: match Haskell's `updateSystem` (Sources.hs:466-468):
    //
    //   updateSystem se =
    //     modify sFormulas (S.union (S.fromList assumptions)) $
    //     set sSourceKind RefinedSource                       $ se
    //
    // Just inject assumptions into formulas — no simplify, no drop.
    // Haskell's `saturateSources` then handles drops via
    // `solveAllSafeGoals` Disj-monad (our `run_solve_all_safe_goals_disj`
    // mzero-equivalent).  Dropping in Step 1 with single-pass simplify
    // is non-Haskell-faithful — it misses cases where the typing
    // violation only surfaces after exhaustive Disj exploration.
    let mut intermediate: Vec<Source> = Vec::new();
    for src in sources {
        let mut new_cases: Vec<(String, System)> = Vec::new();
        for (name, mut sys) in src.cases_take() {
            for a in assumptions {
                if !crate::guarded::stores_contains(&sys.formulas, a)
                    && !crate::guarded::stores_contains(&sys.solved_formulas, a)
                {
                    sys.formulas_mut().push(std::sync::Arc::new(a.clone()));
                }
            }
            // Mirror Haskell `set sSourceKind RefinedSource`.
            sys.source_kind = Some(crate::constraint::system::SourceKind::RefinedSources);
            new_cases.push((name, sys));
        }
        // HS `refineWithSourceAsms` maps over the source LIST (fmap per
        // source) — a zero-case source stays in the list as an entry with
        // an empty case set (same invariant as `saturateSources`, see the
        // "Sources are NEVER dropped" note in the saturate loop).  Dropping
        // it here made the web "Refined sources" pane show 25 entries where
        // HS shows 29 on OIDC_Implicit (the four empties: AdversaryAction,
        // KU(e1/e2/e3)), and starves `solve_with_source_cases_*`'s
        // `Some([])` zero-case match (goal closes) into a `None`
        // fall-through (runtime rule enumeration).
        intermediate.push(Source::eager(src.goal, new_cases, src.incomplete));
    }

    // Step 2 (Haskell `saturateSources`): re-saturate with the
    // assumption-augmented cases.  This step is critical — it
    // propagates the typing constraints through the recursive premise
    // expansion, pruning cases whose continuation introduces premises
    // that violate the [sources] typing.  Haskell threads the SAME
    // `paramSaturationLimit` into this saturate as into the raw one
    // (`refineWithSourceAsms parameters … = saturateSources parameters …`,
    // Sources.hs:460-462), so a `-s` override applies here too — the
    // ctx carries it.
    let limit: usize = ctx.saturation_limit;
    let saturated = saturate_sources_with_simp(intermediate, limit, ctx);

    // Step 3 (Haskell `removeFormulas`): strip formulas + solved
    // formulas after saturation, and drop disjunction goals derived
    // from the assumptions.
    let mut out: Vec<Source> = Vec::new();
    for src in saturated {
        let mut new_cases: Vec<(String, System)> = Vec::new();
        for (name, mut sys) in src.cases_take().into_iter() {
            sys.formulas_mut().clear();
            sys.solved_formulas_mut().clear();
            sys.invalidate_max_var_idx_cache();
            sys.goals_mut()
                .retain(|(g, _)| !matches!(g, crate::constraint::constraints::Goal::Disj(_)));
            new_cases.push((name, sys));
        }
        // Keep zero-case sources — see the Step-1 note above.
        out.push(Source::eager(src.goal, new_cases, src.incomplete));
    }
    out
}

/// Variant of `saturate_sources` that re-simplifies every grafted
/// case so that any newly-fired implied formulas (from the assumption
/// universals) get a chance to prune.  Mirrors Haskell's
/// `saturateSources` invocation inside `refineWithSourceAsms`.
fn saturate_sources_with_simp(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    saturate_sources_with_simp_opt(sources, limit, ctx, /*aggressive_drop=*/ false)
}

/// `pub` re-export of [`saturate_sources_with_simp`] for
/// `ProofContext::ensure_saturated`.
pub fn saturate_sources_with_simp_public(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    saturate_sources_with_simp(sources, limit, ctx)
}

/// Per-source body of `saturate_sources_with_simp_opt`'s inner loop —
/// extracted so it can run in parallel via rayon (mirroring HS's
/// `changes \`using\` parList rdeepseq` at Sources.hs).
///
/// Returns:
///   - `new_cases` (the source's refined case list, post-restrict+dedup);
///   - `changed` (HS's `not (null names)` change signal — i.e. did any
///     case in this source advance via solveAllSafeGoals or get
///     dropped via contradiction?);
///   - `new_case_count` (count of surviving cases, == new_cases.len()).
///
/// Pure with respect to the caller's mutable state — does not touch
/// `next`, `changed`, or `current` from the outer loop.  Reads `ctx`
/// (shared, immutable), `ths_snapshot` (shared, immutable), and other
/// scalar params.  Maude IPC inside is serialised via the handle's
/// Mutex; `PrecomputeModeGuard` toggles the `thread_local!` `IN_PRECOMPUTE`
/// cell, so the per-worker flag toggle is independent.
fn refine_one_source(
    ctx: &crate::constraint::solver::context::ProofContext,
    src: Source,
    ths_snapshot: &[Source],
    branch_cap: usize,
    aggressive_drop: bool,
) -> (Vec<(Vec<String>, System)>, bool, usize) {
    use crate::constraint::solver::contradictions::contradictions;
    let mut new_cases: Vec<(Vec<String>, System)> = Vec::new();
    let mut changed = false;
    // HS-faithful `refineSource` (Sources.hs:131-148): the Reduction
    // monad flattens all `getDisj cdCases th` into a single Disj of
    // post-refine branches; `removeRedundantCases` deduplicates that
    // flat list ONCE at the end.  We accumulate to a deferred list and
    // dedup in a single pass after the loop.
    let mut deferred_filtered: Vec<(Vec<String>, crate::constraint::system::System)> = Vec::new();
    // `stable_vars` (frees of the source's `cdGoal`) is invariant across
    // the whole function — `src.goal` is never mutated by the loop — so
    // compute it ONCE here and reuse it both inside the branch loop and
    // for the post-loop removeRedundantCases.
    let mut stable_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar> =
        std::collections::BTreeSet::new();
    {
        use tamarin_term::lterm::HasFrees;
        src.goal.for_each_free(&mut |v| {
            stable_vars.insert(*v);
        });
    }
    let all_cases = src.cases_take_list();
    // HS `refineSource` (Sources.hs:113-137, see line 128): `fs = avoid th` — the fresh seed
    // for EVERY case is the max var idx over the WHOLE source `th` (all its
    // cases), NOT the per-case `avoid se`.  Compute it once here and thread
    // it as the seed floor into each case's Reduction.
    let source_avoid = all_cases
        .iter()
        .map(|(_, s)| crate::constraint::solver::reduction::bounds_max(s))
        .max()
        .unwrap_or(0);
    for (name_list, sys) in all_cases {
        // === Multi-branch refineSource (Haskell-faithful) ===
        // Precompute mode is scoped to the branch solve only; the block's guard
        // drops at the block's end — restoring the saved value before the
        // restrict/dedup below runs, and on unwind as well.
        let branches = {
            let _precompute_guard = PrecomputeModeGuard::enter();
            // HS-faithful: NO per-branch step cap.  HS `solveAllSafeGoals`
            // (Sources.hs:201-211) recurses until no safe goal and no
            // source-pick remains; the ONLY exploration bounds are the
            // open-chains limit (`chainsLeft`, paramOpenChainsLimit,
            // Sources.hs:151-153/383) and the outer saturation limit
            // (paramSaturationLimit, Sources.hs:355-384, see line 362/368).  A finite default
            // here PARKED branches mid-flight as emitted cases — states
            // with open chain/KD goals HS would have solved or
            // contradicted — ballooning Chen_Kudla's KU(exp) source from
            // HS's 29 cases to 276 and flipping the no_WPFS verdict.  HS has
            // no such cap (only chainsLeft + paramSaturationLimit), so this
            // is unconditionally unbounded.
            let outer_cap: i64 = i64::MAX;
            let (branches, branch_took_step) = run_solve_all_safe_goals_disj_with_progress(
                ctx,
                sys,
                ths_snapshot,
                // HS `solveAllSafeGoals (filter goodTh ths) (get
                // paramOpenChainsLimit parameters)` (Sources.hs:382-383):
                // the `-c/--open-chains` limit, default 10.
                IntegerParameters::current().open_chains_limit,
                outer_cap,
                branch_cap,
                name_list,
                source_avoid,
            );
            if branch_took_step {
                // HS-faithful `not (null names)` change signal —
                // solveAllSafeGoals took at least one step (safe-goal
                // solve or source-pick) on this case.  Drives outer
                // saturate re-iteration even when case count doesn't
                // grow, so multi-iter convergence patterns like
                // chaum's KU(~x:Fresh)→1-case work.
                changed = true;
            }
            branches
        };
        // HS-faithful `refineSource` (Sources.hs:113-137, see line 123):
        //   map (second (modify sSubst (restrict stableVars)))
        // restricts each branch's eq-store subst to the STABLE vars
        // (frees of the source's `cdGoal`) before dedup.  This
        // narrows the subst to bindings the runtime case-matcher
        // cares about; internal fresh bindings are dropped so
        // equivalent branches dedupe.  Dedup itself is applied ONCE
        // across the flat preDedup list (after the loop, see below).
        // `stable_vars` was computed once before the loop above.
        for (mut branch_sys, branch_name_list) in branches {
            if aggressive_drop && !contradictions(ctx, &branch_sys).is_empty() {
                changed = true;
                continue;
            }
            // Apply `restrict stableVars` to the branch's subst.
            let restricted_pairs: Vec<_> = branch_sys
                .eq_store
                .subst
                .to_list()
                .into_iter()
                .filter(|(v, _)| stable_vars.contains(v))
                .collect();
            branch_sys.invalidate_max_var_idx_cache();
            branch_sys.eq_store_mut().subst =
                tamarin_term::subst::Subst::from_list(restricted_pairs);
            deferred_filtered.push((branch_name_list, branch_sys));
        }
    }
    // HS-faithful `removeRedundantCases` (Sources.hs): applies
    // ONCE to the flat list of post-refine branches across all input
    // cases.  Gated on BP/MSet per HS short-circuit (`removeRedundantCases`
    // in Sources.hs returns the input unchanged outside BP/MSet).
    let msig = ctx.maude.maude_sig();
    // `stable_vars` was computed once before the branch loop above; reuse it.
    let deduped = remove_redundant_cases(
        msig.enable_bp,
        msig.enable_mset,
        &stable_vars,
        |c| &c.1,
        deferred_filtered,
    );
    new_cases.extend(deduped);
    let count = new_cases.len();
    (new_cases, changed, count)
}

/// HS `showSaturationSteps` (Sources.hs:363-376): when set, `saturateSources`
/// traces `[Saturating Sources] …` progress lines to stderr.
///
/// The value is `closeTheoryWithMaude`'s last argument (CloseRule.hs:57),
/// which every CLI theory close passes as `True` — `closeTranslatedTheory`
/// (TheoryLoader.hs:679, the batch/`--prove`/`--precompute-only`/web load),
/// `closeTheory` (Prover.hs:51) and `applyPartialEvaluation`
/// (Prover.hs:242).  Only the two auxiliary closes pass `False`: the NDC
/// deduction check (CloseRule.hs:246,251) and the message-derivation check
/// (MessageDerivationChecks.hs:42).  HS then emits nothing on theories whose
/// proofs never force `crcRawSources`/`crcRefinedSources`, since `trace`
/// fires at thunk-force time.
///
/// The port's contexts are built in too many places to thread a value
/// through each, so the gate is process-global:
/// `TheoryPipeline::check_translated_theory` disarms it for the NDC and
/// derivation-check stages, and `close_translated_theory` arms it for the
/// close proper.
static SHOW_SATURATION_STEPS: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

pub fn set_show_saturation_steps(on: bool) {
    SHOW_SATURATION_STEPS.store(on, std::sync::atomic::Ordering::Relaxed);
}

fn saturate_sources_with_simp_opt(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
    aggressive_drop: bool,
) -> Vec<Source> {
    use rayon::prelude::*;
    let show_steps = SHOW_SATURATION_STEPS.load(std::sync::atomic::Ordering::Relaxed);
    let mut current = sources;
    // HS-faithful: ONE pass per saturate iter via `refineSource solver`
    // where `solver = solveAllSafeGoals` (`Sources.hs`).  The
    // `run_solve_all_safe_goals_disj_with_progress` port is the single
    // saturation mechanism, matching HS architecturally — there is no
    // separate chain-fold pre-step (which would materialise branched
    // cases HS only explores lazily inside the Disj monad).
    //
    // ITERATION COUNT — HS applies `refineSource` up to `limit + 1` times
    // when changes persist (Sources.hs:355-370, see line 361).  HS's `go ths n` computes
    // `ths' = refineSource ths` in its `where` at EVERY call, then:
    //   - guard1 `any changes && n <= limit` → recurse `go ths' (n+1)`;
    //   - guard2 `n > limit`                 → return `ths'` (the final
    //     refinement computed at the n = limit+1 call).
    // So with the default limit=5 and never-converging sources, the
    // recursion runs n=1..5 (5 refinements) THEN makes one more `go` call
    // at n=6 whose `where` computes a 6th `refineSource` and returns it via
    // guard2.  Net: 6 = limit+1 refinements.  Our loop must therefore run
    // `limit + 1` iterations (the early `break` on `!changed` below already
    // mirrors HS's `otherwise` branch returning `ths'` on convergence, so
    // the extra pass only fires when changes never stop — exactly HS's
    // behaviour).  Looping only `limit` times left chaum_offline_anonymity's
    // Ku(sign) source one refinement short (29 vs HS's 33 cases), dropping
    // the deepest nested-blind C_2 source cases.
    for iter_n in 0..=limit {
        // Haskell-faithful `goodTh` filter (Sources.hs:380-381):
        //
        //   goodTh th = length (getDisj (get cdCases th)) <= 1
        //   solver = solveAllSafeGoals (filter goodTh ths) ...
        //
        // Haskell passes ONLY single-case sources to `solveAllSafeGoals`
        // during refine/saturate.  This is what bounds Haskell's
        // multi-branch refineSource case-set growth.  Without it,
        // multi-branch explodes to 234+ cases for NSPK3 Pre/Secret
        // (vs Haskell's handful), losing the Lowe attack case.  HS always
        // pairs the multi-branch refineSource with this `goodTh` filter.
        let ths_snapshot: Vec<Source> = current
            .iter()
            .filter(|s| s.cases_len() <= 1)
            .cloned()
            .collect();
        // Inside refine_with_source_asms, drive each case forward by
        // SOLVING its safe goals (chain/KD-premise/non-KU action) —
        // not just simplifying.  Mirrors Haskell's `solveAllSafeGoals`-
        // driven `saturateSources` (`Sources.hs:144-225,355`).  This is
        // what propagates typing assumptions transitively: each safe
        // goal we solve adds a new node/edge whose fact constraints
        // get unified against the assumption's pattern, eventually
        // pruning typing-violating cases.  Bare simplify alone misses
        // most of these because `insert_implied_formulas_pass` relies on
        // term-shape match against system actions, which only get
        // grafted by goal-solving.
        let mut next: Vec<Source> = Vec::new();
        let mut changed = false;
        // Haskell-faithful multi-branch refineSource:
        // run the saturate as a Disj of branches per input case,
        // emit each surviving branch as its own output case.  This
        // is what `refineSource` (Sources.hs:118-133) does via
        // `runReduction proofStep ctxt se fs`.
        //
        // HS-faithful: NO branch cap.  HS `refineSource` collects
        // every Disj-monad branch `runReduction proofStep` yields
        // (Sources.hs:118-133) — there is no bound on the number of
        // output cases.  A finite branch cap would park branches as
        // half-refined cases once the cap is reached, which is a non-HS
        // mechanism.  Unconditionally unbounded to match HS.
        let branch_cap: usize = usize::MAX;
        // Haskell-faithful: multi-branch refineSource.
        // Sources.hs's `saturateSources` runs `solveAllSafeGoals`
        // through the `Reduction` monad which is `Disj`-shaped — every
        // branch survives or dies independently via `mzero`.  The
        // surviving branches become separate output cases.
        //
        // Combined with the `goodTh` filter (Sources.hs:380-381),
        // case-set growth is bounded so attack-class lemmas (NSPK3)
        // remain findable via runtime case enumeration.
        // HS-parallel: `lib/theory/src/Theory/Constraint/Solver/Sources.hs`
        //   `any or (changes \`using\` parList rdeepseq)`
        // HS evaluates each source's `refineSource` in parallel and
        // unzips the result into `(changes, ths')`.  We mirror via
        // rayon `par_iter().map(...).collect()` on the per-source body
        // — index-preserved by `collect`, so subsequent code sees the
        // same source ordering as the sequential version.
        //
        // Determinism: the per-source body has no shared mutable state.
        // `PrecomputeModeGuard` toggles the `thread_local!` `IN_PRECOMPUTE`
        // cell, so each worker's flag is independent.  `ctx`, `ths_snapshot`,
        // `branch_cap`,
        // `aggressive_drop` are read-only.
        // `run_solve_all_safe_goals_disj_with_progress` builds its own
        // Reduction over an owned System, no aliasing.  Maude IPC
        // serialises via `MaudeHandle::inner` (Arc<Mutex>) — workers
        // queue but don't race.
        // Snapshot the per-source metadata that the post-par-iter loop
        // reads (goal / incomplete / prior case-count) BEFORE moving the
        // sources into the workers.  `collect` preserves index order, so
        // `src_meta[i]` lines up with `per_source[i]`.  This lets us move
        // `current`'s Systems into `refine_one_source` (which consumes
        // them) instead of deep-cloning every source first.
        let src_meta: Vec<(crate::constraint::constraints::Goal, bool)> = current
            .iter()
            .map(|s| (s.goal.clone(), s.incomplete))
            .collect();
        let saturated_indexed: Vec<(usize, Source)> = std::mem::take(&mut current)
            .into_iter()
            .enumerate()
            .collect();
        // Per-worker MaudePool acquire: if a pool is set on the ctx, each
        // par_iter task borrows its own Maude subprocess for the
        // duration of `refine_one_source`, so workers don't serialise
        // on the single shared `ctx.maude`'s IPC mutex.  Without a
        // pool, every worker shares `ctx.maude` (the pre-pool
        // behaviour; correct but contended).
        //
        // We build a per-task context with the pooled handle swapped
        // in via `ctx.with_swapped_maude(...)`.  The PooledMaude guard
        // releases back to the pool on drop at end of the closure.
        let per_source: Vec<(Vec<(Vec<String>, System)>, bool, usize)> = saturated_indexed
            .into_par_iter()
            .map(|(_i, src)| {
                if let Some(pool) = &ctx.maude_pool {
                    let pooled = pool.acquire();
                    // Give the worker a FRESH counter (not the pooled handle's
                    // accumulating one) so `refine_one_source`'s internal
                    // `ensure_above(avoid_max)` reseeds it to the source's OWN
                    // structural `avoid_max` — producing CANONICAL, source-
                    // local case var idxs (HS `evalFresh (avoid goalTerm)`,
                    // Sources.hs:268-317, see line 307).  Without this the case idxs depend on
                    // the pooled handle's reuse history, so the refined-source
                    // cache content (shared across lemmas) becomes
                    // order-dependent and breaks under parallel lemma proving.
                    let task_ctx =
                        ctx.with_swapped_maude(pooled.handle().with_fresh_counter_from(0));
                    refine_one_source(&task_ctx, src, &ths_snapshot, branch_cap, aggressive_drop)
                } else {
                    refine_one_source(ctx, src, &ths_snapshot, branch_cap, aggressive_drop)
                }
            })
            .collect();
        for ((new_cases, per_changed, _), (src_goal, src_incomplete)) in
            per_source.into_iter().zip(src_meta)
        {
            // HS `saturateSources` (Sources.hs:355-384) derives its
            // per-source change bit SOLELY from the solver's result:
            //   solver = do names <- solveAllSafeGoals …
            //               return (not $ null names, names)
            // `per_changed` is that `not (null names)` — whether
            // `solveAllSafeGoals` took at least one step on any of the
            // source's cases.  Nothing else feeds `changes`: neither an
            // emptied case list (every branch `mzero`'d) nor a grown one
            // re-arms the loop on its own, because both can only arise
            // from a step the solver already reported.
            if per_changed {
                changed = true;
            }
            // HS-faithful `refineSource` (Sources.hs:113-120):
            //   refineSource ctxt proofStep th = (..., set cdCases newCases th)
            // and `saturateSources` (Sources.hs:379):
            //   (changes, ths') = unzip $ map (refineSource ctxt solver) ths
            // ALWAYS returns one source per input — `set cdCases newCases th`
            // REPLACES the case list, even when it is EMPTY (every branch
            // mzero'd).  Sources are NEVER dropped; the count is constant
            // (`[SAT-FINAL] sources=N` stays fixed) and only `cdCases` shrinks.
            //
            // A source whose refine produces 0 cases must still be pushed
            // (with an empty case list) so its cell is overwritten to empty,
            // matching HS: HS solves the unsolvable KD-premise during
            // saturation, contradicts the branch, and ends with `cdCases = []`.
            // Dropping it would leave the STALE *initial* cases in the cell
            // (e.g. a builtin `check_rep`/`get_rep` coerce case), inflating the
            // locations-report SAPiC proofs.
            next.push(Source::eager_list(src_goal, new_cases, src_incomplete));
        }
        // HS trace guards (Sources.hs:361-377), with n = iter_n + 1 (HS's
        // `go thsInit 1` is 1-based):
        //   guard1 `changes && n <= limit` → "Step n (Max limit)", recurse;
        //   guard2 `n > limit`             → "Saturation aborted, …" — fires
        //     at the n = limit+1 pass REGARDLESS of convergence (guard order:
        //     guard1 already failed on `n <= limit`);
        //   otherwise (no changes, n ≤ limit) → "Done".
        // The aborted text's "can be change" typo is HS's, kept verbatim.
        if show_steps {
            let n = iter_n + 1;
            if changed && n <= limit {
                eprintln!("[Saturating Sources] Step {n} (Max {limit})");
            } else if n > limit {
                eprintln!(
                    "[Saturating Sources] Saturation aborted, more than {limit} \
                     iterations. (Limit can be change with -s=)"
                );
            } else {
                eprintln!("[Saturating Sources] Done");
            }
        }
        current = next;
        if !changed {
            break;
        }
    }
    // HS-faithful final-truncate pass: applies `combine` one more
    // time per case with empty `new_names`, which (per Sources.hs:113-137, see line 137
    // `combine (n:_) _ = [n]`) truncates any multi-element name list
    // to its first non-coerce element.  HS's saturate normally
    // achieves this via iter-2's `combine names names'` on iter-1's
    // multi-element output, but Rust's change-detection skips iter-2
    // when only safe-goal steps fired (avoiding PRF over-refinement).
    // Applying the
    // truncate as a name-only pass matches HS's final case-name
    // display without re-running solveAllSafeGoals.
    for src in current.iter_mut() {
        if let Some(cases) = src.cases_cell.lock().unwrap().as_mut() {
            for (name_list, _) in cases.iter_mut() {
                if name_list.len() > 1 {
                    let truncated = combine_case_names_list(name_list, &[]);
                    *name_list = truncated;
                }
            }
        }
    }
    current
}

/// Read the K(U|D) conclusion term of `c` from `sys` — mirrors HS
/// `kConcTerm` (Sources.hs:220-225): returns Some only when the
/// node's conclusion fact at `c.1` is a KU or KD fact.  Module-level
/// helper used by `run_solve_all_safe_goals_disj_with_progress`'s
/// `lastChainTerm` filter.
fn k_conc_term_for_chain(
    sys: &crate::constraint::system::System,
    c: &crate::constraint::constraints::NodeConc,
) -> Option<tamarin_term::lterm::LNTerm> {
    use crate::fact::FactTag;
    let (id, idx) = (&c.0, &c.1);
    let rule = sys.node_rule_safe(id)?;
    let fact = rule.conclusions.get(idx.0)?;
    if !matches!(fact.tag, FactTag::Ku | FactTag::Kd) {
        return None;
    }
    fact.terms.first().cloned()
}

/// Structural equality modulo fresh variable renaming.  Mirrors HS
/// `eqModuloFreshnessNoAC` (LTerm.hs:663-670, see line 670).  Two terms are equal iff
/// they're structurally identical after renaming every free var to a
/// fresh canonical name preserving ONLY sort.
// alpha-eq var->index maps (outer scope); probed by key only, never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn eq_modulo_freshness_no_ac(
    a: &tamarin_term::lterm::LNTerm,
    b: &tamarin_term::lterm::LNTerm,
) -> bool {
    use std::collections::HashMap;
    use tamarin_term::lterm::LVar;
    // alpha-eq var->index maps (go helper); probed by key only, never iterated;
    // std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    fn go(
        a: &tamarin_term::lterm::LNTerm,
        b: &tamarin_term::lterm::LNTerm,
        ma: &mut HashMap<LVar, u64>,
        mb: &mut HashMap<LVar, u64>,
        next: &mut u64,
    ) -> bool {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        match (a, b) {
            (Term::Lit(Lit::Var(va)), Term::Lit(Lit::Var(vb))) => {
                if va.sort != vb.sort {
                    return false;
                }
                let ka = ma.get(va).copied();
                let kb = mb.get(vb).copied();
                match (ka, kb) {
                    (Some(x), Some(y)) => x == y,
                    (None, None) => {
                        let k = *next;
                        *next += 1;
                        ma.insert(*va, k);
                        mb.insert(*vb, k);
                        true
                    }
                    _ => false,
                }
            }
            (Term::Lit(Lit::Con(ca)), Term::Lit(Lit::Con(cb))) => ca == cb,
            (Term::App(oa, xs), Term::App(ob, ys)) => {
                oa == ob
                    && xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys.iter())
                        .all(|(x, y)| go(x, y, ma, mb, next))
            }
            _ => false,
        }
    }
    let mut ma = HashMap::new();
    let mut mb = HashMap::new();
    let mut next = 0;
    go(a, b, &mut ma, &mut mb, &mut next)
}

/// Multi-branch port of `solveAllSafeGoals` matching Haskell's
/// Disj-monad semantics.  Returns ALL surviving branches as separate
/// `(System, name)` pairs.  This is the multi-output that
/// `refineSource` (Sources.hs:118-133) relies on via:
///
/// ```haskell
/// refinement = do
///     (names, se)        <- get cdCases th
///     ((x, names'), se') <- fst <$> runReduction proofStep ctxt se fs
///     return (x, (combine names names', se'))
/// ```
///
/// `runReduction proofStep ctxt se fs` returns the full Disj of
/// branches from one saturate invocation; each becomes its own output
/// case.  Our port enumerates these branches via a worklist:
///
/// - One worklist entry per alive branch.
/// - At each branching point (`GoalCases::Cases` from Disj/Split/
///   Subterm/rule-instantiation, or source-pick over multiple unused
///   candidates), the entry is replaced by N successor entries.
/// - Branches hitting a contradiction are DROPPED (Haskell mzero).
/// - Branches with no safe-goal AND no viable source-pick candidate
///   are pushed to finished (Haskell `nextStep = Nothing → return
///   caseNames`).
///
/// Termination:
/// - `outer_cap` bounds the per-branch saturate iterations.
/// - `branch_cap` caps total output branches.  When exceeded, alive
///   branches are pushed to finished with their accumulated state.
///
/// This variant also returns a flag indicating whether ANY branch took
/// at least one solve step (safe-goal solve or source-pick).  This is
/// HS-faithful `not (null names)` from `solveAllSafeGoals`'s `caseNames`
/// accumulator — the signal that drives `saturateSources`'s outer-iter
/// "changes" detection.  Without this signal Rust's saturate exits too
/// early on cases like chaum's St_S_1 where a single source-pick on a
/// later iter is needed to converge KU(~x:Fresh-Var) source-cache to
/// 1 case (HS-faithful) rather than 2.
fn run_solve_all_safe_goals_disj_with_progress(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    ths: &[Source],
    chains_limit: i64,
    outer_cap: i64,
    branch_cap: usize,
    initial_name: Vec<String>,
    source_avoid: u64,
) -> (Vec<(System, Vec<String>)>, bool) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::goals::dispatch_solve_goal;
    use crate::constraint::solver::reduction::{GoalCases, Reduction, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::simplify::simplify_system_with_fanout;
    use crate::fact::FactTag;

    // HS-faithful: track step names as a Vec<String> — HS's
    // `caseNames` (the `solve` parameter at Sources.hs:144-225, see line 175) is `[String]`
    // (type at Sources.hs:144-225).  At finish we
    // apply HS's `combine` (Sources.hs:135-139) to merge with the
    // existing case-name list from `initial_name`:
    //
    //   refineSource ctxt proofStep th =
    //     refinement = do
    //       (names, se)        <- get cdCases th
    //       ((x, names'), se') <- fst <$> runReduction proofStep ctxt se fs
    //       return (x, (combine names names', se'))
    //
    // The `Vec<String>` representation lets `combine` truncate to the
    // first non-coerce element exactly as HS does — preserving the
    // list boundary `(n:_)` pattern instead of losing it via
    // concatenation.  Without this, `combine` can't tell where one
    // step name ends and the next begins, so Rust accumulated
    // multi-step names ("Step1sencSetup_Key") that HS truncated to
    // single element ("Step1") at the refineSource boundary.
    // `last_chain_term`: tracks the most recently solved Chain's
    // conclusion term.  Mirrors HS `solveAllSafeGoals.solve`'s
    // `lastChainTerm :: Maybe LNTerm` parameter (Sources.hs:175-211).
    // Used to filter out chain goals whose conclusion is equal modulo
    // freshness to the last solved one — loop-breaker that prevents
    // user-equation destructor explosions.  Lead A from agent #35.
    // The trailing `bool` is the per-branch `took_step` flag: True iff
    // this branch (or an ancestor) dispatched a solve-step.  Mirrors
    // HS's per-Disj-branch `names` accumulator — a branch's step-taken
    // flag is only observed if the branch SURVIVES to a leaf, since
    // HS's `changes = map fst (getDisj refinement)` collects `x = not
    // (null names)` ONLY from surviving Disj branches (Sources.hs:118-
    // 133).  A branch that takes a step then mzero's contributes
    // nothing.
    struct Entry {
        sys: System,
        /// step_names accumulator
        name: Vec<String>,
        used: std::collections::BTreeSet<String>,
        chains_left: i64,
        iters_left: i64,
        last_chain_term: Option<tamarin_term::lterm::LNTerm>,
        took_step: bool,
    }
    // HS-faithful `avoid th` (Sources.hs:113-137, see line 128): thread `source_avoid` as the
    // fresh-counter floor for the WHOLE refinement of this case — including
    // the floor-0 `simplify_system_with_fanout` sub-reductions where the
    // `[sources]`-lemma `Ex #j` node is drawn — via a thread-local, restored
    // on drop.  Without it, that sub-reduction reseeds at the per-case
    // `avoid se`, undershooting HS for any case below the source-wide max.
    let _refine_floor_guard = RefineFsScope::floor(source_avoid);
    let mut worklist: Vec<Entry> = vec![Entry {
        sys: initial_sys,
        name: Vec::new(), /* fresh accumulator for steps */
        used: std::collections::BTreeSet::new(),
        chains_left: chains_limit,
        iters_left: outer_cap,
        last_chain_term: None,
        took_step: false,
    }];
    // `finished` holds (System, accumulated_step_names_list).
    // `combine` runs with `initial_name` after the loop terminates.
    let mut finished: Vec<(System, Vec<String>)> = Vec::new();
    // HS-faithful `not (null names)` progress flag: True iff some
    // SURVIVING branch dispatched a solve-step.  Accumulated only at
    // `finished.push` (a branch reaching a leaf) — see the per-branch
    // `took_step` field on `Entry`.  This drives the outer saturate's
    // "changes" detection (Sources.hs:362-384; `not (null names)` from
    // solveAllSafeGoals returning caseNames, 213-215).
    let mut any_step_taken: bool = false;
    // The sole caller passes outer_cap / branch_cap = MAX (the HS-faithful
    // unbounded default), so on the current path the two guards below never
    // fire — the real bounds are chains_left (HS chainsLeft=10) and the outer
    // saturation limit (paramSaturationLimit=5).  The caps stay as parameters
    // so a bounded caller can still cap exploration.
    let mut total_steps: usize = 0;
    let total_step_cap: usize = branch_cap.saturating_mul(50).max(2000);

    while let Some(Entry {
        sys,
        name,
        used,
        chains_left,
        iters_left,
        last_chain_term,
        took_step,
    }) = worklist.pop()
    {
        total_steps += 1;
        if total_steps > total_step_cap {
            any_step_taken |= took_step;
            finished.push((sys, name));
            continue;
        }
        if finished.len() + 1 > branch_cap || iters_left <= 0 {
            any_step_taken |= took_step;
            finished.push((sys, name));
            continue;
        }

        // HS-faithful `simplifySystem` in DisjT (Sources.hs:144-225, see line 222):
        //   simplifySystem
        //   ctxt <- ask
        //   isContra <- gets (contradictorySystem ctxt)
        //   contradictoryIf isContra
        //
        // HS's `Reduction = StateT (DisjT ...)` means any Disj-monad
        // fan-out inside `simplifySystem` (e.g. internal `solveAction`
        // on KU/KD goals, or `solveTermEqs SplitNow` AC-arms in
        // `enforce_*_uniqueness`) SPLITS the current state into
        // sibling branches BEFORE the contradictoryIf check.  Each
        // sibling proceeds independently through the rest of
        // `solveAllSafeGoals.solve`.
        //
        // This pass must PROPAGATE Disj fan-out, not collapse it in-place:
        // a simplify step that fans out N siblings must yield N sibling
        // systems here (as `simplify_system_with_fanout` does in
        // `exec_proof_method`), else N HS-siblings collapse into 1 RS branch.
        //
        // Strategy: split into N sibling systems, push the tail back
        // onto worklist with same (name, used, chains_left, iters_left,
        // last_chain_term), and process the head.  Empty result drops
        // the branch (HS mzero-equivalent).
        // HS-faithful: propagate the DisjT fan-out from simplifySystem
        // (unconditional).
        let post_simp: Vec<System> = simplify_system_with_fanout(ctx, sys);
        // Pop one sibling to continue with; push the rest back for
        // later processing.  Match HS's Disj-monad insertion order:
        // first sibling processed first (LIFO worklist → push tail
        // reversed so the head pops next).
        let sys = match post_simp.len() {
            0 => continue, // all siblings contradictory / dropped
            1 => post_simp.into_iter().next().unwrap(),
            _ => {
                let mut iter = post_simp.into_iter();
                let head = iter.next().unwrap();
                let tail: Vec<System> = iter.collect();
                for sib in tail.into_iter().rev() {
                    worklist.push(Entry {
                        sys: sib,
                        name: name.clone(),
                        used: used.clone(),
                        chains_left,
                        iters_left,
                        last_chain_term: last_chain_term.clone(),
                        took_step,
                    });
                }
                head
            }
        };
        let mut red = Reduction::new_with_floor(ctx, sys, source_avoid);
        let contras = contradictions(red.ctx, &red.sys);
        if !contras.is_empty() {
            // Haskell mzero — drop branch (don't push to finished).
            continue;
        }

        // Pick a goal — mirrors the saturate goal-pick logic.
        // Saturate-time filter (Haskell `openGoals`) drops msg-var KD
        // ChainG so `split_allowed` correctly flips True when only
        // auto-handled chains remain.  See `is_open_for_saturate_with` in
        // goals.rs for the rationale.
        //
        // Haskell-faithful Goal-Ord (Goals.hs:65-182, see line 67 `M.toList sGoals`).
        // `is_open_for_saturate_with`'s always-before relation depends only on
        // `red.sys` (not the goal), and `red.sys` is unmutated across this
        // filter, so build it once and thread it in.
        let sat_adj = red.sys.build_always_before_adj();
        let mut goals: Vec<(Goal, bool)> = red
            .sys
            .goals
            .iter()
            .filter(|(_, st)| !st.solved && !st.looping)
            .filter(|(g, _)| {
                crate::constraint::solver::goals::is_open_for_saturate_with(g, &red.sys, &sat_adj)
            })
            .map(|(g, st)| (g.clone(), st.looping))
            .collect();
        goals.sort_by(|a, b| a.0.cmp(&b.0));
        // HS-faithful `lastChainTerm` filter (Sources.hs:182-186):
        //   filterM (\(g,_) -> case g of
        //     (ChainG c _) -> (\x -> return $ Just True /=
        //                       liftM2 eqModuloFreshnessNoAC lastChainTerm x)
        //                     =<< kConcTerm c
        //     _            -> return True) goals
        //
        // Drops chain goals whose K-conclusion term is equal modulo
        // freshness to the previously solved chain's conclusion — the
        // loop-breaker that prevents user-equation destructor
        // explosions.  Without this `lastChainTerm` filter here,
        // MTI_C0 saturate iter 0 exhausts chains that HS leaves
        // open (after lastChainTerm filter) — adding the filter
        // restores the open Chain/Split goals HS picks up at iter 1
        // and drops via solveChain's forbiddenEdge / illegalCoerce /
        // isMsgVar plus solveSplit's eqsIsFalse.
        // HS-faithful `lastChainTerm` chain-goal filter (Sources.hs:182-186),
        // applied unconditionally.
        let filtered_goals: Vec<(Goal, bool)> = goals
            .iter()
            .filter(|(g, _)| {
                match g {
                    Goal::Chain(c, _) => {
                        let this_t = k_conc_term_for_chain(&red.sys, c);
                        // HS: `Just True /= liftM2 eqModuloFreshnessNoAC last this`
                        // Drop iff `last` is Some AND `this` is Some AND
                        // they're equal-mod-freshness.  Keep otherwise.
                        match (last_chain_term.as_ref(), this_t.as_ref()) {
                            (Some(lt), Some(tt)) => !eq_modulo_freshness_no_ac(lt, tt),
                            _ => true,
                        }
                    }
                    _ => true,
                }
            })
            .cloned()
            .collect();
        // Unfiltered chains view — Haskell's `unsolvedChains`.
        let any_unsolved_chain = red
            .sys
            .goals
            .iter()
            .any(|(g, st)| !st.solved && matches!(g, Goal::Chain(_, _)));
        let any_chain_goal = goals.iter().any(|(g, _)| matches!(g, Goal::Chain(_, _)));
        let split_allowed = !any_chain_goal && any_unsolved_chain;
        // Haskell parity (Sources.hs:169-170, 159).
        let is_kd_prem = |g: &Goal| -> bool {
            matches!(g, Goal::Premise(_, fa)
                if fa.tag == FactTag::Kd && !crate::fact::is_kd_xor_fact(fa))
        };
        let is_chain_prem1 =
            |g: &Goal| -> bool { matches!(g, Goal::Chain(_, (_, pi)) if pi.0 == 1) };
        // HS-faithful: HS's `safeGoal` predicate (Sources.hs:175-188)
        // marks Split/Disj/Subterm safe when `splitAllowed`.  Split is
        // allowed during saturate when `splitAllowed` (HS's
        // `safeGoal SplitG = doSplit`, Sources.hs:144-225, see line 162/194), regardless
        // of precompute/runtime.  In practice split_allowed is rarely
        // true during saturate (chain goals stay open), so this is a
        // no-op for most cases — but it is the HS-faithful behaviour.
        let is_safe = |g: &Goal| -> bool {
            match g {
                Goal::Chain(_, _) => {
                    if chains_left > 0 {
                        true
                    } else {
                        // HS `safeGoal` traces UNCONDITIONALLY (no
                        // `showSaturationSteps` gate) each time it rejects a
                        // chain goal for an exhausted budget
                        // (Sources.hs:153-155) — every mode, stderr.
                        eprintln!(
                            "[Open Chains] Too many chain constraints, \
                             stopping precomputation. Open Chains limits (can \
                             be changed with -c=): {chains_limit}"
                        );
                        false
                    }
                }
                Goal::Action(_, fa) => !matches!(fa.tag, FactTag::Ku),
                Goal::Premise(_, fa) => {
                    !matches!(fa.tag, FactTag::Ku)
                        && !crate::fact::is_kd_xor_fact(fa)
                        && !fa.is_no_sources()
                }
                Goal::Disj(_) | Goal::Subterm(_) => split_allowed,
                // HS-faithful: `safeGoal SplitG = doSplit = splitAllowed`
                // (Sources.hs:144-225, see line 162/194).
                Goal::Split(_) => split_allowed,
            }
        };
        // HS-faithful: kdPremGoals uses UNFILTERED goals (Sources.hs:144-225, see line 200),
        // safeGoals uses FILTERED (line 195).  Match HS by deriving each
        // candidate from the correct source.  `safeGoals` is a SHARED lazy
        // list in HS — each element is tested by `safeGoal` at most once
        // per iteration — so compute the head once and reuse it for the
        // pick fallback, the chains decrement, and the lastChainTerm
        // update.  (The `[Open Chains]` trace count inside `is_safe` still
        // differs from HS's demand-driven forcing — a documented deliberate
        // divergence; line content and phase placement match.)
        let first_safe = filtered_goals.iter().find(|(g, _)| is_safe(g));
        // HS `remainingChains safeGoals` (Sources.hs:196-197,215-216) keys
        // the chains decrement on the HEAD OF `safeGoals` — not on the goal
        // actually solved — so a kd-prem step still burns a chain tick
        // whenever the first safe goal is a chain, and a chain-prem1 kd
        // pick burns none when it isn't.
        let safe_head_is_chain = matches!(first_safe, Some((Goal::Chain(_, _), _)));
        let pick = goals
            .iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or(first_safe);
        // HS-faithful update of `lastChainTerm'` (Sources.hs:209-211):
        //   case (kdPremGoals, safeGoals) of
        //     ([], ((ChainG c _):_)) -> ... (t <|> lastChainTerm) =<< kConcTerm c
        //     _                      -> return lastChainTerm
        // Update when no kd-prem goals exist AND first safe goal is a
        // Chain.  HS: `t <|> lastChainTerm` keeps the existing value if
        // the new chain has no K-term (`kConcTerm` returns Nothing).
        let kd_prem_empty = !goals
            .iter()
            .any(|(g, _)| is_kd_prem(g) || is_chain_prem1(g));
        let new_last_chain_term = if kd_prem_empty {
            if let Some((Goal::Chain(c, _), _)) = first_safe {
                let t = k_conc_term_for_chain(&red.sys, c);
                // `t <|> lastChainTerm`: prefer new t, else keep old.
                t.or(last_chain_term.clone())
            } else {
                last_chain_term.clone()
            }
        } else {
            last_chain_term.clone()
        };

        if let Some((goal, _)) = pick {
            let goal = goal.clone();
            let new_chains_left = if safe_head_is_chain {
                chains_left - 1
            } else {
                chains_left
            };
            let inner_outcome = dispatch_solve_goal(&mut red, &goal);
            match inner_outcome {
                GoalCases::Contradictory => {
                    // Drop branch — Haskell mzero.
                    continue;
                }
                GoalCases::Linear => {
                    // Single output, no name added.  red.sys was
                    // mutated in place.
                    // HS-faithful change flag: a safe-goal step IS a step
                    // (`names` grows via `caseNames ++ x`, so `not (null
                    // names)` is True — Sources.hs:214-215).  The
                    // outer `saturateSources` re-iterates on ANY step, not
                    // just source-picks.
                    // HS-faithful: mark THIS branch as having taken a step;
                    // it only counts if the branch survives to a leaf.
                    worklist.push(Entry {
                        sys: red.sys,
                        name,
                        used,
                        chains_left: new_chains_left,
                        iters_left: iters_left - 1,
                        last_chain_term: new_last_chain_term.clone(),
                        took_step: true,
                    });
                }
                GoalCases::LinearNamed(sub_name) => {
                    // HS-faithful: INSIDE `solveAllSafeGoals.solve`
                    // (Sources.hs:214-215), step names are APPENDED
                    // via `caseNames ++ x` — not combined via the
                    // coerce-skipping `combine`.  `combine` runs at
                    // `refineSource` level once per saturate-outer
                    // iter (between calls to solveAllSafeGoals), not
                    // per step within solveAllSafeGoals.
                    // HS-faithful change flag: a named safe-goal step is a
                    // step → `not (null names)` True → outer saturate
                    // re-iterates (Sources.hs:214-215).
                    let mut new_name = name.clone();
                    append_step_name_list(&mut new_name, &sub_name);
                    worklist.push(Entry {
                        sys: red.sys,
                        name: new_name,
                        used,
                        chains_left: new_chains_left,
                        iters_left: iters_left - 1,
                        last_chain_term: new_last_chain_term.clone(),
                        took_step: true,
                    });
                }
                GoalCases::Cases(cases) => {
                    // Multi-output — fork.  Each case's System
                    // becomes a new alive branch.
                    //
                    // HS-faithful insertion-order processing:
                    // worklist is Vec-as-stack (LIFO), so naive
                    // push pops branches in REVERSE order.  HS's
                    // Disj-monad is depth-first INSERTION order.
                    // Reverse the cases when pushing so subsequent
                    // `worklist.pop()` calls fire them in the
                    // original [direct, destructor1, destructor2, ...]
                    // order from `solveChain` (Goals.hs:316-380),
                    // matching HS's case ordering at NSPK3/NSLPK3
                    // types and similar source-saturated lemmas.
                    //
                    // HS-faithful change flag: a forking safe-goal step is a
                    // step → each forked branch inherits took_step=true; it
                    // only counts toward `changes` if that branch survives.
                    let case_vec: Vec<_> = cases.into_iter().collect();
                    for (sub_name, case_sys) in case_vec.into_iter().rev() {
                        let mut new_name = name.clone();
                        append_step_name_list(&mut new_name, &sub_name);
                        worklist.push(Entry {
                            sys: case_sys,
                            name: new_name,
                            used: used.clone(),
                            chains_left: new_chains_left,
                            iters_left: iters_left - 1,
                            last_chain_term: new_last_chain_term.clone(),
                            took_step: true,
                        });
                    }
                }
            }
            continue;
        }

        // No safe goal — try source-pick (Haskell's third disjunct
        // of `nextStep`, line 205).
        if ths.is_empty() {
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        // Haskell-faithful: iterates over ALL useful KU goals, returning
        // the FIRST goal whose source-pick has a matching source — not
        // just the first KU action goal — so later goals still get a
        // chance to source-pick when an earlier one has no match.
        // HS-faithful `usefulGoal` filter (Goals.hs:115-123 + Sources.hs:212-213):
        // HS only source-picks KU goals tagged `Useful`.  KU goals tagged
        // `CurrentlyDeducible` / `ProbablyConstructible` / `LoopBreaker`
        // are NOT in `usefulGoals` → source-pick skips them, leaving
        // them as open goals.  Bare-Msg-var KU goals (e.g. `KU(x.13)`
        // from a destructor's KU(x) premise) get `ProbablyConstructible`,
        // NOT `Useful`, so HS does NOT source-pick on them.  Without this
        // filter, RS recursively source-picks on these abstract vars,
        // fanning Chen_Kudla's KU(pmult) into 21+ over-saturated cases
        // (vs HS's 9).  See agent #31 diagnosis.
        //
        // Haskell-faithful `filterCases` (Sources.hs:218-219):
        // skip useful_kus whose source LABEL is already in `used` —
        // picking a case from Source S consumes S entirely, not just
        // the picked case-name.  See `ku_source_label_for_fa`.
        use crate::constraint::solver::annotated_goals::Usefulness;
        let useful_kus: Vec<(crate::constraint::constraints::NodeId, crate::fact::LNFact)> = goals
            .iter()
            .filter_map(|(g, looping)| match g {
                Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
                    // HS-faithful: only `Useful`-tagged KU goals.
                    if crate::constraint::solver::goals::goal_usefulness(g, *looping, &red.sys)
                        != Usefulness::Useful
                    {
                        return None;
                    }
                    if let Some(label) = ku_source_label_for_fa(fa) {
                        if used.contains(&label) {
                            return None;
                        }
                    }
                    Some((*i, fa.clone()))
                }
                _ => None,
            })
            .collect();
        if useful_kus.is_empty() {
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        let avoid_max = system_max_idx(&red.sys);
        // Iterate useful goals in order; first one with a matching
        // source wins (Haskell `asum`).
        let mut picked: Option<(
            crate::constraint::constraints::NodeId,
            crate::fact::LNFact,
            Vec<(
                String,
                crate::constraint::system::System,
                crate::fact::LNFact,
            )>,
        )> = None;
        for (i_cand, fa_cand) in useful_kus {
            let case_pairs_opt =
                solve_with_source_cases_action(ths, &red.sys, &i_cand, &fa_cand, avoid_max);
            if let Some(case_pairs) = case_pairs_opt {
                if !case_pairs.is_empty() {
                    picked = Some((i_cand, fa_cand, case_pairs));
                    break;
                }
            }
        }
        let Some((i, fa, case_pairs)) = picked else {
            // No useful goal has a matching source — Haskell's
            // `nextStep = Nothing` → `return caseNames` (current
            // state survives).
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        };
        // Source-label-based filter (Haskell-faithful): the picked
        // useful_ku's source label was verified NOT in `used` above,
        // so all case_pairs from this single source are available.
        // No per-case-name filter needed.
        if case_pairs.is_empty() {
            // No candidates returned by solve_with_source_cases_action
            // — surface as survivor (Haskell's asum returns [] here).
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }

        // Fork: try each viable candidate as a separate branch.
        // Mirrors Haskell `asum [solveWithSourceAndReturn ctxt ths g
        // | g <- usefulGoals]` — collects all branches that survive.
        let mut any_branched = false;
        for (case_name, sys_cand, case_action) in case_pairs {
            // Graft path: caller runs solve_fact_eqs(action) +
            // chain_eqs over the grafted system.
            let mut sub = Reduction::new(ctx, sys_cand);
            let res = sub.solve_fact_eqs(
                SplitStrategy::SplitNow,
                &[tamarin_term::rewriting::Equal {
                    lhs: case_action,
                    rhs: fa.clone(),
                }],
            );
            if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                continue;
            }
            let mut tag_mismatch_edge = false;
            let chain_eqs: Vec<_> = sub
                .sys
                .edges
                .iter()
                .filter_map(|e| {
                    let src_rule = sub.sys.node_rule_safe(&e.src.0)?;
                    let tgt_rule = sub.sys.node_rule_safe(&e.tgt.0)?;
                    let fc = src_rule.conclusions.get(e.src.1 .0)?.clone();
                    let fp = tgt_rule.premises.get(e.tgt.1 .0)?.clone();
                    if fc.tag != fp.tag || fc.terms.len() != fp.terms.len() {
                        tag_mismatch_edge = true;
                        return None;
                    }
                    if fc == fp {
                        return None;
                    }
                    Some(tamarin_term::rewriting::Equal { lhs: fc, rhs: fp })
                })
                .collect();
            if tag_mismatch_edge {
                continue;
            }
            if !chain_eqs.is_empty() {
                let r2 = sub.solve_fact_eqs(SplitStrategy::SplitNow, &chain_eqs);
                if matches!(r2, Err(_) | Ok(SolveOutcome::Contradictory)) {
                    continue;
                }
            }
            sub.subst_system();

            // HS-faithful (Sources.hs): `_applySource` calls
            // `markGoalAsSolved "precomputed" goal` BEFORE conjoining
            // the case body.  The legacy graft path above does the
            // conjoin via `solve_with_source_cases_action` (which
            // produces `sys_cand`) but never marks the LIVE KU action
            // goal solved in the resulting system.  Without this, the
            // outer saturate packages this system into a source case
            // carrying an OPEN `KU(~x:Fresh)` entry — which at runtime
            // becomes a top-ranked goal (slot 7 FreshKnows) before the
            // sign-KU (slot 10 Signature), causing chaum's
            // unforgeability proof to take an extra `case fresh` step
            // HS never takes.  Mirror HS by marking the goal solved
            // after the case body is merged in.
            //
            // NARROWING: only mark when the KU term contains a Fresh
            // variable.  HS-empirically: pure-public KU terms
            // (`KU(S(myzero))`, `KU(S(S(myzero)))` in Yubi
            // Login_reachable) end up dispatched at runtime as
            // `case c_S` proof steps — HS's saturate-time mark-solved
            // for these doesn't propagate across the conjoin boundary
            // (saturate-abstract-node and live-runtime-node never
            // collide for pure-public terms).  Mark-solved-and-
            // propagate happens for KU terms carrying a Fresh var
            // (`KU(~x:Fresh)` in chaum, `KU(pcs(~k))` in StatVerif)
            // because the substGoals-narrowing path or pair-decomp
            // path that put them into the live system also reused the
            // saturate-abstract node-id.  The Fresh-bearing check
            // approximates this collision pattern faithfully:
            // pure-public KU terms (which the mark would over-approximate)
            // are exactly those whose runtime node-id doesn't collide.
            let has_fresh_var = {
                use tamarin_term::lterm::{HasFrees, LSort};
                let mut found = false;
                fa.for_each_free(&mut |v| {
                    if v.sort == LSort::Fresh {
                        found = true;
                    }
                });
                found
            };
            if has_fresh_var {
                let live_goal_action = crate::constraint::constraints::Goal::Action(i, fa.clone());
                for (g, st) in sub.sys.goals_mut().iter_mut() {
                    if g == &live_goal_action {
                        st.solved = true;
                        break;
                    }
                }
            }

            // This candidate is viable — push as a new alive branch.
            let mut new_used = used.clone();
            // Haskell-faithful: track SOURCE LABEL.
            if let Some(label) = ku_source_label_for_fa(&fa) {
                new_used.insert(label);
            } else {
                new_used.insert(case_name.clone());
            }
            // HS-faithful: source-pick step APPENDS its name to `caseNames`
            // (Sources.hs:144-225, see line 214 `(caseNames ++ x)`); `combine` runs only at the
            // refineSource boundary, not per-step inside solveAllSafeGoals.
            let mut new_name = name.clone();
            append_step_name_list(&mut new_name, &case_name);
            worklist.push(Entry {
                sys: sub.sys,
                name: new_name,
                used: new_used,
                chains_left,
                iters_left: iters_left - 1,
                last_chain_term: new_last_chain_term.clone(),
                took_step: true,
            });
            any_branched = true;
        }

        if !any_branched {
            // No candidate was viable — Haskell `asum [mzero, ...] =
            // mzero` → `nextStep = Nothing` → `solve` returns
            // `caseNames` (keep current state).  This branch survives,
            // so its `took_step` flag now counts toward `changes`.
            any_step_taken |= took_step;
            finished.push((red.sys, name));
        }
    }

    // HS-faithful: apply `refineSource`'s `combine(existing, step_names)`
    // now that solveAllSafeGoals has finished accumulating.  `combine`
    // strips leading "coerce" entries from `initial_name`; if anything
    // non-coerce remains it's the only segment we keep (the rest of
    // the chain is discarded), otherwise the accumulated step_names
    // take over.  Mirrors Sources.hs:135-139 exactly.
    let branches: Vec<(System, Vec<String>)> = finished
        .into_iter()
        .map(|(sys, step_names_list)| {
            let combined = combine_case_names_list(&initial_name, &step_names_list);
            (sys, combined)
        })
        .collect();
    (branches, any_step_taken)
}

/// Convert a stored case-name `String` to a step-name list.  Used
/// when crossing the legacy `String`-based API into the HS-faithful
/// `Vec<String>` representation.  Empty string → empty Vec;
/// otherwise treat the whole String as a single list element.
/// (Multi-element strings from saturate's internal list-aware path
/// reach this function only via the `cases_set`/`cases_take` legacy
/// wrappers, which join with `_` first.)
fn string_to_name_list(name: &str) -> Vec<String> {
    if name.is_empty() {
        Vec::new()
    } else {
        vec![name.to_string()]
    }
}

/// `solveWithSource` lite — match a precomputed source against a live
/// premise goal.  Returns one `(System, conclusion_fact)` per
/// applicable case: the system has the case's nodes/edges grafted in,
/// and the conclusion fact is the case's abstract producer-conclusion
/// term-vector to be unified against `fa_prem` by the caller (so the
/// case's terms align with the live premise's terms).
///
/// Mirrors Haskell's `applySource`:
/// ```text
///   _applySource th = do
///     markGoalAsSolved "precomputed" goal
///     (names, sysTh0) <- disjunctionOfList $ getDisj $ get cdCases th
///     sysTh <- evalBindT (someInst sysTh0) keepVarBindings
///     conjoinSystem sysTh
/// ```
/// The `someInst` step renames the case to fresh vars; `conjoinSystem`
/// merges its nodes/edges/etc into the live one — but it also runs
/// `solveFactEqs` implicitly via the unification path that aligns the
/// abstract goal's bound variables with the live goal's terms.
///
/// Caller (in `Reduction::solve_premise_goal`) drives the
/// `solveFactEqs(SplitNow, [Equal { lhs: conc_fact, rhs: fa_prem }])`
/// step over each returned tuple — that's why we hand back the
/// conclusion fact rather than running unification here (we don't have
/// a `&mut Reduction` at this layer).
/// Haskell-faithful `applySource` driver for Premise goals.  Walks
/// the source's cases, running `refine_source_case` then
/// `conjoin_refine_arm` per case (together they mirror `matchToGoal` +
/// `_applySource` from Sources.hs).
///
/// Returns `(case_name, fully_conjoined_system, branch_counter)` per
/// case that successfully matched + conjoined.  The system is already
/// aligned against the live goal via `conjoinSystem`'s `solveSubstEqs +
/// substSystem` plus a defensive `chain_eqs` pass — no additional
/// fact-eq work needed by the caller.  `branch_counter` is the
/// branch's live-counter continuation (HS FreshT-threading, task #23
/// A(ii) premise parity: `_applySource` forks the counter per case via
/// `disjunctionOfList cdCases` BELOW FreshT, so each output case's
/// continuation = the pick-time fork + that branch's OWN
/// someInst/conjoin/close-chains draws — not the shared handle's
/// post-all-cases position).
pub fn solve_with_source_cases_ctx(
    ctx: &crate::constraint::solver::context::ProofContext,
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    goal_prem_idx: crate::rule::PremIdx,
    fa_prem: &crate::fact::LNFact,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
) -> Option<Vec<(String, System, u64)>> {
    use crate::constraint::constraints::Goal;

    // HS's `filterCases` (Sources.hs:217-218) operates only inside
    // `solveAllSafeGoals` (saturate), not at runtime.  HS's runtime
    // `solveWithSource` (ProofMethod.hs:319-320, the
    // `(intercalate "_" <$>) (solveWithSource ctxt ths goal)` call site)
    // passes the FULL source
    // list every call: `solveWithSource ctxt ths goal` where `ths =
    // pcSources ctxt`.  Re-applying the same source at multiple proof
    // positions is normal HS behaviour: each saturated case has its
    // internal premise goals pre-marked solved, so `conjoinSystem` +
    // `simplifySystem`'s DG4-Fresh-uniqueness → DG3 cascade collapses
    // the grafted case onto existing nodes.  A runtime `used_sources`
    // filter forces fall-through to fresh rule enumeration, creating
    // unmerged Step/Start/Fresh nodes (NoStep_with_induction
    // divergence: extra `solve case Start` after the inner `case
    // Step`).  Removing the filter eliminates that divergence and
    // also closes a similar gap on KAS1.

    let src = sources.iter().find(|s| match &s.goal {
        Goal::Premise(_, fa) => fa.tag == fa_prem.tag,
        _ => false,
    })?;

    // HS-faithful: `solveWithSource` (ProofMethod.hs:319-320) accesses
    // `cdCases` via `(names, sysTh0) <- disjunctionOfList $ getDisj $
    // get cdCases th` — forcing the lazy thunk.  We must force via
    // `src.cases(ctx)` to trigger `ensure_saturated` here at the
    // FIRST source-case dispatch; using `cases_or_empty()` would see
    // empty cells and silently fall through to direct rule enumeration,
    // emitting an extra `[EXEC] solveGoal kind=Premise ...` trace
    // line that HS skips because its `solveWithSource` succeeded.
    // HS `matchToGoal` (Sources.hs:268-317; `maybeMatcher` 298-305) decides Just/Nothing for the
    // WHOLE source based ONLY on `maybeMatcher` (tag match, already
    // guaranteed by the `find` above) AND `doMatch (faTerm matchFact
    // faPat <> iTerm matchLVar iPat)` against the source's ABSTRACT goal
    // (`cdGoal th`, all-fresh-var terms from `precomputeSources`).  It is
    // independent of whether the individual `cdCases` survive conjoin:
    // per-case contradictions are dropped later in `_applySource`
    // (`disjunctionOfList ... >>= conjoinSystem`) WITHOUT causing
    // fall-through to runtime `solveGoal`.  Concretely, if every case is
    // contradictory, `solveWithSource` still returns `Just (empty
    // reduction)` → the proof node renders `by` with ZERO children
    // (Theory/Proof.hs:1054-1075, see line 1065), NOT a runtime bare-rule graft.
    //
    // The abstract premise pattern is all-fresh-vars, so `matchFact`
    // always succeeds for a same-tag/same-arity live fact — mirror that
    // here with an explicit probe so we return `Some` (possibly empty)
    // whenever HS's `matchToGoal` would return `Just`, instead of
    // falling back to runtime `solve_premise_goal` and re-introducing a
    // shallow producer case that HS never explores (the keylessssl
    // `injectivity` `St_C ▶₀ #j` extra-`solve case C_2` divergence:
    // every St_C source-case is `refineSubst`-contradictory at runtime,
    // but HS emits `by`).
    let abstract_match_ok = match &src.goal {
        Goal::Premise(_, fa_pat) => {
            // The precomputed source goal (`cdGoal`) is built by
            // `precomputeSources` with all-fresh-variable terms, so HS's
            // `faTerm matchFact faPat` always succeeds for a same-tag,
            // same-arity live fact.  Require the pattern to be all-var to
            // mirror that exactly (so a hypothetical non-var pattern still
            // falls through to runtime if it genuinely can't match).
            fa_pat.tag == fa_prem.tag
                && fa_pat.terms.len() == fa_prem.terms.len()
                && fa_pat.terms.iter().all(|t| {
                    matches!(
                        t,
                        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(_))
                    )
                })
        }
        _ => false,
    };

    let mut out: Vec<(String, System, u64)> = Vec::new();
    let cases = src.cases(ctx);
    // HS `matchToGoal` renames th0 ONCE for the whole source; the shift's
    // min is over `cdGoal` + ALL cases (HasFrees Source).  Compute it here
    // so every case shares the same rebase, mirroring HS exactly.
    let src_bounds = source_bounds(src, &cases);
    // HS FreshT-threading (`_applySource`, Sources.hs:344-350): the
    // live counter at the pick.  `disjunctionOfList cdCases` forks the
    // DisjT layer BELOW FreshT, so every (case × refineSubst-arm)
    // branch's someInst+conjoin draws start from an independent COPY
    // of this value — the premise-path twin of the action path's
    // `fork_base` in `solve_with_source_cases_action_with_ctx`.
    let fork_base = red_maude.map(|m| m.fresh_counter_peek());
    let live_goal = Goal::Premise((*goal_node, goal_prem_idx), fa_prem.clone());
    for (name, case_sys) in cases {
        // HS-faithful: use the stored (already-`combine`d, `_`-joined) case name
        // verbatim — never re-split on `_` (would corrupt funsyms containing `_`).
        let case_label = name.clone();
        let arms = refine_source_case(
            ctx, src, &case_sys, &live_goal, red_maude, src_bounds, fork_base,
        );
        // HS-faithful: refineSubst's multi-arm fanout (Reduction.hs:742-744
        // `disjunctionOfList performSplit`) produces one System per AC
        // unifier arm with the SAME case name.  Push each as a separate
        // (case_label, sys, branch_counter) entry.  Sibling cases sharing
        // the same case_label get `_case_N` suffixes via `distinguish`
        // (ProofMethod.hs:282-339, see line 335, applied by `uniqueListBy ... distinguish
        // cases` at ProofMethod.hs:282-339, see line 307; `uniqueListBy` at ProofMethod.hs:90-102).
        //
        // Premise sources take no `removeRedundantCases` pass: every
        // refine arm goes straight to conjoin, resuming ITS OWN counter
        // thread (HS conjoins inside the same DisjT-forked branch as the
        // someInst, Sources.hs:348-349).
        for arm in arms {
            if let Some(m) = red_maude {
                m.reset_counter_to(arm.branch_counter);
            }
            for out_arm in conjoin_refine_arm(ctx, sys, &live_goal, arm, red_maude) {
                out.push((case_label.clone(), out_arm.sys, out_arm.cont));
            }
        }
    }
    // HS-faithful: an empty `out` (all cases contradictory) still counts
    // as a successful `solveWithSource` when the abstract `matchToGoal`
    // would have matched — return `Some(empty)` so the dispatcher emits
    // `by` (no children) rather than falling through to runtime.
    if out.is_empty() && !abstract_match_ok {
        return None;
    }
    Some(out)
}

/// `rename` (LTerm.hs:638-645) over a stored source case at saturate time:
/// every free variable's index moves up by `avoid_max + 1`, so the renamed
/// case shares no index with the live system it is grafted into.  Haskell
/// draws `freshStart` from the fresh supply; saturation runs outside a
/// `Reduction`, so the caller's bounds ceiling stands in for it.
///
/// The shift runs over `instance HasFrees System` (System.hs:1864-1877), so it
/// reaches every field that instance walks — the goal store's disjunctions and
/// subterm pairs (Constraints.hs:226-232) and the subterm store's negative
/// subterms (SubtermStore.hs:552-557) included — and leaves the ranges of the
/// equation store's disjunctions alone, whose variables count as fresh
/// (SubstVFresh.hs:196-202).
fn rename_system_above(sys: &System, avoid_max: u64) -> System {
    let shift = avoid_max.saturating_add(1);
    let out = rename_system_by(sys, i128::from(shift));
    // The map invalidates the node-component cache, because a rename can LOWER
    // a maximum.  This one adds the same `shift` to every node var's idx, so
    // the node max rises by exactly `shift` as long as one node var exists:
    // re-seed the pre-shift value and bump it.  An empty node map has
    // component 0 before and after, so it keeps the seeded value.
    out.node_max_cache.set(sys.node_max_cache.get());
    if !out.nodes.is_empty() {
        out.bump_node_max_by_shift(shift);
    }
    out
}

/// `solveWithSource` for ActionG / KU goals.  Mirrors the msgGoals
/// branch of Haskell's `applySource` flow.  Given a live
/// `Action(node_live, KU(m_live))` goal, finds a precomputed source
/// whose abstract KU pattern is head-compatible with `m_live` and
/// returns one `(System, action_fact)` per applicable case.
///
/// Compatibility (mirrors Haskell `matchToGoal` for KU patterns):
///   - bare-var pattern (`KU(t:s)`):  sort `s` of pattern must be
///     ≥ sort of `m_live`.  In our typed surface, the only bare-var
///     KU source we generate is `KU(t:Fresh)`, which fires when
///     `m_live` is itself a Fresh-sorted variable / constant.
///   - app pattern (`KU(f(...))`):  `m_live` must have the same head
///     symbol `f` with matching arity.
///
/// The caller drives `solveFactEqs(SplitNow, [Equal { case_action,
/// fa_live }])` on each returned tuple — that runs Maude AC
/// unification across the case's abstract terms and the concrete
/// `m_live`, exactly mirroring Haskell's `someInst >> conjoinSystem`.
pub fn solve_with_source_cases_action(
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    avoid_max: u64,
) -> Option<Vec<(String, System, crate::fact::LNFact)>> {
    solve_with_source_cases_action_with_ctx(sources, sys, goal_node, fa_live, avoid_max, None, None)
        .map(|v| v.into_iter().map(|(n, s, f, _)| (n, s, f)).collect())
}

/// Variant that takes an optional `ProofContext` to enable the
/// Haskell-faithful `applySource` path (`refine_source_case`).
/// When `ctx_opt = Some(ctx)`, uses one-way Maude matching +
/// `someInst keepVarBindings` + `conjoinSystem` setNodes-collision
/// rule-eqs. When `None`, falls back to the legacy graft (preserves
/// older behaviour for callers that don't have a context — e.g.
/// saturate-time helpers).
#[track_caller]
pub fn solve_with_source_cases_action_with_ctx(
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    avoid_max: u64,
    ctx_opt: Option<&crate::constraint::solver::context::ProofContext>,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    // Fourth tuple element: per-output-entry live-counter continuation
    // (HS FreshT-threading — the producing branch's fork + own draws).
) -> Option<Vec<(String, System, crate::fact::LNFact, u64)>> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Only KU-tagged Action goals consult action sources.
    if fa_live.tag != FactTag::Ku || fa_live.terms.len() != 1 {
        return None;
    }
    let m_live = &fa_live.terms[0];

    // Find a source whose abstract pattern matches `m_live`.
    let src = sources.iter().find(|s| match &s.goal {
        Goal::Action(_, gfa) => {
            if gfa.tag != FactTag::Ku || gfa.terms.len() != 1 {
                return false;
            }
            let pat = &gfa.terms[0];

            match (pat, m_live) {
                (Term::Lit(Lit::Var(pv)), _) => {
                    let live_sort = sort_of_lnterm(m_live);
                    sort_ge(pv.sort, live_sort)
                }
                (Term::App(pf, pargs), Term::App(lf, largs)) => {
                    pf == lf && pargs.len() == largs.len()
                }
                // App pattern + Var live — HS's `maybeMatcher`
                // (Sources.hs:299-305) falls into the `_ -> True`
                // catch-all for this case, allowing the source-pick on
                // bare-var live terms.  The unification then binds the
                // live var to the pattern's structure (e.g.
                // `x.3 → sign(t.1, t.2)`).
                (Term::App(_, _), Term::Lit(Lit::Var(_))) => true,
                _ => false,
            }
        }
        _ => false,
    })?;

    let abstract_orig = match &src.goal {
        Goal::Action(n, _) => *n,
        _ => return None,
    };

    // HS-faithful: force the source's `cdCases` thunk via
    // `src.cases(ctx)` when we have a `ProofContext` available.
    // This triggers `ensure_saturated` on first call per ctx, then
    // returns the saturated case set.  For protocols where this
    // function isn't called (e.g. a Var-headed `KU(t:Fresh)` source
    // pattern on an existence-only lemma whose live goal is `KU(x:Msg)`
    // — sort mismatch, no match) the saturate work is never triggered,
    // matching HS's lazy-thunk behaviour.
    let cases_iter: Vec<(String, System)> = if let Some(c) = ctx_opt {
        src.cases(c)
    } else {
        src.cases_or_empty()
    };
    // HS-faithful `applySource`/`solveWithSource` (Sources.hs:321-350, see line 325,340):
    // once a source's abstract pattern MATCHES the live goal (the `src`
    // find above succeeded), `applySource` returns `Just _` and its
    // reduction runs `disjunctionOfList (getDisj cdCases)`.  When `cdCases`
    // is EMPTY, that `disjunctionOfList []` is `mzero` → ZERO branches, but
    // the OUTER `solveWithSource` still returned `Just` — so `ProofMethod`'s
    // `maybe (solveGoal goal) ... ws` does NOT fall back to `solveGoal`; the
    // goal node closes with zero open cases (rendered `by`).  RS must mirror
    // this: a matched source with ZERO precomputed cases is `Some(vec![])`,
    // NOT `None`.  Returning `None` (the `out.is_empty()` path below) would
    // conflate "matched, empty" (HS `Just []`) with "no match" (HS
    // `Nothing`), letting the caller fall through to runtime rule
    // enumeration — re-opening the `coerce` → `KD` → chain subtree HS prunes
    // for builtin destructors like `check_rep`/`get_rep` (locations-report).
    // This is the runtime half of the saturate-time fix (refineSource keeps
    // 0-case sources); both are needed for the locations-report SAPiC
    // theories' (AKE/SOC/OTP/AC) parity.
    if cases_iter.is_empty() {
        return Some(Vec::new());
    }
    let mut out: Vec<(String, System, crate::fact::LNFact, u64)> = Vec::new();

    if let Some(ctx) = ctx_opt {
        // ----------------------------------------------------------------
        // HS-faithful `refineSource` order (Sources.hs:113-137, see line 122,131;
        // `_applySource` at Sources.hs:344-350):
        //   refineSubst (per case) → removeRedundantCases (BEFORE conjoin)
        //   → _applySource (someInst + conjoinSystem) per SURVIVOR only.
        //
        // Step 1: run the REFINE half (match + refineSubst + someInst) for
        // EVERY case, collecting one `RefineArm` per refineSubst AC arm.
        // No conjoin yet.  refineSubst fan-out (HS `disjunctionOfList
        // performSplit`, Reduction.hs:742-744) yields multiple arms per
        // case; all arms share the case's `case_label`.
        // ----------------------------------------------------------------
        let mut refine_arms: Vec<(String, RefineArm)> = Vec::new();
        // HS `matchToGoal` renames th0 ONCE for the whole source; the
        // shift's min is over `cdGoal` + ALL cases (HasFrees Source).
        // Compute it here so every case shares the same rebase.
        let src_bounds = source_bounds(src, &cases_iter);
        // HS FreshT-threading (`_applySource`, Sources.hs:344-350): the
        // live counter at the pick.  `disjunctionOfList cdCases` forks
        // the DisjT layer BELOW FreshT, so every (case × arm) branch's
        // someInst+conjoin draws start from an independent COPY of this
        // value; each branch's continuation = fork + its OWN draws
        // (recorded per arm in `RefineArm::branch_counter`, resumed in
        // Step 3, and returned per output entry to the adopting caller).
        let fork_base = red_maude.map(|m| m.fresh_counter_peek());
        let live_goal = Goal::Action(*goal_node, fa_live.clone());
        for (name, case_sys) in cases_iter {
            // HS-faithful: the stored case name is ALREADY the final display
            // name — `refineSource` applied `combine` (Sources.hs:135-139) and
            // the list was joined via `intercalate "_"` (ProofMethod.hs:505-515, see line 511).
            // HS NEVER re-splits a name on `_`, so use it verbatim.
            let case_label = name.clone();
            // Haskell-faithful `applySource` path: matches the live goal
            // against the source's ABSTRACT `cdGoal` (`src.goal`) — NOT a
            // case-specific action — mirroring `matchToGoal` (Sources.hs:268-317).
            let arms = refine_source_case(
                ctx, src, &case_sys, &live_goal, red_maude, src_bounds, fork_base,
            );
            for arm in arms {
                refine_arms.push((case_label.clone(), arm));
            }
        }

        // ----------------------------------------------------------------
        // Step 2: `removeRedundantCases ctxt stableVars` (Sources.hs:236-260)
        // — run the dedup BEFORE conjoin, on the pre-conjoin case
        // sub-system (`refined_case_for_dedup`), so the expensive bilinear
        // `conjoinSystem` re-narrow is paid only for survivors HS keeps.
        // Gated on BP/MSet per HS's `removeRedundantCases` short-circuit;
        // for non-BP/non-MSet theories the dedup is a no-op (no two arms
        // ever alpha-coincide) so every arm survives — identical to before.
        // ----------------------------------------------------------------
        let survivors: std::collections::BTreeSet<usize> = {
            let msig = ctx.maude.maude_sig();
            // A 0/1-arm list is a dedup fixpoint: `sortednubBy` keeps it
            // verbatim and survivors = (0..len), so skip building
            // stable_vars/keys entirely — byte-identical to the full path,
            // since compute_compare_systems_key is pure/call-local.
            if (msig.enable_bp || msig.enable_mset) && refine_arms.len() >= 2 {
                use tamarin_term::lterm::HasFrees;
                let stable_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar> = {
                    let mut s = std::collections::BTreeSet::new();
                    s.insert(*goal_node);
                    fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
                        s.insert(*v);
                    });
                    s
                };
                // Mirror `removeRedundantCases` survivor selection exactly:
                // `sortednubBy compareSystemsUpToNewVars` keeps the LAST
                // element of an EQ-run, then `sortOn fst` restores
                // original-index order (last-wins per EQ-run).
                // Carry the previous arm's key length as a capacity hint
                // (sibling keys are similarly sized); 0 first == no reserve.
                let mut cap_hint = 0usize;
                let keyed: Vec<(usize, String)> = refine_arms
                    .iter()
                    .enumerate()
                    .map(|(idx, (_label, arm))| {
                        let key = compute_compare_systems_key(
                            &arm.refined_case_for_dedup,
                            &stable_vars,
                            cap_hint,
                        );
                        cap_hint = key.len();
                        (idx, key)
                    })
                    .collect();
                let deduped = sortednub_by(
                    &|a: &(usize, String), b: &(usize, String)| a.1.cmp(&b.1),
                    keyed,
                );
                deduped.into_iter().map(|(idx, _)| idx).collect()
            } else {
                // No dedup: every arm survives.
                (0..refine_arms.len()).collect()
            }
        };

        // ----------------------------------------------------------------
        // Step 3: `_applySource` (someInst already done; conjoinSystem +
        // conjoin-fanout + E.5 + output) for SURVIVOR arms only.  Same
        // `case_label` for all of a case's arms; proof_method.rs handles
        // `_case_N` disambiguation (HS `uniqueListBy ... distinguish cases`
        // ProofMethod.hs:282-339, see line 307).
        // ----------------------------------------------------------------
        for (idx, (case_label, arm)) in refine_arms.into_iter().enumerate() {
            if !survivors.contains(&idx) {
                continue;
            }
            // HS FreshT-threading: resume THIS branch's counter thread
            // (fork + its own someInst draws) for the conjoin — HS's
            // conjoinSystem runs inside the same DisjT-forked branch as
            // the someInst (Sources.hs:348-349), NOT after the sibling
            // branches' conjoins.
            let arm_branch_counter = arm.branch_counter;
            if let Some(m) = red_maude {
                m.reset_counter_to(arm_branch_counter);
            }
            let result = conjoin_refine_arm(ctx, sys, &live_goal, arm, red_maude);
            // Per-OUTPUT-arm continuation counter (task #23, A(ii)):
            // `conjoin_refine_arm` records each output arm's own
            // thread position — fork + that branch's someInst +
            // conjoin + step-12-arm + E.5 + close-chains draws — so
            // the adopting caller continues every arm at ITS thread,
            // not at a single post-conjoin peek shared across arms.
            for out_arm in result {
                let live_action = out_arm
                    .live_action
                    .expect("an Action-goal arm carries its post-conjoin KU fact");
                out.push((case_label.clone(), out_arm.sys, live_action, out_arm.cont));
            }
        }
    } else {
        // Legacy path: freshen + graft + caller-runs-solve_fact_eqs.
        // Used at saturate time (no ProofContext).  No conjoin-time dedup
        // (the saturate-time `refine_one_source` path already
        // deduplicates).
        for (name, case_sys) in cases_iter {
            // HS-faithful: stored case name is already final; use verbatim
            // (no `_`-splitting).  See note at the action-goal call site.
            let case_label = name.clone();
            let renamed = rename_system_above(&case_sys, avoid_max);
            let abstract_renamed = {
                let mut v = abstract_orig;
                v.idx = v.idx.saturating_add(avoid_max.saturating_add(1));
                v
            };
            let action_fact = renamed.nodes.iter().find_map(|(id, ru)| {
                if id == &abstract_renamed {
                    ru.actions.iter().find(|a| a.tag == FactTag::Ku).cloned()
                } else {
                    None
                }
            });
            let Some(action_fact) = action_fact else {
                continue;
            };
            let Some(grafted) =
                graft_case_into_action(sys, &renamed, &abstract_renamed, goal_node, fa_live)
            else {
                continue;
            };
            // Legacy path has no live-counter thread; `avoid_max` is the
            // caller's bounds ceiling (the wrapper strips this column).
            out.push((case_label, grafted, action_fact, avoid_max));
        }
    }
    if out.is_empty() {
        return None;
    }
    Some(out)
}

/// HS-faithful `caseNames ++ x` (Sources.hs) — append the step name as
/// a NEW list element.  HS's `caseNames` is `[String]`; we model it as
/// `Vec<String>` here.  Empty step names are skipped.  The
/// refineSource-boundary truncation (HS `combine`) lives in
/// `combine_case_names_list`, not here.
fn append_step_name_list(names: &mut Vec<String>, sub_name: &str) {
    if !sub_name.is_empty() {
        names.push(sub_name.to_string());
    }
}

/// Render a step-name list as a single user-facing case-name string,
/// matching HS's `intercalate "_" names'` (ProofMethod.hs:282-339, see line 318).
pub(crate) fn case_name_list_to_string(names: &[String]) -> String {
    names.join("_")
}

/// HS-faithful `combine` (Sources.hs:135-139):
///
/// ```haskell
/// combine []            ns' = ns'
/// combine ("coerce":ns) ns' = combine ns ns'
/// combine (n       :_)  _   = [n]
/// ```
///
/// Strips leading `"coerce"` elements from `existing`, then:
/// - if everything stripped → return `new_names` (HS uses `ns'`)
/// - else return ONLY the first non-coerce element as a singleton,
///   dropping the rest of `existing` AND `new_names` entirely.
///
/// This is the refineSource-boundary collapse that keeps HS's case
/// names short across saturate iters.  Mirrors Sources.hs exactly —
/// no underscore-prefix legacy: each `Vec<String>` element is a
/// single step name from `solveGoal`'s return.
fn combine_case_names_list(existing: &[String], new_names: &[String]) -> Vec<String> {
    let mut i = 0;
    while i < existing.len() && existing[i] == "coerce" {
        i += 1;
    }
    if i >= existing.len() {
        // All stripped (or empty existing) — use new names.
        new_names.to_vec()
    } else {
        // First non-coerce; discard rest of existing AND new_names.
        vec![existing[i].clone()]
    }
}

// A source-case name reaching the runtime is already the final, `combine`d
// display name (HS `combine`, Sources.hs:135-139, ported in
// `combine_case_names_list`; joined with `intercalate "_"`, ProofMethod.hs:505-515, see line 511).
// Use it verbatim — never re-split on `_`, which would corrupt function symbols
// whose names contain `_` (e.g. `c_KDF_SKc` → `SKc`).

/// Compute the term's "effective" sort.  Variables carry their sort;
/// applications default to Msg (the join of all sub-sorts).
fn sort_of_lnterm(t: &tamarin_term::lterm::LNTerm) -> tamarin_term::lterm::LSort {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => v.sort,
        Term::Lit(Lit::Con(_)) => LSort::Pub,
        _ => LSort::Msg,
    }
}

/// `a >= b` in the sort order Pub/Fresh/Nat ⊂ Msg.
fn sort_ge(a: tamarin_term::lterm::LSort, b: tamarin_term::lterm::LSort) -> bool {
    use tamarin_term::lterm::LSort;
    if a == b {
        return true;
    }
    matches!(a, LSort::Msg) && matches!(b, LSort::Pub | LSort::Fresh | LSort::Nat)
}

/// `restrict` the system's eq-store `subst` (`sSubst`) to bindings
/// whose KEY var is in `stable_vars`.  Mirrors Haskell's
/// `modify sSubst (restrict stableVars)` inside `refineSource`
/// (Sources.hs:113-137, see line 123).  All bindings keyed on rule-internal vars
/// (vars not free in the abstract `cdGoal`) are dropped.
///
/// Without this restriction, the case's eq-store at precompute time
/// retains `t:Fresh:1 → ~ltk:Fresh:N` (the abstract pattern var
/// bound to a rule's specific Fresh var).  At runtime, when
/// `conjoin_refine_arm` adds the match-subst `t:Fresh:1
/// (renamed) → ~ltkA:Fresh` to the eq-store, Maude's `addEqs`
/// chains: `~ltk:Fresh:N (renamed) = ~ltkA:Fresh`.  After
/// `subst_system`, the case's grafted Fresh-rule node has
/// conclusion `Fr(~ltkA)` — same as live's existing Fresh-rule.
/// `enforce_fresh_node_uniqueness_pass` then merges these into a
/// single producer, which later trips `prem_idx_clash` because the
/// merged producer feeds two distinct premise positions of different
/// rules.
///
/// Haskell prevents this by restricting `sSubst` to `stableVars`
/// after every `refineSource` call (saturateSources iterations
/// + matchToGoal's refineSubst).  Both places need the restrict
///   for runtime applySource to see a clean precomputed case.
fn restrict_eq_store_to_stable_vars(sys: &mut System, stable_vars: &[tamarin_term::lterm::LVar]) {
    // Haskell's `restrict` (SubstVFree.hs:160-161; call site
    // Sources.hs:122-124 `modify sSubst (restrict stableVars)`) is a
    // simple key-filter using FULL LVar equality:
    //   `Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)`
    // - No chain-chase.
    // - No flipping of non-stable→stable bindings.
    // - No sort-blind (name, idx) matching.
    // Keys not in `vars` are dropped; values that referenced dropped
    // keys become dangling — fine because Haskell's substitution lookup
    // falls back to identity for unbound vars.
    //
    // Divergences this key-filter might appear to mask are bugs
    // elsewhere (unification orientation or narrowing) and must be
    // fixed at that level, not by widening the filter here.
    let kept: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = sys
        .eq_store
        .subst
        .to_list()
        .into_iter()
        .filter(|(v, _)| stable_vars.contains(v))
        .collect();
    sys.invalidate_max_var_idx_cache();
    sys.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(kept);
}

/// `rename th0` (LTerm.hs:638-645) with the shift the caller has already
/// computed: every free variable's index moves by `shift_amount` through
/// `mapFrees (Monotone (incVar shift))`.  At runtime source dispatch this is
/// the rename `matchToGoal` performs on a whole source before matching it
/// against the live goal (Sources.hs:307, `rename th0` under `avoid
/// goalTerm`), so `shift_amount` is `freshStart - minVarIdx` over the SOURCE,
/// not over the single case being renamed.
///
/// The shift is signed: it is negative whenever the source's stored indices
/// sit above the fresh supply's seed, which is the normal case at runtime
/// source dispatch, where the supply is seeded at `avoid goalTerm`.  Every
/// shifted index stays in range by construction (`shift >= -min(source)`);
/// the clamp is defensive.
///
/// A globally-unique shift is what keeps two `applySource` calls against the
/// same live system at the same step from landing on identical indices and
/// creating spurious cycles in the joined system.
fn rename_system_by(sys: &System, shift_amount: i128) -> System {
    use tamarin_term::lterm::HasFrees;
    sys.clone()
        .map_free_monotone(&mut |v: tamarin_term::lterm::LVar| {
            let mut w = v;
            w.idx = (v.idx as i128 + shift_amount).clamp(0, u64::MAX as i128) as u64;
            w
        })
}

/// `evalBindT (someInst sysTh0) keepVarBindings` (Sources.hs:342-348): the
/// source case about to be grafted into the live system takes a fresh index
/// for every free variable whose binding the caller has not already fixed, so
/// the graft shares only the goal's own variables with the live system.
///
/// `someInst` (LTerm.hs:627-632) is `mapFrees (Arbitrary importBinding)`, so
/// the index a variable gets is decided by where `instance HasFrees System`
/// (System.hs:1832-1877) first reaches it, and every index is drawn from the
/// step's own `MonadFresh` — here the Maude handle whose counter the live
/// `Reduction` threads.  `keep` is HS's `frees goal`, seeded into the store as
/// identity bindings that `importBinding` finds and reuses instead of drawing
/// (Control/Monad/Bind.hs:125-140).
fn some_inst_system(
    sys: &System,
    keep: &[tamarin_term::lterm::LVar],
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> System {
    let mut bindings = Bindings::new();
    for v in keep {
        bindings.insert(*v, *v);
    }
    let mut fresh = maude;
    tamarin_term::bind::some_inst(sys.clone(), &mut bindings, &mut fresh)
}

/// Which live goal an `applySource` graft runs for.  HS's `matchToGoal`
/// (Sources.hs:268-317) cases on the goal constructor — `ActionG` and
/// `PremiseG` — and `_applySource` (Sources.hs:344-350) is shared; the
/// RS-only edge and counter compensations in [`refine_source_case`] and
/// [`conjoin_refine_arm`] key off the same distinction.
#[derive(Clone, Copy)]
enum SourceGoalKind {
    Action,
    Premise,
}

/// One refineSubst arm produced by [`refine_source_case`] — the
/// per-arm state at the conjoin boundary of HS's `_applySource`
/// (Sources.hs:344-350), BEFORE `conjoinSystem`.  HS runs
/// `removeRedundantCases` (Sources.hs:236-260) on these (keyed by
/// `refined_case_for_dedup`) BEFORE conjoining only the survivors.
/// [`conjoin_refine_arm`] performs the `markGoalAsSolved` +
/// `conjoinSystem` + conjoin-fanout + E.5 + close-trivial-chains +
/// output for one arm.
struct RefineArm {
    /// someInst result — the freshened case sub-system to conjoin.
    freshened_case: System,
    /// The recovered live KU action fact, for an Action goal; `None` for
    /// a Premise goal, whose caller drives no action fact.
    live_action: Option<crate::fact::LNFact>,
    /// Post-refineSubst+restrict case sub-system (BEFORE someInst/conjoin)
    /// — the dedup key (HS `removeRedundantCases` `compareSystemsUpToNewVars`).
    refined_case_for_dedup: System,
    /// HS FreshT-threading: the live counter position right after this
    /// branch's `someInst` draws.  HS `_applySource` (Sources.hs:344-350)
    /// runs `disjunctionOfList (getDisj cdCases)` BEFORE `someInst`, and
    /// DisjT sits BELOW FreshT in the Reduction stack — so EVERY
    /// (case × refineSubst-arm) branch's someInst starts from an
    /// independent COPY of the counter at the pick, and the branch's
    /// conjoin + continuation proceed from fork + that branch's OWN
    /// draws.  The caller resumes the live counter here per branch,
    /// before [`conjoin_refine_arm`].
    branch_counter: u64,
}

/// One output branch of [`conjoin_refine_arm`].
struct ConjoinedArm {
    /// The grafted live system.
    sys: System,
    /// The post-conjoin live KU action fact, for an Action goal; `None`
    /// for a Premise goal.
    live_action: Option<crate::fact::LNFact>,
    /// This branch's live-counter continuation (HS FreshT-threading):
    /// the fork plus this branch's own someInst + conjoin + step-12-arm
    /// + E.5 + close-chains draws.
    cont: u64,
}

/// Refine half of Haskell's `applySource` (Sources.hs:336-350):
///
/// ```haskell
/// applySource ctxt th0 goal = matchToGoal ctxt th0 goal >>= \th -> do
///   markGoalAsSolved goal
///   (names, sysTh0) <- disjunctionOfList $ get cdCases th
///   sysTh <- evalBindT (someInst sysTh0) keepVarBindings
///   conjoinSystem sysTh
///   return names
///   where keepVarBindings = M.fromList (map (\v -> (v,v)) (frees goal))
/// ```
///
/// And `matchToGoal` (Sources.hs:268-318):
///
/// ```haskell
/// matchToGoal ctxt th0 goalTerm =
///   case (goalTerm, get cdGoal th) of
///     (ActionG iTerm faTerm, ActionG iPat faPat) ->
///       case doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat) of
///         []      -> Nothing
///         subst:_ -> Just $ snd $ refineSource ctxt
///                                   (refineSubst subst) (set cdGoal goalTerm th)
///   where
///     th = (`evalFresh` avoid goalTerm) . rename $ th0
///     refineSubst subst = solveSubstEqs SplitNow subst >> substSystem
/// ```
///
/// `matchToGoal`'s `PremiseG` arm additionally rewires the source case's
/// EDGES onto the live premise index (Sources.hs:268-317, see line 283).
///
/// The live goal is matched against the source's ABSTRACT `cdGoal`
/// (`src.goal`) — NOT against a case-specific action.  That is what
/// Haskell does and it is what avoids conflating the case's rule-internal
/// vars (e.g. C_1's `~nc:Fresh`) with the live goal's fresh vars (e.g.
/// `~ltkA:Fresh`).  The match-subst only binds abstract pattern vars
/// (`t:Fresh:1` and `i:Node:0` from precompute), which after the case's
/// precompute-time `subst_system` are no longer present as free vars in
/// `case_sys`.  Without case-internal conflation, `someInst
/// keepVarBindings` then freshens the rule-internal vars to a globally-
/// unique idx range so the grafted Fresh-rule and live's Fresh-rule
/// remain distinct producers.
///
/// Steps (one per Haskell line above):
///
/// A.1 (`rename th0` in `matchToGoal`):
///     Rename the source — both `src.goal` (the abstract `cdGoal`) and
///     `case_sys` — by shifting every var's idx by `avoid goalTerm`
///     = max(free var idx of the live goal) + 1.  This is a LOCAL
///     counter: it does NOT advance any global state.
///
/// A.2 (`doMatch ... <> ...` in `matchToGoal`):
///     One-way Maude match: pattern (renamed abstract `cdGoal`) →
///     subject (the live goal).  Returns a substitution binding renamed
///     pattern vars to live values.  The no-AC path runs first; on
///     `NeedsAc`, fall back to Maude.
///
/// A.2.5 (`substNodePrem` in `matchToGoal`, Premise goals only):
///     Rewire the renamed case's edges from the source pattern's premise
///     index onto the live one.
///
/// A.3 (`refineSubst subst` in `matchToGoal`):
///     `solveSubstEqs SplitNow subst >> substSystem` on the renamed
///     case, then `restrict` the case's eq-store to the live goal's free
///     vars.  Since the abstract vars are not free in `case_sys` after
///     precompute, this has primarily an effect on the case's stored
///     eq-store; node/edge terms stay unchanged.
///
/// D (`evalBindT (someInst sysTh0) keepVarBindings`):
///     Freshen every var in the case EXCEPT those in `frees goal`.  This
///     is the step that draws from the OUTER `MonadFresh` counter — the
///     live Reduction's `MaudeHandle` counter, mirroring Haskell's
///     `FreshT m` instance.
///
/// ## Return shape
///
/// One `RefineArm` per surviving refineSubst arm, WITHOUT conjoining:
/// `solveTermEqs SplitNow` calls `disjunctionOfList performSplit`
/// (Reduction.hs:712-733; `performSplit` use at 723-725), whose `DisjT`
/// layer replicates the WHOLE remaining continuation per disjunct — so
/// each arm carries its own `sEqStore` into the subsequent `substSystem`
/// / `markGoalAsSolved` / `conjoinSystem` steps.  An empty Vec means the
/// case dropped (match-fail, refineSubst-contradictory, …).
///
/// Stopping at the conjoin boundary lets the caller run HS's
/// `removeRedundantCases` (Sources.hs:236-260, keyed on
/// `refined_case_for_dedup`) BEFORE calling [`conjoin_refine_arm`] on
/// the survivors only — so the expensive bilinear `conjoinSystem`
/// re-narrow is paid only for cases HS actually keeps.
///
/// Case-name disambiguation: callers push one entry per returned arm.
/// When the same `case_label` shows up twice, the proof-method
/// dispatcher appends `_case_N` per HS's `uniqueListBy ... distinguish
/// cases` (ProofMethod.hs:282-339, see line 307, with `uniqueListBy` at
/// ProofMethod.hs:90-102 and `distinguish` at ProofMethod.hs:282-339,
/// see line 335).
fn refine_source_case(
    ctx: &crate::constraint::solver::context::ProofContext,
    src: &Source,
    case_sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
    src_bounds: (Option<u64>, Option<u64>),
    // HS FreshT-threading (`_applySource`, Sources.hs:344-350): the live
    // counter position at the source pick.  `disjunctionOfList cdCases`
    // forks BELOW FreshT, so each (case × refineSubst-arm) branch's
    // `someInst` draws start from an independent COPY of this value —
    // NOT from the previous sibling branch's post-someInst position.
    // `None` = legacy callers without a live counter (no rewind).
    fork_base: Option<u64>,
) -> Vec<RefineArm> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{Reduction, SolveOutcome, SplitStrategy};
    use tamarin_term::lterm::HasFrees;

    // Pull the abstract `cdGoal` and the live goal apart together: HS's
    // `matchToGoal` matches constructor for constructor, and the Premise
    // arm carries the two premise indices for the A.2.5 edge rewire.
    let (kind, abstract_node_orig, abstract_fact_orig, prem_rewire, live_node, fa_live) =
        match (&src.goal, live_goal) {
            (Goal::Action(an, af), Goal::Action(ln, lf)) => {
                (SourceGoalKind::Action, *an, af, None, ln, lf)
            }
            (Goal::Premise((an, ap), af), Goal::Premise((ln, lp), lf)) => {
                (SourceGoalKind::Premise, *an, af, Some((*ap, *lp)), ln, lf)
            }
            _ => {
                return Vec::new();
            }
        };
    if fa_live.tag != abstract_fact_orig.tag
        || fa_live.terms.len() != abstract_fact_orig.terms.len()
    {
        return Vec::new();
    }

    // ---------------------------------------------------------------
    // A.1 — `rename th0` in matchToGoal (Sources.hs:268-317, see line 307):
    //   `th = (`evalFresh` avoid goalTerm) . rename $ th0`
    // HS `rename` (LTerm.hs:638-645) is a UNIFORM SIGNED SHIFT of the
    // whole source's free-var span: `shift = freshStart - minVarIdx th0`
    // with `freshStart = avoid goalTerm` (the supply's first draw), so
    // the renamed source's MIN idx lands exactly at `avoid goalTerm` —
    // a REBASE-DOWN at runtime, where the stored source's idxs are at
    // precompute scale.  The refine (A.3) then runs at live scale, so
    // every derived value — in particular the eq-store conj WITNESSES
    // minted by the per-variant `applyBound` re-unify, whose idxs encode
    // `avoid_max = max(dom(s) ∪ varsRange(newsubst))` — matches HS.
    // A uniform ADDITIVE shift (`goal_max.max(live_max)+1`, case at
    // precompute scale + live_max) would leave those witnesses at
    // session scale (UM_three_pass CK_secure_UM3 R_Activate: RS
    // `∃ ~ey.863 X.863` / `~ey.1193 x.2384 x.2385` vs HS
    // `∃ ~ey.11 X.11` / `~ey.341 x.680 x.681`) — the web sequent-pane
    // conj: DIFF family.  Witnesses are VFresh-bound (batch-invisible;
    // never in printed rule/goal terms).
    //
    // BP-cluster safety (case vars colliding with live `vr.0`/`i1.0`
    // nodes at conjoinSystem→setNodes): conjoin only ever sees the
    // post-`some_inst_system` case (step D), which renames
    // every non-keep var from the LIVE Reduction's counter (≥ live
    // max) — exactly HS's `someInst sysTh0` inside the live Reduction.
    // The refine intermediates at live-goal scale never reach setNodes.
    // ---------------------------------------------------------------
    let mut goal_max: u64 = 0;
    {
        let mut visit = |v: &tamarin_term::lterm::LVar| {
            if v.idx > goal_max {
                goal_max = v.idx;
            }
        };
        live_node.for_each_free(&mut visit);
        fa_live.for_each_free(&mut visit);
    }
    // `avoid goalTerm` (LTerm.hs:680-681): goal always has ≥ 1 free
    // (live_node), so avoid = max idx + 1.
    let avoid_goal = goal_max.saturating_add(1);
    let (src_min, src_cases_max) = src_bounds;
    // HS `rename x`: `boundsVarIdx x == Nothing` → x unchanged (shift 0).
    let rename_shift: i128 = match src_min {
        Some(m) => avoid_goal as i128 - m as i128,
        None => 0,
    };
    let shift_lvar = |v: &tamarin_term::lterm::LVar| {
        let mut v2 = *v;
        let n = v2.idx as i128 + rename_shift;
        v2.idx = if n < 0 { 0 } else { n as u64 };
        v2
    };
    let renamed_abstract_node = shift_lvar(&abstract_node_orig);
    let renamed_abstract_fact = abstract_fact_orig.clone().map_free(&mut |v| shift_lvar(&v));
    let mut renamed_case = rename_system_by(case_sys, rename_shift);
    // HS `refineSource` (Sources.hs:113-137, see line 128): `fs = avoid th` where
    // `th = set cdGoal goalTerm (renamed th0)` — ONE seed for EVERY
    // case's `runReduction proofStep ctxt se fs`, computed over the
    // live goal + ALL renamed cases (NOT the per-case `avoid se`).
    // Thread it into the refine's sub-Reductions via REFINE_FLOOR
    // (floor = fs - 1; `Reduction::new` lifts next-draw to floor + 1),
    // exactly like source precompute does.  Cases whose own max sits
    // below the source-wide max otherwise seed low and their refine
    // draws (freshToFree folds, witness mints) land below HS
    // (UM_three_pass residual: RS `~ex.470 x.927` vs HS `~ex.478
    // x.943` — a source-wide-vs-per-case seed deficit).
    let fs: u64 = {
        let shifted_cases_max = src_cases_max.map(|m| {
            let n = m as i128 + rename_shift;
            if n < 0 {
                0u64
            } else {
                n as u64
            }
        });
        goal_max
            .max(shifted_cases_max.unwrap_or(0))
            .saturating_add(1)
    };

    // ---------------------------------------------------------------
    // A.2 — `doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat)`.
    //
    // DelayedMatches is `Vec<(term, pattern)>` (matching Haskell's
    // `matchFact t p` = subject t, pattern p).  We match the LIVE
    // goal's terms against the RENAMED ABSTRACT pattern.  Plus the
    // node-id pattern→subject pair `(live_node, renamed_abstract_node)`.
    // ---------------------------------------------------------------
    let mut pairs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)> =
        Vec::with_capacity(fa_live.terms.len() + 1);
    for (lt, pt) in fa_live.terms.iter().zip(renamed_abstract_fact.terms.iter()) {
        pairs.push((lt.clone(), pt.clone()));
    }
    pairs.push((
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(*live_node)),
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(renamed_abstract_node)),
    ));

    // HS-faithful `doMatch (faTerm matchFact faPat <> iTerm matchLVar
    // iPat)` = `runReader (solveMatchLNTerm match) hnd` (Sources.hs:268-317, see line 312).  `solveMatchLTerm` (Term/Unification.hs:209-214) runs the
    // native matcher and ONLY shells out to `matchViaMaude` on the
    // `Left ACProblem` branch; a `Left NoMatcher` returns `[]` with NO
    // Maude round-trip.  Mirror that 3-way split: native NoMatcher ⇒
    // bail (no Maude), native match ⇒ use it, NeedsAc ⇒ Maude fallback.
    let match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = {
        use tamarin_term::unification::MatchOutcome;
        let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs.clone());
        match tamarin_term::unification::solve_match_lterm::<tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name,
            problem,
        ) {
            MatchOutcome::Matched(s) => s.to_list(),
            MatchOutcome::NoMatcher => {
                return Vec::new();
            }
            MatchOutcome::NeedsAc => {
                let match_eqs: Vec<_> = pairs
                    .into_iter()
                    .map(|(t, p)| tamarin_term::rewriting::Equal { lhs: t, rhs: p })
                    .collect();
                let substs_res = ctx.maude.match_eqs(&match_eqs);
                let mut substs = match substs_res {
                    Ok(s) => s,
                    Err(_) => {
                        return Vec::new();
                    }
                };
                if substs.is_empty() {
                    return Vec::new();
                }
                substs.swap_remove(0)
            }
        }
    };

    // ---------------------------------------------------------------
    // A.2.5 (Premise goals) — substNodePrem pPat (iPat, premIdxTerm).
    // HS `matchToGoal` (Sources.hs:268-317, see line 283) rewrites ONLY the source case's
    // EDGES: `modM sEdges (substNodePrem pPat (iPat, premIdxTerm))`, where
    // `substNodePrem from to = S.map (\e@(Edge c p) -> if p == from then
    // Edge c to else e)`.  It does NOT touch `sGoals`.  So when the source
    // pattern's consumer premise sits at index 0 (all precomputed sources
    // use `PremIdx 0`, Sources.hs:417) but the LIVE goal being solved is at
    // index i≠0, HS keeps the source case's SOLVED premise goal at index 0.
    // After `conjoinSystem` re-inserts it (with a fresh gsNr) and node-merge
    // relabels its node to the live node, this leaves a redundant SOLVED
    // "ghost" premise goal `fa ▶₀ #i` alongside the genuine (now-solved)
    // `fa ▶ᵢ #i`.  That ghost is search-inert (solved goals never drive open-
    // goal selection) but it IS rendered in the per-node sequent, so the web
    // UI must reproduce it byte-for-byte.  Do not rewrite the GOAL
    // index — only edges — or the ghost goal is deduped away and
    // diverges from HS on the interactive per-node systems.
    if let Some((abstract_prem_idx, live_prem_idx)) = prem_rewire {
        let pat_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
            (renamed_abstract_node, abstract_prem_idx);
        let new_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
            (renamed_abstract_node, live_prem_idx);
        // In-place edge-endpoint rewrite through `content_mut()` — the
        // conservative door bumps `content_stamp` (and, harmlessly, invalidates
        // the caches: `renamed_case` was freshened, marker already cleared, and it
        // is about to be wrapped in a `Reduction` and refined).
        for e in renamed_case.content_mut().edges.iter_mut() {
            if e.tgt == pat_prem {
                e.tgt = new_prem;
            }
        }
    }

    // ---------------------------------------------------------------
    // A.3 — `refineSubst subst = solveSubstEqs SplitNow subst >> substSystem`.
    //
    // Build `Equal (varTerm v) t` for each (v, t) in the match-subst,
    // then run them through the renamed case's Reduction.
    //
    // The whole refine (A.3 solve + per-arm fork/subst_system below)
    // runs under HS's `fs = avoid th` seed via `RefineFsScope`; the
    // guard drops at function end, before the caller's conjoin (LIVE-
    // counter territory in HS).  someInst (`some_inst_system`) draws
    // directly from `red_m`, so it is floor-immune — matching HS where
    // someInst runs in the LIVE Reduction, outside refineSource's
    // runReduction.
    // ---------------------------------------------------------------
    let _refine_fs = RefineFsScope::set(fs);
    let mut refined = Reduction::new(ctx, renamed_case);
    // HS-faithful `solveSubstEqs` (Reduction.hs:721-740, see line 736):
    //   solveTermEqs split [Equal (varTerm v) t | (v, t) <- substToList subst]
    // builds `Equal (varTerm v) t` with no conditional flip.
    let term_eqs: Vec<_> = match_pairs
        .into_iter()
        .map(|(v, t)| {
            let pattern_var_term = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v));
            tamarin_term::rewriting::Equal {
                lhs: pattern_var_term,
                rhs: t,
            }
        })
        .collect();
    // -----------------------------------------------------------------
    // refineSubst fan-out (HS Reduction.hs:712-733; `performSplit` use
    // at 723-725).
    //
    // HS's `solveTermEqs SplitNow` calls
    //     disjunctionOfList $ performSplit eqs2 splitId
    // when the AC unifier produces multiple disjunctive results.  RS's
    // `solve_term_eqs` returns `SolveOutcome::Cases(arms)` when N>1
    // AC arms survive per-arm simp; it does NOT install any arm into
    // `self.sys.eq_store` in that case, so each arm's Fresh-Fresh
    // bindings must be installed explicitly below or they are silently
    // dropped from the live system.  A multiset Counter premise solve
    // yielded by HS as `Inc_case_1 | Inc_case_2` collapses to a single
    // Inc case without the fan-out.
    //
    // Arm order is preserved from `EquationStore::perform_split`, which
    // matches HS's `performSplit eqs2 splitId` enumeration order (Maude
    // unifier result order).
    let arm_eq_stores: Vec<crate::tools::equation_store::EquationStore> = if term_eqs.is_empty() {
        // No refineSubst; keep current eq_store as the sole arm.
        vec![(**refined.sys.eq_store).clone()]
    } else {
        let outcome = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
        match outcome {
            Err(_) | Ok(SolveOutcome::Contradictory) => {
                return Vec::new();
            }
            Ok(SolveOutcome::Linear(_)) => {
                // Single arm: solve_term_eqs already installed it
                // into refined.sys.eq_store.  Mirror as a single-arm
                // Vec so the post-continuation runs once with that
                // store.
                vec![(**refined.sys.eq_store).clone()]
            }
            Ok(SolveOutcome::Cases(arms)) => arms,
        }
    };

    // Fork off a per-arm continuation.  Each arm gets its own clone of
    // the post-refineSubst `refined.sys`, then runs `subst_system` →
    // `restrict_eq_store_to_stable_vars` → someInst — the same flow, but
    // per-arm so each arm's eq_store substitutes through the rest of
    // the case body independently.
    let post_solve_sys_template = refined.sys.clone();
    // HS FreshT-threading (task #23, A(ii)): the refineSubst fan-out
    // point inside refineSource's own `runReduction ... fs` scale —
    // each arm's substSystem continues the refine counter from here
    // (interim: post-solve_term_eqs across-arm high water; faithful
    // would be fork + arm's own eq-simp draws), instead of rewinding
    // to `bounds_max(template)`.
    let refine_fork_cont = refined.maude.fresh_counter_peek();
    let mut out_arms: Vec<RefineArm> = Vec::with_capacity(arm_eq_stores.len());

    for arm_eq_store in arm_eq_stores {
        // Install this arm's eq_store into a fresh per-arm Reduction
        // whose system body is the post-refineSubst template.  This
        // mirrors HS's `DisjT` replication of the Reduction continuation
        // (Reduction.hs:742-744 `disjunctionOfList performSplit`).
        let mut refined = fork_arm_reduction(
            ctx,
            &post_solve_sys_template,
            arm_eq_store,
            refine_fork_cont,
        );
        refined.subst_system();
        if refined.sys.eq_store.is_false() {
            continue;
        }
        // Mirror Haskell `refineSource ctxt (refineSubst subst) (set cdGoal goalTerm th)`
        // (Sources.hs:268-317, see line 285,290): after refineSubst, restrict the case's
        // eq-store to `frees (cdGoal th) = frees goalTerm` — the LIVE
        // goal's free vars (since `set cdGoal goalTerm` was applied).
        // Drops any leftover abstract/rule-internal bindings introduced
        // during precompute and renamed via Step A.1.
        let runtime_stable = frees(&(*live_node, fa_live.clone()));
        restrict_eq_store_to_stable_vars(&mut refined.sys, &runtime_stable);
        let refined_case = refined.sys;
        // The post-refineSubst+restrict case sub-system, the dedup key the
        // caller feeds to HS's `removeRedundantCases ctxt stableVars`.
        let refined_case_for_dedup = refined_case.clone();

        // ---------------------------------------------------------------
        // D — `evalBindT (someInst sysTh0) keepVarBindings`.
        //
        // keepVarBindings = M.fromList (map (\v -> (v,v)) (frees goal)).
        // For `ActionG iTerm faTerm`, `frees goal = [iTerm] ++ frees faTerm`
        // = live_node + free vars of fa_live; `PremiseG (iTerm, pIdx) faTerm`
        // has the same frees (a PremIdx carries no variable).  Vars in this
        // set are kept; all others are freshened.
        // ---------------------------------------------------------------
        let keep_vars = frees(&(*live_node, fa_live.clone()));
        // HS `_applySource` (Sources.hs:344-350) runs `someInst sysTh0` in
        // the LIVE Reduction monad — the imports draw from the step's ONE
        // threaded FreshT counter, sequentially after whatever the step
        // already minted.  Drawing from a separately re-seeded allocator
        // instead can hand out idxs the step counter also mints; two
        // independently minted rule instances sharing (name,sort,idx) then
        // get IDENTIFIED at node-merge.
        let red_m = red_maude
            .expect("refine_source_case someInst path requires the live Reduction's counter");
        // HS FreshT-threading: rewind to the pick-time fork base so THIS
        // branch's someInst starts where HS's DisjT-forked branch does
        // (see `fork_base` param doc).  Without the rewind, sibling
        // (case × arm) branches thread each other's import draws: on
        // csf18-xor/CH07's KU(lh(...)) pick, HS runs c_lh 4→5 and tag1
        // 4→18 (TAM_HS_TRACE_APPLY_SRC freshBefore=4 for BOTH), while RS
        // ran c_lh 4→5 then tag1 5→19 — every tag1-branch var +1, which
        // the eq-store witness mints (avoid-set-derived) then compound
        // into the growing ∃-witness drift on the web proof pages.
        if let Some(fb) = fork_base {
            red_m.reset_counter_to(fb);
        }
        let freshened_case = some_inst_system(&refined_case, &keep_vars, red_m);
        let branch_counter = red_m.fresh_counter_peek();

        // The live action fact an Action goal's caller drives: the KU
        // action at `live_node` in the freshened case (the abstract node
        // was substituted to live_node by Step A.3's subst_system).  If
        // not present (e.g. node-id subst didn't propagate), fall back to
        // any KU action in the case — `conjoin_system`'s setNodes will
        // merge it onto the right node.  A case with no KU action at all
        // cannot serve an Action goal, so the arm drops.
        let live_action = match kind {
            SourceGoalKind::Action => {
                let found = freshened_case
                    .nodes
                    .iter()
                    .find(|(id, _)| id == live_node)
                    .and_then(|(_, r)| {
                        r.actions
                            .iter()
                            .find(|a| a.tag == crate::fact::FactTag::Ku)
                            .cloned()
                    })
                    .or_else(|| {
                        freshened_case.nodes.iter().find_map(|(_, r)| {
                            r.actions
                                .iter()
                                .find(|a| a.tag == crate::fact::FactTag::Ku)
                                .cloned()
                        })
                    });
                match found {
                    Some(la) => Some(la),
                    None => continue,
                }
            }
            SourceGoalKind::Premise => None,
        };

        // HS-faithful split: STOP here (BEFORE conjoinSystem).  The caller
        // dedups these arms (`removeRedundantCases`, Sources.hs:236-260) and
        // calls `conjoin_refine_arm` only on survivors, so the expensive
        // bilinear `conjoinSystem` re-narrow is never paid for a case HS
        // drops.
        out_arms.push(RefineArm {
            freshened_case,
            live_action,
            refined_case_for_dedup,
            branch_counter,
        });
    } // end `for arm_eq_store in arm_eq_stores`
    out_arms
}

/// HS-faithful conjoin half of `applySource` (`_applySource`,
/// Sources.hs:344-350) for a single surviving `RefineArm`: runs
/// `markGoalAsSolved` + `conjoinSystem` + the conjoin-fanout drain +
/// E.5 edge fact-eq propagation + close-trivial-chains, returning one
/// [`ConjoinedArm`] per output arm.  Called only on cases that survived
/// `removeRedundantCases`.  The caller resets the live counter to
/// `arm.branch_counter` first: HS's conjoinSystem runs inside the same
/// DisjT-forked branch as the someInst (Sources.hs:348-349), NOT after
/// the sibling branches' conjoins.
fn conjoin_refine_arm(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    arm: RefineArm,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
) -> Vec<ConjoinedArm> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{Reduction, SolveOutcome, SplitStrategy};

    let (kind, live_node) = match live_goal {
        Goal::Action(n, _) => (SourceGoalKind::Action, n),
        Goal::Premise((n, _), _) => (SourceGoalKind::Premise, n),
        _ => {
            return Vec::new();
        }
    };

    // `branch_counter` was consumed by the caller (its per-branch
    // `reset_counter_to` before this call).
    let RefineArm {
        freshened_case,
        live_action,
        refined_case_for_dedup: _,
        branch_counter: _,
    } = arm;

    // Every output arm is its own DisjT branch in HS, so each carries its
    // own thread position in `ConjoinedArm::cont`; the caller hands it to
    // the adopting caller's per-case `new_inheriting`.
    let mut out_arms: Vec<ConjoinedArm> = Vec::new();

    // ---------------------------------------------------------------
    // B — `markGoalAsSolved "precomputed" goal`.
    // E — `conjoinSystem sysTh`.
    // HS runs conjoinSystem in the SAME live Reduction (`_applySource`,
    // Sources.hs:344-350) — share the step's threaded counter.
    // ---------------------------------------------------------------
    let mut r = Reduction::new(ctx, live_sys.clone());
    if let Some(m) = red_maude {
        r.maude = m.clone();
    }
    // HS-faithful (Sources.hs:196-216): `solveAllSafeGoals.safeGoal`
    // returns `not (isKUFact fa)` for ActionG (Sources.hs:144-225, see line 202), so
    // HS's saturate-time precompute NEVER picks a KU action goal
    // and therefore never calls `applySource` on one (Sources.hs
    // `markGoalAsSolved "precomputed" goal`).  Any precompute-time
    // resolution of a KU goal in HS happens only through chain
    // closure / N5_u merging / N6 ordering — none of which mark
    // the KU ActionG goal as solved in the case sub-system.
    //
    // RS reaches this site during saturate via the chain-fold path
    // (`refine_one_source` → ... → `solve_with_source_cases_action_with_ctx`
    // → `conjoin_refine_arm`).  Marking an Action live_goal as
    // solved during saturate produces case sub-systems with
    // pre-solved KU(...) ActionG goals; `conjoin_system`'s
    // `combineGoalStatus` (Reduction.hs:510-511 `solved1 || solved2`)
    // then stamps solved=true on the live system's KU goals — the
    // runtime `case c_S` (or equivalent constructor) proof step HS
    // emits never fires because the goal is no longer "open".
    // Concrete manifestation: Yubikey's Login_reachable skipped
    // two `case c_S` steps (`... → BuyANewYubikey → c_S → c_S → SOLVED`
    // in HS, `... → BuyANewYubikey → SOLVED` in RS).
    //
    // Gate the Action mark on `!in_precompute_mode()` so saturate-time
    // grafts emit a sub-system whose ActionG goals match HS's
    // safe-goal-only saturation outputs.
    let mark_solved = match kind {
        SourceGoalKind::Action => !in_precompute_mode(),
        SourceGoalKind::Premise => true,
    };
    if let Some(slot) = r.sys.goals_mut().iter_mut().find(|(g, _)| g == live_goal) {
        if mark_solved {
            slot.1.solved = true;
        }
    }
    let res = r.conjoin_system(&freshened_case);
    if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
        return out_arms;
    }

    // Drain `conjoin_system`'s step-12 fanout (HS Reduction.hs:721-740, see line 736
    // `solveSubstEqs SplitNow` inside DisjT).  arm[0] is in r.sys;
    // arms[1..] are post-substSystem snapshots in
    // `pending_conjoin_arm_systems`.  We replay the rest of
    // `_applySource` (E.5 edge_eqs, F close_trivial_chains, output
    // push) per stashed sys.  HS-equivalent: each `DisjT` arm
    // continues independently through the post-`solveSubstEqs`
    // continuation.  The Premise path continues arm[0] only.
    let conjoin_arm_systems = match kind {
        SourceGoalKind::Action => std::mem::take(&mut r.pending_conjoin_arm_systems),
        SourceGoalKind::Premise => Vec::new(),
    };
    // Build a Vec<Reduction> over arm0 + extra-arms so the post-conjoin
    // work loop runs uniformly.  arm0 is the in-place `r` (its `maude`
    // is the LIVE handle when `red_maude` is present); arms[1..] each
    // get a Reduction that CONTINUES the arm's recorded step-12
    // counter thread (HS FreshT-threading, task #23 A(ii): each
    // solveSubstEqs arm is a DisjT fork BELOW FreshT — rebuilding from
    // `Reduction::new`'s bounds_max seed rewound past this branch's
    // someInst/conjoin transient draws, so the arm's E.5/close-chains
    // witness mints landed below HS's).
    let mut arm_reductions: Vec<Reduction> = Vec::with_capacity(1 + conjoin_arm_systems.len());
    arm_reductions.push(r);
    for (sys_i, cont_i) in conjoin_arm_systems {
        arm_reductions.push(Reduction::new_inheriting(ctx, sys_i, cont_i));
    }

    // E.5 — edge fact-equality propagation (see per-arm comment below).
    // `live_node_ids` depends only on `live_sys` (an immutable param,
    // invariant across arms), so build it ONCE here instead of cloning
    // every node id on each arm iteration.
    let live_node_ids = collect_node_ids(live_sys);

    for mut r in arm_reductions {
        // ---------------------------------------------------------------
        // E.5 — edge fact-equality propagation.  After conjoin, walk every
        // edge in the joined system and ensure its conclusion fact and
        // premise fact are unified.  Mirrors Haskell's runtime
        // `insertEdges` (Reduction.hs:278-280), which calls `solveFactEqs`
        // on every new edge so producer-conclusion ⇆ consumer-premise terms
        // unify before downstream `insertImpliedFormulas` runs.  Here the
        // source case's edges arrive via `conjoin_system`, which copies
        // them (`joinSets sEdges`) without running solveFactEqs, so this
        // step re-fires fact-equality on them.
        //
        // Without this, a Serv_1 source-case grafted alongside an existing
        // Register_pk produces a second Register_pk whose `$A` is at a
        // different LVar than the lemma-chain Register_pk's `$A`; the two
        // `!Ltk`/`!Pk` chains never coalesce, and the lemma's universal
        // `∀a. AnswerRequest($S, ~k) @ a ⇒ ⊥` matcher fails.  On the
        // Premise side, Minimal_HashChain::Success_charn case
        // Gen_Stop_case_1 installs an `!Final(kZero)` ←→ `!Final(kOrig)`
        // edge but never unifies kZero ⇆ kOrig, so the IH guard
        // `ChainKey(kOrig)` can't match the Gen_Stop node's
        // `ChainKey(kZero)` action and gfalse never enters sFormulas.
        //
        // SCOPING (HS-faithful): HS's `conjoinSystem` (Reduction.hs:660-690)
        // performs NO edge fact-equality solve at all — `joinSets sEdges`
        // (Reduction.hs:672-701, see line 679) unions the edge SET and relies on the saturated
        // case being edge-consistent.  This E.5 step is an RS-only compensation
        // for saturate output that isn't fully edge-consistent.  It MUST only
        // touch edges INTRODUCED by the grafted case — re-solving a
        // pre-existing LIVE edge re-narrows the live equation store and can
        // collapse live disjunctions HS keeps (Joux_EphkRev: re-solving the
        // live em-exponent Kd-pair chain edge folded the `splitEqs(3)/(4)`
        // disjunctions, turning HS's Split×3/×4 cascade into RS's Split×1;
        // on alethea selectionphase the Premise twin PINNED the witness
        // BB_2/AgSt_BB2 multiset code ('1') on the live `vr.5 → vr.11` edge
        // before the `#a3` AgSt_A3 node-merge fired, turning HS's 2-unifier
        // SplitLater merge into RS's pinned 1-unifier APPLY).
        // A grafted edge is one with at least one endpoint NOT a pre-existing
        // live node.  `live_node_ids` is computed once above the loop.
        let edge_eqs = grafted_edge_eqs(&r.sys, &live_node_ids);
        // The Action arm solves the grafted edges with `SplitNow`, whose
        // `solve_fact_eqs` may return `Cases(arms)` when the edge-fact
        // unification yields multiple AC unifier arms (HS `solveFactEqs
        // SplitNow` → `solveTermEqs SplitNow` → `disjunctionOfList $
        // performSplit eqs2 splitId` forks the `Reduction`/`DisjT`
        // continuation, Reduction.hs:712-733; `performSplit` use at
        // 723-725).  Each arm continues the rest of `_applySource`
        // (F close_trivial_chains + output push) independently.  Each arm's
        // eq-store (from `perform_split`) PRESERVES the live system's other
        // disjunctions — `solve_term_eqs`'s `Cases` branch does NOT
        // reinstall `self.sys.eq_store` (it leaves the default store that
        // `System::take_eq_store` swapped in — reduction.rs's Cases arm), so the
        // caller MUST install an arm or the live `splitEqs` disjunctions
        // are silently dropped (would collapse Joux_EphkRev's cascade).
        //
        // The Premise arm solves them with `SplitLater`, mirroring HS's
        // deferral: `_applySource` -> `conjoinSystem` (Sources.hs:344-350,
        // Reduction.hs:672-700) never fact-solves grafted edges;
        // producer<->consumer AC ambiguity surfaces via node merges as
        // `solveRuleEqs SplitLater` (Reduction.hs:772-777, see line 775) — a DEFERRED eq-store
        // disjunction plus a pending `splitEqs(N)` goal, live vars left
        // uninstantiated.  E.5's alignment job (Minimal_HashChain kZero<->kOrig,
        // TESLA variant drop) is single-unifier, which SplitLater still
        // composes immediately.  SplitNow there eagerly fanned multi-unifier
        // arms into proof cases and let simp collapse the merge-derived
        // splits — on alethea_selectionphase_malS establishedIK this pinned
        // y2 |-> h(<'H1',x.1>) and dropped the splitEqs(5..8) HS keeps
        // pending (web task #22).
        //
        // Each E.5 output arm carries its continuation counter (HS
        // FreshT-threading, task #23 A(ii)): the branch thread up to and
        // including this arm's E.5 solve + substSystem draws.  The
        // close-chains/output continuation below resumes from it instead
        // of a detached `bounds_max` seed.
        let mut e5_arm_systems: Vec<(System, u64)> = Vec::new();
        if !edge_eqs.is_empty() {
            let split = match kind {
                SourceGoalKind::Action => SplitStrategy::SplitNow,
                SourceGoalKind::Premise => SplitStrategy::SplitLater,
            };
            let res = r.solve_fact_eqs(split, &edge_eqs);
            match res {
                Err(_) | Ok(SolveOutcome::Contradictory) => {
                    continue;
                }
                Ok(SolveOutcome::Cases(arms)) if matches!(kind, SourceGoalKind::Action) => {
                    // Multi-arm fanout: `solve_term_eqs` returned the arms
                    // WITHOUT installing any into `r.sys`.  Install each arm
                    // into a clone of the pre-solve `r.sys`, run substSystem,
                    // and continue the rest of `_applySource` per arm — each
                    // arm continuing the counter from the E.5 fan-out point
                    // (post-solve across-arm high water; see
                    // `fork_arm_reduction`).
                    let template = r.sys.clone();
                    subst_arms_into(
                        ctx,
                        &template,
                        arms,
                        r.maude.fresh_counter_peek(),
                        &mut e5_arm_systems,
                    );
                    if e5_arm_systems.is_empty() {
                        continue;
                    }
                }
                // Single arm: `solve_term_eqs` already installed it into
                // `r.sys.eq_store`.  `SplitLater` never returns `Cases`
                // (reduction.rs installs the combined store + SplitG goal
                // and returns Linear); its arm lands here too, for
                // type-completeness.
                Ok(_) => {
                    r.subst_system();
                    e5_arm_systems.push((r.sys.clone(), r.maude.fresh_counter_peek()));
                }
            }
        } else {
            e5_arm_systems.push((r.sys.clone(), r.maude.fresh_counter_peek()));
        }

        for (r_sys, e5_cont) in e5_arm_systems {
            // HS FreshT-threading (task #23, A(ii)): continue the branch's
            // counter thread through close_trivial_chains_in_graft.  Its
            // `solve_fact_eqs` draws (add_eqs witness freshening + eq-store
            // simp folds) are the RS-eager equivalent of unifications HS
            // carries INSIDE the stored case (precompute chain closure /
            // chainToEquality at the next simplify) — HS mints those vars on
            // the live branch thread (someInst import or post-solve simplify),
            // so a detached `Reduction::new` here both numbered them at
            // `bounds_max` scale (below HS) and dropped them from the output
            // arm's continuation counter — the UM_three_pass-family −4/−8/−16
            // proof-page undershoot that grows with depth.
            let mut r = Reduction::new_inheriting(ctx, r_sys, e5_cont);

            // ---------------------------------------------------------------
            // F — Close trivial chains via direct-edge unification.
            //
            // Haskell's precompute `solveAllSafeGoals` closes chains during
            // source-case saturation, so the case_sys merged here already has
            // chain edges (in `sEdges`) and their term equations (in
            // `sSubst`).  Our `close_chains_dfs` defers msg-var KD chains
            // (per the openGoals filter), so they remain as `Goal::Chain` in
            // the precomputed case.  After `refineSubst` substitutes the
            // abstract source pattern var with a concrete (e.g. Fresh-sorted)
            // live term, those chains become closeable via direct edge.  Run
            // that closure here so callers don't have to take an explicit
            // `case irecv` step (which Haskell never does).
            //
            // Conservative: only try Branch 1 (direct edge) — never extend
            // via destructor.  If Branch 1 fails or splits, leave the chain
            // as-is.
            close_trivial_chains_in_graft(&mut r);

            // (No RS-only empty-subst `apply_eq_store` variant re-filter here: HS has
            // none; the conflicting-variant drop is edge-driven via `solveFactEqs`
            // (E.5), which RS mirrors. A second re-key here collapsed distinct
            // witnesses and rotated split ordering — verify_checksign_test::test4/5.)

            // HS-faithful action reconciliation.  HS's `_applySource`
            // (Sources.hs:344-350) reconciles the case's KU-action fact with the
            // live goal ENTIRELY inside `conjoinSystem`'s node-merge — there is NO
            // separate `solveFactEqs [caseAction = goal]` step.  RS's `conjoinSystem`
            // (`r.conjoin_system` above) likewise already reconciled the grafted
            // action node to the live goal fact (its em-agent / DH-exponent vars now
            // carry the LIVE goal's `$A`/`~ex`, not the `someInst`-freshened
            // `$A.12`/`~ex.24`).  The caller (reduction.rs `solve_action_goal`
            // None-branch) then runs `solve_fact_eqs([case_action = fa])` to
            // propagate action bindings before its chain-edge solve.  If we hand it
            // the STALE pre-conjoin `live_action` (`$A.12`), that unify is
            // NON-trivial against `fa` (`$A`) even though the grafted system already
            // carries `$A` — so `add_eqs` re-freshens the live eqStore `conj` a
            // SECOND time (HS re-freshes exactly once, inside conjoinSystem),
            // bumping every DH-variant witness one notch (RYY_PFS
            // Reveal_ltk_case_1: RS `~ex`/`x` = HS +1/+2).  Recover the POST-conjoin
            // action from `r.sys` at the live node instead — when conjoin fully
            // reconciled it (`== fa`) the caller's pass is a no-op (no extra
            // re-fresh); when conjoin left a live var to bind (e.g.
            // Reveal_session_key's `z`), the pass still binds exactly that, matching
            // HS's single reconciliation.
            let post_conjoin_action = live_action.as_ref().map(|la| {
                r.sys
                    .nodes
                    .iter()
                    .find(|(id, _)| id == live_node)
                    .and_then(|(_, ru)| {
                        ru.actions
                            .iter()
                            .find(|a| a.tag == crate::fact::FactTag::Ku)
                            .cloned()
                    })
                    .unwrap_or_else(|| la.clone())
            });
            // Per-output-arm continuation counter: the branch thread including
            // this arm's close-chains draws (HS FreshT-threading, task #23
            // A(ii)) — consumed by the adopting caller's per-case
            // `reset_counter_to` / `last_case_counters`.
            let cont = r.maude.fresh_counter_peek();
            out_arms.push(ConjoinedArm {
                sys: r.sys,
                live_action: post_conjoin_action,
                cont,
            });
        } // end `for (r_sys, e5_cont) in e5_arm_systems`
    } // end `for r in arm_reductions`
    out_arms
}

/// True when `t` is a Msg-sorted free variable.  Used by
/// `close_trivial_chains_in_graft` to match Haskell's
/// `chainToEquality` filter on msg-var KD chains.
fn is_msg_var_for_chain_filter(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg)
}

/// Walk open `Goal::Chain` goals in `r.sys` and close each via the
/// direct-edge branch of `solve_chain_goal` when the endpoints' fact
/// tags + arity match (no destructor extension).  Mirrors the
/// post-saturate state Haskell's precompute produces for source cases.
/// Stops on the first chain where direct-edge unification fails or
/// is contradictory — the chain stays as a `Goal::Chain` and gets
/// handled at search time.
fn close_trivial_chains_in_graft(r: &mut crate::constraint::solver::reduction::Reduction) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{SolveOutcome, SplitStrategy};

    loop {
        // Find one open Chain goal whose endpoints are tag+arity
        // compatible AND not a forbidden edge.  Snapshot the goal so
        // we can release the borrow on `r.sys` before mutating.
        //
        // The `is_open_for_saturate_with` always-before relation depends only
        // on `r.sys`, which is unmutated across this single `find_map` scan, so
        // build it once here and thread it into the closure.
        // REBUILD per outer-loop iteration: `add_edge` below mutates `r.sys`,
        // changing the relation for the next iteration's scan. (The owned
        // `PrebuiltAdj` holds no borrow of `r.sys`, so it does not block the
        // `add_edge` mutation.)
        let sat_adj = r.sys.build_always_before_adj();
        let candidate: Option<(
            crate::constraint::constraints::NodeConc,
            crate::constraint::constraints::NodePrem,
            crate::fact::LNFact,
            crate::fact::LNFact,
        )> = r.sys.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping {
                return None;
            }
            let Goal::Chain(c, p) = g else { return None };
            let c_rule = r
                .sys
                .nodes
                .iter()
                .find(|(id, _)| id == &c.0)
                .map(|(_, ru)| ru)?;
            let p_rule = r
                .sys
                .nodes
                .iter()
                .find(|(id, _)| id == &p.0)
                .map(|(_, ru)| ru)?;
            let fa_conc = c_rule.conclusions.get(c.1 .0)?.clone();
            let fa_prem = p_rule.premises.get(p.1 .0)?.clone();
            if fa_conc.tag != fa_prem.tag || fa_conc.terms.len() != fa_prem.terms.len() {
                return None;
            }
            // Haskell-faithful: msg-var KD chains are auto-handled via
            // `chainToEquality` (Goals.hs:92-100) — they're filtered
            // OUT of `openGoals` and `solveAllSafeGoals` doesn't close
            // them.  Mirroring that here prevents over-eager closure
            // that breaks SplitG resolution downstream (NSPK3/NSLPK3
            // R_1 + I_2 case regressions).
            if fa_conc.tag == crate::fact::FactTag::Kd {
                if let Some(t) = fa_conc.terms.first() {
                    if is_msg_var_for_chain_filter(t) {
                        return None;
                    }
                }
            }
            // HS-faithful: never auto-close a chain that `openChainGoals`
            // (Goals.hs:99-108) keeps as an OPEN ranked goal.  A DnK
            // chain whose conclusion is NOT a Msg-sorted variable (a
            // concrete app OR a Fresh/Pub/Nat name) is ALWAYS open in HS
            // (`otherwise -> not solved`); HS solves it via the explicit
            // `solveChain` proof method, never via an eager graft-time
            // direct edge.  RS's over-eager closure here dropped the
            // deconstruction chain `(#vl,0)~~>(#vk,0)` (conc KD(~x),
            // Fresh-sorted) during the RFID_Simple `!KU(aenc)` Alice
            // graft, where HS keeps it open and renders it as
            // `solve( (#vl,0)~~>(#vk,0) ) case Var_fresh_1_x`.  Gate on
            // the canonical `openGoals` mirror so RS leaves open exactly
            // what HS leaves open; only chains HS itself auto-handles
            // (union-all-known) remain eligible for direct-edge closure.
            if crate::constraint::solver::goals::is_open_for_saturate_with(
                &Goal::Chain(*c, *p),
                &r.sys,
                &sat_adj,
            ) {
                return None;
            }
            Some((*c, *p, fa_conc, fa_prem))
        });
        let Some((c, p, fa_conc, fa_prem)) = candidate else {
            break;
        };

        // Snapshot system; if direct-edge unification contradicts,
        // restore and stop trying.
        let snapshot = r.sys.clone();
        r.sys
            .add_edge(crate::constraint::constraints::Edge { src: c, tgt: p });
        let res = r.solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal {
                lhs: fa_conc,
                rhs: fa_prem,
            }],
        );
        match res {
            Err(_) | Ok(SolveOutcome::Contradictory) | Ok(SolveOutcome::Cases(_)) => {
                // Direct-edge closure not possible, OR it SPLIT into
                // multiple AC arms.  On the `Cases` path `solve_term_eqs`
                // does NOT reinstall the eq-store (it leaves the
                // `mem::take`'d default), so continuing would corrupt the
                // system with a wiped store; and this function's contract
                // is explicitly "if Branch 1 fails or splits, leave the
                // chain as-is".  Restore the snapshot and bail — the chain
                // stays open for the search layer (Branch 2 destructor or
                // Disj-case).
                r.sys = snapshot;
                break;
            }
            Ok(SolveOutcome::Linear(_)) => {
                // Single arm: `solve_term_eqs` installed it.  Mark the
                // chain solved.
                let chain_goal = Goal::Chain(c, p);
                if let Some(slot) = r.sys.goals_mut().iter_mut().find(|(g, _)| g == &chain_goal) {
                    slot.1.solved = true;
                }
                // Continue — additional chains may now be closeable
                // after the eq-store propagation.
            }
        }
    }
}

/// Graft a precomputed Action-source case into `live_sys`, mapping
/// the case's `abstract_node` (which produces the KU action) to the
/// live goal's `live_node`.  Unlike a premise-source graft, no premise
/// edge needs bridging — the action node *is* the consumer.
// dedup membership set over subst vars; .contains only, never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn graft_case_into_action(
    live_sys: &System,
    case_sys: &System,
    abstract_node: &crate::constraint::constraints::NodeId,
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
) -> Option<System> {
    let mut out = live_sys.clone();
    let rename_node = |n: &crate::constraint::constraints::NodeId| {
        if n == abstract_node {
            *live_node
        } else {
            *n
        }
    };
    for (id, rule) in case_sys.nodes.iter() {
        let new_id = rename_node(id);
        if !out.nodes.iter().any(|(n, _)| n == &new_id) {
            out.add_node(new_id, rule.clone());
        }
    }
    for e in &case_sys.edges {
        let new_src_node = rename_node(&e.src.0);
        let new_tgt_node = rename_node(&e.tgt.0);
        out.add_edge(crate::constraint::constraints::Edge {
            src: (new_src_node, e.src.1),
            tgt: (new_tgt_node, e.tgt.1),
        });
    }
    for l in &case_sys.less_atoms {
        out.add_less(crate::constraint::constraints::LessAtom::new(
            rename_node(&l.smaller),
            rename_node(&l.larger),
            l.reason,
        ));
    }
    // Mirrors Haskell `conjoinSystem`: preserve goal status when merging.
    // The case's pre-solved goals must stay marked solved in the live
    // system, or downstream
    // search re-picks them as `case Register_pk` for already-resolved
    // premises (the KAS2_eCK case_1.Resp_2 divergence).
    for (g, st) in case_sys.goals.iter() {
        let renamed_goal = match g {
            crate::constraint::constraints::Goal::Action(n, _fa) if n == abstract_node => continue,
            crate::constraint::constraints::Goal::Action(n, fa) => {
                crate::constraint::constraints::Goal::Action(rename_node(n), fa.clone())
            }
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                crate::constraint::constraints::Goal::Premise((rename_node(&p.0), p.1), fa.clone())
            }
            other => other.clone(),
        };
        if !out
            .goals
            .iter()
            .any(|(existing, _)| existing == &renamed_goal)
        {
            // Keep the full max cache exact across the graft: the case's
            // goals carry freshly-shifted (high) idxs the live cache has
            // not seen (mirrors `add_goal_with_loop_flag`'s bump).
            out.bump_cache_goal(&renamed_goal);
            out.goals_mut().push((renamed_goal, st.clone()));
        }
    }
    let live_goal = crate::constraint::constraints::Goal::Action(*live_node, fa_live.clone());
    if let Some(slot) = out.goals_mut().iter_mut().find(|(g, _)| g == &live_goal) {
        // HS-faithful: see the matching gate in `conjoin_refine_arm`.
        // `solveAllSafeGoals.safeGoal` (Sources.hs:144-225, see line 202) excludes KU
        // ActionG goals from saturate-time dispatch, so applying a
        // source-case for a KU goal during saturate must not mark
        // the live goal as solved — otherwise the case sub-system
        // carries pre-solved KU(...) ActionG goals into the live
        // system via `conjoin_system`'s `combineGoalStatus`.
        if !in_precompute_mode() {
            slot.1.solved = true;
        }
    }
    // Merge the case's eq-store substitutions into the live system.
    //
    // CRITICAL for typing refinement: the case carries precompute-
    // time bindings like `x#3 → senc(<chain_sec, chain_pub>, chain_k)`
    // that bind the abstract KU pattern var to the actual senc
    // structure built by the chain.  Without merging these, when
    // `solve_action_goal` later runs `solve_fact_eqs(case_action,
    // fa_live)` to unify the abstract action with the live goal,
    // the equation collapses to `x#3 → senc(<sec#4, ~mw#5>, ~mw#13)`
    // — but the case-INTERNAL chain vars (chain_sec etc.) never get
    // connected to the live vars.  Out_Initiator's terms still
    // reference chain_sec, so `insert_implied_formulas_pass`'s match
    // against `Out_Initiator(senc(<sec#4, ~mw#5>, ~mw#13))` fails, the
    // typing universal doesn't fire, and the typing-violating case
    // survives → false counterexample.
    //
    // With the merge: both bindings are present.  When solve_fact_eqs
    // runs against fa_live, Maude composes them, yielding
    // `chain_sec → sec#4` etc.  subst_system then rewrites
    // Out_Initiator's terms, the universal fires, and the case is
    // pruned via contradiction.
    let mut merged_pairs: Vec<_> = out.eq_store.subst.to_list();
    let existing: std::collections::HashSet<_> = merged_pairs.iter().map(|(v, _)| *v).collect();
    let mut appended_any = false;
    for (lv, lt) in case_sys.eq_store.subst.to_list() {
        let new_lv = if &lv == abstract_node { *live_node } else { lv };
        if !existing.contains(&new_lv) {
            appended_any = true;
            merged_pairs.push((new_lv, lt));
        }
    }
    if appended_any {
        // The appended case bindings (dom var + range term) join the
        // `bounds_max` domain with freshly-shifted idxs the live cache
        // has not seen — drop the stale-LOW full max.
        out.invalidate_max_var_idx_cache();
    }
    out.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(merged_pairs);
    Some(out)
}

// =============================================================================
// removeRedundantCases — HS Sources.hs
// =============================================================================
//
// Direct port of:
//
//   removeRedundantCases :: ProofContext -> [LVar] -> (a -> System) ->  [a] -> [a]
//   removeRedundantCases ctxt stableVars getSys cases0 =
//       if enableBP msig || enableMSet msig then cases else cases0
//     where
//       decoratedCases = map (second addNormSys) $  zip [(0::Int)..] cases0
//       cases = map (fst . snd) . sortOn fst
//             . sortednubBy (\(_,(_, x)) (_,(_, y)) -> compareSystemsUpToNewVars x y)
//             $ decoratedCases
//       addNormSys = id &&&
//         ((modify sEqStore dropNameHintsBound) . renameDropNameHints . getSys)
//       orderedVars sys =
//           filter ((/= LSortNode) . lvarSort) $ map fst . sortOn snd . varOccurences $ sys
//       renameDropNameHints sys =
//         (`evalFresh` avoid stableVars) . (`evalBindT` stableVarBindings) $ do
//             _ <- renameDropNamehint (orderedVars sys)
//             renameDropNamehint sys
//         where stableVarBindings = M.fromList (map (\v -> (v, v)) stableVars)
//
// Where:
//   varOccurences sys: walks `_sNodes` ONLY (System's foldFreesOcc
//     commented out everything except field a). Produces
//     [(LVar, Set Occurence)] where Occurence = [String].
//   renameDropNamehint: assigns each LVar a fresh idx with name "".
//   compareSystemsUpToNewVars: compareNodesUpToNewVars first; if EQ
//     fall through to structural compare on (b..m, empty nodes).
//   compareRulesUpToNewVars: ignores `_rNewVars`.
//   dropNameHintsBound: drops name hints in `eqStore.conj` VFresh substs.
//
// Implementation strategy (per HS):
//   1. Gate on BP/MSet — non-BP/MSet returns cases0 as-is.
//   2. For each case build a canonical key from the normalised system.
//      The normalisation walks free vars in HS-determined order
//      (varOccurences-ordered first, then foldFrees), assigning each a
//      fresh idx with empty name. Then keys excluding rule.new_vars
//      capture exactly what `compareSystemsUpToNewVars` compares.
//   3. Run a verbatim port of HS `sortednubBy` (`sortednub_by`) over the
//      index-decorated list, comparing on the canonical key, then
//      `sortOn fst` to restore original-index order (matches `sortOn fst`
//      in HS).  NOTE: `sortednubBy` does NOT keep the first element of an
//      EQ-group — its run-detection phase (`sequences`) does
//      `EQ -> sequences xs`, dropping the earlier element and keeping the
//      LATER one; the `merge` phase drops the right-list element on EQ.
//      Since every EQ-group member has an identical key and `sortOn fst`
//      washes out cross-group order, the observable effect is "keep the
//      highest-original-index member of each equal-key group".  (A
//      first-wins dedup — e.g. via `BTreeSet` — would be unfaithful: it
//      flips the surviving representative on symmetric AC peers, e.g.
//      Joux/Scott `Session_Key_Secrecy_PFS`'s B↔C mirror.)

/// One segment of an occurrence path (HS's `[String]` context under
/// `foldFreesOcc`).  A path is materialised once per variable occurrence, so a
/// rendered segment is held behind an `Rc` and cloned as a pointer: a rule's
/// segment is the whole `{:?}` of its info, which on a SAPIC theory carries
/// the rule's process.  `Ord` and `Eq` read the segment's text, so paths order
/// by their text.
#[derive(Clone)]
enum Seg {
    Static(&'static str),
    Shared(std::rc::Rc<str>),
}

impl Seg {
    fn shared(s: &str) -> Self {
        Seg::Shared(std::rc::Rc::from(s))
    }

    fn as_str(&self) -> &str {
        match self {
            Seg::Static(s) => s,
            Seg::Shared(s) => s,
        }
    }
}

impl PartialEq for Seg {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Seg {}

impl PartialOrd for Seg {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Seg {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

/// Walk the free LVars of `sys.nodes` in HS `foldFreesOcc` order
/// (`HS instance HasFrees System`: only field `a` is walked; commented
/// out for `b..m`).  Produces a list of `(LVar, BTreeSet<Vec<Seg>>)`
/// where the inner set is the set of occurrence-context paths each
/// var appears in.  Mirrors `varOccurences`
/// (`lib/term/src/Term/LTerm.hs:622-625, see line 625`).
///
/// HS context format (per HasFrees-instance tree under `foldFreesOcc`):
///   - Map (NodeId, RuleACInst):  context = same `p` for both k and v
///     (`foldFreesOcc f p = M.foldrWithKey combine` calling
///     `foldFreesOcc f p (k, v)`).
///   - Tuple `(k, v)`:  k gets "0":p, v gets "1":p.
///   - Rule i ps cs as _nvs:  the three fact lists run under
///     `((show i):c)` as a (ps, cs, as) triple — each gets
///     "0"/"1"/"2":((show i):c).
///   - [a] (Vec):  each element runs under (show i):c.
///   - Fact:  `f for_each_free` runs each term arg; we walk arg list
///     positionally as well.
///   - Term: a Var leaf returns the LVar with the current context.
///
/// We emit `(v, ctx)` pairs and bucket by var. The outer `_sNodes` map
/// walks its (k,v) entries in BTreeMap key order — i.e. NodeId Ord. RS's
/// `sys.nodes` is `Vec<(NodeId, RuleACInst)>`; we sort by NodeId before
/// walking to match HS.
fn var_occurrences_nodes(
    sys: &crate::constraint::system::System,
) -> Vec<(
    tamarin_term::lterm::LVar,
    std::collections::BTreeSet<Vec<Seg>>,
)> {
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    // ctx is HS's [String] occurrence path; head is innermost.
    // We push for each tree-descend, then mutate-and-pop is impractical;
    // we just clone (HS uses persistent list = sharing tail).
    // HS `foldFreesOcc` context string for a function symbol head
    // (`instance HasFrees (Term l)`, LTerm.hs:782-786, see line 784):
    //   FApp (NoEq o) as  ->  push `BC.unpack . fst $ o`  (the bare op name)
    //   FApp o        as  ->  push `show o`               (the FunSym, for AC/C/List)
    // The SAME context is pushed once for the whole arg list — HS does NOT
    // descend per-argument with an index, so every argument of an `FApp`
    // shares the symbol-name context.
    fn funsym_occ_ctx(sym: &tamarin_term::function_symbols::FunSym) -> Seg {
        use tamarin_term::function_symbols::{AcSym, CSym, FunSym};
        match sym {
            FunSym::NoEq(s) => Seg::shared(&String::from_utf8_lossy(s.name)),
            FunSym::Ac(ac) => match ac {
                AcSym::Union => Seg::Static("AC Union"),
                AcSym::Mult => Seg::Static("AC Mult"),
                AcSym::Xor => Seg::Static("AC Xor"),
                AcSym::NatPlus => Seg::Static("AC NatPlus"),
                // Derived HS `Show` of a user-defined AC symbol.
                AcSym::AcFct(s) => Seg::shared(&format!(
                    "AC (ACfct {})",
                    tamarin_term::function_symbols::show_acfct_sym(s)
                )),
            },
            FunSym::C(c) => match c {
                CSym::EMap => Seg::Static("C EMap"),
            },
            FunSym::List => Seg::Static("List"),
        }
    }
    // HS `show (factTag fa)` (derived `Show FactTag`, Theory/Model/Fact.hs:136-149).
    //   ProtoFact mult name arity -> "ProtoFact <mult> \"<name>\" <arity>"
    //   FreshFact/OutFact/InFact/KUFact/KDFact/DedFact/TermFact (nullary)
    fn fact_tag_occ_ctx(f: &crate::fact::LNFact) -> Seg {
        use crate::fact::{FactTag, Multiplicity};
        match &f.tag {
            FactTag::Proto(m, name, arity) => {
                let mstr = match m {
                    Multiplicity::Persistent => "Persistent",
                    Multiplicity::Linear => "Linear",
                };
                Seg::shared(&format!("ProtoFact {} {:?} {}", mstr, name, arity))
            }
            FactTag::Fresh => Seg::Static("FreshFact"),
            FactTag::Out => Seg::Static("OutFact"),
            FactTag::In => Seg::Static("InFact"),
            FactTag::Ku => Seg::Static("KUFact"),
            FactTag::Kd => Seg::Static("KDFact"),
            FactTag::Ded => Seg::Static("DedFact"),
            FactTag::Term => Seg::Static("TermFact"),
        }
    }
    // ctx is a stack-allocated parent-linked chain (HS's persistent
    // `[String]` occurrence path with shared tails): each descend prepends
    // one `seg` and points at its `parent`, so the whole path is shared
    // rather than re-cloned at every node.  We materialize the flat
    // `Vec<Seg>` ONLY at `Var` leaves — the one place the BTreeSet
    // accumulator needs it — so the emitted sets are byte-identical to the
    // eager path while the O(nodes*depth) intermediate clones are gone.
    struct Ctx<'a> {
        seg: Seg,
        parent: Option<&'a Ctx<'a>>,
    }
    impl<'a> Ctx<'a> {
        // Flatten head-first (innermost segment first) — the exact order the
        // eager path produced by prepending each new segment at index 0.
        fn materialize(&self) -> Vec<Seg> {
            let mut v: Vec<Seg> = Vec::new();
            let mut cur: Option<&Ctx> = Some(self);
            while let Some(c) = cur {
                v.push(c.seg.clone());
                cur = c.parent;
            }
            v
        }
    }
    // Small list/arg indices as borrowed static strs, byte-identical to
    // `i.to_string()`, so a descend never allocates for its index segment.
    fn idx_seg(i: usize) -> Seg {
        const T: [&str; 17] = [
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15",
            "16",
        ];
        if i < T.len() {
            Seg::Static(T[i])
        } else {
            Seg::shared(&i.to_string())
        }
    }
    fn visit_term(
        t: &tamarin_term::lterm::LNTerm,
        ctx: &Ctx,
        out: &mut BTreeMap<LVar, BTreeSet<Vec<Seg>>>,
    ) {
        match t {
            Term::Lit(Lit::Var(v)) => {
                out.entry(*v).or_default().insert(ctx.materialize());
            }
            Term::Lit(Lit::Con(_)) => {}
            Term::App(sym, args) => {
                // HS `instance HasFrees (Term l)` `foldFreesOcc`
                // (LTerm.hs:782-786):
                //   FApp (NoEq o) as -> foldFreesOcc f ((opName):c) as
                //   FApp o        as -> mconcat $ map (foldFreesOcc f (show o:c)) as
                //                       -- AC or C symbols
                // For a NoEq function the args are descended as a LIST, so the
                // `HasFrees [a]` instance (LTerm.hs:877-882, see line 880) prefixes EACH arg with
                // its positional index `show i`: arg i's context becomes
                // `[show i, opName, ...c]`.  For AC/C symbols HS maps over the
                // args DIRECTLY (no list instance), so they get only
                // `[show o, ...c]` with NO per-arg index (AC args are unordered
                // anyway).  Omitting the NoEq per-arg index would collapse
                // structurally-distinct vars at different argument positions to the
                // same occurrence-context set, breaking the canonical
                // `renameDropNameHints` ordering so `removeRedundantCases` keeps
                // alpha-equivalent split cases distinct (`split_case_1` vs `split`).
                let sub = Ctx {
                    seg: funsym_occ_ctx(sym),
                    parent: Some(ctx),
                };
                let is_ac_or_c = sym.is_ac() || sym.is_c();
                for (i, a) in args.iter().enumerate() {
                    if is_ac_or_c {
                        // AC/C: no per-arg index (HS maps directly).
                        visit_term(a, &sub, out);
                    } else {
                        // NoEq: prefix the arg index (HS list instance).
                        let arg_ctx = Ctx {
                            seg: idx_seg(i),
                            parent: Some(&sub),
                        };
                        visit_term(a, &arg_ctx, out);
                    }
                }
            }
        }
    }
    // HS `instance HasFrees Fact` (Theory/Model/Fact.hs:189-194, see line 192):
    //   foldFreesOcc f c fa = foldFreesOcc f (show (factTag fa):c) (factTerms fa)
    // i.e. push `show (factTag fa)` then descend into the term LIST, which
    // (via the `[a]` instance) pushes the list index `show i` per term.  So
    // term i's context = [show i, show factTag, ...c] — the factTag
    // layer must be included, not just the term index.
    fn visit_fact(
        f: &crate::fact::LNFact,
        ctx: &Ctx,
        out: &mut BTreeMap<LVar, BTreeSet<Vec<Seg>>>,
    ) {
        let tag_ctx = Ctx {
            seg: fact_tag_occ_ctx(f),
            parent: Some(ctx),
        };
        for (i, t) in f.terms.iter().enumerate() {
            let sub = Ctx {
                seg: idx_seg(i),
                parent: Some(&tag_ctx),
            };
            visit_term(t, &sub, out);
        }
    }
    fn visit_facts(
        fs: &[crate::fact::LNFact],
        ctx: &Ctx,
        out: &mut BTreeMap<LVar, BTreeSet<Vec<Seg>>>,
    ) {
        for (i, f) in fs.iter().enumerate() {
            let sub = Ctx {
                seg: idx_seg(i),
                parent: Some(ctx),
            };
            visit_fact(f, &sub, out);
        }
    }
    // foldFreesOcc Rule:
    //   foldFreesOcc f c (Rule i ps cs as _) =
    //     foldFreesOcc f ((show i):c) (ps, cs, as)
    // tuple (ps, cs, as) walks: ps → "0":c, cs → "1":c, as → "2":c.
    fn visit_rule(
        r: &crate::rule::RuleACInst,
        ctx: &Ctx,
        out: &mut BTreeMap<LVar, BTreeSet<Vec<Seg>>>,
    ) {
        let rule_ctx = Ctx {
            seg: Seg::shared(&format!("{:?}", r.info)),
            parent: Some(ctx),
        };
        // ps
        let ps_ctx = Ctx {
            seg: idx_seg(0),
            parent: Some(&rule_ctx),
        };
        visit_facts(&r.premises, &ps_ctx, out);
        // cs
        let cs_ctx = Ctx {
            seg: idx_seg(1),
            parent: Some(&rule_ctx),
        };
        visit_facts(&r.conclusions, &cs_ctx, out);
        // as
        let as_ctx = Ctx {
            seg: idx_seg(2),
            parent: Some(&rule_ctx),
        };
        visit_facts(&r.actions, &as_ctx, out);
    }
    // M.Map's foldFreesOcc passes the same `p` to each (k, v) tuple, then
    // the tuple instance splits "0":p and "1":p.  We walk in BTreeMap-key
    // order (Ord LVar on NodeId) — HS's M.foldrWithKey iterates ASC.
    let mut nodes_sorted: Vec<&(tamarin_term::lterm::LVar, crate::rule::RuleACInst)> =
        sys.nodes.iter().collect();
    nodes_sorted.sort_by_key(|a| a.0);
    let mut out: BTreeMap<LVar, BTreeSet<Vec<Seg>>> = BTreeMap::new();
    for (nid, rule) in &nodes_sorted {
        // For (k, v) tuple: "0":p for k (NodeId is just an LVar), "1":p for v.
        // base_ctx is empty, so k = ["0"] and the rule root chain = ["1"].
        out.entry(*nid).or_default().insert(vec![Seg::Static("0")]);
        let v_ctx = Ctx {
            seg: Seg::Static("1"),
            parent: None,
        };
        visit_rule(rule, &v_ctx, &mut out);
    }
    out.into_iter().collect()
}

/// Append the base-10 rendering of `v` — byte-identical to
/// `write!(out, "{}", v)` without the `core::fmt` dyn-dispatch machinery
/// (a measurable cost when fired per node/edge/var of every candidate
/// system key).
fn push_u64(out: &mut String, mut v: u64) {
    let mut buf = [0u8; 20];
    let mut i = buf.len();
    loop {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }
    // Digits are pure ASCII, so the validation scan is a trivially-true
    // ~20-byte check.
    out.push_str(std::str::from_utf8(&buf[i..]).expect("ASCII digits"));
}

/// Append the base-10 rendering of a signed value (`SplitId` payload) —
/// byte-identical to `write!(out, "{}", v)`.
fn push_i64(out: &mut String, v: i64) {
    if v < 0 {
        out.push('-');
    }
    push_u64(out, v.unsigned_abs());
}

/// `{:?}` of an `LSort` as a static str (the derived `Debug` prints the
/// bare variant name), avoiding the formatter round-trip per var leaf.
fn lsort_key_str(s: tamarin_term::lterm::LSort) -> &'static str {
    use tamarin_term::lterm::LSort;
    match s {
        LSort::Pub => "Pub",
        LSort::Fresh => "Fresh",
        LSort::Msg => "Msg",
        LSort::Node => "Node",
        LSort::Nat => "Nat",
    }
}

/// `{}` of a bool as a static str.
fn bool_key_str(b: bool) -> &'static str {
    if b {
        "true"
    } else {
        "false"
    }
}

/// The sort of a binder, spelled into the system key as `Debug` spells it,
/// through static strs so the key costs no formatter.
fn push_sort_dbg(out: &mut String, s: tamarin_term::lterm::LSort) {
    use tamarin_term::lterm::LSort;
    out.push_str(match s {
        LSort::Msg => "Msg",
        LSort::Pub => "Pub",
        LSort::Fresh => "Fresh",
        LSort::Node => "Node",
        LSort::Nat => "Nat",
    });
}

/// Append the pre-rendered `scratch` element `ranges` to `out` in sorted
/// byte order, pushing `sep` after each element.  `str` Ord IS byte-wise
/// lexicographic (== `[u8]` Ord) and the sort is stable, so the appended
/// bytes are identical to collecting per-element `String`s, `sort()`ing
/// the `Vec<String>` and joining — while the N per-element allocations
/// collapse into the one shared `scratch` buffer (same shape as the
/// AC-child sort in `write_term_to_key_with`).
fn push_sorted_ranges(out: &mut String, scratch: &str, ranges: &mut [(usize, usize)], sep: char) {
    let bytes = scratch.as_bytes();
    ranges.sort_by(|&(s1, l1), &(s2, l2)| bytes[s1..s1 + l1].cmp(&bytes[s2..s2 + l2]));
    for &(s, l) in ranges.iter() {
        out.push_str(&scratch[s..s + l]);
        out.push(sep);
    }
}

/// `renameDropNameHints sys` (Sources.hs:252-258) as a binding store the
/// `write_*_to_key` serialisers consult, instead of the renamed `System` HS
/// builds:
///   1. `stableVarBindings`: every stable variable binds to itself.
///   2. `evalFresh … (avoid stableVars)`: the supply starts above the largest
///      stable index.
///   3. `renameDropNamehint (orderedVars sys)` imports the non-`Node` variables
///      of `varOccurences sys` in occurrence-set order first.
///   4. `renameDropNamehint sys` imports the rest, in the order
///      `instance HasFrees System` (System.hs:1832-1848) reaches them.
///
/// Every import draws an empty-named index of the variable's own sort
/// (`renameDropNamehint`, LTerm.hs:737-740), so a stable variable keeps its
/// name and every other one loses it.
fn compute_rename_map(
    sys: &crate::constraint::system::System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> Bindings {
    use tamarin_term::lterm::{HasFrees, LSort};
    let mut rename = Bindings::new();
    for v in stable_vars {
        rename.insert(*v, *v);
    }
    let mut fresh_state = tamarin_utils::fresh::FastFreshState::nothing_used();
    if let Some(max) = stable_vars.iter().map(|v| v.idx).max() {
        fresh_state.fresh_idents(max + 1);
    }
    let mut occs = var_occurrences_nodes(sys);
    occs.sort_by(|a, b| a.1.cmp(&b.1));
    for (v, _occs) in &occs {
        if v.sort == LSort::Node {
            continue;
        }
        rename.import_drop_namehint(v, &mut fresh_state);
    }
    sys.for_each_free(&mut |v| {
        rename.import_drop_namehint(v, &mut fresh_state);
    });
    rename
}

/// The binding of `v`, or `v` itself when the store holds none.
fn rn(rename: &Bindings, v: &tamarin_term::lterm::LVar) -> tamarin_term::lterm::LVar {
    rename.get(v).unwrap_or(*v)
}

/// Write a term to the key buffer with renamed vars.
///
/// For AC and C function symbols, child renderings are sorted alphabetically
/// post-rename so that the key is invariant under permutation of AC args
/// (HS's `renameDropNameHints` calls `fAppAC` which re-canonicalizes the
/// term under the renamed-var Ord; our pre-rendered Vec retains the
/// pre-rename order, so we sort the rendered children here to match).
/// Without this, two systems that differ ONLY by which renamed var ends
/// up in which AC slot (e.g. `Union(v4, v5)` vs `Union(v5, v4)` after
/// renaming `B↔C` to `v4↔v5`) get distinct keys and survive
/// `removeRedundantCases`.
/// Shared term-key serializer owning the `App`/`Con` arms (including the
/// AC/C "render children, sort, join" permutation-invariance logic).  The
/// `Var` leaf is delegated to `leaf`, letting callers choose the name-
/// including vs name-dropping rendering; the recursive structure is
/// therefore edited in exactly one place.
fn write_term_to_key_with(
    t: &tamarin_term::lterm::LNTerm,
    out: &mut String,
    leaf: &dyn Fn(&tamarin_term::lterm::LVar, &mut String),
) {
    use std::fmt::Write as _;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => leaf(v, out),
        Term::Lit(Lit::Con(c)) => {
            let _ = write!(out, "{:?}", c);
        }
        Term::App(sym, args) => {
            let _ = write!(out, "{:?}(", sym);
            // For AC/C symbols, sort child renderings (post-rename) to
            // make the key permutation-invariant.  Render each child
            // contiguously into ONE scratch buffer, recording (start,len)
            // ranges, then sort the ranges by byte-slice compare.  `str`
            // Ord IS byte-wise lexicographic (== `[u8]` Ord), and the join
            // is stable, so the comma-joined bytes are byte-identical to
            // sorting a `Vec<String>` of per-child renderings — while the
            // per-child String allocs collapse to one scratch + one range
            // Vec per AC/C node.
            if sym.is_ac() || sym.is_c() {
                let mut scratch = String::new();
                let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(args.len());
                for a in args.iter() {
                    let start = scratch.len();
                    write_term_to_key_with(a, &mut scratch, leaf);
                    ranges.push((start, scratch.len() - start));
                }
                let bytes = scratch.as_bytes();
                ranges.sort_by(|&(s1, l1), &(s2, l2)| bytes[s1..s1 + l1].cmp(&bytes[s2..s2 + l2]));
                for (i, &(s, l)) in ranges.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str(&scratch[s..s + l]);
                }
            } else {
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_term_to_key_with(a, out, leaf);
                }
            }
            out.push(')');
        }
    }
}

fn write_term_to_key(t: &tamarin_term::lterm::LNTerm, rename: &Bindings, out: &mut String) {
    write_term_to_key_with(t, out, &|v, out| {
        let rv = rn(rename, v);
        // Include the var NAME.  HS's `LVar` Ord is (idx, sort, name)
        // and `renameDropNamehint` (Term/LTerm.hs:738-740) renames each
        // DISTINCT `LVar` via `importBinding` (keyed on full identity),
        // giving non-stable vars an EMPTY name but keeping stable vars
        // bound to themselves (`stableVarBindings`, Sources.hs:254-258)
        // with their ORIGINAL name.  Two distinct stable public vars —
        // e.g. `$A.1` and `$B.1` — share (idx=1, sort=Pub) and differ
        // ONLY in name; `compareSystemsUpToNewVars` therefore keeps them
        // apart.  Dropping the name here conflated them, so the two
        // symmetric commutative-`em` source-graft arms
        // (`em(hp($A.1),hp($B.1))` = `em(x,y)` has two Maude matchings)
        // produced byte-identical dedup keys and `removeRedundantCases`
        // collapsed `c_em_case_1`/`c_em_case_2` into one `c_em` on
        // Scott::key_secrecy.  `compute_rename_map` assigns non-stable
        // vars an empty name, so appending it is a no-op for them and
        // only restores HS's stable-var name discrimination.
        // (Manual pushes are byte-identical to the previous
        // `write!(out, "v{}:{:?}:{}", ...)` — see `push_u64`.)
        out.push('v');
        push_u64(out, rv.idx);
        out.push(':');
        out.push_str(lsort_key_str(rv.sort));
        out.push(':');
        out.push_str(rv.name);
    });
}

fn write_fact_to_key(f: &crate::fact::LNFact, rename: &Bindings, out: &mut String) {
    use std::fmt::Write as _;
    let _ = write!(out, "{:?}:{:?}[", f.tag, f.annotations);
    for (i, t) in f.terms.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_term_to_key(t, rename, out);
    }
    out.push(']');
}

fn write_rule_to_key_excl_new_vars(
    r: &crate::rule::RuleACInst,
    rename: &Bindings,
    out: &mut String,
) {
    use std::fmt::Write as _;
    let _ = write!(out, "info={:?};", r.info);
    out.push_str("ps:[");
    for (i, p) in r.premises.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_fact_to_key(p, rename, out);
    }
    out.push_str("];cs:[");
    for (i, c) in r.conclusions.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_fact_to_key(c, rename, out);
    }
    out.push_str("];as:[");
    for (i, a) in r.actions.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_fact_to_key(a, rename, out);
    }
    out.push(']');
    // Crucial: rule.new_vars EXCLUDED per `compareRulesUpToNewVars`.
}

/// Look up the renamed identity of a free variable leaf and write it.
fn write_gfree_var(v: &tamarin_term::lterm::LVar, rename: &Bindings, out: &mut String) {
    let rv = rename.get(v).unwrap_or(*v);
    // Encode the renamed identity (name + idx + sort) of a Free leaf.
    out.push('F');
    out.push_str(rv.name);
    out.push('#');
    push_u64(out, rv.idx);
    out.push(':');
    out.push_str(lsort_key_str(rv.sort));
}

/// Write a locally-nameless term into the key buffer, renaming free leaves in
/// place.
///
/// The argument lists are written POSITIONALLY, including the AC and `C` ones:
/// the key must partition formulas the way the guarded store's own `==` does,
/// and a stored formula's AC list is sorted under the ORIGINAL variables, not
/// the renamed ones.  Re-sorting the rendered children (as
/// [`write_term_to_key_with`] does for a system term, whose HS counterpart
/// really is rebuilt through `fAppAC`) would make the partition coarser and
/// drop cases the port keeps.
///
/// The `App` arm writes the `FunSym`'s full identity, so the encoding is
/// injective over everything the term holds.
fn write_gterm_struct(t: &crate::formula::BLNTerm, rename: &Bindings, out: &mut String) {
    use std::fmt::Write as _;
    use tamarin_term::lterm::BVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(BVar::Free(v))) => write_gfree_var(v, rename, out),
        Term::Lit(Lit::Var(BVar::Bound(n))) => {
            out.push('B');
            push_u64(out, *n);
        }
        Term::Lit(Lit::Con(c)) => {
            let _ = write!(out, "{:?}", c);
        }
        Term::App(sym, args) => {
            let _ = write!(out, "{:?}(", sym);
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_gterm_struct(a, rename, out);
            }
            out.push(')');
        }
    }
}

fn write_gfact_struct(
    f: &crate::fact::Fact<crate::formula::BLNTerm>,
    rename: &Bindings,
    out: &mut String,
) {
    use std::fmt::Write as _;
    // `{:?}` of the `FactTag` writes the multiplicity, the name and the arity;
    // the annotations follow, so the pair is injective over everything the fact
    // holds beside its terms.
    let _ = write!(out, "{:?}:{:?}", f.tag, f.annotations);
    out.push('[');
    for (i, t) in f.terms.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_gterm_struct(t, rename, out);
    }
    out.push(']');
}

fn write_gatom_struct(
    a: &crate::atom::Atom<crate::formula::BLNTerm>,
    rename: &Bindings,
    out: &mut String,
) {
    use crate::atom::ProtoAtom;
    let bin =
        |tag: &str, x: &crate::formula::BLNTerm, y: &crate::formula::BLNTerm, out: &mut String| {
            out.push_str(tag);
            out.push('(');
            write_gterm_struct(x, rename, out);
            out.push(',');
            write_gterm_struct(y, rename, out);
            out.push(')');
        };
    match a {
        ProtoAtom::EqE(x, y) => bin("EQ", x, y, out),
        ProtoAtom::Less(x, y) => bin("LT", x, y, out),
        ProtoAtom::Subterm(x, y) => bin("SUB", x, y, out),
        ProtoAtom::Action(t, f) => {
            out.push_str("ACT(");
            write_gfact_struct(f, rename, out);
            out.push('@');
            write_gterm_struct(t, rename, out);
            out.push(')');
        }
        ProtoAtom::Last(t) => {
            out.push_str("LAST(");
            write_gterm_struct(t, rename, out);
            out.push(')');
        }
        ProtoAtom::Syntactic(_) => out.push_str("SYN"),
    }
}

/// Render a `Guarded` formula into the redundant-case dedup key buffer,
/// applying the free-var alpha-`rename` INLINE.
///
/// PERF/FAITHFULNESS: this is a direct structural serializer — it walks the
/// formula once, renaming free LVar leaves in place and writing a compact
/// structural fingerprint, with NO formula clone and NO `Debug` dispatch.
/// Cloning the formula via `subst_guarded` to apply the rename and then
/// `format!("{:?}", _)`-ing it through the derived `Debug` machinery would be
/// far slower (term clone churn, the generic `Debug` formatter builders, and
/// an intermediate `String` per formula).
///
/// The key BYTES are an arbitrary internal fingerprint:
/// `compute_compare_systems_key` keys never reach `--prove` output and are
/// only ever compared for equality/ordering against other keys from the
/// SAME `removeRedundantCases` call, so ANY injective encoding induces the
/// same equivalence partition.  The `rename` map is a var→var alpha
/// renaming (`compute_rename_map`), and this serializer renames exactly those
/// free vars in place: it never re-sorts an AC argument list, which a
/// `subst_guarded` rebuild through `fApp` would.  Keeping the argument order
/// keeps the partition as fine as the guarded store's own `==`.
fn write_guarded_struct(g: &crate::guarded::Guarded, rename: &Bindings, out: &mut String) {
    use crate::guarded::Guarded;
    match g {
        Guarded::Atom(a) => {
            out.push_str("A{");
            write_gatom_struct(a, rename, out);
            out.push('}');
        }
        Guarded::Disj(items) => {
            out.push_str("OR[");
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    out.push(';');
                }
                write_guarded_struct(it, rename, out);
            }
            out.push(']');
        }
        Guarded::Conj(items) => {
            out.push_str("AND[");
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    out.push(';');
                }
                write_guarded_struct(it, rename, out);
            }
            out.push(']');
        }
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => {
            out.push('G');
            // `{:?}` of `Quantifier` is the bare variant name.
            out.push_str(match qua {
                crate::formula::Quantifier::All => "All",
                crate::formula::Quantifier::Ex => "Ex",
            });
            out.push('(');
            for (i, b) in vars.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&b.0);
                out.push(':');
                push_sort_dbg(out, b.1);
            }
            out.push_str("){");
            for (i, a) in guards.iter().enumerate() {
                if i > 0 {
                    out.push(';');
                }
                write_gatom_struct(a, rename, out);
            }
            out.push_str("}=>");
            write_guarded_struct(body, rename, out);
        }
    }
}

/// Build the canonical key used to identify a system up to alpha-renaming
/// of non-stable vars and modulo rule.new_vars.  Two systems with the
/// same key are considered redundant per HS's `compareSystemsUpToNewVars`
/// + `renameDropNameHints` + `dropNameHintsBound`.
fn compute_compare_systems_key(
    sys: &crate::constraint::system::System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    cap_hint: usize,
) -> String {
    use std::fmt::Write as _;
    let rename = compute_rename_map(sys, stable_vars);
    // Exhaustive destructure of the system's content (no `..`): adding a
    // `SystemContent` field becomes a compile error here until its role in the
    // comparison key is decided (serialise it, or bind it to `_name` with a
    // reason).  Every content field currently participates in the key, so all
    // bindings are used below.  System-level fields not in `SystemContent`
    // (`source_kind`, `side`, `next_goal_nr`) are read via `sys.` and their
    // additions are caught by the exhaustive destructures in
    // `impl Clone`/`impl PartialEq for System`.  `&**sys` derefs `&System` →
    // `&SystemContent`.
    let crate::constraint::system::SystemContent {
        nodes,
        edges,
        less_atoms,
        formulas,
        solved_formulas,
        lemmas,
        last_atom,
        eq_store,
        subterm_store,
        goals,
    } = &**sys;
    // `cap_hint` pre-sizes the key buffer to a sibling case's key length
    // (keys within one `removeRedundantCases` call have similar sizes),
    // avoiding the ~10 doubling reallocs of a growing key.  Reserve is
    // byte-neutral: only the backing capacity changes, never the content.
    let mut out = String::with_capacity(cap_hint);
    // NODES (with renamed ids, excluding rule.new_vars).
    out.push_str("NODES:[");
    let mut nodes_sorted: Vec<&(tamarin_term::lterm::LVar, crate::rule::RuleACInst)> =
        nodes.iter().collect();
    // `sort_by_cached_key` is stable like `sort_by_key` (same order) but
    // pays ONE `rn` lookup + LVar clone per node instead of one per
    // comparison.
    nodes_sorted.sort_by_cached_key(|a| rn(&rename, &a.0));
    for (nid, rule) in &nodes_sorted {
        let rid = rn(&rename, nid);
        out.push_str("{id=");
        push_u64(&mut out, rid.idx);
        out.push(':');
        out.push_str(lsort_key_str(rid.sort));
        out.push(';');
        write_rule_to_key_excl_new_vars(rule, &rename, &mut out);
        out.push_str("};");
    }
    out.push(']');
    // EDGES.  Rendered as `{idx}:{sort:?}.{ConcIdx:?}->{idx}:{sort:?}.{PremIdx:?};`
    // — the `ConcIdx(_)`/`PremIdx(_)` derived-Debug wrappers are pushed as
    // static text around the payload digits.
    out.push_str(";EDGES:[");
    let mut edges_renamed: Vec<(
        tamarin_term::lterm::LVar,
        crate::rule::ConcIdx,
        tamarin_term::lterm::LVar,
        crate::rule::PremIdx,
    )> = edges
        .iter()
        .map(|e| {
            (
                rn(&rename, &e.src.0),
                e.src.1,
                rn(&rename, &e.tgt.0),
                e.tgt.1,
            )
        })
        .collect();
    edges_renamed.sort();
    for (s, si, t, ti) in &edges_renamed {
        push_u64(&mut out, s.idx);
        out.push(':');
        out.push_str(lsort_key_str(s.sort));
        out.push_str(".ConcIdx(");
        push_u64(&mut out, si.0 as u64);
        out.push_str(")->");
        push_u64(&mut out, t.idx);
        out.push(':');
        out.push_str(lsort_key_str(t.sort));
        out.push_str(".PremIdx(");
        push_u64(&mut out, ti.0 as u64);
        out.push_str(");");
    }
    out.push(']');
    // LESS.
    out.push_str(";LESS:[");
    let mut less_renamed: Vec<(
        tamarin_term::lterm::LVar,
        tamarin_term::lterm::LVar,
        crate::constraint::constraints::Reason,
    )> = less_atoms
        .iter()
        .map(|la| (rn(&rename, &la.smaller), rn(&rename, &la.larger), la.reason))
        .collect();
    less_renamed.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    for (s, t, _r) in &less_renamed {
        push_u64(&mut out, s.idx);
        out.push('<');
        push_u64(&mut out, t.idx);
        out.push(';');
    }
    out.push(']');
    // LAST.
    out.push_str(";LAST:");
    if let Some(j) = last_atom {
        let r = rn(&rename, j);
        push_u64(&mut out, r.idx);
    }
    // SUBTERM STORE.
    out.push_str(";STORE:[");
    for st in &subterm_store.subterms {
        write_term_to_key(&st.small, &rename, &mut out);
        out.push_str("<<");
        write_term_to_key(&st.big, &rename, &mut out);
        out.push(';');
    }
    out.push_str("]/SOLVED:[");
    for st in &subterm_store.solved_subterms {
        write_term_to_key(&st.small, &rename, &mut out);
        out.push_str("<<");
        write_term_to_key(&st.big, &rename, &mut out);
        out.push(';');
    }
    out.push(']');
    // EQSTORE.subst (free subst).
    out.push_str(";SUBST:[");
    // Re-key by renamed var, then sort.
    let mut subst_keyed: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = eq_store
        .subst
        .to_list()
        .into_iter()
        .map(|(v, t)| (rn(&rename, &v), t))
        .collect();
    subst_keyed.sort_by_key(|a| a.0);
    for (v, t) in &subst_keyed {
        push_u64(&mut out, v.idx);
        out.push(':');
        out.push_str(lsort_key_str(v.sort));
        out.push('=');
        write_term_to_key(t, &rename, &mut out);
        out.push(',');
    }
    out.push(']');
    // EQSTORE.conj — domain vars renamed; range is VFresh so name-hints
    // are dropped (we serialise range structurally with empty names).
    out.push_str(";CONJ:[");
    // Sorted-section scratch: elements are rendered contiguously into ONE
    // buffer as (start, len) ranges and joined via `push_sorted_ranges`,
    // replacing a `Vec<String>` (one alloc per element) per section.  The
    // buffer and range Vec are reused across all sorted sections below.
    let mut scratch = String::new();
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    for disj in &eq_store.conj {
        out.push_str("id=SplitId(");
        push_i64(&mut out, disj.split_id.0);
        out.push_str(");");
        scratch.clear();
        ranges.clear();
        for sub in &disj.substs {
            let start = scratch.len();
            let mut entries: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = sub
                .to_list()
                .into_iter()
                .map(|(v, t)| (rn(&rename, &v), t))
                .collect();
            entries.sort_by_key(|a| a.0);
            for (v, t) in &entries {
                push_u64(&mut scratch, v.idx);
                scratch.push(':');
                scratch.push_str(lsort_key_str(v.sort));
                scratch.push('=');
                // For VFresh range vars: strip name hints by writing
                // "v{idx}" — `renameDropNamehint` (LTerm.hs:737-740) over the
                // range term alone.  The store is per RANGE TERM: its free
                // vars, in DFS order, take empty-name indices restarting at 0.
                let mut local_ren = Bindings::new();
                let mut local_fresh = tamarin_utils::fresh::FastFreshState::nothing_used();
                use tamarin_term::lterm::HasFrees;
                t.for_each_free(&mut |v| {
                    local_ren.import_drop_namehint(v, &mut local_fresh);
                });
                write_term_to_key_local(t, &local_ren, &mut scratch);
                scratch.push(',');
            }
            ranges.push((start, scratch.len() - start));
        }
        push_sorted_ranges(&mut out, &scratch, &mut ranges, '|');
        out.push(';');
    }
    out.push(']');
    // FORMULAS / SOLVED FORMULAS / LEMMAS: identical shape — render each
    // guarded formula into the shared scratch buffer as a sorted section.
    let push_guarded_section = |out: &mut String,
                                items: &[std::sync::Arc<crate::guarded::Guarded>],
                                scratch: &mut String,
                                ranges: &mut Vec<(usize, usize)>| {
        scratch.clear();
        ranges.clear();
        for g in items {
            let start = scratch.len();
            write_guarded_struct(g, &rename, scratch);
            ranges.push((start, scratch.len() - start));
        }
        push_sorted_ranges(out, scratch, ranges, ';');
    };
    out.push_str(";FORMS:[");
    push_guarded_section(&mut out, formulas, &mut scratch, &mut ranges);
    out.push(']');
    out.push_str(";SOLV_FORMS:[");
    push_guarded_section(&mut out, solved_formulas, &mut scratch, &mut ranges);
    out.push(']');
    out.push_str(";LEMMAS:[");
    push_guarded_section(&mut out, lemmas, &mut scratch, &mut ranges);
    out.push(']');
    // GOALS (deterministic order, renamed-var keyed).
    // HS structural Ord on System includes `_sGoals :: Map Goal
    // GoalStatus` — both the Goal key AND the GoalStatus value
    // participate.  GoalStatus = (gsSolved, gsNr, gsLoopBreaker)
    // per System.hs:370-380.  Status fields must be included, or
    // cases with the same goals but different goal-status (e.g.
    // differing gsNr from creation order) would under-discriminate.
    out.push_str(";GOALS:[");
    scratch.clear();
    ranges.clear();
    for (g, st) in goals.iter() {
        let start = scratch.len();
        write_goal_to_key(g, &rename, &mut scratch);
        scratch.push_str(":st=");
        scratch.push_str(bool_key_str(st.solved));
        scratch.push(',');
        push_u64(&mut scratch, st.nr);
        scratch.push(',');
        scratch.push_str(bool_key_str(st.looping));
        ranges.push((start, scratch.len() - start));
    }
    push_sorted_ranges(&mut out, &scratch, &mut ranges, ';');
    out.push(']');
    // HS also includes `_sNextGoalNr :: Integer` in the structural Ord
    // (System.hs:383-401, see line 394).  Include for faithfulness.
    out.push_str(";NEXT_NR=");
    push_u64(&mut out, sys.next_goal_nr);
    // SOURCE KIND / DIFF — affect compareSystemsUpToNewVars only via
    // structural fallthrough when m != False.
    let _ = write!(out, ";SK={:?};SIDE={:?}", sys.source_kind, sys.side);
    out
}

/// Serialise a Goal with renamed vars.
fn write_goal_to_key(
    g: &crate::constraint::constraints::Goal,
    rename: &Bindings,
    out: &mut String,
) {
    use crate::constraint::constraints::Goal;
    match g {
        Goal::Action(i, fa) => {
            let ri = rn(rename, i);
            out.push_str("A(");
            push_u64(out, ri.idx);
            out.push(':');
            out.push_str(lsort_key_str(ri.sort));
            out.push(',');
            write_fact_to_key(fa, rename, out);
            out.push(')');
        }
        Goal::Premise(p, fa) => {
            let ri = rn(rename, &p.0);
            out.push_str("P(");
            push_u64(out, ri.idx);
            out.push(':');
            out.push_str(lsort_key_str(ri.sort));
            out.push_str(".PremIdx(");
            push_u64(out, p.1 .0 as u64);
            out.push_str("),");
            write_fact_to_key(fa, rename, out);
            out.push(')');
        }
        Goal::Chain(c, p) => {
            let rc = rn(rename, &c.0);
            let rp = rn(rename, &p.0);
            out.push_str("C(");
            push_u64(out, rc.idx);
            out.push(':');
            out.push_str(lsort_key_str(rc.sort));
            out.push_str(".ConcIdx(");
            push_u64(out, c.1 .0 as u64);
            out.push_str(")->");
            push_u64(out, rp.idx);
            out.push(':');
            out.push_str(lsort_key_str(rp.sort));
            out.push_str(".PremIdx(");
            push_u64(out, p.1 .0 as u64);
            out.push_str("))");
        }
        Goal::Subterm((a, b)) => {
            out.push_str("S(");
            write_term_to_key(a, rename, out);
            out.push_str("<<");
            write_term_to_key(b, rename, out);
            out.push(')');
        }
        Goal::Split(id) => {
            out.push_str("Sp(SplitId(");
            push_i64(out, id.0);
            out.push_str("))");
        }
        Goal::Disj(d) => {
            // HS `DisjG (Disj [LNGuarded])` participates in the structural
            // `Ord System` (via `_sGoals :: Map Goal GoalStatus`) as an
            // ORDERED disjunct list — `renameDropNamehint` (mapFrees,
            // Term/LTerm.hs:738-740) preserves disjunct order, and `Disj`
            // derives `Ord` element-wise.  So serialise the alternatives IN
            // ORDER, not sorted: sorting would conflate `A ∨ B` with
            // `B ∨ A`, and two alpha-equivalent sibling cases whose
            // disjunction goals map to swapped `gsNr` under the canonical
            // rename must stay distinct per HS's `Map Goal GoalStatus` Ord.
            out.push_str("D[");
            for (i, alt) in d.0.iter().enumerate() {
                if i > 0 {
                    out.push('|');
                }
                write_guarded_struct(alt, rename, out);
            }
            out.push(']');
        }
    }
}

/// Local variant of `write_term_to_key` that uses a local rename map
/// for VFresh range vars (no fallback to identity).
fn write_term_to_key_local(t: &tamarin_term::lterm::LNTerm, rename: &Bindings, out: &mut String) {
    // Same App/Con recursion as `write_term_to_key`, but the Var leaf drops
    // the name (local dedup keys use idx:sort only).
    write_term_to_key_with(t, out, &|v, out| {
        let rv = rename.get(v).unwrap_or(*v);
        out.push('v');
        push_u64(out, rv.idx);
        out.push(':');
        out.push_str(lsort_key_str(rv.sort));
    });
}

/// Direct port of HS `sortednubBy` (`lib/utils/src/Extension/Prelude.hs:52-87`,
/// GHC's `Data.List.sortBy` adapted to drop duplicates).  Sorts by `cmp`
/// AND removes elements for which an earlier-in-the-merge element compares
/// `EQ`.  The survivor of an `EQ`-group is NOT simply the first input
/// element: the run-detection phase (`sequences`) does `EQ -> sequences xs`
/// which drops the *earlier* element and keeps the *later* one, while the
/// `merge` phase drops the right-list element on `EQ`.  We replicate the
/// algorithm verbatim so survivor selection matches HS exactly.
fn sortednub_by<T, C>(cmp: &C, xs: Vec<T>) -> Vec<T>
where
    C: Fn(&T, &T) -> std::cmp::Ordering,
{
    use std::cmp::Ordering::*;
    // sequences: build maximal ascending/descending runs, dropping EQ.
    fn sequences<T, C>(cmp: &C, mut xs: Vec<T>) -> Vec<Vec<T>>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        // Iteratively consume `xs`; mirrors the recursive HS `sequences`.
        let mut runs: Vec<Vec<T>> = Vec::new();
        loop {
            if xs.len() < 2 {
                runs.push(xs);
                return runs;
            }
            // pop first two (a, b) preserving the rest order.
            let mut it = xs.into_iter();
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            let rest: Vec<T> = it.collect();
            match cmp(&a, &b) {
                Greater => {
                    // descending b [a] rest'
                    let (run, remaining) = descending(cmp, b, vec![a], rest);
                    runs.push(run);
                    xs = remaining;
                }
                Equal => {
                    // a `cmp` b == EQ -> sequences xs (drop a, keep from b)
                    let mut next = Vec::with_capacity(rest.len() + 1);
                    next.push(b);
                    next.extend(rest);
                    xs = next;
                }
                Less => {
                    // ascending b (a:) rest
                    let (run, remaining) = ascending(cmp, b, vec![a], rest);
                    runs.push(run);
                    xs = remaining;
                }
            }
        }
    }

    // descending a as (b:bs) | a `cmp` b == GT = descending b (a:as) bs
    // descending a as bs = (a:as) : sequences bs   -- (a:as) already reversed -> ascending
    fn descending<T, C>(cmp: &C, mut a: T, mut acc: Vec<T>, mut bs: Vec<T>) -> (Vec<T>, Vec<T>)
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        loop {
            if let Some(b_ref) = bs.first() {
                if cmp(&a, b_ref) == Greater {
                    let mut it = bs.into_iter();
                    let b = it.next().unwrap();
                    bs = it.collect();
                    acc.insert(0, a); // a:as  (acc holds run in ascending order)
                    a = b;
                    continue;
                }
            }
            // (a:as) : run is acc with a prepended; acc already ascending, so result ascending
            acc.insert(0, a);
            return (acc, bs);
        }
    }

    // ascending a as (b:bs) | a `cmp` b == LT = ascending b (\ys -> as (a:ys)) bs
    // ascending a as bs = as [a] : sequences bs
    fn ascending<T, C>(cmp: &C, mut a: T, mut acc: Vec<T>, mut bs: Vec<T>) -> (Vec<T>, Vec<T>)
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        loop {
            if let Some(b_ref) = bs.first() {
                if cmp(&a, b_ref) == Less {
                    let mut it = bs.into_iter();
                    let b = it.next().unwrap();
                    bs = it.collect();
                    acc.push(a); // as ++ [a]
                    a = b;
                    continue;
                }
            }
            acc.push(a); // as [a]
            return (acc, bs);
        }
    }

    // merge two sorted-deduped runs, dropping EQ (right element).
    fn merge<T, C>(cmp: &C, a: Vec<T>, b: Vec<T>) -> Vec<T>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let cap = a.len() + b.len();
        let mut out: Vec<T> = Vec::with_capacity(cap);
        let mut ai = a.into_iter().peekable();
        let mut bi = b.into_iter().peekable();
        loop {
            match (ai.peek(), bi.peek()) {
                (Some(av), Some(bv)) => match cmp(av, bv) {
                    Greater => out.push(bi.next().unwrap()),
                    Equal => {
                        // drop the right-list element (b), keep left
                        bi.next();
                    }
                    Less => out.push(ai.next().unwrap()),
                },
                (Some(_), None) => {
                    out.extend(ai);
                    return out;
                }
                (None, _) => {
                    out.extend(bi);
                    return out;
                }
            }
        }
    }

    fn merge_pairs<T, C>(cmp: &C, xs: Vec<Vec<T>>) -> Vec<Vec<T>>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let mut out: Vec<Vec<T>> = Vec::with_capacity(xs.len().div_ceil(2));
        let mut it = xs.into_iter();
        loop {
            match (it.next(), it.next()) {
                (Some(a), Some(b)) => out.push(merge(cmp, a, b)),
                (Some(a), None) => {
                    out.push(a);
                    return out;
                }
                (None, _) => return out,
            }
        }
    }

    fn merge_all<T, C>(cmp: &C, mut xs: Vec<Vec<T>>) -> Vec<T>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        if xs.is_empty() {
            return Vec::new();
        }
        while xs.len() > 1 {
            xs = merge_pairs(cmp, xs);
        }
        xs.into_iter().next().unwrap()
    }

    merge_all(cmp, sequences(cmp, xs))
}

/// Gated on BP/MSet per HS short-circuit.  Faithful port of HS
/// `removeRedundantCases` (`Sources.hs:236-260`, body at 242-244): decorate each case with
/// its original index, run `sortednubBy compareSystemsUpToNewVars` over the
/// decorated list, then `sortOn fst` to restore original-index order.  The
/// survivor of an alpha-equivalent group is the one `sortednubBy` keeps —
/// which is the LAST element of an `EQ`-run, not the first
/// (cf. Joux/Scott `Session_Key_Secrecy_PFS` B↔C mirror).  We port `sortednubBy` verbatim
/// rather than approximate it: for the common case (an `EQ`-group of pure
/// alpha-duplicates with identical keys) this keeps the LAST member and,
/// after `sortOn fst`, emits survivors in original-index order — the exact
/// flip the Joux/Scott mirror needed.  (The string key encodes what
/// `compareSystemsUpToNewVars` distinguishes, so two cases compare `EQ`
/// here iff they are alpha-equivalent there.)
pub fn remove_redundant_cases<T, F>(
    enable_bp: bool,
    enable_mset: bool,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    get_sys: F,
    cases: Vec<T>,
) -> Vec<T>
where
    F: Fn(&T) -> &crate::constraint::system::System,
{
    if !(enable_bp || enable_mset) {
        return cases;
    }
    // A 0- or 1-element list is a dedup fixpoint: `sortednubBy` then
    // `sortOn fst` are the identity on it, so skip the full-system keying
    // (compute_compare_systems_key is pure/call-local, so eliding it for
    // len<2 cannot perturb fresh-var numbering, goal order, or stdout).
    if cases.len() < 2 {
        return cases;
    }
    let pre = cases.len();
    // Decorate with (original index, canonical key).  HS:
    //   decoratedCases = map (second addNormSys) $ zip [0..] cases0
    // where addNormSys produces the renamed/normed system; we precompute
    // the string key (which encodes exactly what compareSystemsUpToNewVars
    // distinguishes) instead of carrying the normed System.
    let mut decorated: Vec<(usize, String, T)> = Vec::with_capacity(pre);
    // Carry the previous case's key length as a capacity hint (sibling keys
    // in one call are similarly sized); 0 for the first case == no reserve.
    let mut cap_hint = 0usize;
    for (idx, c) in cases.into_iter().enumerate() {
        let key = compute_compare_systems_key(get_sys(&c), stable_vars, cap_hint);
        cap_hint = key.len();
        decorated.push((idx, key, c));
    }
    // sortednubBy (\(_,x) (_,y) -> compare x y)  -- compare on the key only,
    // matching HS comparing on the normed system via compareSystemsUpToNewVars.
    let mut deduped = sortednub_by(
        &|a: &(usize, String, T), b: &(usize, String, T)| a.1.cmp(&b.1),
        decorated,
    );
    // sortOn fst : restore original-index order.
    deduped.sort_by_key(|a| a.0);
    deduped.into_iter().map(|(_, _, c)| c).collect()
}

// SplitG is not a "safe" goal at saturate time while chains are open
// (`doSplit = noChainGoals && not (null chains)`, Sources.hs:152-164) —
// HS leaves `RuleACConstrs` SplitG OPEN, and variant narrowing happens
// at runtime as a deeper `case split` step, never as sibling source cases.

#[cfg(test)]
#[path = "sources_tests.rs"]
mod tests;
