// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.Solver.Sources`.
//!
//! Sources represent the big-step proofs computing the possible
//! sources of a fact in a constraint system. This module implements:
//!
//! - Building ordered source patterns for protocol facts and intruder knowledge,
//!   then enumerating the initial cases for each pattern.
//! - Saturating sources with respect to each other
//!   (`saturate_sources_with_simp*`, mirroring `saturateSources`).
//! - Refining sources with source-assumption lemmas
//!   (`refine_with_source_asms`, mirroring `refineWithSourceAsms`).
//! - Solving a goal by application of a precomputed source
//!   (`solve_with_source` / `apply_source`, mirroring `solveWithSource`).
//! - Removing redundant cases (`remove_redundant_cases`).
//!
//! Alongside the full machinery it also exposes the public data shapes
//! and the `IntegerParameters` config used by the rest of the solver.

use crate::constraint::solver::reduction::{GoalBranch, SystemBranch};
use crate::constraint::system::System;
use tamarin_term::bind::Bindings;
use tamarin_term::lterm::frees;

/// Solver-tuning parameters mirroring Haskell's `IntegerParameters`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntegerParameters {
    /// Maximum number of open destruction chains `solveAllSafeGoals` may
    /// solve during saturation before chain goals stop being safe (HS
    /// `paramOpenChainsLimit`, fed from `-c/--open-chains`).
    open_chains_limit: i64,
    /// Maximum saturation iterations during source refinement (HS
    /// `paramSaturationLimit`, fed from `-s/--saturation`).
    saturation_limit: usize,
}

impl Default for IntegerParameters {
    fn default() -> Self {
        // Defaults match Haskell's `defaultTheoryLoadOptions`
        // (TheoryLoader.hs): openChain=10, saturation=5.
        IntegerParameters {
            open_chains_limit: 10,
            saturation_limit: 5,
        }
    }
}

impl IntegerParameters {
    /// Build the Haskell defaults with any non-negative overrides applied.
    /// Values wider than the corresponding internal representation saturate;
    /// the CLI rejects values beyond Haskell's `Int` domain earlier, while
    /// library callers remain panic-free.
    pub fn with_overrides(open_chains: Option<u64>, saturation: Option<u64>) -> Self {
        let mut p = IntegerParameters::default();
        if let Some(value) = open_chains {
            p.open_chains_limit = i64::try_from(value).unwrap_or(i64::MAX);
        }
        if let Some(value) = saturation {
            p.saturation_limit = usize::try_from(value).unwrap_or(usize::MAX);
        }
        p
    }

    pub fn open_chains_limit(self) -> i64 {
        self.open_chains_limit
    }

    pub fn saturation_limit(self) -> usize {
        self.saturation_limit
    }

    pub(crate) fn with_saturation_limit(mut self, limit: usize) -> Self {
        self.saturation_limit = limit;
        self
    }
}

/// Number of unsolved-chain constraints in the system. Mirrors
/// `length . unsolvedChains` (System.hs), counting unsolved Chain
/// goals in one System. (Distinct from Haskell `unsolvedChainConstraints
/// :: Source -> [Int]` at Sources.hs, which maps over a Source's
/// cases.)
pub fn unsolved_chain_constraints(sys: &System) -> usize {
    sys.unsolved_chains().count()
}

/// Case names retain their components until the proof label is rendered.
pub type SourceCase = (Vec<String>, System);

/// One ordered source goal and its cases. A builder initialises each cell
/// once. Cloning a source shares its systems until refinement takes ownership.
#[derive(Clone)]
pub(crate) struct Source {
    pub goal: crate::constraint::constraints::Goal,
    cases: std::sync::OnceLock<std::sync::Arc<SourceCases>>,
}

struct SourceCases {
    systems: std::sync::Mutex<Vec<SourceCase>>,
    var_bounds: std::sync::OnceLock<Option<(u64, u64)>>,
}

impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = f.debug_struct("Source");
        out.field("goal", &self.goal);
        match self.cases.get().map(|cases| cases.systems.lock()) {
            Some(Ok(cases)) => out.field("cases", &*cases),
            Some(Err(_)) => out.field("cases", &"<poisoned>"),
            None => out.field("cases", &"<lazy>"),
        }
        .finish()
    }
}

impl Source {
    pub(crate) fn lazy(goal: crate::constraint::constraints::Goal) -> Self {
        Self {
            goal,
            cases: Default::default(),
        }
    }

    pub(crate) fn eager(
        goal: crate::constraint::constraints::Goal,
        cases: Vec<SourceCase>,
    ) -> Self {
        let source = Self::lazy(goal);
        source.set_cases(cases);
        source
    }

    pub(crate) fn cases(&self) -> Option<impl std::ops::Deref<Target = Vec<SourceCase>> + '_> {
        self.cases.get().map(|cases| cases.systems.lock().unwrap())
    }

    pub(crate) fn cases_or_empty(&self) -> Vec<SourceCase> {
        self.cases().map(|cases| cases.clone()).unwrap_or_default()
    }

    pub(crate) fn cases_len(&self) -> usize {
        self.cases().map_or(0, |cases| cases.len())
    }

    pub(crate) fn case_system_at(&self, n: usize) -> Option<System> {
        self.cases()?.get(n).map(|(_, sys)| sys.clone())
    }

    fn cases_take(&mut self) -> Vec<SourceCase> {
        self.cases
            .take()
            .map(|cases| match std::sync::Arc::try_unwrap(cases) {
                Ok(cases) => cases.systems.into_inner().unwrap(),
                Err(cases) => cases.systems.lock().unwrap().clone(),
            })
            .unwrap_or_default()
    }

    pub(crate) fn set_cases(&self, cases: Vec<SourceCase>) {
        assert!(
            self.cases
                .set(std::sync::Arc::new(SourceCases {
                    systems: std::sync::Mutex::new(cases),
                    var_bounds: Default::default(),
                }))
                .is_ok(),
            "source cases already initialised"
        );
    }
}

/// HS `initialSource` (Sources.hs): solve the goal once in a system holding
/// only the safety restrictions (CloseRule.hs), keeping every resulting case
/// as it is. Saturation simplifies them and drops the contradictory ones.
pub(crate) fn initial_source_cases(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Result<Vec<SourceCase>, crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};

    let mut sys = System::empty();
    sys.source_kind = Some(crate::constraint::system::SourceKind::RawSources);
    sys.insert_lemmas(ctx.safety_restrictions.iter().cloned());
    if !matches!(goal, Goal::Action(..) | Goal::Premise(..)) {
        return Ok(Vec::new());
    }
    let mut red = Reduction::new(ctx, sys);
    red.insert_goal(goal.clone());
    let outcome = crate::constraint::solver::goals::solve_goal(&mut red, goal)?;
    // `polish ((name, se), _) = ([name], se)`.
    Ok(match outcome {
        GoalCases::LinearNamed(name) => vec![(vec![name], red.sys)],
        GoalCases::Cases(branches) => branches
            .into_iter()
            .map(|branch| (vec![branch.name], branch.sys))
            .collect(),
        GoalCases::Contradictory => Vec::new(),
    })
}

/// Build the ordered protocol-fact and intruder-knowledge (KU) goal patterns.
/// [`ProofContext::build_sources`](super::context::ProofContext::build_sources)
/// enumerates their cases and saturates them in this order.
pub(crate) fn source_patterns(
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    use crate::constraint::constraints::Goal;
    use crate::fact::{fact_tag_arity, Fact, FactTag};
    use crate::rule::PremIdx;
    use tamarin_term::lterm::{LNTerm, LSort, LVar};

    /// HS `nMsgVars n = [varTerm (LVar "t" LSortMsg i) | i <- [1..n]]`
    /// (Sources.hs), for any sort.
    fn n_vars(sort: LSort, n: usize) -> Vec<LNTerm> {
        (1..=n as u64)
            .map(|i| {
                tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new(
                    "t", sort, i,
                )))
            })
            .collect()
    }

    use std::collections::BTreeSet;
    let mut tags: BTreeSet<FactTag> = BTreeSet::new();
    for o in &ctx.rules {
        for fa in o.rule.premises.iter().chain(o.rule.conclusions.iter()) {
            if matches!(&fa.tag, FactTag::Proto(_, _, _)) {
                tags.insert(fa.tag);
            }
        }
    }

    let mut out: Vec<Source> = Vec::new();
    // -----------------------------------------------------------------
    // protoGoals — PremiseG for each proto-fact tag seen in the rules.
    // Mirrors Haskell's protoGoals branch of `precomputeSources`.
    // -----------------------------------------------------------------
    for tag in tags {
        let goal_node = LVar::new("i", LSort::Node, 0);
        let abstract_fact = Fact::new(tag, n_vars(LSort::Msg, fact_tag_arity(&tag)));
        let goal = Goal::Premise((goal_node, PremIdx(0)), abstract_fact);
        out.push(Source::lazy(goal));
    }

    // HS `msgGoals = someKUGoal <$> absMsgFacts`: KU goals for a fresh
    // variable and for each function symbol head.
    let goal_node = LVar::new("i", LSort::Node, 0);
    let mut ku_patterns: Vec<LNTerm> = Vec::new();
    // `absMsgFacts` is `sortednub`ed, and runtime lookup takes the first
    // matching source, so order matters: the fresh variable sorts first,
    // then NoEq applications by name (`fun_syms` order), then AC (natural
    // numbers) and C (bilinear pairing) heads (`FunSym` Ord NoEq < Ac < C).
    ku_patterns.push(tamarin_term::term::Term::Lit(
        tamarin_term::vterm::Lit::Var(LVar::new("t", LSort::Fresh, 1)),
    ));
    let msig = ctx.maude.maude_sig();
    // `[fAppNoEq o (nMsgVars k) | o <- noEqFunSyms msig, NoEq o `notMember`
    // implicitFunSig, k > 0 || priv == Private]`, destructors included.
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
            ku_patterns.push(tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::NoEq(*noeq),
                n_vars(LSort::Msg, noeq.arity).into(),
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
        ku_patterns.push(tamarin_term::term::f_app_ac(
            tamarin_term::function_symbols::AcSym::NatPlus,
            n_vars(LSort::Nat, 2),
        ));
    }
    // Bilinear pairing branch.  Mirrors HS Sources.hs:
    //     if enableBP msig then return $ fAppC EMap $ nMsgVars (2::Int) else []
    // C-headed; sortednub puts this LAST (after every NoEq + Ac term).
    if msig.enable_bp {
        ku_patterns.push(tamarin_term::term::f_app_c(
            tamarin_term::function_symbols::CSym::EMap,
            n_vars(LSort::Msg, 2),
        ));
    }
    for pat in ku_patterns {
        let goal = Goal::Action(goal_node, crate::fact::ku_fact(pat));
        out.push(Source::lazy(goal));
    }

    out
}

/// HS-faithful idx bounds over a WHOLE precomputed `Source` for the
/// `matchToGoal` rename + `refineSource` seed:
///
/// * `.0` = `boundsVarIdx th0` MIN (`matchToGoal`, Sources.hs,
///   under `instance HasFrees Source`, System.hs: `cdGoal`
///   pattern + ALL `cdCases`) — the rename's rebase origin.
/// * `.1` = the CASES-only MAX — feeds `fs = avoid th`
///   (Sources.hs) where
///   `th = set cdGoal goalTerm (renamed th0)` (Sources.hs):
///   `cdGoal` is the LIVE goal by then, so the pattern's frees don't
///   count; the caller maxes this (post-shift) with the live goal's
///   own max.
fn source_bounds(src: &Source) -> (Option<u64>, Option<u64>) {
    use tamarin_term::lterm::bounds_var_idx;
    let goal_min = bounds_var_idx(&src.goal).map(|(min, _)| min);
    let case_bounds = src.cases.get().and_then(|cases| {
        *cases.var_bounds.get_or_init(|| {
            cases
                .systems
                .lock()
                .unwrap()
                .iter()
                .filter_map(|(_, sys)| bounds_var_idx(sys))
                .reduce(|(lo, hi), (a, b)| (lo.min(a), hi.max(b)))
        })
    });
    match case_bounds {
        Some((lo, hi)) => (Some(goal_min.map_or(lo, |g| g.min(lo))), Some(hi)),
        None => (goal_min, None),
    }
}

/// Haskell `avoid th` for source saturation: the maximum free index in the
/// complete Source, including `cdGoal` and every case system.
fn source_avoid(src: &Source, cases: &[SourceCase]) -> u64 {
    cases
        .iter()
        .map(|(_, sys)| crate::constraint::solver::reduction::bounds_max(sys))
        .chain(std::iter::once(
            tamarin_term::lterm::bounds_var_idx(&src.goal)
                .map(|(_, max)| max)
                .unwrap_or(0),
        ))
        .max()
        .unwrap_or(0)
}

/// Restore the previous fresh-variable floor when a refinement scope ends.
/// [`Self::set`] takes the next variable index. [`Self::floor`] takes the
/// highest index already in use by the source.
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

/// HS `refineWithSourceAsms` (Sources.hs): add the `[sources]` assumptions
/// to every case, re-saturate so cases contradicting them disappear, then
/// remove the formulas again (`removeFormulas`).
pub(crate) fn refine_with_source_asms(
    sources: Vec<Source>,
    assumptions: &[std::sync::Arc<crate::guarded::Guarded>],
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Result<Vec<Source>, crate::prove::ProveError> {
    if assumptions.is_empty() {
        // HS `refineWithSourceAsms _ []` still applies `updateSystem`, so
        // refined consumers see `RefinedSource` even though no formulas need
        // to be added and no second saturation can change the cases.
        return Ok(sources
            .into_iter()
            .map(|mut src| {
                let cases = src
                    .cases_take()
                    .into_iter()
                    .map(|(name, mut sys)| {
                        sys.source_kind =
                            Some(crate::constraint::system::SourceKind::RefinedSources);
                        (name, sys)
                    })
                    .collect();
                Source::eager(src.goal, cases)
            })
            .collect());
    }

    // Add the assumptions to every raw case. Saturation explores their branches
    // and discards those that contradict the assumptions.
    let mut intermediate: Vec<Source> = Vec::new();
    for mut src in sources {
        let mut new_cases: Vec<SourceCase> = Vec::new();
        for (name, mut sys) in src.cases_take() {
            for a in assumptions {
                sys.insert_formula(a.clone());
            }
            // Mirror Haskell `set sSourceKind RefinedSource`.
            sys.source_kind = Some(crate::constraint::system::SourceKind::RefinedSources);
            new_cases.push((name, sys));
        }
        // An empty case list closes a matching goal. Keep its source entry.
        intermediate.push(Source::eager(src.goal, new_cases));
    }

    // HS uses the same `paramSaturationLimit` as the raw saturation.
    let limit = ctx.parameters.saturation_limit();
    let saturated = saturate_sources_with_simp(intermediate, limit, ctx)?;

    // `removeFormulas` (Sources.hs): strip formulas + solved
    // formulas after saturation, and drop disjunction goals derived
    // from the assumptions.
    let mut out: Vec<Source> = Vec::new();
    for mut src in saturated {
        let mut new_cases: Vec<SourceCase> = Vec::new();
        for (name, mut sys) in src.cases_take().into_iter() {
            sys.clear_formula_stores();
            sys.invalidate_max_var_idx_cache();
            sys.goals_mut()
                .retain(|(g, _)| !matches!(g, crate::constraint::constraints::Goal::Disj(_)));
            new_cases.push((name, sys));
        }
        // Empty case lists remain matching sources that close the goal.
        out.push(Source::eager(src.goal, new_cases));
    }
    Ok(out)
}

/// Refine one source and keep its goal even when all its cases disappear.
/// The change bit is HS's `not (null names)` for the surviving branches.
fn refine_one_source(
    ctx: &crate::constraint::solver::context::ProofContext,
    mut src: Source,
    ths_snapshot: &[Source],
    previously_deduplicated: bool,
) -> Result<(Source, bool), crate::prove::ProveError> {
    let mut changed = false;
    // HS-faithful `refineSource` (Sources.hs): the Reduction
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
    let all_cases = src.cases_take();
    // HS `refineSource` (Sources.hs): `fs = avoid th` — the fresh seed
    // for EVERY case is the max var idx over the WHOLE source `th` (all its
    // cases), NOT the per-case `avoid se`.  Compute it once here and thread
    // it as the seed floor into each case's Reduction.
    let source_avoid = source_avoid(&src, &all_cases);
    const LARGE_SOURCE: usize = 8;
    let sig = ctx.maude.maude_sig();
    let needs_dedup = sig.enable_bp || sig.enable_mset;
    // An ordered subset of a deduplicated source is still distinct if every
    // surviving system equals its input after substitution restriction.
    let mut still_distinct =
        previously_deduplicated && needs_dedup && all_cases.len() >= LARGE_SOURCE;
    for (name_list, sys) in all_cases {
        let original = still_distinct.then(|| sys.clone());
        let (branches, took_step) =
            solve_all_safe_goals(ctx, sys, ths_snapshot, name_list, source_avoid)?;
        changed |= took_step;
        still_distinct &= branches.len() <= 1;
        // `refineSource` restricts each branch's substitution to the
        // source goal's variables before removing redundant cases.
        for (mut branch_sys, branch_name_list) in branches {
            restrict_eq_store_to_stable_vars(&mut branch_sys, &stable_vars);
            if still_distinct {
                still_distinct = original.as_ref() == Some(&branch_sys);
            }
            deferred_filtered.push((branch_name_list, branch_sys));
        }
    }
    // `removeRedundantCases` runs once over all refined branches. Larger
    // sources compute the comparison keys on several workers.
    let deduped = if still_distinct {
        deferred_filtered
    } else if needs_dedup
        && deferred_filtered.len() >= LARGE_SOURCE
        && rayon::current_num_threads() > 1
    {
        let keyed = tamarin_utils::parallel::map_independent(deferred_filtered, move |case| {
            (norm_sys_for_compare(&case.1, &stable_vars), case)
        })?;
        deduplicate_normalized_cases(keyed)
    } else {
        remove_redundant_cases(
            sig.enable_bp,
            sig.enable_mset,
            &stable_vars,
            |c| &c.1,
            deferred_filtered,
        )
    };
    Ok((Source::eager(src.goal, deduped), changed))
}

/// HS `saturateSources` (Sources.hs): refine every source against the
/// single-case ones until no surviving case takes a step or `limit` passes
/// have run. With `show_saturation_steps` (HS `showSaturationSteps`, set by
/// every CLI close but not the auxiliary deduction and derivation checks) it
/// traces `[Saturating Sources]` progress to stderr.
pub(crate) fn saturate_sources_with_simp(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Result<Vec<Source>, crate::prove::ProveError> {
    let mut current = sources;
    // saturateSources performs one refinement even at limit zero, then repeats
    // up to `limit` times while a surviving case makes progress.
    for iter_n in 0..=limit {
        super::search::check_cancelled()?;
        // `goodTh` (Sources.hs) restricts saturation's solver to sources with
        // at most one case, bounding branching during refinement.
        let ths_snapshot: Vec<Source> = current
            .iter()
            .filter(|s| s.cases_len() <= 1)
            .cloned()
            .collect();
        // HS refines each source against the same snapshot, keeping each
        // goal with its own cases, including an empty case list.
        let worker_ctx = ctx.clone();
        let refined = tamarin_utils::parallel::try_map(current, move |src| {
            let ctx = &worker_ctx;
            #[cfg(test)]
            super::cancellation_tests::checkpoint(ctx, super::cancellation_tests::Work::Sources);
            super::search::check_cancelled()?;
            // This source is already assigned. Use the caller's process if no
            // helper is ready so its refinement can start immediately.
            let pooled = ctx
                .maude_pool
                .as_ref()
                .and_then(|pool| pool.try_take_idle_owned());
            let task_maude = pooled.as_ref().map_or_else(
                || ctx.maude.clone(),
                |p| p.handle().with_fresh_counter_from(0),
            );
            let task_ctx = ctx.with_swapped_maude(task_maude);
            refine_one_source(&task_ctx, src, &ths_snapshot, iter_n > 0)
        })?;
        let changed = refined.iter().any(|(_, changed)| *changed);
        current = refined.into_iter().map(|(source, _)| source).collect();
        let n = iter_n + 1;
        if ctx.show_saturation_steps {
            // HS checks the iteration limit before convergence, even on the
            // final pass. The aborted message retains its upstream wording.
            if n > limit {
                eprintln!(
                    "[Saturating Sources] Saturation aborted, more than {limit} \
                     iterations. (Limit can be changed with -s=)"
                );
            } else if changed {
                eprintln!("[Saturating Sources] Step {n} (Max {limit})");
            } else {
                eprintln!("[Saturating Sources] Done");
            }
        }
        if !changed {
            break;
        }
    }
    Ok(current)
}

/// Read the K(U|D) conclusion term of `c` from `sys` — mirrors HS
/// `kConcTerm` (Sources.hs): returns Some only when the
/// node's conclusion fact at `c.1` is a KU or KD fact.  Module-level
/// helper used by `solve_all_safe_goals`'s
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

/// Refine one case until its surviving branches have no safe goal or eligible
/// source left to apply. Each branch inherits the remaining open-chain limit.
/// The flag requests another saturation pass if any surviving branch took a step.
fn solve_all_safe_goals(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    ths: &[Source],
    initial_name: Vec<String>,
    source_avoid: u64,
) -> Result<(Vec<(System, Vec<String>)>, bool), crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::contradictions::first_contradiction;
    use crate::constraint::solver::goals::solve_goal;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};
    use crate::constraint::solver::simplify::simplify_system_with_fanout_seeded_with_counters;
    use crate::fact::FactTag;

    struct Entry {
        sys: System,
        /// Keep step names separate so `combine` can select the first non-coercion step.
        name: Vec<String>,
        /// Indices of the sources this branch has applied, which HS
        /// `filterCases` removes from its source list.
        used: std::collections::BTreeSet<usize>,
        chains_left: i64,
        /// Skip chain conclusions equal modulo freshness to the last one solved.
        last_chain_term: Option<tamarin_term::lterm::LNTerm>,
        /// Contributes to saturation progress when this branch survives.
        took_step: bool,
        fresh_counter: u64,
    }
    // `avoid th` (Sources.hs) bounds the entire source, including all its
    // cases. Carry this floor into nested simplification reductions and
    // restore the outer scope when this refinement returns.
    let _refine_floor_guard = RefineFsScope::floor(source_avoid);
    let chains_limit = ctx.parameters.open_chains_limit();
    let mut worklist: Vec<Entry> = vec![Entry {
        sys: initial_sys,
        name: Vec::new(), /* fresh accumulator for steps */
        used: std::collections::BTreeSet::new(),
        chains_left: chains_limit,
        last_chain_term: None,
        took_step: false,
        fresh_counter: source_avoid.saturating_add(1),
    }];
    let mut finished: Vec<(System, Vec<String>)> = Vec::new();
    // Only steps on branches that reach a leaf count towards saturation progress.
    let mut any_step_taken = false;

    while let Some(Entry {
        sys,
        name,
        used,
        chains_left,
        last_chain_term,
        took_step,
        fresh_counter,
    }) = worklist.pop()
    {
        // HS `solve` starts with `simplifySystem` and `contradictoryIf`. A
        // simplification that splits the state (`DisjT`) yields sibling
        // systems; continue with the first and push the rest so they pop in
        // order. An empty result drops the branch.
        let post_simp = simplify_system_with_fanout_seeded_with_counters(ctx, sys, fresh_counter)?;
        let SystemBranch {
            sys,
            counter: fresh_counter,
        } = match post_simp.len() {
            0 => continue, // all siblings contradictory / dropped
            1 => post_simp.into_iter().next().unwrap(),
            _ => {
                let mut iter = post_simp.into_iter();
                let head = iter.next().unwrap();
                let tail: Vec<_> = iter.collect();
                for SystemBranch {
                    sys: sib,
                    counter: sibling_counter,
                } in tail.into_iter().rev()
                {
                    worklist.push(Entry {
                        sys: sib,
                        name: name.clone(),
                        used: used.clone(),
                        chains_left,
                        last_chain_term: last_chain_term.clone(),
                        took_step,
                        fresh_counter: sibling_counter,
                    });
                }
                head
            }
        };
        let mut red = Reduction::new_inheriting(ctx, sys, fresh_counter);
        if first_contradiction(red.ctx, &red.sys)?.is_some() {
            // Haskell mzero — drop branch (don't push to finished).
            continue;
        }

        // HS `openGoals` in `Goal` order (`M.toList sGoals`).
        let sat_adj = red.sys.build_always_before_adj();
        let mut goals: Vec<(Goal, bool)> = red
            .sys
            .goals
            .iter()
            .filter(|(_, st)| !st.solved)
            .filter(|(g, _)| {
                crate::constraint::solver::goals::is_open_in_sys(g, &red.sys, &sat_adj)
            })
            .map(|(g, st)| (g.clone(), st.looping))
            .collect();
        goals.sort_by(|a, b| a.0.cmp(&b.0));
        // `lastChainTerm` (Sources.hs) excludes a chain whose conclusion is
        // equal modulo freshness to the last solved chain's conclusion. This
        // bounds repeated destructor expansion during saturation.
        let last_canon = last_chain_term
            .clone()
            .map(crate::tools::abstract_interpretation::canonicalize_freshness_no_ac);
        let filtered_goals: Vec<(Goal, bool)> = goals
            .iter()
            .filter(|(g, _)| {
                match g {
                    Goal::Chain(c, _) => {
                        // HS: `Just True /= liftM2 eqModuloFreshnessNoAC last this`
                        match (&last_canon, k_conc_term_for_chain(&red.sys, c)) {
                            (Some(lt), Some(tt)) => {
                                *lt != crate::tools::abstract_interpretation::canonicalize_freshness_no_ac(tt)
                            }
                            _ => true,
                        }
                    }
                    _ => true,
                }
            })
            .cloned()
            .collect();
        // Unfiltered chains view — Haskell's `unsolvedChains`.
        let any_unsolved_chain = red.sys.unsolved_chains().next().is_some();
        let any_chain_goal = goals.iter().any(|(g, _)| matches!(g, Goal::Chain(_, _)));
        let split_allowed = !any_chain_goal && any_unsolved_chain;
        // Haskell parity (Sources.hs).
        let is_kd_prem = |g: &Goal| -> bool {
            matches!(g, Goal::Premise(_, fa)
                if fa.tag == FactTag::Kd && !crate::fact::is_kd_xor_fact(fa))
        };
        let is_chain_prem1 =
            |g: &Goal| -> bool { matches!(g, Goal::Chain(_, (_, pi)) if pi.0 == 1) };
        // HS `safeGoal`: splits are safe only when `splitAllowed`.
        let is_safe = |g: &Goal, looping: bool| -> bool {
            if looping {
                return false;
            }
            match g {
                Goal::Chain(_, _) => {
                    if chains_left > 0 {
                        true
                    } else {
                        // HS `traceChainLimit`, gated by `showSaturationSteps`.
                        if red.ctx.show_saturation_steps {
                            eprintln!(
                                "[Open Chains] Too many chain constraints, \
                                 stopping precomputation. Open Chains limits (can \
                                 be changed with -c=): {chains_limit}"
                            );
                        }
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
                Goal::Split(_) => split_allowed,
            }
        };
        // HS `kdPremGoals` read all open goals and `safeGoals` the
        // chain-filtered ones. The head of `safeGoals` decides the chain
        // budget (`remainingChains`) and `lastChainTerm'`, whichever goal is
        // solved. (The `[Open Chains]` trace can fire more often than HS's
        // lazily forced list.)
        let first_safe = filtered_goals.iter().find(|(g, l)| is_safe(g, *l));
        let safe_head_is_chain = matches!(first_safe, Some((Goal::Chain(_, _), _)));
        let pick = goals
            .iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or(first_safe);
        let kd_prem_empty = !goals
            .iter()
            .any(|(g, _)| is_kd_prem(g) || is_chain_prem1(g));
        let new_last_chain_term = if kd_prem_empty {
            if let Some((Goal::Chain(c, _), _)) = first_safe {
                let t = k_conc_term_for_chain(&red.sys, c);
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
            let inner_outcome = solve_goal(&mut red, &goal)?;
            match inner_outcome {
                GoalCases::Contradictory => {
                    continue;
                }
                GoalCases::LinearNamed(sub_name) => {
                    // Steps append their names (`caseNames ++ x`); `combine`
                    // runs only at the `refineSource` boundary.
                    let mut new_name = name.clone();
                    new_name.push(sub_name);
                    worklist.push(Entry {
                        sys: red.sys,
                        name: new_name,
                        used,
                        chains_left: new_chains_left,
                        last_chain_term: new_last_chain_term.clone(),
                        took_step: true,
                        fresh_counter: red.maude.fresh_counter_peek(),
                    });
                }
                GoalCases::Cases(cases) => {
                    // Push the cases reversed so they pop in HS's order.
                    for branch in cases.into_iter().rev() {
                        let mut new_name = name.clone();
                        new_name.push(branch.name);
                        worklist.push(Entry {
                            sys: branch.sys,
                            name: new_name,
                            used: used.clone(),
                            chains_left: new_chains_left,
                            last_chain_term: new_last_chain_term.clone(),
                            took_step: true,
                            fresh_counter: branch.counter,
                        });
                    }
                }
            }
            continue;
        }

        // No safe goal: try a source (the third alternative of `nextStep`).
        if ths.is_empty() {
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        // HS `usefulGoals`: pick the first Useful goal with a matching source
        // among the sources this branch has not applied yet. Sources match
        // only premises and KU actions; a premise that is not a loop breaker
        // is Useful, as is a KU action unless it is deducible or probably
        // constructible. `sat_adj` still describes `red.sys` here, since no
        // goal was solved above.
        use crate::constraint::solver::annotated_goals::Usefulness;
        let has_ku_guards = crate::constraint::solver::goals::has_ku_guards(&red.sys);
        let useful: Vec<Goal> = goals
            .iter()
            .filter(|(g, looping)| match g {
                Goal::Premise(_, _) => !looping,
                Goal::Action(_, fa) if matches!(fa.tag, FactTag::Ku) => {
                    crate::constraint::solver::goals::goal_usefulness_with_adj(
                        g,
                        *looping,
                        &red.sys,
                        sat_adj.map(),
                        has_ku_guards,
                    ) == Usefulness::Useful
                }
                _ => false,
            })
            .map(|(g, _)| g.clone())
            .collect();
        if useful.is_empty() {
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        // Iterate useful goals in order; first one with a matching
        // source wins (Haskell `asum`). A matching source whose cases all
        // vanish makes `disjunctionOfList []` fail, dropping this branch.
        let mut picked = None;
        for goal in &useful {
            let unused = ths.iter().enumerate().filter(|(i, _)| !used.contains(i));
            picked = apply_first_source(ctx, unused, &red.sys, goal, &red.maude)?;
            if picked.is_some() {
                break;
            }
        }
        let Some((source_index, branches)) = picked else {
            // `nextStep = Nothing`: the branch is finished.
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        };
        for (
            case_names,
            SystemBranch {
                sys: sys_cand,
                counter: branch_counter,
            },
        ) in branches
        {
            let mut new_used = used.clone();
            new_used.insert(source_index);
            // `caseNames ++ x`, where `x` is the applied case's name list.
            let mut new_name = name.clone();
            new_name.extend(case_names);
            worklist.push(Entry {
                sys: sys_cand,
                name: new_name,
                used: new_used,
                chains_left,
                last_chain_term: new_last_chain_term.clone(),
                took_step: true,
                fresh_counter: branch_counter,
            });
        }
    }

    // `refineSource` combines the case's name with the steps taken.
    let branches: Vec<(System, Vec<String>)> = finished
        .into_iter()
        .map(|(sys, step_names_list)| {
            let combined = combine_case_names_list(&initial_name, &step_names_list);
            (sys, combined)
        })
        .collect();
    Ok((branches, any_step_taken))
}

/// HS `solveWithSource` (Sources.hs) during proof search: apply the first of
/// the proof's sources that matches `goal`. `None` when no source matches; a
/// matched source whose cases all vanish closes the goal with no branches.
pub(crate) fn solve_with_source(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: &System,
    goal: &crate::constraint::constraints::Goal,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<Option<Vec<GoalBranch>>, crate::prove::ProveError> {
    // Goal matching uses the layout alone. Force the proof's sources only
    // after finding a candidate.
    if !ctx
        .full_sources
        .iter()
        .any(|source| source_goal_may_match(&source.goal, goal))
    {
        return Ok(None);
    }
    let sources = ctx.ensure_saturated()?;
    // `intercalate "_"` of each case's names (ProofMethod.hs `solve`).
    Ok(
        apply_first_source(ctx, sources.iter().enumerate(), sys, goal, maude)?.map(
            |(_, branches)| {
                branches
                    .into_iter()
                    .map(|(names, SystemBranch { sys, counter })| GoalBranch {
                        name: case_name_list_to_string(&names),
                        sys,
                        counter,
                    })
                    .collect()
            },
        ),
    )
}

/// A case of an applied source: its name list and resulting branch.
type SourceBranch = (Vec<String>, SystemBranch);

/// HS `solveWithSourceAndReturn` (Sources.hs): `applySource` with the first
/// of `sources` that `matchToGoal` accepts, returning that source's index
/// with the resulting branches.
fn apply_first_source<'s>(
    ctx: &crate::constraint::solver::context::ProofContext,
    sources: impl IntoIterator<Item = (usize, &'s Source)>,
    sys: &System,
    goal: &crate::constraint::constraints::Goal,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<Option<(usize, Vec<SourceBranch>)>, crate::prove::ProveError> {
    for (index, source) in sources {
        if !source_goal_may_match(&source.goal, goal) {
            continue;
        }
        if let Some(prepared) = prepare_source_match(ctx, source, goal)? {
            let branches = apply_source(ctx, source.cases_or_empty(), &prepared, sys, goal, maude)?;
            return Ok(Some((index, branches)));
        }
    }
    Ok(None)
}

/// HS `applySource` (Sources.hs) for a matched source: `refineSource` refines
/// every case and removes redundant ones, then `_applySource` marks the goal
/// solved, instantiates each surviving case with `someInst` and conjoins it.
/// The case disjunction sits below FreshT, so every case starts from the
/// counter at the pick and carries only its own draws onward.
fn apply_source(
    ctx: &crate::constraint::solver::context::ProofContext,
    cases: Vec<SourceCase>,
    prepared: &PreparedSourceMatch,
    sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<Vec<SourceBranch>, crate::prove::ProveError> {
    let fork_base = maude.fresh_counter_peek();
    let mut refined = Vec::new();
    for (name, case_sys) in cases {
        refined.extend(
            refine_source_case(ctx, prepared, case_sys)?
                .into_iter()
                .map(|case| (name.clone(), case)),
        );
    }
    let msig = ctx.maude.maude_sig();
    let refined = remove_redundant_cases(
        msig.enable_bp,
        msig.enable_mset,
        &prepared.stable_vars,
        |(_, case): &(Vec<String>, System)| case,
        refined,
    );
    let keep_vars: Vec<_> = prepared.stable_vars.iter().copied().collect();
    let mut out = Vec::new();
    for (name, case) in refined {
        maude.reset_counter_to(fork_base);
        let case = some_inst_system(case, &keep_vars, maude);
        for branch in conjoin_source_case(ctx, sys, live_goal, &case, maude)? {
            out.push((name.clone(), branch));
        }
    }
    Ok(out)
}

/// Render a step-name list as a single user-facing case-name string,
/// matching HS's `intercalate "_" names'` (ProofMethod.hs).
pub fn case_name_list_to_string(names: &[String]) -> String {
    names.join("_")
}

/// HS `combine` (Sources.hs `refineSource`): drop leading `coerce` steps,
/// then keep only the first remaining name, or take the new names if none
/// remains.
///
/// ```haskell
/// combine []            ns' = ns'
/// combine ("coerce":ns) ns' = combine ns ns'
/// combine (n       :_)  _   = [n]
/// ```
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

/// HS `modify sSubst (restrict stableVars)` (Sources.hs `refineSource`): keep
/// only the substitution bindings whose variable is stable. `restrict`
/// (SubstVFree.hs) filters keys by full `LVar` equality and leaves values
/// that mention dropped variables as they are.
fn restrict_eq_store_to_stable_vars(
    sys: &mut System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) {
    let kept: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = sys
        .eq_store()
        .subst
        .to_list()
        .into_iter()
        .filter(|(v, _)| stable_vars.contains(v))
        .collect();
    sys.invalidate_max_var_idx_cache();
    sys.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(kept);
}

/// `rename th0` (LTerm.hs) with the shift the caller has already
/// computed: every free variable's index moves by `shift_amount` through
/// `mapFrees (Monotone (incVar shift))`.  At runtime source dispatch this is
/// the rename `matchToGoal` performs on a whole source before matching it
/// against the live goal (Sources.hs, `rename th0` under `avoid
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
fn rename_system_by(sys: System, shift_amount: i128) -> System {
    use tamarin_term::lterm::HasFrees;
    sys.map_free_monotone(&mut |v: tamarin_term::lterm::LVar| {
        let mut w = v;
        w.idx = (v.idx as i128 + shift_amount).clamp(0, u64::MAX as i128) as u64;
        w
    })
}

/// `evalBindT (someInst sysTh0) keepVarBindings` (Sources.hs): the
/// source case about to be grafted into the live system takes a fresh index
/// for every free variable whose binding the caller has not already fixed, so
/// the graft shares only the goal's own variables with the live system.
///
/// `someInst` (LTerm.hs) is `mapFrees (Arbitrary importBinding)`, so
/// the index a variable gets is decided by where `instance HasFrees System`
/// (System.hs) first reaches it, and every index is drawn from the
/// step's own `MonadFresh` — here the Maude handle whose counter the live
/// `Reduction` threads.  `keep` is HS's `frees goal`, seeded into the store as
/// identity bindings that `importBinding` finds and reuses instead of drawing
/// (Control/Monad/Bind.hs).
fn some_inst_system(
    sys: System,
    keep: &[tamarin_term::lterm::LVar],
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> System {
    let mut bindings = Bindings::new();
    for v in keep {
        bindings.insert(*v, *v);
    }
    let mut fresh = maude;
    tamarin_term::bind::some_inst(sys, &mut bindings, &mut fresh)
}

/// Cheap half of Haskell's `maybeMatcher`.  In particular, reject action
/// sources with incompatible application heads before forcing their lazy
/// saturated cases or asking Maude for an AC match.
pub(super) fn source_goal_may_match(
    source: &crate::constraint::constraints::Goal,
    live: &crate::constraint::constraints::Goal,
) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::term::Term;

    match (source, live) {
        (Goal::Premise(_, source_fact), Goal::Premise(_, live_fact)) => {
            source_fact.tag == live_fact.tag
        }
        (Goal::Action(_, source_fact), Goal::Action(_, live_fact))
            if source_fact.tag == FactTag::Ku
                && live_fact.tag == FactTag::Ku
                && source_fact.terms.len() == 1
                && live_fact.terms.len() == 1 =>
        {
            match (&source_fact.terms[0], &live_fact.terms[0]) {
                (Term::App(source_head, _), Term::App(live_head, _)) => source_head == live_head,
                // Do not reject a non-Fresh live term for the abstract
                // `t:Fresh` source here.  Current Haskell checks
                // `sortOfLNTerm tPat` after already pattern-matching tPat as
                // Fresh, so that guard is tautological; the real matcher is
                // responsible for deciding whether the source applies.
                _ => true,
            }
        }
        _ => false,
    }
}

/// Source-wide part of `matchToGoal`.  Haskell renames and matches a Source
/// once, then refines each member of `cdCases` with the resulting
/// substitution.  Keeping that boundary explicit both avoids repeated Maude
/// matching and prevents a failed individual case from being mistaken for a
/// failed source match.
struct PreparedSourceMatch {
    renamed_abstract_node: tamarin_term::lterm::LVar,
    prem_rewire: Option<(crate::rule::PremIdx, crate::rule::PremIdx)>,
    /// `frees goal`: the variables refinement keeps bound and `someInst`
    /// leaves unchanged.
    stable_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    rename_shift: i128,
    refine_seed: u64,
    match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>,
}

fn prepare_source_match(
    ctx: &crate::constraint::solver::context::ProofContext,
    src: &Source,
    live_goal: &crate::constraint::constraints::Goal,
) -> Result<Option<PreparedSourceMatch>, crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;
    use tamarin_term::lterm::HasFrees;

    let (abstract_node, abstract_fact, prem_rewire, live_node, live_fact) =
        match (&src.goal, live_goal) {
            (Goal::Action(an, af), Goal::Action(ln, lf)) => (*an, af, None, *ln, lf),
            (Goal::Premise((an, ap), af), Goal::Premise((ln, lp), lf)) => {
                (*an, af, Some((*ap, *lp)), *ln, lf)
            }
            _ => return Ok(None),
        };
    if live_fact.tag != abstract_fact.tag || live_fact.terms.len() != abstract_fact.terms.len() {
        return Ok(None);
    }

    let mut goal_max = 0;
    live_node.for_each_free(&mut |v| goal_max = goal_max.max(v.idx));
    live_fact.for_each_free(&mut |v| goal_max = goal_max.max(v.idx));
    let (src_min, src_cases_max) = source_bounds(src);
    let rename_shift = src_min
        .map(|min| i128::from(goal_max.saturating_add(1)) - i128::from(min))
        .unwrap_or(0);
    let shift_var = |mut v: tamarin_term::lterm::LVar| {
        v.idx = (i128::from(v.idx) + rename_shift).clamp(0, u64::MAX as i128) as u64;
        v
    };
    let renamed_abstract_node = shift_var(abstract_node);
    let renamed_abstract_fact = abstract_fact.clone().map_free(&mut |v| shift_var(v));
    let shifted_cases_max =
        src_cases_max.map(|max| (i128::from(max) + rename_shift).clamp(0, u64::MAX as i128) as u64);
    let refine_seed = goal_max
        .max(shifted_cases_max.unwrap_or(0))
        .saturating_add(1);

    let mut pairs = Vec::with_capacity(live_fact.terms.len() + 1);
    pairs.extend(
        live_fact
            .terms
            .iter()
            .cloned()
            .zip(renamed_abstract_fact.terms.iter().cloned()),
    );
    pairs.push((
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(live_node)),
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(renamed_abstract_node)),
    ));

    use tamarin_term::unification::MatchOutcome;
    let match_pairs =
        match tamarin_term::unification::solve_match_lterm::<tamarin_term::lterm::Name, _, _>(
            &tamarin_term::lterm::sort_of_name,
            &|_| true,
            tamarin_term::rewriting::Match::DelayedMatches(pairs.clone()),
        ) {
            MatchOutcome::Matched(subst) => subst.to_list(),
            MatchOutcome::NoMatcher => return Ok(None),
            MatchOutcome::NeedsAc => {
                let eqs = pairs
                    .into_iter()
                    .map(|(lhs, rhs)| tamarin_term::rewriting::Equal { lhs, rhs })
                    .collect::<Vec<_>>();
                let mut matches = ctx.maude.match_eqs(&eqs).map_err(|error| {
                    crate::prove::ProveError::maude("source matching failed", error)
                })?;
                if matches.is_empty() {
                    return Ok(None);
                }
                matches.swap_remove(0)
            }
        };

    Ok(Some(PreparedSourceMatch {
        renamed_abstract_node,
        prem_rewire,
        stable_vars: frees(live_goal).into_iter().collect(),
        rename_shift,
        refine_seed,
        match_pairs,
    }))
}

/// Upstream #958 `matchToGoal`: move a source's premise endpoint in both
/// edges and goals. Leaving a solved goal at the old index can discharge an
/// unrelated live premise when the source is conjoined with the system.
fn rewire_source_premise(
    sys: &mut System,
    from: (tamarin_term::lterm::LVar, crate::rule::PremIdx),
    to: (tamarin_term::lterm::LVar, crate::rule::PremIdx),
) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::system::GoalStatus;
    if from == to {
        return;
    }
    let mut goals = std::collections::BTreeMap::<Goal, GoalStatus>::new();
    for (goal, status) in sys.goals.iter() {
        let mut goal = goal.clone();
        match &mut goal {
            Goal::Premise(prem, _) | Goal::Chain(_, prem) if *prem == from => *prem = to,
            _ => {}
        }
        goals
            .entry(goal)
            .and_modify(|old| {
                old.merge_from(status);
            })
            .or_insert_with(|| status.clone());
    }
    let content = sys.content_mut();
    for edge in &mut content.edges {
        if edge.tgt == from {
            edge.tgt = to;
        }
    }
    // Haskell's S.map also collapses edges whose endpoints now coincide.
    content.edges.sort();
    content.edges.dedup();
    content.goals = std::sync::Arc::new(goals.into_iter().collect());
}

/// Refine one case using a prepared `matchToGoal` result (Sources.hs).
///
/// Rename the case by the source-wide shift, rewire premise endpoints when
/// needed, solve the match substitution with `SplitNow`, then substitute each
/// resulting system and restrict its bindings to the live goal's variables.
/// Every surviving equality branch retains its own system and fresh counter.
///
/// Source matching and its first substitution are prepared once by
/// [`prepare_source_match`]. The returned systems are still local to
/// `refineSource`: [`apply_source`] deduplicates them before instantiating
/// each survivor in the live counter scope.
fn refine_source_case(
    ctx: &crate::constraint::solver::context::ProofContext,
    prepared: &PreparedSourceMatch,
    case_sys: System,
) -> Result<Vec<System>, crate::prove::ProveError> {
    use crate::constraint::solver::reduction::{Reduction, SplitStrategy};
    let PreparedSourceMatch {
        renamed_abstract_node,
        prem_rewire,
        stable_vars,
        rename_shift,
        refine_seed,
        match_pairs,
    } = prepared;
    let mut renamed_case = rename_system_by(case_sys, *rename_shift);

    // `matchToGoal` (Sources.hs) rewires edges and premise/chain goals,
    // combining goal status when the rewritten keys coincide.
    if let Some((abstract_prem_idx, live_prem_idx)) = prem_rewire {
        let pat_prem = (*renamed_abstract_node, *abstract_prem_idx);
        let new_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
            (*renamed_abstract_node, *live_prem_idx);
        rewire_source_premise(&mut renamed_case, pat_prem, new_prem);
    }

    // `refineSubst` (Sources.hs) solves the match substitution with SplitNow
    // and substitutes each resulting system.
    //
    // Build `Equal (varTerm v) t` for each (v, t) in the match-subst,
    // then run them through the renamed case's Reduction.
    //
    // Refinement uses the local `avoid th` seed through `RefineFsScope`.
    // The scope ends before `apply_source` uses the live counter for
    // `someInst` and conjoins the case.
    // ---------------------------------------------------------------
    let _refine_fs = RefineFsScope::set(*refine_seed);
    let mut refined = Reduction::new(ctx, renamed_case);
    // HS-faithful `solveSubstEqs` (Reduction.hs):
    //   solveTermEqs split [Equal (varTerm v) t | (v, t) <- substToList subst]
    // builds `Equal (varTerm v) t` with no conditional flip.
    let term_eqs: Vec<_> = match_pairs
        .iter()
        .map(|(v, t)| {
            let pattern_var_term = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(*v));
            tamarin_term::rewriting::Equal {
                lhs: pattern_var_term,
                rhs: t.clone(),
            }
        })
        .collect();
    // -----------------------------------------------------------------
    // `solveTermEqs SplitNow` (Reduction.hs) branches over `performSplit`,
    // in Maude's unifier order.
    let arms = if term_eqs.is_empty() {
        // No refineSubst; the case continues as the sole arm.
        vec![refined.into_branch()]
    } else {
        let outcome = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs)?;
        refined.outcome_branches(outcome)
    };

    // Each arm continues from the post-refineSubst system with its own
    // equation store and FreshT counter (HS `DisjT` over `performSplit`,
    // Reduction.hs), substitutes it through the case, and restricts it to
    // the live goal's variables (`frees (cdGoal th)` after `set cdGoal
    // goalTerm`).
    let mut out = Vec::with_capacity(arms.len());
    for arm in arms {
        let mut refined = Reduction::new_inheriting(ctx, arm.sys, arm.counter);
        refined.subst_system()?;
        if refined.sys.eq_store().is_false() {
            continue;
        }
        restrict_eq_store_to_stable_vars(&mut refined.sys, stable_vars);
        out.push(refined.sys);
    }
    Ok(out)
}

/// The conjoin half of `_applySource` (Sources.hs) for one instantiated
/// case: `markGoalAsSolved` and `conjoinSystem` in the live reduction, whose
/// counter `maude` carries. Each conjoin branch keeps its own FreshT
/// continuation.
fn conjoin_source_case(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    case: &System,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<Vec<SystemBranch>, crate::prove::ProveError> {
    use crate::constraint::solver::reduction::{Reduction, SystemOutcome};

    let mut r = Reduction::new(ctx, live_sys.clone());
    r.maude = maude.clone();
    r.mark_goal_as_solved(live_goal);
    Ok(match r.conjoin_system(case)? {
        SystemOutcome::Contradictory => Vec::new(),
        SystemOutcome::Linear => vec![r.into_branch()],
        SystemOutcome::Cases(arms) => arms
            .into_iter()
            .map(|arm| Reduction::new_inheriting(ctx, arm.sys, arm.counter).into_branch())
            .collect(),
    })
}

// =============================================================================
// removeRedundantCases (Sources.hs)
// =============================================================================
//
// Only with bilinear pairing or multisets: normalise each case
// (`addNormSys`: rename non-stable variables in `varOccurences` order, then
// the rest, dropping name hints), `sortednubBy compareSystemsUpToNewVars`,
// and restore the survivors' input order.

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

/// Collect the distinct occurrence paths of non-node variables in rule nodes.
/// Path segments follow Haskell's `foldFreesOcc`. A node-sorted variable gets
/// its canonical index later in the whole-system free-variable traversal.
fn var_occurrences_nodes(
    sys: &crate::constraint::system::System,
) -> Vec<(
    tamarin_term::lterm::LVar,
    std::collections::BTreeSet<Vec<Seg>>,
)> {
    use std::collections::{BTreeMap, BTreeSet};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    fn funsym_occ_ctx(sym: &tamarin_term::function_symbols::FunSym) -> Seg {
        match tamarin_term::subsumption::occ_label(sym) {
            std::borrow::Cow::Borrowed(s) => Seg::Static(s),
            std::borrow::Cow::Owned(s) => Seg::shared(&s),
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
            Term::Lit(Lit::Var(v)) if v.sort != LSort::Node => {
                out.entry(*v).or_default().insert(ctx.materialize());
            }
            Term::Lit(_) => {}
            Term::App(sym, args) => {
                // HS `instance HasFrees (Term l)` `foldFreesOcc`
                // (LTerm.hs):
                //   FApp (NoEq o) as -> foldFreesOcc f ((opName):c) as
                //   FApp o        as -> mconcat $ map (foldFreesOcc f (show o:c)) as
                //                       -- AC or C symbols
                // For a NoEq function the args are descended as a LIST, so the
                // `HasFrees [a]` instance (LTerm.hs) prefixes EACH arg with
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
    // HS `instance HasFrees Fact` (Theory/Model/Fact.hs):
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
            seg: Seg::shared(&crate::fact::show_fact_tag_derived(&f.tag)),
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
    let mut out: BTreeMap<LVar, BTreeSet<Vec<Seg>>> = BTreeMap::new();
    // Map keys and values have distinct tuple paths. The sets collect each
    // path independently of the order in which the nodes are visited.
    for (nid, rule) in sys.nodes.iter() {
        if nid.sort != LSort::Node {
            out.entry(*nid).or_default().insert(vec![Seg::Static("0")]);
        }
        let v_ctx = Ctx {
            seg: Seg::Static("1"),
            parent: None,
        };
        visit_rule(rule, &v_ctx, &mut out);
    }
    out.into_iter().collect()
}

/// The variable rename of `renameDropNameHints sys` (Sources.hs),
/// as a binding store [`norm_sys_for_compare`] maps the system through:
///   1. `stableVarBindings`: every stable variable binds to itself.
///   2. `evalFresh … (avoid stableVars)`: the supply starts above the largest
///      stable index.
///   3. `renameDropNamehint (orderedVars sys)` imports the non-`Node` variables
///      of `varOccurences sys` in occurrence-set order first.
///   4. `renameDropNamehint sys` imports the rest, in the order
///      `instance HasFrees System` (System.hs) reaches them.
///
/// Every import draws an empty-named index of the variable's own sort
/// (`renameDropNamehint`, LTerm.hs), so a stable variable keeps its
/// name and every other one loses it.
fn compute_rename_map(
    sys: &crate::constraint::system::System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> Bindings {
    use tamarin_term::lterm::HasFrees;
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

/// HS `addNormSys` (Sources.hs):
/// `(modify sEqStore dropNameHintsBound) . renameDropNameHints`.
///
/// `renameDropNameHints` maps the system's free variables through the
/// canonical rename (`compute_rename_map`).  HS holds the set-like stores in
/// `Data.Set` / `Data.Map`, so its `mapFrees` rebuilds them and the renamed
/// stores come back sorted and duplicate-free; the port holds them in `Vec`s,
/// so this sorts and dedups them after the rename.  `dropNameHintsBound`
/// then rewrites every equation-store disjunct substitution into its
/// name-hint-free canonical form.
fn norm_sys_for_compare(
    sys: &crate::constraint::system::System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> crate::constraint::system::System {
    use std::sync::Arc;
    use tamarin_term::lterm::HasFrees;
    let rename = compute_rename_map(sys, stable_vars);
    let mut s = sys.clone().map_free(&mut |v| rn(&rename, &v));
    {
        let c = s.content_mut();
        Arc::make_mut(&mut c.nodes).sort_by_key(|a| a.0);
        c.edges.sort();
        c.edges.dedup();
        c.less_atoms.sort();
        c.less_atoms.dedup();
        for store in [&mut c.formulas, &mut c.solved_formulas, &mut c.lemmas] {
            store.sort();
            store.dedup();
        }
        let goals = Arc::make_mut(&mut c.goals);
        goals.sort_by(|a, b| a.0.cmp(&b.0));
        // `rename` is injective, so equal keys can only have been duplicate
        // before this pass. The survivor therefore cannot expose Rust's
        // first-wins `dedup_by` versus HS `M.fromList`'s last-wins choice.
        goals.dedup_by(|a, b| a.0 == b.0);
    }
    {
        let st = s.subterm_store_mut();
        for cs in [&mut st.subterms, &mut st.solved_subterms] {
            cs.sort_by(|a, b| a.hs_pair().cmp(&b.hs_pair()));
            cs.dedup_by(|a, b| a.hs_pair() == b.hs_pair());
        }
    }
    {
        let es = s.eq_store_mut();
        for disj in &mut es.conj {
            for sub in &mut disj.substs {
                *sub = sub.drop_name_hints();
            }
            disj.substs.sort();
            disj.substs.dedup();
        }
    }
    s
}

/// HS `compareRulesUpToNewVars` (Theory/Model/Rule.hs): the info, the
/// premises, the conclusions and the actions, with `new_vars` left out.
fn compare_rules_up_to_new_vars(
    a: &crate::rule::RuleACInst,
    b: &crate::rule::RuleACInst,
) -> std::cmp::Ordering {
    a.info
        .cmp(&b.info)
        .then_with(|| a.premises.cmp(&b.premises))
        .then_with(|| a.conclusions.cmp(&b.conclusions))
        .then_with(|| a.actions.cmp(&b.actions))
}

/// HS `compareSystemsUpToNewVars` (System.hs) over two systems that
/// `norm_sys_for_compare` has already normalised.  The nodes compare through
/// `compare_rules_up_to_new_vars` over both maps in `M.toAscList` order (HS
/// `compareNodesUpToNewVars`/`compareListsUpToNewVars`, System.hs,
/// which is the lexicographic order on the two lists).  When the nodes tie,
/// HS blanks that field in both records and falls back to the derived
/// `Ord System`, so the rest compares in HS's declaration order
/// (System.hs): edges, lessAtoms, lastAtom, subtermStore, eqStore,
/// formulas, solvedFormulas, lemmas, goals, nextGoalNr, sourceKind,
/// diffSystem.  `SystemContent` declares its fields in another order, so the
/// chain below names the HS one field by field.
fn compare_systems_up_to_new_vars(
    a: &crate::constraint::system::System,
    b: &crate::constraint::system::System,
) -> std::cmp::Ordering {
    let nodes = a
        .nodes
        .iter()
        .zip(b.nodes.iter())
        .map(|((x1, x2), (y1, y2))| {
            x1.cmp(y1)
                .then_with(|| compare_rules_up_to_new_vars(x2, y2))
        })
        .find(|o| o.is_ne())
        .unwrap_or_else(|| a.nodes.len().cmp(&b.nodes.len()));
    if nodes.is_ne() {
        return nodes;
    }
    a.compare_hs_fields_after_nodes(b)
        .then_with(|| a.next_goal_nr.cmp(&b.next_goal_nr))
        .then_with(|| a.source_kind.cmp(&b.source_kind))
        // Rust carries the selected diff side; HS stores only whether this is
        // a diff system, so LHS and RHS compare equal at this final field.
        .then_with(|| a.side.is_some().cmp(&b.side.is_some()))
}

/// Sort and deduplicate with the survivor rules of Haskell's `sortednubBy`
/// (`lib/utils/src/Extension/Prelude.hs`). Equal elements at the start of a
/// run keep the later element. Equal elements across runs keep the one from
/// the left run.
fn sortednub_by<T, C>(cmp: &C, xs: Vec<T>) -> Vec<T>
where
    C: Fn(&T, &T) -> std::cmp::Ordering,
{
    use std::cmp::Ordering::*;

    fn sequences<T, C>(cmp: &C, xs: Vec<T>) -> Vec<Vec<T>>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let mut input = xs.into_iter().peekable();
        let mut runs = Vec::new();
        while let Some(mut first) = input.next() {
            loop {
                let Some(mut last) = input.next() else {
                    runs.push(vec![first]);
                    return runs;
                };
                let direction = cmp(&first, &last);
                if direction == Equal {
                    first = last;
                    continue;
                }

                let mut run = vec![first];
                while let Some(next) = input.next_if(|next| cmp(&last, next) == direction) {
                    run.push(last);
                    last = next;
                }
                run.push(last);
                if direction == Greater {
                    run.reverse();
                }
                runs.push(run);
                break;
            }
        }
        runs
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

/// For bilinear pairings or multisets, deduplicate cases by their normalized
/// systems using `sortednub_by`, then restore the survivors' input order.
pub(crate) fn remove_redundant_cases<T, F>(
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
    // `sortOn fst` are the identity on it, so skip the normalisation
    // (`norm_sys_for_compare` is pure, so eliding it for len<2 cannot
    // perturb fresh-var numbering, goal order, or stdout).
    if cases.len() < 2 {
        return cases;
    }
    deduplicate_normalized_cases(
        cases
            .into_iter()
            .map(|case| (norm_sys_for_compare(get_sys(&case), stable_vars), case)),
    )
}

fn deduplicate_normalized_cases<T>(cases: impl IntoIterator<Item = (System, T)>) -> Vec<T> {
    let decorated = cases.into_iter().enumerate().collect();
    // sortednubBy (\(_,(_,x)) (_,(_,y)) -> compareSystemsUpToNewVars x y)
    let mut deduped = sortednub_by(
        &|(_, (a, _)), (_, (b, _))| compare_systems_up_to_new_vars(a, b),
        decorated,
    );
    // sortOn fst : restore original-index order.
    deduped.sort_by_key(|a| a.0);
    deduped.into_iter().map(|(_, (_, c))| c).collect()
}

#[cfg(test)]
#[path = "sources_tests.rs"]
mod tests;
