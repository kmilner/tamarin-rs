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
//!   (`solve_with_source_cases*` / `apply_source_case_*`).
//! - Removing redundant cases (`remove_redundant_cases`).
//!
//! Alongside the full machinery it also exposes the public data shapes
//! and the `IntegerParameters` config used by the rest of the solver.

use crate::constraint::solver::reduction::SystemBranch;
use crate::constraint::system::System;
use tamarin_term::bind::Bindings;
use tamarin_term::lterm::frees;

// =============================================================================
// Precompute-mode marker
// =============================================================================
//
// Source refinement records dangling premises for subsequent saturation passes.
// The guard scopes that mode to the current worker's branch solve.

thread_local! {
    static IN_PRECOMPUTE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Clone a source-case branch, install its equation store, and continue from
/// the split's fresh counter. Shared by the action and premise fan-outs.
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

pub(crate) fn in_precompute_mode() -> bool {
    IN_PRECOMPUTE.with(|c| c.get())
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

/// Enumerate the raw cases for one source goal under the safety restrictions.
/// Normalize the surviving cases with their full substitutions. Refinement
/// later restricts each substitution to the free variables of the source goal.
pub(crate) fn initial_source_cases(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Result<Vec<SourceCase>, crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};

    let mut sys = System::empty();
    sys.source_kind = Some(crate::constraint::system::SourceKind::RawSources);
    // HS-faithful (CloseRule.hs): source precomputation gets ONLY
    // safety restrictions.  Non-safety restrictions (e.g.
    // `Start_implies_Stop = All x #i. Start(x)@i ⇒ Ex #j. Stop(x)@j`)
    // would fire `insertImpliedFormulas` during saturate, spawning Stop
    // ActionG / node via `solveUniqueActions`, which would re-open B
    // premise → another Step → another A premise → another Start →
    // restriction fires again → Cyclic.  HS skips this entire chain by
    // filtering to safety formulas at `CloseRule.hs`.
    sys.insert_lemmas(ctx.safety_restrictions.iter().cloned());
    let mut red = Reduction::new(ctx, sys);
    red.insert_goal(goal.clone());
    // HS-faithful: `solveGoal goal` (Goals.hs) marks the goal
    // BEFORE invoking the solver, since unification inside the solver
    // can rewrite the goal's fact terms.
    red.mark_goal_as_solved(goal);

    let outcome = match goal {
        Goal::Action(node, fa) => red.solve_action_goal(node, fa)?,
        Goal::Premise(prem, fa) => red.solve_premise_goal(prem, fa)?,
        _ => return Ok(Vec::new()),
    };

    // Every solver branch descends from `red.sys`, so it already carries the
    // safety restrictions installed above.
    let normalize_and_keep = |ctx: &ProofContext, sys: System, counter: u64| {
        crate::constraint::solver::simplify::simplify_system_with_fanout_seeded_with_counters(
            ctx, sys, counter,
        )?
        .into_iter()
        .filter_map(|SystemBranch { sys: s, .. }| {
            if s.eq_store().is_false() {
                return None;
            }
            match crate::constraint::solver::contradictions::contradictions(ctx, &s) {
                Err(error) => return Some(Err(error)),
                Ok(cs) if !cs.is_empty() => return None,
                Ok(_) => {}
            }
            // `initialSource` (Sources.hs) retains every substitution binding.
            // Rule-internal variables participate in `avoid th`, which seeds
            // saturation's fresh supply. `refineSource` restricts bindings to
            // the abstract goal's stable variables after refinement.
            Some(Ok(s))
        })
        .collect::<Result<Vec<_>, crate::prove::ProveError>>()
    };
    let linear_counter = red.maude.fresh_counter_peek();
    Ok(match outcome {
        GoalCases::Linear => normalize_and_keep(ctx, red.sys, linear_counter)?
            .into_iter()
            .map(|s| (vec!["only".into()], s))
            .collect(),
        GoalCases::LinearNamed(name) => {
            let names = (!name.is_empty())
                .then_some(name)
                .into_iter()
                .collect::<Vec<_>>();
            normalize_and_keep(ctx, red.sys, linear_counter)?
                .into_iter()
                .map(|s| (names.clone(), s))
                .collect()
        }
        GoalCases::Cases(systems) => {
            // Keep initial sources themselves ordered: their simplification
            // can consult already populated source cells. Cases of ONE source
            // share that same read-only view and can normalize independently.
            // Publish only after every case has finished, in the original order.
            let precompute = in_precompute_mode();
            let refine_floor = crate::constraint::solver::reduction::refine_floor();
            let ctx = ctx.clone();
            let cases = tamarin_utils::parallel::try_map(systems, move |branch| {
                let _mode =
                    PrecomputeModeGuard(IN_PRECOMPUTE.with(|cell| cell.replace(precompute)));
                let _floor = RefineFsScope::floor(refine_floor);
                #[cfg(test)]
                super::cancellation_tests::checkpoint(
                    &ctx,
                    super::cancellation_tests::Work::InitialSources,
                );
                // This case is already required. Only borrow a warm process here.
                let pooled = ctx
                    .maude_pool
                    .as_ref()
                    .and_then(|pool| pool.try_take_idle_owned());
                let maude = pooled.as_ref().map_or(&ctx.maude, |p| p.handle());
                let worker_ctx =
                    ctx.with_swapped_maude(maude.with_fresh_counter_next(branch.counter));
                let names = (!branch.name.is_empty())
                    .then_some(branch.name)
                    .into_iter()
                    .collect::<Vec<_>>();
                Ok::<_, crate::prove::ProveError>(
                    normalize_and_keep(&worker_ctx, branch.sys, branch.counter)?
                        .into_iter()
                        .map(|s| (names.clone(), s))
                        .collect::<Vec<_>>(),
                )
            })?;
            cases.into_iter().flatten().collect()
        }
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
    // (see FunctionSymbols.hs; mirrored by the `enum FunSym`
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
    // symbols (FunctionSymbols.hs).  Includes both constructors
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
        out.push(Source::lazy(goal));
    }

    out
}

/// Compute the source label that would identify a KU-action source
/// matching the given live `fa` (a KU fact with a single term).
/// Mirrors `source_label`'s KU arm — used at the runtime filterCases
/// step where we have the live fa (not the source).  Equivalent to
/// Haskell's full-`Source` equality (Sources.hs,
/// `filterCases usedCase cds = filter (\x -> usedCase /= x) cds`)
/// under the precompute invariant: `source_patterns` emits
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

    // Step 2 (Haskell `saturateSources`): re-saturate with the
    // assumption-augmented cases.  This step is critical — it
    // propagates the typing constraints through the recursive premise
    // expansion, pruning cases whose continuation introduces premises
    // that violate the [sources] typing.  Haskell threads the SAME
    // `paramSaturationLimit` into this saturate as into the raw one
    // (`refineWithSourceAsms parameters … = saturateSources parameters …`,
    // Sources.hs), so a `-s` override applies here too — the
    // ctx carries it.
    let limit = ctx.parameters.saturation_limit();
    let saturated = saturate_sources_with_simp(intermediate, limit, ctx)?;

    // Step 3 (Haskell `removeFormulas`): strip formulas + solved
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
        // Keep zero-case sources — see the Step-1 note above.
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
        let (branches, took_step) = {
            let _precompute_guard = PrecomputeModeGuard::enter();
            solve_all_safe_goals(ctx, sys, ths_snapshot, name_list, source_avoid)?
        };
        changed |= took_step;
        still_distinct &= branches.len() <= 1;
        // HS-faithful `refineSource` (Sources.hs):
        //   map (second (modify sSubst (restrict stableVars)))
        // restricts each branch's eq-store subst to the STABLE vars
        // (frees of the source's `cdGoal`) before dedup.  This
        // narrows the subst to bindings the runtime case-matcher
        // cares about; internal fresh bindings are dropped so
        // equivalent branches dedupe.  Dedup itself is applied ONCE
        // across the flat preDedup list (after the loop, see below).
        // `stable_vars` was computed once before the loop above.
        for (mut branch_sys, branch_name_list) in branches {
            // Apply `restrict stableVars` to the branch's subst.
            let restricted_pairs: Vec<_> = branch_sys
                .eq_store()
                .subst
                .to_list()
                .into_iter()
                .filter(|(v, _)| stable_vars.contains(v))
                .collect();
            branch_sys.invalidate_max_var_idx_cache();
            branch_sys.eq_store_mut().subst =
                tamarin_term::subst::Subst::from_list(restricted_pairs);
            if still_distinct {
                still_distinct = original.as_ref() == Some(&branch_sys);
            }
            deferred_filtered.push((branch_name_list, branch_sys));
        }
    }
    // HS-faithful `removeRedundantCases` (Sources.hs): applies
    // ONCE to the flat list of post-refine branches across all input
    // cases.  Gated on BP/MSet per HS short-circuit (`removeRedundantCases`
    // in Sources.hs returns the input unchanged outside BP/MSet).
    // Compute independent comparison keys across workers for larger sources.
    // Deduplication consumes those keys in the original case order.
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

/// HS `showSaturationSteps` (Sources.hs): when set, `saturateSources`
/// traces `[Saturating Sources] …` progress lines to stderr.
///
/// The value is `closeTheoryWithMaude`'s last argument (CloseRule.hs),
/// which every CLI theory close passes as `True` — `closeTranslatedTheory`
/// (TheoryLoader.hs, the batch/`--prove`/`--precompute-only`/web load),
/// `closeTheory` (Prover.hs) and `applyPartialEvaluation`
/// (Prover.hs).  Only the two auxiliary closes pass `False`: the NDC
/// deduction check (CloseRule.hs) and the message-derivation check
/// (MessageDerivationChecks.hs).  HS then emits nothing on theories whose
/// proofs never force `crcRawSources`/`crcRefinedSources`, since `trace`
/// fires at thunk-force time.
///
/// Re-simplify every grafted source case so newly-fired implied formulas can
/// prune it. Mirrors Haskell's `saturateSources`, including its iteration cap.
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
        // Haskell-faithful `goodTh` filter (Sources.hs):
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
        // driven `saturateSources` (`Sources.hs`).  This is
        // what propagates typing assumptions transitively: each safe
        // goal we solve adds a new node/edge whose fact constraints
        // get unified against the assumption's pattern, eventually
        // pruning typing-violating cases.  Bare simplify alone misses
        // most of these because `insert_implied_formulas_pass` relies on
        // term-shape match against system actions, which only get
        // grafted by goal-solving.
        // HS refines each source against the same snapshot. The ordered map
        // keeps each goal with its own cases, including an empty case list.
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
    // HS-faithful final-truncate pass: applies `combine` one more
    // time per case with empty `new_names`, which (per Sources.hs
    // `combine (n:_) _ = [n]`) truncates any multi-element name list
    // to its first non-coerce element.  HS's saturate normally
    // achieves this via iter-2's `combine names names'` on iter-1's
    // multi-element output, but Rust's change-detection skips iter-2
    // when only safe-goal steps fired (avoiding PRF over-refinement).
    // Applying the
    // truncate as a name-only pass matches HS's final case-name
    // display without re-running solveAllSafeGoals.
    for src in current.iter_mut() {
        let mut cases = src.cases_take();
        for (name_list, _) in &mut cases {
            if name_list.len() > 1 {
                let truncated = combine_case_names_list(name_list, &[]);
                *name_list = truncated;
            }
        }
        src.set_cases(cases);
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

/// Structural equality modulo fresh variable renaming.  Mirrors HS
/// `eqModuloFreshnessNoAC` (LTerm.hs).  Two terms are equal iff
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
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::goals::dispatch_solve_goal;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};
    use crate::constraint::solver::simplify::simplify_system_with_fanout_seeded_with_counters;
    use crate::fact::FactTag;

    struct Entry {
        sys: System,
        /// Keep step names separate so `combine` can select the first non-coercion step.
        name: Vec<String>,
        used: std::collections::BTreeSet<String>,
        chains_left: i64,
        /// Skip chain conclusions equal modulo freshness to the last one solved.
        last_chain_term: Option<tamarin_term::lterm::LNTerm>,
        /// Contributes to saturation progress when this branch survives.
        took_step: bool,
        fresh_counter: u64,
    }
    // HS-faithful `avoid th` (Sources.hs): thread `source_avoid` as the
    // fresh-counter floor for the WHOLE refinement of this case — including
    // the floor-0 `simplify_system_with_fanout` sub-reductions where the
    // `[sources]`-lemma `Ex #j` node is drawn — via a thread-local, restored
    // on drop.  Without it, that sub-reduction reseeds at the per-case
    // `avoid se`, undershooting HS for any case below the source-wide max.
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
        // HS-faithful `simplifySystem` in DisjT (Sources.hs):
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
        // onto worklist with same (name, used, chains_left,
        // last_chain_term), and process the head.  Empty result drops
        // the branch (HS mzero-equivalent).
        // HS-faithful: propagate the DisjT fan-out from simplifySystem
        // (unconditional).
        let post_simp = simplify_system_with_fanout_seeded_with_counters(ctx, sys, fresh_counter)?;
        // Pop one sibling to continue with; push the rest back for
        // later processing.  Match HS's Disj-monad insertion order:
        // first sibling processed first (LIFO worklist → push tail
        // reversed so the head pops next).
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
        let contras = contradictions(red.ctx, &red.sys)?;
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
        // Haskell-faithful Goal-Ord (Goals.hs `M.toList sGoals`).
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
        // HS-faithful `lastChainTerm` filter (Sources.hs):
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
        // HS-faithful `lastChainTerm` chain-goal filter (Sources.hs),
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
        // HS-faithful: HS's `safeGoal` predicate (Sources.hs)
        // marks Split/Disj/Subterm safe when `splitAllowed`.  Split is
        // allowed during saturate when `splitAllowed` (HS's
        // `safeGoal SplitG = doSplit`, Sources.hs), regardless
        // of precompute/runtime.  In practice split_allowed is rarely
        // true during saturate (chain goals stay open), so this is a
        // no-op for most cases — but it is the HS-faithful behaviour.
        let is_safe = |g: &Goal| -> bool {
            match g {
                Goal::Chain(_, _) => {
                    if chains_left > 0 {
                        true
                    } else {
                        // HS `safeGoal` reports an exhausted chain budget via
                        // `traceChainLimit` (Sources.hs), gated by
                        // `showSaturationSteps`, keeping auxiliary derivation
                        // and NDC checks silent.
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
                // HS-faithful: `safeGoal SplitG = doSplit = splitAllowed`
                // (Sources.hs).
                Goal::Split(_) => split_allowed,
            }
        };
        // HS-faithful: kdPremGoals uses UNFILTERED goals (Sources.hs),
        // safeGoals uses FILTERED.  Match HS by deriving each
        // candidate from the correct source.  `safeGoals` is a SHARED lazy
        // list in HS — each element is tested by `safeGoal` at most once
        // per iteration — so compute the head once and reuse it for the
        // pick fallback, the chains decrement, and the lastChainTerm
        // update.  (The `[Open Chains]` trace count inside `is_safe` still
        // differs from HS's demand-driven forcing — a documented deliberate
        // divergence; line content and phase placement match.)
        let first_safe = filtered_goals.iter().find(|(g, _)| is_safe(g));
        // HS `remainingChains safeGoals` (Sources.hs) keys
        // the chains decrement on the HEAD OF `safeGoals` — not on the goal
        // actually solved — so a kd-prem step still burns a chain tick
        // whenever the first safe goal is a chain, and a chain-prem1 kd
        // pick burns none when it isn't.
        let safe_head_is_chain = matches!(first_safe, Some((Goal::Chain(_, _), _)));
        let pick = goals
            .iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or(first_safe);
        // HS-faithful update of `lastChainTerm'` (Sources.hs):
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
            let inner_outcome = dispatch_solve_goal(&mut red, &goal)?;
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
                    // names)` is True — Sources.hs).  The
                    // outer `saturateSources` re-iterates on ANY step, not
                    // just source-picks.
                    // HS-faithful: mark THIS branch as having taken a step;
                    // it only counts if the branch survives to a leaf.
                    worklist.push(Entry {
                        sys: red.sys,
                        name,
                        used,
                        chains_left: new_chains_left,
                        last_chain_term: new_last_chain_term.clone(),
                        took_step: true,
                        fresh_counter: red.maude.fresh_counter_peek(),
                    });
                }
                GoalCases::LinearNamed(sub_name) => {
                    // HS-faithful: INSIDE `solveAllSafeGoals.solve`
                    // (Sources.hs), step names are APPENDED
                    // via `caseNames ++ x` — not combined via the
                    // coerce-skipping `combine`.  `combine` runs at
                    // `refineSource` level once per saturate-outer
                    // iter (between calls to solveAllSafeGoals), not
                    // per step within solveAllSafeGoals.
                    // HS-faithful change flag: a named safe-goal step is a
                    // step → `not (null names)` True → outer saturate
                    // re-iterates (Sources.hs).
                    let mut new_name = name.clone();
                    append_step_name_list(&mut new_name, &sub_name);
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
                    // order from `solveChain` (Goals.hs),
                    // matching HS's case ordering at NSPK3/NSLPK3
                    // types and similar source-saturated lemmas.
                    //
                    // HS-faithful change flag: a forking safe-goal step is a
                    // step → each forked branch inherits took_step=true; it
                    // only counts toward `changes` if that branch survives.
                    for branch in cases.into_iter().rev() {
                        let mut new_name = name.clone();
                        append_step_name_list(&mut new_name, &branch.name);
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

        // No safe goal — try source-pick (Haskell's third disjunct
        // of `nextStep`).
        if ths.is_empty() {
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        // Pick the first Useful KU goal with a matching source. A branch can
        // use each source label once, across all cases with that label.
        use crate::constraint::solver::annotated_goals::Usefulness;
        let useful_kus: Vec<(crate::constraint::constraints::NodeId, crate::fact::LNFact)> = goals
            .iter()
            .filter_map(|(g, looping)| match g {
                Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
                    if crate::constraint::solver::goals::goal_usefulness(g, *looping, &red.sys)
                        != Usefulness::Useful
                    {
                        return None;
                    }
                    if let Some(label) = ku_source_label_for_fa(fa)
                        && used.contains(&label)
                    {
                        return None;
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
        // Iterate useful goals in order; first one with a matching
        // source wins (Haskell `asum`).
        let mut picked: Option<(
            crate::constraint::constraints::NodeId,
            crate::fact::LNFact,
            Vec<(String, crate::constraint::system::System, u64)>,
        )> = None;
        let mut matched = false;
        for (i_cand, fa_cand) in useful_kus {
            match solve_with_source_cases_action(
                ctx,
                Some(ths),
                &red.sys,
                &i_cand,
                &fa_cand,
                &red.maude,
                Some(red.maude.fresh_counter_peek()),
            )? {
                SourceMatch::NoMatch => continue,
                SourceMatch::Matched(case_pairs) => {
                    matched = true;
                    if !case_pairs.is_empty() {
                        picked = Some((i_cand, fa_cand, case_pairs));
                    }
                    break;
                }
            }
        }
        if !matched {
            // No useful goal has a matching source — Haskell's
            // `nextStep = Nothing` → `return caseNames` (current
            // state survives).
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        let Some((_i, fa, case_pairs)) = picked else {
            // A matching source with no surviving cases makes
            // `disjunctionOfList []` fail, dropping this branch.
            continue;
        };
        // Source-label-based filter (Haskell-faithful): the picked
        // useful_ku's source label was verified NOT in `used` above,
        // so all case_pairs from this single source are available.
        // No per-case-name filter needed.
        // Fork: try each viable candidate as a separate branch.
        // Mirrors Haskell `asum [solveWithSourceAndReturn ctxt ths g
        // | g <- usefulGoals]` — collects all branches that survive.
        let mut any_branched = false;
        for (case_name, sys_cand, branch_counter) in case_pairs {
            let mut new_used = used.clone();
            // Haskell-faithful: track SOURCE LABEL.
            if let Some(label) = ku_source_label_for_fa(&fa) {
                new_used.insert(label);
            } else {
                new_used.insert(case_name.clone());
            }
            // HS-faithful: source-pick step APPENDS its name to `caseNames`
            // (Sources.hs `(caseNames ++ x)`); `combine` runs only at the
            // refineSource boundary, not per-step inside solveAllSafeGoals.
            let mut new_name = name.clone();
            append_step_name_list(&mut new_name, &case_name);
            worklist.push(Entry {
                sys: sys_cand,
                name: new_name,
                used: new_used,
                chains_left,
                last_chain_term: new_last_chain_term.clone(),
                took_step: true,
                fresh_counter: branch_counter,
            });
            any_branched = true;
        }

        debug_assert!(any_branched, "a non-empty matched source produces a branch");
    }

    // HS-faithful: apply `refineSource`'s `combine(existing, step_names)`
    // now that solveAllSafeGoals has finished accumulating.  `combine`
    // strips leading "coerce" entries from `initial_name`; if anything
    // non-coerce remains it's the only segment we keep (the rest of
    // the chain is discarded), otherwise the accumulated step_names
    // take over.  Mirrors Sources.hs exactly.
    let branches: Vec<(System, Vec<String>)> = finished
        .into_iter()
        .map(|(sys, step_names_list)| {
            let combined = combine_case_names_list(&initial_name, &step_names_list);
            (sys, combined)
        })
        .collect();
    Ok((branches, any_step_taken))
}

/// Refine, deduplicate, instantiate, and conjoin one already-matched source.
/// Shared by premise and action source application so their FreshT branch
/// semantics cannot drift apart.
fn apply_prepared_source_cases(
    ctx: &crate::constraint::solver::context::ProofContext,
    cases: Vec<SourceCase>,
    prepared: &PreparedSourceMatch,
    sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    red_maude: &tamarin_term::maude_proc::MaudeHandle,
    fork_base: u64,
) -> Result<Vec<(String, System, u64)>, crate::prove::ProveError> {
    // HS `refineSource` first refines every case, then removes redundant
    // refined systems, and only then runs `_applySource` (someInst + conjoin)
    // for each survivor. The source-case disjunction sits below FreshT, so
    // every survivor starts at the same pick-time counter and returns its own
    // continuation.
    let mut refine_arms = Vec::new();
    for (name, case_sys) in cases {
        let case_label = case_name_list_to_string(&name);
        refine_arms.extend(
            refine_source_case(ctx, prepared, case_sys)?
                .into_iter()
                .map(|arm| (case_label.clone(), arm)),
        );
    }

    let keep_vars = tamarin_term::lterm::frees(live_goal);
    let stable_vars = keep_vars.iter().copied().collect();
    let msig = ctx.maude.maude_sig();
    let refine_arms = remove_redundant_cases(
        msig.enable_bp,
        msig.enable_mset,
        &stable_vars,
        |(_, arm): &(String, RefinedArm)| &arm.sys,
        refine_arms,
    );
    let mut out = Vec::new();
    for (case_label, arm) in refine_arms {
        let arm = instantiate_refined_arm(arm, &keep_vars, red_maude, fork_base);
        red_maude.reset_counter_to(arm.branch_counter);
        for out_arm in conjoin_refine_arm(ctx, sys, live_goal, arm, Some(red_maude))? {
            out.push((case_label.clone(), out_arm.sys, out_arm.cont));
        }
    }
    Ok(out)
}

/// Haskell-faithful `applySource` driver for premise goals. A matched source
/// remains matched even when all of its cases disappear during refinement.
pub(crate) fn solve_with_source_cases_ctx(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    goal_prem_idx: crate::rule::PremIdx,
    fa_prem: &crate::fact::LNFact,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
) -> Result<SourceMatch<(String, System, u64)>, crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;

    // HS's `filterCases` (Sources.hs) operates only inside
    // `solveAllSafeGoals` (saturate), not at runtime.  HS's runtime
    // `solveWithSource` (ProofMethod.hs, the
    // `(intercalate "_" <$>) (solveWithSource ctxt ths goal)` call site)
    // passes the FULL source
    // list every call: `solveWithSource ctxt ths goal` where `ths =
    // pcSources ctxt`.  Re-applying the same source at multiple proof
    // positions is normal HS behaviour: each saturated case has its
    // internal premise goals pre-marked solved, so `conjoinSystem` +
    // `simplifySystem`'s DG4-Fresh-uniqueness → DG3 cascade collapses
    // the grafted case onto existing nodes.  Filtering already-used cases
    // here would instead create unmerged Step/Start/Fresh nodes.

    // HS `matchToGoal` (Sources.hs; `maybeMatcher`) decides Just/Nothing for the
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
    // (Theory/Proof.hs), NOT a runtime bare-rule graft.
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
    let live_goal = Goal::Premise((*goal_node, goal_prem_idx), fa_prem.clone());
    let Some((cases, prepared)) = find_prepared_source(ctx, None, &live_goal)? else {
        return Ok(SourceMatch::NoMatch);
    };
    // HS FreshT-threading (`_applySource`, Sources.hs): the
    // live counter at the pick.  `disjunctionOfList cdCases` forks the
    // DisjT layer BELOW FreshT, so every (case × refineSubst-arm)
    // branch's someInst+conjoin draws start from an independent COPY
    // of this value — the premise-path twin of the action path's
    // `fork_base` in `solve_with_source_cases_action`.
    let red_maude = red_maude.expect("runtime source application requires a live counter");
    let fork_base = red_maude.fresh_counter_peek();
    // HS-faithful: an empty `out` (all cases contradictory) still counts
    // as a successful `solveWithSource` when the abstract `matchToGoal`
    // would have matched — return `Some(empty)` so the dispatcher emits
    // `by` (no children) rather than falling through to runtime.
    Ok(SourceMatch::Matched(apply_prepared_source_cases(
        ctx, cases, &prepared, sys, &live_goal, red_maude, fork_base,
    )?))
}

/// Haskell-faithful `applySource` path for KU action goals: one-way matching,
/// `someInst keepVarBindings`, and `conjoinSystem`.
#[track_caller]
pub(crate) fn solve_with_source_cases_action(
    ctx: &crate::constraint::solver::context::ProofContext,
    iteration: Option<&[Source]>,
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    red_maude: &tamarin_term::maude_proc::MaudeHandle,
    precompute_fork_base: Option<u64>,
    // Fourth tuple element: per-output-entry live-counter continuation
    // (HS FreshT-threading — the producing branch's fork + own draws).
) -> Result<SourceMatch<(String, System, u64)>, crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;

    // Only KU-tagged Action goals consult action sources.
    if fa_live.tag != FactTag::Ku || fa_live.terms.len() != 1 {
        return Ok(SourceMatch::NoMatch);
    }
    let live_goal = Goal::Action(*goal_node, fa_live.clone());
    let Some((cases_iter, prepared)) = find_prepared_source(ctx, iteration, &live_goal)? else {
        return Ok(SourceMatch::NoMatch);
    };
    // HS-faithful `applySource`/`solveWithSource` (Sources.hs):
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
        return Ok(SourceMatch::Matched(Vec::new()));
    }
    let fork_base = precompute_fork_base.unwrap_or_else(|| red_maude.fresh_counter_peek());
    Ok(SourceMatch::Matched(apply_prepared_source_cases(
        ctx, cases_iter, &prepared, sys, &live_goal, red_maude, fork_base,
    )?))
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
/// matching HS's `intercalate "_" names'` (ProofMethod.hs).
pub fn case_name_list_to_string(names: &[String]) -> String {
    names.join("_")
}

/// HS-faithful `combine` (Sources.hs):
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
// display name (HS `combine`, Sources.hs, ported in
// `combine_case_names_list`; joined with `intercalate "_"`, ProofMethod.hs).
// Use it verbatim — never re-split on `_`, which would corrupt function symbols
// whose names contain `_` (e.g. `c_KDF_SKc` → `SKc`).

/// `restrict` the system's eq-store `subst` (`sSubst`) to bindings
/// whose KEY var is in `stable_vars`.  Mirrors Haskell's
/// `modify sSubst (restrict stableVars)` inside `refineSource`
/// (Sources.hs).  All bindings keyed on rule-internal vars
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
    // Haskell's `restrict` (SubstVFree.hs; call site
    // Sources.hs `modify sSubst (restrict stableVars)`) is a
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

/// Continue one retained refine arm through Haskell's `someInst`.  The
/// source-case disjunction is below FreshT, so every sibling starts from the
/// same pick-time counter and carries only its own draws onward.
fn instantiate_refined_arm(
    arm: RefinedArm,
    keep_vars: &[tamarin_term::lterm::LVar],
    maude: &tamarin_term::maude_proc::MaudeHandle,
    fork_base: u64,
) -> RefineArm {
    maude.reset_counter_to(fork_base);
    let freshened_case = some_inst_system(arm.sys, keep_vars, maude);
    RefineArm {
        freshened_case,
        branch_counter: maude.fresh_counter_peek(),
    }
}

/// Result of probing the source list for a goal.  A matched source with no
/// surviving cases is semantically different from no matching source:
/// Haskell's `Maybe Reduction` takes the source path in the former case and
/// the ordinary goal solver only in the latter.
pub(crate) enum SourceMatch<T> {
    NoMatch,
    Matched(Vec<T>),
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
    live_node: tamarin_term::lterm::LVar,
    live_fact: crate::fact::LNFact,
    rename_shift: i128,
    refine_seed: u64,
    match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>,
}

fn find_prepared_source(
    ctx: &crate::constraint::solver::context::ProofContext,
    iteration: Option<&[Source]>,
    live_goal: &crate::constraint::constraints::Goal,
) -> Result<Option<(Vec<SourceCase>, PreparedSourceMatch)>, crate::prove::ProveError> {
    // Goal matching uses the layout alone. Force the proof's sources only
    // after finding a candidate. Saturation supplies its iteration directly.
    let matches = |source: &Source| source_goal_may_match(&source.goal, live_goal);
    let materialized;
    let sources = match iteration {
        Some(sources) => sources,
        None if !ctx.full_sources.iter().any(matches) => return Ok(None),
        None => {
            materialized = ctx.ensure_saturated()?;
            &materialized
        }
    };
    for source in sources.iter().filter(|source| matches(source)) {
        if let Some(prepared) = prepare_source_match(ctx, source, live_goal)? {
            return Ok(Some((source.cases_or_empty(), prepared)));
        }
    }
    Ok(None)
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
        match tamarin_term::unification::solve_match_lterm::<tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name,
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
                    crate::prove::ProveError::Maude(format!("source matching failed: {error}"))
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
        live_node,
        live_fact: live_fact.clone(),
        rename_shift,
        refine_seed,
        match_pairs,
    }))
}

/// One post-`refineSubst` arm, before `someInst`.  Action-source arms are
/// deduplicated in this compact form so rejected arms never clone and
/// freshen an entire System.
struct RefinedArm {
    sys: System,
}

/// One surviving arm at the conjoin boundary of HS's `_applySource`.
struct RefineArm {
    /// someInst result — the freshened case sub-system to conjoin.
    freshened_case: System,
    /// HS FreshT-threading: the live counter position right after this
    /// branch's `someInst` draws.  HS `_applySource` (Sources.hs)
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
    /// This branch's live-counter continuation (HS FreshT-threading):
    /// the fork plus this branch's own someInst + conjoin + step-12-arm
    /// + close-chains draws.
    cont: u64,
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

/// Refine half of Haskell's `applySource` (Sources.hs):
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
/// And `matchToGoal` (Sources.hs):
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
/// edges AND premise/chain goals onto the live premise index (upstream #958).
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
///     Rewire the renamed case's edges and premise/chain goals from the
///     source pattern's premise index onto the live one.
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
/// (Reduction.hs; `performSplit`), whose `DisjT`
/// layer replicates the WHOLE remaining continuation per disjunct — so
/// each arm carries its own `sEqStore` into the subsequent `substSystem`
/// / `markGoalAsSolved` / `conjoinSystem` steps.  An empty Vec means the
/// case dropped (match-fail, refineSubst-contradictory, …).
///
/// Stopping at the conjoin boundary lets the caller run HS's
/// `removeRedundantCases` (Sources.hs, keyed on the returned
/// refined systems) BEFORE calling [`conjoin_refine_arm`] on
/// the survivors only — so the expensive bilinear `conjoinSystem`
/// re-narrow is paid only for cases HS actually keeps.
///
/// Case-name disambiguation: callers push one entry per returned arm.
/// When the same `case_label` shows up twice, the proof-method
/// dispatcher appends `_case_N` per HS's `uniqueListBy ... distinguish
/// cases` (ProofMethod.hs, with `uniqueListBy` at
/// ProofMethod.hs and `distinguish` at ProofMethod.hs).
fn refine_source_case(
    ctx: &crate::constraint::solver::context::ProofContext,
    prepared: &PreparedSourceMatch,
    case_sys: System,
) -> Result<Vec<RefinedArm>, crate::prove::ProveError> {
    use crate::constraint::solver::reduction::{Reduction, SolveOutcome, SplitStrategy};
    let PreparedSourceMatch {
        renamed_abstract_node,
        prem_rewire,
        live_node,
        live_fact: fa_live,
        rename_shift,
        refine_seed,
        match_pairs,
    } = prepared;
    let mut renamed_case = rename_system_by(case_sys, *rename_shift);

    // ---------------------------------------------------------------
    // A.2.5: upstream #958 moves both edges and solved premise/chain goals,
    // combining goal status when the rewritten keys coincide.
    if let Some((abstract_prem_idx, live_prem_idx)) = prem_rewire {
        let pat_prem = (*renamed_abstract_node, *abstract_prem_idx);
        let new_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
            (*renamed_abstract_node, *live_prem_idx);
        rewire_source_premise(&mut renamed_case, pat_prem, new_prem);
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
    // refineSubst fan-out (HS Reduction.hs; `performSplit`).
    //
    // HS's `solveTermEqs SplitNow` calls
    //     disjunctionOfList $ performSplit eqs2 splitId
    // when the AC unifier produces multiple disjunctive results.  RS's
    // `solve_term_eqs` returns `SolveOutcome::Cases(arms)` when N>1
    // AC arms survive per-arm simp; it does NOT install any arm into
    // `self.sys.eq_store()` in that case, so each arm's Fresh-Fresh
    // bindings must be installed explicitly below or they are silently
    // dropped from the live system.  A multiset Counter premise solve
    // yielded by HS as `Inc_case_1 | Inc_case_2` collapses to a single
    // Inc case without the fan-out.
    //
    // Arm order is preserved from `EquationStore::perform_split`, which
    // matches HS's `performSplit eqs2 splitId` enumeration order (Maude
    // unifier result order).
    let arm_eq_stores: Vec<(crate::tools::equation_store::EquationStore, u64)> =
        if term_eqs.is_empty() {
            // No refineSubst; keep current eq_store as the sole arm.
            vec![(
                refined.sys.eq_store().clone(),
                refined.maude.fresh_counter_peek(),
            )]
        } else {
            let outcome = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
            match outcome {
                Err(error) => return Err(error),
                Ok(SolveOutcome::Contradictory) => {
                    return Ok(Vec::new());
                }
                Ok(SolveOutcome::Linear) => {
                    // Single arm: solve_term_eqs already installed it
                    // into refined.sys.eq_store().  Mirror as a single-arm
                    // Vec so the post-continuation runs once with that
                    // store.
                    vec![(
                        refined.sys.eq_store().clone(),
                        refined.maude.fresh_counter_peek(),
                    )]
                }
                Ok(SolveOutcome::Cases(arms)) => arms
                    .into_iter()
                    .map(|arm| (arm.eq_store, arm.counter))
                    .collect(),
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
    // each arm's substSystem continues from that arm's own post-solve
    // counter, instead of rewinding to `bounds_max(template)`.
    let mut out_arms: Vec<RefinedArm> = Vec::with_capacity(arm_eq_stores.len());

    for (arm_eq_store, arm_counter) in arm_eq_stores {
        // Install this arm's eq_store into a fresh per-arm Reduction
        // whose system body is the post-refineSubst template.  This
        // mirrors HS's `DisjT` replication of the Reduction continuation
        // (Reduction.hs `disjunctionOfList performSplit`).
        let mut refined =
            fork_arm_reduction(ctx, &post_solve_sys_template, arm_eq_store, arm_counter);
        refined.subst_system()?;
        if refined.sys.eq_store().is_false() {
            continue;
        }
        // Mirror Haskell `refineSource ctxt (refineSubst subst) (set cdGoal goalTerm th)`
        // (Sources.hs): after refineSubst, restrict the case's
        // eq-store to `frees (cdGoal th) = frees goalTerm` — the LIVE
        // goal's free vars (since `set cdGoal goalTerm` was applied).
        // Drops any leftover abstract/rule-internal bindings introduced
        // during precompute and renamed via Step A.1.
        let runtime_stable = frees(&(*live_node, fa_live.clone()));
        restrict_eq_store_to_stable_vars(&mut refined.sys, &runtime_stable);
        let refined_case = refined.sys;
        out_arms.push(RefinedArm { sys: refined_case });
    } // end `for arm_eq_store in arm_eq_stores`
    Ok(out_arms)
}

/// HS-faithful conjoin half of `applySource` (`_applySource`,
/// Sources.hs) for a single surviving `RefineArm`: runs
/// `markGoalAsSolved` + `conjoinSystem` + close-trivial-chains, returning one
/// [`ConjoinedArm`] per output arm.  Called only on cases that survived
/// `removeRedundantCases`.  The caller resets the live counter to
/// `arm.branch_counter` first: HS's conjoinSystem runs inside the same
/// DisjT-forked branch as the someInst (Sources.hs), NOT after
/// the sibling branches' conjoins.
fn conjoin_refine_arm(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    arm: RefineArm,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
) -> Result<Vec<ConjoinedArm>, crate::prove::ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{Reduction, SystemOutcome};

    if !matches!(live_goal, Goal::Action(_, _) | Goal::Premise(_, _)) {
        return Ok(Vec::new());
    }

    // `branch_counter` was consumed by the caller (its per-branch
    // `reset_counter_to` before this call).
    let RefineArm {
        freshened_case,
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
    // Sources.hs) — share the step's threaded counter.
    // ---------------------------------------------------------------
    let mut r = Reduction::new(ctx, live_sys.clone());
    if let Some(m) = red_maude {
        r.maude = m.clone();
    }
    // `_applySource` marks the selected goal before choosing and conjoining
    // the case, in both proof search and source saturation.
    if let Some(slot) = r.sys.goals_mut().iter_mut().find(|(g, _)| g == live_goal) {
        slot.1.solved = true;
    }
    // Continue every conjoin arm independently through the remainder of
    // `_applySource`, preserving each arm's FreshT continuation.
    let arm_reductions = match r.conjoin_system(&freshened_case) {
        Err(error) => return Err(error),
        Ok(SystemOutcome::Contradictory) => return Ok(out_arms),
        Ok(SystemOutcome::Linear) => vec![r],
        Ok(SystemOutcome::Cases(arms)) => arms
            .into_iter()
            .map(|arm| Reduction::new_inheriting(ctx, arm.sys, arm.counter))
            .collect(),
    };

    // Haskell's saturation source-pick ends here: `_applySource` performs
    // `markGoalAsSolved`, `someInst`, and `conjoinSystem`, then returns the
    // case name. The delayed-chain pass below is a Rust runtime compensation
    // for applying stored cases during proof search; repeating it while those
    // cases are themselves being saturated is both non-Haskell and can turn a
    // linear refinement into an explosion.
    if in_precompute_mode() {
        return Ok(arm_reductions
            .into_iter()
            .map(|r| ConjoinedArm {
                sys: r.sys,
                cont: r.maude.fresh_counter_peek(),
            })
            .collect());
    }

    for mut r in arm_reductions {
        // Haskell's precompute `solveAllSafeGoals` normally closes chains
        // before storing a source case. A chain whose abstract message
        // variable becomes concrete only during `refineSubst` can become
        // safe at this boundary, so finish that delayed closure here.
        close_trivial_chains_in_graft(&mut r)?;

        out_arms.push(ConjoinedArm {
            cont: r.maude.fresh_counter_peek(),
            sys: r.sys,
        });
    } // end `for r in arm_reductions`
    Ok(out_arms)
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
fn close_trivial_chains_in_graft(
    r: &mut crate::constraint::solver::reduction::Reduction,
) -> Result<(), crate::prove::ProveError> {
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
            // `chainToEquality` (Goals.hs) — they're filtered
            // OUT of `openGoals` and `solveAllSafeGoals` doesn't close
            // them.  Mirroring that here prevents over-eager closure
            // that breaks SplitG resolution downstream (NSPK3/NSLPK3
            // R_1 + I_2 case regressions).
            if fa_conc.tag == crate::fact::FactTag::Kd
                && let Some(t) = fa_conc.terms.first()
                && is_msg_var_for_chain_filter(t)
            {
                return None;
            }
            // HS-faithful: never auto-close a chain that `openChainGoals`
            // (Goals.hs) keeps as an OPEN ranked goal.  A DnK
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

        // Run the speculative edge closure in a child Reduction.  A failed
        // or split solve must not leak its taken equation store, fresh-counter
        // draws, change flag, or pending fan-out scratch into the live branch.
        let mut trial = r.speculative_branch();
        trial
            .sys
            .add_edge(crate::constraint::constraints::Edge { src: c, tgt: p });
        let res = trial.solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal {
                lhs: fa_conc,
                rhs: fa_prem,
            }],
        );
        match res {
            Err(error) => return Err(error),
            Ok(SolveOutcome::Contradictory) | Ok(SolveOutcome::Cases(_)) => {
                // This function's contract is explicitly "if Branch 1 fails
                // or splits, leave the chain as-is".  Dropping `trial`
                // restores all Reduction state atomically.
                break;
            }
            Ok(SolveOutcome::Linear) => {
                *r = trial;
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
    Ok(())
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
//   2. For each case build the normalised system.  The normalisation
//      walks free vars in HS-determined order (varOccurences-ordered
//      first, then foldFrees), assigning each a fresh idx with empty
//      name.
//   3. Deduplicate the indexed cases with Haskell's `sortednubBy` survivor
//      rules, then sort the survivors by their original indices.

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
        let a = self.as_str().as_bytes();
        let b = other.as_str().as_bytes();
        if std::ptr::eq(a, b) {
            return std::cmp::Ordering::Equal;
        }
        match (a.first(), b.first()) {
            (Some(x), Some(y)) if x != y => x.cmp(y),
            _ if a.len().min(b.len()) <= 1 => a.len().cmp(&b.len()),
            _ => a.cmp(b),
        }
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
        use tamarin_term::function_symbols::{AcSym, CSym, FunSym};
        match sym {
            FunSym::NoEq(s) => match String::from_utf8_lossy(s.name) {
                std::borrow::Cow::Borrowed(s) => Seg::Static(s),
                std::borrow::Cow::Owned(s) => Seg::shared(&s),
            },
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
    // HS `show (factTag fa)` (derived `Show FactTag`, Theory/Model/Fact.hs).
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

// SplitG is not a "safe" goal at saturate time while chains are open
// (`doSplit = noChainGoals && not (null chains)`, Sources.hs) —
// HS leaves `RuleACConstrs` SplitG OPEN, and variant narrowing happens
// at runtime as a deeper `case split` step, never as sibling source cases.

#[cfg(test)]
#[path = "sources_tests.rs"]
mod tests;
