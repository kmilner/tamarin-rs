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
        // (TheoryLoader.hs:273-274): openChain=10, saturation=5.
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
/// `length . unsolvedChains` (System.hs:1603-1607), counting unsolved Chain
/// goals in one System. (Distinct from Haskell `unsolvedChainConstraints
/// :: Source -> [Int]` at Sources.hs:87-89, which maps over a Source's
/// cases.)
pub fn unsolved_chain_constraints(sys: &System) -> usize {
    sys.unsolved_chains().count()
}

/// `Source` — one precomputed case distinction. The Haskell version
/// is `Source { _cdGoal :: Goal, _cdCases :: Disj (M.Map CaseName System) }`.
/// `cdCases` is a lazy thunk in HS; matched here by `cases_cell`, which is
/// filled on the first `cases(ctx)` call. Trivial
/// protocols never force `KU(t:Fresh)`-style sources (HS's
/// `smartRanking.getMsgOneCase` pattern-matches on `FApp o _` before
/// touching `cdCases`, so Var-headed sources never trigger the thunk);
/// Rust matches by deferring `solve_action_goal` / `solve_premise_goal`
/// out of `precompute_full_sources` until the owning context forces them.
pub type SourceCase = (Vec<String>, System);
pub(crate) type SourceCases = std::sync::Arc<std::sync::Mutex<Vec<SourceCase>>>;

pub(crate) struct Source {
    pub goal: crate::constraint::constraints::Goal,
    /// Lazy cases — wrapped in `Mutex<Option<…>>` for interior
    /// mutability. The inner shared backing lets session cache hits and
    /// proof-context worker snapshots reuse the heavy systems; taking a list
    /// for a mutating saturation pass unwraps it when unique and clones
    /// otherwise. The inner mutex is also what makes non-`Sync` `System`
    /// caches safe to carry in a context shared by rayon workers.
    /// Internally stores case names as `Vec<String>` — HS's
    /// `caseNames :: [String]` (the `caseNames` parameter of `solve` at
    /// Sources.hs:144-225, see line 175; `[String]` type at Sources.hs:144-225).  The list
    /// representation is critical for `combine`'s truncation rule
    /// `combine (n:_) _ = [n]` (Sources.hs:113-137, see line 137): without per-element
    /// boundaries, multi-step accumulated names can't be truncated
    /// to a single element across refineSource iterations. Names are joined
    /// only by presentation and proof-case-label code.
    pub(crate) cases_cell: std::sync::Mutex<Option<SourceCases>>,
}

impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = f.debug_struct("Source");
        out.field("goal", &self.goal);
        match self.cases_cell.lock() {
            Err(_) => out.field("cases", &"<poisoned>"),
            Ok(cases) => match cases.as_ref() {
                None => out.field("cases", &"<lazy>"),
                Some(cases) => match cases.lock() {
                    Ok(cases) => out.field("cases", &*cases),
                    Err(_) => out.field("cases", &"<poisoned>"),
                },
            },
        };
        out.finish()
    }
}

impl Clone for Source {
    fn clone(&self) -> Self {
        let v = self.cases_cell.lock().unwrap().clone();
        Source {
            goal: self.goal.clone(),
            cases_cell: std::sync::Mutex::new(v),
        }
    }
}

impl Source {
    /// Build a Source whose cases will be computed lazily via
    /// `initial_source_cases(goal, ctx)` when the owning context is first
    /// forced. Matches HS's `initialSource` (Sources.hs:97-110, see line 103) thunk.
    pub(crate) fn lazy(goal: crate::constraint::constraints::Goal) -> Self {
        Source {
            goal,
            cases_cell: std::sync::Mutex::new(None),
        }
    }

    /// Build a Source with cases already computed. Case-name component
    /// boundaries are retained until the rendering boundary.
    pub(crate) fn eager(
        goal: crate::constraint::constraints::Goal,
        cases: Vec<SourceCase>,
    ) -> Self {
        Source {
            goal,
            cases_cell: std::sync::Mutex::new(Some(std::sync::Arc::new(std::sync::Mutex::new(
                cases,
            )))),
        }
    }

    /// Materialise + return the cases. Session-backed contexts resolve their
    /// shared raw/refined slot here; standalone contexts perform their own
    /// saturation. The state machine makes repeated calls inexpensive.
    ///
    /// Returns an owned working copy. The stored list itself remains shared
    /// across context clones and cache hits; solver consumers generally mutate
    /// their returned systems while grafting them into a branch.
    pub(crate) fn cases_unchecked(
        &self,
        ctx: &crate::constraint::solver::context::ProofContext,
    ) -> Vec<SourceCase> {
        ctx.ensure_saturated();
        self.cases_cell
            .lock()
            .unwrap()
            .as_ref()
            .expect("saturated source must have a materialised case list")
            .lock()
            .unwrap()
            .clone()
    }

    /// Cases used by `applySource`. Runtime application forces the context's
    /// lazy saturated sources; saturation itself consumes the materialised
    /// snapshot for its current iteration. The latter may run on a Rayon
    /// worker, which must not wait on the saturation gate owned by its caller.
    fn cases_for_apply(
        &self,
        ctx: &crate::constraint::solver::context::ProofContext,
    ) -> Vec<SourceCase> {
        if in_precompute_mode() {
            self.cases_or_empty()
        } else {
            self.cases_unchecked(ctx)
        }
    }

    /// Shared read-only cases, or an empty list when still lazy.
    pub(crate) fn cases_or_empty(&self) -> Vec<SourceCase> {
        self.cases_cell
            .lock()
            .unwrap()
            .as_ref()
            .map(|cases| cases.lock().unwrap().clone())
            .unwrap_or_default()
    }

    /// Shared backing storage for source-cache snapshots and restoration.
    pub(crate) fn cases_shared_or_empty(&self) -> SourceCases {
        self.cases_cell
            .lock()
            .unwrap()
            .clone()
            .unwrap_or_else(|| std::sync::Arc::new(std::sync::Mutex::new(Vec::new())))
    }

    /// Number of materialised cases — equal to `cases_or_empty().len()`
    /// but WITHOUT deep-cloning every case `System` to count them.
    /// Returns 0 when the cell hasn't been forced yet.  O(1).
    pub(crate) fn cases_len(&self) -> usize {
        self.cases_cell
            .lock()
            .unwrap()
            .as_ref()
            .map_or(0, |cases| cases.lock().unwrap().len())
    }

    /// The `n`-th materialised case's system — `cases_or_empty()[n].1`
    /// WITHOUT deep-cloning the cases either side of it.  Returns `None`
    /// when the cell hasn't been forced yet or `n` is past the end.
    pub(crate) fn case_system_at(&self, n: usize) -> Option<System> {
        let g = self.cases_cell.lock().unwrap();
        let cases = g.as_ref()?.lock().unwrap();
        let (_, sys) = cases.get(n)?;
        Some(sys.clone())
    }

    /// Drain the materialised cases out of the cell, leaving it lazy again.
    pub(crate) fn cases_take(&self) -> Vec<SourceCase> {
        self.cases_cell
            .lock()
            .unwrap()
            .take()
            .map(|cases| match std::sync::Arc::try_unwrap(cases) {
                Ok(cases) => cases.into_inner().unwrap(),
                Err(cases) => cases.lock().unwrap().clone(),
            })
            .unwrap_or_default()
    }

    /// Replace the cases cell with a new value.  Used by saturate to
    /// install a refined case set, AND by `ensure_saturated`'s post-
    /// saturate writeback.  Takes `&self` (not `&mut`) so it works
    /// through immutable `ctx.full_sources` borrows.
    pub(crate) fn cases_set(&self, cases: Vec<SourceCase>) {
        self.cases_set_shared(std::sync::Arc::new(std::sync::Mutex::new(cases)));
    }

    /// Install a case list shared with the session cache.
    pub(crate) fn cases_set_shared(&self, cases: SourceCases) {
        *self.cases_cell.lock().unwrap() = Some(cases);
    }
}

/// HS-faithful port of `initialSource ctxt restrictions goal`
/// (Sources.hs:97-110, see line 103).  Builds a fresh empty system with restrictions
/// injected, inserts `goal`, marks-as-solved (HS `solveGoal`-style),
/// then dispatches to the goal-specific solver.  The resulting cases
/// are normalised: subst applied, simplify run, contradictory cases
/// dropped, eq-store restricted to stable (= `frees (cdGoal th)`) vars.
/// `ProofContext::ensure_saturated` uses this to pre-populate each source's
/// cases before running saturation.
pub(crate) fn initial_source_cases(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<SourceCase> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};

    let mut sys = System::empty();
    sys.source_kind = Some(crate::constraint::system::SourceKind::RawSources);
    // HS-faithful (CloseRule.hs:422-426): source precomputation gets ONLY
    // safety restrictions.  Non-safety restrictions (e.g.
    // `Start_implies_Stop = All x #i. Start(x)@i ⇒ Ex #j. Stop(x)@j`)
    // would fire `insertImpliedFormulas` during saturate, spawning Stop
    // ActionG / node via `solveUniqueActions`, which would re-open B
    // premise → another Step → another A premise → another Start →
    // restriction fires again → Cyclic.  HS skips this entire chain by
    // filtering to safety formulas at `CloseRule.hs:425`.
    sys.insert_lemmas(ctx.safety_restrictions.iter().cloned());
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

    // Every solver branch descends from `red.sys`, so it already carries the
    // safety restrictions installed above.
    let normalize_and_keep = |sys: System, counter: u64| -> Vec<System> {
        crate::constraint::solver::simplify::simplify_system_with_fanout_seeded_with_counters(
            ctx, sys, counter,
        )
        .into_iter()
        .filter_map(|(s, _)| {
            if s.eq_store.is_false()
                || !crate::constraint::solver::contradictions::contradictions(ctx, &s).is_empty()
            {
                return None;
            }
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
        })
        .collect()
    };
    let linear_counter = red.maude.fresh_counter_peek();
    match outcome {
        GoalCases::Linear => normalize_and_keep(red.sys, linear_counter)
            .into_iter()
            .map(|s| (vec!["only".into()], s))
            .collect(),
        GoalCases::LinearNamed(name) => {
            let names = (!name.is_empty())
                .then_some(name)
                .into_iter()
                .collect::<Vec<_>>();
            normalize_and_keep(red.sys, linear_counter)
                .into_iter()
                .map(|s| (names.clone(), s))
                .collect()
        }
        GoalCases::Cases(systems) => systems
            .into_iter()
            .flat_map(|branch| {
                let names = (!branch.name.is_empty())
                    .then_some(branch.name)
                    .into_iter()
                    .collect::<Vec<_>>();
                normalize_and_keep(branch.sys, branch.counter)
                    .into_iter()
                    .map(move |s| (names.clone(), s))
            })
            .collect(),
        GoalCases::Contradictory => Vec::new(),
    }
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
pub(crate) fn precompute_full_sources(
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
    // Saturation (`saturate_sources_with_simp`) is a separate
    // concern: it iterates `cases` and would defeat the laziness if
    // run here.  This precompute function does not run it; `context.rs`
    // invokes `saturate_sources_with_simp` separately.
    //
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
///   under `instance HasFrees Source`, System.hs:1881-1891: `cdGoal`
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
fn source_bounds(src: &Source, cases: &[SourceCase]) -> (Option<u64>, Option<u64>) {
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
) -> Vec<Source> {
    if assumptions.is_empty() {
        // HS `refineWithSourceAsms _ []` still applies `updateSystem`, so
        // refined consumers see `RefinedSource` even though no formulas need
        // to be added and no second saturation can change the cases.
        return sources
            .into_iter()
            .map(|src| {
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
            .collect();
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
        let mut new_cases: Vec<SourceCase> = Vec::new();
        for (name, mut sys) in src.cases_take() {
            for a in assumptions {
                sys.insert_formula(a.clone());
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
        intermediate.push(Source::eager(src.goal, new_cases));
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
    let limit = ctx.parameters.saturation_limit();
    let saturated = saturate_sources_with_simp(intermediate, limit, ctx);

    // Step 3 (Haskell `removeFormulas`): strip formulas + solved
    // formulas after saturation, and drop disjunction goals derived
    // from the assumptions.
    let mut out: Vec<Source> = Vec::new();
    for src in saturated {
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
    out
}

/// Per-source body of `saturate_sources_with_simp`'s inner loop —
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
) -> (Vec<(Vec<String>, System)>, bool, usize) {
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
    let all_cases = src.cases_take();
    // HS `refineSource` (Sources.hs:113-137, see line 128): `fs = avoid th` — the fresh seed
    // for EVERY case is the max var idx over the WHOLE source `th` (all its
    // cases), NOT the per-case `avoid se`.  Compute it once here and thread
    // it as the seed floor into each case's Reduction.
    let source_avoid = source_avoid(&src, &all_cases);
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
                ctx.parameters.open_chains_limit(),
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
/// Re-simplify every grafted source case so newly-fired implied formulas can
/// prune it. Mirrors Haskell's `saturateSources`, including its iteration cap.
pub(crate) fn saturate_sources_with_simp(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    use rayon::prelude::*;
    let show_steps = ctx.show_saturation_steps;
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
        // The task inputs are read-only.
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
        let src_goals: Vec<crate::constraint::constraints::Goal> =
            current.iter().map(|s| s.goal.clone()).collect();
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
                let pooled = ctx.maude_pool.as_ref().and_then(|pool| pool.try_acquire());
                if let Some(pooled) = pooled {
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
                    refine_one_source(&task_ctx, src, &ths_snapshot, branch_cap)
                } else {
                    // Source materialisation can be forced by a search worker
                    // which already owns a pool entry. Blocking here could
                    // deadlock when every entry is held by such a worker.
                    refine_one_source(ctx, src, &ths_snapshot, branch_cap)
                }
            })
            .collect();
        assert_eq!(per_source.len(), src_goals.len());
        for ((new_cases, per_changed, _), src_goal) in per_source.into_iter().zip(src_goals) {
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
            next.push(Source::eager(src_goal, new_cases));
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
        let mut cases = src.cases_take();
        for (name_list, _) in &mut cases {
            if name_list.len() > 1 {
                let truncated = combine_case_names_list(name_list, &[]);
                *name_list = truncated;
            }
        }
        src.cases_set(cases);
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
    use crate::constraint::solver::reduction::{GoalCases, Reduction};
    use crate::constraint::solver::simplify::simplify_system_with_fanout_seeded_with_counters;
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
        fresh_counter: u64,
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
        fresh_counter: source_avoid.saturating_add(1),
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
        fresh_counter,
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
        let post_simp = simplify_system_with_fanout_seeded_with_counters(ctx, sys, fresh_counter);
        // Pop one sibling to continue with; push the rest back for
        // later processing.  Match HS's Disj-monad insertion order:
        // first sibling processed first (LIFO worklist → push tail
        // reversed so the head pops next).
        let (sys, fresh_counter) = match post_simp.len() {
            0 => continue, // all siblings contradictory / dropped
            1 => post_simp.into_iter().next().unwrap(),
            _ => {
                let mut iter = post_simp.into_iter();
                let head = iter.next().unwrap();
                let tail: Vec<_> = iter.collect();
                for (sib, sibling_counter) in tail.into_iter().rev() {
                    worklist.push(Entry {
                        sys: sib,
                        name: name.clone(),
                        used: used.clone(),
                        chains_left,
                        iters_left,
                        last_chain_term: last_chain_term.clone(),
                        took_step,
                        fresh_counter: sibling_counter,
                    });
                }
                head
            }
        };
        let mut red = Reduction::new_inheriting(ctx, sys, fresh_counter);
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
        let any_unsolved_chain = red.sys.unsolved_chains().next().is_some();
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
                        fresh_counter: red.maude.fresh_counter_peek(),
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
                    // order from `solveChain` (Goals.hs:316-380),
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
                            iters_left: iters_left - 1,
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
                ths,
                &red.sys,
                &i_cand,
                &fa_cand,
                &red.maude,
                Some(red.maude.fresh_counter_peek()),
            ) {
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
            // (Sources.hs:144-225, see line 214 `(caseNames ++ x)`); `combine` runs only at the
            // refineSource boundary, not per-step inside solveAllSafeGoals.
            let mut new_name = name.clone();
            append_step_name_list(&mut new_name, &case_name);
            worklist.push(Entry {
                sys: sys_cand,
                name: new_name,
                used: new_used,
                chains_left,
                iters_left: iters_left - 1,
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

/// Refine, deduplicate, instantiate, and conjoin one already-matched source.
/// Shared by premise and action source application so their FreshT branch
/// semantics cannot drift apart.
fn apply_prepared_source_cases(
    ctx: &crate::constraint::solver::context::ProofContext,
    cases: &[SourceCase],
    prepared: &PreparedSourceMatch,
    sys: &System,
    live_goal: &crate::constraint::constraints::Goal,
    red_maude: &tamarin_term::maude_proc::MaudeHandle,
    fork_base: u64,
) -> Vec<(String, System, u64)> {
    // HS `refineSource` first refines every case, then removes redundant
    // refined systems, and only then runs `_applySource` (someInst + conjoin)
    // for each survivor. The source-case disjunction sits below FreshT, so
    // every survivor starts at the same pick-time counter and returns its own
    // continuation.
    let mut refine_arms = Vec::new();
    for (name, case_sys) in cases {
        let case_label = case_name_list_to_string(name);
        refine_arms.extend(
            refine_source_case(ctx, prepared, case_sys)
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
        for out_arm in conjoin_refine_arm(ctx, sys, live_goal, arm, Some(red_maude)) {
            out.push((case_label.clone(), out_arm.sys, out_arm.cont));
        }
    }
    out
}

/// Haskell-faithful `applySource` driver for premise goals. A matched source
/// remains matched even when all of its cases disappear during refinement.
pub(crate) fn solve_with_source_cases_ctx(
    ctx: &crate::constraint::solver::context::ProofContext,
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    goal_prem_idx: crate::rule::PremIdx,
    fa_prem: &crate::fact::LNFact,
    red_maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
) -> SourceMatch<(String, System, u64)> {
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
    // the grafted case onto existing nodes.  Filtering already-used cases
    // here would instead create unmerged Step/Start/Fresh nodes.

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
    let live_goal = Goal::Premise((*goal_node, goal_prem_idx), fa_prem.clone());
    let Some((cases, prepared)) = sources.iter().find_map(|src| {
        if !source_goal_may_match(&src.goal, &live_goal) {
            return None;
        }
        let cases = src.cases_for_apply(ctx);
        prepare_source_match(ctx, src, &cases, &live_goal).map(|prepared| (cases, prepared))
    }) else {
        return SourceMatch::NoMatch;
    };
    // HS FreshT-threading (`_applySource`, Sources.hs:344-350): the
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
    SourceMatch::Matched(apply_prepared_source_cases(
        ctx, &cases, &prepared, sys, &live_goal, red_maude, fork_base,
    ))
}

/// Haskell-faithful `applySource` path for KU action goals: one-way matching,
/// `someInst keepVarBindings`, and `conjoinSystem`.
#[track_caller]
pub(crate) fn solve_with_source_cases_action(
    ctx: &crate::constraint::solver::context::ProofContext,
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    red_maude: &tamarin_term::maude_proc::MaudeHandle,
    precompute_fork_base: Option<u64>,
    // Fourth tuple element: per-output-entry live-counter continuation
    // (HS FreshT-threading — the producing branch's fork + own draws).
) -> SourceMatch<(String, System, u64)> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;

    // Only KU-tagged Action goals consult action sources.
    if fa_live.tag != FactTag::Ku || fa_live.terms.len() != 1 {
        return SourceMatch::NoMatch;
    }
    let live_goal = Goal::Action(*goal_node, fa_live.clone());
    let Some((cases_iter, prepared)) = sources.iter().find_map(|src| {
        if !source_goal_may_match(&src.goal, &live_goal) {
            return None;
        }
        let cases = src.cases_for_apply(ctx);
        prepare_source_match(ctx, src, &cases, &live_goal).map(|prepared| (cases, prepared))
    }) else {
        return SourceMatch::NoMatch;
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
        return SourceMatch::Matched(Vec::new());
    }
    let fork_base = precompute_fork_base.unwrap_or_else(|| red_maude.fresh_counter_peek());
    SourceMatch::Matched(apply_prepared_source_cases(
        ctx,
        &cases_iter,
        &prepared,
        sys,
        &live_goal,
        red_maude,
        fork_base,
    ))
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
pub fn case_name_list_to_string(names: &[String]) -> String {
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
/// (System.hs:1834-1879) first reaches it, and every index is drawn from the
/// step's own `MonadFresh` — here the Maude handle whose counter the live
/// `Reduction` threads.  `keep` is HS's `frees goal`, seeded into the store as
/// identity bindings that `importBinding` finds and reuses instead of drawing
/// (Control/Monad/Bind.hs:125-140).
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
fn source_goal_may_match(
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

fn prepare_source_match(
    ctx: &crate::constraint::solver::context::ProofContext,
    src: &Source,
    cases: &[SourceCase],
    live_goal: &crate::constraint::constraints::Goal,
) -> Option<PreparedSourceMatch> {
    use crate::constraint::constraints::Goal;
    use tamarin_term::lterm::HasFrees;

    let (abstract_node, abstract_fact, prem_rewire, live_node, live_fact) =
        match (&src.goal, live_goal) {
            (Goal::Action(an, af), Goal::Action(ln, lf)) => (*an, af, None, *ln, lf),
            (Goal::Premise((an, ap), af), Goal::Premise((ln, lp), lf)) => {
                (*an, af, Some((*ap, *lp)), *ln, lf)
            }
            _ => return None,
        };
    if live_fact.tag != abstract_fact.tag || live_fact.terms.len() != abstract_fact.terms.len() {
        return None;
    }

    let mut goal_max = 0;
    live_node.for_each_free(&mut |v| goal_max = goal_max.max(v.idx));
    live_fact.for_each_free(&mut |v| goal_max = goal_max.max(v.idx));
    let (src_min, src_cases_max) = source_bounds(src, cases);
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
            MatchOutcome::NoMatcher => return None,
            MatchOutcome::NeedsAc => {
                let eqs = pairs
                    .into_iter()
                    .map(|(lhs, rhs)| tamarin_term::rewriting::Equal { lhs, rhs })
                    .collect::<Vec<_>>();
                let mut matches = ctx.maude.match_eqs(&eqs).ok()?;
                if matches.is_empty() {
                    return None;
                }
                matches.swap_remove(0)
            }
        };

    Some(PreparedSourceMatch {
        renamed_abstract_node,
        prem_rewire,
        live_node,
        live_fact: live_fact.clone(),
        rename_shift,
        refine_seed,
        match_pairs,
    })
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
    /// This branch's live-counter continuation (HS FreshT-threading):
    /// the fork plus this branch's own someInst + conjoin + step-12-arm
    /// + close-chains draws.
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
/// `removeRedundantCases` (Sources.hs:236-260, keyed on the returned
/// refined systems) BEFORE calling [`conjoin_refine_arm`] on
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
    prepared: &PreparedSourceMatch,
    case_sys: &System,
) -> Vec<RefinedArm> {
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
        let pat_prem = (*renamed_abstract_node, *abstract_prem_idx);
        let new_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
            (*renamed_abstract_node, *live_prem_idx);
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
    let _refine_fs = RefineFsScope::set(*refine_seed);
    let mut refined = Reduction::new(ctx, renamed_case);
    // HS-faithful `solveSubstEqs` (Reduction.hs:721-740, see line 736):
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
    let arm_eq_stores: Vec<(crate::tools::equation_store::EquationStore, u64)> =
        if term_eqs.is_empty() {
            // No refineSubst; keep current eq_store as the sole arm.
            vec![(
                (**refined.sys.eq_store).clone(),
                refined.maude.fresh_counter_peek(),
            )]
        } else {
            let outcome = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
            match outcome {
                Err(_) | Ok(SolveOutcome::Contradictory) => {
                    return Vec::new();
                }
                Ok(SolveOutcome::Linear) => {
                    // Single arm: solve_term_eqs already installed it
                    // into refined.sys.eq_store.  Mirror as a single-arm
                    // Vec so the post-continuation runs once with that
                    // store.
                    vec![(
                        (**refined.sys.eq_store).clone(),
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
        // (Reduction.hs:742-744 `disjunctionOfList performSplit`).
        let mut refined =
            fork_arm_reduction(ctx, &post_solve_sys_template, arm_eq_store, arm_counter);
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
        out_arms.push(RefinedArm { sys: refined_case });
    } // end `for arm_eq_store in arm_eq_stores`
    out_arms
}

/// HS-faithful conjoin half of `applySource` (`_applySource`,
/// Sources.hs:344-350) for a single surviving `RefineArm`: runs
/// `markGoalAsSolved` + `conjoinSystem` + close-trivial-chains, returning one
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
    use crate::constraint::solver::reduction::{Reduction, SystemOutcome};

    if !matches!(live_goal, Goal::Action(_, _) | Goal::Premise(_, _)) {
        return Vec::new();
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
    // Sources.hs:344-350) — share the step's threaded counter.
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
        Err(_) | Ok(SystemOutcome::Contradictory) => return out_arms,
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
        return arm_reductions
            .into_iter()
            .map(|r| ConjoinedArm {
                sys: r.sys,
                cont: r.maude.fresh_counter_peek(),
            })
            .collect();
    }

    for mut r in arm_reductions {
        // Haskell's precompute `solveAllSafeGoals` normally closes chains
        // before storing a source case. A chain whose abstract message
        // variable becomes concrete only during `refineSubst` can become
        // safe at this boundary, so finish that delayed closure here.
        close_trivial_chains_in_graft(&mut r);

        out_arms.push(ConjoinedArm {
            cont: r.maude.fresh_counter_peek(),
            sys: r.sys,
        });
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
            if fa_conc.tag == crate::fact::FactTag::Kd
                && let Some(t) = fa_conc.terms.first()
                && is_msg_var_for_chain_filter(t)
            {
                return None;
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
            Err(_) | Ok(SolveOutcome::Contradictory) | Ok(SolveOutcome::Cases(_)) => {
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
//   3. Run a verbatim port of HS `sortednubBy` (`sortednub_by`) over the
//      index-decorated list, comparing with
//      `compare_systems_up_to_new_vars`, then
//      `sortOn fst` to restore original-index order (matches `sortOn fst`
//      in HS).  NOTE: `sortednubBy` does NOT keep the first element of an
//      EQ-group — its run-detection phase (`sequences`) does
//      `EQ -> sequences xs`, dropping the earlier element and keeping the
//      LATER one; the `merge` phase drops the right-list element on EQ.
//      Since the members of an EQ-group compare equal and `sortOn fst`
//      washes out cross-group order, the observable effect is "keep the
//      highest-original-index member of each group".  (A
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

/// The variable rename of `renameDropNameHints sys` (Sources.hs:252-258),
/// as a binding store [`norm_sys_for_compare`] maps the system through:
///   1. `stableVarBindings`: every stable variable binds to itself.
///   2. `evalFresh … (avoid stableVars)`: the supply starts above the largest
///      stable index.
///   3. `renameDropNamehint (orderedVars sys)` imports the non-`Node` variables
///      of `varOccurences sys` in occurrence-set order first.
///   4. `renameDropNamehint sys` imports the rest, in the order
///      `instance HasFrees System` (System.hs:1834-1850) reaches them.
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

/// HS `addNormSys` (Sources.hs:246):
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

/// HS `compareRulesUpToNewVars` (Theory/Model/Rule.hs:273-284): the info, the
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

/// HS `compareSystemsUpToNewVars` (System.hs:1911-1924) over two systems that
/// `norm_sys_for_compare` has already normalised.  The nodes compare through
/// `compare_rules_up_to_new_vars` over both maps in `M.toAscList` order (HS
/// `compareNodesUpToNewVars`/`compareListsUpToNewVars`, System.hs:1896-1909,
/// which is the lexicographic order on the two lists).  When the nodes tie,
/// HS blanks that field in both records and falls back to the derived
/// `Ord System`, so the rest compares in HS's declaration order
/// (System.hs:382-396): edges, lessAtoms, lastAtom, subtermStore, eqStore,
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
    // Exhaustive destructure (no `..`): a new `SystemContent` field becomes a
    // compile error here until its role in the comparison is decided.
    let crate::constraint::system::SystemContent {
        nodes: _,
        edges,
        less_atoms,
        formulas,
        solved_formulas,
        lemmas,
        last_atom,
        eq_store,
        subterm_store,
        goals,
    } = &**a;
    let crate::constraint::system::SystemContent {
        nodes: _,
        edges: b_edges,
        less_atoms: b_less_atoms,
        formulas: b_formulas,
        solved_formulas: b_solved_formulas,
        lemmas: b_lemmas,
        last_atom: b_last_atom,
        eq_store: b_eq_store,
        subterm_store: b_subterm_store,
        goals: b_goals,
    } = &**b;
    edges
        .cmp(b_edges)
        .then_with(|| less_atoms.cmp(b_less_atoms))
        .then_with(|| last_atom.cmp(b_last_atom))
        .then_with(|| subterm_store.cmp_hs(b_subterm_store))
        .then_with(|| eq_store.cmp(b_eq_store))
        .then_with(|| formulas.cmp(b_formulas))
        .then_with(|| solved_formulas.cmp(b_solved_formulas))
        .then_with(|| lemmas.cmp(b_lemmas))
        .then_with(|| goals.cmp(b_goals))
        .then_with(|| a.next_goal_nr.cmp(&b.next_goal_nr))
        .then_with(|| a.source_kind.cmp(&b.source_kind))
        // Rust carries the selected diff side; HS stores only whether this is
        // a diff system, so LHS and RHS compare equal at this final field.
        .then_with(|| a.side.is_some().cmp(&b.side.is_some()))
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
            if let Some(b_ref) = bs.first()
                && cmp(&a, b_ref) == Greater
            {
                let mut it = bs.into_iter();
                let b = it.next().unwrap();
                bs = it.collect();
                acc.insert(0, a); // a:as  (acc holds run in ascending order)
                a = b;
                continue;
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
            if let Some(b_ref) = bs.first()
                && cmp(&a, b_ref) == Less
            {
                let mut it = bs.into_iter();
                let b = it.next().unwrap();
                bs = it.collect();
                acc.push(a); // as ++ [a]
                a = b;
                continue;
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
/// alpha-duplicates) this keeps the LAST member and, after `sortOn fst`,
/// emits survivors in original-index order — the exact flip the Joux/Scott
/// mirror needed.
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
    let pre = cases.len();
    // Decorate with (original index, normed system).  HS:
    //   decoratedCases = map (second addNormSys) $ zip [0..] cases0
    let mut decorated: Vec<(usize, crate::constraint::system::System, T)> = Vec::with_capacity(pre);
    for (idx, c) in cases.into_iter().enumerate() {
        let normed = norm_sys_for_compare(get_sys(&c), stable_vars);
        decorated.push((idx, normed, c));
    }
    // sortednubBy (\(_,(_,x)) (_,(_,y)) -> compareSystemsUpToNewVars x y)
    let mut deduped = sortednub_by(
        &|a: &(usize, crate::constraint::system::System, T),
          b: &(usize, crate::constraint::system::System, T)| {
            compare_systems_up_to_new_vars(&a.1, &b.1)
        },
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
