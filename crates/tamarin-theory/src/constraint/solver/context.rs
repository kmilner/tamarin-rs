// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Solver context — port of the `ProofContext` data type from
//! `Theory.Constraint.System`.
//!
//! The Haskell `ProofContext` is a fat record carrying every piece of
//! per-theory information the solver needs:
//!
//! - The underlying signature (with Maude handle).
//! - The protocol rules and their AC variants.
//! - Sources / case-distinctions used to bias goal solving.
//! - Heuristic / tactic configuration.
//! - Whether to use induction, whether diff mode is on, etc.
//!
//! The Rust port carries all of these, split across two structs: the
//! per-lemma / post-construction-mutable fields owned directly by
//! [`ProofContext`], and the immutable-after-build bundle
//! ([`ProofContextShared`]) held behind an `Arc` so a context with a swapped
//! Maude handle is a refcount bump rather than a deep copy.

use tamarin_term::maude_proc::{MaudeHandle, MaudePool};

use crate::rule::IntrRuleAC;
use crate::theory::OpenProtoRule;

/// Shared handle on a theory's intruder-rule cache.
///
/// The rules are read-only once built: HS's `closeRuleCache` consumes
/// `_thyCache` verbatim.  The load paths build the cache once per theory
/// (the NDC pass, `close_rule::check_close_intr_rule`) and hand that one
/// handle to every context derived from it, so the many per-probe /
/// per-deduction / per-lemma contexts cost a refcount bump instead of a
/// deep copy of the rule list.  A context built WITHOUT an injected cache
/// assembles its own ([`ProofContext::assemble_intruder_rules`] plus the
/// cache permutation) and shares that one with its own clones.
///
/// Reads go through the [`std::ops::Deref`] to `[IntrRuleAC]` (and the
/// borrowing [`IntoIterator`]), which keeps the slice API — `.iter()`,
/// indexing, `for r in &cache` — available on the handle.  There is
/// deliberately no `DerefMut` and no interior mutability: sharing cannot
/// change what any context sees.
#[derive(Debug, Clone)]
pub struct IntrRuleCache(std::sync::Arc<Vec<IntrRuleAC>>);

impl From<Vec<IntrRuleAC>> for IntrRuleCache {
    fn from(rules: Vec<IntrRuleAC>) -> Self {
        IntrRuleCache(std::sync::Arc::new(rules))
    }
}

impl std::ops::Deref for IntrRuleCache {
    type Target = [IntrRuleAC];
    fn deref(&self) -> &[IntrRuleAC] {
        &self.0
    }
}

impl<'a> IntoIterator for &'a IntrRuleCache {
    type Item = &'a IntrRuleAC;
    type IntoIter = std::slice::Iter<'a, IntrRuleAC>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Read-only, immutable-after-build bundle of a `ProofContext`.
///
/// These fields are computed once at theory-load time and shared unchanged by
/// every lemma and proof-search worker. Mutable source materialisation lives
/// directly on [`ProofContext`], outside this bundle.
#[derive(Debug)]
pub struct ProofContextShared {
    /// Protocol rules after loop-breaker and variant annotation. They become
    /// immutable before source precomputation and are shared by every lemma
    /// and proof-search worker.
    pub rules: Vec<OpenProtoRule>,
    /// The theory's intruder-rule cache: either the once-per-load
    /// NDC-checked cache injected by the loader, or
    /// [`ProofContext::assemble_intruder_rules`] (subterm constructor rules,
    /// the special rules — `Coerce`, `PubConstr`, `FreshConstr`, `ISend`,
    /// `IRecv`, plus `IEquality` in diff mode — the MSet/Xor rules, the
    /// user-symbol destruction rules, then the DH/BP variants) run through
    /// `ndc_check_cache_order`.  These let the solver discharge `KU(_)` /
    /// `KD(_)` goals that arise from `In(_)`-fact reasoning.  Held as a
    /// shared [`IntrRuleCache`] handle, so cloning the bundle shares the
    /// rule list instead of copying it.
    pub intruder_rules: IntrRuleCache,
    /// Action `(tag, arity)` shapes that occur in exactly one protocol or
    /// intruder rule. `solveUniqueActions` consults this on every simplify
    /// iteration, so derive it once with the immutable rule bundle.
    pub(crate) unique_action_shapes: std::collections::BTreeSet<(crate::fact::FactTag, usize)>,
    /// Theory-level restrictions (safety formulas), in guarded form.
    /// Mirrors Haskell's `pcRestrictions` — passed to `initialSource`
    /// so each precomputed source-case starts from a system with the
    /// restrictions installed as `sLemmas`.  Without this, restrictions
    /// like `True_is_true` never fire during precompute saturation,
    /// leaving spurious cases (e.g. Responder for `KU(senc)` in
    /// Pattern_matching::Responder_secrecy) that Haskell would have
    /// dropped via the restriction's implied-formula propagation.
    pub safety_restrictions: Vec<std::sync::Arc<crate::guarded::Guarded>>,
    /// Non-safety restrictions conjoined into each lemma's initial formula.
    pub other_restrictions: Vec<std::sync::Arc<crate::guarded::Guarded>>,
    /// Fact tags whose instances are uniquely identified by their first
    /// argument. Computed once from the theory and immutable thereafter.
    pub injective_fact_insts: std::collections::BTreeMap<
        crate::fact::FactTag,
        Vec<Vec<crate::tools::injective_fact_instances::MonotonicBehaviour>>,
    >,
    /// `pcTrueSubterm` — True iff every destructor rule has its
    /// RHS as a proper subterm of its LHS (`all isSubtermRule $
    /// filter isDestrRule $ intruder_rules`).  Mirrors Haskell's
    /// `_pcTrueSubterm` (System.hs:748-768, see line 764) and gates the
    /// `has_impossible_chain` analysis: when True, only the chain-end
    /// root symbol is checked against the chain-start's possible
    /// decomposition root syms (a STRICTER test that fires more often);
    /// when False, all possible subterm syms of the chain-end are
    /// checked for intersection (a more LENIENT test).
    pub pc_true_subterm: bool,
    /// Solver limits fixed when the context is built, matching Haskell's
    /// explicit `IntegerParameters` threading.
    pub(crate) parameters: crate::constraint::solver::sources::IntegerParameters,
}

/// Minimum-viable context for the solver loop.
#[derive(Debug)]
pub struct ProofContext {
    pub maude: MaudeHandle,
    /// Optional pool of additional Maude subprocesses used at rayon
    /// parallel sites (rule-variant closure, saturate refinement) to
    /// avoid serialising every worker on the single `maude`'s internal
    /// IPC mutex.  `None` means "use the single `maude` only" (the
    /// original behaviour; byte-identical to `--processors=1`).
    ///
    /// HS uses a single Maude per ClosedTheory; this pool is a
    /// Rust-specific implementation improvement that doesn't change
    /// semantics — workers acquire a pool member at task start and
    /// reads/writes its own subprocess for the task's duration.  Each
    /// pool member's `with_fresh_counter_from(avoid_max)` still gives
    /// HS-faithful per-call witness allocation.
    pub maude_pool: Option<std::sync::Arc<MaudePool>>,
    /// Which expanded proof nodes retain their constraint systems.
    pub(crate) sys_retention: crate::constraint::solver::search::SysRetention,
    /// Emit Haskell-compatible source-saturation progress messages.
    pub(crate) show_saturation_steps: bool,
    /// Whether the solver should attempt induction at the start of a
    /// proof. Mirrors Haskell's `pcUseInduction` flag.  Set per-lemma
    /// (`force_induction`), so owned rather than shared.
    pub use_induction: UseInduction,
    /// Set when the current proof is for an exists-trace lemma.
    /// Used by `is_finished` to decide whether the Fresh-conflation
    /// case-drop should convert Contradictory→Unfinishable: for
    /// exists-trace lemmas the dropped case might have been the
    /// witness path (sound only via Unfinishable); for all-traces
    /// lemmas the drop is harmless (no witness to lose).  Defaults
    /// to false; set by `prove_lemma` based on the lemma's
    /// trace-quantifier attribute (per-lemma, so owned).
    pub is_exists_trace: bool,
    /// The solved-leaf extraction strategy for this lemma's auto-prover,
    /// mirroring HS `apCut` (Theory/Proof.hs:696-703, see line 700) threaded from
    /// `--stop-on-trace` (TheoryLoader.hs:397-405).  `Dfs` is the default
    /// (`fromMaybe CutDFS`); consumed once per lemma by `run_proof_search`
    /// (search.rs).  Per-lemma / theory-global, so owned.
    pub cut: CutStrategy,
    /// Pending typing assumptions (from `[sources]`-tagged lemmas)
    /// applied during `ensure_saturated`'s refinement step.  Set by
    /// `prove_lemma` before any source-case access; refinement is
    /// deferred to keep `ensure_saturated`'s trace emissions
    /// interleaved with the lemma proof's first source-case access
    /// (HS-faithful: `refineWithSourceAsms` operates on lazy `Source`
    /// thunks; its work only fires when a downstream consumer forces
    /// a `cdCases` thunk).  Per-lemma, so owned.
    pub typing_assumptions: Vec<std::sync::Arc<crate::guarded::Guarded>>,
    /// The goal ranking list for this lemma, mirroring HS's
    /// `Heuristic ProofContext = Heuristic [GoalRanking ProofContext]`
    /// (System.hs:521-522).  `None` ⇒ HS's `defaultHeuristic False`
    /// (`defaultRankings False = [SmartRanking False]`, System.hs:525-527, see line 526).
    /// Resolved per-lemma in `prove_lemma`
    /// (per-lemma `[heuristic=..]` overrides the theory-level directive,
    /// matching `apDefaultHeuristic <|> pcHeuristic`).
    /// Round-robin scheduling: depth d → `rankings[d % n]`
    /// (ProofMethod.hs).  Per-lemma, so owned.
    pub heuristic: Option<Vec<crate::constraint::solver::goals::GoalRanking>>,
    /// Whether lazily refining this context's sources can fail. Fallible
    /// searches stay serial so an error cannot be hidden behind an unbounded
    /// sibling running in parallel.
    /// The name of the lemma being proved.  Passed as `argv[1]` to
    /// the oracle script (HS `L.get pcLemmaName ctxt`, ProofMethod.hs).
    /// Per-lemma, so owned.
    pub lemma_name: String,
    /// Path to the theory file being proved.  Used to resolve the
    /// oracle script path as `takeDirectory theory_file </> oracle_rel_path`
    /// (HS Theory/Text/Parser.hs:309, System.hs:575-576).  Stored as the absolute
    /// path passed to `--prove`.  Per-lemma, so owned.
    pub theory_file: String,
    /// Source-cell layout for this context. Session-backed contexts own these
    /// lightweight cells while sharing their materialised case vectors.
    pub(crate) full_sources: std::sync::Arc<Vec<crate::constraint::solver::sources::Source>>,
    /// Optional session-level source materialiser. Batch/web contexts install
    /// this so the first actual `pcSources` access can populate the shared
    /// raw/refined cache; standalone contexts saturate themselves directly.
    pub(crate) source_provider: Option<std::sync::Arc<dyn SourceProvider>>,
    /// Per-context lazy saturation gate.
    pub(crate) saturate_gate: SaturateGate,
    /// Read-only theory data (`intruder_rules`, `restrictions`, …), shared
    /// behind an `Arc`. Field reads are
    /// transparent through the [`std::ops::Deref`] implementation below.
    pub shared: std::sync::Arc<ProofContextShared>,
}

/// Theory-wide inputs used to build a proof context.
#[derive(Default)]
pub struct ProofContextOptions {
    pub maude_pool: Option<std::sync::Arc<MaudePool>>,
    pub restrictions: Vec<crate::guarded::Guarded>,
    pub forced_injective_facts: Vec<crate::fact::FactTag>,
    pub intruder_rules: Option<IntrRuleCache>,
    pub parameters: crate::constraint::solver::sources::IntegerParameters,
    pub sys_retention: crate::constraint::solver::search::SysRetention,
    pub show_saturation_steps: bool,
    /// The caller already annotated loop breakers while closing the theory.
    /// Standalone contexts leave this false. Variant preparation is completed
    /// here in either case because raw AC queries are phase-sensitive.
    pub loop_breakers_prepared: bool,
}

pub(crate) trait SourceProvider: std::fmt::Debug + Send + Sync {
    /// Whether materialisation can fail for this provider. Unknown
    /// implementations are conservatively fallible.
    fn may_fail(&self) -> bool {
        true
    }

    fn materialize(&self, ctx: &ProofContext) -> Result<(), crate::prove::ProveError>;
}

/// Transparent read access to immutable theory data.
impl std::ops::Deref for ProofContext {
    type Target = ProofContextShared;
    fn deref(&self) -> &ProofContextShared {
        &self.shared
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SaturateState {
    Pending,
    InProgress(std::thread::ThreadId),
    Done(Result<(), crate::prove::ProveError>),
}

#[derive(Debug)]
pub(crate) struct SaturateGate {
    state: std::sync::Mutex<SaturateState>,
    ready: std::sync::Condvar,
}

impl SaturateGate {
    fn new(state: SaturateState) -> Self {
        Self {
            state: std::sync::Mutex::new(state),
            ready: std::sync::Condvar::new(),
        }
    }
}

impl ProofContext {
    pub(crate) fn proving_may_fail(&self) -> bool {
        self.source_provider
            .as_ref()
            .is_some_and(|provider| provider.may_fail())
            || self
                .heuristic
                .as_deref()
                .is_some_and(crate::constraint::solver::goals::rankings_may_fail)
    }

    /// Materialise this context's sources and return independent working
    /// copies. Source forcing belongs here so a caller cannot accidentally
    /// pair a lazy source cell with a different context.
    pub fn source_cases(
        &self,
    ) -> Result<
        Vec<(
            crate::constraint::constraints::Goal,
            Vec<crate::constraint::solver::sources::SourceCase>,
        )>,
        crate::prove::ProveError,
    > {
        self.ensure_saturated()?;
        Ok(self
            .full_sources
            .iter()
            .map(|source| (source.goal.clone(), source.cases_or_empty()))
            .collect())
    }

    /// Return one materialised source-case system by zero-based indices.
    pub fn source_case_system_at(
        &self,
        source: usize,
        case: usize,
    ) -> Result<Option<crate::constraint::system::System>, crate::prove::ProveError> {
        self.ensure_saturated()?;
        Ok(self
            .full_sources
            .get(source)
            .and_then(|source| source.case_system_at(case)))
    }

    fn copy_with_sources(
        &self,
        full_sources: std::sync::Arc<Vec<crate::constraint::solver::sources::Source>>,
        saturate_state: SaturateState,
    ) -> Self {
        Self {
            maude: self.maude.clone(),
            maude_pool: self.maude_pool.clone(),
            sys_retention: self.sys_retention,
            show_saturation_steps: self.show_saturation_steps,
            use_induction: self.use_induction,
            is_exists_trace: self.is_exists_trace,
            cut: self.cut,
            typing_assumptions: self.typing_assumptions.clone(),
            heuristic: self.heuristic.clone(),
            lemma_name: self.lemma_name.clone(),
            theory_file: self.theory_file.clone(),
            full_sources,
            source_provider: self.source_provider.clone(),
            saturate_gate: SaturateGate::new(saturate_state),
            shared: std::sync::Arc::clone(&self.shared),
        }
    }

    /// Build an independent context around a fresh set of lazy source cells.
    /// Materialised cases may still be shared by a session source provider.
    pub(crate) fn fresh_with_sources(
        &self,
        full_sources: std::sync::Arc<Vec<crate::constraint::solver::sources::Source>>,
    ) -> Self {
        self.copy_with_sources(full_sources, SaturateState::Pending)
    }
}

/// Restores saturation's logically local fresh counter and wakes waiters on
/// both normal completion and unwinding. A failed pass becomes retryable
/// instead of leaving the context permanently in progress.
struct SaturationRun<'a> {
    ctx: &'a ProofContext,
    counter_before: u64,
    completed: bool,
}

impl<'a> SaturationRun<'a> {
    fn new(ctx: &'a ProofContext, counter_before: u64) -> Self {
        Self {
            ctx,
            counter_before,
            completed: false,
        }
    }

    fn finish(mut self, result: Result<(), crate::prove::ProveError>) {
        self.ctx.maude.reset_counter_to(self.counter_before);
        *self
            .ctx
            .saturate_gate
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = SaturateState::Done(result);
        self.completed = true;
        self.ctx.saturate_gate.ready.notify_all();
    }
}

impl Drop for SaturationRun<'_> {
    fn drop(&mut self) {
        if self.completed {
            return;
        }
        self.ctx.maude.reset_counter_to(self.counter_before);
        *self
            .ctx
            .saturate_gate
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = SaturateState::Pending;
        self.ctx.saturate_gate.ready.notify_all();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseInduction {
    UseInduction,
    AvoidInduction,
}

/// How the auto-prover cuts the proof tree around solved leaves,
/// mirroring HS `SolutionExtractor` (Theory/Proof.hs:693-694) as selected
/// by `runAutoProver` (Theory/Proof.hs:730-739).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum CutStrategy {
    /// HS `CutDFS` → `cutOnSolvedDFS` (Theory/Proof.hs:845-884): parallel
    /// iterative-deepening DFS, doubling `dMax` from 4.  Selects the leftmost
    /// (preorder, CaseName order) solved leaf among those shallower than the
    /// first `dMax` (4, 8, 16, …) to admit any solved leaf — within that
    /// depth bucket a deeper-but-leftmost leaf beats a shallower one further
    /// right, so this is NOT globally-shallowest.  The default when
    /// `--stop-on-trace` is absent
    /// (HS `constructAutoProver`: `fromMaybe CutDFS`, TheoryLoader.hs:802-810, see line 809).
    #[default]
    Dfs,
    /// HS `CutSingleThreadDFS` → `cutOnSolvedSingleThreadDFS`
    /// (Theory/Proof.hs:788-814): single-thread depth-first with NO depth
    /// bound and NO iterative deepening.  `findSolved`'s `foldMap` over the
    /// children map descends the leftmost branch (CaseName order) to
    /// completion before its siblings and stops at the first solved leaf, so
    /// a deep solved leaf under the leftmost branch wins over a shallower one
    /// further right even when the shallower leaf sits inside `Dfs`'s first
    /// depth bucket (where `Dfs` would cut the deep branch off and pick it).
    SeqDfs,
    /// HS `CutBFS` → `cutOnSolvedBFS` (Theory/Proof.hs:927-955): iterative
    /// level-deepening over the DFS proof tree.  At each level `l` the tree
    /// is forced to depth `l` and walked in CaseName order with threaded
    /// state: a Solved leaf at exactly depth `l` flips TraceFound; a node
    /// still pending at depth `l` is cut to `sorry /* bound reached */`
    /// (`sorry /* ignored (attack exists) */` once TraceFound).  On
    /// TraceFound the CUT tree is the result — those sorry leaves are part
    /// of the printed proof; a level that completes with nothing pending
    /// returns the full tree unchanged.
    Bfs,
    /// HS `CutNothing` → `id` (Theory/Proof.hs:730-739, see line 738): no cut at all — the
    /// full proof tree is built and printed; sibling exploration does not
    /// stop when a trace is found.
    Nothing,
    /// HS `CutAfterSorry` → `cutAfterFirstSorry` (Theory/Proof.hs:986-998):
    /// preorder walk in CaseName order; the first `Sorry` or Solved leaf
    /// aborts, and every node visited after the abort becomes a bare
    /// `sorry` leaf (children dropped, system annotation kept).  Under the
    /// unbounded default prover the only aborter is a Solved leaf, so this
    /// reads as "stop at the first trace, sorry out the remainder".
    AfterSorry,
}

impl ProofContext {
    pub fn new(maude: MaudeHandle, rules: Vec<OpenProtoRule>) -> Self {
        Self::with_options(maude, rules, ProofContextOptions::default())
    }

    /// Cheap clone with `maude` replaced.  Used at the rayon parallel
    /// sites where each worker wants its own subprocess (acquired from
    /// `maude_pool`) for the duration of one task, so workers don't
    /// serialise on a single Maude's IPC mutex.
    ///
    /// Immutable theory data remains shared through `Arc`. Completed source
    /// snapshots are shared with workers; an ordinary worker waits for an
    /// active saturation pass, while a defensive call before saturation gets
    /// independent source cells.
    ///
    /// The new context drops `maude_pool` (set to None): the worker
    /// already owns a per-task subprocess for the task's duration, and
    /// dropping the pool here keeps the nested fan-out (`search.rs`) on
    /// its non-blocking `try_acquire` + `ctx.maude` fallback, which is
    /// what prevents deadlock when the pool is smaller than the rayon
    /// worker count.
    pub fn with_swapped_maude(&self, maude: MaudeHandle) -> Self {
        let parent_state = {
            let mut state = self
                .saturate_gate
                .state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            while matches!(*state, SaturateState::InProgress(_)) {
                state = self
                    .saturate_gate
                    .ready
                    .wait(state)
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
            }
            state.clone()
        };
        let (full_sources, worker_state) = match parent_state {
            SaturateState::Pending => (
                std::sync::Arc::new(self.full_sources.iter().cloned().collect()),
                SaturateState::Pending,
            ),
            SaturateState::InProgress(_) => unreachable!("in-progress saturation was awaited"),
            SaturateState::Done(result) => (
                std::sync::Arc::clone(&self.full_sources),
                SaturateState::Done(result),
            ),
        };
        // Saturation workers read the previous iteration's source cells;
        // proof-search workers inherit an already-complete set. Both are O(1)
        // refcount bumps. A defensive pre-saturation call instead receives
        // independent lazy cells and remains Pending.
        let mut worker = self.copy_with_sources(full_sources, worker_state);
        worker.maude = maude;
        worker.maude_pool = None;
        worker
    }

    /// HS-faithful lazy `saturateSources` (Sources.hs:355-384, see line 373).  Runs at
    /// most once per `ProofContext`: forces `initial_source_cases`
    /// for each source in `full_sources`, then drives
    /// `saturate_sources_with_simp` to convergence.  Subsequent
    /// calls no-op via the `saturate_state` flag.
    ///
    /// Triggered by `Source::cases(ctx)` on first force.  Trivial
    /// protocols whose lemma proofs never pattern-match on source
    /// cases (e.g. Var-headed `KU(t:Fresh)` source on an existence
    /// lemma) never call this, so zero saturate-time `[EXEC]` lines
    /// fire — matching HS's lazy-thunk behaviour.
    pub(crate) fn ensure_saturated(&self) -> Result<(), crate::prove::ProveError> {
        {
            let current_thread = std::thread::current().id();
            let mut state = self
                .saturate_gate
                .state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            loop {
                match &*state {
                    SaturateState::Done(result) => return result.clone(),
                    SaturateState::InProgress(owner) if *owner == current_thread => {
                        // Re-entrant call from inside saturate's own
                        // source-case grafting.  Return without re-running
                        // — the caller sees the partially-populated cells,
                        // matching HS's lazy fix-point semantics where
                        // iteration N forces iteration N-1's cached value.
                        return Ok(());
                    }
                    SaturateState::InProgress(_) => {
                        state = self
                            .saturate_gate
                            .ready
                            .wait(state)
                            .unwrap_or_else(std::sync::PoisonError::into_inner);
                    }
                    SaturateState::Pending => {
                        *state = SaturateState::InProgress(current_thread);
                        break;
                    }
                }
            }
        }
        // Snapshot only after this thread owns the saturation run. A waiter
        // may observe the shared Maude counter while the owner is using it;
        // taking the snapshot before the gate would then restore that
        // transient value instead of the caller's counter.
        let saturate_cnt_before = self.maude.fresh_counter_peek();
        let run = SaturationRun::new(self, saturate_cnt_before);
        if let Some(provider) = &self.source_provider {
            let result = provider.materialize(self);
            run.finish(result.clone());
            return result;
        }
        // HS-FAITHFUL PURITY: source refinement (`precomputeSources` /
        // `saturateSources` / `refineWithSourceAsms`, Sources.hs) is a PURE
        // `[Source] -> [Source]` computation with LOCAL `evalFresh (avoid
        // goalTerm)` scopes — it does NOT thread the per-proof `MonadFresh`
        // counter.  Each proof step independently resets fresh to `avoid sys`
        // (ProofMethod.hs:282-339, see line 305 `runReduction (m <* simplifySystem) ctxt sys
        // (avoid sys)`), and source cases are re-freshened on apply.  RS's
        // saturation, by contrast, advances the shared `maude` counter while
        // computing cases; that advance is HS-invisible and its magnitude is
        // parallelism- and source-structure-dependent (large for SAPiC state
        // facts), which leaks into the proof when the cache skips/replays it.
        // Snapshot the counter and restore it after saturation so the refine
        // is counter-neutral exactly as in HS — making the post-saturation
        // counter (hence cache reuse vs recompute) byte-identical regardless.
        // Pre-populate every source's cell with `Some(vec![])` BEFORE
        // running `initial_source_cases` on any of them.  This breaks
        // the recursion: when `initial_source_cases` for source A
        // calls `solve_with_source_cases_action` against source B
        // (forcing B.cases() recursively), B's cell is already
        // `Some(empty)`, so the recursive call returns empty rather
        // than re-entering `initial_source_cases` for B.  After this
        // pass we run the second pass that fills each cell with the
        // actual unsaturated `initialSource` cases — HS's `mapM`
        // over the lazy list under the iterative fix-point.
        for src in self.full_sources.iter() {
            if src.cases_cell.lock().unwrap().is_none() {
                src.cases_set(Vec::new());
            }
        }
        // Saturation's own solver calls must see the previous iteration's
        // partially populated source cells without recursively entering (or
        // waiting on) this gate. Giving the whole pass one completed view
        // makes that invariant structural; ordinary contexts still wait for
        // the real result in `with_swapped_maude`.
        let saturation_ctx = self.copy_with_sources(
            std::sync::Arc::clone(&self.full_sources),
            SaturateState::Done(Ok(())),
        );
        let result = (|| {
            for src in self.full_sources.iter() {
                let init = crate::constraint::solver::sources::initial_source_cases(
                    &src.goal,
                    &saturation_ctx,
                )?;
                src.cases_set(init);
            }
            // HS-faithful `saturate_sources_with_simp` (mirrors HS's
            // `saturateSources` driven by `solveAllSafeGoals` as the
            // proofStep): each iteration performs HS's per-step
            // `insertEdges`/`solveTermEqs`/`exploitPrems` work, so the
            // emitted trace matches HS's saturation rather than collapsing
            // it into a single graft operation.
            let raw: Vec<crate::constraint::solver::sources::Source> = self.full_sources.to_vec();
            let saturated = crate::constraint::solver::sources::saturate_sources_with_simp(
                raw,
                self.parameters.saturation_limit(),
                &saturation_ctx,
            )?;
            // HS-faithful: apply `refineWithSourceAsms` AFTER saturate.
            // HS does this lazily — `refineWithSourceAsms` produces
            // updated `Source` thunks that only fire their inner saturate
            // when forced.  We approximate by running both inside
            // `ensure_saturated` (which itself is lazy at the first
            // `cases(ctx)` call), so the refinement traces still
            // interleave with the lemma proof's first source-case access
            // rather than firing during `prove_lemma` setup.
            let refined = if self.typing_assumptions.is_empty() {
                saturated
            } else {
                crate::constraint::solver::sources::refine_with_source_asms(
                    saturated,
                    &self.typing_assumptions,
                    &saturation_ctx,
                )?
            };
            // Saturation and refinement preserve one source per input, even
            // when its case list becomes empty. Check that contract before
            // publishing any of the refined cells.
            assert_eq!(self.full_sources.len(), refined.len());
            assert!(self
                .full_sources
                .iter()
                .zip(&refined)
                .all(|(original, refined)| original.goal == refined.goal));
            for (original, refined) in self.full_sources.iter().zip(&refined) {
                original.cases_set_shared(refined.cases_shared_or_empty());
            }
            // Restore the fresh counter to its pre-saturation value (see the
            // HS-FAITHFUL PURITY note above): the refine consumed idxs only for
            // the stored cases, which are re-freshened from `avoid(live_sys)` on
            // every apply, so the global counter must not retain the advance.
            self.dump_sources();
            Ok(())
        })();
        run.finish(result.clone());
        result
    }

    /// Mark this context's sources as already saturated, bypassing the
    /// `ensure_saturated` pass. Used by the session-level refined-source
    /// cache: when raw cases are restored into its internal refinement
    /// context, set the state to `Done` so later
    /// `cases(ctx)` calls read the restored cells directly instead of
    /// re-running the (expensive) `saturate_sources_with_simp` pass.
    pub(crate) fn mark_saturated_done(&self) {
        *self
            .saturate_gate
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = SaturateState::Done(Ok(()));
        self.saturate_gate.ready.notify_all();
    }

    pub(crate) fn set_source_provider(&mut self, provider: std::sync::Arc<dyn SourceProvider>) {
        self.source_provider = Some(provider);
    }

    /// HS-faithful assembly of the intruder-rule cache
    /// (`addMessageDeductionRuleVariants`, TheoryLoader.hs): subterm
    /// constructor rules, special rules, the theory-specific MSet/Xor
    /// rules, the narrowing-based destruction rules for user-defined
    /// symbols, then the DH/BP cached variants — all in HS order.
    /// Depends only on `sig` and `maude`.
    ///
    /// Mirrors Haskell's `addMessageDeductionRuleVariants`:
    ///
    /// ```haskell
    /// rules0 = reader $ \hnd -> subtermConstructorRules False hnd msig
    ///                ++ specialIntruderRules False
    ///                ++ (if enableMSet msig then multisetIntruderRules else [])
    ///                ++ (if enableXor msig then xorIntruderRules else [])
    /// rulesAC   = destructionRulesAC False (acUserFunSyms msig)
    /// rulesNoEq = destructionRulesNoEq False (noEqFunSyms msig)
    /// rules     = liftA2 (++) rules0 (liftA2 (++) rulesAC rulesNoEq)
    /// ```
    ///
    /// (Note that HS's trace-mode `rules0` does NOT include
    /// `natIntruderRules` — only the diff-mode assembly adds it.)
    /// Intruder rules arrive here fully processed: the destruction-rule
    /// generators already compute variants and per-rule chain budgets, so
    /// no per-rule closing pass runs at cache-build time (HS
    /// `closeRuleCache`: `rulesAC = (fmap IntrInfo <$> intrRules) <|> ...`).
    ///
    /// The ORDER MATTERS for solveAction's `disjunctionOfList rules` —
    /// a `KU(aenc(t1,t2))` goal is matched against c_aenc BEFORE
    /// coerce, producing cdCases = [c_aenc, coerce] instead of
    /// [coerce, c_aenc].  This downstream determines which case
    /// applies first in the proof renderer (e.g. NSPK3 injective_agree
    /// picks `case c_aenc` like Haskell does).
    ///
    /// `pub(crate)` for the load-time NDC pass
    /// (`close_rule::check_close_intr_rule`), which assembles the same
    /// cache once per theory before checking/permuting it.
    pub(crate) fn assemble_intruder_rules(
        sig: &tamarin_term::maude_sig::MaudeSig,
        maude: &MaudeHandle,
        initial: &[IntrRuleAC],
    ) -> Vec<IntrRuleAC> {
        let mut intruder_rules =
            crate::intruder_rules::subterm_constructor_rules(false, maude, sig);
        intruder_rules.extend(crate::intruder_rules::special_intruder_rules(false));
        // For multiset: adds `_union` destructor (`KD(x++y) → KD(x)`,
        // subterm=True, budget=0) and `_union` constructor.  Without these,
        // the precomputed `KU(t)` source-cases miss the chain-extension
        // path through union-decomposition, causing `hasImpossibleChain`
        // to fire on legitimate chains from `KD(t1++t2)` to `KD(t1)`.
        // Root cause of the `minimal_multiset::Reachable`/`issue519` cluster.
        if sig.enable_mset {
            intruder_rules.extend(crate::intruder_rules::multiset_intruder_rules());
        }
        // XOR intruder rules — port of HS `xorIntruderRules`
        // (IntruderRules.hs:404-413) wired in `addMessageDeduction
        // RuleVariants` (TheoryLoader.hs:878-900, see line 894).  Two destructor rules
        // for XOR cancellation (KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z) and
        // KD(x⊕y) ∧ KU(y) → KD(x)), one constructor (KU(x⊕y) from
        // KU(x), KU(y)), plus the `zero` constructor.  Without
        // these every XOR-using theory is unsound: the canonical
        // adversary attack `(x⊕y) ⊕ y = x` is unreachable, so
        // `xor.spthy::Secret` and all `recentalive_tag`-style lemmas
        // wrongly verify.  Mirrors HS's enableXor branch.
        if sig.enable_xor {
            intruder_rules.extend(crate::intruder_rules::xor_intruder_rules());
        }
        // Narrowing-based destruction rules for user-defined function
        // symbols — HS `rulesACNoEq`:
        //
        // ```haskell
        // rulesAC   = destructionRulesAC False (acUserFunSyms msig)
        // rulesNoEq = destructionRulesNoEq False (noEqFunSyms msig)
        // rulesACNoEq = liftA2 (++) rulesAC rulesNoEq
        // ```
        //
        // AC first, then NoEq; appended after `rules0` and before the
        // DH/BP cached variants.
        intruder_rules.extend(crate::intruder_rules::destruction_rules_ac(
            false,
            maude,
            &sig.ac_user_fun_syms(),
        ));
        intruder_rules.extend(crate::intruder_rules::destruction_rules_no_eq(
            false,
            maude,
            &sig.no_eq_fun_syms(),
        ));
        // DH / BP intruder variants — port of HS
        // `Main.TheoryLoader.addMessageDeductionRuleVariants`
        // (src/Main/TheoryLoader.hs):
        //
        // ```haskell
        // addMessageDeductionRuleVariants thy0
        //   | enableBP msig = addIntruderVariants
        //                       [mkDhIntruderVariants, mkBpIntruderVariants]
        //   | enableDH msig = addIntruderVariants [mkDhIntruderVariants]
        //   | otherwise     = thy
        // ```
        //
        // HS's `mkDhIntruderVariants` (TheoryLoader.hs:860-867)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`
        // (Template-Haskell `embedFile`), not the runtime
        // `dhIntruderRules` generator.  HS's `Main.Mode.Intruder.run`
        // is what PRODUCES that cache file in the first place
        // (Main/Mode/Intruder.hs:43-63, see line 48), but the production theory-load
        // path always reads the cache.
        //
        // The cached-file parser (`mk_dh_intruder_variants` /
        // `mk_bp_intruder_variants` from `crate::intruder_variants`)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`,
        // matching HS's `mkDhIntruderVariants` (TheoryLoader.hs:860-867)
        // and making us mechanism-identical to HS.  The runtime
        // generator (`dh_intruder_rules`) is retained as the regenerator
        // (callable when one wants to refresh the cache from local
        // Maude); a bridge test in `tests/intruder_variants_render.rs` flags any
        // divergence.
        //
        // Ordering matches HS exactly: DH BEFORE BP, both AFTER
        // subterm + special rules.  When BP is enabled HS adds DH
        // FIRST (the list `[mkDhIntruderVariants, mkBpIntruderVariants]`
        // — TheoryLoader.hs:878-900, see line 885).
        if sig.enable_bp {
            intruder_rules.extend(crate::intruder_variants::mk_dh_intruder_variants(sig));
            intruder_rules.extend(crate::intruder_variants::mk_bp_intruder_variants(sig));
        } else if sig.enable_dh {
            intruder_rules.extend(crate::intruder_variants::mk_dh_intruder_variants(sig));
        }
        // HS `addIntrRuleACsAfterTranslate rs'` is `nub (rs ++ rs')`:
        // source-declared cache entries lead, generated rules follow, and the
        // first structurally equal rule survives.
        let mut assembled = initial.to_vec();
        for rule in intruder_rules {
            if !assembled.contains(&rule) {
                assembled.push(rule);
            }
        }
        assembled
    }

    /// Debug dump of the context's final intruder-rule cache, gated by
    /// `TAM_RS_DBG_INTR_DUMP`.
    fn dump_intruder_rules(out: &[IntrRuleAC]) {
        if !tamarin_utils::env_gate!("TAM_RS_DBG_INTR_DUMP") {
            return;
        }
        use crate::rule::IntrRuleACInfo;
        let pf = |fs: &[crate::fact::LNFact]| {
            fs.iter()
                .map(crate::pretty_system::pretty_fact)
                .collect::<Vec<_>>()
                .join(", ")
        };
        for (i, r) in out.iter().enumerate() {
            let kind = match &r.info {
                IntrRuleACInfo::ConstrRule { name, .. } => {
                    format!("CONSTR {}", String::from_utf8_lossy(name))
                }
                IntrRuleACInfo::DestrRule {
                    name,
                    remaining_applications,
                    rhs_is_proper_subterm,
                    rhs_is_constant,
                    ..
                } => format!(
                    "DESTR {} b={} s={} c={}",
                    String::from_utf8_lossy(name),
                    remaining_applications,
                    rhs_is_proper_subterm,
                    rhs_is_constant
                ),
                other => format!("{:?}", other),
            };
            eprintln!(
                "[INTRDUMP] {} {} | prems=[{}] concs=[{}]",
                i,
                kind,
                pf(&r.premises),
                pf(&r.conclusions)
            );
        }
    }

    /// Debug dump of this context's precomputed sources — one line per
    /// source, with its goal and its materialised case names — gated by
    /// `TAM_RS_DBG_SOURCES_DUMP`.
    fn dump_sources(&self) {
        if !tamarin_utils::env_gate!("TAM_RS_DBG_SOURCES_DUMP") {
            return;
        }
        use crate::constraint::constraints::Goal;
        for (i, src) in self.full_sources.iter().enumerate() {
            let goal = match &src.goal {
                Goal::Action(_, fa) => format!("Action {}", crate::pretty_system::pretty_fact(fa)),
                Goal::Premise(_, fa) => {
                    format!("Premise {}", crate::pretty_system::pretty_fact(fa))
                }
                _ => "other".to_string(),
            };
            let names: Vec<String> = src
                .cases_cell
                .lock()
                .unwrap()
                .as_ref()
                .map(|cs| {
                    cs.lock()
                        .unwrap()
                        .iter()
                        .map(|(ns, _)| ns.join("_"))
                        .collect()
                })
                .unwrap_or_default();
            eprintln!(
                "[SRCDUMP] {} goal=<{}> ncases={} names={:?}",
                i,
                goal,
                names.len(),
                names
            );
        }
    }

    /// Cache permutation performed by HS `prettyNDCcheck` (CloseRule.hs),
    /// which `checkCloseIntrRule` (TheoryLoader.hs:569) runs on the
    /// assembled cache right after `addMessageDeductionRuleVariants`:
    ///
    /// ```haskell
    /// (builtInOrConstrOrNDC, nonBuiltInDestr) = partition
    ///     (\x -> isBuiltInIntruderRule x || isConstrRule x
    ///            || isJust (isNDCRule x)) initRules
    /// t' = groupBy ((==) `on` getDestrRuleFunction)
    ///          $ sortOn getDestrRuleFunction nonBuiltInDestr
    /// (subtermRules, t) = partition (all isSubtermRule) t'
    /// -- result: concat t ++ builtInOrConstrOrNDC ++ concat subtermRules
    /// ```
    ///
    /// i.e. checked (non-all-subterm) user destructor groups first, then the
    /// builtin/constructor/NDC-tagged rules in assembly order, then the
    /// all-subterm user destructor groups.  The order feeds chain-extension
    /// and source-case enumeration, so it is parity-relevant (e.g. the
    /// `C_2_case_NN` source numbering of csf18-xor/chaum theories).
    ///
    /// Only the permutation is applied here — the property check itself
    /// (`crate::close_rule::pretty_ndc_check`) is bypassed.  Applied to
    /// contexts built WITHOUT an injected cache (tests / library callers):
    /// the load paths run the check once per theory
    /// (`close_rule::check_close_intr_rule`) and inject its result, so a
    /// non-injected construction never re-runs the proving work.
    /// The concatenation order lives in `close_rule::ndc_cache_order`,
    /// shared with `pretty_ndc_check` so the two cannot drift.
    fn ndc_check_cache_order(rules: Vec<IntrRuleAC>) -> Vec<IntrRuleAC> {
        let (builtin_or_constr_or_ndc, checked_groups, all_subterm) =
            crate::close_rule::partition_for_ndc(rules);
        crate::close_rule::ndc_cache_order(
            checked_groups.into_iter().flatten().collect(),
            builtin_or_constr_or_ndc,
            all_subterm,
        )
    }

    /// Build a context with explicit theory-wide options.
    pub fn with_options(
        maude: MaudeHandle,
        rules: Vec<OpenProtoRule>,
        options: ProofContextOptions,
    ) -> Self {
        Self::try_with_options(maude, rules, options)
            .expect("prepare protocol-rule variants for proof context")
    }

    /// Build a context while preserving Maude failures from protocol-rule
    /// variant preparation. Frontends use this form so a broken transport
    /// cannot be mistaken for a rule with no variants.
    pub fn try_with_options(
        maude: MaudeHandle,
        rules: Vec<OpenProtoRule>,
        options: ProofContextOptions,
    ) -> Result<Self, crate::tools::rule_variants::VariantsError> {
        let ProofContextOptions {
            maude_pool,
            restrictions,
            forced_injective_facts,
            intruder_rules: intr_override,
            mut parameters,
            mut sys_retention,
            show_saturation_steps,
            loop_breakers_prepared,
        } = options;
        let mut rules = rules;
        if std::env::var_os("TAM_RS_KEEP_SYS").is_some() {
            sys_retention = crate::constraint::solver::search::SysRetention::KeepAll;
        }
        let (safety_restrictions, other_restrictions) = restrictions
            .into_iter()
            .map(std::sync::Arc::new)
            .partition(|restriction| crate::guarded::is_safety_formula(restriction));
        // Inherit the maude signature from the handle so we can
        // synthesise per-symbol construction rules.
        let sig = maude.maude_sig();
        // Injected cache = the theory's once-per-load NDC-checked rules,
        // consumed verbatim (HS `closeRuleCache` on `_thyCache`).
        // Without one, assemble from the signature and apply the NDC
        // cache permutation — never the property check, which runs only
        // once per theory at load (`close_rule::check_close_intr_rule`).
        let intruder_rules: IntrRuleCache = match intr_override {
            Some(cache) => cache,
            None => IntrRuleCache::from(Self::ndc_check_cache_order(
                Self::assemble_intruder_rules(&sig, &maude, &[]),
            )),
        };
        Self::dump_intruder_rules(&intruder_rules);
        // Detect injective fact instances ahead of time — mirrors
        // Haskell's `pcInjectiveFactInsts` precomputation.
        let proto_rules: Vec<crate::rule::ProtoRuleE> =
            rules.iter().map(|r| r.rule.clone()).collect();
        let proto_rule_refs: Vec<&crate::rule::ProtoRuleE> = proto_rules.iter().collect();
        let mut injective_fact_insts =
            crate::tools::injective_fact_instances::simple_injective_fact_instances(
                &proto_rule_refs,
                &sig.reducible_fun_syms_fast,
            );
        // HS `closeRuleCache` (CloseRule.hs:417-420): union the FORCED injective
        // fact tags BEFORE source precomputation reads `injective_fact_insts`.
        if !forced_injective_facts.is_empty() {
            injective_fact_insts =
                crate::tools::injective_fact_instances::union_forced_injective_fact_instances(
                    injective_fact_insts,
                    &forced_injective_facts,
                );
        }
        let injective_fact_insts = injective_fact_insts.into_iter().collect();
        if !loop_breakers_prepared {
            annotate_loop_breakers(&mut rules.iter_mut().collect::<Vec<_>>(), &maude);
        }
        for rule in &mut rules {
            crate::tools::rule_variants::prepare_open_rule_variant(rule, &maude)?;
        }
        // `pcTrueSubterm` — all destructor rules are subterm rules.
        let pc_true_subterm = intruder_rules
            .iter()
            .filter(|r| crate::rule::is_destr_rule(&r.info))
            .all(|r| crate::rule::is_subterm_rule_info(&r.info));
        let unique_action_shapes = {
            let mut counts = std::collections::BTreeMap::new();
            for action in rules
                .iter()
                .flat_map(|rule| &rule.rule.actions)
                .chain(intruder_rules.iter().flat_map(|rule| &rule.actions))
            {
                *counts
                    .entry((action.tag, action.terms.len()))
                    .or_insert(0usize) += 1;
            }
            counts
                .into_iter()
                .filter_map(|(shape, count)| (count == 1).then_some(shape))
                .collect()
        };
        // The diagnostic environment knob deliberately outranks the frontend
        // value, but is still snapshotted with the rest of this context.
        if let Some(limit) = std::env::var("TAM_SATURATION_LIMIT")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
        {
            parameters = parameters.with_saturation_limit(limit);
        }
        let mut ctx = ProofContext {
            maude,
            maude_pool,
            sys_retention,
            show_saturation_steps,
            use_induction: UseInduction::AvoidInduction,
            is_exists_trace: false,
            cut: CutStrategy::Dfs,
            typing_assumptions: Vec::new(),
            heuristic: None,
            lemma_name: String::new(),
            theory_file: String::new(),
            full_sources: std::sync::Arc::new(Vec::new()),
            source_provider: None,
            saturate_gate: SaturateGate::new(SaturateState::Pending),
            shared: std::sync::Arc::new(ProofContextShared {
                rules,
                intruder_rules,
                unique_action_shapes,
                safety_restrictions,
                other_restrictions,
                injective_fact_insts,
                pc_true_subterm,
                parameters,
            }),
        };
        // Precompute full source-case enumerations.  Runs *after*
        // rule construction and with an empty `full_sources` itself so there's
        // no recursive lookup during precomputation. Saturates the cases via
        // `saturate_sources` so recursive Loop-style chains fold into a finite
        // enumeration of self-contained sub-systems.
        // Install rule variants BEFORE precompute, so
        // `precompute_full_sources` sees the variant-expanded (abstracted)
        // rule set, matching HS (whose
        // precompute runs over `cprRuleAC`; Items/RuleItem.hs:56-59, see line 58).
        //
        let raw_sources = crate::constraint::solver::sources::precompute_full_sources(&ctx);
        // HS-faithful lazy precompute: `saturateSources` (Sources.hs:355-384, see line 373)
        // is *lazy in cdCases* — its `refineSource ctxt solver`
        // applications produce `Source`s whose updated `cdCases` is
        // itself a thunk that forces only when a consumer pattern-
        // matches on `(name, sys) <- get cdCases th` in a Disj-monad
        // bind.  For protocols where the lemma proof never forces a
        // particular source's `cdCases` (e.g. `Heard`-style existence
        // lemmas on a Var-headed `KU(t:Fresh)` source — HS's
        // `getMsgOneCase` short-circuits on the goal-shape pattern
        // before touching `cdCases`), the thunk never runs and zero
        // saturate-time `[EXEC] solveGoal / exploitPrems / ...` lines
        // are emitted.
        //
        // To preserve this laziness we defer saturation to the first
        // `Source::cases(ctx)` call via `ProofContext::ensure_saturated`
        // (which drives `saturate_sources_with_simp`).  `ctx.full_sources`
        // holds the unsaturated raw sources from `precompute_full_sources`
        // (each with `cases_cell = None`); no `[EXEC] solveGoal /
        // exploitPrems / ...` lines fire here — they only fire when a
        // lemma proof forces a source's cases via pattern-matching on its
        // `cdCases` (HS-faithful).
        ctx.full_sources = std::sync::Arc::new(raw_sources);
        // No saturation here — `ctx.full_sources` holds unsaturated
        // raw sources.  `prove_lemma` calls `ctx.ensure_saturated()`
        // AFTER assigning `ctx.typing_assumptions` so that
        // `refine_with_source_asms` runs with the lemma's [sources]
        // assumptions in hand.  Matches HS's `refineWithSourceAsms`
        // timing where `[Saturating Sources] Done` fires after
        // assumptions are applied.
        // No post-saturate drop pass — Haskell doesn't have one.
        // Haskell relies on saturate-time `contradictoryIf` inside
        // `solveAllSafeGoals` (Sources.hs:174-178, see line 178) + runtime
        // contradiction detection during proof search.
        Ok(ctx)
    }
}

/// Mutate `rules` in place, populating each rule's
/// `info.loop_breakers` from the dataflow relation.  Mirrors Haskell's
/// `useAutoLoopBreakersAC`:
///
/// 1. Build a dataflow over-approximation:
///    `(ruFrom, (ruTo, premIdx))`
///    where some conclusion of `ruFrom` has the same fact tag as the
///    `premIdx`-th premise of `ruTo`.
/// 2. Lift to the premise-solving relation by pairing every `(ruTo,
///    premIdx)` with every premise of `ruFrom`:
///    `((ruTo, premIdx), (ruFrom, fromPrem))`
/// 3. `dfs_loop_breakers` returns the set of `(rule, prem_idx)`
///    targets to mark — the premises whose goals should be tagged
///    loop-breaker.
///
/// The rules are taken by `&mut` reference each, so a caller holding them
/// inside a theory can borrow them where they live: only `loop_breakers` is
/// written, and a `Vec<OpenProtoRule>` copy would deep-clone every rule's
/// `variant_substs` and `abstracted_rule` just to copy that one field back.
pub(crate) fn annotate_loop_breakers(
    rules: &mut [&mut OpenProtoRule],
    maude: &tamarin_term::maude_proc::MaudeHandle,
) {
    use crate::rule::PremIdx;

    // HS keys the relation nodes by the WHOLE closed theory item under its
    // derived `Ord` (`useAutoLoopBreakersAC`'s carrier `a`, matched back to
    // rules with full `ru == ru'` equality, LoopBreakers.hs:72-81) — NOT by
    // rule name.  After partial evaluation several refined rules share one
    // name with different bodies; each is its own graph node in HS, while a
    // name key would collapse them and fabricate cycles (e.g. the refined
    // `ChanIn_A` rules of csf20-disputeResolution/PR1_ShHh.spthy, where the
    // oracle renders zero breakers).  Key each rule by the index of the
    // first structurally-equal rule: structurally identical items collapse
    // exactly as HS's `Ord`-keyed sets collapse them, and everything else
    // stays distinct.  `loop_breakers` is deliberately NOT part of the
    // identity — HS compares the pre-annotation items, where every
    // `pracLoopBreakers` is still `[]`.
    let same_item = |a: &OpenProtoRule, b: &OpenProtoRule| -> bool {
        a.rule == b.rule
            && a.variant_substs == b.variant_substs
            && a.abstracted_rule == b.abstracted_rule
    };
    let mut keys: Vec<usize> = Vec::with_capacity(rules.len());
    for i in 0..rules.len() {
        let k = (0..i).find(|&j| same_item(rules[j], rules[i])).unwrap_or(i);
        keys.push(k);
    }

    // HS `premSolvingRelAC` builds the dataflow relation over `instances`:
    //   `instances ru fa = [ apply (subst `freshToFreeAvoiding` fa) fa
    //                       | subst <- eVariants ru ]`   (LoopBreakers.hs:55-57)
    // where `eVariants ru` is the rule's AC-VARIANT disjunction
    // (`variantsProtoRule`).  For a rule whose conclusion carries a
    // reducible/DH-laden term (e.g. GDH RecvOthers concludes
    // `!AO(.., 'g'^y^~esk)`), a variant substitution expands that term to a
    // syntactic-AC form (`z.1 = 'g'^(~esk*y)`) that Maude's plain `unify`
    // can solve against another rule's premise (`!AO(.., 'g'^y)`).  Unifying
    // the RAW E-rule facts instead — as RS did — sends the local `unifyRaw`
    // (and Maude) `exp(exp('g',y),esk) =? exp('g',y')`, a NESTED-exp
    // narrowing problem the AC unifier rejects, so the dataflow edge (and
    // hence the loop-breaker cycle) is never found.
    //
    // `populate_rule_variants` (run.rs) already computed and stored each
    // rule's variant disjunction (keyed by the *abstracted* rule's fresh
    // z-vars) on every `OpenProtoRule` BEFORE `annotate_loop_breakers`
    // runs, so reuse `o.variant_substs`/`o.abstracted_rule` rather than
    // recomputing via the narrowing-only `variant_substs_for_rule` (which
    // misses DH `exp`/`mult` variant expansion).  When variants are empty
    // (no reducible sub-terms, or this is the precompute call before
    // population) `instances` yields the bare fact, preserving prior
    // behaviour.
    let variant_substs: Vec<&Vec<tamarin_term::subst_vfresh::LNSubstVFresh>> =
        rules.iter().map(|o| &o.variant_substs).collect();

    // `instances ru fa`: apply each variant subst (as a free subst via
    // `freshToFreeAvoiding`) to `fa`.  Empty variant list ⇒ `[fa]`.
    let instances = |rule_idx: usize, fa: &crate::fact::LNFact| -> Vec<crate::fact::LNFact> {
        use tamarin_term::lterm::HasFrees;
        let substs = variant_substs[rule_idx];
        if substs.is_empty() || substs.iter().all(|s| s.is_empty()) {
            return vec![fa.clone()];
        }
        substs
            .iter()
            .map(|s| {
                // HS `apply (subst `freshToFreeAvoiding` fa) fa`: rename the
                // VFresh range vars to fresh free vars avoiding `fa`'s frees,
                // then apply.  We seed the witness counter above the max idx
                // appearing in `fa` (the avoid set), matching HS's
                // `evalFreshAvoiding (frees fa)`.
                let mut avoid_max: u64 = 0;
                fa.for_each_free(&mut |v| {
                    if v.idx + 1 > avoid_max {
                        avoid_max = v.idx + 1;
                    }
                });
                let mut next = avoid_max;
                let free = s.fresh_to_free(|_| {
                    let i = next;
                    next += 1;
                    i
                });
                // freshToFree rename + apply — frees change; recompute the bloom.
                let terms: Vec<tamarin_term::lterm::LNTerm> = fa
                    .terms
                    .iter()
                    .map(|t| tamarin_term::subst::apply_vterm(&free, t.clone()))
                    .collect();
                crate::fact::LNFact::fresh_annotated(fa.tag, fa.annotations.clone(), terms)
            })
            .collect()
    };

    // Build the prem-solving relation, mirroring HS's `premSolvingRelAC`
    // (`LoopBreakers.hs:35-58`) EXACTLY, including iteration nesting —
    // `dfsLoopBreakers` walks the relation in list order, so the order
    // determines which node becomes each DFS root and therefore which
    // breakers are picked.
    //
    // HS structure:
    //   dataflowRelAC: ruFrom <- rules; ruTo <- rules;
    //                  (premIdx,premFa0) <- ePrems ruTo; [unifiable];
    //                  return (ruFrom, (ruTo, premIdx))
    //   premSolvingRelAC: (toRu=ruFrom, from=(ruTo,premIdx)) <- dataflowRelAC;
    //                     (toPrem,_) <- ePrems toRu;
    //                     return (from, (toRu, toPrem))
    //                   = ((ruTo,premIdx), (ruFrom,toPrem))
    //
    // So the nesting is: ruFrom (outer) → ruTo → premIdx(of ruTo) →
    // toPrem(of ruFrom, innermost).  Each emitted element's FIRST
    // component is (ruTo, premIdx); the relation appears grouped by
    // ruFrom because that's the outermost loop.
    // HS enumerates premises/conclusions of the AC rule, i.e. the
    // *abstracted* rule (whose reducible-headed sub-terms are replaced by
    // the fresh z-vars the variant substs are keyed on).  Use
    // `abstracted_rule` when present, falling back to the raw E-rule.
    let ac_rules: Vec<&crate::rule::ProtoRuleE> = rules
        .iter()
        .map(|o| o.abstracted_rule.as_ref().unwrap_or(&o.rule))
        .collect();
    // `instances` is a pure function of `(rule_idx, fact)`, so each rule's
    // premise and conclusion instance lists are built once here rather than
    // once per `(ru_from, ru_to, premise)` triple of the loop below.
    let prem_insts_by_rule: Vec<Vec<Vec<crate::fact::LNFact>>> = ac_rules
        .iter()
        .enumerate()
        .map(|(i, ru)| {
            ru.enumerate_premises()
                .map(|(_, fa)| instances(i, fa))
                .collect()
        })
        .collect();
    let conc_insts_by_rule: Vec<Vec<Vec<crate::fact::LNFact>>> = ac_rules
        .iter()
        .enumerate()
        .map(|(i, ru)| ru.conclusions.iter().map(|fa| instances(i, fa)).collect())
        .collect();

    let mut relation: Vec<((usize, PremIdx), (usize, PremIdx))> = Vec::new();
    for (i_from, _ru_from) in rules.iter().enumerate() {
        let ru_from_ac = ac_rules[i_from];
        for (i_to, _ru_to) in rules.iter().enumerate() {
            let ru_to_ac = ac_rules[i_to];
            for (to_prem_idx, prem_fa) in ru_to_ac.enumerate_premises() {
                // HS `dataflowRelAC` (LoopBreakers.hs:43-54) enumerates ALL
                // premises (`enumPrems`, Theory/Model/Rule.hs:258-259) with no tag filter;
                // the only premise-level guard is `not (isNoSourcesFact …)`.
                // Non-Proto premises are kept here too: the tag-equality
                // (`c0.tag != prem_fa.tag`) + `unifiable_ln_facts` gates below
                // already exclude any conclusion that cannot form an edge,
                // exactly as HS's `unifiableLNFacts` does (it returns []
                // whenever `factTag fa1 /= factTag fa2`,
                // Theory/Model/Fact.hs:472-480, see line 474).
                //
                // Haskell `LoopBreakers.hs:30-58, see line 48`:
                //   `guard $ not (isNoSourcesFact premFa0)`
                if prem_fa.is_no_sources() {
                    continue;
                }
                // Haskell `LoopBreakers.hs:49-53`: edge exists iff some
                // conclusion of `ruFrom` is AC-UNIFIABLE with this premise
                // (not merely same-tag).  Tag-only matching over-approximates
                // and adds spurious self-edges (e.g. `I_m0`'s `St_I(<'m2'>)`
                // conclusion vs its own `St_I('m0')` premise share a tag but
                // do NOT unify), which fabricate extra cycles and over-mark
                // loop breakers.  Use real Maude unifiability, mirroring HS.
                //
                // HS `dataflowRelAC` (LoopBreakers.hs:49-53):
                //   guard $ or $ do
                //     premFa <- instances ruTo premFa0
                //     concFa <- instances ruFrom =<< (snd <$> eConcs ruFrom)
                //     let concFaFresh = rename concFa `evalFresh` avoid premFa
                //     return $ unifiableLNFacts concFaFresh premFa
                // i.e. iterate the VARIANT INSTANCES of both the premise and
                // each conclusion, rename the conclusion away from the
                // premise's frees, and check Maude AC-unifiability.
                let prem_insts = &prem_insts_by_rule[i_to][to_prem_idx.0];
                let conc_unifies = ru_from_ac.conclusions.iter().enumerate().any(|(ci, c0)| {
                    if c0.tag != prem_fa.tag {
                        return false;
                    }
                    conc_insts_by_rule[i_from][ci].iter().any(|conc| {
                        prem_insts.iter().any(|prem| {
                            let mut fresh = tamarin_term::lterm::avoid(prem);
                            let conc_fresh = tamarin_term::lterm::rename(conc.clone(), &mut fresh);
                            crate::rule::unifiable_ln_facts(maude, &conc_fresh, prem)
                                .unwrap_or(false)
                        })
                    })
                });
                if !conc_unifies {
                    continue;
                }
                for (from_prem_idx, _) in ru_from_ac.enumerate_premises() {
                    relation.push(((keys[i_to], to_prem_idx), (keys[i_from], from_prem_idx)));
                }
            }
        }
    }
    // Run DFS loop-breaker selection. `dfsLoopBreakers` lives in HS
    // `Data.DAG.Simple`, ported to `tamarin_utils::dag`.
    let breakers: Vec<(usize, PremIdx)> = tamarin_utils::dag::dfs_loop_breakers(&relation);
    // Annotate each rule's `loop_breakers` with the picked premises (HS
    // `[ u | (ru', u) <- breakers, ru == ru' ]` — equal items share one
    // node and therefore one breaker set).
    for (k, ru) in keys.iter().zip(rules.iter_mut()) {
        ru.loop_breakers = breakers
            .iter()
            .filter(|(rk, _)| rk == k)
            .map(|(_, p)| *p)
            .collect();
    }
}

/// Run [`annotate_loop_breakers`] over a theory's rules, in place and in
/// source order.
///
/// Both front ends need the annotation on the theory they keep: the batch
/// close (mirroring the breaker pass of HS `closeTheoryWithMaude`) and its
/// `--partial-evaluation` re-close (`applyPartialEvaluation`'s second
/// `closeTheoryWithMaude`, Prover.hs:240), and the web load path, whose
/// rule/source/message renderers print HS's `// loop breaker: [<idx>]`
/// comments.  Sharing one traversal keeps the two from drifting in which
/// rules they hand the pass, and in what order.
pub fn annotate_theory_loop_breakers(
    theory: &mut crate::theory::Theory,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) {
    use crate::theory::TheoryItem;
    let mut rules: Vec<&mut OpenProtoRule> = theory
        .items
        .iter_mut()
        .filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .collect();
    annotate_loop_breakers(&mut rules, maude);
}

#[cfg(test)]
mod tests {
    use super::{IntrRuleCache, ProofContext, SaturateState, SaturationRun};
    use crate::rule::IntrRuleAC;
    use tamarin_test_support::require_maude_path;

    /// A small Maude-free rule list: the special intruder rules
    /// (`coerce`, `pub`, `fresh`, `isend`, `irecv`).
    fn sample_rules() -> Vec<IntrRuleAC> {
        let rules = crate::intruder_rules::special_intruder_rules(false);
        assert!(rules.len() > 1, "sample needs several rules to compare");
        rules
    }

    /// Cloning a handle must hand out the SAME rule list, not a copy —
    /// this is what makes the per-probe / per-deduction / per-lemma
    /// contexts inexpensive.  A field that becomes an owned `Vec` breaks the
    /// pointer identity.  A `Clone` that copies deeply breaks it too.  A
    /// `Deref` that exposes anything but the complete list breaks the length.
    #[test]
    fn intr_rule_cache_clone_shares_one_allocation() {
        let rules = sample_rules();
        let n = rules.len();
        let cache = IntrRuleCache::from(rules);
        let shared = cache.clone();
        assert_eq!(cache.as_ptr(), shared.as_ptr());
        assert_eq!(cache.len(), n);
        assert_eq!(shared.len(), n);
    }

    #[test]
    fn worker_snapshot_shares_sources() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let ctx = ProofContext::new(
            tamarin_term::maude_proc::MaudeHandle::start(
                &path,
                tamarin_term::maude_sig::pair_maude_sig(),
            )
            .unwrap(),
            Vec::new(),
        );
        ctx.mark_saturated_done();
        let worker = ctx.with_swapped_maude(ctx.maude.clone());
        assert!(std::sync::Arc::ptr_eq(
            &ctx.full_sources,
            &worker.full_sources
        ));
        assert_eq!(
            *worker.saturate_gate.state.lock().unwrap(),
            SaturateState::Done(Ok(()))
        );
    }

    #[test]
    fn ordinary_worker_waits_for_saturation_and_inherits_its_error() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let ctx = ProofContext::new(
            tamarin_term::maude_proc::MaudeHandle::start(
                &path,
                tamarin_term::maude_sig::pair_maude_sig(),
            )
            .unwrap(),
            Vec::new(),
        );
        *ctx.saturate_gate.state.lock().unwrap() =
            SaturateState::InProgress(std::thread::current().id());

        std::thread::scope(|scope| {
            let (started_tx, started_rx) = std::sync::mpsc::channel();
            let (done_tx, done_rx) = std::sync::mpsc::channel();
            let ctx_ref = &ctx;
            scope.spawn(move || {
                started_tx.send(()).unwrap();
                let worker = ctx_ref.with_swapped_maude(ctx_ref.maude.clone());
                done_tx
                    .send(worker.saturate_gate.state.lock().unwrap().clone())
                    .unwrap();
            });
            started_rx.recv().unwrap();
            assert!(matches!(
                done_rx.recv_timeout(std::time::Duration::from_millis(25)),
                Err(std::sync::mpsc::RecvTimeoutError::Timeout)
            ));

            *ctx.saturate_gate.state.lock().unwrap() = SaturateState::Done(Err(
                crate::prove::ProveError::Guarded("conversion failed".into()),
            ));
            ctx.saturate_gate.ready.notify_all();
            assert_eq!(
                done_rx.recv().unwrap(),
                SaturateState::Done(Err(crate::prove::ProveError::Guarded(
                    "conversion failed".into()
                )))
            );
        });
    }

    #[test]
    fn fresh_session_layout_resets_saturation_result() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let ctx = ProofContext::new(
            tamarin_term::maude_proc::MaudeHandle::start(
                &path,
                tamarin_term::maude_sig::pair_maude_sig(),
            )
            .unwrap(),
            Vec::new(),
        );
        *ctx.saturate_gate.state.lock().unwrap() =
            SaturateState::Done(Err(crate::prove::ProveError::Guarded("old".into())));

        let fresh = ctx.fresh_with_sources(std::sync::Arc::clone(&ctx.full_sources));
        assert_eq!(
            *fresh.saturate_gate.state.lock().unwrap(),
            SaturateState::Pending
        );
    }

    #[test]
    fn aborted_saturation_is_retryable_and_counter_neutral() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let ctx = ProofContext::new(
            tamarin_term::maude_proc::MaudeHandle::start(
                &path,
                tamarin_term::maude_sig::pair_maude_sig(),
            )
            .unwrap(),
            Vec::new(),
        );
        let before = ctx.maude.fresh_counter_peek();
        *ctx.saturate_gate.state.lock().unwrap() =
            SaturateState::InProgress(std::thread::current().id());
        {
            let _run = SaturationRun::new(&ctx, before);
            ctx.maude.ensure_above(before.saturating_add(50));
        }

        assert_eq!(ctx.maude.fresh_counter_peek(), before);
        assert_eq!(
            *ctx.saturate_gate.state.lock().unwrap(),
            SaturateState::Pending
        );
    }
}
