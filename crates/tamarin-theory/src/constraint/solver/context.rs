// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

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

use super::sources::Source;
use crate::prove::ProveError;
use std::sync::{Arc, OnceLock};
use tamarin_term::maude_proc::{MaudeHandle, MaudePool, OwnedPooledMaude};
use tamarin_utils::cancellation;

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

/// A rule instance with its variant disjunction (`Maybe RuleACConstrs`);
/// intruder rules carry none.
pub(crate) type RuleWithConstrs = (
    crate::rule::RuleACInst,
    Option<Vec<tamarin_term::subst_vfresh::LNSubstVFresh>>,
);

/// HS `ClassifiedRules` (System.hs), partitioned once per context.
#[derive(Debug)]
pub(crate) struct ClassifiedRules {
    /// `crProtocol`: the intruder rules that neither construct nor destruct,
    /// then the protocol rules (`rulesAC = intruder ++ proto`).
    pub(crate) protocol: Vec<RuleWithConstrs>,
    /// `crDestruct`: destructor rules and `IEquality`.
    pub(crate) destruct: Vec<RuleWithConstrs>,
    /// `crConstruct`: constructor rules and `Coerce`.
    pub(crate) construct: Vec<RuleWithConstrs>,
}

impl ClassifiedRules {
    fn new(rules: &[OpenProtoRule], intruder_rules: &[IntrRuleAC]) -> Self {
        use crate::constraint::solver::reduction::{
            canonical_rule_inst, intr_rule_to_rule_ac_inst,
        };
        use crate::rule::{is_constr_rule, is_destr_rule};
        let intr = |keep: fn(&crate::rule::IntrRuleACInfo) -> bool| {
            intruder_rules
                .iter()
                .filter(|ir| keep(&ir.info))
                .map(|ir| (intr_rule_to_rule_ac_inst(ir.clone()), None))
                .collect::<Vec<RuleWithConstrs>>()
        };
        let mut protocol = intr(|info| !is_constr_rule(info) && !is_destr_rule(info));
        protocol.extend(rules.iter().map(|o| {
            // HS `someRuleACInst`: `Just` the disjunction, even an empty one.
            let constrs = match &o.variants {
                crate::theory::RuleVariants::Closed { variants, .. } => Some(variants.clone()),
                _ => None,
            };
            (canonical_rule_inst(o), constrs)
        }));
        ClassifiedRules {
            protocol,
            destruct: intr(is_destr_rule),
            construct: intr(is_constr_rule),
        }
    }

    /// HS `nonSilentRules = filter (not . null . get rActs) . joinAllRules`.
    pub(crate) fn non_silent(&self) -> impl Iterator<Item = &RuleWithConstrs> {
        self.protocol
            .iter()
            .chain(&self.destruct)
            .chain(&self.construct)
            .filter(|(rule, _)| !rule.actions.is_empty())
    }
}

/// Read-only, immutable-after-build bundle of a `ProofContext`.
///
/// These fields are computed once at theory-load time and shared unchanged by
/// every lemma and proof-search worker. Mutable source materialisation lives
/// directly on [`ProofContext`], outside this bundle.
#[derive(Debug)]
pub struct ProofContextShared {
    #[cfg(test)]
    pub(crate) worker_gate:
        std::sync::Mutex<Option<std::sync::Arc<super::cancellation_tests::WorkerGate>>>,
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
    /// `rules` and `intruder_rules` partitioned as HS `ClassifiedRules`.
    pub(crate) classified_rules: ClassifiedRules,
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
    pub injective_fact_insts: crate::tools::injective_fact_instances::InjectiveFactInsts,
    /// `pcTrueSubterm` — True iff every destructor rule has its
    /// RHS as a proper subterm of its LHS (`all isSubtermRule $
    /// filter isDestrRule $ intruder_rules`).  Mirrors Haskell's
    /// `_pcTrueSubterm` (System.hs) and gates the
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
#[derive(Debug, Clone)]
pub struct ProofContext {
    pub maude: MaudeHandle,
    /// Optional pool of additional Maude subprocesses. Parallel work leases
    /// one per task instead of serialising on `maude`'s IPC mutex, and falls
    /// back to `maude` when none is free. `None` means only `maude` exists
    /// and every task shares it.
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
    pub is_exists_trace: bool,
    /// The solved-leaf extraction strategy for this lemma's auto-prover,
    /// mirroring HS `apCut` (Theory/Proof.hs) threaded from
    /// `--stop-on-trace` (TheoryLoader.hs).  `Dfs` is the default
    /// (`fromMaybe CutDFS`); consumed once per lemma by `run_proof_search`
    /// (search.rs).  Per-lemma / theory-global, so owned.
    pub cut: CutStrategy,
    /// Assumptions used when a standalone context builds refined sources.
    /// Session proofs obtain their theory-wide refinement from the source provider.
    pub typing_assumptions: Vec<std::sync::Arc<crate::guarded::Guarded>>,
    /// The goal ranking list for this lemma, mirroring HS's
    /// `Heuristic ProofContext = Heuristic [GoalRanking ProofContext]`
    /// (System.hs).  `None` ⇒ HS's `defaultHeuristic False`
    /// (`defaultRankings False = [SmartRanking False]`, System.hs).
    /// Resolved per-lemma in `prove_lemma`
    /// (per-lemma `[heuristic=..]` overrides the theory-level directive,
    /// matching `apDefaultHeuristic <|> pcHeuristic`).
    /// Round-robin scheduling: depth d → `rankings[d % n]`
    /// (ProofMethod.hs).  Per-lemma, so owned.
    pub heuristic: Option<Vec<crate::constraint::solver::goals::GoalRanking>>,
    /// The name of the lemma being proved.  Passed as `argv[1]` to
    /// the oracle script (HS `L.get pcLemmaName ctxt`, ProofMethod.hs).
    /// Per-lemma, so owned.
    pub lemma_name: String,
    /// Path to the theory file being proved.  Used to resolve the
    /// oracle script path as `takeDirectory theory_file </> oracle_rel_path`
    /// (HS Theory/Text/Parser.hs, System.hs).  Stored as the absolute
    /// path passed to `--prove`.  Per-lemma, so owned.
    pub theory_file: String,
    /// Ordered source patterns, or source cases for a materialized context.
    pub(crate) full_sources: SharedSources,
    sources: ContextSources,
    /// Read-only theory data (`intruder_rules`, `restrictions`, …), shared
    /// behind an `Arc`. Field reads are
    /// transparent through the [`std::ops::Deref`] implementation below.
    pub shared: std::sync::Arc<ProofContextShared>,
}

/// Theory-wide inputs used to build a proof context.
#[derive(Default)]
pub struct ProofContextOptions {
    pub maude_pool: Option<std::sync::Arc<MaudePool>>,
    /// Expand the original E rules for injectivity analysis, even when the
    /// executable rules have been unfolded or annotated by auto-sources.
    pub macros: Vec<tamarin_term::macro_expand::LNMacro>,
    pub restrictions: Vec<crate::guarded::Guarded>,
    pub forced_injective_facts: std::collections::BTreeSet<crate::fact::FactTag>,
    pub intruder_rules: Option<IntrRuleCache>,
    pub parameters: crate::constraint::solver::sources::IntegerParameters,
    pub sys_retention: crate::constraint::solver::search::SysRetention,
    pub show_saturation_steps: bool,
    /// The caller already annotated loop breakers while closing the theory.
    /// Standalone contexts leave this false; their unprepared rules get
    /// their variants here.
    pub loop_breakers_prepared: bool,
}

pub(crate) type SharedSources = Arc<Vec<Source>>;

#[derive(Debug, Default)]
pub(crate) struct SourceSlot {
    pub(crate) ready: tamarin_utils::parallel::SharedOnce<SharedSources>,
}

impl SourceSlot {
    pub(crate) fn get_or_build<F>(
        self: &Arc<Self>,
        prepare: impl FnOnce() -> F,
    ) -> Result<SharedSources, ProveError>
    where
        F: FnOnce() -> Result<SharedSources, ProveError> + Send + 'static,
    {
        cancellation::check()?;
        if let Some(ready) = self.ready.get() {
            return Ok(ready.clone());
        }
        let build = prepare();
        // Claim the slot on a worker that can build it. Claiming before
        // admission could leave every worker waiting for the queued owner.
        let slot = self.clone();
        tamarin_utils::parallel::in_pool(move || slot.ready.get_or_try_init(build).cloned())
    }
}

#[derive(Debug)]
enum ContextSources {
    /// Standalone callers may set their own typing assumptions before forcing.
    Local(OnceLock<Arc<SourceSlot>>),
    Session(Arc<dyn SourceProvider>),
    /// Saturation reads its private working set directly.
    Materialized,
}

impl Clone for ContextSources {
    fn clone(&self) -> Self {
        match self {
            // A standalone copy can select its own assumptions until a
            // successful computation fixes its view. Session copies always
            // use their theory's selected raw or refined slot.
            Self::Local(slot) if slot.get().is_some_and(|s| s.ready.get().is_some()) => {
                Self::Local(slot.clone())
            }
            Self::Local(_) => Self::Local(OnceLock::new()),
            Self::Session(provider) => Self::Session(provider.clone()),
            Self::Materialized => Self::Materialized,
        }
    }
}

pub(crate) trait SourceProvider: std::fmt::Debug + Send + Sync {
    fn may_fail(&self) -> bool {
        true
    }

    fn materialize(&self, maude: &MaudeHandle) -> Result<SharedSources, ProveError>;
}

#[cfg(test)]
#[derive(Debug)]
pub(crate) struct FailingSourceProvider;

#[cfg(test)]
impl SourceProvider for FailingSourceProvider {
    fn materialize(&self, _: &MaudeHandle) -> Result<SharedSources, ProveError> {
        Err(ProveError::Guarded("bad source".into()))
    }
}

/// Transparent read access to immutable theory data.
impl std::ops::Deref for ProofContext {
    type Target = ProofContextShared;
    fn deref(&self) -> &ProofContextShared {
        &self.shared
    }
}

impl ProofContextShared {
    /// Membership in HS `S.map fst $ L.get pcInjectiveFactInsts ctxt`
    /// (Contradictions.hs, Simplify.hs).
    pub fn is_injective_tag(&self, tag: &crate::fact::FactTag) -> bool {
        self.injective_fact_insts.iter().any(|(t, _)| t == tag)
    }
}

/// Failure to select a materialised source case. Keep the two bounds errors
/// distinct: callers such as the web routes report the failed lookup.
#[derive(Debug)]
pub enum SourceCaseError {
    SourceIndex,
    CaseIndex,
    Proof(crate::prove::ProveError),
}

impl ProofContext {
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
        Ok(self
            .ensure_saturated()?
            .iter()
            .map(|source| (source.goal.clone(), source.cases_or_empty()))
            .collect())
    }

    /// Return one materialised source-case system by zero-based indices.
    pub fn source_case_system_at(
        &self,
        source: usize,
        case: usize,
    ) -> Result<crate::constraint::system::System, SourceCaseError> {
        self.ensure_saturated()
            .map_err(SourceCaseError::Proof)?
            .get(source)
            .ok_or(SourceCaseError::SourceIndex)?
            .case_system_at(case)
            .ok_or(SourceCaseError::CaseIndex)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseInduction {
    UseInduction,
    AvoidInduction,
}

/// How the auto-prover cuts the proof tree around solved leaves,
/// mirroring HS `SolutionExtractor` (Theory/Proof.hs) as selected
/// by `runAutoProver` (Theory/Proof.hs).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum CutStrategy {
    /// HS `CutDFS` → `cutOnSolvedDFS` (Theory/Proof.hs): parallel
    /// iterative-deepening DFS, doubling `dMax` from 4.  Selects the leftmost
    /// (preorder, CaseName order) solved leaf among those shallower than the
    /// first `dMax` (4, 8, 16, …) to admit any solved leaf — within that
    /// depth bucket a deeper-but-leftmost leaf beats a shallower one further
    /// right, so this is NOT globally-shallowest.  The default when
    /// `--stop-on-trace` is absent
    /// (HS `constructAutoProver`: `fromMaybe CutDFS`, TheoryLoader.hs).
    #[default]
    Dfs,
    /// HS `CutSingleThreadDFS` → `cutOnSolvedSingleThreadDFS`
    /// (Theory/Proof.hs): single-thread depth-first with NO depth
    /// bound and NO iterative deepening.  `findSolved`'s `foldMap` over the
    /// children map descends the leftmost branch (CaseName order) to
    /// completion before its siblings and stops at the first solved leaf, so
    /// a deep solved leaf under the leftmost branch wins over a shallower one
    /// further right even when the shallower leaf sits inside `Dfs`'s first
    /// depth bucket (where `Dfs` would cut the deep branch off and pick it).
    SeqDfs,
    /// HS `CutBFS` → `cutOnSolvedBFS` (Theory/Proof.hs): iterative
    /// level-deepening over the DFS proof tree.  At each level `l` the tree
    /// is forced to depth `l` and walked in CaseName order with threaded
    /// state: a Solved leaf at exactly depth `l` flips TraceFound; a node
    /// still pending at depth `l` is cut to `sorry /* bound reached */`
    /// (`sorry /* ignored (attack exists) */` once TraceFound).  On
    /// TraceFound the CUT tree is the result — those sorry leaves are part
    /// of the printed proof; a level that completes with nothing pending
    /// returns the full tree unchanged.
    Bfs,
    /// HS `CutNothing` → `id` (Theory/Proof.hs): no cut at all — the
    /// full proof tree is built and printed; sibling exploration does not
    /// stop when a trace is found.
    Nothing,
    /// HS `CutAfterSorry` → `cutAfterFirstSorry` (Theory/Proof.hs):
    /// preorder walk in CaseName order; the first `Sorry` or Solved leaf
    /// aborts, and every node visited after the abort becomes a bare
    /// `sorry` leaf (children dropped, system annotation kept).  Under the
    /// unbounded default prover the only aborter is a Solved leaf, so this
    /// reads as "stop at the first trace, sorry out the remainder".
    AfterSorry,
}

impl ProofContext {
    /// Build a standalone context without theory macros. Use `with_options`
    /// to supply the macro environment when rules retain unexpanded E halves.
    pub fn new(maude: MaudeHandle, rules: Vec<OpenProtoRule>) -> Self {
        Self::with_options(maude, rules, ProofContextOptions::default())
    }

    /// Number of protocol-class rules, including non-constructor/non-destructor
    /// intruder rules, after compiled-member deduplication.
    pub fn protocol_rule_count(&self) -> usize {
        self.classified_rules.protocol.len()
    }

    /// Whether a search with a deadline visits its cases in order: a witness
    /// search, or one whose ranking or source provider can fail. A later
    /// case of such a search could end or fail it after the deadline has cut
    /// the cases before it.
    pub(crate) fn serial_under_a_deadline(&self) -> bool {
        self.is_exists_trace
            || matches!(&self.sources, ContextSources::Session(provider) if provider.may_fail())
            || self
                .heuristic
                .as_deref()
                .is_some_and(super::goals::rankings_may_fail)
    }

    /// Use the assigned Maude process for this task and its nested reductions.
    pub fn with_swapped_maude(&self, maude: MaudeHandle) -> Self {
        let mut worker = self.clone();
        worker.maude = maude;
        worker.maude_pool = None;
        worker
    }

    pub(crate) fn for_dfs_case(&self, lease: Option<&OwnedPooledMaude>) -> Self {
        let mut worker = self.clone();
        if let Some(lease) = lease {
            worker.maude = lease.handle().clone();
        }
        worker
    }

    /// Resolve the ordered source set on first case access. Builders have a
    /// private iteration view so their recursive reads never enter the cache.
    pub(crate) fn ensure_saturated(&self) -> Result<SharedSources, ProveError> {
        match &self.sources {
            ContextSources::Session(provider) => provider.materialize(&self.maude),
            ContextSources::Materialized => Ok(self.full_sources.clone()),
            ContextSources::Local(local) => {
                let slot = local.get_or_init(Arc::default);
                slot.get_or_build(|| {
                    let ctx = self.clone();
                    move || ctx.build_sources()
                })
            }
        }
    }

    pub(crate) fn build_sources(self) -> Result<SharedSources, ProveError> {
        self.build_source_sets().map(|(_, refined)| refined)
    }

    /// Build raw and refined sources in one fresh-variable scope. Auto-source
    /// generation reads the raw half while its trigger reads the refined half.
    pub(crate) fn build_source_sets(
        mut self,
    ) -> Result<(SharedSources, SharedSources), ProveError> {
        let raw = self.build_raw_sources()?;
        let refined =
            super::sources::refine_with_source_asms(raw.to_vec(), &self.typing_assumptions, &self)?;
        Ok((raw, Arc::new(refined)))
    }

    /// Saturate the raw sources (HS `precomputeSources`).
    pub(crate) fn build_raw_sources(&mut self) -> Result<SharedSources, ProveError> {
        self.sources = ContextSources::Materialized;
        self.full_sources = Arc::new(
            self.full_sources
                .iter()
                .map(|s| Source::lazy(s.goal.clone()))
                .collect(),
        );
        for src in self.full_sources.iter() {
            src.set_cases(super::sources::initial_source_cases(&src.goal, self)?);
        }
        let saturated = super::sources::saturate_sources_with_simp(
            self.full_sources.to_vec(),
            self.parameters.saturation_limit(),
            self,
        )?;
        let raw = Arc::new(saturated);
        Self::dump_sources(&raw);
        Ok(raw)
    }

    pub(crate) fn use_materialized_sources(&mut self, sources: SharedSources) {
        self.full_sources = sources;
        self.sources = ContextSources::Materialized;
    }

    pub(crate) fn set_source_provider(&mut self, provider: std::sync::Arc<dyn SourceProvider>) {
        self.sources = ContextSources::Session(provider);
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
    ) -> Result<Vec<IntrRuleAC>, tamarin_term::maude_proc::MaudeError> {
        let mut intruder_rules = crate::intruder_rules::subterm_constructor_rules(maude, sig)?;
        intruder_rules.extend(crate::intruder_rules::special_intruder_rules());
        // Union construction and decomposition supply multiset KU sources
        // and KD chain extensions (`multisetIntruderRules`, IntruderRules.hs).
        if sig.enable_mset {
            intruder_rules.extend(crate::intruder_rules::multiset_intruder_rules());
        }
        // `xorIntruderRules` (IntruderRules.hs) supplies two cancellation
        // destructors, the XOR constructor and the zero constructor.
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
            maude,
            &sig.ac_user_fun_syms(),
        )?);
        intruder_rules.extend(crate::intruder_rules::destruction_rules_no_eq(
            maude,
            &sig.no_eq_fun_syms(),
        )?);
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
        // HS's `mkDhIntruderVariants` (TheoryLoader.hs)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`
        // (Template-Haskell `embedFile`), not the runtime
        // `dhIntruderRules` generator.  HS's `Main.Mode.Intruder.run`
        // is what PRODUCES that cache file in the first place
        // (Main/Mode/Intruder.hs), but the production theory-load
        // path always reads the cache.
        //
        // The cached-file parser (`mk_dh_intruder_variants` /
        // `mk_bp_intruder_variants` from `crate::intruder_variants`)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`,
        // matching HS's `mkDhIntruderVariants` (TheoryLoader.hs)
        // and making us mechanism-identical to HS.  The runtime
        // generator (`dh_intruder_rules`) is retained as the regenerator
        // (callable when one wants to refresh the cache from local
        // Maude); the `variants` row of the prover's cli_refs table flags any
        // divergence.
        //
        // Ordering matches HS exactly: DH BEFORE BP, both AFTER
        // subterm + special rules.  When BP is enabled HS adds DH
        // FIRST (the list `[mkDhIntruderVariants, mkBpIntruderVariants]`
        // — TheoryLoader.hs).
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
        Ok(assembled)
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
    fn dump_sources(sources: &[Source]) {
        if !tamarin_utils::env_gate!("TAM_RS_DBG_SOURCES_DUMP") {
            return;
        }
        use crate::constraint::constraints::Goal;
        for (i, src) in sources.iter().enumerate() {
            let goal = match &src.goal {
                Goal::Action(_, fa) => format!("Action {}", crate::pretty_system::pretty_fact(fa)),
                Goal::Premise(_, fa) => {
                    format!("Premise {}", crate::pretty_system::pretty_fact(fa))
                }
                _ => "other".to_string(),
            };
            let names: Vec<String> = src
                .cases()
                .map(|cases| cases.iter().map(|(ns, _)| ns.join("_")).collect())
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
    /// which `checkCloseIntrRule` (TheoryLoader.hs) runs on the
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
            macros,
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
                Self::assemble_intruder_rules(&sig, &maude, &[])?,
            )),
        };
        Self::dump_intruder_rules(&intruder_rules);
        // HS closeRuleCache analyzes macro-expanded cprRuleE, including
        // after auto-sources has replaced executable bodies by AC members.
        let injective_fact_insts =
            crate::tools::injective_fact_instances::injective_fact_instances_for_rules(
                &rules,
                &macros,
                &sig.reducible_fun_syms_fast,
                &forced_injective_facts,
            );
        // Explicit AC families are executable rules, not display-only metadata.
        // Keep injectivity based on the original expanded E rules, but build
        // all solver indices and loop breakers from the supplied members.
        let has_explicit_variants = rules.iter().any(|rule| !rule.rule_ac.is_empty());
        if has_explicit_variants {
            rules = rules
                .into_iter()
                .flat_map(|mut rule| {
                    rule.expand_variant_macros(&macros);
                    if rule.rule_ac.is_empty() {
                        vec![rule]
                    } else {
                        crate::theory::closed_rules_ac(&rule)
                            .iter()
                            .map(|ac| crate::tools::rule_variants::closed_rule_as_open(&rule, ac))
                            .collect()
                    }
                })
                .collect();
        }
        if !loop_breakers_prepared || has_explicit_variants {
            annotate_loop_breakers(&mut rules.iter_mut().collect::<Vec<_>>(), &maude)?;
        }
        for rule in &mut rules {
            crate::tools::rule_variants::prepare_open_rule_variant(rule, &maude)?;
        }
        // Identical closed members must not create duplicate source cases.
        let rules = tamarin_utils::prelude_ext::nub(rules);
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
                *counts.entry((action.tag, action.arity())).or_insert(0usize) += 1;
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
            sources: ContextSources::Local(OnceLock::new()),
            shared: std::sync::Arc::new(ProofContextShared {
                #[cfg(test)]
                worker_gate: std::sync::Mutex::new(None),
                classified_rules: ClassifiedRules::new(&rules, &intruder_rules),
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
        ctx.full_sources = Arc::new(super::sources::source_patterns(&ctx));
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
/// variants just to copy that one field back.
pub(crate) fn annotate_loop_breakers(
    rules: &mut [&mut OpenProtoRule],
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<(), tamarin_term::maude_proc::MaudeError> {
    use crate::rule::PremIdx;

    // HS keys the relation nodes by the WHOLE closed theory item under its
    // derived `Ord` (`useAutoLoopBreakersAC`'s carrier `a`, matched back to
    // rules with full `ru == ru'` equality, LoopBreakers.hs) — NOT by
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
        a.rule == b.rule && a.variants == b.variants
    };
    let mut keys: Vec<usize> = Vec::with_capacity(rules.len());
    for i in 0..rules.len() {
        let k = (0..i).find(|&j| same_item(rules[j], rules[i])).unwrap_or(i);
        keys.push(k);
    }

    // `premSolvingRelAC` (LoopBreakers.hs) unifies AC-variant instances of
    // facts. The cached abstracted bodies and variant substitutions include
    // reducible-term normalization, including flattened DH exponents. An empty
    // variant list yields the bare fact.
    let variants: Vec<&crate::theory::RuleVariants> = rules.iter().map(|o| &o.variants).collect();

    // `instances ru fa`: apply each variant subst (as a free subst via
    // `freshToFreeAvoiding`) to `fa`.  Empty variant list ⇒ `[fa]`.
    let instances = |rule_idx: usize, fa: &crate::fact::LNFact| -> Vec<crate::fact::LNFact> {
        use tamarin_term::lterm::HasFrees;
        let substs = match variants[rule_idx] {
            crate::theory::RuleVariants::Closed { variants, .. } => variants.as_slice(),
            _ => return vec![fa.clone()],
        };
        if !substs.is_empty() && substs.iter().all(|s| s.is_empty()) {
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
                let free = s.fresh_to_free_avoiding(|_| {
                    let i = next;
                    next += 1;
                    i
                });
                // freshToFree rename + apply — frees change; recompute the bloom.
                let terms: Vec<tamarin_term::lterm::LNTerm> = fa
                    .terms()
                    .iter()
                    .map(|t| tamarin_term::subst::apply_vterm(&free, t.clone()))
                    .collect();
                crate::fact::LNFact::fresh_annotated(fa.tag, fa.annotations.clone(), terms)
            })
            .collect()
    };

    // Build the prem-solving relation, mirroring HS's `premSolvingRelAC`
    // (`LoopBreakers.hs`) EXACTLY, including iteration nesting —
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
    // the fresh z-vars the variant substs are keyed on).
    let ac_rules: Vec<&crate::rule::ProtoRuleE> = rules.iter().map(|o| o.ac_body()).collect();
    // Memoize variant instances only after a compatible fact tag is found.
    // Upstream #978 rejects incompatible tags before instantiation; retaining
    // the memoized lists also avoids repeating substitutions for later edges.
    let prem_insts_by_rule: Vec<Vec<std::cell::OnceCell<Vec<crate::fact::LNFact>>>> = ac_rules
        .iter()
        .map(|ru| {
            ru.premises
                .iter()
                .map(|_| std::cell::OnceCell::new())
                .collect()
        })
        .collect();
    let conc_insts_by_rule: Vec<Vec<std::cell::OnceCell<Vec<crate::fact::LNFact>>>> = ac_rules
        .iter()
        .map(|ru| {
            ru.conclusions
                .iter()
                .map(|_| std::cell::OnceCell::new())
                .collect()
        })
        .collect();

    let mut relation: Vec<((usize, PremIdx), (usize, PremIdx))> = Vec::new();
    for (i_from, _ru_from) in rules.iter().enumerate() {
        let ru_from_ac = ac_rules[i_from];
        for (i_to, _ru_to) in rules.iter().enumerate() {
            let ru_to_ac = ac_rules[i_to];
            for (to_prem_idx, prem_fa) in ru_to_ac.enumerate_premises() {
                // HS `dataflowRelAC` (LoopBreakers.hs) enumerates ALL
                // premises (`enumPrems`, Theory/Model/Rule.hs) with no tag filter;
                // the only premise-level guard is `not (isNoSourcesFact …)`.
                // Non-Proto premises are kept here too: the tag-equality
                // (`c0.tag != prem_fa.tag`) + `unifiable_ln_facts` gates below
                // already exclude any conclusion that cannot form an edge,
                // exactly as HS's `unifiableLNFacts` does (it returns []
                // whenever `factTag fa1 /= factTag fa2`,
                // Theory/Model/Fact.hs).
                //
                // Haskell `LoopBreakers.hs`:
                //   `guard $ not (isNoSourcesFact premFa0)`
                if prem_fa.is_no_sources() {
                    continue;
                }
                // Haskell `LoopBreakers.hs`: edge exists iff some
                // conclusion of `ruFrom` is AC-UNIFIABLE with this premise
                // (not merely same-tag).  Tag-only matching over-approximates
                // and adds spurious self-edges (e.g. `I_m0`'s `St_I(<'m2'>)`
                // conclusion vs its own `St_I('m0')` premise share a tag but
                // do NOT unify), which fabricate extra cycles and over-mark
                // loop breakers.  Use real Maude unifiability, mirroring HS.
                //
                // HS `dataflowRelAC` (LoopBreakers.hs):
                //   guard $ or $ do
                //     concFa0 <- snd <$> eConcs ruFrom
                //     guard (factTag concFa0 == factTag premFa0)
                //     premFa <- instances ruTo premFa0
                //     concFa <- instances ruFrom concFa0
                //     let concFaFresh = rename concFa `evalFresh` avoid premFa
                //     return $ unifiableLNFacts concFaFresh premFa
                // i.e. iterate the VARIANT INSTANCES of both the premise and
                // each conclusion, rename the conclusion away from the
                // premise's frees, and check Maude AC-unifiability.
                // HS runs the unifier purely, so a failed backend aborts
                // the pass instead of dropping the edge.
                let mut conc_unifies = false;
                'concs: for (ci, c0) in ru_from_ac.conclusions.iter().enumerate() {
                    if c0.tag != prem_fa.tag {
                        continue;
                    }
                    let prem_insts = prem_insts_by_rule[i_to][to_prem_idx.0]
                        .get_or_init(|| instances(i_to, prem_fa));
                    let conc_insts =
                        conc_insts_by_rule[i_from][ci].get_or_init(|| instances(i_from, c0));
                    for conc in conc_insts {
                        for prem in prem_insts {
                            let mut fresh = tamarin_term::lterm::avoid(prem);
                            let conc_fresh = tamarin_term::lterm::rename(conc.clone(), &mut fresh);
                            if crate::rule::unifiable_ln_facts(maude, &conc_fresh, prem)? {
                                conc_unifies = true;
                                break 'concs;
                            }
                        }
                    }
                }
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
    Ok(())
}

/// Run [`annotate_loop_breakers`] over a theory's rules, in place and in
/// source order.
///
/// Both front ends need the annotation on the theory they keep: the batch
/// close (mirroring the breaker pass of HS `closeTheoryWithMaude`) and its
/// `--partial-evaluation` re-close (`applyPartialEvaluation`'s second
/// `closeTheoryWithMaude`, Prover.hs), and the web load path, whose
/// rule/source/message renderers print HS's `// loop breaker: [<idx>]`
/// comments.  Sharing one traversal keeps the two from drifting in which
/// rules they hand the pass, and in what order.
pub fn annotate_theory_loop_breakers(
    theory: &mut crate::theory::Theory,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Result<(), tamarin_term::maude_proc::MaudeError> {
    use crate::theory::TheoryItem;
    let mut rules: Vec<&mut OpenProtoRule> = theory
        .items
        .iter_mut()
        .filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .collect();
    annotate_loop_breakers(&mut rules, maude)
}

#[cfg(test)]
mod tests {
    use super::{Arc, IntrRuleCache, ProveError, SourceSlot};
    use crate::rule::IntrRuleAC;

    /// A small Maude-free rule list: the special intruder rules
    /// (`coerce`, `pub`, `fresh`, `isend`, `irecv`).
    fn sample_rules() -> Vec<IntrRuleAC> {
        let rules = crate::intruder_rules::special_intruder_rules();
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
    fn source_consumers_share_the_build_and_run_its_jobs() {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap();
        let slot = Arc::new(SourceSlot::default());
        let start = std::sync::Barrier::new(2);
        let results = pool
            .install(|| {
                tamarin_utils::parallel::try_map(vec![(), ()], move |()| {
                    start.wait();
                    slot.get_or_build(|| {
                        move || {
                            let (ready, waiting) = std::sync::mpsc::channel();
                            let waiting = std::sync::Mutex::new(waiting);
                            let threads = tamarin_utils::parallel::try_map(vec![0, 1], move |i| {
                                if i == 0 {
                                    waiting
                                        .lock()
                                        .unwrap()
                                        .recv_timeout(std::time::Duration::from_secs(5))
                                        .unwrap();
                                } else {
                                    ready.send(()).unwrap();
                                }
                                Ok::<_, ProveError>(std::thread::current().id())
                            })?;
                            assert_ne!(threads[0], threads[1]);
                            Ok(Arc::new(Vec::new()))
                        }
                    })
                })
            })
            .unwrap();
        assert!(Arc::ptr_eq(&results[0], &results[1]));
    }
}
