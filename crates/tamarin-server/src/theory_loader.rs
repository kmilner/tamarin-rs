// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of HS `Main.TheoryLoader` (src/Main/TheoryLoader.hs): the theory
//! load pipeline batch mode and the web UI share, and its options record.
//!
//!   closeTheory             = translateTheory >=> removeTranslationItems
//!                             >=> checkTranslatedTheory
//!                             >=> closeTranslatedTheory >=> withVersionAndReport
//!   translateAndCheckTheory = the same minus closeTranslatedTheory
//!
//! [`load_theory`] parses; [`TheoryPipeline`] carries one theory through the
//! remaining stages. Proving (`proveTheory`) is left to the front-end: batch
//! mode proves the selected lemmas, the web UI builds its proof session
//! lazily.

use std::path::PathBuf;
use std::sync::Arc;

use tamarin_term::maude_proc::{MaudeHandle, MaudePool, SharedMaudeCaches};
use tamarin_theory::closed_theory::ClosedTheory;
use tamarin_theory::constraint::solver::context::{CutStrategy, IntrRuleCache};
use tamarin_theory::constraint::solver::sources::IntegerParameters;
use tamarin_theory::deriv_check::DerivCheckTimeout;
use tamarin_theory::module::ModuleType;
use tamarin_theory::prove::{ConfigBlock, ProveError};
use tamarin_theory::theory::Theory;
use tamarin_theory::tools::rule_variants::VariantsError;
use tamarin_theory::tools::EvaluationStyle;
use tamarin_theory::wellformedness::{WfError, WfReport};

/// HS `TheoryLoadOptions` (TheoryLoader.hs). Field order follows HS's record;
/// the last two fields are Rust-only.
#[derive(Debug, Clone)]
pub struct TheoryLoadOptions {
    /// HS `proveMode`.
    pub prove_mode: bool,
    /// HS `lemmaNames` (`--prove` ++ `--lemma`).
    pub lemma_names: Vec<String>,
    /// HS `stopOnTrace`; `None` when the flag is absent, so the theory's
    /// `configuration:` block can supply it.
    pub stop_on_trace: Option<CutStrategy>,
    /// HS folds `--heuristic`/`--oraclename` into one `Heuristic`; the port
    /// keeps both raw for `tamarin_theory::prove::CliHeuristic`.
    pub heuristic: Option<String>,
    pub oracle_name: Option<String>,
    /// HS `oracleOnly`.
    pub oracle_only: bool,
    /// HS `partialEvaluation`.
    pub partial_evaluation: Option<EvaluationStyle>,
    /// HS `defines`.
    pub defines: Vec<String>,
    /// HS `quitOnWarning`.
    pub quit_on_warning: bool,
    /// HS `autoSources` (the CLI value; OR-combined with the theory's
    /// `configuration:` block).
    pub auto_sources: bool,
    /// HS `outputModule`.
    pub output_module: Option<ModuleType>,
    /// HS `parseOnlyMode`.
    pub parse_only_mode: bool,
    /// HS `precomputeOnlyMode`.
    pub precompute_only_mode: bool,
    /// HS `derivationChecks`, default resolved (`derivDefault = 5`).
    pub derivation_checks: DerivCheckTimeout,
    /// HS `ndcCheck`.
    pub ndc_check: bool,
    /// HS `openChain` / `saturation`.
    pub parameters: IntegerParameters,
    /// HS `maudePath`.
    pub maude_path: String,
    /// Size of the auxiliary Maude pool; below 2 there is none.
    pub maude_processes: usize,
    /// `--quiet`: drop Rust-side diagnostics that have no HS counterpart.
    pub quiet: bool,
}

impl TheoryLoadOptions {
    /// HS `defaultTheoryLoadOptions` with the given Maude binary.
    pub fn new(maude_path: String) -> Self {
        Self {
            prove_mode: false,
            lemma_names: Vec::new(),
            stop_on_trace: None,
            heuristic: None,
            oracle_name: None,
            oracle_only: false,
            partial_evaluation: None,
            defines: Vec::new(),
            quit_on_warning: false,
            auto_sources: false,
            output_module: None,
            parse_only_mode: false,
            precompute_only_mode: false,
            derivation_checks: DerivCheckTimeout::DEFAULT,
            ndc_check: true,
            parameters: IntegerParameters::default(),
            maude_path,
            maude_processes: 1,
            quiet: false,
        }
    }

    /// HS `toParserFlags`: `["diff" | diffMode] ++ defines ++
    /// ["quit-on-warning" | quitOnWarning]`. The `diff` element is never
    /// present: diff mode is not ported.
    pub fn parser_flags(&self) -> Vec<&str> {
        let mut flags: Vec<&str> = self.defines.iter().map(String::as_str).collect();
        if self.quit_on_warning {
            flags.push("quit-on-warning");
        }
        flags
    }
}

/// The `-m` modules translate mode renders (HS `ModuleType` minus the export
/// backends). `None` in [`TheoryPipeline::translate_module`] selects
/// `closeTheory`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranslateModule {
    Spthy,
    SpthyTyped,
    Msr,
}

/// HS `TheoryLoadError` plus the Rust-side failures with no HS counterpart.
#[derive(Debug)]
pub enum LoadError {
    /// An exception HS lets escape to the runtime (`tamarin-prover: <msg>`).
    Exception(String),
    /// HS `UnsupportedInputError`.
    UnsupportedInput(WfReport),
    /// HS `WarningError`, raised by `--quit-on-warning`.
    Warning(WfReport),
    /// A failure HS has no counterpart for.
    Other(String),
}

impl LoadError {
    fn variants(error: VariantsError) -> Self {
        match error {
            VariantsError::UnsupportedInput(report) => Self::UnsupportedInput(report),
            other => Self::Other(other.to_string()),
        }
    }
}

impl From<ProveError> for LoadError {
    fn from(error: ProveError) -> Self {
        match error {
            ProveError::Guarded(message) => Self::Exception(message),
            ProveError::Ranking(error) => Self::Exception(error.to_string()),
            ProveError::InvalidHeuristic(message) => Self::Other(message),
            other => Self::Other(other.to_string()),
        }
    }
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Exception(message) | Self::Other(message) => f.write_str(message),
            // HS `show` of both report errors.
            Self::UnsupportedInput(report) | Self::Warning(report) => f.write_str(
                tamarin_theory::pretty_theory::render_wf_error_report(report)
                    .trim_end_matches('\n'),
            ),
        }
    }
}

impl std::error::Error for LoadError {}

/// HS `[Theory X] …` progress marker (`traceM`): stderr, never silenced.
pub fn theory_marker(theory_name: &str, msg: &str) {
    eprintln!("[Theory {theory_name}] {msg}");
}

thread_local! {
    /// Progress-marker lines the panic hook must print BEFORE a marked HS
    /// `error` block. GHC leaves ill-formed rule terms unforced past
    /// `loadTheory`, so `Term.fAppAC: empty argument list` (Raw.hs) escapes
    /// only once a later stage forces them; the port's elaboration builds
    /// those terms eagerly, so [`elaborate_loaded`] parks the markers HS
    /// prints first here for the span of that call.
    static DEFERRED_HS_ERROR_MARKERS: std::cell::Cell<Option<String>> =
        const { std::cell::Cell::new(None) };
}

/// Marker lines the panic hook must emit before its `tamarin-prover: …`
/// report, if any; consumed on read. Thread-local, so the hook only sees
/// lines parked by the panicking thread.
pub fn take_deferred_hs_error_markers() -> Option<String> {
    DEFERRED_HS_ERROR_MARKERS.take()
}

/// The parsing half of HS `loadTheory`: parse `src` with the options'
/// parser flags, resolving `#include` against `base_dir` (HS `takeDirectory
/// inFile`). HS's parser also performs what the port's elaboration checks,
/// so `Theory loaded` follows elaboration ([`TheoryPipeline::new`], or
/// [`elaborate_loaded`] for `--parse-only`): an elaboration error is an HS
/// parse error, which no marker precedes.
pub fn load_theory(
    opts: &TheoryLoadOptions,
    src: &str,
    base_dir: Option<PathBuf>,
) -> Result<tamarin_parser::Theory, tamarin_parser::ParseError> {
    tamarin_theory::elaborate::parse_theory_checked(src, &opts.parser_flags(), base_dir)
}

/// Elaborate `parsed` and print `Theory loaded`, which ends HS `loadTheory`.
///
/// `forced_after` names the markers HS prints after `Theory loaded` and
/// before the first stage that forces the rule terms: none under
/// `--parse-only` (the echo forces them), `Theory translated` in close mode
/// (the wellformedness report `rejectUnsupported` inspects), and in
/// translate mode also the NDC markers, as nothing forces the report there
/// before `checkCloseIntrRule`. An eager elaboration panic prints them.
pub fn elaborate_loaded(
    parsed: &tamarin_parser::Theory,
    in_file: &str,
    forced_after: &[&str],
) -> Result<Theory, LoadError> {
    let name = &parsed.name;
    let mut lines = format!("[Theory {name}] Theory loaded\n");
    for marker in forced_after {
        lines.push_str(&format!("[Theory {name}] {marker}\n"));
    }
    DEFERRED_HS_ERROR_MARKERS.set(Some(lines));
    let elaborated = tamarin_theory::elaborate::elaborate_with_in_file(parsed, in_file);
    DEFERRED_HS_ERROR_MARKERS.take();
    let theory = elaborated
        .map_err(|e| LoadError::Other(format!("elaboration error in {in_file}: {}", e.message)))?;
    theory_marker(name, "Theory loaded");
    Ok(theory)
}

/// A loaded theory: open until [`TheoryPipeline::check_translated_theory`]
/// closes it, which close mode always does; translate mode leaves it open.
#[derive(Debug, Clone)]
pub enum LoadedTheory {
    Open(Arc<Theory>),
    Closed(ClosedTheory),
}

impl std::ops::Deref for LoadedTheory {
    type Target = Theory;

    fn deref(&self) -> &Theory {
        match self {
            Self::Open(theory) => theory,
            Self::Closed(theory) => theory,
        }
    }
}

impl LoadedTheory {
    /// The closed theory, which every prover session is built from.
    pub fn closed(&self) -> Option<&ClosedTheory> {
        match self {
            Self::Open(_) => None,
            Self::Closed(theory) => Some(theory),
        }
    }

    fn open_mut(&mut self) -> &mut Theory {
        match self {
            Self::Open(theory) => Arc::make_mut(theory),
            Self::Closed(_) => unreachable!("a closed theory is changed only through ClosedTheory"),
        }
    }

    fn closed_mut(&mut self) -> &mut ClosedTheory {
        match self {
            Self::Open(_) => unreachable!("close mode closes the theory"),
            Self::Closed(theory) => theory,
        }
    }
}

/// One theory's state through HS's load stages.
pub struct TheoryPipeline<'a> {
    pub opts: &'a TheoryLoadOptions,
    /// `Some` runs `translateAndCheckTheory` for that module, `None` runs
    /// `closeTheory`.
    pub translate_module: Option<TranslateModule>,
    /// Shared with the prover session; the stages mutate it while the
    /// pipeline holds the only reference.
    pub theory: LoadedTheory,
    /// HS `preReport ++ postReport`.
    pub wf_report: Vec<WfError>,
    /// The open theory's signature, which every Maude process for this
    /// theory loads (HS `toSignatureWithMaude` before `closeTheory`). The NDC
    /// join never reaches it.
    pub maude_sig: tamarin_term::maude_sig::MaudeSig,
    /// HS `configAutoSources`: the CLI flag OR the configuration block.
    pub auto_sources: bool,
    /// The autoprover's cut strategy (`effective_cut`).
    pub cut: CutStrategy,
    pub maude: Option<MaudeHandle>,
    pub maude_pool: Option<Arc<MaudePool>>,
    /// The NDC-checked intruder rules (`checkCloseIntrRule`), shared by every
    /// proof context built for this theory.
    pub ndc_cache: Option<IntrRuleCache>,
    /// NDC-tagged symbols, joined into the signature by
    /// [`Self::close_translated_theory`] only: `closeTheory` adopts
    /// `checkTranslatedTheory`'s `sign'`, `translateAndCheckTheory` drops it.
    ndc_funs: Vec<tamarin_term::function_symbols::FunSym>,
}

/// HS `closeTheory`'s configuration-block read: the theory's
/// `configuration:` arguments, empty in translate mode (`translateAndCheckTheory`
/// never reads them, so a block that would kill a close run is inert there).
fn read_config_block(
    parsed: &tamarin_parser::Theory,
    translate_module: Option<TranslateModule>,
) -> Result<ConfigBlock, LoadError> {
    let config = match (translate_module, parsed.configuration.as_deref()) {
        (None, Some(block)) => tamarin_theory::prove::parse_config_block(block),
        _ => ConfigBlock::default(),
    };
    match &config.flag_error {
        Some(message) => Err(LoadError::Other(format!("configuration block: {message}"))),
        None => Ok(config),
    }
}

/// The cut strategy HS's autoprover runs with: `constructAutoProver`'s
/// `fromMaybe CutDFS` over `configStopOnTrace` (TheoryLoader.hs). The CLI
/// `--stop-on-trace` wins. Otherwise the configuration block's value is read,
/// but only in prove mode, the one place HS forces it; the web's prover is
/// built from the CLI options alone (Interactive.hs). An unreadable value is
/// reported at once, not with HS's deferred `error`.
fn effective_cut(opts: &TheoryLoadOptions, config: &ConfigBlock) -> Result<CutStrategy, LoadError> {
    match (opts.stop_on_trace, config.stop_on_trace.as_deref()) {
        (Some(cut), _) => Ok(cut),
        (None, Some(raw)) if opts.prove_mode => tamarin_theory::prove::parse_stop_on_trace(raw)
            .map_err(|e| LoadError::Other(format!("configuration block: {e}"))),
        _ => Ok(CutStrategy::Dfs),
    }
}

impl<'a> TheoryPipeline<'a> {
    /// Elaborate ([`elaborate_loaded`], which ends HS `loadTheory`), read the
    /// configuration block ([`read_config_block`]) and apply HS
    /// `addParamsOptions`.
    pub fn new(
        opts: &'a TheoryLoadOptions,
        parsed: tamarin_parser::Theory,
        in_file: &str,
        translate_module: Option<TranslateModule>,
    ) -> Result<Self, LoadError> {
        let mut forced_after = vec!["Theory translated"];
        if translate_module.is_some() && opts.ndc_check {
            forced_after.extend([
                "No Deconstruction Chain checks started",
                "No Deconstruction Chain checks ended",
            ]);
        }
        let mut theory = elaborate_loaded(&parsed, in_file, &forced_after)?;

        // HS reads the configuration block after `loadTheory`.
        let config = read_config_block(&parsed, translate_module)?;
        let cut = effective_cut(opts, &config)?;
        let auto_sources = opts.auto_sources || config.auto_sources;

        // HS `addParamsOptions`: `addNdcOption` and `addLemmaToProve`.
        theory.options.deduction_chain_check = opts.ndc_check;
        theory.options.lemmas_to_prove = opts.lemma_names.clone();
        let maude_sig = theory.signature.clone();
        Ok(Self {
            opts,
            translate_module,
            theory: LoadedTheory::Open(Arc::new(theory)),
            wf_report: Vec::new(),
            maude_sig,
            auto_sources,
            cut,
            maude: None,
            maude_pool: None,
            ndc_cache: None,
            ndc_funs: Vec::new(),
        })
    }

    /// `[Theory X] MSG` for this theory.
    pub fn marker(&self, msg: &str) {
        theory_marker(&self.theory.name, msg);
    }

    /// `[Theory X] Theory closed`, followed by `--partial-evaluation`'s
    /// `Debug.Trace` output, which the oracle forces right after it.
    pub fn closed_marker(&self, pe_trace: &str) {
        self.marker("Theory closed");
        eprint!("{pe_trace}");
    }

    /// This theory's Maude handle, or the spawn failure every close-time
    /// stage reports.
    pub fn require_maude(&self) -> Result<MaudeHandle, LoadError> {
        self.maude.clone().ok_or_else(|| {
            LoadError::Other(format!(
                "failed to start maude at {:?}",
                self.opts.maude_path
            ))
        })
    }

    fn theory_mut(&mut self) -> &mut Theory {
        self.theory.open_mut()
    }

    /// HS `translateTheory` with `processOpenTheory`'s per-module dispatch
    /// and `-m msr`'s lemma filter: the report opens with the
    /// pre-translation `Sapic.checkWellformedness ++ Acc.checkWellformedness`.
    pub fn translate_theory(&mut self) -> Result<(), LoadError> {
        let module = self.translate_module;
        self.marker("Theory translated");

        // `Acc.checkWellformedness` reads the pre-translation theory.
        let acc_wf = tamarin_accountability::check_wellformedness(&self.theory);
        // HS `addHeuristic` returns `Nothing` when a `heuristic:` item exists.
        let user_set_heuristic = !self.theory.heuristic.is_empty();
        // `processOpenTheory`: `spthy` is `pure`, `spthytyped` is
        // `Sapic.typeTheory`, `msr` and close mode run `Sapic.typeTheory >=>
        // Sapic.translate >=> Acc.translate`.
        let sapic_wf = match module {
            Some(TranslateModule::Spthy | TranslateModule::SpthyTyped) => {
                let wf = tamarin_sapic::apply::sapic_pre_report(&self.theory);
                if module == Some(TranslateModule::SpthyTyped) {
                    tamarin_sapic::type_theory::type_theory(self.theory_mut())
                        .map_err(|e| LoadError::Exception(e.message))?;
                }
                wf
            }
            None | Some(TranslateModule::Msr) => {
                // SAPIC and accountability exceptions (e.g. `duplicate rule`,
                // `CaseTestsUndefined`) escape to GHC's runtime.
                let wf = tamarin_sapic::apply::apply_sapic(self.theory_mut(), user_set_heuristic)
                    .map_err(|e| LoadError::Exception(e.message))?;
                tamarin_accountability::translate(self.theory_mut())
                    .map_err(|e| LoadError::Exception(e.to_string()))?;
                wf
            }
        };
        self.wf_report.extend(sapic_wf);
        self.wf_report.extend(acc_wf);

        // `-m msr` keeps only the selected lemmas (`filterLemma
        // (lemmaSelector thyOpts)`), before the checks below.
        if module == Some(TranslateModule::Msr) {
            let lemma_names = &self.opts.lemma_names;
            self.theory_mut().items.retain(|i| match i {
                tamarin_theory::theory::TheoryItem::Lemma(l) => lemma_matches(lemma_names, &l.name),
                _ => true,
            });
        }
        Ok(())
    }

    /// HS `checkTranslatedTheory`: start Maude (the `SignatureWithMaude`),
    /// prepare the protocol rules (variants, wellformedness, rejection of
    /// unsupported input in close mode), run the NDC check, and run the
    /// message-derivation checks on the open theory. Close mode then closes
    /// it (`closeTheoryWithMaude`'s zero-variant filter and loop breakers).
    pub fn check_translated_theory(&mut self) -> Result<(), LoadError> {
        let close_mode = self.translate_module.is_none();
        // One memo-cache set shared by the handle and every pool member.
        let caches = Arc::new(SharedMaudeCaches::default());
        self.maude = MaudeHandle::start_with_caches(
            &self.opts.maude_path,
            self.maude_sig.clone(),
            Arc::clone(&caches),
        )
        .ok();
        // HS closes the theory with Maude, so a load that cannot start it
        // fails; only translate mode carries on without one.
        if close_mode {
            self.require_maude()?;
        }
        // Parallel sites lease pool members instead of serialising on `maude`.
        self.maude_pool = if self.opts.maude_processes >= 2 {
            match MaudePool::new(
                &self.opts.maude_path,
                self.maude_sig.clone(),
                self.opts.maude_processes,
                caches,
            ) {
                Ok(pool) => Some(Arc::new(pool)),
                Err(e) => {
                    if !self.opts.quiet {
                        eprintln!(
                            "[warn] failed to spawn MaudePool({}): {} \
                                — falling back to single shared Maude",
                            self.opts.maude_processes, e
                        );
                    }
                    None
                }
            }
        } else {
            None
        };

        if let Some(maude) = self.maude.clone() {
            let pool = self.maude_pool.as_deref();
            let report = tamarin_theory::tools::rule_variants::prepare_theory_rules(
                self.theory.open_mut(),
                &maude,
                pool,
                close_mode,
            )
            .map_err(LoadError::variants)?;
            self.wf_report.extend(report);
        } else {
            let report = tamarin_theory::wellformedness::check_wellformedness(&self.theory, None)
                .map_err(LoadError::variants)?;
            self.wf_report.extend(report);
        }

        // `checkCloseIntrRule`, before the derivation checks.
        if let Some(maude) = self.maude.as_ref() {
            let checked = tamarin_theory::close_rule::check_close_intr_rule(
                maude,
                Some(self.theory.name.as_str()),
                self.theory.options.deduction_chain_check,
                &self.theory.intruder_rules,
                self.opts.parameters,
            )?;
            self.ndc_funs = checked.ndc_funs;
            self.ndc_cache = Some(checked.cache.into());
        }

        // `checkVariableDeducibility`, skipped entirely when disabled.
        let timeout = self.opts.derivation_checks;
        if timeout.is_enabled() {
            self.marker("Derivation checks started");
            if let Some(maude) = self.maude.as_ref() {
                let report = tamarin_theory::deriv_check::check_message_derivation(
                    &self.theory,
                    maude,
                    self.maude_pool.as_ref(),
                    timeout,
                    self.ndc_cache.clone(),
                    self.opts.parameters,
                )?;
                self.wf_report.extend(report);
            }
            self.marker("Derivation checks ended");
        }

        // `closeTranslatedTheory`'s `closeTheoryWithMaude`: the checks above
        // ran on the open theory, zero-variant rules included.
        if close_mode {
            let maude = self.require_maude()?;
            let placeholder = Theory::new(self.theory.name.clone(), self.maude_sig.clone());
            let LoadedTheory::Open(open) =
                std::mem::replace(&mut self.theory, LoadedTheory::Open(Arc::new(placeholder)))
            else {
                unreachable!("the theory is closed once")
            };
            let closed = tamarin_theory::closed_theory::close_prepared_theory(
                Arc::unwrap_or_clone(open),
                &maude,
            )
            .map_err(LoadError::variants)?;
            self.theory = LoadedTheory::Closed(closed);
        }
        Ok(())
    }

    /// HS `closeTranslatedTheory` minus `proveTheory`, with
    /// `withVersionAndReport`'s `--quit-on-warning` raise: HS prints `Theory
    /// closed` before the unforced close, auto-sources and proof, then raises
    /// once the report is known, so none of them run.
    ///
    /// Otherwise adopt the NDC-joined signature, apply `--auto-sources`
    /// (`closeTheoryWithMaude`) and `--partial-evaluation`
    /// (`applyPartialEvaluation`, which re-closes with auto-sources).
    /// Returns the partial evaluation's trace for [`Self::closed_marker`].
    /// The warning error takes the report, leaving `wf_report` empty.
    pub fn close_translated_theory(&mut self) -> Result<String, LoadError> {
        if self.opts.quit_on_warning && !self.wf_report.is_empty() {
            self.marker("Theory closed");
            return Err(LoadError::Warning(std::mem::take(&mut self.wf_report)));
        }

        let ndc_funs = std::mem::take(&mut self.ndc_funs);
        let theory = self.theory.closed_mut();
        for f in ndc_funs {
            theory.join_ndc_in_sig(f, tamarin_term::function_symbols::NdcState::IsNdc);
        }

        if self.auto_sources {
            self.apply_auto_sources()?;
        }

        let mut pe_trace = String::new();
        if let (Some(style), Some(maude)) = (self.opts.partial_evaluation, self.maude.clone()) {
            let in_file = self.theory.in_file.clone();
            let pool = self.maude_pool.clone();
            let theory = self.theory.closed_mut();
            // The refined rules are closed again before auto-sources.
            pe_trace = theory
                .apply_partial_evaluation(&maude, pool.as_deref(), style)
                .map_err(|e| {
                    LoadError::Other(format!("partial evaluation of {in_file} failed: {e}"))
                })?;
            if self.auto_sources {
                self.apply_auto_sources()?;
            }
        }
        Ok(pe_trace)
    }

    fn apply_auto_sources(&mut self) -> Result<(), LoadError> {
        let maude = self.require_maude()?;
        let pool = self.maude_pool.clone();
        let ndc_cache = self.ndc_cache.clone();
        let parameters = self.opts.parameters;
        let theory = self.theory.closed_mut();
        theory.apply_auto_sources(maude, pool, ndc_cache.as_ref(), parameters)?;
        Ok(())
    }
}

/// HS `lemmaSelector` (TheoryLoader.hs): `[]`, `[""]` and `["",""]` select
/// every lemma; otherwise a pattern ending in `*` matches by prefix and any
/// other pattern (a bare `""` included) by exact name.
pub fn lemma_matches(filter: &[String], lemma_name: &str) -> bool {
    match filter.len() {
        0 => return true,
        1 if filter[0].is_empty() => return true,
        2 if filter[0].is_empty() && filter[1].is_empty() => return true,
        _ => {}
    }
    filter.iter().any(|pat| match pat.strip_suffix('*') {
        Some(prefix) => lemma_name.starts_with(prefix),
        None => pat == lemma_name,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `configStopOnTrace` precedence: the CLI value wins, and the block's
    /// value is read, and so validated, only in prove mode.
    #[test]
    fn effective_cut_follows_config_stop_on_trace() {
        let block = |raw: &str| ConfigBlock {
            stop_on_trace: Some(raw.to_string()),
            ..ConfigBlock::default()
        };
        let mut opts = TheoryLoadOptions::new(String::new());
        let cut = |opts: &TheoryLoadOptions, config: &ConfigBlock| {
            effective_cut(opts, config).map_err(|e| match e {
                LoadError::Other(message) => message,
                _ => unreachable!(),
            })
        };
        assert_eq!(cut(&opts, &block("bfs")), Ok(CutStrategy::Dfs));
        assert_eq!(cut(&opts, &block("xyz")), Ok(CutStrategy::Dfs));
        opts.prove_mode = true;
        assert_eq!(cut(&opts, &ConfigBlock::default()), Ok(CutStrategy::Dfs));
        assert_eq!(cut(&opts, &block("BFS")), Ok(CutStrategy::Bfs));
        assert_eq!(
            cut(&opts, &block("xyz")),
            Err("configuration block: unknown stop-on-trace method: xyz".to_string())
        );
        opts.stop_on_trace = Some(CutStrategy::SeqDfs);
        assert_eq!(cut(&opts, &block("xyz")), Ok(CutStrategy::SeqDfs));
        opts.prove_mode = false;
        assert_eq!(cut(&opts, &block("bfs")), Ok(CutStrategy::SeqDfs));
    }
}
