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
//! [`load_theory`] parses. [`translate_and_check_theory`] returns an open
//! theory for export, and [`close_theory`] prepares a theory for proving.
//! Batch mode proves the selected lemmas. The web UI builds its proof session
//! lazily.

use std::path::PathBuf;
use std::sync::Arc;

use tamarin_term::maude_proc::{MaudeHandle, MaudePool, SharedMaudeCaches};
use tamarin_theory::close_rule::NdcCheckedCache;
use tamarin_theory::closed_theory::{ClosedTheory, PreparedTheory};
use tamarin_theory::constraint::solver::context::{CutStrategy, IntrRuleCache};
use tamarin_theory::constraint::solver::sources::IntegerParameters;
use tamarin_theory::deriv_check::DerivCheckTimeout;
use tamarin_theory::module::ModuleType;
use tamarin_theory::prove::{ConfigBlock, ProveError};
use tamarin_theory::theory::Theory;
use tamarin_theory::tools::rule_variants::VariantsError;
use tamarin_theory::tools::EvaluationStyle;
use tamarin_theory::wellformedness::WfReport;

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
/// backends).
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
/// so `Theory loaded` follows [`elaborate_loaded`]: an elaboration error is an HS
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

/// The closed theory and the resources needed to prove or serve it.
pub struct ClosedTheoryLoad {
    pub theory: ClosedTheory,
    pub wf_report: WfReport,
    pub maude: MaudeHandle,
    pub maude_pool: Option<Arc<MaudePool>>,
    pub ndc_cache: IntrRuleCache,
    pub cut: CutStrategy,
    pe_trace: String,
}

impl ClosedTheoryLoad {
    /// Emit the trace when the front end first consumes the closed theory.
    pub fn print_partial_evaluation_trace(&self) {
        eprint!("{}", self.pe_trace);
    }
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

/// A translated, open theory and the load-time choices made from its source.
struct TranslatedTheory {
    theory: Theory,
    report: WfReport,
    maude_sig: tamarin_term::maude_sig::MaudeSig,
    auto_sources: bool,
    cut: CutStrategy,
}

impl TranslatedTheory {
    fn translate(
        opts: &TheoryLoadOptions,
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
        drop(parsed);
        let cut = effective_cut(opts, &config)?;

        // HS `addParamsOptions`: `addNdcOption` and `addLemmaToProve`.
        theory.options.deduction_chain_check = opts.ndc_check;
        theory.options.lemmas_to_prove = opts.lemma_names.clone();
        let maude_sig = theory.signature.clone();
        theory_marker(&theory.name, "Theory translated");

        // `Acc.checkWellformedness` reads the pre-translation theory.
        let acc_wf = tamarin_accountability::check_wellformedness(&theory);
        // HS `addHeuristic` returns `Nothing` when a `heuristic:` item exists.
        let user_set_heuristic = !theory.heuristic.is_empty();
        // `processOpenTheory`: `spthy` is `pure`, `spthytyped` is
        // `Sapic.typeTheory`, `msr` and close mode run `Sapic.typeTheory >=>
        // Sapic.translate >=> Acc.translate`.
        let mut report = match translate_module {
            Some(TranslateModule::Spthy | TranslateModule::SpthyTyped) => {
                let wf = tamarin_sapic::apply::sapic_pre_report(&theory);
                if translate_module == Some(TranslateModule::SpthyTyped) {
                    tamarin_sapic::type_theory::type_theory(&mut theory)
                        .map_err(|e| LoadError::Exception(e.message))?;
                }
                wf
            }
            None | Some(TranslateModule::Msr) => {
                // SAPIC and accountability exceptions (e.g. `duplicate rule`,
                // `CaseTestsUndefined`) escape to GHC's runtime.
                let wf = tamarin_sapic::apply::apply_sapic(&mut theory, user_set_heuristic)
                    .map_err(|e| LoadError::Exception(e.message))?;
                tamarin_accountability::translate(&mut theory)
                    .map_err(|e| LoadError::Exception(e.to_string()))?;
                wf
            }
        };
        report.extend(acc_wf);

        // `-m msr` keeps only the selected lemmas (`filterLemma
        // (lemmaSelector thyOpts)`), before the checks below.
        if translate_module == Some(TranslateModule::Msr) {
            let lemma_names = &opts.lemma_names;
            theory.items.retain(|i| match i {
                tamarin_theory::theory::TheoryItem::Lemma(l) => lemma_matches(lemma_names, &l.name),
                _ => true,
            });
        }
        Ok(Self {
            theory,
            report,
            maude_sig,
            auto_sources: opts.auto_sources || config.auto_sources,
            cut,
        })
    }

    fn maude(
        &self,
        opts: &TheoryLoadOptions,
        caches: &Arc<SharedMaudeCaches>,
    ) -> Result<MaudeHandle, LoadError> {
        MaudeHandle::start_with_caches(&opts.maude_path, self.maude_sig.clone(), Arc::clone(caches))
            .map_err(|_| {
                LoadError::Other(format!("failed to start maude at {:?}", opts.maude_path))
            })
    }

    fn maude_pool(
        &self,
        opts: &TheoryLoadOptions,
        caches: Arc<SharedMaudeCaches>,
    ) -> Option<Arc<MaudePool>> {
        // Parallel sites lease pool members instead of serialising on `maude`.
        if opts.maude_processes >= 2 {
            match MaudePool::new(
                &opts.maude_path,
                self.maude_sig.clone(),
                opts.maude_processes,
                caches,
            ) {
                Ok(pool) => Some(Arc::new(pool)),
                Err(e) => {
                    if !opts.quiet {
                        eprintln!(
                            "[warn] failed to spawn MaudePool({}): {} \
                                — falling back to single shared Maude",
                            opts.maude_processes, e
                        );
                    }
                    None
                }
            }
        } else {
            None
        }
    }
}

fn check_derivations(
    theory: &Theory,
    report: &mut WfReport,
    opts: &TheoryLoadOptions,
    maude: &MaudeHandle,
    pool: Option<&Arc<MaudePool>>,
) -> Result<NdcCheckedCache, LoadError> {
    let checked = tamarin_theory::close_rule::check_close_intr_rule(
        maude,
        Some(&theory.name),
        theory.options.deduction_chain_check,
        &theory.intruder_rules,
        opts.parameters,
    )?;
    // `checkVariableDeducibility`, skipped entirely when disabled.
    let timeout = opts.derivation_checks;
    if timeout.is_enabled() {
        theory_marker(&theory.name, "Derivation checks started");
        report.extend(tamarin_theory::deriv_check::check_message_derivation(
            theory,
            maude,
            pool,
            timeout,
            Some(checked.cache.clone()),
            opts.parameters,
        )?);
        theory_marker(&theory.name, "Derivation checks ended");
    }

    Ok(checked)
}

/// HS `translateAndCheckTheory`. Translation can produce an open theory
/// even if Maude is unavailable.
pub fn translate_and_check_theory(
    opts: &TheoryLoadOptions,
    parsed: tamarin_parser::Theory,
    in_file: &str,
    module: TranslateModule,
) -> Result<(Theory, WfReport), LoadError> {
    let mut open = TranslatedTheory::translate(opts, parsed, in_file, Some(module))?;
    let caches = Arc::new(SharedMaudeCaches::default());
    let maude = open.maude(opts, &caches);
    let pool = open.maude_pool(opts, caches);
    if let Ok(maude) = maude {
        open.report.extend(
            tamarin_theory::tools::rule_variants::prepare_theory_rules(
                &mut open.theory,
                &maude,
                pool.as_deref(),
                false,
            )
            .map_err(LoadError::variants)?,
        );
        check_derivations(&open.theory, &mut open.report, opts, &maude, pool.as_ref())?;
    } else {
        let report = tamarin_theory::wellformedness::check_wellformedness(&open.theory, None)
            .map_err(LoadError::variants)?;
        open.report.extend(report);
        // Translation still reports the derivation stage when Maude is unavailable.
        if opts.derivation_checks.is_enabled() {
            theory_marker(&open.theory.name, "Derivation checks started");
            theory_marker(&open.theory.name, "Derivation checks ended");
        }
    }
    if opts.quit_on_warning && !open.report.is_empty() {
        return Err(LoadError::Warning(open.report));
    }
    Ok((open.theory, open.report))
}

/// HS `closeTheory` up to proof search. Checking sees the open theory.
/// Closing consumes it, adopts the NDC verdicts and applies the requested
/// auto-sources and partial evaluation passes.
pub fn close_theory(
    opts: &TheoryLoadOptions,
    parsed: tamarin_parser::Theory,
    in_file: &str,
) -> Result<ClosedTheoryLoad, LoadError> {
    let mut open = TranslatedTheory::translate(opts, parsed, in_file, None)?;
    let caches = Arc::new(SharedMaudeCaches::default());
    let maude = open.maude(opts, &caches)?;
    let pool = open.maude_pool(opts, caches);
    let (prepared, report) = PreparedTheory::prepare(open.theory, &maude, pool.as_deref())
        .map_err(LoadError::variants)?;
    open.report.extend(report);
    let checked = check_derivations(
        prepared.theory(),
        &mut open.report,
        opts,
        &maude,
        pool.as_ref(),
    )?;
    theory_marker(&prepared.theory().name, "Theory closed");
    if opts.quit_on_warning && !open.report.is_empty() {
        return Err(LoadError::Warning(open.report));
    }

    let mut theory = prepared.close(&maude).map_err(LoadError::variants)?;
    for f in checked.ndc_funs {
        theory.join_ndc_in_sig(f, tamarin_term::function_symbols::NdcState::IsNdc);
    }

    let auto_sources = |theory: &mut ClosedTheory| -> Result<(), LoadError> {
        if open.auto_sources {
            theory.apply_auto_sources(
                maude.clone(),
                pool.clone(),
                Some(&checked.cache),
                opts.parameters,
            )?;
        }
        Ok(())
    };
    auto_sources(&mut theory)?;
    let mut pe_trace = String::new();
    if let Some(style) = opts.partial_evaluation {
        pe_trace = theory
            .apply_partial_evaluation(&maude, pool.as_deref(), style)
            .map_err(|e| {
                LoadError::Other(format!("partial evaluation of {in_file} failed: {e}"))
            })?;
        auto_sources(&mut theory)?;
    }
    Ok(ClosedTheoryLoad {
        theory,
        wf_report: open.report,
        maude,
        maude_pool: pool,
        ndc_cache: checked.cache,
        cut: open.cut,
        pe_trace,
    })
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
