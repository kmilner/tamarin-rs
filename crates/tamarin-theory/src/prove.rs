// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The per-theory prover session and per-lemma proof entry points: lemma
//! systems and contexts, heuristics, and the shared raw and refined sources
//! (HS `proveLemma`, ClosedTheory.hs and TheoryLoader.hs).

use crate::constraint::solver::context::{IntrRuleCache, ProofContext, SharedSources, SourceSlot};
use crate::constraint::solver::goals::RankingError;
use crate::constraint::solver::search::{run_proof_search_at_depth, ProofNode, ProofTimeLimit};
use crate::constraint::system::SourceKind;
use crate::guarded::{formula_to_guarded, Guarded};
use crate::theory::OpenProtoRule;
use std::sync::Arc;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_utils::cancellation;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    Cancelled,
    LemmaNotFound(String),
    Guarded(String),
    InvalidHeuristic(String),
    Ranking(RankingError),
    Maude(String),
    UnsupportedInput(String),
}

impl From<tamarin_utils::cancellation::Cancelled> for ProveError {
    fn from(_: tamarin_utils::cancellation::Cancelled) -> Self {
        Self::Cancelled
    }
}

impl From<crate::tools::equation_store::AddEqsError> for ProveError {
    fn from(error: crate::tools::equation_store::AddEqsError) -> Self {
        let crate::tools::equation_store::AddEqsError::Maude(message) = error;
        Self::Maude(message)
    }
}

impl From<RankingError> for ProveError {
    fn from(error: RankingError) -> Self {
        Self::Ranking(error)
    }
}

impl From<crate::tools::rule_variants::VariantsError> for ProveError {
    fn from(error: crate::tools::rule_variants::VariantsError) -> Self {
        match error {
            crate::tools::rule_variants::VariantsError::Maude(message) => Self::Maude(message),
            other => Self::UnsupportedInput(other.to_string()),
        }
    }
}

/// Policy local to one automatic search. Interactive requests must not
/// mutate the theory-wide prover session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SearchOptions {
    pub proof_bound: usize,
    pub ranking_depth_offset: usize,
    pub cut: crate::constraint::solver::context::CutStrategy,
    pub oracle_only: bool,
}

/// HS `formulaToGuarded_ = either (error . render) id` (Guarded.hs):
/// the guarded formula, or the full `ppError` doc (Guarded.hs) HS dies
/// with — the error text, the quoted failing sub-formula (both
/// quantifier-level errors include `ppFormula f0`, Guarded.hs), then "in the formula" and the quoted converted formula.
fn guarded_or_error(f: &crate::formula::LNFormula) -> Result<Guarded, ProveError> {
    formula_to_guarded(f).map_err(|e| {
        ProveError::Guarded(e.full_doc(f).render_with(
            crate::pretty_hpj::DEFAULT_LINE_LENGTH,
            crate::pretty_hpj::DEFAULT_RIBBON,
        ))
    })
}

impl ProveError {
    /// A failed Maude call made for `context`. A cancelled call stays a
    /// cancellation instead of becoming a Maude error.
    pub(crate) fn maude(context: &str, error: tamarin_term::maude_proc::MaudeError) -> Self {
        match error {
            tamarin_term::maude_proc::MaudeError::Cancelled => ProveError::Cancelled,
            error if context.is_empty() => ProveError::Maude(error.to_string()),
            error => ProveError::Maude(format!("{context}: {error}")),
        }
    }
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveError::Cancelled => f.write_str("proof cancelled"),
            ProveError::LemmaNotFound(n) => write!(f, "lemma not found: {}", n),
            ProveError::Guarded(m) => write!(f, "guarded conversion: {}", m),
            ProveError::InvalidHeuristic(m) => f.write_str(m),
            ProveError::Ranking(m) => write!(f, "goal ranking: {m}"),
            ProveError::Maude(m) => write!(f, "Maude error: {m}"),
            ProveError::UnsupportedInput(m) => write!(f, "{m}"),
        }
    }
}

impl std::error::Error for ProveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ProveError::Ranking(error) => Some(error),
            ProveError::Cancelled
            | ProveError::LemmaNotFound(_)
            | ProveError::Guarded(_)
            | ProveError::InvalidHeuristic(_)
            | ProveError::Maude(_)
            | ProveError::UnsupportedInput(_) => None,
        }
    }
}

/// HS `System.FilePath.takeDirectory`: the directory portion of a path.
///
/// Crucially, HS returns `"."` (NOT `""`) for a path with no directory
/// component (e.g. `takeDirectory "foo.spthy" == "."`), and drops a trailing
/// slash from the directory (e.g. `takeDirectory "a/b" == "a"`).  Rust's
/// `Path::parent()` returns `Some("")` for a no-dir path, which — when later
/// joined and handed to `Command::new` — produces a path with NO `/`
/// (e.g. `"foo.oracle"`), which Unix `exec` treats as a PATH lookup rather
/// than a CWD-relative file.  HS's `"." </> "foo.oracle" == "./foo.oracle"`
/// execs from the CWD.  Mirroring `takeDirectory`'s `"."` here is what makes
/// the oracle path exec-faithful (Theory/Text/Parser.hs `workDir = takeDirectory inFile`).
fn hs_take_directory(path: &str) -> String {
    match path.rfind('/') {
        // Strip the final segment.  HS keeps any leading run so e.g.
        // `takeDirectory "/a/b" == "/a"`, `takeDirectory "a/b" == "a"`.
        // A path like `"a/"` → `"a"`.  Collapse a bare `""` (root-only
        // e.g. `"/foo"` → `"/"`) per HS (`takeDirectory "/foo" == "/"`).
        Some(0) => "/".to_string(),
        Some(i) => path[..i].to_string(),
        None => ".".to_string(),
    }
}

/// HS `System.FilePath.</>`: join two path components with a single `/`,
/// but if the right side is absolute it REPLACES the left (HS semantics).
/// We only ever call this with a non-absolute right side (absolute relPaths
/// short-circuit at the caller), so the simple join suffices; we still guard
/// the absolute case to stay faithful.  An empty left side yields the right
/// side unchanged (HS `"" </> b == b`).
fn hs_combine(a: &str, b: &str) -> String {
    if b.starts_with('/') {
        return b.to_string();
    }
    if a.is_empty() {
        return b.to_string();
    }
    if a.ends_with('/') {
        format!("{}{}", a, b)
    } else {
        format!("{}/{}", a, b)
    }
}

/// Resolve an oracle ranking's relPath against a workDir, mirroring HS
/// `oraclePath oracle = fromMaybe "." workDir </> normalise relPath`
/// (System.hs). `work_dir` is the directory attached to the oracle;
/// an absent directory falls back to `"."`.
/// The relPath is normalised BEFORE the join (`normalise "./oracle-x"` =
/// `"oracle-x"`), so a `heuristic: o "./oracle-x"` under a real theory dir
/// yields `<dir>/oracle-x` — the web sequent pane prints this path verbatim
/// ("Goals sorted according to an oracle … located at <path>").  The
/// leading `./` of a CWD-relative result comes from the join with workDir
/// `"."`, exactly as in HS.
fn resolve_oracle_path(oracle_path: &str, work_dir: Option<&str>) -> String {
    let normalized = hs_normalise_path(oracle_path);
    if std::path::Path::new(oracle_path).is_absolute() {
        return normalized;
    }
    let wd = work_dir.unwrap_or(".");
    hs_combine(wd, &normalized)
}

/// The Unix spelling of HS `System.FilePath.normalise`: drop `.` segments and
/// redundant separators without collapsing `..`.
fn hs_normalise_path(p: &str) -> String {
    let absolute = p.starts_with('/');
    let segs: Vec<&str> = p
        .split('/')
        .filter(|s| !s.is_empty() && *s != ".")
        .collect();
    if segs.is_empty() {
        if absolute { "/" } else { "." }.to_string()
    } else if absolute {
        format!("/{}", segs.join("/"))
    } else {
        segs.join("/")
    }
}

/// A theory's in-file `configuration:` block as cmdargs RECORDS it — HS
/// `closeTheory`'s `argsConfigString` (TheoryLoader.hs) runs
/// `processValue` over a two-flag mode: `--stop-on-trace[=v]`
/// (`flagOpt "dfs"` — valueless records `dfs`, and no separate token is
/// ever consumed) and `--auto-sources` (`flagNone`).  Bare tokens land in
/// the positional catch-all (`flagArg (updateArg "") ""`) and are ignored.
///
/// Rejections are RECORDED here, not raised.  (In HS the block is
/// processed lazily and its errors surface at scattered forcing points;
/// the shared theory loader validates the record eagerly instead: it checks
/// `flag_error` and reads the value through its `effective_cut`.)
#[derive(Debug, Clone, Default)]
pub struct ConfigBlock {
    /// The first cmdargs-level rejection, message exactly as HS emits it:
    /// `Unknown flag: --x`, `Unhandled argument to flag, none expected:
    /// --auto-sources=x`, `Ambiguous flag '--', could be any of: …`.
    pub flag_error: Option<String>,
    /// The recorded `--stop-on-trace` value, RAW — validation is the
    /// reader's (HS `stopOnTrace`, TheoryLoader.hs, via
    /// [`parse_stop_on_trace`]).
    pub stop_on_trace: Option<String>,
    /// `--auto-sources` was given.
    pub auto_sources: bool,
}

/// Parse a `configuration:` block with cmdargs' own matching, all
/// oracle-verified: a long flag resolves by exact name, else by
/// unambiguous prefix over the two declared names (`--stop`, even `--s`;
/// `--=x` is ambiguous over both, listed in declaration order); an inline
/// value on the `flagNone` rejects with the whole token; a short flag is
/// unknown by its FIRST cluster char (`-abc` → `Unknown flag: -a`).
pub fn parse_config_block(cfg: &str) -> ConfigBlock {
    // Declaration order (TheoryLoader.hs) — ambiguity lists it.
    const NAMES: [&str; 2] = ["stop-on-trace", "auto-sources"];
    let mut out = ConfigBlock::default();
    for tok in cfg.split_whitespace() {
        if out.flag_error.is_some() {
            break;
        }
        if tok == "--" {
            // End of flags: the rest is positional, hence ignored.
            break;
        }
        if let Some(rest) = tok.strip_prefix("--") {
            let (key, val) = match rest.find('=') {
                Some(i) => (&rest[..i], Some(&rest[(i + 1)..])),
                None => (rest, None),
            };
            let hits: Vec<&str> = NAMES
                .iter()
                .copied()
                .filter(|n| n.starts_with(key))
                .collect();
            match hits.as_slice() {
                [] => out.flag_error = Some(format!("Unknown flag: --{key}")),
                ["stop-on-trace"] => {
                    out.stop_on_trace = Some(val.unwrap_or("dfs").to_string());
                }
                ["auto-sources"] => match val {
                    Some(_) => {
                        out.flag_error =
                            Some(format!("Unhandled argument to flag, none expected: {tok}"));
                    }
                    None => out.auto_sources = true,
                },
                _ => {
                    out.flag_error = Some(format!(
                        "Ambiguous flag '--{key}', could be any of: {}",
                        hits.join(" ")
                    ));
                }
            }
        } else if let Some(rest) = tok.strip_prefix('-') {
            // No short flags are declared; a bare `-` is positional.
            if let Some(c) = rest.chars().next() {
                out.flag_error = Some(format!("Unknown flag: -{c}"));
            }
        }
        // Bare token: cmdargs positional catch-all — ignored.
    }
    out
}

/// HS `stopOnTrace` (TheoryLoader.hs): the value is matched
/// LOWERCASED, and an unknown one is `ArgumentError ("unknown
/// stop-on-trace method: " ++ unknown)` — raised as `error e`
/// (TheoryLoader.hs) only where the prover forces the field.
pub fn parse_stop_on_trace(
    raw: &str,
) -> Result<crate::constraint::solver::context::CutStrategy, String> {
    use crate::constraint::solver::context::CutStrategy;
    match raw.to_ascii_lowercase().as_str() {
        "dfs" => Ok(CutStrategy::Dfs),
        "bfs" => Ok(CutStrategy::Bfs),
        "seqdfs" => Ok(CutStrategy::SeqDfs),
        "sorry" => Ok(CutStrategy::AfterSorry),
        "none" => Ok(CutStrategy::Nothing),
        other => Err(format!("unknown stop-on-trace method: {}", other)),
    }
}

/// The CLI-supplied heuristic / oracle flags, carried verbatim from the
/// command line.  Mirrors the `AutoProver` fields populated by HS
/// `constructAutoProver` (TheoryLoader.hs) from `thyOpts`:
///   * `raw`         = `--heuristic` ranking string (`apDefaultHeuristic`)
///   * `oracle_name` = `--oraclename` (`Just "" -> Nothing`, TheoryLoader.hs)
///   * `oracle_only` = `--oracle-only` (`quitOnEmptyOracle`)
///
/// `None` for any field means the flag was absent.  This whole struct is
/// `None` on `ProverSession`/the prove entry points when `--heuristic` was
/// not given, in which case the per-lemma / theory heuristic is used unchanged
/// (HS `selectHeuristic`: `apDefaultHeuristic <|> pcHeuristic`,
/// Theory/Proof.hs).
#[derive(Debug, Clone, Default)]
pub struct CliHeuristic {
    /// `--heuristic` raw ranking string (e.g. `"O"`, `"iSs"`).  When
    /// `Some`, this OVERRIDES the per-lemma / theory `heuristic:` (HS
    /// `apDefaultHeuristic prover <|> L.get pcHeuristic ctx`,
    /// Theory/Proof.hs).
    pub raw: Option<String>,
    /// `--oraclename` — sets the oracle relPath for EVERY oracle ranking in
    /// the CLI heuristic (HS `mapOracleRanking (maybeSetOracleRelPath
    /// oraclename)`, TheoryLoader.hs).  `Just ""` parses to `None`.
    pub oracle_name: Option<String>,
    /// `--oracle-only` — sets `quitOnEmpty` on every oracle / tactic ranking
    /// in the selected heuristic (HS `setQuitOnEmpty`,
    /// Theory/Proof.hs).
    pub oracle_only: bool,
}

/// Resolve the CLI `--heuristic`/`--oraclename` into a `GoalRanking` list,
/// mirroring HS's CLI heuristic pipeline:
///
///   1. `filterHeuristic diff rawRankings` — parse the ranking string char
///      by char (System.hs).  RS `parse_heuristic_str_with_tactics`.
///   2. `map (mapOracleRanking (maybeSetOracleRelPath oraclename))` — set the
///      oracle relPath from `--oraclename` (TheoryLoader.hs).
///   3. `defaultOracleNames srcThyInFileName` (TheoryLoader.hs) — fill any
///      oracle ranking that STILL has no relPath with the default `.oracle`
///      name (theory-basename `.oracle` if it exists on disk, else `"oracle"`).
///   4. `defaultOracleNames` assigns the theory directory as the workDir when
///      filling an absent path. An explicit `--oraclename` leaves the CLI
///      ranking's workDir absent and is therefore CWD-relative.
///   5. `setQuitOnEmpty` (Theory/Proof.hs) — `--oracle-only` sets
///      `quitOnEmpty` on every oracle / tactic ranking.
fn resolve_cli_heuristic(
    cli: &CliHeuristic,
    in_file: &str,
    tactics: &[crate::tactic::Tactic],
) -> Option<Vec<crate::constraint::solver::goals::GoalRanking>> {
    let raw = cli.raw.as_ref()?;
    // Step 1: parse the ranking string.  `parse_heuristic_str_with_tactics`
    // also computes the default `.oracle` name (HS `defaultOracleNames`) for
    // oracle rankings without an inline `"path"` — which covers BOTH HS step 2
    // (oraclename, applied below) and step 3 (default name).
    let mut rankings =
        crate::constraint::solver::goals::parse_heuristic_str_with_tactics(raw, in_file, tactics);
    resolve_oracle_rankings(&mut rankings, in_file, cli.oracle_name.as_deref());
    if cli.oracle_only {
        set_quit_on_empty(&mut rankings);
    }
    Some(rankings)
}

/// HS `setQuitOnEmpty` (Theory/Proof.hs): `--oracle-only` sets `quitOnEmpty`
/// on every oracle and tactic ranking.
fn set_quit_on_empty(rankings: &mut [crate::constraint::solver::goals::GoalRanking]) {
    use crate::constraint::solver::goals::GoalRanking;
    for ranking in rankings {
        if let GoalRanking::Oracle { quit_on_empty, .. }
        | GoalRanking::OracleSmart { quit_on_empty, .. }
        | GoalRanking::Tactic { quit_on_empty, .. } = ranking
        {
            *quit_on_empty = true;
        }
    }
}

/// Resolve oracle paths. HS `oraclePath oracle = fromMaybe "." workDir </>
/// normalise relPath` (System.hs) with `workDir = takeDirectory inFile`; the
/// `"."` prefix gives the path its leading `./`, so `exec` resolves it from
/// the CWD rather than by PATH lookup. A non-empty `--oraclename` (`Just ""
/// -> Nothing`, TheoryLoader.hs) replaces the path and stays CWD-relative.
fn resolve_oracle_rankings(
    rankings: &mut [crate::constraint::solver::goals::GoalRanking],
    in_file: &str,
    oracle_name: Option<&str>,
) {
    use crate::constraint::solver::goals::GoalRanking;
    let work_dir = hs_take_directory(in_file);
    let oracle_name = oracle_name.filter(|name| !name.is_empty());
    for ranking in rankings {
        let (GoalRanking::Oracle { oracle_path, .. }
        | GoalRanking::OracleSmart { oracle_path, .. }) = ranking
        else {
            continue;
        };
        *oracle_path = if let Some(name) = oracle_name {
            resolve_oracle_path(name, None)
        } else {
            resolve_oracle_path(oracle_path, Some(&work_dir))
        };
    }
}

/// Resolve every oracle referenced by one heuristic exactly as proving does.
/// Used by parser-backed cache/staging manifests so dependency selection and
/// execution cannot drift.
pub fn oracle_paths_for_heuristic(
    raw: &str,
    in_file: &str,
    oracle_name: Option<&str>,
) -> Vec<String> {
    use crate::constraint::solver::goals::GoalRanking;
    let mut rankings =
        crate::constraint::solver::goals::parse_heuristic_str_with_tactics(raw, in_file, &[]);
    resolve_oracle_rankings(&mut rankings, in_file, oracle_name);
    rankings
        .iter_mut()
        .filter_map(|ranking| match ranking {
            GoalRanking::Oracle { oracle_path, .. }
            | GoalRanking::OracleSmart { oracle_path, .. } => Some(std::mem::take(oracle_path)),
            _ => None,
        })
        .collect()
}

/// Validate the CLI `--heuristic` string against the set HS actually
/// accepts (`filterHeuristic`, System.hs): identifier characters
/// from `goalRankingIdentifiers` plus `{tactic}` groups whose name is
/// declared by the theory (`chosenTactic`, ProofMethod.hs; names
/// match verbatim, no trim).  The shared parser
/// (`parse_heuristic_str_with_tactics`) is deliberately lenient — unknown
/// input falls back to the smart ranking, which is right for in-file
/// `heuristic:` headers and the web routes but on the CLI would prove the
/// theory under a heuristic the user never asked for and report a verdict
/// HS refuses to produce.  So the batch prove loop rejects first.  The
/// wording (and the rejection's timing relative to HS's lazy forcing) is
/// ours, per the canonical-clap policy: invalid usage needs a loud error,
/// not the oracle's bytes.
pub fn validate_cli_heuristic(
    cli: &CliHeuristic,
    tactics: &[crate::tactic::Tactic],
) -> Result<(), String> {
    let Some(raw) = cli.raw.as_deref() else {
        return Ok(());
    };
    if raw.is_empty() {
        return Err("--heuristic: at least one ranking must be given".to_string());
    }
    let chars: Vec<char> = raw.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '{' {
            let Some(len) = chars[i + 1..].iter().position(|&x| x == '}') else {
                return Err(format!("--heuristic: unterminated '{{' in {raw:?}"));
            };
            let name: String = chars[i + 1..i + 1 + len].iter().collect();
            if !tactics.iter().any(|t| t.name == name) {
                let declared = if tactics.is_empty() {
                    "the theory declares no tactics".to_string()
                } else {
                    let names: Vec<&str> = tactics.iter().map(|t| t.name.as_str()).collect();
                    format!("declared: {}", names.join(", "))
                };
                return Err(format!(
                    "--heuristic: tactic {name:?} is not declared in the theory ({declared})"
                ));
            }
            i += len + 2;
            continue;
        }
        let c = chars[i];
        if !matches!(c, 's' | 'S' | 'o' | 'O' | 'p' | 'P' | 'c' | 'C' | 'i' | 'I') {
            return Err(format!(
                "--heuristic: unknown goal ranking {c:?} \
                 (valid: s S i I c C o O p P, or a declared '{{tactic}}')"
            ));
        }
        i += 1;
    }
    Ok(())
}

#[derive(Clone, Default)]
struct SourceCache {
    raw: Arc<SourceSlot>,
    refined: Arc<SourceSlot>,
}

impl SourceCache {
    fn slot(&self, kind: SourceKind) -> &Arc<SourceSlot> {
        match kind {
            SourceKind::RawSources => &self.raw,
            SourceKind::RefinedSources => &self.refined,
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        usize::from(self.raw.ready.get().is_some())
            + usize::from(self.refined.ready.get().is_some())
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Shares the theory's prepared rules, lemma formulas, and source patterns.
/// With source caching enabled, multi-worker batches prepare sources before
/// proving several selected lemmas. Single selections and interactive proofs
/// request sources on demand.
#[derive(Clone)]
pub struct ProverSession {
    /// The closed theory: lemmas, restrictions, rules, heuristic. Shares the
    /// caller's allocation; the session never mutates it.
    theory: crate::closed_theory::ClosedTheory,
    /// Guarded formulas and resolved rankings aligned with `theory.lemmas()`.
    prepared_lemmas: std::sync::Arc<[PreparedLemma]>,
    /// The `[sources]` subset of `prepared_lemmas`, retained as shared handles.
    source_assumptions: std::sync::Arc<Result<Vec<std::sync::Arc<Guarded>>, ProveError>>,
    /// Solved-leaf extraction strategy (HS `apCut`, threaded from
    /// `--stop-on-trace`, TheoryLoader.hs).  Theory-global (HS
    /// stores it once in `TheoryLoadOptions.stopOnTrace`), so it is set on
    /// every per-lemma `ProofContext` in [`Self::setup_per_lemma_ctx`].
    cut: crate::constraint::solver::context::CutStrategy,
    /// Template `ProofContext` carrying the expensive precompute:
    /// `rules` (with variants installed), `intruder_rules`,
    /// `full_sources` (raw, unsaturated cells), etc.
    /// Proof contexts share the template's ordered source goals.
    template_ctx: std::sync::Arc<ProofContext>,
    /// Fresh-counter value BEFORE the template was built.  The template
    /// build is counter-neutral (the build's fresh allocation is undone by
    /// restoring the counter), so every lemma starts from this same base.
    /// Used as the `ensure_above` floor on the per-lemma counter clone.
    setup_counter_before: u64,
    /// Raw and refined results are published once per successful build.
    source_cache: SourceCache,
    /// Snapshot the process-wide diagnostic gate when the session is built so
    /// all contexts in one session follow the same cache policy.
    source_cache_disabled: bool,
}

// Jobs own their position in the immutable theory, so the pool can run them
// without borrowing the batch or cloning proof trees.
#[derive(Clone, Copy)]
struct LemmaJob {
    lemma_index: usize,
    item_index: usize,
    bound: Option<usize>,
    source_kind: Option<SourceKind>,
}

#[derive(Clone)]
struct PreparedLemma {
    guarded: Result<std::sync::Arc<Guarded>, ProveError>,
    heuristic: Option<Vec<crate::constraint::solver::goals::GoalRanking>>,
}

/// Frontend policy for one shared prover session.
pub struct ProverSessionOptions {
    pub maude_pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    pub cli_heuristic: CliHeuristic,
    pub cut: crate::constraint::solver::context::CutStrategy,
    pub ndc_cache: Option<IntrRuleCache>,
    pub parameters: crate::constraint::solver::sources::IntegerParameters,
    pub sys_retention: crate::constraint::solver::search::SysRetention,
    /// Primary theory closes trace source-saturation progress; auxiliary
    /// deduction and derivation checks use `ProofContextOptions::default()`.
    pub show_saturation_steps: bool,
}

impl Default for ProverSessionOptions {
    fn default() -> Self {
        Self {
            maude_pool: None,
            cli_heuristic: CliHeuristic::default(),
            cut: crate::constraint::solver::context::CutStrategy::Dfs,
            ndc_cache: None,
            parameters: crate::constraint::solver::sources::IntegerParameters::default(),
            sys_retention: crate::constraint::solver::search::SysRetention::DropAll,
            show_saturation_steps: true,
        }
    }
}

struct SessionSourceProvider {
    kind: SourceKind,
    session: ProverSession,
}

impl std::fmt::Debug for SessionSourceProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SessionSourceProvider")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}

impl crate::constraint::solver::context::SourceProvider for SessionSourceProvider {
    fn may_fail(&self) -> bool {
        self.kind == SourceKind::RefinedSources && self.session.source_assumptions.is_err()
    }

    fn materialize(&self, maude: &MaudeHandle) -> Result<SharedSources, ProveError> {
        self.session.sources(self.kind, maude)
    }
}

/// HS `inductionHint` (ClosedTheory.hs): a lemma tagged
/// `[use_induction]` (`InvariantLemma`) or `[sources]` (`SourceLemma`) is
/// proved with `pcUseInduction = UseInduction`, so its first proof method is
/// Induction; every other lemma avoids it.
pub(crate) fn induction_hint(
    lemma: &crate::theory::Lemma,
) -> crate::constraint::solver::context::UseInduction {
    use crate::constraint::solver::context::UseInduction;
    if lemma.attributes.iter().any(|a| {
        matches!(
            a,
            crate::theory::LemmaAttr::UseInduction | crate::theory::LemmaAttr::Sources
        )
    }) {
        UseInduction::UseInduction
    } else {
        UseInduction::AvoidInduction
    }
}

/// Gather the visible reusable assumptions in declaration order.
fn gather_reusable_lemmas(
    theory: &crate::theory::Theory,
    prepared_lemmas: &[PreparedLemma],
    lemma: &crate::theory::Lemma,
) -> Result<Vec<std::sync::Arc<Guarded>>, ProveError> {
    theory
        .lemmas()
        .zip(prepared_lemmas)
        .take_while(|(prior, _)| prior.name != lemma.name)
        .filter(|(prior, _)| lemma.can_reuse(prior))
        .map(|(_, prepared)| prepared.guarded.clone())
        .collect()
}

/// Refined sources use every all-traces `[sources]` assumption in the theory,
/// regardless of declaration order. Source lemmas themselves use raw sources.
fn gather_typing_assumptions(
    theory: &crate::theory::Theory,
    prepared_lemmas: &[PreparedLemma],
) -> Result<Vec<std::sync::Arc<Guarded>>, ProveError> {
    let mut typing_assumptions = Vec::new();
    for (lemma, prepared) in theory.lemmas().zip(prepared_lemmas) {
        if !lemma.is_source_assumption() {
            continue;
        }
        typing_assumptions.push(prepared.guarded.clone()?);
    }
    Ok(typing_assumptions)
}

/// `--precompute-only` stats (HS `prettyPrecomputation`, ClosedTheory.hs):
/// protocol-rule count, raw/refined source-GROUP counts (`length cases` over
/// `getSource kind thy` — the number of `Source` entries, not the per-case
/// total), unsolved-chain sums, and whether the label needs the
/// "and restrictions" suffix (`theoryRestrictions thy` non-empty).
pub struct PrecomputationStats {
    pub rules: usize,
    pub raw_cases: usize,
    pub raw_chains: usize,
    pub refined_cases: usize,
    pub refined_chains: usize,
    pub has_restrictions: bool,
}

/// Counts used by the web source overview without cloning source systems.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceCaseStats {
    pub cases: usize,
    pub chains: usize,
}

/// Raw and refined source counts. Both can fail on Maude errors; guarded
/// conversion of a refined-source assumption may fail independently.
pub struct SourceStats {
    pub raw: Result<SourceCaseStats, ProveError>,
    pub refined: Result<SourceCaseStats, ProveError>,
}

/// Resolve the goal-ranking heuristic for a lemma, mirroring HS
/// `selectHeuristic prover ctx = apDefaultHeuristic prover <|> L.get
/// pcHeuristic ctx` (Theory/Proof.hs): the CLI `--heuristic`
/// (`apDefaultHeuristic`) OVERRIDES the per-lemma / theory heuristic when
/// present.  Otherwise fall back to per-lemma `[heuristic=..]` > theory-level
/// `heuristic:` > None (`getProofContext.specifiedHeuristic`,
/// ClosedTheory.hs); `None` becomes `SmartRanking False` downstream.
/// The lemma attribute keeps its elaboration-frozen text, so it is parsed
/// here, with `{name}` tactic rankings resolved against `tactics`; the
/// theory's header is already parsed. Oracle paths are resolved beside the
/// root or included file that declared the selected heuristic.
fn resolve_heuristic(
    cli: Option<&[crate::constraint::solver::goals::GoalRanking]>,
    lemma: &crate::theory::Lemma,
    theory_heuristic: &[crate::constraint::solver::goals::GoalRanking],
    tactics: &[crate::tactic::Tactic],
    in_file: &str,
    theory_heuristic_in_file: Option<&str>,
) -> Option<Vec<crate::constraint::solver::goals::GoalRanking>> {
    if let Some(rankings) = cli {
        return Some(rankings.to_vec());
    }
    let lemma_heuristic: Option<&str> = lemma.attributes.iter().find_map(|a| match a {
        crate::theory::LemmaAttr::Heuristic(s) => Some(s.as_str()),
        _ => None,
    });
    let (mut rankings, ranking_file) = match lemma_heuristic {
        Some(h) => {
            let source = lemma.heuristic_in_file.as_deref().unwrap_or(in_file);
            (
                crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
                    h, source, tactics,
                ),
                source,
            )
        }
        None if !theory_heuristic.is_empty() => (
            theory_heuristic.to_vec(),
            theory_heuristic_in_file.unwrap_or(in_file),
        ),
        None => return None,
    };
    resolve_oracle_rankings(&mut rankings, ranking_file, None);
    Some(rankings)
}

impl ProverSession {
    /// The immutable theory this session and all of its caches describe.
    pub fn theory(&self) -> &crate::closed_theory::ClosedTheory {
        &self.theory
    }

    /// The first remaining lemma whose formula cannot be guarded.
    pub fn first_lemma_error(&self) -> Option<&ProveError> {
        self.prepared_lemmas
            .iter()
            .find_map(|prepared| prepared.guarded.as_ref().err())
    }

    /// Remove a lemma. Raw sources depend only on the rules and restrictions,
    /// while refined sources also depend on the surviving source assumptions.
    pub fn without_lemma(&self, name: &str) -> Option<Self> {
        let (index, removed) = self
            .theory
            .lemmas()
            .enumerate()
            .find(|(_, lemma)| lemma.name == name)?;
        let mut prepared_lemmas = self.prepared_lemmas.to_vec();
        prepared_lemmas.remove(index);
        let mut edited = Self {
            theory: self.theory.without_lemma(name)?,
            prepared_lemmas: prepared_lemmas.into(),
            ..self.clone()
        };
        if removed.is_source_assumption() {
            edited.source_assumptions = Arc::new(gather_typing_assumptions(
                &edited.theory,
                &edited.prepared_lemmas,
            ));
            edited.source_cache.refined = Arc::default();
        }
        Some(edited)
    }

    /// Read the theory-wide, unspecialised context built by this session.
    ///
    /// This is intended for web views which only inspect immutable
    /// close-time data. Lemma proof operations must use
    /// [`Self::context_for_lemma`].
    pub fn template_context(&self) -> &ProofContext {
        &self.template_ctx
    }

    /// Prove selected lemmas and replay stored proofs for the rest. A selected
    /// lemma gets the supplied depth bound. Render each completed tree on its
    /// worker and return the rendered results in declaration order.
    /// Selection runs on the caller. Renderers can run concurrently and must
    /// follow the nesting rules of [`tamarin_utils::parallel::try_map`]. An
    /// independent Rayon join can steal work from a blocked ancestor.
    pub fn map_lemma_proofs<T: Send + 'static>(
        &self,
        selected_bound: impl Fn(&crate::theory::Lemma) -> Option<usize>,
        render: impl Fn(&crate::theory::Lemma, ProofNode) -> T + Sync + Send + 'static,
    ) -> Result<Vec<T>, ProveError> {
        cancellation::check()?;
        let jobs = self.lemma_jobs(selected_bound);
        let session = self.clone();
        // Search durations start separately for each lemma, on whichever worker
        // takes it. Capture the caller's policy before dispatch changes threads.
        let time_limit = ProofTimeLimit::current();
        tamarin_utils::parallel::with_worker(move || {
            session.map_prepared_lemmas(jobs, time_limit, render)
        })
    }

    fn lemma_jobs(
        &self,
        selected_bound: impl Fn(&crate::theory::Lemma) -> Option<usize>,
    ) -> Vec<LemmaJob> {
        self.theory
            .items
            .iter()
            .enumerate()
            .filter_map(|(item_index, item)| {
                let crate::theory::TheoryItem::Lemma(lemma) = item else {
                    return None;
                };
                Some((item_index, lemma))
            })
            .enumerate()
            .map(|(lemma_index, (item_index, lemma))| {
                let bound = selected_bound(lemma);
                LemmaJob {
                    lemma_index,
                    item_index,
                    bound,
                    source_kind: (bound.is_some() || lemma.proof.is_some())
                        .then(|| lemma.source_kind()),
                }
            })
            .collect()
    }

    fn map_prepared_lemmas<T: Send + 'static>(
        self,
        lemmas: Vec<LemmaJob>,
        time_limit: ProofTimeLimit,
        render: impl Fn(&crate::theory::Lemma, ProofNode) -> T + Sync + Send + 'static,
    ) -> Result<Vec<T>, ProveError> {
        // Replay can consume sources too, but selecting a single lemma keeps its
        // batch demand-driven. Refined sources include the raw build.
        let selected = lemmas.iter().filter(|job| job.bound.is_some()).count();
        // A malformed theory reports the error of its first lemma in error,
        // which building the sources first could pre-empt.
        let guarded_may_fail = self.guarded_lemmas_may_fail();
        if !self.source_cache_disabled
            && !guarded_may_fail
            && selected > 1
            && rayon::current_num_threads() > 1
            && let Some(kind) = lemmas.iter().filter_map(|job| job.source_kind).max()
        {
            self.sources(kind, &self.template_ctx.maude)?;
        }

        let pool = self.template_ctx.maude_pool.clone();
        let primary = self.template_ctx.maude.clone();
        let prove = move |job: LemmaJob, maude: &MaudeHandle| {
            let crate::theory::TheoryItem::Lemma(lemma) = &self.theory.items[job.item_index] else {
                unreachable!("batch jobs refer to lemma items")
            };
            let _deadline = time_limit.install();
            let proof = prove_lemma_in_session_mode(
                &self,
                (lemma, &self.prepared_lemmas[job.lemma_index]),
                job.bound.unwrap_or(usize::MAX),
                job.bound.is_some(),
                maude,
            )?;
            Ok::<_, ProveError>(render(lemma, proof))
        };
        // Replay also needs a guarded formula. For malformed theories, visit
        // lemmas in declaration order so an earlier proof can report its own error.
        if guarded_may_fail {
            return lemmas
                .into_iter()
                .map(|item| {
                    cancellation::check()?;
                    prove(item, &primary)
                })
                .collect();
        }
        // A helper tries for a process before it takes a lemma, so a start
        // that hangs holds up no lemma. Without one it shares the primary's,
        // as every helper does when at most one lemma needs Maude.
        let searching = lemmas
            .iter()
            .filter(|job| job.source_kind.is_some())
            .count();
        let pool = pool.filter(|_| searching > 1);
        tamarin_utils::parallel::try_map_with_helpers(
            lemmas,
            move || {
                let own = pool.as_ref().and_then(|pool| pool.try_acquire_ready());
                Some(own.map_or(
                    tamarin_utils::parallel::Helper::Shared,
                    tamarin_utils::parallel::Helper::Own,
                ))
            },
            move |lease, item| prove(item, lease.as_deref().unwrap_or(&primary)),
        )
    }

    /// Whether per-lemma setup can fail anywhere in the batch traversal.
    pub fn guarded_lemmas_may_fail(&self) -> bool {
        self.prepared_lemmas
            .iter()
            .any(|prepared| prepared.guarded.is_err())
    }

    fn lemma_and_prepared(
        &self,
        lemma_name: &str,
    ) -> Result<(&crate::theory::Lemma, &PreparedLemma), ProveError> {
        self.theory
            .lemmas()
            .zip(self.prepared_lemmas.iter())
            .find(|(lemma, _)| lemma.name == lemma_name)
            .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))
    }

    /// Build the structural per-lemma context used by batch and web replay.
    /// Constructing the context does not force its sources.
    pub fn context_for_lemma(&self, lemma_name: &str) -> Result<ProofContext, ProveError> {
        let (lemma, prepared) = self.lemma_and_prepared(lemma_name)?;
        Ok(self.setup_per_lemma_ctx(lemma, prepared, &self.template_ctx.maude))
    }

    /// Build a disposable source context for interactive views. Materialise
    /// through the same provider as proof search so cache bypass and deferred
    /// conversion failures have one implementation.
    pub fn context_for_sources(&self, kind: SourceKind) -> Result<ProofContext, ProveError> {
        let mut ctx = self.fresh_context(&self.template_ctx.maude);
        self.install_source_provider(&mut ctx, kind);
        ctx.ensure_saturated()?;
        Ok(ctx)
    }

    /// Compute the `--precompute-only` stats (HS `prettyPrecomputation`,
    /// ClosedTheory.hs). Materialises the same session cache entries
    /// later proof requests use, avoiding a separate saturation/refinement.
    pub fn precomputation_stats(&self) -> Result<PrecomputationStats, ProveError> {
        let rules = self.template_ctx.protocol_rule_count();

        let SourceStats { raw, refined } = self.source_stats();
        let raw = raw?;
        let refined = refined?;

        Ok(PrecomputationStats {
            rules,
            raw_cases: raw.cases,
            raw_chains: raw.chains,
            refined_cases: refined.cases,
            refined_chains: refined.chains,
            has_restrictions: !self.template_ctx.safety_restrictions.is_empty()
                || !self.template_ctx.other_restrictions.is_empty(),
        })
    }

    /// Materialise both source-cache slots and count them in place. The
    /// result preserves a usable raw count when refined assumption conversion
    /// fails, matching the two independent links in the web overview.
    pub fn source_stats(&self) -> SourceStats {
        fn count(sources: &SharedSources) -> SourceCaseStats {
            use crate::constraint::solver::sources::unsolved_chain_constraints;

            let chains = sources
                .iter()
                .map(|source| {
                    source
                        .cases()
                        .expect("materialised source")
                        .iter()
                        .map(|(_, system)| unsolved_chain_constraints(system))
                        .sum::<usize>()
                })
                .sum();
            SourceCaseStats {
                cases: sources.len(),
                chains,
            }
        }

        let session = self.source_session();
        let count_kind = |kind| {
            session
                .sources(kind, &self.template_ctx.maude)
                .map(|s| count(&s))
        };
        SourceStats {
            raw: count_kind(SourceKind::RawSources),
            refined: count_kind(SourceKind::RefinedSources),
        }
    }

    /// Build the shared per-file state: guarded restrictions and lemmas,
    /// resolved heuristics (the CLI heuristic overrides every lemma's, HS
    /// `selectHeuristic`) and the template `ProofContext` with its intruder
    /// rules and rule variants. `ndc_cache` reuses the theory's NDC-checked
    /// intruder rules.
    pub fn build(
        theory: &crate::closed_theory::ClosedTheory,
        maude: tamarin_term::maude_proc::MaudeHandle,
        options: ProverSessionOptions,
    ) -> Result<Self, ProveError> {
        let theory = theory.clone();
        let ProverSessionOptions {
            maude_pool,
            cli_heuristic,
            cut,
            ndc_cache,
            parameters,
            sys_retention,
            show_saturation_steps,
        } = options;
        validate_cli_heuristic(&cli_heuristic, &theory.tactic)
            .map_err(ProveError::InvalidHeuristic)?;
        let resolved_cli = resolve_cli_heuristic(&cli_heuristic, &theory.in_file, &theory.tactic);
        let prepared_lemmas: std::sync::Arc<[_]> = theory
            .lemmas()
            .map(|lemma| PreparedLemma {
                guarded: guarded_or_error(&lemma.formula).map(std::sync::Arc::new),
                heuristic: resolve_heuristic(
                    resolved_cli.as_deref(),
                    lemma,
                    &theory.heuristic,
                    &theory.tactic,
                    &theory.in_file,
                    theory.heuristic_in_file.as_deref(),
                ),
            })
            .collect();
        let source_assumptions =
            std::sync::Arc::new(gather_typing_assumptions(&theory, &prepared_lemmas));
        // HS `mkSystem` maps `formulaToGuarded_ = either (error . render) id`
        // (CloseRule.hs, Guarded.hs) over restriction formulas — it
        // ABORTS on a non-guardable restriction rather than silently dropping
        // it (which would weaken the constraint set and could let an unsound
        // proof through).  Mirror the fail-loud behaviour: propagate a
        // `ProveError::Guarded` instead of skipping.
        let mut restrictions: Vec<Guarded> = Vec::new();
        for r in theory.restrictions() {
            restrictions.push(guarded_or_error(&r.formula)?);
        }
        let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
        // HS `setforcedInjectiveFacts {L_PureState, L_CellLocked}`
        // (lib/sapic/src/Sapic.hs): when the state-channel optimisation is
        // on, those two facts are forced
        // injective for the WHOLE proof (`closeRuleCache`, CloseRule.hs).
        let forced_injective_facts: Vec<crate::fact::FactTag> =
            if theory.options.state_channel_opt() {
                crate::tools::injective_fact_instances::pure_state_forced_fact_tags()
            } else {
                Vec::new()
            };
        // HS closes the theory once and each proof seeds its fresh supply
        // from `avoid sys`; restore the counter so the template build does
        // not shift any lemma's numbering.
        let setup_counter_before = maude.fresh_counter_peek();
        let template_ctx = ProofContext::try_with_options(
            maude.clone(),
            rules,
            crate::constraint::solver::context::ProofContextOptions {
                maude_pool,
                macros: theory.macros().cloned().collect(),
                restrictions,
                forced_injective_facts,
                intruder_rules: ndc_cache,
                parameters,
                sys_retention,
                show_saturation_steps,
                loop_breakers_prepared: true,
            },
        )?;
        maude.reset_counter_to(setup_counter_before);
        Ok(ProverSession {
            theory,
            prepared_lemmas,
            source_assumptions,
            cut,
            template_ctx: std::sync::Arc::new(template_ctx),
            setup_counter_before,
            source_cache: SourceCache::default(),
            source_cache_disabled: tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE"),
        })
    }

    /// Batch search and interactive replay use the same per-lemma context.
    /// Each lemma has its own fresh counter on the assigned Maude process.
    /// The session supplies raw or refined sources on demand.
    fn setup_per_lemma_ctx(
        &self,
        lemma: &crate::theory::Lemma,
        prepared: &PreparedLemma,
        maude: &MaudeHandle,
    ) -> ProofContext {
        let source_kind = lemma.source_kind();
        let mut ctx = self.fresh_context(maude);
        ctx.use_induction = induction_hint(lemma);
        ctx.is_exists_trace = matches!(
            lemma.trace_quantifier,
            crate::theory::TraceQuantifier::ExistsTrace,
        );
        // HS `apCut` is theory-global (one `TheoryLoadOptions.stopOnTrace`),
        // so stamp the session's cut onto every per-lemma context.
        ctx.cut = self.cut;
        let session_in_file = self.theory.in_file.as_str();
        ctx.heuristic = prepared.heuristic.clone();
        ctx.lemma_name = lemma.name.clone();
        ctx.theory_file = session_in_file.to_string();
        self.install_source_provider(&mut ctx, source_kind);
        ctx
    }

    fn fresh_context(&self, maude: &MaudeHandle) -> ProofContext {
        let mut ctx = (*self.template_ctx).clone();
        ctx.maude = maude.with_fresh_counter_from(0);
        ctx.maude
            .ensure_above(self.setup_counter_before.saturating_sub(1));
        ctx
    }

    fn install_source_provider(&self, ctx: &mut ProofContext, kind: SourceKind) {
        ctx.set_source_provider(std::sync::Arc::new(SessionSourceProvider {
            kind,
            session: self.source_session(),
        }));
    }

    fn source_session(&self) -> Self {
        let mut session = self.clone();
        if self.source_cache_disabled {
            session.source_cache = SourceCache::default();
        }
        session
    }

    fn sources(&self, kind: SourceKind, maude: &MaudeHandle) -> Result<SharedSources, ProveError> {
        self.source_cache.slot(kind).get_or_build(|| {
            let maude = maude.clone();
            let session = self.clone();
            move || {
                let mut ctx = session.fresh_context(&maude);
                if kind == SourceKind::RawSources {
                    return ctx.build_raw_sources();
                }
                let assumptions = session.source_assumptions.as_ref().clone()?;
                let raw = session.sources(SourceKind::RawSources, &ctx.maude)?;
                ctx.use_materialized_sources(raw);
                crate::constraint::solver::sources::refine_with_source_asms(
                    ctx.full_sources.to_vec(),
                    &assumptions,
                    &ctx,
                )
                .map(Arc::new)
            }
        })
    }
}

/// Prove a lemma using the session's prepared formula, earlier reusable
/// lemmas and selected ranking. Proof search forces its source set on demand.
pub fn prove_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(
        session,
        session.lemma_and_prepared(lemma_name)?,
        proof_bound,
        true,
        &session.template_ctx.maude,
    )
}

/// Replay a non-target lemma's stored skeleton WITHOUT auto-proving its
/// open leaves — HS's close-time `checkAndExtendProver (sorryProver
/// Nothing)` (CloseRule.hs).  Used for lemmas the `--prove`
/// selector does not target: HS retains their close-time-replayed proof
/// verbatim (`proveLemma`'s `| otherwise = lem`, CloseRule.hs) and
/// reports the stored status.  Returns
/// the lemma's own start system + a `Sorry` placeholder when no stored
/// skeleton exists (HS keeps the parsed `unproven ()` skeleton, which is
/// a single `sorry`).
pub fn check_and_extend_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(
        session,
        session.lemma_and_prepared(lemma_name)?,
        proof_bound,
        false,
        &session.template_ctx.maude,
    )
}

/// Prove a focused system with request-local search policy.
pub fn prove_system_in_session_with_options(
    session: &ProverSession,
    lemma_name: &str,
    sys: crate::constraint::system::System,
    options: SearchOptions,
) -> Result<ProofNode, ProveError> {
    let mut ctx = session.context_for_lemma(lemma_name)?;
    ctx.cut = options.cut;
    if options.oracle_only
        && let Some(rankings) = &mut ctx.heuristic
    {
        set_quit_on_empty(rankings);
    }
    run_proof_search_at_depth(&ctx, sys, options.proof_bound, options.ranking_depth_offset)
}

fn prove_lemma_in_session_mode(
    session: &ProverSession,
    lemma: (&crate::theory::Lemma, &PreparedLemma),
    proof_bound: usize,
    auto_prove: bool,
    maude: &MaudeHandle,
) -> Result<ProofNode, ProveError> {
    let (ctx, sys) = lemma_context_and_system(session, lemma, maude)?;
    let (lemma, _) = lemma;

    // Replay the stored skeleton before proving open leaves.
    if let Some(tree) = &lemma.proof {
        if auto_prove {
            return crate::replay::replace_sorry_prove(&ctx, sys, tree, proof_bound);
        } else {
            // Non-target lemma: HS close-time check-and-extend
            // replay, no auto-proving of open leaves.
            return crate::replay::check_and_extend(&ctx, sys, tree, proof_bound);
        }
    }
    if !auto_prove {
        // Non-target lemma with no stored skeleton: HS keeps the parsed
        // `unproven ()` single-`sorry` proof (`unproven = sorry Nothing`,
        // Theory/Proof.hs; used by the lemma constructor at
        // ProofSkeleton.hs) — an
        // annotated Sorry at the lemma's start system (the node carries
        // the start system, so it renders as plain `by sorry`).
        return Ok(crate::replay::sorry_node(None, sys, []));
    }
    run_proof_search_at_depth(&ctx, sys, proof_bound, 0)
}

/// Replay an interactive proof skeleton against a freshly constructed lemma
/// system. Used when editing a theory invalidates the systems stored on a live
/// tree but its user-visible proof steps should be retained and rechecked.
pub fn check_and_extend_proof_in_session(
    session: &ProverSession,
    lemma_name: &str,
    proof: &crate::theory::ProofTree,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    let (ctx, sys) = lemma_context_and_system(
        session,
        session.lemma_and_prepared(lemma_name)?,
        &session.template_ctx.maude,
    )?;
    crate::replay::check_and_extend(&ctx, sys, proof, proof_bound)
}

fn lemma_context_and_system(
    session: &ProverSession,
    (lemma, prepared): (&crate::theory::Lemma, &PreparedLemma),
    maude: &MaudeHandle,
) -> Result<(ProofContext, crate::constraint::system::System), ProveError> {
    let theory = &session.theory;
    let g = prepared.guarded.clone()?;

    let reuse_lemmas = gather_reusable_lemmas(theory, &session.prepared_lemmas, lemma)?;

    let mut sys = crate::constraint::system::formula_to_system_partitioned(
        &session.template_ctx.safety_restrictions,
        &session.template_ctx.other_restrictions,
        lemma.source_kind(),
        lemma.trace_quantifier,
        &g,
    );
    sys.insert_lemmas(reuse_lemmas);

    // A non-target lemma without a stored proof needs only its initial system.
    // Replay and proof search force sources when a proof method reads them,
    // so a run that proves nothing (`--prove=<no match>`) never builds them.
    let ctx = session.setup_per_lemma_ctx(lemma, prepared, maude);
    Ok((ctx, sys))
}

/// Drive a proof attempt for one lemma in an elaborated theory.
///
/// `proof_bound` is `--bound=N`'s proof-depth bound (HS `apBound`,
/// applied as `boundProofDepth` in `runAutoProver`,
/// Theory/Proof.hs via Theory/Proof.hs#runAutoProver):
/// nodes at that depth become
/// `sorry /* bound N hit */` leaves.  Pass `usize::MAX` for unbounded
/// (HS `Nothing`, the default).
pub fn prove_lemma(
    theory: std::sync::Arc<crate::theory::Theory>,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;
    // Reject cheap per-lemma errors before constructing the Maude-backed
    // prover session.
    guarded_or_error(&lemma.formula)?;

    let (theory, _report) =
        crate::closed_theory::close_theory(std::sync::Arc::unwrap_or_clone(theory), &maude, None)?;
    let session = ProverSession::build(&theory, maude, ProverSessionOptions::default())?;
    prove_lemma_in_session(&session, lemma_name, proof_bound)
}

#[cfg(test)]
#[path = "prove_tests.rs"]
mod tests;
