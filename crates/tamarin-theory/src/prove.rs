// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end `prove_lemma` entry point.
//!
//! Bridges an elaborated theory and a lemma name into the
//! proof-search driver. Mirrors the high-level shape of Haskell's
//! `Theory.Proof.proveLemma`:
//!
//! 1. Look up the lemma by name in the elaborated theory.
//! 2. Convert its formula to guarded form.
//! 3. Convert restrictions to guarded form.
//! 4. Build the initial `System` via `formula_to_system`.
//! 5. Build a `ProofContext` carrying the theory's rules.
//! 6. Drive `run_proof_search` to produce a `ProofNode` tree.
//!
//! Returns `Err` on lemma lookup, guarded conversion, or goal-ranking
//! failures.

use crate::constraint::solver::context::{IntrRuleCache, ProofContext};
use crate::constraint::solver::goals::RankingError;
use crate::constraint::solver::search::{run_proof_search_at_depth, ProofNode};
use crate::constraint::system::{formula_to_system, SourceKind};
use crate::guarded::{formula_to_guarded, Guarded};
use crate::theory::OpenProtoRule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    LemmaNotFound(String),
    Guarded(String),
    InvalidHeuristic(String),
    Ranking(RankingError),
}

impl From<RankingError> for ProveError {
    fn from(error: RankingError) -> Self {
        Self::Ranking(error)
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

/// HS `formulaToGuarded_ = either (error . render) id` (Guarded.hs:466-467):
/// the guarded formula, or the full `ppError` doc (Guarded.hs:477-479) HS dies
/// with — the error text, the quoted failing sub-formula (both
/// quantifier-level errors include `ppFormula f0`, Guarded.hs:508-514 and
/// 561-563), then "in the formula" and the quoted converted formula.
fn guarded_or_error(f: &crate::formula::LNFormula) -> Result<Guarded, ProveError> {
    formula_to_guarded(f).map_err(|e| {
        ProveError::Guarded(e.full_doc(f).render_with(
            crate::pretty_hpj::DEFAULT_LINE_LENGTH,
            crate::pretty_hpj::DEFAULT_RIBBON,
        ))
    })
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveError::LemmaNotFound(n) => write!(f, "lemma not found: {}", n),
            ProveError::Guarded(m) => write!(f, "guarded conversion: {}", m),
            ProveError::InvalidHeuristic(m) => f.write_str(m),
            ProveError::Ranking(m) => write!(f, "goal ranking: {m}"),
        }
    }
}

impl std::error::Error for ProveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ProveError::Ranking(error) => Some(error),
            ProveError::LemmaNotFound(_)
            | ProveError::Guarded(_)
            | ProveError::InvalidHeuristic(_) => None,
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
/// the oracle path exec-faithful (Theory/Text/Parser.hs:309 `workDir = takeDirectory inFile`).
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
/// (System.hs:576-577). `work_dir` is the directory attached to the oracle;
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

/// Resolve Oracle/OracleSmart rankings parsed from an in-file `heuristic:` or
/// lemma attribute against the theory directory.
///
/// Mirrors HS `oraclePath oracle = fromMaybe "." workDir </> normalise relPath`
/// (System.hs:576-577) with `workDir = takeDirectory inFile`.  Producing the
/// `"."`-for-no-dir prefix (via [`hs_take_directory`]) is what gives the
/// oracle path its leading `./` so Unix `exec` resolves it from the CWD rather
/// than doing a PATH lookup.
pub(crate) fn prepend_theory_dir_to_oracle_paths(
    rankings: &mut [crate::constraint::solver::goals::GoalRanking],
    in_file: &str,
) {
    use crate::constraint::solver::goals::GoalRanking;
    let work_dir = hs_take_directory(in_file);
    for r in rankings.iter_mut() {
        match r {
            GoalRanking::Oracle { oracle_path, .. }
            | GoalRanking::OracleSmart { oracle_path, .. } => {
                *oracle_path = resolve_oracle_path(oracle_path, Some(&work_dir));
            }
            _ => {}
        }
    }
}

/// A theory's in-file `configuration:` block as cmdargs RECORDS it — HS
/// `closeTheory`'s `argsConfigString` (TheoryLoader.hs:748-757) runs
/// `processValue` over a two-flag mode: `--stop-on-trace[=v]`
/// (`flagOpt "dfs"` — valueless records `dfs`, and no separate token is
/// ever consumed) and `--auto-sources` (`flagNone`).  Bare tokens land in
/// the positional catch-all (`flagArg (updateArg "") ""`) and are ignored.
///
/// Rejections are RECORDED here, not raised.  (In HS the block is
/// processed lazily and its errors surface at scattered forcing points;
/// the port's callers validate the record eagerly instead — the batch
/// loader checks `flag_error` in its close pipeline and reads the value
/// through `effective_cut`, and [`config_block_options`] wraps the same
/// checks for the server's per-theory load.)
#[derive(Debug, Clone, Default)]
pub struct ConfigBlock {
    /// The first cmdargs-level rejection, message exactly as HS emits it:
    /// `Unknown flag: --x`, `Unhandled argument to flag, none expected:
    /// --auto-sources=x`, `Ambiguous flag '--', could be any of: …`.
    pub flag_error: Option<String>,
    /// The recorded `--stop-on-trace` value, RAW — validation is the
    /// reader's (HS `stopOnTrace`, TheoryLoader.hs:397-405, via
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
    // Declaration order (TheoryLoader.hs:754-757) — ambiguity lists it.
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

/// HS `stopOnTrace` (TheoryLoader.hs:397-405): the value is matched
/// LOWERCASED, and an unknown one is `ArgumentError ("unknown
/// stop-on-trace method: " ++ unknown)` — raised as `error e`
/// (TheoryLoader.hs:761) only where the prover forces the field.
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

/// [`parse_config_block`] + eager validation of both recorded errors —
/// used by the web server's per-theory load (the batch loader performs
/// the same eager checks inline in run.rs).  Returns
/// `(stop_on_trace, auto_sources)`; callers merge with the CLI per HS
/// precedence — CLI `--stop-on-trace` wins when given
/// (`configStopOnTrace`), `--auto-sources` is OR-combined
/// (`configAutoSources`).
pub fn config_block_options(
    cfg: &str,
) -> Result<
    (
        Option<crate::constraint::solver::context::CutStrategy>,
        bool,
    ),
    String,
> {
    let block = parse_config_block(cfg);
    if let Some(e) = block.flag_error {
        return Err(e);
    }
    let cut = match block.stop_on_trace.as_deref() {
        Some(raw) => Some(parse_stop_on_trace(raw)?),
        None => None,
    };
    Ok((cut, block.auto_sources))
}

/// The CLI-supplied heuristic / oracle flags, carried verbatim from the
/// command line.  Mirrors the `AutoProver` fields populated by HS
/// `constructAutoProver` (TheoryLoader.hs:803-810) from `thyOpts`:
///   * `raw`         = `--heuristic` ranking string (`apDefaultHeuristic`)
///   * `oracle_name` = `--oraclename` (`Just "" -> Nothing`, TheoryLoader.hs:347-349, see line 348)
///   * `oracle_only` = `--oracle-only` (`quitOnEmptyOracle`)
///
/// `None` for any field means the flag was absent.  This whole struct is
/// `None` on `ProverSession`/the prove entry points when `--heuristic` was
/// not given, in which case the per-lemma / theory heuristic is used unchanged
/// (HS `selectHeuristic`: `apDefaultHeuristic <|> pcHeuristic`,
/// Theory/Proof.hs:705-716, see line 707).
#[derive(Debug, Clone, Default)]
pub struct CliHeuristic {
    /// `--heuristic` raw ranking string (e.g. `"O"`, `"iSs"`).  When
    /// `Some`, this OVERRIDES the per-lemma / theory `heuristic:` (HS
    /// `apDefaultHeuristic prover <|> L.get pcHeuristic ctx`,
    /// Theory/Proof.hs:705-716, see line 707).
    pub raw: Option<String>,
    /// `--oraclename` — sets the oracle relPath for EVERY oracle ranking in
    /// the CLI heuristic (HS `mapOracleRanking (maybeSetOracleRelPath
    /// oraclename)`, TheoryLoader.hs:337-344, see line 343).  `Just ""` parses to `None`.
    pub oracle_name: Option<String>,
    /// `--oracle-only` — sets `quitOnEmpty` on every oracle / tactic ranking
    /// in the selected heuristic (HS `setQuitOnEmpty`,
    /// Theory/Proof.hs:709-716).
    pub oracle_only: bool,
}

/// Resolve the CLI `--heuristic`/`--oraclename` into a `GoalRanking` list,
/// mirroring HS's CLI heuristic pipeline:
///
///   1. `filterHeuristic diff rawRankings` — parse the ranking string char
///      by char (System.hs:682-686).  RS `parse_heuristic_str_with_tactics`.
///   2. `map (mapOracleRanking (maybeSetOracleRelPath oraclename))` — set the
///      oracle relPath from `--oraclename` (TheoryLoader.hs:337-344, see line 343).
///   3. `defaultOracleNames srcThyInFileName` (TheoryLoader.hs:744-746, see line 746) — fill any
///      oracle ranking that STILL has no relPath with the default `.oracle`
///      name (theory-basename `.oracle` if it exists on disk, else `"oracle"`).
///   4. `defaultOracleNames` assigns the theory directory as the workDir when
///      filling an absent path. An explicit `--oraclename` leaves the CLI
///      ranking's workDir absent and is therefore CWD-relative.
///   5. `setQuitOnEmpty` (Theory/Proof.hs:709-716) — `--oracle-only` sets
///      `quitOnEmpty` on every oracle / tactic ranking.
fn resolve_cli_heuristic(
    cli: &CliHeuristic,
    in_file: &str,
    tactics: &[crate::tactic::Tactic],
) -> Option<Vec<crate::constraint::solver::goals::GoalRanking>> {
    use crate::constraint::solver::goals::GoalRanking;
    let raw = cli.raw.as_ref()?;
    // Step 1: parse the ranking string.  `parse_heuristic_str_with_tactics`
    // also computes the default `.oracle` name (HS `defaultOracleNames`) for
    // oracle rankings without an inline `"path"` — which covers BOTH HS step 2
    // (oraclename, applied below) and step 3 (default name).
    let mut rankings =
        crate::constraint::solver::goals::parse_heuristic_str_with_tactics(raw, in_file, tactics);
    // The CLI `--oraclename` (`Just "" -> Nothing`, TheoryLoader.hs:347-349, see line 348).
    let oraclename: Option<&str> = match cli.oracle_name.as_deref() {
        Some("") => None,
        other => other,
    };
    resolve_oracle_rankings(&mut rankings, in_file, oraclename);
    // Step 5: --oracle-only quitOnEmpty.
    for r in rankings.iter_mut() {
        match r {
            GoalRanking::Oracle { quit_on_empty, .. }
            | GoalRanking::OracleSmart { quit_on_empty, .. } => {
                if cli.oracle_only {
                    *quit_on_empty = true;
                }
            }
            // Step 5: --oracle-only also sets quitOnEmpty on tactic rankings
            // (HS `aux (InternalTacticRanking _ t) = InternalTacticRanking
            // (quitOnEmptyOracle prover) t`, Theory/Proof.hs:705-716, see line
            // 715).
            GoalRanking::Tactic { quit_on_empty, .. } if cli.oracle_only => {
                *quit_on_empty = true;
            }
            _ => {}
        }
    }
    Some(rankings)
}

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
/// accepts (`filterHeuristic`, System.hs:681-685): identifier characters
/// from `goalRankingIdentifiers` plus `{tactic}` groups whose name is
/// declared by the theory (`chosenTactic`, ProofMethod.hs:493-502; names
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

/// One theory-level cache entry of source cases — the result of a
/// `ctx.ensure_saturated()` pass, kept in the same order as `full_sources`.
///
/// Why this is safe to share across lemmas (HS computes
/// `_crcRefinedSources` ONCE per `ClosedRuleCache` — RuleItem.hs:64-69
/// for the field, `closeRuleCache` at CloseRule.hs:402-404,427 for the
/// single computation — and `proveTheory` reuses that one cache for
/// every lemma, CloseRule.hs:148-163):
///   * Every `[sources]` lemma is itself a raw-source lemma, while every
///     other lemma uses the same complete set of `[sources]` assumptions.
///     There are therefore exactly two possible computations per theory:
///     raw and refined.
///   * `ensure_saturated` restores the Maude fresh counter before returning,
///     so the raw computation and its refined derivative are safe to share
///     without changing the following proof's counter trajectory.
type CachedSources = Vec<crate::constraint::solver::sources::SourceCases>;

#[derive(Default)]
struct SourceCache {
    raw: std::sync::OnceLock<CachedSources>,
    refined: std::sync::OnceLock<Result<CachedSources, ProveError>>,
}

impl SourceCache {
    #[cfg(test)]
    fn len(&self) -> usize {
        usize::from(self.raw.get().is_some()) + usize::from(self.refined.get().is_some())
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Per-file shared prover state — the bits of work that depend only on
/// the theory, not on which lemma is being proved.  Built once via
/// [`ProverSession::build_with_heuristic`] and reused across
/// `prove_lemma_in_session` calls so each lemma in a multi-lemma `--prove`
/// run pays the heavy setup cost only ONCE.
///
/// The expensive part is `ProofContext::new` (intruder rules,
/// `close_intr_rule` Maude variants, DH/BP cached variants, per-rule
/// variant precomputation and `precompute_full_sources`) —
/// seconds per call, which HS amortises across the whole file.  Sharing the
/// template `ProofContext` recovers that. Source-consuming proofs select one
/// of the session's two cached computations: raw or refined.
pub struct ProverSession {
    /// Elaborated typed theory.  Used to look up lemmas, restrictions,
    /// rules, heuristic.  Shares the caller's allocation (`Arc`); the
    /// session never mutates it.
    theory: std::sync::Arc<crate::theory::Theory>,
    /// Fully resolved per-lemma rankings, frozen when the session is built so
    /// later filesystem changes cannot switch a loaded theory's oracle.
    lemma_heuristics:
        tamarin_utils::FastMap<String, Option<Vec<crate::constraint::solver::goals::GoalRanking>>>,
    /// Whether converting any lemma to guarded form can fail. Every lemma is
    /// checked or proved by the batch loop, even when `--prove` selects a
    /// subset, so this is a genuinely session-wide ordering constraint.
    guarded_lemmas_may_fail: bool,
    /// Whether the shared refined-source materialisation can fail.
    source_refinement_may_fail: bool,
    /// Solved-leaf extraction strategy (HS `apCut`, threaded from
    /// `--stop-on-trace`, TheoryLoader.hs:803-810, see line 809).  Theory-global (HS
    /// stores it once in `TheoryLoadOptions.stopOnTrace`), so it is set on
    /// every per-lemma `ProofContext` in [`Self::setup_per_lemma_ctx`].
    cut: crate::constraint::solver::context::CutStrategy,
    /// Guarded-form restrictions (constructed once from theory).
    restrictions: Vec<Guarded>,
    /// Template `ProofContext` carrying the expensive precompute:
    /// `rules` (with variants installed), `intruder_rules`,
    /// `full_sources` (raw, unsaturated cells), etc.
    /// Per-lemma contexts share its immutable data. Their lightweight source
    /// cells are local; materialised raw/refined case vectors are cached.
    template_ctx: std::sync::Arc<ProofContext>,
    /// Fresh-counter value BEFORE the template was built.  The template
    /// build is counter-neutral (the build's fresh allocation is undone by
    /// restoring the counter), so every lemma starts from this same base.
    /// Used as the `ensure_above` floor on the per-lemma counter clone.
    setup_counter_before: u64,
    /// Shared raw/refined source cache (see [`CachedSources`]). Each slot is
    /// populated lazily and at most once, so concurrent lemma workers wait for
    /// the same computation instead of duplicating saturation. The refined
    /// slot also memoises guarded-conversion failure.
    source_cache: std::sync::Arc<SourceCache>,
    /// Snapshot the process-wide diagnostic gate when the session is built so
    /// all contexts in one session follow the same cache policy.
    source_cache_disabled: bool,
}

#[derive(Clone)]
struct SessionSourceProvider {
    kind: SourceKind,
    theory: std::sync::Arc<crate::theory::Theory>,
    template_ctx: std::sync::Arc<ProofContext>,
    setup_counter_before: u64,
    source_cache: std::sync::Arc<SourceCache>,
    cache_disabled: bool,
    may_fail: bool,
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
        self.may_fail
    }

    fn materialize(&self, ctx: &ProofContext) -> Result<(), ProveError> {
        let local_cache;
        let cache = if self.cache_disabled {
            local_cache = SourceCache::default();
            &local_cache
        } else {
            self.source_cache.as_ref()
        };
        let cached = session_sources(
            self.kind,
            &self.theory,
            &self.template_ctx,
            self.setup_counter_before,
            cache,
        )?;
        restore_sources(ctx, cached);
        Ok(())
    }
}

/// Per-lemma source kind, mirroring HS `lemmaSourceKind`
/// (lib/theory/src/Lemma.hs:38-41):
///   lemmaSourceKind lem
///     | SourceLemma `elem` lAttributes lem = RawSource
///     | otherwise                          = RefinedSource
/// HS sets `pcSourceKind = lemmaSourceKind l` (ClosedTheory.hs:97-138, see line 116) and
/// `mkSystem` stamps it onto the initial system's `sSourceKind`
/// (CloseRule.hs:167-188, see line 175).  In RS `SourceKind`, `RawSources < RefinedSources`,
/// matching HS's `RawSource < RefinedSource` Ord (System.hs:362-365), so it
/// can be used directly as the `lemmaSourceKind lem <= kind` bound below.
pub(crate) fn lemma_source_kind(lemma: &crate::theory::Lemma) -> SourceKind {
    if lemma
        .attributes
        .iter()
        .any(|a| matches!(a, crate::theory::LemmaAttr::Sources))
    {
        SourceKind::RawSources
    } else {
        SourceKind::RefinedSources
    }
}

/// HS `inductionHint` (ClosedTheory.hs:119-121): a lemma tagged
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

/// Gather the `[reuse]` lemmas declared BEFORE `lemma_name`, mirroring HS
/// `gatherReusableLemmas $ L.get sSourceKind sys` (CloseRule.hs:179-188):
///
///   guard $ lemmaSourceKind lem <= kind
///        && ReuseLemma `elem` lAttributes lem
///        && AllTraces == lTraceQuantifier lem
///        && lName lem `notElem` pcHiddenLemmas ctxt
///        && "ALL"     `notElem` pcHiddenLemmas ctxt
///
/// `kind` is the source kind of the system being built (= the proved
/// lemma's `lemmaSourceKind`).  `pcHiddenLemmas` is populated from the
/// PROVED lemma's own `[hide_lemma=..]` attributes (ClosedTheory.hs:97-138, see line 109),
/// so the hidden set is computed here from `lemma_name`'s attributes.
/// HS uses `formulaToGuarded_` (fail-loud) on each reuse formula, so a
/// non-guardable reuse formula propagates a `ProveError` rather than being
/// silently dropped.
///
/// Both batch and interactive entry points reach this one implementation
/// through their shared [`ProverSession`].
pub(crate) fn gather_reusable_lemmas(
    theory: &crate::theory::Theory,
    lemma_name: &str,
    kind: SourceKind,
) -> Result<Vec<Guarded>, ProveError> {
    // HS `pcHiddenLemmas` = the proved lemma's `[hide_lemma=h]` names.
    let hidden: Vec<&str> = theory
        .lookup_lemma(lemma_name)
        .map(|l| {
            l.attributes
                .iter()
                .filter_map(|a| match a {
                    crate::theory::LemmaAttr::HideLemma(h) => Some(h.as_str()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    let hide_all = hidden.contains(&"ALL");
    let mut reuse_lemmas: Vec<Guarded> = Vec::new();
    for prior in theory.lemmas() {
        if prior.name == lemma_name {
            break;
        }
        if lemma_source_kind(prior) > kind {
            continue;
        }
        if !prior
            .attributes
            .iter()
            .any(|a| matches!(a, crate::theory::LemmaAttr::Reuse))
        {
            continue;
        }
        if !matches!(
            prior.trace_quantifier,
            crate::theory::TraceQuantifier::AllTraces
        ) {
            continue;
        }
        if hide_all || hidden.contains(&prior.name.as_str()) {
            continue;
        }
        reuse_lemmas.push(guarded_or_error(&prior.formula)?);
    }
    Ok(reuse_lemmas)
}

/// Gather the typing assumptions folded into the theory's refined sources.
///
/// HS-faithful per-lemma RAW-vs-REFINED selection (ClosedTheory.hs:116-118
/// `cases = case lemmaSourceKind l of RawSource -> crcRawSources;
/// RefinedSource -> crcRefinedSources`).  `[sources]` lemmas (RawSource,
/// lib/theory/src/Lemma.hs:38-41, see line 40) use the RAW precomputed
/// sources — `refineWithSourceAsms` is NEVER applied to them — so they carry NO typing assumptions (an empty
/// list makes `ensure_saturated` skip the refine and use the raw cases
/// verbatim).  All other lemmas (RefinedSource) use the refined sources
/// (`refineWithSourceAsms parameters typAsms`, CloseRule.hs:427), so they fold in
/// every prior `[sources]`-lemma assumption (HS `typAsms`, CloseRule.hs:117-119,
/// which uses `formulaToGuarded_` — fail-loud, so a non-guardable formula
/// propagates a `ProveError` rather than being silently dropped).  The proved
/// `[sources]` lemma is itself proved against raw sources, so there is no
/// per-lemma self-exclusion: every refined-source consumer uses this same set.
fn gather_typing_assumptions(
    theory: &crate::theory::Theory,
    kind: SourceKind,
) -> Result<Vec<Guarded>, ProveError> {
    let mut typing_assumptions: Vec<Guarded> = Vec::new();
    if kind >= SourceKind::RefinedSources {
        for prior in theory.lemmas() {
            if !prior
                .attributes
                .iter()
                .any(|a| matches!(a, crate::theory::LemmaAttr::Sources))
            {
                continue;
            }
            if !matches!(
                prior.trace_quantifier,
                crate::theory::TraceQuantifier::AllTraces
            ) {
                continue;
            }
            typing_assumptions.push(guarded_or_error(&prior.formula)?);
        }
    }
    Ok(typing_assumptions)
}

/// `--precompute-only` stats (HS `prettyPrecomputation`, ClosedTheory.hs:553-575):
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

/// Raw and refined source counts. Raw materialisation is infallible; guarded
/// conversion of a refined-source assumption may fail independently.
pub struct SourceStats {
    pub raw: SourceCaseStats,
    pub refined: Result<SourceCaseStats, ProveError>,
}

/// Resolve the goal-ranking heuristic for a lemma, mirroring HS
/// `selectHeuristic prover ctx = apDefaultHeuristic prover <|> L.get
/// pcHeuristic ctx` (Theory/Proof.hs:706-707): the CLI `--heuristic`
/// (`apDefaultHeuristic`) OVERRIDES the per-lemma / theory heuristic when
/// present.  Otherwise fall back to per-lemma `[heuristic=..]` > theory-level
/// `heuristic:` > None (`getProofContext.specifiedHeuristic`,
/// ClosedTheory.hs:123-131); `None` becomes `SmartRanking False` downstream.
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
    prepend_theory_dir_to_oracle_paths(&mut rankings, ranking_file);
    Some(rankings)
}

impl ProverSession {
    /// The immutable theory this session and all of its caches describe.
    pub fn theory(&self) -> &crate::theory::Theory {
        &self.theory
    }

    /// Read the theory-wide, unspecialised context built by this session.
    ///
    /// This is intended for web views which only inspect immutable
    /// close-time data. Lemma proof operations must use
    /// [`Self::context_for_lemma`].
    pub fn template_context(&self) -> &ProofContext {
        &self.template_ctx
    }

    /// Whether per-lemma setup can fail anywhere in the batch traversal.
    pub fn guarded_lemmas_may_fail(&self) -> bool {
        self.guarded_lemmas_may_fail
    }

    /// Whether this lemma's selected ranking can fail when auto-proved.
    pub fn lemma_ranking_may_fail(&self, lemma_name: &str) -> bool {
        self.lemma_heuristics
            .get(lemma_name)
            .and_then(Option::as_deref)
            .is_some_and(crate::constraint::solver::goals::rankings_may_fail)
    }

    /// Build the structural per-lemma context used by batch and web replay.
    /// Sources remain lazy until a solver operation actually needs them.
    pub fn context_for_lemma(&self, lemma_name: &str) -> Result<ProofContext, ProveError> {
        let lemma = self
            .theory
            .lookup_lemma(lemma_name)
            .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;
        let mut ctx = self.setup_per_lemma_ctx(lemma, lemma_name);
        ctx.use_induction = induction_hint(lemma);
        Ok(ctx)
    }

    /// Build a disposable source context for interactive views. Materialise
    /// through the same provider as proof search so cache bypass and deferred
    /// conversion failures have one implementation.
    pub fn context_for_sources(&self, kind: SourceKind) -> Result<ProofContext, ProveError> {
        let mut ctx = self.fresh_context();
        self.install_source_provider(&mut ctx, kind);
        ctx.ensure_saturated();
        if let Some(error) = ctx.source_error() {
            return Err(error);
        }
        Ok(ctx)
    }

    /// Compute the `--precompute-only` stats (HS `prettyPrecomputation`,
    /// ClosedTheory.hs:553-575). Materialises the same session cache entries
    /// later proof requests use, avoiding a separate saturation/refinement.
    pub fn precomputation_stats(&self) -> Result<PrecomputationStats, ProveError> {
        // HS `length (getClassifiedRules thy)._crProtocol`: the theory's
        // rule items plus the intruder members of `crProtocol` —
        // everything that is neither a construction rule (`isConstrRule`,
        // Model/Rule.hs:707-714) nor a destruction rule (`isDestrRule`,
        // Model/Rule.hs:694-698), i.e. ISend/IRecv/IRecvNC/Fresh.
        let rules = self.theory.rules().count()
            + self
                .template_ctx
                .intruder_rules
                .iter()
                .filter(|ir| {
                    !crate::rule::is_constr_rule(&ir.info) && !crate::rule::is_destr_rule(&ir.info)
                })
                .count();

        let SourceStats { raw, refined } = self.source_stats();
        let refined = refined?;

        Ok(PrecomputationStats {
            rules,
            raw_cases: raw.cases,
            raw_chains: raw.chains,
            refined_cases: refined.cases,
            refined_chains: refined.chains,
            has_restrictions: !self.restrictions.is_empty(),
        })
    }

    /// Materialise both source-cache slots and count them in place. The
    /// result preserves a usable raw count when refined assumption conversion
    /// fails, matching the two independent links in the web overview.
    pub fn source_stats(&self) -> SourceStats {
        fn count(sources: &CachedSources) -> SourceCaseStats {
            use crate::constraint::solver::sources::unsolved_chain_constraints;

            let chains = sources
                .iter()
                .map(|cases| {
                    cases
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
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

        let local_cache = SourceCache::default();
        let cache = if self.source_cache_disabled {
            &local_cache
        } else {
            self.source_cache.as_ref()
        };
        SourceStats {
            raw: count(raw_sources(
                &self.template_ctx,
                self.setup_counter_before,
                cache,
            )),
            refined: session_sources(
                SourceKind::RefinedSources,
                &self.theory,
                &self.template_ctx,
                self.setup_counter_before,
                cache,
            )
            .map(count),
        }
    }

    /// Build the shared per-file state. The theory's `in_file` resolves oracle
    /// paths (HS Theory/Text/Parser.hs). Does the expensive
    /// once-per-file work: restriction conversion and full `ProofContext`
    /// construction (which runs intruder rule generation,
    /// `close_intr_rule`, DH/BP cached variants, per-rule variant
    /// expansion, source precomputation).  Carries the CLI
    /// `--heuristic`/`--oraclename`/`--oracle-only` (HS `AutoProver`): when
    /// `cli_heuristic.raw` is `Some`, every lemma's goal ranking is the CLI
    /// heuristic (HS `selectHeuristic`: `apDefaultHeuristic <|> pcHeuristic`,
    /// Theory/Proof.hs).
    ///
    /// `ndc_cache`: the theory's once-per-load NDC-checked intruder cache
    /// (`close_rule::check_close_intr_rule`), injected into the template
    /// context so the session reuses the tagged+permuted rules instead of
    /// re-running the check.  Taken as a borrowed handle: the caller keeps
    /// the one cache and the template context shares its allocation.
    pub fn build_with_heuristic(
        theory: std::sync::Arc<crate::theory::Theory>,
        maude: tamarin_term::maude_proc::MaudeHandle,
        pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
        cli_heuristic: CliHeuristic,
        cut: crate::constraint::solver::context::CutStrategy,
        ndc_cache: Option<&IntrRuleCache>,
    ) -> Result<Self, ProveError> {
        validate_cli_heuristic(&cli_heuristic, &theory.tactic)
            .map_err(ProveError::InvalidHeuristic)?;
        let resolved_cli = resolve_cli_heuristic(&cli_heuristic, &theory.in_file, &theory.tactic);
        let lemma_heuristics: tamarin_utils::FastMap<
            String,
            Option<Vec<crate::constraint::solver::goals::GoalRanking>>,
        > = theory
            .lemmas()
            .map(|lemma| {
                (
                    lemma.name.clone(),
                    resolve_heuristic(
                        resolved_cli.as_deref(),
                        lemma,
                        &theory.heuristic,
                        &theory.tactic,
                        &theory.in_file,
                        theory.heuristic_in_file.as_deref(),
                    ),
                )
            })
            .collect();
        let mut guarded_lemmas_may_fail = false;
        let mut source_refinement_may_fail = false;
        for lemma in theory.lemmas() {
            let invalid = formula_to_guarded(&lemma.formula).is_err();
            guarded_lemmas_may_fail |= invalid;
            source_refinement_may_fail |= invalid
                && lemma
                    .attributes
                    .iter()
                    .any(|attribute| matches!(attribute, crate::theory::LemmaAttr::Sources))
                && matches!(
                    lemma.trace_quantifier,
                    crate::theory::TraceQuantifier::AllTraces
                );
        }
        // HS `mkSystem` maps `formulaToGuarded_ = either (error . render) id`
        // (CloseRule.hs:167-188, see line 174, Guarded.hs:466-467) over restriction formulas — it
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
        // (lib/sapic/src/Sapic.hs:84): when the state-channel optimisation is
        // on, those two facts are forced
        // injective for the WHOLE proof (`closeRuleCache`, CloseRule.hs:417-420).
        let forced_injective_facts: Vec<crate::fact::FactTag> =
            if theory.options.state_channel_opt() {
                crate::tools::injective_fact_instances::pure_state_forced_fact_tags()
            } else {
                Vec::new()
            };
        // HS-FAITHFUL PURITY (mirrors the source-refinement purity in
        // `ensure_saturated`): HS closes the theory ONCE and each lemma's
        // proof independently resets fresh to `avoid sys` per step
        // (ProofMethod.hs) — the theory-build's fresh allocation never
        // feeds the per-lemma proof counter.  RS's template build advances
        // the shared counter, so restore the counter to its pre-build value
        // to keep the build counter-neutral: every lemma starts from the same
        // base and template vars are re-freshened from `avoid sys` on
        // instantiation.
        let setup_counter_before = maude.fresh_counter_peek();
        let template_ctx = ProofContext::new_with_restrictions_pool_forced(
            maude.clone(),
            pool,
            rules,
            restrictions.clone(),
            &forced_injective_facts,
            ndc_cache.cloned(),
        );
        maude.reset_counter_to(setup_counter_before);
        Ok(ProverSession {
            theory,
            lemma_heuristics,
            guarded_lemmas_may_fail,
            source_refinement_may_fail,
            cut,
            restrictions,
            template_ctx: std::sync::Arc::new(template_ctx),
            setup_counter_before,
            source_cache: std::sync::Arc::new(SourceCache::default()),
            source_cache_disabled: tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE"),
        })
    }

    /// Build the per-lemma `ProofContext` shared verbatim by both session
    /// entry points (`prove_lemma_in_session_mode` and
    /// `prove_system_in_session`): clone the template ctx, give it its own
    /// fresh-counter floored at the shared `setup_counter_before` base (B1
    /// lemma-level parallelism), then stamp `is_exists_trace` / `heuristic`
    /// / `lemma_name` / `theory_file`. Source conversion remains deferred
    /// behind the session provider.
    fn setup_per_lemma_ctx(&self, lemma: &crate::theory::Lemma, lemma_name: &str) -> ProofContext {
        let source_kind = lemma_source_kind(lemma);
        let mut ctx = self.fresh_context();
        ctx.is_exists_trace = matches!(
            lemma.trace_quantifier,
            crate::theory::TraceQuantifier::ExistsTrace,
        );
        // HS `apCut` is theory-global (one `TheoryLoadOptions.stopOnTrace`),
        // so stamp the session's cut onto every per-lemma context.
        ctx.cut = self.cut;
        let session_in_file = self.theory.in_file.as_str();
        ctx.heuristic = self.lemma_heuristics.get(lemma_name).cloned().flatten();
        ctx.lemma_name = lemma_name.to_string();
        ctx.theory_file = session_in_file.to_string();
        self.install_source_provider(&mut ctx, source_kind);
        ctx
    }

    fn fresh_context(&self) -> ProofContext {
        let sources = std::sync::Arc::new(
            self.template_ctx
                .full_sources
                .iter()
                .map(|source| crate::constraint::solver::sources::Source::lazy(source.goal.clone()))
                .collect(),
        );
        let mut ctx = self.template_ctx.fresh_with_sources(sources);
        ctx.maude = ctx.maude.with_fresh_counter_from(0);
        ctx.maude
            .ensure_above(self.setup_counter_before.saturating_sub(1));
        ctx
    }

    fn install_source_provider(&self, ctx: &mut ProofContext, kind: SourceKind) {
        ctx.set_source_provider(std::sync::Arc::new(SessionSourceProvider {
            kind,
            theory: std::sync::Arc::clone(&self.theory),
            template_ctx: std::sync::Arc::clone(&self.template_ctx),
            setup_counter_before: self.setup_counter_before,
            source_cache: std::sync::Arc::clone(&self.source_cache),
            cache_disabled: self.source_cache_disabled,
            may_fail: kind >= SourceKind::RefinedSources && self.source_refinement_may_fail,
        }));
    }
}

fn fresh_source_context(template: &ProofContext, setup_counter_before: u64) -> ProofContext {
    let mut ctx = template.clone();
    ctx.maude = ctx.maude.with_fresh_counter_from(0);
    ctx.maude
        .ensure_above(setup_counter_before.saturating_sub(1));
    ctx
}

fn raw_sources<'a>(
    template: &ProofContext,
    setup_counter_before: u64,
    cache: &'a SourceCache,
) -> &'a CachedSources {
    cache.raw.get_or_init(|| {
        let raw_ctx = fresh_source_context(template, setup_counter_before);
        raw_ctx.ensure_saturated();
        snapshot_sources(&raw_ctx.full_sources)
    })
}

fn session_sources<'a>(
    kind: SourceKind,
    theory: &crate::theory::Theory,
    template: &ProofContext,
    setup_counter_before: u64,
    cache: &'a SourceCache,
) -> Result<&'a CachedSources, ProveError> {
    if kind == SourceKind::RawSources {
        return Ok(raw_sources(template, setup_counter_before, cache));
    }
    cache
        .refined
        .get_or_init(|| {
            let assumptions = gather_typing_assumptions(theory, SourceKind::RefinedSources)?;
            let refinement_ctx = fresh_source_context(template, setup_counter_before);
            restore_sources(
                &refinement_ctx,
                raw_sources(template, setup_counter_before, cache),
            );
            // This internal refinement starts from a fully restored raw snapshot;
            // no outer saturation run owns its gate.
            refinement_ctx.mark_saturated_done();
            let refined = crate::constraint::solver::sources::refine_with_source_asms(
                refinement_ctx.full_sources.to_vec(),
                &assumptions,
                &refinement_ctx,
            );
            Ok(snapshot_sources(&refined))
        })
        .as_ref()
        .map_err(Clone::clone)
}

fn snapshot_sources(sources: &[crate::constraint::solver::sources::Source]) -> CachedSources {
    sources
        .iter()
        .map(|source| {
            source
                .cases_cell
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .clone()
                .expect("saturated source must have a materialised case list")
        })
        .collect()
}

fn restore_sources(ctx: &ProofContext, cached: &CachedSources) {
    assert_eq!(
        ctx.full_sources.len(),
        cached.len(),
        "cached source list must match the context template"
    );
    for (source, cases) in ctx.full_sources.iter().zip(cached) {
        source.cases_set_shared(std::sync::Arc::clone(cases));
    }
}

/// Prove a single lemma using a pre-built `ProverSession`.  Skips the
/// expensive theory-level setup (which `ProverSession::build_with_heuristic`
/// did) and runs only the per-lemma work: guarded conversion of lemma+reuse
/// formulas, `formula_to_system`, ProofContext clone +
/// per-lemma-field setup, `ensure_saturated` (typing-asm refinement),
/// and proof-tree search.
pub fn prove_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(session, lemma_name, proof_bound, true)
}

/// Replay a non-target lemma's stored skeleton WITHOUT auto-proving its
/// open leaves — HS's close-time `checkAndExtendProver (sorryProver
/// Nothing)` (CloseRule.hs:71).  Used for lemmas the `--prove`
/// selector does not target: HS retains their close-time-replayed proof
/// verbatim (`proveLemma`'s `| otherwise = lem`, CloseRule.hs:157-159) and
/// reports the stored status.  Returns
/// the lemma's own start system + a `Sorry` placeholder when no stored
/// skeleton exists (HS keeps the parsed `unproven ()` skeleton, which is
/// a single `sorry`).
pub fn check_and_extend_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(session, lemma_name, proof_bound, false)
}

/// Run the from-scratch autoprover on an ARBITRARY start system under
/// `lemma_name`'s per-lemma `ProofContext` — the web interactive
/// `autoprove` primitive.
///
/// HS `getProverR` → `applyProverAtPath` (`src/Web/Theory.hs:146-149`) →
/// `focus proofPath (runAutoProver ap)` (`lib/theory/src/Theory/Proof.hs:601-610`)
/// runs the prover from the subproof's system at the URL's proof path,
/// under the per-lemma context `modifyLemmaProof` supplies
/// (`getProofContext l thy`, ClosedTheory.hs — `pcSources` picked raw vs
/// refined by `lemmaSourceKind`, `pcUseInduction`, `pcHeuristic`,
/// typing-assumption-refined source cases).  This builds that context
/// EXACTLY as [`prove_lemma_in_session`] does — same template clone, same
/// counter base, same lazy refined-source cache, same saturation +
/// source-cache participation — then drives `run_proof_search` from the
/// caller's `sys` instead of the lemma's initial system.
///
/// Deliberately NO skeleton replay: web `runAutoProver` "ignores the
/// existing proof and tries to find one by itself" (Theory/Proof.hs:741-745)
/// — it is not wrapped in `replaceSorryProver` (batch-`--prove`-only,
/// Main/TheoryLoader.hs:705-707, see line 706).
pub fn prove_system_in_session(
    session: &ProverSession,
    lemma_name: &str,
    sys: crate::constraint::system::System,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    prove_system_in_session_with_options(
        session,
        lemma_name,
        sys,
        SearchOptions {
            proof_bound,
            ranking_depth_offset: 0,
            cut: session.cut,
            oracle_only: false,
        },
    )
}

/// Prove a focused system with request-local search policy.
pub fn prove_system_in_session_with_options(
    session: &ProverSession,
    lemma_name: &str,
    sys: crate::constraint::system::System,
    options: SearchOptions,
) -> Result<ProofNode, ProveError> {
    use crate::constraint::solver::goals::GoalRanking;

    let mut ctx = session.context_for_lemma(lemma_name)?;
    ctx.cut = options.cut;
    if options.oracle_only {
        if let Some(rankings) = &mut ctx.heuristic {
            for ranking in rankings {
                match ranking {
                    GoalRanking::Oracle { quit_on_empty, .. }
                    | GoalRanking::OracleSmart { quit_on_empty, .. }
                    | GoalRanking::Tactic { quit_on_empty, .. } => *quit_on_empty = true,
                    _ => {}
                }
            }
        }
    }
    run_proof_search_at_depth(&ctx, sys, options.proof_bound, options.ranking_depth_offset)
}

fn prove_lemma_in_session_mode(
    session: &ProverSession,
    lemma_name: &str,
    proof_bound: usize,
    auto_prove: bool,
) -> Result<ProofNode, ProveError> {
    let theory = &session.theory;
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;

    let g = guarded_or_error(&lemma.formula)?;

    // Per-lemma source kind, mirroring HS `lemmaSourceKind`
    // (lib/theory/src/Lemma.hs:38-41):
    // `[sources]`-tagged lemmas get RawSource, all others RefinedSource.
    // HS sets `pcSourceKind = lemmaSourceKind l` (ClosedTheory.hs:97-138, see line 102,116)
    // and `formulaToSystem` stamps it onto the initial system's
    // `sSourceKind` (CloseRule.hs:167-188, see line 175).
    let lemma_source_kind = lemma_source_kind(lemma);

    // `[reuse]` lemmas declared BEFORE this one.  Same gather logic as
    // the one-shot and shared-session entry points.
    let reuse_lemmas = gather_reusable_lemmas(theory, lemma_name, lemma_source_kind)?;

    let mut sys = formula_to_system(
        session.restrictions.clone(),
        lemma_source_kind,
        lemma.trace_quantifier,
        &g,
    );
    sys.insert_lemmas(reuse_lemmas);

    // Per-lemma ProofContext: clone the template (built once at session
    // construction with raw, unsaturated `full_sources` — each source's
    // `cases_cell = None`), give it its OWN fresh-counter Arc floored at the
    // shared `setup_counter_before` base (B1 lemma-level parallelism: still
    // sharing the template's Maude subprocess, but concurrently proving
    // lemmas must not race on a shared counter), and stamp the per-lemma
    // fields. See `setup_per_lemma_ctx`. Source cases are restored from the
    // session's immutable raw/refined slots when a proof actually needs them.
    let mut ctx = session.setup_per_lemma_ctx(lemma, lemma_name);
    // HS-faithful laziness: refined sources are a lazy `where`-bound thunk
    // in HS's `ClosedRuleCache` (`refinedSources` = `precomputeSources` →
    // `refineWithSourceAsms`, CloseRule.hs:426-427), forced ONLY when a proof
    // method reads `pcSources` (ProofMethod.hs:283-340, see line 316).  A non-target lemma
    // with NO stored skeleton replays HS's parsed `unproven () = sorry`
    // (`unproven = sorry Nothing`, Theory/Proof.hs:255-256; used by the lemma
    // constructor at ProofSkeleton.hs:59-61, see line 61) via `checkAndExtendProver`'s
    // `sorry` walk
    // (Theory/Proof.hs:623-630) — that single `Sorry` node consults no source,
    // so HS never forces the (potentially very expensive) refined-source
    // thunk for it.  RS mirrors that here: such a lemma will hit the
    // `annotated_sorry_root` early return below WITHOUT touching
    // `cases(ctx)`, so we must NOT eagerly run `ensure_saturated` for it.
    // (Eagerly saturating every lemma — even bare-sorry ones — made
    // `--prove=__nomatch__`-style runs over a multiset theory spend the
    // full per-lemma source-saturation budget × #lemmas while HS returned
    // in moments; e.g. spdm121 `--prove=<no match>` was ~61s vs HS 0.7s.
    // The `cases(ctx)` accessor (sources.rs) still calls `ensure_saturated`
    // lazily for every path that DOES consult a source — skeleton replay
    // and `run_proof_search` — so correctness is unchanged.)
    ctx.use_induction = induction_hint(lemma);
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
        // Theory/Proof.hs:255-256; used by the lemma constructor at
        // ProofSkeleton.hs:59-61, see line 61) — an
        // annotated Sorry at the lemma's start system (the node carries
        // the start system, so it renders as plain `by sorry`).
        return Ok(crate::replay::annotated_sorry_root(sys));
    }
    run_proof_search_at_depth(&ctx, sys, proof_bound, 0)
}

/// Drive a proof attempt for one lemma in an elaborated theory.
///
/// `proof_bound` is `--bound=N`'s proof-depth bound (HS `apBound`,
/// applied as `boundProofDepth` in `runAutoProver`,
/// Theory/Proof.hs:336-344 via Theory/Proof.hs:730-750#runAutoProver):
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

    let session = ProverSession::build_with_heuristic(
        theory,
        maude,
        None,
        CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    )?;
    prove_lemma_in_session(&session, lemma_name, proof_bound)
}

#[cfg(test)]
#[path = "prove_tests.rs"]
mod tests;
