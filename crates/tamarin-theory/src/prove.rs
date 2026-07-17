// Currently GPL 3.0 until granted permission by the following authors:
//   Jannik Dreier, Simon Meier, Hong-Thai Luu, Artur Cygan, Robert
//   Künnemann, Kevin Morio, Felix Linker, "Pops" (github racoucho1u),
//   Benedikt Schmidt, Ralf Sasse, Philip Lukert, Charlie Jacomme, Yavor
//   Ivanov, "Jackie" (github kanakanajm), "Tom" (github BTom-GH), Adrian
//   Dapprich, Cas Cremers, symphorien, "gilcu3" (github), "ValentinYuri"
//   (github), Yann Colomb, Felix Yan, Mathias Aurand, "Nynko" (github),
//   Katriel Cohn-Gordon, Alexander Dax, Nick Moore, Jérôme (github Azurios-
//   git), Dominik Schoop, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Maude/Parser.hs, lib/theory/src/ClosedTheory.hs,
//   lib/theory/src/Items/RuleItem.hs, lib/theory/src/Lemma.hs,
//   lib/theory/src/Prover.hs, lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Model/Rule.hs, lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/ProofSkeleton.hs, lib/theory/src/Theory/Sapic.hs,
//   lib/theory/src/Theory/Text/Parser.hs, src/Main/TheoryLoader.hs,
//   src/Web/Theory.hs

//! End-to-end `prove_lemma` entry point.
//!
//! Bridges a parsed `.spthy` theory and a lemma name into the
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
//! Returns `Err` on parser/elaboration/guarded-conversion failures.

use tamarin_parser::ast as p;

use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::search::{run_proof_search, ProofNode};
use crate::constraint::system::{formula_to_system, SourceKind};
use crate::elaborate::elaborate;
use crate::guarded::{formula_to_guarded, Guarded};
use crate::theory::OpenProtoRule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    LemmaNotFound(String),
    Elaboration(String),
    Guarded(String),
}

/// Render the full HS `ppError` doc (Guarded.hs:477) for a failed guarded
/// conversion: the error text, the quoted failing sub-formula (both
/// quantifier-level errors include `ppFormula f0`, Guarded.hs:508-514 and
/// 561-563), then "in the formula" + the quoted converted formula.  This is
/// the exact message HS's `formulaToGuarded_ = either (error . render) id`
/// (Guarded.hs:464-465) dies with when a proven lemma's formula cannot be
/// converted.
fn guard_error_doc(
    e: &crate::guarded::GuardError,
    formula: &tamarin_parser::ast::Formula,
) -> String {
    let full = crate::pretty_formula::pretty_formula(formula);
    let sub = e.subject_formula.as_ref()
        .map(crate::pretty_formula::pretty_formula)
        .unwrap_or_else(|| full.clone());
    format!("{}\n  \"{}\"\nin the formula\n  \"{}\"", e.message, sub, full)
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveError::LemmaNotFound(n) => write!(f, "lemma not found: {}", n),
            ProveError::Elaboration(m) => write!(f, "elaboration: {}", m),
            ProveError::Guarded(m) => write!(f, "guarded conversion: {}", m),
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
/// the oracle path exec-faithful (Parser.hs:304 `workDir = takeDirectory inFile`).
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
/// (System.hs:574-575).  `work_dir` is `Some(dir)` for the in-file heuristic
/// (= `takeDirectory inFile`, Parser.hs:304) or `None` for the CLI
/// heuristic (HS `defaultOracle = Oracle Nothing Nothing` ⇒ `fromMaybe "."`).
/// The relPath is normalised BEFORE the join (`normalise "./oracle-x"` =
/// `"oracle-x"`), so a `heuristic: o "./oracle-x"` under a real theory dir
/// yields `<dir>/oracle-x` — the web sequent pane prints this path verbatim
/// ("Goals sorted according to an oracle … located at <path>").  The
/// leading `./` of a CWD-relative result comes from the join with workDir
/// `"."`, exactly as in HS.
fn resolve_oracle_path(oracle_path: &str, work_dir: Option<&str>) -> String {
    let p = std::path::Path::new(oracle_path);
    if p.is_absolute() {
        return oracle_path.to_string();
    }
    let wd = work_dir.unwrap_or(".");
    hs_combine(wd, &hs_normalise_relative(oracle_path))
}

/// HS `System.FilePath.normalise` restricted to the relative-path case the
/// caller guards (absolute paths return early): drop `.` segments and
/// redundant separators.  (`..` is NOT collapsed, as in HS.)
fn hs_normalise_relative(p: &str) -> String {
    let segs: Vec<&str> = p
        .split('/')
        .filter(|s| !s.is_empty() && *s != ".")
        .collect();
    if segs.is_empty() {
        ".".to_string()
    } else {
        segs.join("/")
    }
}

/// Prepend the theory file's directory to any Oracle/OracleSmart rankings
/// whose path is not already absolute.  Used for the IN-FILE `heuristic:`
/// block whose oracle workDir is `takeDirectory inFile` (Parser.hs:304).
///
/// Mirrors HS `oraclePath oracle = fromMaybe "." workDir </> normalise relPath`
/// (System.hs:574-575) with `workDir = takeDirectory inFile`.  Producing the
/// `"."`-for-no-dir prefix (via [`hs_take_directory`]) is what gives the
/// oracle path its leading `./` so Unix `exec` resolves it from the CWD rather
/// than doing a PATH lookup.
pub fn prepend_theory_dir_to_oracle_paths(
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

/// Parse a theory's in-file `configuration:` block — HS `closeTheory`'s
/// `theoryConfFlags` (TheoryLoader.hs:640-666).  Exactly two flags are
/// accepted: `--stop-on-trace[=v]` (`flagOpt "dfs"` — valueless means
/// `dfs`; value matched case-insensitively per HS `stopOnTrace`,
/// TheoryLoader.hs:355-362) and `--auto-sources` (`flagNone`).  Bare
/// (non-flag) tokens land in cmdargs' positional catch-all
/// (`flagArg (updateArg "") ""`) and are ignored; an unknown flag or
/// stop-on-trace value is an error (cmdargs `processValue` / HS
/// `error e` on `ArgumentError`, TheoryLoader.hs:661).
///
/// Returns `(stop_on_trace, auto_sources)`; callers merge with the CLI
/// per HS precedence — CLI `--stop-on-trace` wins when given
/// (`configStopOnTrace`), `--auto-sources` is OR-combined
/// (`configAutoSources`).
pub fn config_block_options(
    cfg: &str,
) -> Result<(Option<crate::constraint::solver::context::CutStrategy>, bool), String> {
    use crate::constraint::solver::context::CutStrategy;
    let mut stop_on_trace: Option<CutStrategy> = None;
    let mut auto_sources = false;
    for tok in cfg.split_whitespace() {
        if tok == "--auto-sources" {
            auto_sources = true;
        } else if let Some(rest) = tok.strip_prefix("--stop-on-trace") {
            let value = if let Some(v) = rest.strip_prefix('=') {
                v
            } else if rest.is_empty() {
                "dfs"
            } else {
                return Err(format!("configuration block: unknown flag: {}", tok));
            };
            stop_on_trace = Some(match value.to_ascii_lowercase().as_str() {
                "dfs" => CutStrategy::Dfs,
                "bfs" => CutStrategy::Bfs,
                "seqdfs" => CutStrategy::SeqDfs,
                "sorry" => CutStrategy::AfterSorry,
                "none" => CutStrategy::Nothing,
                other => return Err(format!(
                    "unknown stop-on-trace method: {}", other)),
            });
        } else if tok.starts_with("--") {
            return Err(format!("configuration block: unknown flag: {}", tok));
        }
        // Bare token: cmdargs positional catch-all — ignored.
    }
    Ok((stop_on_trace, auto_sources))
}

/// The CLI-supplied heuristic / oracle flags, carried verbatim from the
/// command line.  Mirrors the `AutoProver` fields populated by HS
/// `constructAutoProver` (TheoryLoader.hs:702-706) from `thyOpts`:
///   * `raw`         = `--heuristic` ranking string (`apDefaultHeuristic`)
///   * `oracle_name` = `--oraclename` (`Just "" -> Nothing`, TheoryLoader.hs:310)
///   * `oracle_only` = `--oracle-only` (`quitOnEmptyOracle`)
///
/// `None` for any field means the flag was absent.  This whole struct is
/// `None` on `ProverSession`/the prove entry points when `--heuristic` was
/// not given, in which case the per-lemma / theory heuristic is used unchanged
/// (HS `selectHeuristic`: `apDefaultHeuristic <|> pcHeuristic`, Proof.hs:707).
#[derive(Debug, Clone, Default)]
pub struct CliHeuristic {
    /// `--heuristic` raw ranking string (e.g. `"O"`, `"s1Ss"`).  When
    /// `Some`, this OVERRIDES the per-lemma / theory `heuristic:` (HS
    /// `apDefaultHeuristic prover <|> L.get pcHeuristic ctx`, Proof.hs:708).
    pub raw: Option<String>,
    /// `--oraclename` — sets the oracle relPath for EVERY oracle ranking in
    /// the CLI heuristic (HS `mapOracleRanking (maybeSetOracleRelPath
    /// oraclename)`, TheoryLoader.hs:305).  `Just ""` parses to `None`.
    pub oracle_name: Option<String>,
    /// `--oracle-only` — sets `quitOnEmpty` on every oracle / tactic ranking
    /// in the selected heuristic (HS `setQuitOnEmpty`, Proof.hs:712-716).
    pub oracle_only: bool,
}

/// Resolve the CLI `--heuristic`/`--oraclename` into a `GoalRanking` list,
/// mirroring HS's CLI heuristic pipeline:
///
///   1. `filterHeuristic diff rawRankings` — parse the ranking string char
///      by char (System.hs:680-684).  RS `parse_heuristic_str_with_tactics`.
///   2. `map (mapOracleRanking (maybeSetOracleRelPath oraclename))` — set the
///      oracle relPath from `--oraclename` (TheoryLoader.hs:305).
///   3. `defaultOracleNames srcThyInFileName` (TheoryLoader.hs:646) — fill any
///      oracle ranking that STILL has no relPath with the default `.oracle`
///      name (theory-basename `.oracle` if it exists on disk, else `"oracle"`).
///   4. `oraclePath = fromMaybe "." workDir </> normalise relPath`
///      (System.hs:574-575).  The CLI heuristic's `defaultOracle = Oracle
///      Nothing Nothing` (System.hs:548) has workDir `Nothing` ⇒ `"."`, so
///      its oracle exec path is CWD-relative (`./<name>`), NOT theory-dir
///      relative (unlike the in-file heuristic).
///   5. `setQuitOnEmpty` (Proof.hs:712-716) — `--oracle-only` sets
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
    // (oraclename, applied below) and step 3 (default name).  We post-process
    // to (a) override the parsed default with `--oraclename` where given, and
    // (b) resolve every relPath against workDir `"."` (CLI-heuristic workDir).
    let mut rankings = crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
        raw, in_file, tactics);
    // The CLI `--oraclename` (`Just "" -> Nothing`, TheoryLoader.hs:310).
    let oraclename: Option<&str> = match cli.oracle_name.as_deref() {
        Some("") => None,
        other => other,
    };
    // Default `.oracle` name (HS `defaultOracleNames`) for oracle rankings
    // that carried no inline `"path"` AND get no `--oraclename`.
    let default_name = crate::pretty_theory::oracle_name_for_theory(in_file);
    for r in rankings.iter_mut() {
        match r {
            GoalRanking::Oracle { oracle_path, quit_on_empty }
            | GoalRanking::OracleSmart { oracle_path, quit_on_empty } => {
                // Step 2/3: relPath = --oraclename if given, else the default
                // name (the parser already filled the default name, but for a
                // bare `O`/`o` from the CLI string it set the default — so we
                // only OVERRIDE when --oraclename is present; if --oraclename
                // is absent, the parser's default-name value stands).
                if let Some(name) = oraclename {
                    *oracle_path = name.to_string();
                } else if oracle_path.is_empty() {
                    *oracle_path = default_name.clone();
                }
                // Step 4: workDir = "." for the CLI heuristic (Oracle Nothing).
                *oracle_path = resolve_oracle_path(oracle_path, None);
                // Step 5: --oracle-only quitOnEmpty (Proof.hs:713-714).
                if cli.oracle_only {
                    *quit_on_empty = true;
                }
            }
            // Step 5: --oracle-only also sets quitOnEmpty on tactic rankings
            // (HS `aux (InternalTacticRanking _ t) = InternalTacticRanking
            // (quitOnEmptyOracle prover) t`, Proof.hs:715).
            GoalRanking::Tactic { quit_on_empty, .. }
                if cli.oracle_only => {
                    *quit_on_empty = true;
                }
            _ => {}
        }
    }
    Some(rankings)
}

/// One theory-level cache entry of refined source cases — the result of
/// a `ctx.ensure_saturated()` pass, snapshotted per `Source` by goal.
/// Keyed (in [`ProverSession::source_cache`]) by the SORTED set of
/// `[sources]`-lemma names folded into `typing_assumptions`.
///
/// Why this is safe to share across lemmas (lever #3 — HS computes
/// `_crcRefinedSources` ONCE per `ClosedRuleCache` and reuses it for
/// every lemma; RuleItem.hs:64-69, Prover.hs:170-184):
///   * The saturated+refined cases are a pure function of the (shared
///     template) raw sources + rules + restrictions + `typing_assumptions`.
///     Two lemmas with the same source-name key feed identical inputs, so
///     they produce identical cases.
///   * We ONLY cache (and therefore only reuse) entries whose producing
///     `ensure_saturated` consumed ZERO fresh Maude vars (`delta == 0`).
///     With no fresh allocation the cases embed only template-sourced var
///     indices (shared, identical across clones) AND the per-lemma
///     fresh-counter trajectory is unperturbed — so a cache hit is
///     byte-identical to recomputing, both in the cases and in the counter
///     state the subsequent proof search starts from.  `delta` is
///     deterministic for a given key, so a key that cached once (delta 0)
///     yields delta 0 on every hit.  Sources lemmas (which DO allocate,
///     e.g. NSLPK3 `types` delta=5, and carry a self-excluded key) are
///     never cached and keep recomputing — they are rare and proved once.
struct CachedSources {
    /// Per source: (goal join-key, refined case list, incomplete flag).
    sources: Vec<(
        crate::constraint::constraints::Goal,
        Vec<(Vec<String>, crate::constraint::system::System)>,
        bool,
    )>,
}

/// Per-file shared prover state — the bits of work that depend only on
/// the theory, not on which lemma is being proved.  Built once via
/// [`ProverSession::build_with_in_file_and_heuristic`] and reused across
/// `prove_lemma_in_session` calls so each lemma in a multi-lemma `--prove`
/// run pays the heavy setup cost only ONCE.
///
/// Profile showed ~3s of `ProofContext::new` work (intruder rules,
/// `close_intr_rule` Maude variants, DH/BP cached variants, per-rule
/// variant precomputation, `precompute_sources`, `precompute_full_sources`)
/// re-running per lemma.  On wireguard's 8 lemmas that was ~24s
/// (HS amortises this across the file).  By sharing the template
/// `ProofContext` we recover that cost; per-lemma we still run the
/// lightweight `ensure_saturated` (each lemma needs its own
/// `typing_assumptions`-refined source cases).
pub struct ProverSession {
    /// Elaborated typed theory.  Used to look up lemmas, restrictions,
    /// rules, heuristic.  Constructed once.
    pub theory: crate::theory::Theory,
    /// CLI `--heuristic`/`--oraclename`/`--oracle-only` (HS `AutoProver`
    /// fields).  When `cli_heuristic.raw` is `Some`, it OVERRIDES the per-lemma
    /// / theory heuristic for EVERY lemma (HS `selectHeuristic`, Proof.hs:707).
    cli_heuristic: CliHeuristic,
    /// Solved-leaf extraction strategy (HS `apCut`, threaded from
    /// `--stop-on-trace`, TheoryLoader.hs:356-360).  Theory-global (HS
    /// stores it once in `TheoryLoadOptions.stopOnTrace`), so it is set on
    /// every per-lemma `ProofContext` in [`Self::setup_per_lemma_ctx`].
    cut: crate::constraint::solver::context::CutStrategy,
    /// File-level RAII guard for `set_user_funs_for_theory`.  Kept
    /// alive for the whole session so per-lemma `term_to_lnterm`
    /// calls see the right user-fn-symbol set on the BUILDING thread.
    _user_funs_guard: crate::elaborate::UserFunsForTheoryGuard,
    /// Cached user-declared function-name sets, re-installed per lemma on
    /// the proving thread.  Under B1 (lemma-level parallelism) each lemma
    /// is proved on a rayon WORKER thread whose thread-locals are empty —
    /// the file-level `_user_funs_guard` above only populated them on the
    /// thread that BUILT the session (main).  `term_to_lnterm` /
    /// `term_to_gterm` (in `formula_to_guarded` etc.) read those
    /// thread-locals during the proof, so each worker must re-install them
    /// or it would mis-classify user nullary/unary funs (e.g. a declared
    /// `left/0` lifted to a free variable), corrupting the guarded formulas
    /// and the proof.  See `prove_lemma_in_session_mode`.
    user_funs: crate::elaborate::CollectedUserFuns,
    /// Guarded-form restrictions (constructed once from theory).
    restrictions: Vec<Guarded>,
    /// Template `ProofContext` carrying the expensive precompute:
    /// `rules` (with variants installed), `intruder_rules`,
    /// `unique_sources`, `full_sources` (raw, unsaturated cells), etc.
    /// Cloned per lemma; each clone sets its own
    /// `typing_assumptions`/`heuristic`/`is_exists_trace`/`use_induction`
    /// and runs `ensure_saturated` to materialise lemma-specific
    /// refined source cases.
    template_ctx: ProofContext,
    /// Fresh-counter value BEFORE the template was built.  The template
    /// build is counter-neutral (the build's fresh allocation is undone by
    /// restoring the counter), so every lemma starts from this same base.
    /// Used as the `ensure_above` floor on the per-lemma counter clone.
    setup_counter_before: u64,
    /// Lever #3 — shared refined-source cache (see [`CachedSources`]).
    /// Keyed by the sorted `[sources]`-lemma name set.  Populated lazily
    /// on the first lemma of each key; reused by all later lemmas with the
    /// same key (every normal lemma shares the all-sources key), letting
    /// the expensive `saturate_sources_with_simp` pass run once per theory
    /// instead of once per lemma.  `Mutex` keeps the session `&self`.
    // keyed source cache (Mutex); source-key->CachedSources
    // lookup, never iterated; std kept (byte-inert) — order never reaches output.
    #[allow(clippy::disallowed_types)]
    source_cache: std::sync::Mutex<
        std::collections::HashMap<Vec<String>, CachedSources>,
    >,
}

/// Per-lemma source kind, mirroring HS `lemmaSourceKind` (Lemma.hs:38-41):
///   lemmaSourceKind lem
///     | SourceLemma `elem` lAttributes lem = RawSource
///     | otherwise                          = RefinedSource
/// HS sets `pcSourceKind = lemmaSourceKind l` (ClosedTheory.hs:116) and
/// `mkSystem` stamps it onto the initial system's `sSourceKind`
/// (Prover.hs:325).  In RS `SourceKind`, `RawSources < RefinedSources`,
/// matching HS's `RawSource < RefinedSource` Ord (System.hs:362-365), so it
/// can be used directly as the `lemmaSourceKind lem <= kind` bound below.
fn lemma_source_kind(lemma: &crate::theory::Lemma) -> SourceKind {
    if lemma.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Sources)) {
        SourceKind::RawSources
    } else {
        SourceKind::RefinedSources
    }
}

/// Gather the `[reuse]` lemmas declared BEFORE `lemma_name`, mirroring HS
/// `gatherReusableLemmas $ L.get sSourceKind sys` (Prover.hs:329-338):
///
///   guard $ lemmaSourceKind lem <= kind
///        && ReuseLemma `elem` lAttributes lem
///        && AllTraces == lTraceQuantifier lem
///        && lName lem `notElem` pcHiddenLemmas ctxt
///        && "ALL"     `notElem` pcHiddenLemmas ctxt
///
/// `kind` is the source kind of the system being built (= the proved
/// lemma's `lemmaSourceKind`).  `pcHiddenLemmas` is populated from the
/// PROVED lemma's own `[hide_lemma=..]` attributes (ClosedTheory.hs:109),
/// so the hidden set is computed here from `lemma_name`'s attributes.
/// HS uses `formulaToGuarded_` (fail-loud) on each reuse formula, so a
/// non-guardable reuse formula propagates a `ProveError` rather than being
/// silently dropped.
fn gather_reusable_lemmas(
    theory: &crate::theory::Theory,
    lemma_name: &str,
    kind: SourceKind,
) -> Result<Vec<Guarded>, ProveError> {
    // HS `pcHiddenLemmas` = the proved lemma's `[hide_lemma=h]` names.
    let hidden: Vec<&str> = theory
        .lookup_lemma(lemma_name)
        .map(|l| l.attributes.iter().filter_map(|a| match a {
            crate::theory::LemmaAttr::HideLemma(h) => Some(h.as_str()),
            _ => None,
        }).collect())
        .unwrap_or_default();
    let hide_all = hidden.contains(&"ALL");
    let mut reuse_lemmas: Vec<Guarded> = Vec::new();
    for prior in theory.lemmas() {
        if prior.name == lemma_name { break; }
        if lemma_source_kind(prior) > kind { continue; }
        if !prior.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Reuse)) {
            continue;
        }
        if !matches!(prior.trace_quantifier, crate::theory::TraceQuantifier::AllTraces) {
            continue;
        }
        if hide_all || hidden.contains(&prior.name.as_str()) {
            continue;
        }
        let rg = formula_to_guarded(&prior.formula)
            .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &prior.formula)))?;
        reuse_lemmas.push(rg);
    }
    Ok(reuse_lemmas)
}

/// Gather the typing assumptions folded into a lemma's refined-source
/// computation, plus the SORTED `source_key` identifying that computation
/// (the set of `[sources]`-lemma names used; callers off the session cache
/// path ignore the key).
///
/// HS-faithful per-lemma RAW-vs-REFINED selection (ClosedTheory.hs:116-118
/// `cases = case lemmaSourceKind l of RawSource -> crcRawSources;
/// RefinedSource -> crcRefinedSources`).  `[sources]` lemmas (RawSource,
/// Lemma.hs:40) use the RAW precomputed sources — `refineWithSourceAsms` is
/// NEVER applied to them — so they carry NO typing assumptions (an empty
/// list makes `ensure_saturated` skip the refine and use the raw cases
/// verbatim).  All other lemmas (RefinedSource) use the refined sources
/// (`refineWithSourceAsms parameters typAsms`, Rule.hs:157), so they fold in
/// every prior `[sources]`-lemma assumption (HS `typAsms`, Prover.hs:142-144,
/// which uses `formulaToGuarded_` — fail-loud, so a non-guardable formula
/// propagates a `ProveError` rather than being silently dropped).  The proved
/// lemma is excluded (self-refinement is circular).
fn gather_typing_assumptions(
    theory: &crate::theory::Theory,
    lemma_name: &str,
    kind: SourceKind,
) -> Result<(Vec<Guarded>, Vec<String>), ProveError> {
    let mut typing_assumptions: Vec<Guarded> = Vec::new();
    let mut source_key: Vec<String> = Vec::new();
    if kind >= SourceKind::RefinedSources {
        for prior in theory.lemmas() {
            if prior.name == lemma_name { continue; }
            if !prior.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Sources)) {
                continue;
            }
            if !matches!(prior.trace_quantifier, crate::theory::TraceQuantifier::AllTraces) {
                continue;
            }
            let rg = formula_to_guarded(&prior.formula)
                .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &prior.formula)))?;
            typing_assumptions.push(rg);
            source_key.push(prior.name.clone());
        }
    }
    source_key.sort();
    Ok((typing_assumptions, source_key))
}

/// Resolve the goal-ranking heuristic for a lemma, mirroring HS
/// `selectHeuristic prover ctx = apDefaultHeuristic prover <|> L.get
/// pcHeuristic ctx` (Proof.hs:707-708): the CLI `--heuristic`
/// (`apDefaultHeuristic`) OVERRIDES the per-lemma / theory heuristic when
/// present.  Otherwise fall back to per-lemma `[heuristic=..]` > theory-level
/// `heuristic:` > None (`getProofContext.specifiedHeuristic`,
/// ClosedTheory.hs:123-131); `None` becomes `SmartRanking False` downstream.
/// The in-file fallback resolves oracle paths against the theory dir and
/// `{name}` tactic rankings against `tactics`.
fn resolve_heuristic(
    cli: &CliHeuristic,
    lemma: &crate::theory::Lemma,
    theory_heuristic_first: Option<&str>,
    tactics: &[crate::tactic::Tactic],
    in_file: &str,
) -> Option<Vec<crate::constraint::solver::goals::GoalRanking>> {
    match resolve_cli_heuristic(cli, in_file, tactics) {
        Some(rankings) => Some(rankings),
        None => {
            let lemma_heuristic: Option<&str> =
                lemma.attributes.iter().find_map(|a| match a {
                    crate::theory::LemmaAttr::Heuristic(s) => Some(s.as_str()),
                    _ => None,
                });
            let heuristic_raw: Option<String> = match lemma_heuristic {
                Some(h) => Some(h.to_string()),
                None => theory_heuristic_first.map(|s| s.to_string()),
            };
            heuristic_raw.map(|h| {
                let mut rankings =
                    crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
                        &h, in_file, tactics);
                prepend_theory_dir_to_oracle_paths(&mut rankings, in_file);
                rankings
            })
        }
    }
}

impl ProverSession {
    /// Build the shared per-file state, also setting `theory.in_file` for
    /// oracle path resolution (HS Parser.hs).  Does the expensive
    /// once-per-file work: theory elaboration, restriction conversion, full
    /// `ProofContext` construction (which runs intruder rule generation,
    /// `close_intr_rule`, DH/BP cached variants, per-rule variant
    /// expansion, source precomputation).  Carries the CLI
    /// `--heuristic`/`--oraclename`/`--oracle-only` (HS `AutoProver`): when
    /// `cli_heuristic.raw` is `Some`, every lemma's goal ranking is the CLI
    /// heuristic (HS `selectHeuristic`: `apDefaultHeuristic <|> pcHeuristic`,
    /// Proof.hs).
    // keyed source cache constructor; lookup-only map;
    // std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    pub fn build_with_in_file_and_heuristic(
        parser_theory: &p::Theory,
        maude: tamarin_term::maude_proc::MaudeHandle,
        pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
        in_file: &str,
        cli_heuristic: CliHeuristic,
        cut: crate::constraint::solver::context::CutStrategy,
    ) -> Result<Self, ProveError> {
        // RAII-set the user-fn-symbol thread-locals for the WHOLE
        // session.  Per-lemma `term_to_lnterm` calls during search
        // need these set; the parser-theory drives the set.
        let user_funs = crate::elaborate::collect_user_funs_for_theory(parser_theory);
        let _user_funs_guard = crate::elaborate::set_user_funs_from_collected(&user_funs);
        let mut theory = elaborate(parser_theory)
            .map_err(|e| ProveError::Elaboration(e.message))?;
        // Set in_file for oracle path resolution (HS Parser.hs:304).
        theory.in_file = in_file.to_string();
        // HS `mkSystem` maps `formulaToGuarded_ = either (error . render) id`
        // (Prover.hs:324, Guarded.hs:466-467) over restriction formulas — it
        // ABORTS on a non-guardable restriction rather than silently dropping
        // it (which would weaken the constraint set and could let an unsound
        // proof through).  Mirror the fail-loud behaviour: propagate a
        // `ProveError::Guarded` instead of skipping.
        let mut restrictions: Vec<Guarded> = Vec::new();
        for r in theory.restrictions() {
            let rg = formula_to_guarded(&r.formula)
                .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &r.formula)))?;
            restrictions.push(rg);
        }
        let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
        // HS `setforcedInjectiveFacts {L_PureState, L_CellLocked}` (Sapic.hs:84):
        // when the state-channel optimisation is on, those two facts are forced
        // injective for the WHOLE proof (`closeRuleCache`, Rule.hs:147-150).
        let forced_injective_facts: Vec<crate::fact::FactTag> = if theory.options.state_channel_opt {
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
            maude.clone(), pool, rules, restrictions.clone(), &forced_injective_facts);
        maude.reset_counter_to(setup_counter_before);
        Ok(ProverSession {
            theory,
            cli_heuristic,
            cut,
            _user_funs_guard,
            user_funs,
            restrictions,
            template_ctx,
            setup_counter_before,
            source_cache: std::sync::Mutex::new(std::collections::HashMap::new()),
        })
    }

    /// Build the per-lemma `ProofContext` shared verbatim by both session
    /// entry points (`prove_lemma_in_session_mode` and
    /// `prove_system_in_session`): clone the template ctx, give it its own
    /// fresh-counter floored at the shared `setup_counter_before` base (B1
    /// lemma-level parallelism), then stamp `is_exists_trace` / `heuristic`
    /// / `lemma_name` / `theory_file` and fold in the `[sources]`-lemma
    /// typing assumptions.  Returns the ctx plus its source-cache key.
    fn setup_per_lemma_ctx(
        &self,
        lemma: &crate::theory::Lemma,
        lemma_name: &str,
        lemma_source_kind: SourceKind,
    ) -> Result<(ProofContext, Vec<String>), ProveError> {
        let theory = &self.theory;
        let mut ctx = self.template_ctx.clone();
        ctx.maude = ctx.maude.with_fresh_counter_from(0);
        ctx.maude.ensure_above(self.setup_counter_before.saturating_sub(1));
        ctx.is_exists_trace = matches!(
            lemma.trace_quantifier,
            crate::theory::TraceQuantifier::ExistsTrace,
        );
        // HS `apCut` is theory-global (one `TheoryLoadOptions.stopOnTrace`),
        // so stamp the session's cut onto every per-lemma context.
        ctx.cut = self.cut;
        let session_in_file = &theory.in_file;
        ctx.heuristic = resolve_heuristic(
            &self.cli_heuristic, lemma, theory.heuristic.first().map(|s| s.as_str()),
            &theory.tactic, session_in_file);
        ctx.lemma_name = lemma_name.to_string();
        ctx.theory_file = session_in_file.clone();
        let (typing_assumptions, source_key) =
            gather_typing_assumptions(theory, lemma_name, lemma_source_kind)?;
        ctx.typing_assumptions = typing_assumptions;
        Ok((ctx, source_key))
    }

    /// Restore the refined source cases for `source_key` from the session
    /// cache, or saturate them and (when the fresh-counter delta is 0) write
    /// them back.  Returns whether the cache was hit.  Shared by both session
    /// entry points; the `TAM_DBG_SAT_COUNTER` diagnostics live here.  The
    /// caller must have already gated out the `will_emit_bare_sorry` case
    /// (which forces no source and must skip this entirely).
    fn restore_or_saturate_sources(
        &self,
        ctx: &mut ProofContext,
        source_key: Vec<String>,
        cache_disabled: bool,
    ) -> bool {
        let mut cache_hit = false;
        if !cache_disabled {
            let guard = self.source_cache.lock().unwrap();
            if let Some(entry) = guard.get(&source_key) {
                // Restore cached cases onto this clone's lazy sources by goal,
                // then mark saturation Done so `cases(ctx)` reads them directly
                // and the expensive `ensure_saturated` pass is skipped.
                // `ctx` is a fresh `template_ctx.clone()` (deep copy), so its
                // shared bundle is uniquely owned; `Arc::get_mut` succeeds and
                // the `src.incomplete = …` write cannot reach a sibling lemma.
                let shared = std::sync::Arc::get_mut(&mut ctx.shared)
                    .expect("per-lemma ctx uniquely owns its source bundle before search");
                for src in &mut shared.full_sources {
                    if let Some((_, cases, incomplete)) =
                        entry.sources.iter().find(|(g, _, _)| *g == src.goal)
                    {
                        src.cases_set_list(cases.clone());
                        src.incomplete = *incomplete;
                    }
                }
                ctx.mark_saturated_done();
                cache_hit = true;
            }
        }
        if !cache_hit {
            let cnt_before = ctx.maude.fresh_counter_peek();
            ctx.ensure_saturated();
            let delta = ctx.maude.fresh_counter_peek().saturating_sub(cnt_before);
            if tamarin_utils::env_gate!("TAM_DBG_SAT_COUNTER") {
                eprintln!("[SAT_COUNTER] lemma={} key={:?} delta={} (computed)",
                    ctx.lemma_name, source_key, delta);
            }
            // Only cache results that allocated NO fresh vars — those are the
            // ones safe to replay byte-identically (counter unperturbed, cases
            // carry only template-sourced var indices).  Sources lemmas (delta
            // > 0) keep recomputing.
            if !cache_disabled && delta == 0 {
                let snapshot: Vec<_> = ctx.full_sources.iter()
                    .map(|s| (s.goal.clone(), s.cases_or_empty_list(), s.incomplete))
                    .collect();
                self.source_cache.lock().unwrap()
                    .entry(source_key)
                    .or_insert(CachedSources { sources: snapshot });
            }
        } else if tamarin_utils::env_gate!("TAM_DBG_SAT_COUNTER") {
            eprintln!("[SAT_COUNTER] lemma={} key={:?} (cache hit)", ctx.lemma_name, source_key);
        }
        cache_hit
    }

    /// Pre-fan-out single-flight saturation (lever #3): compute each DISTINCT
    /// `source_key`'s refined-source cases ONCE (sequentially over keys) and
    /// seed the session `source_cache` BEFORE the per-lemma proof fan-out, so
    /// the concurrent fan-out lemmas all take the cache-hit restore arm of
    /// [`Self::restore_or_saturate_sources`] rather than each recomputing the
    /// identical `saturate_sources_with_simp` pass.  HS computes
    /// `_crcRefinedSources` ONCE per `ClosedRuleCache` and reuses it for every
    /// lemma (RuleItem.hs:64-69, Prover.hs:170-184); without this pre-pass the
    /// rayon fan-out duplicates that compute per lemma, because at
    /// `processors >= 2` every worker misses — no sibling has finished writing
    /// the cache yet.
    ///
    /// `is_target(name)` reports whether the batch selector targets a lemma
    /// (HS `--prove` match).  A lemma saturates its `source_key` iff it is a
    /// target OR carries a stored proof skeleton — exactly the fan-out's own
    /// gate: see the `will_emit_bare_sorry` derivation in
    /// [`prove_lemma_in_session_mode`], where a non-target lemma with no stored
    /// tree emits a bare `sorry`, consults no source, and so never saturates.
    /// Such a lemma MUST NOT seed a key here, or the pre-pass would pay a full
    /// saturation for work the fan-out skips (the spdm121 `--prove=<no match>`
    /// 61s-vs-0.7s precedent).
    ///
    /// Seeding reuses [`Self::restore_or_saturate_sources`] verbatim, so its
    /// `delta == 0` write gate stays the single source of truth: the pre-pass
    /// caches exactly the keys the fan-out would.  Because `setup_per_lemma_ctx`
    /// floors every clone's fresh counter at the shared `setup_counter_before`
    /// base, the representative lemma computes the same cases any fan-out lemma
    /// of the key would (the `CachedSources` are a pure function of the key) —
    /// so this only converts concurrent misses into hits, changing nothing
    /// else.  `ensure_saturated` restores the fresh counter before returning
    /// (see its tail in context.rs), so `delta` is 0 for every key and every
    /// saturating key is cached.
    ///
    /// Runs on the caller's thread before the fan-out; re-installs the
    /// user-fn-symbol thread-locals for its `formula_to_guarded` calls (same
    /// rationale as `prove_lemma_in_session_mode`).  Returns the number of
    /// DISTINCT keys saturated — the count of `saturate_sources_with_simp`
    /// passes the pre-pass runs (one per distinct key rather than one per
    /// lemma).  `cache_disabled` (`TAM_RS_NO_SOURCE_CACHE`) makes it a no-op,
    /// leaving every lemma on the per-lemma compute path.
    pub fn presaturate_shared_sources(
        &self,
        cache_disabled: bool,
        is_target: impl Fn(&str) -> bool,
    ) -> usize {
        if cache_disabled { return 0; }
        let _lemma_user_funs_guard =
            crate::elaborate::set_user_funs_from_collected(&self.user_funs);
        let mut seen: tamarin_utils::FastSet<Vec<String>> =
            tamarin_utils::FastSet::default();
        let mut saturated = 0usize;
        for lemma in self.theory.lemmas() {
            // Fan-out saturation gate (see `will_emit_bare_sorry`): a lemma
            // consults its source cases — and so saturates its key — iff it is
            // a `--prove` target OR carries a stored proof skeleton that
            // `check_and_extend` replays.
            if !(is_target(lemma.name.as_str()) || lemma.proof.tree.is_some()) {
                continue;
            }
            let kind = lemma_source_kind(lemma);
            // Compute the key (guarded-convert the prior `[sources]` lemmas)
            // BEFORE the deep `template_ctx` clone, so a repeat key skips
            // without cloning.  A non-guardable `[sources]`/typing formula
            // errors here; the fan-out reproduces the identical per-lemma
            // abort, so skip it in the pre-pass rather than preempting it.
            let source_key = match gather_typing_assumptions(
                &self.theory, lemma.name.as_str(), kind) {
                Ok((_, key)) => key,
                Err(_) => continue,
            };
            if !seen.insert(source_key) { continue; }
            // First lemma of this key: build its per-lemma ctx and saturate +
            // seed through the shared `delta == 0` gate.  The cache starts
            // empty and `seen` skips repeats, so this always misses and
            // computes.
            let (mut ctx, key) = match self.setup_per_lemma_ctx(
                lemma, lemma.name.as_str(), kind) {
                Ok(v) => v,
                Err(_) => continue,
            };
            self.restore_or_saturate_sources(&mut ctx, key, false);
            saturated += 1;
        }
        saturated
    }
}

/// Prove a single lemma using a pre-built `ProverSession`.  Skips the
/// expensive theory-level setup (which `ProverSession::build_with_in_file_and_heuristic`
/// did) and runs only the per-lemma work: guarded conversion of lemma+reuse
/// formulas, `formula_to_system`, ProofContext clone +
/// per-lemma-field setup, `ensure_saturated` (typing-asm refinement),
/// and proof-tree search.
pub fn prove_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(session, lemma_name, max_steps, true)
}

/// Replay a non-target lemma's stored skeleton WITHOUT auto-proving its
/// open leaves — HS's close-time `checkAndExtendProver (sorryProver
/// Nothing)` (Prover.hs:174-185).  Used for lemmas the `--prove`
/// selector does not target: HS retains their close-time-replayed proof
/// verbatim (Prover.hs:273-275) and reports the stored status.  Returns
/// the lemma's own start system + a `Sorry` placeholder when no stored
/// skeleton exists (HS keeps the parsed `unproven ()` skeleton, which is
/// a single `sorry`).
pub fn check_and_extend_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(session, lemma_name, max_steps, false)
}

/// Run the from-scratch autoprover on an ARBITRARY start system under
/// `lemma_name`'s per-lemma `ProofContext` — the web interactive
/// `autoprove` primitive.
///
/// HS `getProverR` → `applyProverAtPath` (`src/Web/Theory.hs:140-143`) →
/// `focus proofPath (runAutoProver ap)` (`lib/theory/src/Theory/Proof.hs:604-612`)
/// runs the prover from the subproof's system at the URL's proof path,
/// under the per-lemma context `modifyLemmaProof` supplies
/// (`getProofContext l thy`, ClosedTheory.hs — `pcSources` picked raw vs
/// refined by `lemmaSourceKind`, `pcUseInduction`, `pcHeuristic`,
/// typing-assumption-refined source cases).  This builds that context
/// EXACTLY as [`prove_lemma_in_session`] does — same template clone, same
/// counter base, same `typing_assumptions` gate, same saturation +
/// source-cache participation — then drives `run_proof_search` from the
/// caller's `sys` instead of the lemma's initial system.
///
/// Deliberately NO skeleton replay: web `runAutoProver` "ignores the
/// existing proof and tries to find one by itself" (Theory/Proof.hs:743-747)
/// — it is not wrapped in `replaceSorryProver` (batch-`--prove`-only,
/// Main/TheoryLoader.hs:518,606).
pub fn prove_system_in_session(
    session: &ProverSession,
    lemma_name: &str,
    sys: crate::constraint::system::System,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    // Thread-locals for user-fn-symbol resolution — the web autoprove
    // runs on a blocking-pool thread whose locals start empty.  Same
    // rationale as `prove_lemma_in_session_mode`.
    let _lemma_user_funs_guard =
        crate::elaborate::set_user_funs_from_collected(&session.user_funs);

    let theory = &session.theory;
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;
    let lemma_source_kind = lemma_source_kind(lemma);

    // --- Per-lemma ProofContext, mirroring `prove_lemma_in_session_mode`
    // step for step (see the comments there for the HS citations). ------
    // `[sources]` lemmas prove against RAW sources (no typing assumptions);
    // all others fold in every prior `[sources]` lemma — the `source_key`
    // gate is inside `setup_per_lemma_ctx`.
    let (mut ctx, source_key) =
        session.setup_per_lemma_ctx(lemma, lemma_name, lemma_source_kind)?;
    // Saturate (or restore from the session's refined-source cache) — the
    // search below always consults source cases, so this is unconditionally
    // the `will_emit_bare_sorry == false` arm of `prove_lemma_in_session_mode`,
    // including the delta==0 cache-write gate.
    let cache_disabled = tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
    let _cache_hit = session.restore_or_saturate_sources(&mut ctx, source_key, cache_disabled);
    let force_induction = lemma.attributes.iter().any(|a| matches!(a,
        crate::theory::LemmaAttr::UseInduction | crate::theory::LemmaAttr::Sources));
    if force_induction {
        ctx.use_induction = crate::constraint::solver::context::UseInduction::UseInduction;
    }
    Ok(run_proof_search(&ctx, sys, max_steps))
}

fn prove_lemma_in_session_mode(
    session: &ProverSession,
    lemma_name: &str,
    max_steps: usize,
    auto_prove: bool,
) -> Result<ProofNode, ProveError> {
    let trace = tamarin_utils::env_gate!("TAM_DBG_PHASE");
    let t_phase: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };

    // B1 (lemma-level parallelism): under the per-lemma rayon `par_iter`,
    // this runs on a WORKER thread whose user-fn-symbol thread-locals are
    // empty (the session's file-level `_user_funs_guard` only set them on
    // the thread that BUILT the session, i.e. `main`).  `formula_to_guarded`
    // below — and every search-time `term_to_lnterm` / `term_to_gterm` —
    // reads those thread-locals, so re-install them here for the duration of
    // this prove call.  Without this, a declared nullary fun (e.g. `left/0`)
    // is mis-classified as a free variable on the worker, corrupting the
    // guarded formula and flipping the lemma verdict.  The guard restores
    // the previous (empty) values on drop, so it is safe to nest and is
    // output-identical to the serial path (where the file-level guard
    // already covered the main thread).
    let _lemma_user_funs_guard =
        crate::elaborate::set_user_funs_from_collected(&session.user_funs);

    let theory = &session.theory;
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;

    let g = formula_to_guarded(&lemma.formula)
        .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &lemma.formula)))?;

    // Per-lemma source kind, mirroring HS `lemmaSourceKind` (Lemma.hs:38-41):
    // `[sources]`-tagged lemmas get RawSource, all others RefinedSource.
    // HS sets `pcSourceKind = lemmaSourceKind l` (ClosedTheory.hs:102,116)
    // and `formulaToSystem` stamps it onto the initial system's
    // `sSourceKind` (Prover.hs:325).
    let lemma_source_kind = lemma_source_kind(lemma);

    // `[reuse]` lemmas declared BEFORE this one.  Same gather logic as
    // the pre-session prove_lemma_with_pool_file_heuristic path.
    let reuse_lemmas =
        gather_reusable_lemmas(theory, lemma_name, lemma_source_kind)?;

    let tq = match lemma.trace_quantifier {
        crate::theory::TraceQuantifier::AllTraces => p::TraceQuantifier::AllTraces,
        crate::theory::TraceQuantifier::ExistsTrace => p::TraceQuantifier::ExistsTrace,
    };
    let mut sys = formula_to_system(
        session.restrictions.clone(),
        lemma_source_kind,
        tq,
        false,
        &g,
    );
    sys.insert_lemmas(reuse_lemmas);

    if trace { eprintln!("[phase] (session) formula_to_system done dt={:.3}s",
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_ctx: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    // Per-lemma ProofContext: clone the template (built once at session
    // construction with raw, unsaturated `full_sources` — each source's
    // `cases_cell = None`), give it its OWN fresh-counter Arc floored at the
    // shared `setup_counter_before` base (B1 lemma-level parallelism: still
    // sharing the template's Maude subprocess, but concurrently proving
    // lemmas must not race on a shared counter), and stamp the per-lemma
    // fields.  See `setup_per_lemma_ctx`.  Each clone's `ensure_saturated`
    // populates ITS OWN cells from ITS OWN `typing_assumptions`, so there is
    // no cross-lemma contamination.
    let (mut ctx, source_key) =
        session.setup_per_lemma_ctx(lemma, lemma_name, lemma_source_kind)?;
    if trace { eprintln!("[phase] (session) ProofContext clone dt={:.3}s",
        t_ctx.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_sat: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    // HS-faithful laziness: refined sources are a lazy `where`-bound thunk
    // in HS's `ClosedRuleCache` (`refinedSources` = `precomputeSources` →
    // `refineWithSourceAsms`, Rule.hs:156-157), forced ONLY when a proof
    // method reads `pcSources` (ProofMethod.hs:317).  A non-target lemma
    // with NO stored skeleton replays HS's parsed `unproven () = sorry`
    // (`unproven = sorry Nothing`, Proof.hs:255-256; used by the lemma
    // constructor at ProofSkeleton.hs:61) via `checkAndExtendProver`'s
    // `sorry` walk
    // (Proof.hs:624-630) — that single `Sorry` node consults no source,
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
    let will_emit_bare_sorry =
        !auto_prove && lemma.proof.tree.is_none();
    // Lever #3: reuse a previously-computed refined-source set when one
    // exists for this exact `source_key`.  See [`CachedSources`] for why a
    // hit is byte-identical (only delta==0 results are ever cached).
    let cache_disabled = tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
    let cache_hit = if will_emit_bare_sorry {
        // Skip the eager saturate + cache entirely — this lemma forces no
        // source case (matches HS's lazy `pcSources`).  Leave the lazy
        // `cases(ctx)` hook in place in case some future path consults a
        // source; for the bare-sorry early return it never fires.
        if tamarin_utils::env_gate!("TAM_DBG_SAT_COUNTER") {
            eprintln!("[SAT_COUNTER] lemma={} key={:?} (bare-sorry, saturation deferred)",
                lemma_name, source_key);
        }
        false
    } else {
        session.restore_or_saturate_sources(&mut ctx, source_key, cache_disabled)
    };
    if trace { eprintln!("[phase] (session) ensure_saturated dt={:.3}s hit={}",
        t_sat.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64()), cache_hit); }
    if tamarin_utils::env_gate!("TAM_RS_DBG_PHASE") {
        eprintln!("[rs-phase] lemma-proof START");
    }
    let force_induction = lemma.attributes.iter().any(|a| matches!(a,
        crate::theory::LemmaAttr::UseInduction | crate::theory::LemmaAttr::Sources));
    if force_induction {
        ctx.use_induction = crate::constraint::solver::context::UseInduction::UseInduction;
    }
    // Skeleton replay: same logic as in `prove_lemma_with_pool_file_heuristic`.
    if let Some(tree) = lemma.proof.tree.clone() {
        if auto_prove {
            return Ok(crate::replay::replace_sorry_prove(&ctx, sys, &tree, max_steps));
        } else {
            // Non-target lemma: HS close-time check-and-extend
            // replay, no auto-proving of open leaves.
            return Ok(crate::replay::check_and_extend(&ctx, sys, &tree, max_steps));
        }
    }
    if !auto_prove {
        // Non-target lemma with no stored skeleton: HS keeps the parsed
        // `unproven ()` single-`sorry` proof (`unproven = sorry Nothing`,
        // Proof.hs:255-256; used by the lemma constructor at
        // ProofSkeleton.hs:61) — an
        // annotated Sorry at the lemma's start system (the node carries
        // the start system, so it renders as plain `by sorry`).
        return Ok(crate::replay::annotated_sorry_root(sys));
    }
    let t_search: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    let r = run_proof_search(&ctx, sys, max_steps);
    if trace { eprintln!("[phase] (session) run_proof_search dt={:.3}s total={:.3}s",
        t_search.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64()),
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    Ok(r)
}

/// Drive a proof attempt for one lemma in a parsed theory.
///
/// `max_steps` bounds the proof-tree depth so the call always
/// terminates. Pass a generous value (e.g. 100+) for non-trivial
/// proofs.
pub fn prove_lemma(
    parser_theory: &p::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_with_pool_file_heuristic(
        parser_theory, lemma_name, maude, None, max_steps, "",
        &CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs)
}

/// Like [`prove_lemma`] but accepts a `MaudePool` (consulted ONLY inside
/// `par_iter` closures — see `sources.rs::saturate_sources_with_simp_opt`),
/// the source file path (oracle path resolution, HS `oraclePath oracle =
/// takeDirectory inFile </> normalise relPath`, System.hs:574-575,
/// Parser.hs:304), and the CLI
/// `--heuristic`/`--oraclename`/`--oracle-only` (HS `AutoProver`).  This is
/// the per-lemma (non-session) fallback path; when `cli_heuristic.raw` is
/// `Some` it OVERRIDES the per-lemma / theory heuristic (HS `selectHeuristic`,
/// Proof.hs:707).
pub fn prove_lemma_with_pool_file_heuristic(
    parser_theory: &p::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    max_steps: usize,
    in_file: &str,
    cli_heuristic: &CliHeuristic,
    cut: crate::constraint::solver::context::CutStrategy,
) -> Result<ProofNode, ProveError> {
    let trace = tamarin_utils::env_gate!("TAM_DBG_PHASE");
    // Per-phase wall-clock instrumentation, gated by TAM_DBG_PHASE.
    // `Option<Instant>` keeps the disabled-path branch-predictable to
    // a single `if let Some(_)` check at each phase boundary.
    let t_phase: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    if trace { eprintln!("[phase] elaborate start"); }
    // Re-set the thread-locals that track user-declared function symbols
    // for the *duration of this prove call*.  `elaborate()` sets them
    // for its own scope via RAII guards that drop on return — so
    // `term_to_lnterm` calls during search would otherwise see an
    // empty set.  Mirror Haskell's funSig staying available through
    // the whole prover lifetime.
    let _user_funs_guard = crate::elaborate::set_user_funs_for_theory(parser_theory);
    // Elaborate to get the typed theory, then pull rules + restrictions.
    let mut theory = elaborate(parser_theory)
        .map_err(|e| ProveError::Elaboration(e.message))?;
    // Set in_file for oracle path resolution (HS Parser.hs:304).
    if !in_file.is_empty() { theory.in_file = in_file.to_string(); }
    if trace { eprintln!("[phase] elaborate done dt={:.3}s",
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_after_elab: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };

    // Find the lemma (parser-AST formula stays accessible via Theory's items).
    // Our typed theory's lemma carries a parser-AST formula too — look it up.
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;

    let g = formula_to_guarded(&lemma.formula)
        .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &lemma.formula)))?;

    // Per-lemma source kind (HS `lemmaSourceKind`, Lemma.hs:38-41): RawSource
    // for `[sources]`-tagged lemmas, RefinedSource for all others.  Stamped
    // onto the initial system's `sSourceKind` (Prover.hs:325).
    let lemma_source_kind = lemma_source_kind(lemma);

    // Convert restrictions to guarded.  HS `mkSystem` maps
    // `formulaToGuarded_ = either (error . render) id` (Prover.hs:324,
    // Guarded.hs:466-467) over restriction formulas — it ABORTS on a
    // non-guardable restriction rather than silently dropping it (a silent
    // drop weakens the constraint set and could let an unsound proof
    // through).  Mirror the fail-loud behaviour: propagate `ProveError`.
    let mut restrictions: Vec<Guarded> = Vec::new();
    for r in theory.restrictions() {
        let rg = formula_to_guarded(&r.formula)
            .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &r.formula)))?;
        restrictions.push(rg);
    }

    // `[reuse]` lemmas declared BEFORE this one are gathered separately
    // and pushed into `sLemmas` (not `sFormulas`) after building the
    // system. Mirrors Haskell's `mkSystem` (Prover.hs:317-338):
    //
    //   addLemmas
    //   . formulaToSystem restrictions ...
    //   where addLemmas sys = insertLemmas (gatherReusableLemmas ...) sys
    //
    // `gatherReusableLemmas` honours the source-kind bound and
    // `pcHiddenLemmas` guards (see [`gather_reusable_lemmas`]).
    //
    // The distinction is load-bearing for induction: `formulaToSystem`
    // conjoins non-safety restrictions into `sFormulas` so they're
    // included in `toInductionHypothesis(gf)` — yielding a `Disj` over
    // each conjunct's IH. Reuse lemmas, in contrast, must NOT be
    // conjoined: their IH would weaken the inductive hypothesis to a
    // disjunction across all reuse lemmas, blocking simplify from
    // resolving the IH against current trace actions.
    let reuse_lemmas =
        gather_reusable_lemmas(&theory, lemma_name, lemma_source_kind)?;

    // Bridge our typed `theory::TraceQuantifier` back to the parser's
    // `ast::TraceQuantifier` (which `formula_to_system` consumes).
    let tq = match lemma.trace_quantifier {
        crate::theory::TraceQuantifier::AllTraces => p::TraceQuantifier::AllTraces,
        crate::theory::TraceQuantifier::ExistsTrace => p::TraceQuantifier::ExistsTrace,
    };
    let mut sys = formula_to_system(
        restrictions.clone(),
        lemma_source_kind,
        tq,
        false,
        &g,
    );
    // Haskell's `addLemmas`: push reuse lemmas into `sLemmas`. They
    // become drivers for `insertImpliedFormulas` (which iterates
    // `sFormulas ++ sLemmas`) but are excluded from `ginduct`.
    //
    // Note: `[sources]`-tagged lemmas are NOT added to sLemmas.
    // Haskell's `gatherReusableLemmas` (Prover.hs:331) filters to
    // `[reuse]` only; `[sources]` lemmas are consumed solely by
    // `refineWithSourceAsms` at precompute time (driven below by the
    // `ctx.ensure_saturated()` call over `ctx.full_sources`).
    // Coverage on typing-class
    // lemmas (NSLPK3, chaum, foo, okamoto) depends on the
    // architecture matching Haskell exactly — no workaround.
    sys.insert_lemmas(reuse_lemmas);

    if trace { eprintln!("[phase] formula_to_system done dt={:.3}s; ProofContext::new start",
        t_after_elab.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_ctx: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    // Bridge the elaborated theory's rules into the proof context.
    let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
    // HS `setforcedInjectiveFacts {L_PureState, L_CellLocked}` (Sapic.hs:84):
    // force those facts injective when the state-channel optimisation is on.
    let forced_injective_facts: Vec<crate::fact::FactTag> = if theory.options.state_channel_opt {
        crate::tools::injective_fact_instances::pure_state_forced_fact_tags()
    } else {
        Vec::new()
    };
    // Install the optional `maude_pool` BEFORE the precompute phase
    // runs inside the constructor — `precompute_full_sources` calls
    // `saturate_sources_with_simp` which is parallel and benefits
    // from the pool.  Setting `maude_pool` after construction would
    // leave that initial precompute on the single shared `maude`.
    let mut ctx = ProofContext::new_with_restrictions_pool_forced(
        maude, pool, rules, restrictions.clone(), &forced_injective_facts);
    if trace { eprintln!("[phase] ProofContext::new done dt={:.3}s",
        t_ctx.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    // Propagate the lemma's trace quantifier so `is_finished` can
    // decide whether the Fresh-conflation case-drop should convert
    // Contradictory→Unfinishable (sound only on exists-trace where
    // the dropped case might have been the witness).
    ctx.is_exists_trace = matches!(
        lemma.trace_quantifier,
        crate::theory::TraceQuantifier::ExistsTrace,
    );
    // Solved-leaf extraction strategy (HS `apCut`, threaded from
    // `--stop-on-trace`).  Consumed once by `run_proof_search` below.
    ctx.cut = cut;

    // Resolve the goal-ranking heuristic.  HS `selectHeuristic prover ctx =
    // ... apDefaultHeuristic prover <|> L.get pcHeuristic ctx` (Proof.hs:707):
    // the CLI `--heuristic` (apDefaultHeuristic) OVERRIDES the per-lemma /
    // theory heuristic when present.  Otherwise (`getProofContext.
    // specifiedHeuristic`, ClosedTheory.hs:123-131): per-lemma `[heuristic=..]`
    // > theory-level `heuristic:` > None.  `None` falls back to `SmartRanking
    // False` in `rank_goals_with` (= HS's `defaultHeuristic False`).
    // `parse_heuristic_str_with_tactics` returns the full list for
    // round-robin scheduling (HS `roundRobinHeuristic`/`useHeuristic`,
    // ProofMethod.hs:576-595), resolves oracle paths, and resolves
    // `{name}` tactic rankings against `theory.tactic`.
    let in_file = &theory.in_file;
    ctx.heuristic = resolve_heuristic(
        cli_heuristic, lemma, theory.heuristic.first().map(|s| s.as_str()),
        &theory.tactic, in_file);
    // Set lemma_name and theory_file on ctx for oracle invocation.
    ctx.lemma_name = lemma_name.to_string();
    ctx.theory_file = in_file.clone();

    // `refineWithSourceAsms`: prune precomputed source cases by
    // assumptions from `[sources]`-tagged lemmas.  Mirrors Haskell's
    // `refineWithSourceAsms` — typing-style protocols rely on these
    // assumptions to filter out spurious decryption cases that would
    // otherwise surface as false counterexamples in our search.
    // HS-faithful per-lemma RAW-vs-REFINED selection (ClosedTheory.hs:116-118,
    // Lemma.hs:40): `[sources]` lemmas (RawSource) use the RAW precomputed
    // sources — `refineWithSourceAsms` is NEVER applied to them — so they
    // carry NO typing assumptions (empty list => `ensure_saturated` skips the
    // refine).  All other lemmas (RefinedSource) fold in every prior
    // `[sources]`-lemma assumption (HS `typAsms`, Prover.hs:142-144).
    // The proved lemma is excluded (self-refinement is circular); the
    // sorted source_key is unused off the session path.
    let (typing_assumptions, _source_key) =
        gather_typing_assumptions(&theory, lemma_name, lemma_source_kind)?;
    // HS-faithful saturation: store typing assumptions, then eagerly
    // run `ensure_saturated` (which applies `refine_with_source_asms`
    // with the assumptions just set).  This matches HS's
    // `refineWithSourceAsms` call site emitting `[Saturating Sources]
    // Done` at theory-close time — Rust does it per-lemma because the
    // ctx is per-lemma.
    ctx.typing_assumptions = typing_assumptions;
    let t_sat: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    ctx.ensure_saturated();
    if trace { eprintln!("[phase] ensure_saturated done dt={:.3}s",
        t_sat.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_search: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    if trace { eprintln!("[phase] run_proof_search start"); }
    // Phase marker so TAM_RS_DBG_* counts can be filtered to the
    // lemma-proof phase only.  Pair with HS's `[Saturating Sources]
    // Done` marker for HS↔Rust diffing of just the lemma proof
    // (excludes precompute/saturation).  Gated behind TAM_RS_DBG_PHASE
    // so default --prove stderr stays HS-faithful.
    if tamarin_utils::env_gate!("TAM_RS_DBG_PHASE") {
        eprintln!("[rs-phase] lemma-proof START");
    }
    // Honour the `[use_induction]` and `[sources]` attributes by
    // forcing the first proof method to be Induction. Haskell's
    // `ClosedTheory.hs` flips `pcUseInduction = UseInduction` for
    // `SourceLemma` and `InvariantLemma`-tagged lemmas — sources
    // proofs essentially always run via induction.
    let force_induction = lemma.attributes.iter().any(|a| matches!(a,
        crate::theory::LemmaAttr::UseInduction | crate::theory::LemmaAttr::Sources));
    if force_induction {
        ctx.use_induction = crate::constraint::solver::context::UseInduction::UseInduction;
    }

    // HS-faithful `replaceSorryProver` (Proof.hs:642-650):
    // when the lemma carries a parsed skeleton, walk that skeleton and
    // invoke the auto-prover only at `by sorry` leaves.  Otherwise (no
    // skeleton or parser couldn't structure it) fall through to the
    // pre-existing auto-prover-from-scratch behavior.
    if let Some(tree) = lemma.proof.tree.clone() {
        if tamarin_utils::env_gate!("TAM_DBG_REPLAY") {
            eprintln!("[replay] firing skeleton replay for `{}` (raw {} bytes)",
                lemma_name, lemma.proof.raw.len());
        }
        return Ok(crate::replay::replace_sorry_prove(&ctx, sys, &tree, max_steps));
    } else if tamarin_utils::env_gate!("TAM_DBG_REPLAY") {
        eprintln!("[replay] NO tree on `{}` (raw {} bytes) — falling through to auto-prover",
            lemma_name, lemma.proof.raw.len());
    }
    let r = run_proof_search(&ctx, sys, max_steps);
    if trace { eprintln!("[phase] run_proof_search done dt={:.3}s total={:.3}s",
        t_search.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64()),
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    Ok(r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn maude_path_local() -> Option<String> {
        std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        })
    }

    fn maude() -> Option<MaudeHandle> {
        let path = maude_path_local()?;
        MaudeHandle::start(&path, pair_maude_sig()).ok()
    }

    #[test]
    fn prove_lemma_unknown_name_is_error() {
        let h = match maude() { Some(m) => m, None => return };
        let parser_theory = tamarin_parser::parse_theory("theory T begin end", &[])
            .expect("parse");
        let r = prove_lemma(&parser_theory, "nonexistent", h, 5);
        assert!(matches!(r, Err(ProveError::LemmaNotFound(_))));
    }

    fn print_tree(node: &super::ProofNode, depth: usize) {
        let pad = "  ".repeat(depth);
        let reason = if let crate::constraint::solver::proof_method::ProofMethod::Finished(r) = &node.method {
            format!(" reason={:?}", r)
        } else { String::new() };
        eprintln!("{}status={:?} method={:?} children={} goals={} nodes={} formulas={} less_atoms={} edges={} {}",
            pad, node.status, node.method, node.children.len(),
            node.sys.goals.len(), node.sys.nodes.len(), node.sys.formulas.len(),
            node.sys.less_atoms.len(), node.sys.edges.len(), reason);
        if depth > 0 {
            for (id, ru) in node.sys.nodes.iter() {
                let info = match &ru.info {
                    crate::rule::RuleInfo::Proto(p) => format!("{:?}", p.name),
                    crate::rule::RuleInfo::Intr(i) => format!("Intr({:?})", i),
                };
                let concs: Vec<String> = ru.conclusions.iter()
                    .map(|c| format!("{}({})", crate::fact::fact_tag_name(&c.tag),
                        c.terms.iter().map(|t| format!("{:?}", t)).collect::<Vec<_>>().join(",")))
                    .collect();
                eprintln!("{}  node {:?} = {} concs=[{}]", pad,
                    (id.name, id.idx), info, concs.join("; "));
            }
            eprintln!("{}  eq_store.subst = {:?}", pad, node.sys.eq_store.subst);
            for la in &node.sys.less_atoms {
                eprintln!("{}  less {:?} < {:?}", pad,
                    (la.smaller.name, la.smaller.idx),
                    (la.larger.name, la.larger.idx));
            }
            for e in &node.sys.edges {
                eprintln!("{}  edge {:?} -> {:?}", pad,
                    (e.src.0.name, e.src.0.idx),
                    (e.tgt.0.name, e.tgt.0.idx));
            }
        }
        for (k, c) in &node.children {
            eprintln!("{}case '{}'", pad, k);
            if depth < 9 { print_tree(c, depth + 1); }
        }
    }

    #[test]
    fn probe_two_rules_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/two_rules.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "reachable", h, 200).expect("prove");
        eprintln!("=== two_rules.spthy `reachable` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_two_actions_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/two_actions.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "both_actions", h, 200).expect("prove");
        eprintln!("=== two_actions.spthy `both_actions` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_falsifiable_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/falsifiable.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "never_both", h, 200).expect("prove");
        eprintln!("=== falsifiable.spthy `never_both` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_three_facts_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/three_facts.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "all_three", h, 200).expect("prove");
        eprintln!("=== three_facts.spthy `all_three` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_single_recv_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/single_recv.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "chain", h, 200).expect("prove");
        eprintln!("=== single_recv ===");
        eprintln!("status={:?}", root.status);
    }

    #[test]
    fn probe_injectivity_with_pair_sig() {
        // Probes the `injectivity::injectivity_check` corpus example.
        // Resolves the example via a workspace-relative path computed
        // from CARGO_MANIFEST_DIR (crate lives at crates/tamarin-theory,
        // so the corpus is at ../../tamarin-prover/examples in the
        // submodule); skips gracefully if the example is not present.
        let mp = match maude_path_local() { Some(p) => p, None => return };
        let src = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tamarin-prover/examples/features/injectivity/injectivity.spthy"
        )).unwrap_or_default();
        if src.is_empty() { return; }
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let h = MaudeHandle::start(&mp, pair_maude_sig()).expect("start maude");
        let root = prove_lemma(&pt, "injectivity_check", h, 200).expect("prove");
        eprintln!("injectivity status = {:?}", root.status);
    }

    #[test]
    fn probe_cr_recentalive_with_hashing_sig() {
        // Regression test: with the elaborated MaudeSig (hashing), the
        // simplify loop must converge instead of spinning on
        // already-canonical edges.
        let mp = match maude_path_local() { Some(p) => p, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/CR_external.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
        let sig = elab.signature.maude_sig.clone();
        let h = MaudeHandle::start(&mp, sig).expect("start maude");
        let t0 = std::time::Instant::now();
        let _ = prove_lemma(&pt, "recentalive", h, 200).expect("prove");
        let dt = t0.elapsed();
        // Must complete within a generous bound; the load-bearing
        // assertion is that the simplify loop converges, not the specific
        // timing.
        assert!(dt < std::time::Duration::from_secs(60),
            "recentalive ran {:?}, expected ≤60s (simplify-loop converges)", dt);
    }

    #[test]
    fn probe_sig_minimal_with_hashing_sig() {
        // Try the trivially-true tautology with the elaborated theory's
        // MaudeSig (which adds h/1) instead of pair-only. If this hangs,
        // the goal explosion is reproducible on a near-empty file.
        let mp = match maude_path_local() { Some(p) => p, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/sig_minimal.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
        let sig = elab.signature.maude_sig.clone();
        eprintln!("sig fun_syms count = {}", sig.fun_syms.len());
        for fs in &sig.fun_syms {
            if let tamarin_term::function_symbols::FunSym::NoEq(s) = fs {
                eprintln!("  {} (arity={}, priv={:?}, ctor={:?})",
                    String::from_utf8_lossy(s.name), s.arity, s.privacy, s.constructability);
            }
        }
        let h = MaudeHandle::start(&mp, sig).expect("start maude");
        let root = prove_lemma(&pt, "a_self", h, 50).expect("prove");
        eprintln!("status = {:?}", root.status);
        // The lemma is a tautology; should reach Contradictory after
        // negation reduces to ⊥.
    }

    #[test]
    fn probe_auth_pattern_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/auth_pattern.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "protocol_runs", h, 200).expect("prove");
        eprintln!("=== auth_pattern.spthy ===");
        print_tree(&root, 0);
    }

    #[test]
    fn probe_fresh_ordering_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/fresh_ordering.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "order", h, 200).expect("prove");
        eprintln!("=== fresh_ordering.spthy `order` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_needs_constructor_simple_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/needs_constructor_simple.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "sent_exists", h, 200).expect("prove");
        eprintln!("=== needs_constructor_simple ===");
        eprintln!("status={:?}", root.status);
    }

    #[test]
    fn probe_needs_constructor_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/needs_constructor.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "pair_arrives", h, 2000).expect("prove");
        eprintln!("=== needs_constructor.spthy `pair_arrives` ===");
        eprintln!("status={:?}", root.status);
    }

    /// Smaller test: just receive a fresh that was Out-ed.
    #[test]
    fn probe_recv_one_fresh() {
        let h = match maude() { Some(m) => m, None => return };
        let src = "theory T begin
rule S: [Fr(~k)] --[Sent(~k)]-> [Out(~k)]
rule R: [In(x)] --[Got(x)]-> []
lemma chain: exists-trace \"Ex k #i #j. Sent(k)@i & Got(k)@j\"
end";
        let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&pt, "chain", h, 500).expect("prove");
        eprintln!("=== probe_recv_one_fresh ===");
        eprintln!("status={:?}", root.status);
    }

    #[test]
    fn probe_reuse_lemma() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/reuse_lemma.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let r1 = prove_lemma(&pt, "setup_unique", maude().unwrap(), 200).expect("prove1");
        let r2 = prove_lemma(&pt, "setup_unique_key", h, 200).expect("prove2");
        eprintln!("setup_unique={:?}, setup_unique_key={:?}", r1.status, r2.status);
    }

    #[test]
    fn probe_restriction_unique() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/restriction_unique.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "setup_unique", h, 200).expect("prove");
        eprintln!("=== restriction_unique ===");
        eprintln!("status={:?}", root.status);
        // Diagnostic: count lemmas in the proof tree's leaves.
        fn collect_max_lemmas(n: &super::ProofNode, out: &mut usize) {
            *out = (*out).max(n.sys.lemmas.len());
            for c in n.children.values() { collect_max_lemmas(c, out); }
        }
        let mut max_lemmas = 0;
        collect_max_lemmas(&root, &mut max_lemmas);
        eprintln!("max lemma count seen in tree: {}", max_lemmas);
    }

    #[test]
    fn probe_safety_two_keys_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/safety_two_keys.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "fresh_distinct_times", h, 200).expect("prove");
        eprintln!("=== safety_two_keys.spthy `fresh_distinct_times` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_safety_unique_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/safety_unique.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "setup_unique", h, 200).expect("prove");
        eprintln!("=== safety_unique.spthy `setup_unique` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    /// Web-parity regression: with `set_keep_sys(true)` (what the
    /// interactive server sets at startup), `run_proof_search` must
    /// RETAIN each proof node's constraint `System` instead of dropping
    /// it to `System::default()` (the `--prove` RSS optimisation in
    /// `expand`).  The interactive proof-view snippet renders the
    /// annotated system + applicable proof methods at every proof path,
    /// so an empty root would show a bogus "Constraint System is Solved"
    /// with no formulas (HS keeps a `Just System` on every node).
    #[test]
    fn prove_lemma_keep_sys_retains_node_systems() {
        let h = match maude() { Some(m) => m, None => return };
        let src = r#"
theory T begin
rule R:
  [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]
lemma always_A:
  all-traces
  "All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j"
end
"#;
        crate::constraint::solver::search::set_keep_sys(true);
        let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&pt, "always_A", h, 200).expect("prove");
        // Root = the initial constraint system (the negated goal formula),
        // with the lemma's refined source kind — NOT an empty default.
        assert!(!root.sys.formulas.is_empty(),
            "root node must retain the initial system's formulas");
        assert_eq!(root.sys.source_kind,
            Some(crate::constraint::system::SourceKind::RefinedSources),
            "root system source kind must survive (refined for a non-sources lemma)");
        // Every child must also carry a real system.
        for (name, ch) in &root.children {
            assert!(ch.sys.source_kind.is_some(),
                "child {:?} must retain a real system, not System::default()", name);
        }
    }

    /// Drive the tiny_setup proof and inspect the proof-tree shape.
    /// We expect the search to:
    /// 1. Pick `Induction` (root).
    /// 2. In `non_empty_trace`, decompose Ex → Goal::Action(Setup(_))
    ///    via simplify.
    /// 3. SolveGoal(Action) → instantiates the Setup rule, exploits
    ///    its `Fr(~k)` premise, leaves no further goals.
    /// 4. Status reaches `Solved` (or `Contradictory` for some branches).
    #[test]
    fn prove_lemma_tiny_setup_drives_through_action_goal() {
        let h = match maude() { Some(m) => m, None => return };
        let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
        let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&parser_theory, "trivial", h, 100)
            .expect("prove_lemma should not error");

        // Root method: under the `AvoidInduction` default (exists-trace
        // lemmas), Haskell's `rankProofMethods` tries Simplify first.
        // If Simplify produces non-empty cases (decomposes the formula
        // into goals), that's picked; otherwise we fall through to
        // Induction.  For this trivial existence lemma the Ex is
        // reducible, so Simplify is the root method.  Either is
        // structurally acceptable as long as the proof reaches Solved.
        use crate::constraint::solver::proof_method::ProofMethod;
        use crate::constraint::solver::search::NodeStatus;
        assert!(matches!(root.method,
            ProofMethod::Induction | ProofMethod::Simplify
            | ProofMethod::SolveGoal(_)),
            "expected Simplify/Induction/SolveGoal at root, got {:?}", root.method);
        assert_eq!(root.status, NodeStatus::Solved,
            "expected Solved on tiny_setup, got {:?}", root.status);
    }

    #[test]
    fn prove_lemma_tiny_setup_terminates() {
        let h = match maude() { Some(m) => m, None => return };
        let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
        let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&parser_theory, "trivial", h, 50)
            .expect("prove_lemma should not error");
        // Tamarin's proof is `induction → SOLVED` in the empty branch,
        // and the non_empty branch needs the existential to be
        // decomposed — which produces a Goal::Action. Whatever our
        // verdict, the search must terminate, and the non-trivial
        // branch should reach a method beyond the initial induction.
        use crate::constraint::solver::search::NodeStatus;
        assert!(!matches!(root.status, NodeStatus::Open),
            "search must terminate within budget");
    }

    /// Build a `ProverSession` from theory source for the pre-pass tests.
    fn session_from(src: &str) -> Option<ProverSession> {
        let h = maude()?;
        let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
        ProverSession::build_with_in_file_and_heuristic(
            &pt, h, None, "", CliHeuristic::default(),
            crate::constraint::solver::context::CutStrategy::Dfs,
        ).ok()
    }

    const SHARED_KEY_TWO_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma a: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\"\n\
lemma b: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\"\n\
end";

    /// Two lemmas with the same (empty) `source_key` saturate ONCE in the
    /// pre-pass, seed one cache entry, and a same-key lemma then restores it.
    #[test]
    fn presaturate_dedups_shared_source_key() {
        let session = match session_from(SHARED_KEY_TWO_LEMMAS) { Some(s) => s, None => return };
        // Both lemmas are RefinedSource with no prior `[sources]` lemma, so
        // both carry the identical empty key — one saturation covers both.
        let n = session.presaturate_shared_sources(false, |_| true);
        assert_eq!(n, 1, "two lemmas sharing a key must saturate once");
        assert_eq!(session.source_cache.lock().unwrap().len(), 1,
            "exactly one refined-source set is cached");
        // A fan-out lemma of the same key restores from the pre-seeded cache.
        let lemma_b = session.theory.lookup_lemma("b").expect("lemma b");
        let kind = lemma_source_kind(lemma_b);
        let (mut ctx, key) = session.setup_per_lemma_ctx(lemma_b, "b", kind).expect("ctx");
        let hit = session.restore_or_saturate_sources(&mut ctx, key, false);
        assert!(hit, "lemma b must restore from the pre-seeded shared-key cache");
    }

    /// A lemma that would emit a bare `sorry` (not a `--prove` target and with
    /// no stored proof tree) never saturates in the fan-out, so the pre-pass
    /// must skip it — the spdm121 `--prove=<no match>` regression precedent.
    #[test]
    fn presaturate_skips_bare_sorry_lemmas() {
        let session = match session_from(SHARED_KEY_TWO_LEMMAS) { Some(s) => s, None => return };
        // Freshly parsed lemmas have no stored proof tree; with no target
        // selected they emit a bare sorry and never consult a source.
        let n = session.presaturate_shared_sources(false, |_| false);
        assert_eq!(n, 0, "bare-sorry lemmas must not be pre-saturated");
        assert!(session.source_cache.lock().unwrap().is_empty(),
            "no key is seeded for bare-sorry lemmas");
        // The SAME lemmas do saturate once they are `--prove` targets.
        let n2 = session.presaturate_shared_sources(false, |_| true);
        assert_eq!(n2, 1, "targeted lemmas saturate their shared key once");
    }

    /// `cache_disabled` (`TAM_RS_NO_SOURCE_CACHE`) bypasses the pre-pass
    /// entirely, falling back to the per-lemma compute path.
    #[test]
    fn presaturate_disabled_is_noop() {
        let session = match session_from(SHARED_KEY_TWO_LEMMAS) { Some(s) => s, None => return };
        let n = session.presaturate_shared_sources(true, |_| true);
        assert_eq!(n, 0, "the disabled pre-pass saturates nothing");
        assert!(session.source_cache.lock().unwrap().is_empty(),
            "the disabled pre-pass seeds no cache entries");
    }
}
