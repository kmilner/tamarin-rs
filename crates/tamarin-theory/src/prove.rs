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
//! Returns `Err` on lemma-lookup / guarded-conversion failures.

use crate::constraint::solver::context::{IntrRuleCache, ProofContext};
use crate::constraint::solver::search::{run_proof_search, ProofNode};
use crate::constraint::system::{formula_to_system, SourceKind};
use crate::guarded::{formula_to_guarded, Guarded};
use crate::theory::OpenProtoRule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    LemmaNotFound(String),
    Guarded(String),
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

/// Resolve Oracle/OracleSmart rankings parsed from an in-file `heuristic:` or
/// lemma attribute. A standalone oracle token carries `takeDirectory inFile`
/// as its workDir; an `o`/`O` inside a compact letter run carries no workDir.
///
/// Mirrors HS `oraclePath oracle = fromMaybe "." workDir </> normalise relPath`
/// (System.hs:576-577) with `workDir = takeDirectory inFile`.  Producing the
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
            GoalRanking::Oracle {
                oracle_path,
                display_path,
                ..
            }
            | GoalRanking::OracleSmart {
                oracle_path,
                display_path,
                ..
            } => {
                let ranking_work_dir = display_path.is_none().then_some(work_dir.as_str());
                *oracle_path = resolve_oracle_path(oracle_path, ranking_work_dir);
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
///   4. CLI rankings have no workDir. `defaultOracleNames` preserves that
///      absence for both default and explicit names, so execution is
///      CWD-relative.
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
    // Default `.oracle` name (HS `defaultOracleNames`) for oracle rankings
    // that carried no inline `"path"` AND get no `--oraclename`.
    for r in rankings.iter_mut() {
        match r {
            GoalRanking::Oracle {
                oracle_path,
                display_path,
                quit_on_empty,
                ..
            }
            | GoalRanking::OracleSmart {
                oracle_path,
                display_path,
                quit_on_empty,
                ..
            } => {
                if let Some(name) = oraclename {
                    *oracle_path = name.to_string();
                    *oracle_path = resolve_oracle_path(oracle_path, None);
                    if display_path.is_some() {
                        *display_path = Some(oracle_path.clone());
                    }
                } else {
                    // CLI rankings are parsed with `workDir = Nothing` in HS.
                    // `defaultOracleNames` fills only the relative name and
                    // preserves that absent workDir, so execution is CWD-relative.
                    *oracle_path = resolve_oracle_path(oracle_path, None);
                    if display_path.is_some() {
                        *display_path = Some(oracle_path.clone());
                    }
                }
                // Step 5: --oracle-only quitOnEmpty (Theory/Proof.hs:713-714).
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

/// One theory-level cache entry of refined source cases — the result of
/// a `ctx.ensure_saturated()` pass, snapshotted per `Source` by goal.
/// Keyed (in [`ProverSession::source_cache`]) by the SORTED set of
/// `[sources]`-lemma names folded into `typing_assumptions`.
///
/// Why this is safe to share across lemmas (HS computes
/// `_crcRefinedSources` ONCE per `ClosedRuleCache` — RuleItem.hs:64-69
/// for the field, `closeRuleCache` at CloseRule.hs:402-404,427 for the
/// single computation — and `proveTheory` reuses that one cache for
/// every lemma, CloseRule.hs:148-163):
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
    /// Per source: (goal join-key, refined case list).
    sources: Vec<(
        crate::constraint::constraints::Goal,
        crate::constraint::solver::sources::SourceCases,
    )>,
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
/// template `ProofContext` recovers that; per-lemma we still run the
/// lightweight `ensure_saturated` (each lemma needs its own
/// `typing_assumptions`-refined source cases).
pub struct ProverSession {
    /// Elaborated typed theory.  Used to look up lemmas, restrictions,
    /// rules, heuristic.  Shares the caller's allocation (`Arc`); the
    /// session never mutates it.
    pub theory: std::sync::Arc<crate::theory::Theory>,
    /// CLI `--heuristic`/`--oraclename`/`--oracle-only` (HS `AutoProver`
    /// fields).  When `cli_heuristic.raw` is `Some`, it OVERRIDES the per-lemma
    /// / theory heuristic for EVERY lemma (HS `selectHeuristic`,
    /// Theory/Proof.hs:705-716, see line 707).
    cli_heuristic: CliHeuristic,
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
    /// Shared refined-source cache (see [`CachedSources`]).
    /// Keyed by the sorted `[sources]`-lemma name set.  Populated lazily
    /// on the first lemma of each key; reused by all later lemmas with the
    /// same key (every normal lemma shares the all-sources key), letting
    /// the expensive `saturate_sources_with_simp` pass run once per theory
    /// instead of once per lemma.  `Mutex` keeps the session `&self`.
    // keyed source cache (Mutex); source-key->CachedSources
    // lookup, never iterated; std kept (byte-inert) — order never reaches output.
    #[allow(clippy::disallowed_types)]
    source_cache: std::sync::Mutex<std::collections::HashMap<Vec<String>, CachedSources>>,
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
pub fn lemma_source_kind(lemma: &crate::theory::Lemma) -> SourceKind {
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
pub fn induction_hint(
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
/// HS keeps ONE implementation of the gather, inside `mkSystem`
/// (CloseRule.hs:167-188#mkSystem).  The batch prover reaches it through
/// `proveTheory` (CloseRule.hs:162#mkSystem); the interactive server reaches
/// the same function through `modifyLemmaProof`
/// (Prover.hs:349-360#modifyLemmaProof, see line 358) and through its own
/// `import Prover (mkSystem)` (Handler.hs:160#mkSystem) at
/// Handler.hs:205#mkSystem and Handler.hs:265#mkSystem.  The web server crate
/// calls this function so that the port keeps one implementation too.
pub fn gather_reusable_lemmas(
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

/// Gather the typing assumptions folded into a lemma's refined-source
/// computation, plus the SORTED `source_key` identifying that computation
/// (the set of `[sources]`-lemma names used; callers off the session cache
/// path ignore the key).
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
            if prior.name == lemma_name {
                continue;
            }
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
            source_key.push(prior.name.clone());
        }
    }
    source_key.sort();
    Ok((typing_assumptions, source_key))
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

/// Resolve the goal-ranking heuristic for a lemma, mirroring HS
/// `selectHeuristic prover ctx = apDefaultHeuristic prover <|> L.get
/// pcHeuristic ctx` (Theory/Proof.hs:706-707): the CLI `--heuristic`
/// (`apDefaultHeuristic`) OVERRIDES the per-lemma / theory heuristic when
/// present.  Otherwise fall back to per-lemma `[heuristic=..]` > theory-level
/// `heuristic:` > None (`getProofContext.specifiedHeuristic`,
/// ClosedTheory.hs:123-131); `None` becomes `SmartRanking False` downstream.
/// The lemma attribute keeps its source text, so it is parsed here, with
/// `{name}` tactic rankings resolved against `tactics`; the theory's header
/// is already parsed.  Both have their oracle paths resolved against the
/// theory dir.
pub fn resolve_heuristic(
    cli: &CliHeuristic,
    lemma: &crate::theory::Lemma,
    theory_heuristic: &[crate::constraint::solver::goals::GoalRanking],
    tactics: &[crate::tactic::Tactic],
    in_file: &str,
) -> Option<Vec<crate::constraint::solver::goals::GoalRanking>> {
    if let Some(rankings) = resolve_cli_heuristic(cli, in_file, tactics) {
        return Some(rankings);
    }
    let lemma_heuristic: Option<&str> = lemma.attributes.iter().find_map(|a| match a {
        crate::theory::LemmaAttr::Heuristic(s) => Some(s.as_str()),
        _ => None,
    });
    let mut rankings = match lemma_heuristic {
        Some(h) => {
            crate::constraint::solver::goals::parse_heuristic_str_with_tactics(h, in_file, tactics)
        }
        None if !theory_heuristic.is_empty() => theory_heuristic.to_vec(),
        None => return None,
    };
    prepend_theory_dir_to_oracle_paths(&mut rankings, in_file);
    Some(rankings)
}

impl ProverSession {
    /// Read the theory-wide, unspecialised context built by this session.
    ///
    /// This is intended for web views which only inspect immutable
    /// close-time data. Lemma proof operations must use
    /// [`Self::context_for_lemma`].
    pub fn template_context(&self) -> &ProofContext {
        &self.template_ctx
    }

    /// Build the same per-lemma context used by batch proving, including
    /// refined-source cache restoration/saturation.
    pub fn context_for_lemma(&self, lemma_name: &str) -> Result<ProofContext, ProveError> {
        let lemma = self
            .theory
            .lookup_lemma(lemma_name)
            .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;
        let source_kind = lemma_source_kind(lemma);
        let (mut ctx, source_key) = self.setup_per_lemma_ctx(lemma, lemma_name, source_kind)?;
        let cache_disabled = tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
        self.restore_or_saturate_sources(&mut ctx, source_key, cache_disabled);
        ctx.use_induction = induction_hint(lemma);
        Ok(ctx)
    }

    /// Build a disposable raw-source context for interactive source views.
    /// The session template stays pristine for later lemma specialisation;
    /// materialised cases are reused through the session source cache.
    pub fn context_for_raw_sources(&self) -> ProofContext {
        let mut ctx = self.template_ctx.clone();
        ctx.maude = ctx.maude.with_fresh_counter_from(0);
        ctx.maude
            .ensure_above(self.setup_counter_before.saturating_sub(1));
        let cache_disabled = tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
        self.restore_or_saturate_sources(&mut ctx, Vec::new(), cache_disabled);
        ctx
    }

    /// Compute the `--precompute-only` stats (HS `prettyPrecomputation`,
    /// ClosedTheory.hs:553-575).  Forces the template's source cells
    /// (`ensure_saturated`), so it is intended for the precompute-only
    /// path where the session serves no proving afterwards.
    pub fn precomputation_stats(&self) -> Result<PrecomputationStats, ProveError> {
        use crate::constraint::solver::sources::{
            refine_with_source_asms, unsolved_chain_constraints, Source,
        };
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

        // Raw = the saturated precompute (HS `precomputeSources`,
        // CloseRule.hs:426).  The template ctx carries no typing
        // assumptions, so `ensure_saturated` stops at the raw saturate
        // and the cells hold exactly `getSource RawSource thy`.
        self.template_ctx.ensure_saturated();
        let chains_of = |sources: &[Source]| -> usize {
            sources
                .iter()
                .map(|s| {
                    s.cases_or_empty()
                        .iter()
                        .map(|(_, sys)| unsolved_chain_constraints(sys))
                        .sum::<usize>()
                })
                .sum()
        };
        let raw_cases = self.template_ctx.full_sources.len();
        let raw_chains = chains_of(&self.template_ctx.full_sources);

        // Refined = `refineWithSourceAsms typAsms` over the raw set
        // (CloseRule.hs:427).  `typAsms` = every `[sources]` AllTraces
        // lemma's guarded formula ("" matches no lemma name, so nothing
        // is excluded).  With no such lemma HS's refine is a plain
        // relabel (Sources.hs:458-459) — counts identical to raw.
        let (typ_asms, _key) =
            gather_typing_assumptions(&self.theory, "", SourceKind::RefinedSources)?;
        let (refined_cases, refined_chains) = if typ_asms.is_empty() {
            (raw_cases, raw_chains)
        } else {
            let refined = refine_with_source_asms(
                self.template_ctx.full_sources.to_vec(),
                &typ_asms,
                &self.template_ctx,
            );
            (refined.len(), chains_of(&refined))
        };

        Ok(PrecomputationStats {
            rules,
            raw_cases,
            raw_chains,
            refined_cases,
            refined_chains,
            has_restrictions: !self.restrictions.is_empty(),
        })
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
    // keyed source cache constructor; lookup-only map;
    // std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    pub fn build_with_heuristic(
        theory: std::sync::Arc<crate::theory::Theory>,
        maude: tamarin_term::maude_proc::MaudeHandle,
        pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
        cli_heuristic: CliHeuristic,
        cut: crate::constraint::solver::context::CutStrategy,
        ndc_cache: Option<&IntrRuleCache>,
    ) -> Result<Self, ProveError> {
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
            cli_heuristic,
            cut,
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
        ctx.maude
            .ensure_above(self.setup_counter_before.saturating_sub(1));
        ctx.is_exists_trace = matches!(
            lemma.trace_quantifier,
            crate::theory::TraceQuantifier::ExistsTrace,
        );
        // HS `apCut` is theory-global (one `TheoryLoadOptions.stopOnTrace`),
        // so stamp the session's cut onto every per-lemma context.
        ctx.cut = self.cut;
        let session_in_file = self.theory.in_file.as_str();
        ctx.heuristic = resolve_heuristic(
            &self.cli_heuristic,
            lemma,
            &theory.heuristic,
            &theory.tactic,
            session_in_file,
        );
        ctx.lemma_name = lemma_name.to_string();
        ctx.theory_file = session_in_file.to_string();
        let (typing_assumptions, source_key) =
            gather_typing_assumptions(theory, lemma_name, lemma_source_kind)?;
        ctx.typing_assumptions = typing_assumptions;
        Ok((ctx, source_key))
    }

    /// Restore the refined source cases for `source_key` from the session
    /// cache, or saturate them and (when the fresh-counter delta is 0) write
    /// them back.  Returns whether the cache was hit.  Shared by both session
    /// entry points.  The caller must have already gated out the
    /// `will_emit_bare_sorry` case (which forces no source and must skip this
    /// entirely).
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
                for src in ctx.full_sources.iter() {
                    if let Some((_, cases)) = entry.sources.iter().find(|(g, _)| *g == src.goal) {
                        src.cases_set_shared(std::sync::Arc::clone(cases));
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
            // Only cache results that allocated NO fresh vars — those are the
            // ones safe to replay byte-identically (counter unperturbed, cases
            // carry only template-sourced var indices).  Sources lemmas (delta
            // > 0) keep recomputing.
            if !cache_disabled && delta == 0 {
                let snapshot: Vec<_> = ctx
                    .full_sources
                    .iter()
                    .map(|s| (s.goal.clone(), s.cases_shared_or_empty()))
                    .collect();
                self.source_cache
                    .lock()
                    .unwrap()
                    .entry(source_key)
                    .or_insert(CachedSources { sources: snapshot });
            }
        }
        cache_hit
    }

    /// Pre-fan-out single-flight saturation: compute each DISTINCT
    /// `source_key`'s refined-source cases ONCE (sequentially over keys) and
    /// seed the session `source_cache` BEFORE the per-lemma proof fan-out, so
    /// the concurrent fan-out lemmas all take the cache-hit restore arm of
    /// [`Self::restore_or_saturate_sources`] rather than each recomputing the
    /// identical `saturate_sources_with_simp` pass.  HS computes
    /// `_crcRefinedSources` ONCE per `ClosedRuleCache` (RuleItem.hs:64-69;
    /// `closeRuleCache` at CloseRule.hs:402-404,427) and `proveTheory` reuses
    /// that one cache for every lemma (CloseRule.hs:148-163); without this
    /// pre-pass the
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
    /// user-fn-symbol thread-locals for its guarded-conversion calls (same
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
        if cache_disabled {
            return 0;
        }
        let mut seen: tamarin_utils::FastSet<Vec<String>> = tamarin_utils::FastSet::default();
        let mut saturated = 0usize;
        for lemma in self.theory.lemmas() {
            // Fan-out saturation gate (see `will_emit_bare_sorry`): a lemma
            // consults its source cases — and so saturates its key — iff it is
            // a `--prove` target OR carries a stored proof skeleton that
            // `check_and_extend` replays.
            if !(is_target(lemma.name.as_str()) || lemma.proof.is_some()) {
                continue;
            }
            let kind = lemma_source_kind(lemma);
            // Compute the key (guarded-convert the prior `[sources]` lemmas)
            // BEFORE the deep `template_ctx` clone, so a repeat key skips
            // without cloning.  A non-guardable `[sources]`/typing formula
            // errors here; the fan-out reproduces the identical per-lemma
            // abort, so skip it in the pre-pass rather than preempting it.
            let source_key =
                match gather_typing_assumptions(&self.theory, lemma.name.as_str(), kind) {
                    Ok((_, key)) => key,
                    Err(_) => continue,
                };
            if !seen.insert(source_key) {
                continue;
            }
            // First lemma of this key: build its per-lemma ctx and saturate +
            // seed through the shared `delta == 0` gate.  The cache starts
            // empty and `seen` skips repeats, so this always misses and
            // computes.
            let (mut ctx, key) = match self.setup_per_lemma_ctx(lemma, lemma.name.as_str(), kind) {
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
/// counter base, same `typing_assumptions` gate, same saturation +
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
    let ctx = session.context_for_lemma(lemma_name)?;
    Ok(run_proof_search(&ctx, sys, proof_bound))
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
    // the pre-session prove_lemma_with_pool_file_heuristic path.
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
    // fields.  See `setup_per_lemma_ctx`.  Each clone's `ensure_saturated`
    // populates ITS OWN cells from ITS OWN `typing_assumptions`, so there is
    // no cross-lemma contamination.
    let (mut ctx, source_key) =
        session.setup_per_lemma_ctx(lemma, lemma_name, lemma_source_kind)?;
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
    let will_emit_bare_sorry = !auto_prove && lemma.proof.is_none();
    // Reuse a previously-computed refined-source set when one
    // exists for this exact `source_key`.  See [`CachedSources`] for why a
    // hit is byte-identical (only delta==0 results are ever cached).
    let cache_disabled = tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
    if !will_emit_bare_sorry {
        // A bare-sorry lemma skips the eager saturate + cache entirely — it
        // forces no source case (matches HS's lazy `pcSources`).  The lazy
        // `cases(ctx)` hook stays in place for any path that does consult a
        // source; for the bare-sorry early return it never fires.
        session.restore_or_saturate_sources(&mut ctx, source_key, cache_disabled);
    }
    ctx.use_induction = induction_hint(lemma);
    // Skeleton replay: same logic as in `prove_lemma_with_pool_file_heuristic`.
    if let Some(tree) = &lemma.proof {
        if auto_prove {
            return Ok(crate::replay::replace_sorry_prove(
                &ctx,
                sys,
                tree,
                proof_bound,
            ));
        } else {
            // Non-target lemma: HS close-time check-and-extend
            // replay, no auto-proving of open leaves.
            return Ok(crate::replay::check_and_extend(
                &ctx,
                sys,
                tree,
                proof_bound,
            ));
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
    let r = run_proof_search(&ctx, sys, proof_bound);
    Ok(r)
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
    theory: &crate::theory::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_with_pool_file_heuristic(
        theory,
        lemma_name,
        maude,
        None,
        proof_bound,
        "",
        &CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    )
}

/// Like [`prove_lemma`] but accepts a `MaudePool` (consulted ONLY inside
/// `par_iter` closures — see `sources.rs::saturate_sources_with_simp_opt`),
/// the source file path (oracle path resolution, HS `oraclePath oracle =
/// takeDirectory inFile </> normalise relPath`, System.hs:576-577,
/// Theory/Text/Parser.hs:309), and the CLI
/// `--heuristic`/`--oraclename`/`--oracle-only` (HS `AutoProver`).  This is
/// the per-lemma (non-session) fallback path; when `cli_heuristic.raw` is
/// `Some` it OVERRIDES the per-lemma / theory heuristic (HS `selectHeuristic`,
/// Theory/Proof.hs:705-716, see line 707).  `ndc_cache` is the theory's
/// once-per-load NDC-checked intruder cache, injected into the context so
/// the fallback path never re-runs the check; the borrowed handle lets a
/// whole per-lemma loop share one cache allocation.
pub fn prove_lemma_with_pool_file_heuristic(
    theory: &crate::theory::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    proof_bound: usize,
    in_file: &str,
    cli_heuristic: &CliHeuristic,
    cut: crate::constraint::solver::context::CutStrategy,
    ndc_cache: Option<&IntrRuleCache>,
) -> Result<ProofNode, ProveError> {
    // in_file for oracle path resolution (HS Theory/Text/Parser.hs:309);
    // the theory's own path fills in when the caller passes none.
    let in_file = if in_file.is_empty() {
        theory.in_file.as_str()
    } else {
        in_file
    };

    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;

    let g = guarded_or_error(&lemma.formula)?;

    // Per-lemma source kind (HS `lemmaSourceKind`,
    // lib/theory/src/Lemma.hs:38-41): RawSource
    // for `[sources]`-tagged lemmas, RefinedSource for all others.  Stamped
    // onto the initial system's `sSourceKind` (CloseRule.hs:167-188, see line 175).
    let lemma_source_kind = lemma_source_kind(lemma);

    // Convert restrictions to guarded.  HS `mkSystem` maps
    // `formulaToGuarded_ = either (error . render) id` (CloseRule.hs:167-188, see line 174,
    // Guarded.hs:466-467) over restriction formulas — it ABORTS on a
    // non-guardable restriction rather than silently dropping it (a silent
    // drop weakens the constraint set and could let an unsound proof
    // through).  Mirror the fail-loud behaviour: propagate `ProveError`.
    let mut restrictions: Vec<Guarded> = Vec::new();
    for r in theory.restrictions() {
        restrictions.push(guarded_or_error(&r.formula)?);
    }

    // `[reuse]` lemmas declared BEFORE this one are gathered separately
    // and pushed into `sLemmas` (not `sFormulas`) after building the
    // system. Mirrors Haskell's `mkSystem` (CloseRule.hs:167-188):
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
    let reuse_lemmas = gather_reusable_lemmas(theory, lemma_name, lemma_source_kind)?;

    let mut sys = formula_to_system(
        restrictions.clone(),
        lemma_source_kind,
        lemma.trace_quantifier,
        &g,
    );
    // Haskell's `addLemmas`: push reuse lemmas into `sLemmas`. They
    // become drivers for `insertImpliedFormulas` (which iterates
    // `sFormulas ++ sLemmas`) but are excluded from `ginduct`.
    //
    // Note: `[sources]`-tagged lemmas are NOT added to sLemmas.
    // Haskell's `gatherReusableLemmas` (CloseRule.hs:167-188, see line 184) filters to
    // `[reuse]` only; `[sources]` lemmas are consumed solely by
    // `refineWithSourceAsms` at precompute time (driven below by the
    // `ctx.ensure_saturated()` call over `ctx.full_sources`).
    sys.insert_lemmas(reuse_lemmas);

    // Bridge the elaborated theory's rules into the proof context.
    let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
    // HS `setforcedInjectiveFacts {L_PureState, L_CellLocked}`
    // (lib/sapic/src/Sapic.hs:84):
    // force those facts injective when the state-channel optimisation is on.
    let forced_injective_facts: Vec<crate::fact::FactTag> = if theory.options.state_channel_opt() {
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
        maude,
        pool,
        rules,
        restrictions.clone(),
        &forced_injective_facts,
        ndc_cache.cloned(),
    );
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
    // ... apDefaultHeuristic prover <|> L.get pcHeuristic ctx`
    // (Theory/Proof.hs:705-716, see line 707):
    // the CLI `--heuristic` (apDefaultHeuristic) OVERRIDES the per-lemma /
    // theory heuristic when present.  Otherwise (`getProofContext.
    // specifiedHeuristic`, ClosedTheory.hs:123-131): per-lemma `[heuristic=..]`
    // > theory-level `heuristic:` > None.  `None` falls back to `SmartRanking
    // False` in `rank_goals_with` (= HS's `defaultHeuristic False`).  The
    // whole ranking list is kept for round-robin scheduling (HS
    // `roundRobinHeuristic`/`useHeuristic`, ProofMethod.hs:576-595).
    ctx.heuristic = resolve_heuristic(
        cli_heuristic,
        lemma,
        &theory.heuristic,
        &theory.tactic,
        in_file,
    );
    // Set lemma_name and theory_file on ctx for oracle invocation.
    ctx.lemma_name = lemma_name.to_string();
    ctx.theory_file = in_file.to_string();

    // `refineWithSourceAsms`: prune precomputed source cases by
    // assumptions from `[sources]`-tagged lemmas.  Mirrors Haskell's
    // `refineWithSourceAsms` — typing-style protocols rely on these
    // assumptions to filter out spurious decryption cases that would
    // otherwise surface as false counterexamples in our search.
    // HS-faithful per-lemma RAW-vs-REFINED selection (ClosedTheory.hs:116-118,
    // lib/theory/src/Lemma.hs:38-41, see line 40): `[sources]` lemmas
    // (RawSource) use the RAW precomputed sources — `refineWithSourceAsms` is NEVER applied to them — so they
    // carry NO typing assumptions (empty list => `ensure_saturated` skips the
    // refine).  All other lemmas (RefinedSource) fold in every prior
    // `[sources]`-lemma assumption (HS `typAsms`, CloseRule.hs:117-119).
    // The proved lemma is excluded (self-refinement is circular); the
    // sorted source_key is unused off the session path.
    let (typing_assumptions, _source_key) =
        gather_typing_assumptions(theory, lemma_name, lemma_source_kind)?;
    // HS-faithful saturation: store typing assumptions, then eagerly
    // run `ensure_saturated` (which applies `refine_with_source_asms`
    // with the assumptions just set).  This matches HS's
    // `refineWithSourceAsms` call site emitting `[Saturating Sources]
    // Done` at theory-close time — Rust does it per-lemma because the
    // ctx is per-lemma.
    ctx.typing_assumptions = typing_assumptions;
    ctx.ensure_saturated();
    ctx.use_induction = induction_hint(lemma);

    // HS-faithful `replaceSorryProver` (Theory/Proof.hs:642-650):
    // when the lemma carries a parsed skeleton, walk that skeleton and
    // invoke the auto-prover only at `by sorry` leaves.  Otherwise (no
    // skeleton or parser couldn't structure it) fall through to the
    // pre-existing auto-prover-from-scratch behavior.
    if let Some(tree) = &lemma.proof {
        return Ok(crate::replay::replace_sorry_prove(
            &ctx,
            sys,
            tree,
            proof_bound,
        ));
    }
    let r = run_proof_search(&ctx, sys, proof_bound);
    Ok(r)
}

#[cfg(test)]
#[path = "prove_tests.rs"]
mod tests;
