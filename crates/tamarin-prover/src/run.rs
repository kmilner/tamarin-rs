// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Batch-mode driver: turn parsed [`Args`] into proof attempts and
//! produce an analyzed-theory output document.
//!
//! Mirrors `Main.Mode.Batch.run` in spirit — load each input file,
//! parse + elaborate, optionally prove lemmas, and emit either to
//! stdout or to `--output=` / `-O DIR`. The analyzed-theory output is
//! rendered via `pretty_theory::pretty_closed_theory`, the port of
//! Haskell's `prettyClosedTheory`, which interleaves the theory items
//! with their per-lemma proof/summary annotations.
//!
//! `--parse-only` stops after parsing and prints the pretty-printed OPEN
//! theory to stdout (HS `prettyOpenTheory`, Batch.hs — always stdout,
//! `-o`/`-O` are ignored there); `-m`/`--output-module` (Batch.hs)
//! translates and CHECKS but never closes: per-module preprocessing
//! (`processOpenTheory` — identity for `spthy`, SAPIC typing for
//! `spthytyped`, full translation + lemma filter for `msr`), the full
//! wellformedness/NDC/derivation stage, then the OPEN print
//! (`prettyOpenTheoryByModule`) with the wf + version comment blocks, docs
//! deferred until every file is processed; all other modes close the theory
//! and go through `prettyClosedTheory`.

// Sanctioned stdout path: this is the batch-mode CLI output module — it emits
// the analyzed-theory document and progress lines to stdout by design (the
// byte-parity surface itself).  `println!`/`print!` are the intended output
// mechanism here, so the `disallowed_macros` convention freeze is allowed for
// this file.  (Library crates stay guarded; only the binary's output paths and
// examples carry this allow.)
#![allow(clippy::disallowed_macros)]

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::constraint::solver::search::{ProofNode, ProofStatus};
use tamarin_theory::constraint::system::System;
use tamarin_theory::elaborate::elaborate_with_in_file;
use tamarin_theory::module::ModuleType;

use tamarin_server::theory_loader::{
    lemma_matches, load_theory, read_config_block, LoadError, TheoryLoadOptions, TheoryPipeline,
    TranslateModule,
};

use crate::cli::{Args, Subcommand};

#[derive(Debug, PartialEq, Eq)]
pub enum RunError {
    /// An ordinary CLI/runtime error, rendered with the port's `error:` prefix.
    Regular(String),
    /// An exception which escapes to Haskell's top-level runtime handler.
    GhcException(String),
    /// A fatal wellformedness report, printed on stdout by Batch.handleError.
    UnsupportedInput {
        in_file: String,
        report: tamarin_theory::wellformedness::WfReport,
    },
    /// HS `WarningError` under `--quit-on-warning`, printed by
    /// [`print_quit_on_warning`].
    Warning(tamarin_theory::wellformedness::WfReport),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Regular(message) | Self::GhcException(message) => f.write_str(message),
            Self::UnsupportedInput { in_file, report } => write!(
                f,
                "unsupported rule semantics in {in_file}:\n{}",
                tamarin_theory::pretty_theory::render_console_wf_error_report(report)
            ),
            Self::Warning(report) => f.write_str(
                &tamarin_theory::pretty_theory::render_wf_error_report(report),
            ),
        }
    }
}

impl std::error::Error for RunError {}

impl RunError {
    /// The batch rendering of a shared-pipeline failure for `in_file`.
    fn load(error: LoadError, in_file: &str) -> Self {
        match error {
            LoadError::Exception(message) => Self::GhcException(message),
            LoadError::UnsupportedInput(report) => Self::UnsupportedInput {
                in_file: in_file.to_owned(),
                report,
            },
            LoadError::Warning(report) => Self::Warning(report),
            LoadError::Other(message) => Self::Regular(message),
        }
    }
}

/// Batch.hs `handleError (WarningError report)`: the report block on stdout,
/// then `die`.
pub fn print_quit_on_warning(report: &tamarin_theory::wellformedness::WfReport) {
    let report = tamarin_theory::pretty_theory::render_wf_error_report(report);
    // `putStrLn . renderDoc $ vcat` of: blank, the WARNING header, blank,
    // the report, blank.
    println!(
        "\nWARNING: the following wellformedness checks failed!\n\n{}\n",
        report.trim_end_matches('\n')
    );
    eprintln!("quit-on-warning mode selected - aborting on wellformedness errors.");
}

/// Batch.hs `handleError (UnsupportedInputError report)`: the report goes to
/// stdout; only the abort message goes to stderr. No theory or summary follows.
pub fn print_unsupported_input(in_file: &str, report: &tamarin_theory::wellformedness::WfReport) {
    let report = tamarin_theory::pretty_theory::render_console_wf_error_report(report);
    println!(
        "\nERROR: unsupported rule semantics in {in_file}:\n\n{}\n",
        report.trim_end_matches('\n')
    );
    eprintln!("Unsupported rule semantics - aborting before proof search.");
}

impl From<tamarin_theory::prove::ProveError> for RunError {
    fn from(error: tamarin_theory::prove::ProveError) -> Self {
        match error {
            tamarin_theory::prove::ProveError::Guarded(message) => Self::GhcException(message),
            tamarin_theory::prove::ProveError::Ranking(error) => {
                Self::GhcException(error.to_string())
            }
            tamarin_theory::prove::ProveError::InvalidHeuristic(message) => Self::Regular(message),
            other => Self::Regular(other.to_string()),
        }
    }
}

impl From<tamarin_theory::tools::rule_variants::VariantsError> for RunError {
    fn from(error: tamarin_theory::tools::rule_variants::VariantsError) -> Self {
        Self::Regular(error.to_string())
    }
}

/// HS `showProofStatus` (Theory/Proof.hs). An all-traces lemma is the
/// `ExistsNoTrace` system quantifier, an exists-trace lemma `ExistsSomeTrace`.
fn show_proof_status(exists_trace: bool, status: ProofStatus) -> &'static str {
    match (exists_trace, status) {
        (false, ProofStatus::TraceFound) => "falsified - found trace",
        (false, ProofStatus::Complete) => "verified",
        (true, ProofStatus::Complete) => "falsified - no trace found",
        (true, ProofStatus::TraceFound) => "verified",
        (_, ProofStatus::Unfinishable) => "analysis cannot be finished",
        (_, ProofStatus::Incomplete) => "analysis incomplete",
        (_, ProofStatus::Undetermined) => "analysis undetermined",
        (_, ProofStatus::Invalidated) => "proof has been invalidated",
    }
}

/// One `prettyClosedSummary` line (ClosedTheory.hs):
/// `<lemma> (<quantifier>): <showProofStatus> (<N> steps)`.
fn format_lemma_summary_line(r: &LemmaResult) -> String {
    let quantifier = if r.exists_trace {
        "exists-trace"
    } else {
        "all-traces"
    };
    format!(
        "{} ({}): {} ({} steps)",
        r.name,
        quantifier,
        show_proof_status(r.exists_trace, r.status),
        r.proof_steps
    )
}

#[derive(Debug, Clone)]
pub(crate) struct LemmaResult {
    pub name: String,
    /// HS `getProofStatus` folded over the whole proof tree.
    pub status: ProofStatus,
    /// Proof-tree node count — matches HS's "(N steps)" in
    /// `--prove` output (`foldProof proofStepSummary`, ClosedTheory.hs,
    /// summing one per ProofStep via `foldProof`, Theory/Proof.hs).
    pub proof_steps: usize,
    /// `true` for `exists-trace` lemmas, `false` for `all-traces`.
    /// Drives the trace-quantifier label in the summary.
    pub exists_trace: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct FileResult {
    pub in_file: String,
    pub out_file: Option<String>,
    pub results: Vec<LemmaResult>,
    pub elapsed_ms: u128,
    /// Number of wellformedness check failures for this file.
    /// Surfaced in `summary of summaries` per HS's format.
    pub wf_count: usize,
}

/// Top-level dispatch. Reports any error as a `RunError` and returns
/// the exit code the binary should use (0 for success).
///
/// `--help` and `--version` never reach this point — clap answers them
/// inside `parse_args`' error path.
pub fn run(args: &Args) -> Result<i32, RunError> {
    match args.subcommand {
        Subcommand::Batch => run_batch(args),
        Subcommand::Interactive => run_interactive(args),
        Subcommand::Variants => run_variants(args),
        Subcommand::Test => run_test(args),
        Subcommand::InputManifest => run_input_manifest(args),
    }
}

fn run_input_manifest(args: &Args) -> Result<i32, RunError> {
    use std::collections::BTreeSet;
    use std::os::unix::ffi::OsStrExt;
    use std::path::Path;
    use tamarin_parser::ast::TheoryItem;
    use tamarin_parser::{LemmaAttr, ParseErrorKind};

    // Manifest rows are line-oriented, so raw paths cannot safely contain a
    // tab or newline. Prefix a byte-for-byte hex encoding with `x:`; the shared
    // shell reader decodes it only when a path is actually consumed. Besides
    // making the delimiters unambiguous, this avoids `Path::display()`'s lossy
    // replacement of non-UTF-8 Unix path bytes.
    let path_field = |path: &Path| {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let bytes = path.as_os_str().as_bytes();
        let mut encoded = String::with_capacity(2 + bytes.len() * 2);
        encoded.push_str("x:");
        for &byte in bytes {
            encoded.push(HEX[(byte >> 4) as usize] as char);
            encoded.push(HEX[(byte & 0x0f) as usize] as char);
        }
        encoded
    };

    let root = PathBuf::from(
        args.in_files
            .first()
            .ok_or_else(|| RunError::Regular("input-manifest requires one file".into()))?,
    );
    let source = fs::read_to_string(&root)
        .map_err(|error| RunError::Regular(format!("{}: {error}", root.display())))?;
    let flags: Vec<&str> = args.defines.iter().map(String::as_str).collect();
    let (theory, aliases) = match tamarin_parser::parse_theory_with_manifest(
        &source,
        &flags,
        root.clone(),
        args.diff,
    ) {
        Ok(manifest) => manifest,
        Err(error) => {
            eprintln!(
                "error: {}",
                error.render_plain_with_source(&root.to_string_lossy(), &source)
            );
            // The cache harness may conservatively scan rejected syntax (3),
            // but missing/unreadable active inputs (1) must stop cache creation.
            // Keep this protocol in sync with scripts/gate_common.sh.
            return Ok(match error.kind() {
                ParseErrorKind::IncludeIo { .. } => 1,
                _ => 3,
            });
        }
    };

    let has_lemmas = theory.items.iter().any(|item| {
        matches!(
            item,
            TheoryItem::Lemma(_)
                | TheoryItem::DiffLemma(_)
                | TheoryItem::AccLemma(_)
                | TheoryItem::EquivLemma(_, _)
                | TheoryItem::DiffEquivLemma(_)
        )
    });
    println!("M\thas_lemmas\t{}", u8::from(has_lemmas));

    let mut seen_sources = BTreeSet::new();
    for alias in &aliases {
        let row = format!(
            "S\t{}\t{}",
            path_field(&alias.physical),
            alias.staged.as_deref().map_or_else(String::new, path_field)
        );
        if seen_sources.insert(row.clone()) {
            println!("{row}");
        }
    }

    let mut oracle_rows = BTreeSet::new();
    let mut add_heuristic = |raw: &str, source_file: Option<&str>| {
        let source_file = source_file.unwrap_or_else(|| root.to_str().unwrap_or_default());
        for oracle in tamarin_theory::prove::oracle_paths_for_heuristic(raw, source_file, None) {
            let oracle = PathBuf::from(oracle);
            if !oracle.is_file() {
                continue;
            }
            let source_aliases = aliases
                .iter()
                .filter(|alias| alias.physical == Path::new(source_file));
            for alias in source_aliases {
                let staged = staged_oracle_path(alias, &oracle);
                oracle_rows.insert(format!(
                    "O\t{}\t{}",
                    path_field(&oracle),
                    staged.as_deref().map_or_else(String::new, path_field)
                ));
            }
        }
    };
    if args.heuristic.is_none() {
        for item in &theory.items {
            match item {
                TheoryItem::Heuristic { raw, source_file } => {
                    add_heuristic(raw, source_file.as_deref())
                }
                TheoryItem::Lemma(lemma) => {
                    for attr in &lemma.attributes {
                        if let LemmaAttr::Heuristic(raw) = attr {
                            add_heuristic(raw, lemma.source_file.as_deref());
                        }
                    }
                }
                TheoryItem::DiffLemma(lemma) => {
                    for attr in &lemma.attributes {
                        if let LemmaAttr::Heuristic(raw) = attr {
                            add_heuristic(raw, lemma.source_file.as_deref());
                        }
                    }
                }
                TheoryItem::AccLemma(lemma) => {
                    for attr in &lemma.attributes {
                        if let LemmaAttr::Heuristic(raw) = attr {
                            add_heuristic(raw, lemma.source_file.as_deref());
                        }
                    }
                }
                _ => {}
            }
        }
    }
    if let Some(raw) = args.heuristic.as_deref() {
        let root_alias = aliases.first();
        let has_oracle_override = args
            .oracle_name
            .as_deref()
            .is_some_and(|name| !name.is_empty());
        for oracle in tamarin_theory::prove::oracle_paths_for_heuristic(
            raw,
            root.to_str().unwrap_or_default(),
            args.oracle_name.as_deref(),
        ) {
            let oracle = PathBuf::from(oracle);
            if oracle.is_file() {
                let staged = if has_oracle_override {
                    None
                } else {
                    root_alias.and_then(|alias| staged_oracle_path(alias, &oracle))
                };
                oracle_rows.insert(format!(
                    "O\t{}\t{}",
                    path_field(&oracle),
                    staged.as_deref().map_or_else(String::new, path_field)
                ));
            }
        }
    }
    for row in oracle_rows {
        println!("{row}");
    }
    Ok(0)
}

fn staged_oracle_path(
    source: &tamarin_parser::InputAlias,
    oracle: &std::path::Path,
) -> Option<PathBuf> {
    let staged = source.staged.as_ref()?;
    let source_dir = source.physical.parent()?;
    let relative = oracle.strip_prefix(source_dir).ok()?;
    Some(
        staged
            .parent()
            .unwrap_or_else(|| std::path::Path::new(""))
            .join(relative),
    )
}

/// Check Maude and GraphViz availability (HS Main.Mode.Test); the Haskell
/// unification suite is not run here. Qualify batch-tamarin's required
/// `All tests successful` marker to identify which checks ran.
/// Return 0 if both tools pass, otherwise 1.
fn run_test(args: &Args) -> Result<i32, RunError> {
    println!("Self-testing the tamarin-prover installation.\n");
    println!("*** Testing the availability of the required tools ***");
    // HS `ensureMaude` (Test.hs) runs its two probes through `testProcess`,
    // so the whole maude block lands on STDERR — the `***` topic lines around
    // it are the only part of this section on stdout.  A maude that cannot be
    // started aborts the run inside the probe, so `success_maude` is `false`
    // only for a maude that ran but failed a check.
    let (success_maude, _) = ensure_maude(args, &maude_invocation_path(args));
    // Test.hs — a bare `putStrLn ""` separates the two tool blocks.
    println!();
    // HS `ensureGraphVizDot` (Test.hs) reads `dotPath`
    // (Environment.hs): the `--with-dot` value, else the bare `"dot"`.
    let dot_cmd = args.dot_path.as_deref().unwrap_or("dot");
    // HS `successGraphVizDot = isJust maybeSuccessGraphVizDot` (Test.hs):
    // a missing/unavailable `dot` is a test FAILURE, not a silent skip.
    let success_graphviz = crate::probe::ensure_graph_viz_dot(dot_cmd).is_some();
    println!("\n*** TEST SUMMARY ***");
    // HS `success = successMaude && successGraphVizDot && successTerm`
    // (Test.hs); on failure it warns and `exitFailure` (Test.hs).
    if success_maude && success_graphviz {
        println!("All tests successful (Maude/GraphViz availability checks only).");
        println!("The tamarin-prover should work as intended.\n");
        // Test.hs is `putStrLn "\n           :-) happy proving (-:\n"`, so
        // the smiley is followed by a blank line — the leading one is already
        // supplied by the line above.
        println!("           :-) happy proving (-:\n");
        Ok(0)
    } else {
        println!("\nWARNING: Some tests failed.");
        println!("The tamarin-prover might NOT WORK AS INTENDED.\n");
        Ok(1)
    }
}

/// `tamarin-prover variants` — mirror HS's `Main.Mode.Intruder.run`.
/// HS dumps the DH-intruder rule variants (the `c_exp`, `c_inv`,
/// `c_mult`, `c_one`, etc. rules) then the BP-intruder variants, without
/// needing a `.spthy` file (Intruder.hs).
///
/// We mirror the DH half: spin up Maude with `dh_maude_sig()`, generate the
/// rules via [`tamarin_theory::intruder_rules::dh_intruder_rules`] with the
/// HS-hardcoded `False` flag, and pretty-print each rule in HS's
/// `rule (modulo AC) NAME:` shape, and the BP half the same way on a second
/// handle (see body for why the two signatures stay separate).
/// `-O`/`--Output` additionally writes the two blocks to files, as HS's
/// `writeRules` does (see the tail of the body).  Both blocks and the stdout
/// dump are byte-identical to the oracle's — 5811 / 10426 / 16238 bytes.
fn run_variants(args: &Args) -> Result<i32, RunError> {
    let maude_path = maude_invocation_path(args);
    // HS `Main.Mode.Intruder.run` runs `ensureMaude` BEFORE it starts either
    // handle (Intruder.hs), so the tool block — stderr only, the rule dump
    // alone goes to stdout — precedes any Maude spawn, and a maude that cannot
    // be started aborts here rather than in `MaudeHandle::start`.  The verdict
    // is discarded (`_ <- ensureMaude as`).
    let _ = ensure_maude(args, &maude_path);
    let start_maude = |sig| {
        MaudeHandle::start(&maude_path, sig).map_err(|e| {
            RunError::Regular(format!(
                "failed to start maude at {:?}: {:?}",
                maude_path, e
            ))
        })
    };
    // HS `Main.Mode.Intruder.run` (Intruder.hs) starts TWO SEPARATE
    // Maude handles — one on `dhMaudeSig`, one on `bpMaudeSig` — and
    // generates `dhIntruderRules False` then `bpIntruderRules False`, then
    // emits `dhS ++ bpS`.  We mirror the DH handle on `dh_maude_sig()` ALONE
    // (NOT merged with bp): merging exposes pmult/em to Maude during the DH
    // variant query and could perturb DH variant enumeration.  The DH
    // generator is hardcoded `False` in HS, not the --diff flag, so we pass
    // `false`.
    let maude = start_maude(tamarin_term::maude_sig::dh_maude_sig())?;
    // HS `Main.Mode.Intruder.run` (Intruder.hs) generates BOTH the DH
    // and the bilinear-pairing variants and emits `dhS ++ bpS`:
    //   - DH: `dhIntruderRules False` (runtime, via Maude).  RS's runtime
    //     generator is byte-faithful (exactly 51 rules); `MaudeHandle::variants`
    //     applies `remove_renamings` to drop redundant identity-variants.
    //   - BP: `bpIntruderRules False` (runtime).  Like HS
    //     (Intruder.hs), we start a SECOND Maude handle on
    //     `bp_maude_sig()` and generate the 74 BP rules at runtime via
    //     `bp_intruder_rules(false, ..)`.  This tracks the CURRENT Maude
    //     rather than the stale cached `data/intruder_variants_bp.spthy`
    //     (which production proving still parses via
    //     `mk_bp_intruder_variants`); HS's `variants` command likewise
    //     generates BP at runtime, so the two stay byte-identical.
    let dh_rules = tamarin_theory::intruder_rules::dh_intruder_rules(&maude);
    let bp_maude = start_maude(tamarin_term::maude_sig::bp_maude_sig())?;
    let bp_rules = tamarin_theory::intruder_rules::bp_intruder_rules(&bp_maude);
    // HS `putStrLn (dhS ++ bpS)` where each block is `renderDoc .
    // prettyIntruderVariants` (Theory/Model/Rule.hs):
    // blank-line-separated `rule (modulo AC) NAME:` rules with HughesPJ body
    // wrapping (`sep`/`fsep` at the standard width) and NO trailing newline —
    // so the DH and BP blocks abut (the DH `d_inv` body directly precedes the
    // BP `c_pmult` header with no separating newline).  `putStrLn` appends the
    // single trailing newline.
    let dh_s = tamarin_theory::pretty_formula::pretty_intruder_variants(&dh_rules);
    let bp_s = tamarin_theory::pretty_formula::pretty_intruder_variants(&bp_rules);
    print!("{}{}", dh_s, bp_s);
    println!();
    // HS `writeRules` (Intruder.hs): with `-O`/`--Output` the two blocks
    // ALSO go to `<outDir>/data/intruder_variants_{dh,bp}.spthy`
    // (`dhIntruderVariantsFile`/`bpIntruderVariantsFile`,
    // TheoryLoader.hs) — each block alone, without the newline
    // `putStrLn` gave the stdout dump.  `writeFileWithDirs` creates the `data`
    // level; a bare `-O` records `""`, which `</>` resolves against the cwd.
    if let Some(out_dir) = &args.output_dir {
        for (rel, body) in [
            ("data/intruder_variants_dh.spthy", &dh_s),
            ("data/intruder_variants_bp.spthy", &bp_s),
        ] {
            let path = PathBuf::from(out_dir).join(rel);
            if let Err(io) = write_file_with_dirs(&path.to_string_lossy(), body) {
                return Err(RunError::GhcException(io));
            }
        }
    }
    Ok(0)
}

/// Default port matches Haskell `Web.Settings.defaultPort` (3001).
const DEFAULT_INTERACTIVE_PORT: u16 = 3001;

/// Run the interactive web UI. Mirrors `Main.Mode.Interactive.run`:
/// builds a [`tamarin_server::ServerConfig`] from the CLI flags, eagerly
/// loads any positional `.spthy` files into the theory store, and serves
/// HTTP until SIGINT/SIGTERM. Returns 0 on graceful shutdown.
fn run_interactive(args: &Args) -> Result<i32, RunError> {
    use std::net::{IpAddr, Ipv4Addr, SocketAddr};

    if args.in_files.is_empty() {
        return Err(RunError::Regular(
            "no working directory specified — pass a directory of .spthy \
             files or one or more .spthy paths"
                .to_string(),
        ));
    }
    // Validate the workdir/theories before any tool probe runs (a typo'd
    // path should fail fast, not after the maude banner).
    for f in &args.in_files {
        if !std::path::Path::new(f).exists() {
            return Err(RunError::Regular(format!(
                "directory '{}' does not exist",
                f
            )));
        }
    }

    init_rayon_pool(args);

    // Haskell defaults: 3001 on 127.0.0.1.  clap has already parsed
    // `--port` as a `u16` (an unreadable value is a usage error).
    let port = args.port.unwrap_or(DEFAULT_INTERACTIVE_PORT);

    // `--interface` accepts a literal IP address. Haskell's `*4` / `*` /
    // `*6` magic strings bind to all interfaces; mirror those.
    let iface_str = args
        .interface
        .clone()
        .unwrap_or_else(|| "127.0.0.1".to_string());
    let ip: IpAddr = match iface_str.as_str() {
        "*" | "*4" => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        "*6" => IpAddr::V6(std::net::Ipv6Addr::UNSPECIFIED),
        other => other.parse::<IpAddr>().map_err(|e| {
            RunError::Regular(format!(
                "could not parse --interface={:?} as an IP address: {}\n\
                 Use --interface=\"*4\" to bind to all IPv4 interfaces.",
                other, e,
            ))
        })?,
    };
    let bind_addr = SocketAddr::new(ip, port);

    // Use the embedded GUI unless the user explicitly overrides it.
    let data_dir = args.data_dir.clone().map(PathBuf::from);
    let frontend_dist = data_dir
        .as_deref()
        .and_then(tamarin_server::handlers::static_files::frontend_dist);

    let mut cfg =
        tamarin_server::ServerConfig::new(bind_addr, data_dir, maude_invocation_path(args));
    // HS `withWebUI` closes over the CLI's `TheoryLoadOptions` for every web
    // load: startup, upload and reload (Interactive.hs). `--bound` reaches
    // nothing: every autoprove route replaces `apBound` with the URL's
    // (`getAutoProverR`'s `adapt`, Web/Handler.hs).
    cfg.load = mk_theory_load_options(args, cfg.load.maude_path.clone())?;
    // One best-effort collection after Stop completes proof cleanup.
    cfg.cancel_cleanup = Some(|| {
        // Initialize the cleanup thread's heap before collecting.
        // SAFETY: the process main heap remains valid; collection preserves live
        // allocations and attempts to purge shared arenas.
        unsafe { rustfs_mimalloc_sys::mi_heap_collect(rustfs_mimalloc_sys::mi_heap_main(), true) }
    });
    cfg.frontend_dist = frontend_dist;
    // `--with-dot` / `--with-json` — HS stores `readOutputCommand as`
    // (Environment.hs) as `WebUI.outputCmd` (Interactive.hs,
    // Web/Types.hs); the graph route then spawns `ocGraphCommand` —
    // `dot` args for `OutDot` (Web/Theory.hs), `<cmd> <img>
    // <json>` for `OutJSON` (Web/Theory.hs).  `--with-json` wins
    // when both are given, exactly as `readOutputCommand` prefers it.
    cfg.dot_path = args.dot_path.clone().unwrap_or_else(|| "dot".to_string());
    cfg.json_path = args.json_path.clone();

    // Positional args are theory files (Haskell uses a working
    // directory, but we accept either: a single dir arg, or one-or-more
    // .spthy paths).
    let theory_paths: Vec<PathBuf> = collect_theory_paths(&args.in_files)?;

    // HS interactive runs the tool checks BEFORE the banner
    // (Interactive.hs): `ensureMaudeAndGetVersion` prints the
    // maude block (Console.hs) and `ensureGraphVizDot` the
    // GraphViz block (Environment.hs), both on stderr.  Neither is
    // gated on any flag — `--quiet` leaves them in place (see `Args::quiet`).
    // The version data feeds HS's `__versionPrettyPrint__` argument, which
    // this port's web UI does not surface, so only the probe's stderr and its
    // abort-on-missing-maude matter here.
    let _ = ensure_maude(args, &cfg.load.maude_path);
    // HS picks the graph-tool check by `(readOutputCommand as).ocFormat`
    // (Interactive.hs): `--with-json` selects `ensureGraphCommand`
    // (Environment.hs) and the `GraphViz tool:` block does not run at
    // all; otherwise `ensureGraphVizDot` (Environment.hs) runs.  Both
    // results are discarded (`_ <-`), so an unavailable tool never aborts
    // startup.  `--with-json` also overrides `--with-dot` (Environment.hs).
    let dot_cmd = args.dot_path.as_deref().unwrap_or("dot");
    if let Some(json_cmd) = args.json_path.as_deref() {
        let _ = crate::probe::ensure_graph_command(json_cmd);
    } else {
        let _ = crate::probe::ensure_graph_viz_dot(dot_cmd);
    }

    // HS startup banner (Interactive.hs) — stdout (`putStrLn`),
    // including the "Loading the security protocol theories" line and
    // the trailing blank line (`intercalate "\n" [.., ""]` plus
    // putStrLn's newline).  HS shows `workDir </> "*.spthy"`; we accept
    // dir-or-files, so a single dir arg renders HS-style and explicit
    // file paths are listed verbatim.
    let loading_what = match &args.in_files[..] {
        [one] if std::path::Path::new(one).is_dir() => {
            format!("{}", std::path::Path::new(one).join("*.spthy").display())
        }
        files => files.join(", "),
    };
    // The banner's URL is HS `serverUrl` (Interactive.hs): the
    // INTERFACE string with the `*`/`*4`/`*6` wildcards displayed as
    // 127.0.0.1 — not the bind address, whose host would render as 0.0.0.0
    // and whose port is the `Word16` truncation.
    let display_host = match iface_str.as_str() {
        "*" | "*4" | "*6" => "127.0.0.1",
        other => other,
    };
    println!(
        "The server is starting up on port {}.\nBrowse to http://{}:{} once the server is ready.\n\nLoading the security protocol theories '{}' ...\n",
        port, display_host, port, loading_what,
    );

    // Spin up a tokio runtime and run the server. We use a multi-thread
    // runtime so background `spawn_blocking` proof tasks don't park the
    // single executor thread.
    //
    // `thread_stack_size`: the web constraint-system pane is rendered as
    // ONE HughesPJ Doc (HS `prettyNonGraphSystem = vsep …`), and the
    // eager Doc builders (`beside`/`aboveNest`) recurse along the left
    // operand's token spine — depth scales with the pane size.  GHC grows
    // its stack on demand; tokio's default 2 MiB worker stacks do not, and
    // overflowed on fact-heavy panes (UM_three_pass).  64 MiB is reserved
    // virtual address space only (committed on use), applied to both
    // worker and `spawn_blocking` threads.
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(64 * 1024 * 1024)
        .build()
        .map_err(|e| RunError::Regular(format!("failed to build tokio runtime: {}", e)))?;
    match runtime.block_on(tamarin_server::serve(cfg, theory_paths)) {
        Ok(()) => Ok(0),
        // `serve` printed the report and the abort message.
        Err(e) if e.is::<tamarin_server::QuitOnWarning>() => Ok(1),
        Err(e) => Err(RunError::Regular(format!("server error: {}", e))),
    }
}

/// Expand the positional input list into a list of `.spthy` files.
/// Haskell's interactive mode takes a single working directory; we
/// accept either a directory (whose `.spthy` files we glob) or any
/// number of `.spthy` files (the path Tamarin batch mode uses).
fn collect_theory_paths(in_files: &[String]) -> Result<Vec<std::path::PathBuf>, RunError> {
    let mut out: Vec<PathBuf> = Vec::new();
    for f in in_files {
        let p = PathBuf::from(f);
        if p.is_dir() {
            let entries = std::fs::read_dir(&p).map_err(|e| {
                RunError::Regular(format!("could not read directory {}: {}", p.display(), e))
            })?;
            for e in entries.flatten() {
                let ep = e.path();
                if ep.extension().and_then(|s| s.to_str()) == Some("spthy") {
                    out.push(ep);
                }
            }
        } else {
            out.push(p);
        }
    }
    out.sort();
    Ok(out)
}

/// The effective per-theory cut strategy: the CLI `--stop-on-trace` wins;
/// with the flag absent the theory's `configuration:` block is consulted
/// (HS `configStopOnTrace` precedence, TheoryLoader.hs).  An
/// unreadable block value is an error — reported immediately and plainly,
/// not with HS's deferred `error` choreography.
fn effective_cut(
    opts: &TheoryLoadOptions,
    block: &tamarin_theory::prove::ConfigBlock,
) -> Result<tamarin_theory::constraint::solver::context::CutStrategy, RunError> {
    use tamarin_theory::constraint::solver::context::CutStrategy;
    if !opts.prove_mode {
        return Ok(CutStrategy::Dfs);
    }
    match opts.stop_on_trace {
        Some(cut) => Ok(cut),
        None => match block.stop_on_trace.as_deref() {
            Some(raw) => tamarin_theory::prove::parse_stop_on_trace(raw)
                .map_err(|e| RunError::Regular(format!("configuration block: {}", e))),
            None => Ok(CutStrategy::Dfs),
        },
    }
}

/// Map a CLI `--stop-on-trace` value to its `CutStrategy`.
fn stop_on_trace_cut(
    s: &crate::cli::StopOnTrace,
) -> tamarin_theory::constraint::solver::context::CutStrategy {
    use tamarin_theory::constraint::solver::context::CutStrategy;
    match s {
        crate::cli::StopOnTrace::Dfs => CutStrategy::Dfs,
        crate::cli::StopOnTrace::SeqDfs => CutStrategy::SeqDfs,
        crate::cli::StopOnTrace::Bfs => CutStrategy::Bfs,
        crate::cli::StopOnTrace::Sorry => CutStrategy::AfterSorry,
        crate::cli::StopOnTrace::None => CutStrategy::Nothing,
    }
}

/// HS `ensureMaude` (Console.hs) on the binary this run invokes — the
/// probe every mode but `--parse-only` runs first.
///
/// The name HS reports is `maudePath as` (Console.hs):
/// the `--with-maude` value, else the bare `"maude"` it lets `PATH` resolve.
/// The port resolves that default to an absolute path of its own
/// ([`default_maude_path`]) but still reports the basename HS would print, so
/// only which of two identical binaries is spawned differs.
///
/// `maude_path` is [`maude_invocation_path`]'s answer, taken as a parameter so
/// a caller that already resolved it (resolving the default probes the
/// filesystem) does not pay for it twice.
fn ensure_maude(args: &Args, maude_path: &str) -> (bool, String) {
    let reported: &str = if args.maude_path.is_some() {
        maude_path
    } else {
        std::path::Path::new(maude_path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(maude_path)
    };
    crate::probe::ensure_maude(reported, maude_path)
}

/// The maude binary this run invokes: the `--with-maude` path when given,
/// else the probed default.  HS `ensureMaude` reads the same `maudePath`
/// for both the version check and every later maude spawn (Console.hs), so the reported version is always the invoked binary's.
fn maude_invocation_path(args: &Args) -> String {
    args.maude_path.clone().unwrap_or_else(default_maude_path)
}

/// Report a failed input-file read the way GHC's runtime does.
///
/// HS never guards the read: `openFile` throws an IOException that escapes to
/// the runtime, which writes `tamarin-prover: <path>: openFile: <reason>` (the
/// IOException `Show` instance, GHC.IO.Exception) to stderr and exits 1.
///
/// A directory is the one reason GHC does not take from the errno: `openFile`
/// checks the file type itself and raises `InappropriateType` with the
/// hand-written description `is a directory` (GHC.IO.FD), where the write
/// side's EISDIR carries `strerror`'s capitalised `Is a directory`.  Every
/// other reason is the shared errno rendering — [`io_exception_reason`].
fn open_file_error(in_file: &str, e: &std::io::Error) -> RunError {
    let reason = if e.kind() == std::io::ErrorKind::IsADirectory {
        "inappropriate type (is a directory)".to_string()
    } else {
        io_exception_reason(e)
    };
    RunError::GhcException(format!("{in_file}: openFile: {reason}"))
}

/// Report a non-UTF-8 input the way GHC's runtime does.
///
/// The file OPENED, so this failure is not `openFile`'s but the decoder's,
/// raised from `hGetContents` and naming the first byte it rejected in decimal
/// (GHC.IO.Encoding.Failure).  `valid_up_to` indexes exactly that byte — the
/// start of the offending sequence, so a truncated `c3 28` reports 195.
fn decode_error(in_file: &str, e: &std::string::FromUtf8Error) -> RunError {
    let bad = e
        .as_bytes()
        .get(e.utf8_error().valid_up_to())
        .copied()
        .unwrap_or_default();
    RunError::GhcException(format!(
        "{in_file}: hGetContents: invalid argument \
         (cannot decode byte sequence starting from {bad})"
    ))
}

/// HS `mkOutPath`'s miss — `-o=` with no `-O` — `die`s with this exact line
/// (Batch.hs) instead of falling back to stdout: the line on stderr,
/// stdout empty, exit 1.  Returns that exit code for the caller to propagate.
fn missing_output_path() -> i32 {
    eprintln!("Please specify a valid output file/directory");
    1
}

/// GHC's `show` for an `IOException` that escapes an unguarded file write:
/// `<path>: <op>: <description> (<strerror>)` (the `Show IOException`
/// instance, GHC.IO.Exception).  `op` is the frame that opened the handle —
/// `withFile` for `writeFile`, `withBinaryFile` for `BL.writeFile`, and
/// `createDirectory` for `createDirectoryIfMissing`.
///
/// `<description>` is `Show IOErrorType` of the type `errnoToIOError` picks
/// for the errno (Foreign.C.Error), and the parenthesised tail is
/// `strerror(errno)` — the very text Rust's `Display` prints ahead of its own
/// ` (os error N)` suffix, which GHC has no counterpart for.  An errno outside
/// the table keeps Rust's message whole, suffix included.
fn write_io_exception(path: &str, op: &str, e: &std::io::Error) -> String {
    format!("{path}: {op}: {}", io_exception_reason(e))
}

/// The `<description> (<strerror>)` tail of an `IOException`'s `show` — see
/// [`write_io_exception`], whose two halves this is the errno-derived one of.
/// Shared with [`open_file_error`], which prefixes the same tail with
/// its own `openFile` frame.
///
/// The errnos remain explicit because GHC's buckets differ from Rust's
/// `ErrorKind` classifications (for example EROFS and ELOOP).
fn io_exception_reason(e: &std::io::Error) -> String {
    let errno = e.raw_os_error();
    // Named constants rather than literals: ENAMETOOLONG, ELOOP and EDQUOT
    // have different numbers on Linux and the BSDs (36/40/122 against 63/62/69
    // on macOS), so a literal table silently stops matching off-Linux and the
    // reason falls back to Rust's own message instead of GHC's.  GHC resolves
    // the same names through the platform's `errno.h`.
    let ioe_type = match errno {
        Some(libc::EPERM) | Some(libc::EACCES) | Some(libc::EROFS) => Some("permission denied"),
        Some(libc::ENOENT) => Some("does not exist"),
        Some(libc::EEXIST) => Some("already exists"),
        Some(libc::ENOTDIR) | Some(libc::EISDIR) => Some("inappropriate type"),
        Some(libc::EINVAL) | Some(libc::ENAMETOOLONG) | Some(libc::ELOOP) => {
            Some("invalid argument")
        }
        Some(libc::ENOSPC) | Some(libc::EMLINK) | Some(libc::EDQUOT) => Some("resource exhausted"),
        _ => None,
    };
    let rust = e.to_string();
    match (ioe_type, errno) {
        (Some(t), Some(n)) => {
            let strerror = rust
                .strip_suffix(&format!(" (os error {n})"))
                .unwrap_or(&rust);
            format!("{t} ({strerror})")
        }
        _ => rust,
    }
}

/// HS `writeFileWithDirs` (Main/Utils.hs): create the target's parent
/// directories, then write `body` VERBATIM.  Neither step is guarded there,
/// so a failure escapes as the [`write_io_exception`] text — returned here for
/// the caller to report as a [`RunError::GhcException`].
fn write_file_with_dirs(path: &str, body: &str) -> Result<(), String> {
    if let Some(parent) = std::path::Path::new(path).parent()
        && !parent.as_os_str().is_empty()
    {
        create_dirs(parent).map_err(|(dir, e)| {
            write_io_exception(&dir.to_string_lossy(), "createDirectory", &e)
        })?;
    }
    fs::write(path, body).map_err(|e| write_io_exception(path, "withFile", &e))
}

/// `createDirectoryIfMissing True` (directory's `createDirs`): try the DEEPEST
/// directory first and walk UP only while `mkdir` reports `ENOENT`, retrying
/// each level on the way back down.  The `IOException` a failure raises names
/// the level that raised it, so that order decides which ancestor the report
/// blames: a missing chain blames the shallowest unreachable link, while an
/// `EEXIST`/`ENOTDIR` stops at the level that hit it.  `std`'s
/// `create_dir_all` walks the same levels but re-raises under the path it was
/// called with, which is why it cannot serve here.
///
/// `Err` carries that level alongside its error.
fn create_dirs(dir: &std::path::Path) -> Result<(), (std::path::PathBuf, std::io::Error)> {
    let blame = |e: std::io::Error| (dir.to_path_buf(), e);
    match create_dir_once(dir) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            // `parents` bottoms out at the first path component, whose
            // `createDir` gets no not-exist handler and reports itself.
            match dir.parent() {
                Some(p) if !p.as_os_str().is_empty() => create_dirs(p)?,
                _ => return Err(blame(e)),
            }
            create_dir_once(dir).map_err(blame)
        }
        r => r.map_err(blame),
    }
}

/// `createDir`'s own `mkdir` step: an `EEXIST` naming a path that is already a
/// directory is swallowed — `mkdir` cannot tell an existing directory from an
/// existing file, so the type is checked here — and every other outcome is the
/// caller's.  `EEXIST` is the only errno that reaches the check: Linux reports
/// an existing directory that way even when its parent denies write.
fn create_dir_once(dir: &std::path::Path) -> std::io::Result<()> {
    fs::create_dir(dir).or_else(|e| {
        if e.kind() == std::io::ErrorKind::AlreadyExists && dir.is_dir() {
            Ok(())
        } else {
            Err(e)
        }
    })
}

/// The `GraphOptions` every `outputTraces` graph is rendered with.  The label
/// [`trace_label_options`] builds ADVERTISES these very values (the
/// `SL2-AS0-CL0-A1-C1-NB` segment), so the renderers and the label read one
/// source: two independent reads can drift into a label that describes a body
/// it did not produce.
fn trace_graph_options() -> tamarin_theory::constraint::system::graph::GraphOptions {
    tamarin_theory::constraint::system::graph::GraphOptions::default()
}

/// HS `traceLabelOptions` (Batch.hs): the fixed middle segment of an
/// `outputTraces` label.  Batch always feeds it `defaultGraphOptions`
/// (Graph.hs) and `defaultDotOptions` (Theory/Constraint/System/Dot.hs) — Batch.hs
/// hard-codes both, so no CLI flag (`--no-compress` included) can move it.
/// Every input is a compile-time constant, so the segment is derived once and
/// reused by every label the run emits.
fn trace_label_options() -> &'static str {
    static LABEL: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    LABEL.get_or_init(|| {
        let o = trace_graph_options();
        // `show graphOptions._goSimplificationLevel` — the derived `Show`, i.e.
        // the bare constructor name `SL0`..`SL3`.
        let s1 = format!("{:?}", o.simplification_level);
        let s2 = if o.show_auto_source { "AS1" } else { "AS0" };
        let s3 = if o.clustering_similar_names {
            "CL1"
        } else {
            "CL0"
        };
        let s4 = if o.abbreviate { "A1" } else { "A0" };
        let s5 = if o.compress { "C1" } else { "C0" };
        // `_doNodeStyle`: RS has no `DotOptions` type — `constraint::system::dot` renders
        // `CompactBoringNodes` unconditionally, which is `defaultDotOptions`.
        let s6 = "NB";
        format!("{}-{}-{}-{}-{}-{}", s1, s2, s3, s4, s5, s6)
    })
}

/// HS `traceOutputLabel` (Batch.hs): the digraph id (`--output-dot`)
/// and `jgLabel` (`--output-json`) of one serialised trace.
///
/// There is NO separator between the lemma name and the proof path
/// (Batch.hs is `++ lemma._lName ++ intercalate "-" proofPath`).
/// HS's single-case methods use the empty case name, so the path's first
/// element is usually `""` and a real label reads `…_<lemma>-<case1>-<case2>`.
fn trace_output_label(theory_name: &str, lemma_name: &str, path: &[String]) -> String {
    format!(
        "trace_{}_{}_{}{}",
        theory_name,
        trace_label_options(),
        lemma_name,
        path.join("-")
    )
}

/// Did the run ask for serialised traces?  Gates the three places
/// `--output-dot` / `--output-json` cost anything: the solver's solved-`System`
/// retention, the per-lemma collection in the prove loop, and
/// [`write_output_traces`] itself.
fn wants_trace_output(args: &Args) -> bool {
    args.trace_dot.is_some() || args.trace_json.is_some()
}

/// HS `outputTraces`' two writers (Batch.hs), run once per input file
/// inside `processThy`'s close-and-prove branch.  `writeFile`/`BL.writeFile`
/// TRUNCATE, so with several input files the LAST file's traces survive.
///
/// `traces` is the labelled `(label, system)` list in HS's order: lemma
/// declaration order, then `proofSystems`' case-name walk.
/// Both writers stream graph-by-graph so peak RSS tracks the largest single
/// graph, not the total output (HS's DOT side is a lazily-consumed
/// `writeFile`; its JSON side materialises the document, which the port
/// need not reproduce — the bytes are identical either way).
fn write_output_traces(args: &Args, traces: Vec<(String, System)>) -> Result<(), String> {
    use std::io::Write;
    use tamarin_theory::constraint::system::graph::RenderSystem;
    let opts = trace_graph_options();
    if let Some(p) = &args.trace_dot {
        // `intercalate "\n" $ map serializeDot labelledSystems`.  Each graph
        // already ends `}\n`, so the separator yields one blank line between
        // graphs; an empty list is `intercalate "\n" [] == ""`, a 0-byte file.
        // `writeFile` — an unguarded text write, so a failure escapes as
        // GHC's `withFile` IOException.
        let io = |e: &std::io::Error| write_io_exception(p, "withFile", e);
        let mut w = std::io::BufWriter::new(fs::File::create(p).map_err(|e| io(&e))?);
        for (i, (label, sys)) in traces.iter().enumerate() {
            let graph =
                tamarin_theory::constraint::system::dot::system_to_dot_labeled(sys, &opts, label);
            if i > 0 {
                w.write_all(b"\n").map_err(|e| io(&e))?;
            }
            w.write_all(graph.as_bytes()).map_err(|e| io(&e))?;
        }
        w.flush().map_err(|e| io(&e))?;
    }
    if let Some(p) = &args.trace_json {
        // `sequentsToJSONPretty graphOptions labelledSystems` — one document
        // for all graphs; an empty list is `{"graphs": []}`.  Batch does NOT
        // pre-abbreviate the systems (that is the web proof route only), so
        // the systems cross the clone-for-render boundary as they are; each
        // is converted and dropped per graph inside the streaming writer.
        // `BL.writeFile` — the lazy-ByteString writer, whose IOException
        // names `withBinaryFile` instead.
        let io = |e: &std::io::Error| write_io_exception(p, "withBinaryFile", e);
        let mut w = std::io::BufWriter::new(fs::File::create(p).map_err(|e| io(&e))?);
        tamarin_theory::constraint::system::json::write_sequents_json_pretty(
            &opts,
            traces
                .into_iter()
                .map(|(label, sys)| (label, RenderSystem::from_prover(sys))),
            &mut w,
        )
        .map_err(|e| io(&e))?;
        w.flush().map_err(|e| io(&e))?;
    }
    Ok(())
}

/// Port of HS `mkTheoryLoadOptions` (TheoryLoader.hs): assemble the
/// record from the parsed argv.  clap has already validated the enum-valued
/// flags (`--stop-on-trace`, `--partial-evaluation`, `--output-module`), so
/// only `--heuristic=` (an explicit empty ranking) can still fail here.
fn mk_theory_load_options(args: &Args, maude_path: String) -> Result<TheoryLoadOptions, RunError> {
    // A bare `--heuristic` records the default `s` in `parse_args`; only an
    // explicit `--heuristic=` reaches this with an empty ranking list.
    if args.heuristic.as_deref() == Some("") {
        return Err(RunError::Regular(
            "--heuristic: at least one ranking must be given".to_string(),
        ));
    }
    let output_module = args.output_module.as_deref().map(|s| {
        ModuleType::from_show(s)
            .expect("clap's --output-module value_parser matches ModuleType's show strings")
    });
    Ok(TheoryLoadOptions {
        prove_mode: args.prove_mode,
        lemma_names: args.lemma_names.clone(),
        stop_on_trace: args.stop_on_trace.as_ref().map(stop_on_trace_cut),
        heuristic: args.heuristic.clone(),
        oracle_name: args.oracle_name.clone(),
        oracle_only: args.oracle_only,
        // TheoryLoader.hs: `SUMMARY` → `Summary`, `VERBOSE` → `Tracing`.
        partial_evaluation: args.partial_evaluation.as_ref().map(|style| match style {
            crate::cli::PartialEval::Summary => tamarin_theory::tools::EvaluationStyle::Summary,
            crate::cli::PartialEval::Verbose => tamarin_theory::tools::EvaluationStyle::Tracing,
        }),
        defines: args.defines.clone(),
        quit_on_warning: args.quit_on_warning,
        auto_sources: args.auto_sources,
        output_module,
        parse_only_mode: args.parse_only,
        precompute_only_mode: args.precompute_only,
        derivation_checks: args
            .derivcheck_timeout
            .unwrap_or(tamarin_theory::deriv_check::DerivCheckTimeout::DEFAULT),
        ndc_check: !args.no_ndc,
        parameters: tamarin_theory::constraint::solver::sources::IntegerParameters::with_overrides(
            args.open_chains,
            args.saturation,
        ),
        maude_path,
        // `--processors=1` means one shared Maude: byte-identical to sequential.
        maude_processes: args.effective_maude_processes(),
        quiet: args.quiet,
    })
}

/// No proof step requested: every lemma keeps its default `Sorry` proof.
fn skipped_results(elaborated: &tamarin_theory::theory::Theory) -> Vec<LemmaResult> {
    elaborated
        .lemmas()
        .map(|l| LemmaResult {
            name: l.name.clone(),
            // The default `Sorry` proof is `IncompleteProof`.
            status: ProofStatus::Incomplete,
            // HS counts the default `Sorry` placeholder proof
            // as 1 step (one `LNode (ProofStep Sorry ...)` —
            // see `foldProof proofStepSummary`, ClosedTheory.hs).
            // Match it.
            proof_steps: 1,
            exists_trace: matches!(
                l.trace_quantifier,
                tamarin_theory::theory::TraceQuantifier::ExistsTrace,
            ),
        })
        .collect()
}

/// What [`prove_theory`] hands back to the render/output phase: the
/// per-lemma summary rows, the proof bodies for the closed-theory render, and
/// the labelled solved systems `--output-dot` / `--output-json` serialise.
struct ClosedOutcome {
    results: Vec<LemmaResult>,
    proved_lemmas: Vec<tamarin_theory::pretty_theory::ProvedLemma>,
    trace_systems: Vec<(String, System)>,
}

/// The CLI half of HS `constructAutoProver` (TheoryLoader.hs).
/// When `--heuristic` is given it OVERRIDES the per-lemma / theory
/// heuristic for every lemma (HS `selectHeuristic`, Theory/Proof.hs).
fn cli_heuristic(opts: &TheoryLoadOptions) -> tamarin_theory::prove::CliHeuristic {
    tamarin_theory::prove::CliHeuristic {
        raw: opts.heuristic.clone(),
        oracle_name: opts.oracle_name.clone(),
        oracle_only: opts.oracle_only,
    }
}

/// Prepare the rule variants and source patterns shared by the batch proof
/// loop and `--precompute-only` statistics.
fn build_prover_session(
    args: &Args,
    st: &TheoryPipeline,
    cut: tamarin_theory::constraint::solver::context::CutStrategy,
    cli_heuristic: tamarin_theory::prove::CliHeuristic,
) -> Result<tamarin_theory::prove::ProverSession, RunError> {
    let in_file = &st.theory.in_file;
    let maude = st.require_maude().map_err(|e| RunError::load(e, in_file))?;
    Ok(tamarin_theory::prove::ProverSession::build(
        st.theory.clone(),
        maude,
        tamarin_theory::prove::ProverSessionOptions {
            maude_pool: st.maude_pool.clone(),
            cli_heuristic,
            cut,
            ndc_cache: st.ndc_cache.clone(),
            parameters: st.opts.parameters,
            sys_retention: if wants_trace_output(args) {
                tamarin_theory::constraint::solver::search::SysRetention::KeepSolved
            } else {
                tamarin_theory::constraint::solver::search::SysRetention::DropAll
            },
            show_saturation_steps: true,
            loop_breakers_prepared: true,
        },
    )?)
}

/// HS `proveTheory`, the last step of `closeTranslatedTheory`: run the
/// selected lemmas' auto-prover and, without `--prove`, the close-time
/// `checkAndExtendProver` replay of stored proofs. Prints `Theory closed`
/// (with `pe_trace`) before any proof search: HS forces the proofs lazily as
/// the theory is rendered.
fn prove_theory(
    args: &Args,
    st: &TheoryPipeline,
    cut: tamarin_theory::constraint::solver::context::CutStrategy,
    pe_trace: &str,
) -> Result<ClosedOutcome, RunError> {
    let opts = st.opts;
    let want_traces = wants_trace_output(args);
    let lemma_filter: &[String] = &opts.lemma_names;
    let prove_anything = opts.prove_mode;
    // A plain load still validates embedded proofs; proofless files skip the
    // solver, whose output would be the same 1-step sorry per lemma.
    let any_stored_proof = st.theory.lemmas().any(|l| l.proof.is_some());
    if opts.precompute_only_mode || (!prove_anything && !any_stored_proof) {
        st.closed_marker(pe_trace);
        return Ok(ClosedOutcome {
            results: skipped_results(&st.theory),
            proved_lemmas: Vec::new(),
            trace_systems: Vec::new(),
        });
    }

    // `--bound=N` is HS `apBound`, applied by `runAutoProver` as
    // `boundProofDepth` to the `--prove` targets only; replayed non-targets
    // run under `checkAndExtendProver (sorryProver Nothing)`, unbounded.
    let target_bound: usize = args.bound.map_or(usize::MAX, |b| b as usize);
    let has_target = prove_anything
        && st
            .theory
            .lemmas()
            .any(|lemma| lemma_matches(lemma_filter, &lemma.name));
    let heuristic = if has_target {
        cli_heuristic(opts)
    } else {
        tamarin_theory::prove::CliHeuristic::default()
    };
    let session = build_prover_session(args, st, cut, heuristic)?;
    st.closed_marker(pe_trace);

    let theory_name = st.theory.name.clone();
    let render = move |l: &tamarin_theory::theory::Lemma, root: ProofNode| {
        let lemma_name = l.name.clone();
        let exists_trace = matches!(
            l.trace_quantifier,
            tamarin_theory::theory::TraceQuantifier::ExistsTrace,
        );
        // HS `getProofStatus` folds the WHOLE tree: a stale stored branch is
        // `Undetermined`, absorbed by its freshly proved siblings.
        let status = tamarin_theory::constraint::solver::search::proof_status(&root);
        let proof_steps = count_proof_steps(&root);
        let proof_body = Some(tamarin_theory::pretty_theory::pretty_proof_body(&root));
        // HS `systemsWithMetadata` (Batch.hs) reads every lemma's proof
        // tree; this consumes the tree for its solved systems.
        let mut lemma_traces: Vec<(String, System)> = Vec::new();
        if want_traces {
            for (path, sys) in tamarin_theory::constraint::solver::search::into_solved_systems(root)
            {
                lemma_traces.push((trace_output_label(&theory_name, &lemma_name, &path), sys));
            }
        }
        let proved = tamarin_theory::pretty_theory::ProvedLemma {
            name: lemma_name.clone(),
            proof_body,
        };
        let result = LemmaResult {
            name: lemma_name,
            status,
            proof_steps,
            exists_trace,
        };
        (proved, result, lemma_traces)
    };

    // The session joins active proofs and returns results in declaration order.
    let lemma_results = session.map_lemma_proofs(
        |lemma| {
            (prove_anything && lemma_matches(lemma_filter, &lemma.name)).then_some(target_bound)
        },
        render,
    )?;
    let mut outcome = ClosedOutcome {
        results: Vec::new(),
        proved_lemmas: Vec::new(),
        trace_systems: Vec::new(),
    };
    for (proved, result, traces) in lemma_results {
        outcome.proved_lemmas.push(proved);
        outcome.results.push(result);
        outcome.trace_systems.extend(traces);
    }
    Ok(outcome)
}

fn run_batch(args: &Args) -> Result<i32, RunError> {
    init_rayon_pool(args);
    if args.diff {
        return Err(RunError::Regular(
            "--diff (observational equivalence) is not yet ported to the Rust prover.".to_string(),
        ));
    }
    // `--stop-on-trace` selects HS's `SolutionExtractor` (Theory/Proof.hs,
    // TheoryLoader.hs) and, when the CLI flag is absent, HS
    // additionally consults the theory's in-file `configuration:` block
    // (`configStopOnTrace`, TheoryLoader.hs) — a PER-THEORY value,
    // so the effective strategy is resolved inside the file loop by
    // `effective_cut` once the theory is parsed.

    if args.in_files.is_empty() {
        return Err(RunError::Regular("no input files given".to_string()));
    }
    let mut file_results: Vec<FileResult> = Vec::new();
    // `--parse-only` docs, buffered and printed AFTER the file loop: HS
    // (Batch.hs) runs `mapM (processThy "") inFiles` to completion
    // BEFORE the `mapM_ (putStrLn . renderDoc) docs` — so a parse error in a
    // later file aborts the run (`die`) with NOTHING printed for the earlier
    // files, and the stderr `[Theory X] Theory loaded` markers all precede
    // the stdout docs.
    let mut parse_only_docs: Vec<String> = Vec::new();
    // `--precompute-only` per-file state (HS Batch.hs): like
    // `--parse-only`, HS prints every file's doc to stdout AFTER the file
    // loop (`mapM_ (putStrLn . renderDoc)`), ignoring `-o`/`-O` and
    // skipping the summary block.  The doc's stats force the saturation
    // lazily at that renderDoc, so each file's `[Saturating Sources]`
    // stderr trace fires in the PRINT phase (after every file's markers),
    // not during its loop iteration — stash the session and the wf-failure
    // count here and defer the stats computation to match.
    let mut precompute_pending: Vec<(tamarin_theory::prove::ProverSession, usize)> = Vec::new();

    // The maude binary this run invokes is argv-constant, and resolving the
    // default probes the filesystem — resolve it ONCE here and lend it to the
    // version check and to every file's pipeline state.
    let maude_path = maude_invocation_path(args);

    // HS runs `ensureMaudeAndGetVersion` ONCE at the top of the batch run
    // (Batch.hs), before the first theory is loaded: it writes the
    // tool block to stderr and returns the version data every file's
    // `Generated from:` block reports.  `--parse-only` is the one branch that
    // does NOT run it (Batch.hs), so no probe and no banner there;
    // `--quiet` does not suppress it either (see `Args::quiet`).
    let maude_version: Option<String> = if args.parse_only {
        None
    } else {
        let (_, version_data) = ensure_maude(args, &maude_path);
        // `getVersionIO` splices the version data — which ends in maude's own
        // newline — straight into the block; `BuildInfo` holds the line's
        // content instead, so drop it here.
        Some(version_data.trim_end().to_string())
    };

    let opts: TheoryLoadOptions = mk_theory_load_options(args, maude_path)?;

    // Batch.hs guard order: parseOnly > precomputeOnly > outModule >
    // normal — `--parse-only -m msr` behaves as plain `--parse-only`, and
    // `--prove -m spthy` does not prove.
    let requested_module: Option<ModuleType> = if opts.parse_only_mode || opts.precompute_only_mode
    {
        None
    } else {
        opts.output_module
    };
    let translate_module: Option<TranslateModule> = match requested_module {
        None => None,
        Some(ModuleType::Spthy) => Some(TranslateModule::Spthy),
        Some(ModuleType::SpthyTyped) => Some(TranslateModule::SpthyTyped),
        Some(ModuleType::Msr) => Some(TranslateModule::Msr),
        Some(
            m @ (ModuleType::ProVerifEquivalence | ModuleType::ProVerif | ModuleType::DeepSec),
        ) => {
            return Err(RunError::Regular(format!(
                "--output-module={}: the ProVerif / DeepSec export backends are not yet ported to \
                 the Rust prover.",
                m.as_str()
            )));
        }
    };
    // Translate-only docs, buffered and emitted AFTER the file loop
    // (Batch.hs: `mapM processThy` to completion, then either the
    // `-o`/`-O` writes or `mapM_ (putStrLn . renderDoc)`).
    let mut translate_docs: Vec<String> = Vec::new();

    // The `Generated from:` block's metadata (HS `withVersionAndReport`,
    // TheoryLoader.hs).  Every field is build- or argv-constant, so
    // one value serves every file's render.
    let build_info = tamarin_theory::pretty_theory::BuildInfo {
        tamarin_version: crate::cli::VERSION.to_string(),
        maude_version: maude_version.unwrap_or_else(|| "unknown".to_string()),
        git_revision: crate::cli::GIT_REV.to_string(),
        git_branch: crate::cli::GIT_BRANCH.to_string(),
        compiled_at: crate::cli::BUILD_TIMESTAMP.to_string(),
    };

    for in_file in &args.in_files {
        let t0 = Instant::now();
        // Bytes first, then the decode: the two failures are DIFFERENT HS
        // exceptions — `openFile`'s for a path that cannot be read at all,
        // `hGetContents`' for a file that opens but is not UTF-8.
        let src = match fs::read(in_file) {
            Ok(bytes) => match String::from_utf8(bytes) {
                Ok(s) => s,
                Err(e) => return Err(decode_error(in_file, &e)),
            },
            Err(e) => return Err(open_file_error(in_file, &e)),
        };
        // Thread the including file's directory so `#include "file"` resolves
        // relative to it (HS `takeDirectory inFile0`, Theory/Text/Parser.hs).
        let base_dir = std::path::Path::new(in_file)
            .parent()
            .map(|p| p.to_path_buf());
        // HS `loadTheory`: prints `Theory loaded` in every mode,
        // `--parse-only` included.
        let parsed = match load_theory(&opts, &src, base_dir) {
            Ok(thy) => thy,
            Err(e) => {
                report_parser_error(e, in_file, &src);
                return Ok(1);
            }
        };

        if opts.parse_only_mode {
            // HS-faithful `--parse-only` (Batch.hs + TheoryLoader.hs): parse, emit the marker above, pretty-print the OPEN
            // theory (`prettyOpenTheory`) — no wellformedness, no
            // configuration-block processing (that happens in `closeTheory`,
            // TheoryLoader.hs), no Maude, no output files (`-o`/`-O`
            // are ignored: the parseOnly branch never consults `writeOutput`),
            // no `summary of summaries`.
            //
            // The elaborated theory here only supplies the parse-time
            // signature + hoisted heuristic/tactic headers + the arity-1
            // fold set — elaboration is RS's signature-construction step
            // (HS builds the same pure signature during parsing).
            let elaborated = elaborate_with_in_file(&parsed, in_file).map_err(|e| {
                RunError::Regular(format!("elaboration error in {}: {}", in_file, e.message))
            })?;
            let body = tamarin_theory::pretty_theory::pretty_open_theory(&elaborated);
            parse_only_docs.push(body);
            file_results.push(FileResult {
                in_file: in_file.clone(),
                out_file: None,
                results: Vec::new(),
                elapsed_ms: t0.elapsed().as_millis(),
                wf_count: 0,
            });
            continue;
        }

        // The cut follows `configStopOnTrace` precedence. An unreadable
        // block value is reported whenever `--prove` was given, eagerer than
        // HS, which exits 0 when no selected lemma forces it.
        let config =
            read_config_block(&parsed, translate_module).map_err(|e| RunError::load(e, in_file))?;
        let cut = effective_cut(&opts, &config)?;
        let mut st = TheoryPipeline::new(&opts, parsed, in_file, translate_module, config)
            .map_err(|e| RunError::load(e, in_file))?;
        st.translate_theory()
            .map_err(|e| RunError::load(e, in_file))?;
        st.check_translated_theory()
            .map_err(|e| RunError::load(e, in_file))?;

        // Per-file summary rows for `file_results`.  Translate mode records
        // skipped rows too, though its output phase never prints a summary.
        let results: Vec<LemmaResult> = match translate_module {
            Some(module) => {
                // HS `translateAndCheckTheory` never closes, never proves
                // and never replays stored skeletons — it skips
                // `closeTranslatedTheory`'s `proveTheory` entirely
                // (TheoryLoader.hs) — so every lemma is a skipped
                // summary row.
                let results = skipped_results(&st.theory);

                // `finalizeTheory`'s `--quit-on-warning` raise
                // (`prettyOpenTheoryByModule`): no `Theory closed` marker.
                if opts.quit_on_warning && !st.wf_report.is_empty() {
                    return Err(RunError::Warning(st.wf_report.clone()));
                }

                // Translate-only render (`prettyOpenTheoryByModule`,
                // TheoryLoader.hs#prettyOpenTheoryByModule, followed by `withVersionAndReport`'s
                // two trailing comment items, TheoryLoader.hs).  The doc
                // is BUFFERED — Batch.hs processes every file before any
                // doc is printed or written.
                //
                // `spthy` and `spthytyped` share `prettyOpenTheory` and differ
                // only in the theory value `translate_theory` left behind;
                // `msr` renders every translation item as empty.
                let wf_block = tamarin_theory::pretty_theory::format_wf_block(&st.wf_report);
                let body = match module {
                    TranslateModule::Msr => {
                        tamarin_theory::pretty_theory::pretty_open_translated_theory_by_module(
                            &st.theory,
                            &wf_block,
                            &build_info,
                        )
                    }
                    TranslateModule::Spthy | TranslateModule::SpthyTyped => {
                        tamarin_theory::pretty_theory::pretty_open_theory_by_module(
                            &st.theory,
                            &wf_block,
                            &build_info,
                        )
                    }
                };
                translate_docs.push(body);
                results
            }
            None => {
                let pe_trace = st
                    .close_translated_theory()
                    .map_err(|e| RunError::load(e, in_file))?;
                let closed = prove_theory(args, &st, cut, &pe_trace)?;

                if opts.precompute_only_mode {
                    // HS `--precompute-only` (Batch.hs): the file's
                    // doc is `ppWf report $--$ prettyPrecomputation thy''` — the
                    // wellformedness WARNING line and a compact 3-line stats
                    // overview — NOT the full closed theory.  The stats need the
                    // closed theory's saturated sources, so build the prover
                    // session (the `closeTheory` analog) here — in-loop, like HS's
                    // eager close — but defer forcing the sources to the print
                    // phase below, where HS's lazy renderDoc forces them.
                    let session = build_prover_session(
                        args,
                        &st,
                        cut,
                        tamarin_theory::prove::CliHeuristic::default(),
                    )?;
                    let wf_len = st.wf_report.len();
                    precompute_pending.push((session, wf_len));
                } else {
                    // HS `outputTraces` (Batch.hs) runs in `processThy`'s
                    // close-and-prove `else` — the ONLY branch that reaches it.
                    // `--parse-only` (Batch.hs), `--precompute-only`
                    // and `-m` all return first, so they leave
                    // the target paths untouched, as does a run with no input files
                    // (`helpAndExit`, Batch.hs) and `--diff` (the `bitraverse`
                    // `Right` arm is `pure ()`; RS rejects `--diff` before the loop).
                    // It precedes the theory render, matching HS's force order: the
                    // write is an `IO` action inside `processThy`, while the doc is
                    // rendered later in `Batch.hs`'s output phase.
                    if wants_trace_output(args)
                        && let Err(io) = write_output_traces(args, closed.trace_systems)
                    {
                        return Err(RunError::GhcException(io));
                    }
                    // Build the HS-faithful theory pretty-print body.  This replaces
                    // the verbatim source dump with HS's `prettyClosedTheory`
                    // output shape — re-rendered signature, rules with `(modulo E)`
                    // prefix and AC-variant comments, lemmas with inline guarded
                    // formula and proof body, wellformedness block, and
                    // Generated-from footer.
                    let wf_block = tamarin_theory::pretty_theory::format_wf_block(&st.wf_report);
                    let body = tamarin_theory::pretty_theory::pretty_closed_theory(
                        &st.theory,
                        &closed.proved_lemmas,
                        &wf_block,
                        &build_info,
                    );
                    // HS normal mode: `writeOutput` is true whenever `-o`/`-O` was
                    // given (Batch.hs), and a `mkOutPath` miss — `-o=` with no
                    // `-O` — `die`s with this exact line (Batch.hs) instead
                    // of falling back to stdout: markers printed, stdout empty, rc 1.
                    // (HS processes every file before dying; with several input
                    // files this port dies after the first, an accepted divergence —
                    // the condition is argv-constant, so no file output differs.)
                    if (args.output_file.is_some() || args.output_dir.is_some())
                        && out_path_for(args, in_file).is_none()
                    {
                        return Ok(missing_output_path());
                    }
                    if let Err(io) = emit_output(args, in_file, &body) {
                        return Err(RunError::GhcException(io));
                    }
                }
                closed.results
            }
        };

        file_results.push(FileResult {
            in_file: in_file.clone(),
            out_file: out_path_for(args, in_file),
            results,
            elapsed_ms: t0.elapsed().as_millis(),
            wf_count: st.wf_report.len(),
        });
    }

    // HS-faithful: `--parse-only` and `--precompute-only` return from
    // `Batch.hs` before `ppRep` runs, so they skip the `summary of
    // summaries:` block entirely and instead print each file's doc via
    // `mapM_ (putStrLn . renderDoc)` — one trailing newline per doc, always
    // to stdout (`-o`/`-O` ignored), after ALL files were processed.
    // Every other batch run emits the summary on stdout, `--quiet`
    // notwithstanding (see `Args::quiet`).
    if opts.parse_only_mode {
        for doc in &parse_only_docs {
            println!("{}", doc);
        }
    } else if opts.precompute_only_mode {
        // HS precompute arm (Batch.hs): same deferred
        // `mapM_ (putStrLn . renderDoc)` shape as `--parse-only` — all
        // docs to stdout after the file loop, no summary block.  Forcing
        // each file's stats here (traces, then its doc) reproduces HS's
        // renderDoc-time stderr order — see `precompute_pending`.
        for (session, wf_len) in &precompute_pending {
            // The trace is already armed: each file's `close_translated_theory`
            // left it on, matching HS, where this forcing happens inside the
            // same `showSaturation = True` close.
            let stats = session.precomputation_stats().map_err(RunError::from)?;
            // HS `casesInfo` (ClosedTheory.hs).
            let chain_info = |n: usize| -> String {
                if n == 0 {
                    "deconstructions complete".to_string()
                } else {
                    format!("{n} partial deconstructions left")
                }
            };
            let mut doc = String::new();
            // `ppWf` (Batch.hs) joined by `$--$`: exactly one blank
            // line between the WARNING and the stats, nothing when the
            // report is empty.  Under `--prove` the vcat gains HS's
            // 9-space-indented "might be wrong!" second line —
            // `proveMode` and `precomputeOnlyMode` are set independently
            // (TheoryLoader.hs), so the combination is reachable.
            if *wf_len > 0 {
                doc.push_str(&format!(
                    "WARNING: {} wellformedness check failed!\n",
                    wf_len
                ));
                if opts.prove_mode {
                    doc.push_str("         The analysis results might be wrong!\n");
                }
                doc.push('\n');
            }
            doc.push_str(&format!(
                "Multiset rewriting rules{}: {}\n",
                if stats.has_restrictions {
                    " and restrictions"
                } else {
                    ""
                },
                stats.rules
            ));
            doc.push_str(&format!(
                "Raw sources: {} cases, {}\n",
                stats.raw_cases,
                chain_info(stats.raw_chains)
            ));
            doc.push_str(&format!(
                "Refined sources: {} cases, {}",
                stats.refined_cases,
                chain_info(stats.refined_chains)
            ));
            // The trailing newline comes from `println!` (HS `putStrLn`).
            println!("{}", doc);
        }
    } else if translate_module.is_some() {
        // Translate-only output phase (Batch.hs): every file was
        // processed above; now either write the docs to `-o`/`-O` or print
        // them to stdout.  NO `summary of summaries:` block in this mode.
        if args.output_file.is_some() || args.output_dir.is_some() {
            // `mapM mkOutPath inFiles` (Batch.hs): resolve EVERY
            // path first — a single miss (`-o=` with no `-O`) dies before
            // anything is written.
            let mut out_files: Vec<String> = Vec::with_capacity(args.in_files.len());
            for f in &args.in_files {
                match out_path_for(args, f) {
                    Some(p) => out_files.push(p),
                    None => return Ok(missing_output_path()),
                }
            }
            for (out, doc) in out_files.iter().zip(&translate_docs) {
                // `writeFileWithDirs o (renderDoc d)` — doc written VERBATIM
                // (no trailing newline; the stdout arm's `putStrLn` newline is
                // absent here — 881 vs 882 bytes on typing4.spthy).
                if let Err(io) = write_file_with_dirs(out, doc) {
                    return Err(RunError::GhcException(io));
                }
            }
        } else {
            for doc in &translate_docs {
                // `mapM_ (putStrLn . renderDoc) docs` — exactly one trailing
                // newline per doc.
                println!("{}", doc);
            }
        }
    } else {
        print_overall_summary(&file_results, opts.prove_mode);
    }

    // Every analysis verdict is a successful invocation. Parse, I/O, Maude,
    // guarded-conversion and ranking failures have already returned above.
    Ok(0)
}

/// HS-equivalent: GHC's `+RTS -N RTS_FLAG` sets the worker capacity for
/// the `par*`/`Strategies` sites HS uses (`using parList` / `parMap`:
/// CloseRule.hs, Prover.hs, Theory/Constraint/Solver/Sources.hs,
/// TheoryObject.hs).  We mirror that surface via a CLI flag.
/// Idempotent across files in a batch — `build_global` silently errors on
/// the second call, which is what we want.
///
/// Default: `available_parallelism()` (full machine).  `MaudePool`
/// (`--maude-processes=M`) removes the Maude IPC mutex contention that
/// would otherwise serialise every worker on a single subprocess, so
/// users can productively scale to every core.  Memory budget is
/// mediated by `--maude-processes`, which defaults to `processors` (1:1).
fn init_rayon_pool(args: &Args) {
    let n = args.effective_processors();
    // `build_global` is idempotent-error: the SECOND call returns Err
    // even if N matches.  We swallow the error: the first invocation
    // wins (which is the desired behaviour — RS runs `run_batch` once
    // per process, and tests install their own pool).
    // `stack_size`: the theory item fold renders each item as ONE HughesPJ
    // Doc on a worker (HS `parMap rdeepseq ppItem`, TheoryObject.hs), and
    // the eager Doc builders (`beside`/`above_g`) recurse along the left
    // operand's token spine, so depth scales with the item's size.  GHC grows
    // its stack on demand; rayon's default worker stacks do not, and overflow
    // on equation- and formula-heavy theories (`jcs18/trace-existence.spthy`).
    // 64 MiB is reserved virtual address space only, committed on use — the
    // same size the interactive server gives its tokio workers.
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .stack_size(64 * 1024 * 1024)
        .thread_name(|i| format!("tamarin-rayon-{}", i))
        .build_global();
}

fn default_maude_path() -> String {
    for c in ["/usr/local/bin/maude", "/usr/bin/maude"] {
        if std::path::Path::new(c).exists() {
            return c.to_string();
        }
    }
    "maude".to_string()
}

/// Emit `body` to `--output` / `-O` / stdout.
///
/// The two sinks differ by one byte: HS writes `renderDoc d` VERBATIM to the
/// file (`writeFileWithDirs`, Main/Utils.hs) and `putStrLn`s it to stdout
/// (Batch.hs), and `renderDoc` of a closed theory ends at `end` with
/// no newline.  `body` carries the stdout form (one trailing newline), so the
/// file write drops it — oracle-verified: a v1.13.0 `--output=FILE` run ends
/// the file with the bytes `end`.
///
/// `Err` is the [`write_io_exception`] text for the caller to report as a
/// [`RunError::GhcException`].
fn emit_output(args: &Args, in_file: &str, body: &str) -> Result<(), String> {
    if let Some(out) = out_path_for(args, in_file) {
        write_file_with_dirs(&out, body.strip_suffix('\n').unwrap_or(body))?;
    } else {
        // stdout
        print!("{}", body);
    }
    Ok(())
}

/// Resolve the output path for `in_file` given the user's `-o` / `-O`
/// flags. Returns `None` when output should go to stdout.
pub(crate) fn out_path_for(args: &Args, in_file: &str) -> Option<String> {
    if let Some(of) = &args.output_file
        && !of.is_empty()
    {
        return Some(of.clone());
    }
    if let Some(dir) = &args.output_dir {
        let stem = std::path::Path::new(in_file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("theory");
        let mut p = PathBuf::from(dir);
        p.push(format!("{}_analyzed.spthy", stem));
        return Some(p.to_string_lossy().to_string());
    }
    None
}

/// Count proof-tree nodes — the number of `LNode` constructors in the
/// proof tree.  Each `step` in the proof's textual form (a `simplify` /
/// `solve(...) case X` / `qed` / `SOLVED` annotation) corresponds to one
/// ProofNode.  Mirrors HS's `foldProof proofStepSummary` (which sums
/// `const (Sum 1)` over every ProofStep — ClosedTheory.hs via
/// `foldProof`, Theory/Proof.hs).
fn count_proof_steps(node: &tamarin_theory::constraint::solver::search::ProofNode) -> usize {
    1 + node.children.values().map(count_proof_steps).sum::<usize>()
}

fn print_overall_summary(file_results: &[FileResult], prove_mode: bool) {
    // Mirrors HS `summary of summaries:` block (`Main.Mode.Batch`).
    let line = "=".repeat(78);
    println!();
    println!("{}", line);
    println!("summary of summaries:");
    println!();
    for fr in file_results {
        println!("analyzed: {}", fr.in_file);
        // HS `ppRep` (Batch.hs) has TWO `Pretty.text ""` between
        // `analyzed:` and the nested `output:`/`processing time:` block, but
        // HughesPJ collapses adjacent empty lines under `vcat`, so the rendered
        // output is a SINGLE blank line here.  Verified against the v1.13.0
        // binary: `tamarin-prover --prove` emits exactly one blank line between
        // `analyzed:` and `output:`/`processing time:`, so one `println!()` is
        // byte-faithful.
        println!();
        if let Some(out) = &fr.out_file {
            // HS aligns `output:` and `processing time:` columns
            // (`ppRep`, Batch.hs).
            println!("  output:          {}", out);
        }
        println!("  processing time: {:.2}s", fr.elapsed_ms as f64 / 1000.0);
        println!("  ");
        if fr.wf_count > 0 {
            println!("  WARNING: {} wellformedness check failed!", fr.wf_count);
            // HS Batch.hs emits this second line only in prove mode:
            //   [ Pretty.text "         The analysis results might be wrong!"
            //   | thyLoadOptions.proveMode ]
            if prove_mode {
                println!("           The analysis results might be wrong!");
            }
            // HS `summary = ppWf report $--$ prettyClosedSummary` (Batch.hs):
            // `$--$` (above with a blank-line gap) inserts the blank ONLY when
            // both operands are non-empty.  Under the enclosing `nest 2` a
            // blank `Pretty.text ""` renders as `"  "`.  So this separator
            // appears between the warning block and the per-lemma summary
            // lines ONLY when there are summary lines to follow; emitting it
            // unconditionally would add a spurious trailing `"  "` line.
            if !fr.results.is_empty() {
                println!("  ");
            }
        }
        for r in &fr.results {
            println!("  {}", format_lemma_summary_line(r));
        }
        println!();
    }
    println!("{}", line);
}

/// Render the parser's semantic diagnostic with source-labelled spans.
fn report_parser_error(err: tamarin_parser::ParseError, root_name: &str, root_source: &str) {
    use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
    use std::io::{IsTerminal, Write};

    let color = if std::io::stderr().is_terminal() {
        ColorChoice::Auto
    } else {
        ColorChoice::Never
    };
    let writer = StandardStream::stderr(color);
    let mut writer = writer.lock();
    if emit_parser_error(&mut writer, &err, root_name, root_source).is_err() {
        let _ = writeln!(
            writer,
            "{}",
            err.render_plain_with_source(root_name, root_source)
        );
    }
}

struct ParserDiagnosticFile<'a>(codespan_reporting::files::SimpleFile<&'a str, &'a str>);

impl<'a> ParserDiagnosticFile<'a> {
    fn new(name: &'a str, source: &'a str) -> Self {
        Self(codespan_reporting::files::SimpleFile::new(name, source))
    }
}

impl<'a> codespan_reporting::files::Files<'a> for ParserDiagnosticFile<'a> {
    type FileId = ();
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, (): ()) -> Result<Self::Name, codespan_reporting::files::Error> {
        Ok(*self.0.name())
    }

    fn source(&'a self, (): ()) -> Result<Self::Source, codespan_reporting::files::Error> {
        Ok(*self.0.source())
    }

    fn line_index(
        &'a self,
        (): (),
        byte_index: usize,
    ) -> Result<usize, codespan_reporting::files::Error> {
        codespan_reporting::files::Files::line_index(&self.0, (), byte_index)
    }

    fn line_range(
        &'a self,
        (): (),
        line_index: usize,
    ) -> Result<std::ops::Range<usize>, codespan_reporting::files::Error> {
        codespan_reporting::files::Files::line_range(&self.0, (), line_index)
    }

    fn column_number(
        &'a self,
        (): (),
        line_index: usize,
        byte_index: usize,
    ) -> Result<usize, codespan_reporting::files::Error> {
        let line = self.line_range((), line_index)?;
        let source = *self.0.source();
        let offset = byte_index.clamp(line.start, line.end);
        Ok(
            tamarin_parser::parse_error::line_column(&source[line.clone()], offset - line.start).1
                as usize,
        )
    }
}

fn emit_parser_error(
    writer: &mut impl codespan_reporting::term::termcolor::WriteColor,
    err: &tamarin_parser::ParseError,
    root_name: &str,
    root_source: &str,
) -> Result<(), codespan_reporting::files::Error> {
    use codespan_reporting::diagnostic::{Diagnostic, Label};
    use codespan_reporting::term;

    let source_name = err.source_name().unwrap_or(root_name);
    let source_text = err.source_text().unwrap_or(root_source);
    let mut diagnostic_labels = err.diagnostic_labels_with_source(root_source).into_iter();
    let primary = diagnostic_labels
        .next()
        .expect("parser diagnostics have a primary label");
    let files = ParserDiagnosticFile::new(source_name, source_text);
    let file_id = ();
    let message = primary.message;
    let labels = std::iter::once(Label::primary(file_id, primary.span))
        .chain(
            diagnostic_labels
                .map(|label| Label::secondary(file_id, label.span).with_message(label.message)),
        )
        .collect();
    let diagnostic = Diagnostic::error()
        .with_message(message)
        .with_labels(labels)
        .with_notes(err.diagnostic_notes());
    let config = term::Config {
        tab_width: tamarin_parser::parse_error::PARSEC_TAB_WIDTH as usize,
        ..term::Config::default()
    };
    term::emit_to_write_style(writer, &config, &files, &diagnostic)
}

#[cfg(test)]
#[path = "run_tests.rs"]
mod tests;
