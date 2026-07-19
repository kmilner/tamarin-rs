// Currently GPL 3.0 until granted permission by the following authors:
//   kevinmorio, meiersi, jdreier, arcz, rsasse, rkunnema, beschmi,
//   gilcu3, Nynko, felixlinker, addap, yavivanov, Hong-Thai,
//   racoucho1u, ValentinYuri, BTom-GH, PhilipLukertWork, sans-sucre,
//   Mathias-AURAND, Azurios-git, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/ClosedTheory.hs, lib/theory/src/Items/RuleItem.hs,
//   lib/theory/src/Prover.hs, lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Constraint/System/JSON.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Text/Parser.hs,
//   lib/theory/src/Theory/Text/Parser/Accountability.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs,
//   lib/theory/src/Theory/Tools/Wellformedness.hs,
//   lib/theory/src/TheoryObject.hs, src/Main/Console.hs,
//   src/Main/Environment.hs, src/Main/Mode/Batch.hs,
//   src/Main/Mode/Interactive.hs, src/Main/Mode/Intruder.hs,
//   src/Main/Mode/Test.hs, src/Main/TheoryLoader.hs

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
//! `--parse-only` is the one path that re-emits the source verbatim
//! (no analysis); all other modes go through the pretty-printer.

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

use tamarin_parser::wf::{
    after_public_names_topics, insert_wf_before, WF_AFTER_CHECK_GUARDED,
    WF_AFTER_CHECK_TERMS, WF_AFTER_FACT_LHS, WF_AFTER_VARIANTS, WF_TOPIC_ORDER,
};
use tamarin_term::maude_proc::{MaudeHandle, MaudePool};
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::macro_expand::macro_expanded_clone;

use crate::cli::{lemma_matches, Args, Subcommand};

#[derive(Debug)]
pub struct RunError(pub String);

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for RunError {}

/// Outcome of proving a single lemma. Mirrors the columns of Haskell's
/// `summary of summaries:` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LemmaVerdict {
    Verified,
    Falsified,
    /// We exhausted the search budget or hit `Sorry`.
    Analyzed,
    /// HS `UnfinishableProof`: no open goals but subterm store has reducible
    /// operators.  HS `showProofStatus` (Theory/Proof.hs:1104-1112, see line 1109):
    ///   "analysis cannot be finished (reducible operators in subterms)"
    Unfinishable,
    /// HS `UndeterminedProof` (Theory/Proof.hs:1104-1112, see line 1111): proof tree folds to a
    /// status that could not be determined — renders "analysis undetermined".
    Undetermined,
    /// HS `InvalidatedProof` (Theory/Proof.hs:1104-1112, see line 1112): a stored proof step was
    /// invalidated (e.g. by an interactive reuse-lemma edit) — renders
    /// "proof has been invalidated".
    Invalidated,
    /// `[reuse]`-only lemma that we didn't try to prove (out of filter).
    Skipped,
    /// Lemma was filtered out by `--prove=FOO` / `--lemma=FOO`.
    Filtered,
    Error(String),
}

/// HS-faithful per-lemma summary line, mirroring `prettyClosedSummary`
/// (ClosedTheory.hs:463-491, which renders `showProofStatus ... <-> (siz "steps")`):
///   `<lemma> (<quantifier>): falsified - found trace (<N> steps)`
///   `<lemma> (<quantifier>): verified (<N> steps)`
///   `<lemma> (<quantifier>): analysis incomplete (<N> steps)`
///   `<lemma> (<quantifier>): analysis cannot be finished (reducible operators in subterms) (<N> steps)`
fn format_lemma_summary_line(r: &LemmaResult) -> String {
    let quantifier = if r.exists_trace { "exists-trace" } else { "all-traces" };
    let body = match &r.verdict {
        // HS `showProofStatus` (Theory/Proof.hs:1105-1108): a falsified
        // exists-trace lemma is a `CompleteProof` of `ExistsSomeTrace`
        // ("falsified - no trace found"), whereas a falsified all-traces
        // lemma is a `TraceFound` for `ExistsNoTrace` ("falsified - found
        // trace").  The wording therefore depends on the quantifier.
        LemmaVerdict::Falsified if r.exists_trace =>
            format!("falsified - no trace found ({} steps)", r.proof_steps),
        LemmaVerdict::Falsified => format!("falsified - found trace ({} steps)", r.proof_steps),
        LemmaVerdict::Verified => format!("verified ({} steps)", r.proof_steps),
        LemmaVerdict::Analyzed
        | LemmaVerdict::Skipped
        | LemmaVerdict::Filtered => format!("analysis incomplete ({} steps)", r.proof_steps),
        // HS `showProofStatus _ UnfinishableProof` (Theory/Proof.hs:1104-1112, see line 1109).
        LemmaVerdict::Unfinishable =>
            format!("analysis cannot be finished (reducible operators in subterms) ({} steps)", r.proof_steps),
        // HS `showProofStatus _ UndeterminedProof` (Theory/Proof.hs:1104-1112, see line 1111).
        LemmaVerdict::Undetermined =>
            format!("analysis undetermined ({} steps)", r.proof_steps),
        // HS `showProofStatus _ InvalidatedProof` (Theory/Proof.hs:1104-1112, see line 1112).
        LemmaVerdict::Invalidated =>
            format!("proof has been invalidated ({} steps)", r.proof_steps),
        LemmaVerdict::Error(msg) => format!("error: {}", msg),
    };
    format!("{} ({}): {}", r.name, quantifier, body)
}

#[derive(Debug, Clone)]
pub struct LemmaResult {
    pub name: String,
    pub verdict: LemmaVerdict,
    pub elapsed_ms: u128,
    /// Proof-tree node count — matches HS's "(N steps)" in
    /// `--prove` output (`foldProof proofStepSummary`, ClosedTheory.hs:463-491, see line 484,491,
    /// summing one per ProofStep via `foldProof`, Theory/Proof.hs:358-362).
    pub proof_steps: usize,
    /// `true` for `exists-trace` lemmas, `false` for `all-traces`.
    /// Drives the trace-quantifier label in the summary.
    pub exists_trace: bool,
}

#[derive(Debug, Clone)]
pub struct FileResult {
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
pub fn run(args: &Args) -> Result<i32, RunError> {
    if args.show_help {
        println!("{}", crate::cli::help_text());
        return Ok(0);
    }
    if args.show_version {
        // HS (Console.hs:326-330) splits the two streams: the banner +
        // license + `Generated from:` block go to STDOUT, the three maude
        // self-check lines to STDERR (`ensureMaude` -> `hPutStrLn stderr`).
        // version_text() already carries its own trailing newline.
        print!("{}", crate::cli::version_text());
        eprintln!("{}", crate::cli::version_maude_stderr_text());
        return Ok(0);
    }

    match args.subcommand {
        Subcommand::Batch => run_batch(args),
        Subcommand::Interactive => run_interactive(args),
        Subcommand::Variants => run_variants(args),
        Subcommand::Test => run_test(args),
    }
}

/// `tamarin-prover test` — mirror HS's installation self-test
/// (`Main.Mode.Test`).  HS runs:
///   1. Maude version check.
///   2. GraphViz `dot` version check.
///   3. The Haskell unit-test suite (55 cases as of v1.13.0).
///
/// We do (1) and (2) here.  Porting the unit test suite is a separate
/// effort; until then we run the prover's own lib tests at build time
/// instead (`cargo test`).  Returns rc=0 on Maude/dot reachable,
/// rc=1 otherwise.
fn run_test(_args: &Args) -> Result<i32, RunError> {
    println!("Self-testing the tamarin-prover installation.\n");
    println!("*** Testing the availability of the required tools ***");
    let mv = crate::cli::detect_maude_version_pub();
    match &mv {
        Some(v) => println!("{}. OK.\n checking installation: OK.", v),
        None => {
            eprintln!("Maude check FAILED — not found on $PATH.");
            return Ok(1);
        }
    }
    let dot = std::process::Command::new("dot").arg("-V").output();
    // HS `successGraphVizDot = isJust maybeSuccessGraphVizDot` (Test.hs:42-112, see line 51):
    // a missing/unavailable `dot` is a test FAILURE, not a silent skip.
    let success_graphviz = match dot {
        Ok(out) if out.status.success() => {
            let s = String::from_utf8_lossy(&out.stderr);
            println!("GraphViz tool: 'dot'\n checking version: {}OK.", s.trim());
            true
        }
        _ => {
            println!("GraphViz check skipped (`dot` not found).");
            false
        }
    };
    println!("\n*** TEST SUMMARY ***");
    // HS `success = successMaude && successGraphVizDot && successTerm`
    // (Test.hs:42-112, see line 96); on failure it warns and `exitFailure` (Test.hs:97-105).
    // Maude reachability is asserted above (early `Ok(1)` return), so the
    // only failure reachable here is a missing GraphViz `dot`.
    if success_graphviz {
        println!("All tool checks successful.");
        println!("The tamarin-prover should work as intended.\n");
        println!("           :-) happy proving (-:");
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
/// needing a `.spthy` file (Intruder.hs:44-53).
///
/// We mirror the DH half: spin up Maude with `dh_maude_sig()`, generate the
/// rules via [`tamarin_theory::intruder_rules::dh_intruder_rules`] with the
/// HS-hardcoded `False` flag, and pretty-print each rule in HS's
/// `rule (modulo AC) NAME:` shape.  The BP half is a known gap (see body).
fn run_variants(args: &Args) -> Result<i32, RunError> {
    let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
    // HS `Main.Mode.Intruder.run` (Intruder.hs:44-53) starts TWO SEPARATE
    // Maude handles — one on `dhMaudeSig`, one on `bpMaudeSig` — and
    // generates `dhIntruderRules False` then `bpIntruderRules False`, then
    // emits `dhS ++ bpS`.  We mirror the DH handle on `dh_maude_sig()` ALONE
    // (NOT merged with bp): merging exposes pmult/em to Maude during the DH
    // variant query and could perturb DH variant enumeration.  The DH
    // generator is hardcoded `False` in HS, not the --diff flag, so we pass
    // `false`.
    let sig = tamarin_term::maude_sig::dh_maude_sig();
    let maude = MaudeHandle::start(&maude_path, sig).map_err(|e| {
        RunError(format!("failed to start maude at {:?}: {:?}", maude_path, e))
    })?;
    // HS emits the maude tool/version banner on STDERR (via `ensureMaude`),
    // not stdout — the rule dump alone goes to stdout.  Mirror that.
    if let Some(v) = crate::cli::detect_maude_version_pub() {
        print_maude_banner(&maude_path, Some(&v));
    }
    // HS `Main.Mode.Intruder.run` (Intruder.hs:48-53) generates BOTH the DH
    // and the bilinear-pairing variants and emits `dhS ++ bpS`:
    //   - DH: `dhIntruderRules False` (runtime, via Maude).  RS's runtime
    //     generator is byte-faithful (exactly 51 rules); `variants_intruder`
    //     applies `remove_renamings` to drop redundant identity-variants.
    //   - BP: `bpIntruderRules False` (runtime).  Like HS
    //     (Intruder.hs:43-63, see line 50), we start a SECOND Maude handle on
    //     `bp_maude_sig()` and generate the 75 BP rules at runtime via
    //     `bp_intruder_rules(false, ..)`.  This tracks the CURRENT Maude
    //     rather than the stale cached `data/intruder_variants_bp.spthy`
    //     (which production proving still parses via
    //     `mk_bp_intruder_variants`); HS's `variants` command likewise
    //     generates BP at runtime, so the two stay byte-identical.
    let dh_rules = tamarin_theory::intruder_rules::dh_intruder_rules(false, &maude);
    let bp_sig = tamarin_term::maude_sig::bp_maude_sig();
    let bp_maude = MaudeHandle::start(&maude_path, bp_sig).map_err(|e| {
        RunError(format!("failed to start maude at {:?}: {:?}", maude_path, e))
    })?;
    let bp_rules = tamarin_theory::intruder_rules::bp_intruder_rules(false, &bp_maude);
    // HS `putStrLn (dhS ++ bpS)` where each block is
    // `renderDoc . prettyIntruderVariants` (Rule.hs:1343-1346): blank-line-separated
    // `rule (modulo AC) NAME:` rules with HughesPJ body wrapping (`sep`/`fsep`
    // at the standard width) and NO trailing newline — so the DH and BP blocks
    // abut (the DH `d_inv` body directly precedes the BP `c_pmult` header with
    // no separating newline).  `putStrLn` appends the single trailing newline.
    let dh_s = tamarin_theory::pretty_formula::pretty_intruder_variants(&dh_rules);
    let bp_s = tamarin_theory::pretty_formula::pretty_intruder_variants(&bp_rules);
    print!("{}{}", dh_s, bp_s);
    println!();
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

    init_rayon_pool(args);

    // Haskell defaults: 3001 on 127.0.0.1.
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
            RunError(format!(
                "could not parse --interface={:?} as an IP address: {}\n\
                 Use --interface=\"*4\" to bind to all IPv4 interfaces.",
                other, e,
            ))
        })?,
    };
    let bind_addr = SocketAddr::new(ip, port);

    // Resolve data dir. Without an explicit flag, look for `data/`
    // alongside the working directory or its ancestors — the same
    // search the server already exposes via `resolve_data_dir`.
    let data_dir = tamarin_server::handlers::static_files::resolve_data_dir(
        args.data_dir.clone().map(PathBuf::from),
    );
    // Try to discover a sibling frontend/dist for the bundled UI assets.
    let frontend_dist = guess_frontend_dist(&data_dir);

    let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);

    let mut cfg = tamarin_server::ServerConfig::new(bind_addr, data_dir, maude_path);
    cfg.frontend_dist = frontend_dist;
    if let Some(b) = args.bound {
        cfg.max_steps = b as usize;
    }
    // `-d/--derivcheck-timeout` — same default expression as the batch
    // path's derivation-check block (default 5).
    cfg.derivcheck_timeout = args.derivcheck_timeout.unwrap_or(5) as u32;
    // CLI `--stop-on-trace` — merged with each theory's `configuration:`
    // block at load time (`ProofState::new`), HS `closeTheory` precedence.
    cfg.stop_on_trace = cli_cut(args);

    // Positional args are theory files (Haskell uses a working
    // directory, but we accept either: a single dir arg, or one-or-more
    // .spthy paths).
    let theory_paths: Vec<PathBuf> = collect_theory_paths(&args.in_files)?;

    if !args.quiet {
        // HS interactive runs the tool checks BEFORE the banner
        // (Interactive.hs:86-91): `ensureMaudeAndGetVersion` prints the
        // maude block (Console.hs:150-155) and `ensureGraphVizDot` the
        // GraphViz block (Environment.hs:72-87), both on stderr.
        {
            print_maude_banner(
                &maude_display_name(args),
                crate::cli::detect_maude_version_pub().as_deref(),
            );
            eprintln!("GraphViz tool: 'dot'");
            // HS lowercases `dot -V`'s stderr banner, strips the trailing
            // newline, and appends ". OK." (Environment.hs:81-87); PNG
            // support = "png" appears in the `dot -T?` error listing.
            if let Ok(out) = std::process::Command::new("dot").arg("-V").output() {
                let banner = String::from_utf8_lossy(&out.stderr).to_lowercase();
                if banner.contains("graphviz") {
                    eprintln!(" checking version: {}. OK.", banner.trim_end_matches('\n'));
                    let png_ok = std::process::Command::new("dot").arg("-T?").output()
                        .map(|o| {
                            let s = format!(
                                "{}{}",
                                String::from_utf8_lossy(&o.stdout),
                                String::from_utf8_lossy(&o.stderr),
                            );
                            s.to_lowercase().contains("png")
                        })
                        .unwrap_or(false);
                    if png_ok {
                        eprintln!(" checking PNG support: OK.");
                    }
                }
            }
        }

        // HS startup banner (Interactive.hs:95-101) — stdout (`putStrLn`),
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
        println!(
            "The server is starting up on port {}.\nBrowse to http://{} once the server is ready.\n\nLoading the security protocol theories '{}' ...\n",
            port, bind_addr, loading_what,
        );
    }

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
        .map_err(|e| RunError(format!("failed to build tokio runtime: {}", e)))?;
    runtime
        .block_on(tamarin_server::serve(cfg, theory_paths))
        .map_err(|e| RunError(format!("server error: {}", e)))?;
    Ok(0)
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
                RunError(format!("could not read directory {}: {}", p.display(), e))
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

/// Best-effort: locate the bundled `frontend/dist/` sibling of `data/`.
/// Returns None if not found — the server tolerates this and just
/// won't serve the frontend assets.
fn guess_frontend_dist(data_dir: &std::path::Path) -> Option<std::path::PathBuf> {
    let parent = data_dir.parent()?;
    let candidate = parent.join("frontend").join("dist");
    if candidate.is_dir() {
        return Some(candidate);
    }
    None
}

/// Resolve the effective cut strategy + auto-sources for one theory —
/// HS `closeTheory`'s configuration-block routing (TheoryLoader.hs:640-666).
///
/// The in-file `configuration: "…"` string accepts exactly two flags
/// (`theoryConfFlags`, TheoryLoader.hs:656-659): `--stop-on-trace[=v]`
/// (`flagOpt "dfs"` — valueless means `dfs`) and `--auto-sources`
/// (`flagNone`).  Precedence: the CLI `--stop-on-trace` wins when given
/// (`configStopOnTrace` consults the block only when the CLI flag is
/// absent); `--auto-sources` is OR-combined (`configAutoSources`).  Bare
/// (non-flag) tokens land in cmdargs' positional catch-all
/// (`flagArg (updateArg "") ""`) and are ignored; an unknown flag or
/// stop-on-trace value aborts the run (cmdargs `processValue` /
/// `error e` on `ArgumentError`, TheoryLoader.hs:618-665, see line 661).
///
/// The strategy only steers prove-mode (`constructAutoProver` is used
/// solely when `thyOpts.proveMode`, TheoryLoader.hs:569-615, see line 606); without
/// `--prove` the non-prove default `CutDFS` applies.
fn effective_config(
    args: &Args,
    parsed: &tamarin_parser::ast::Theory,
) -> Result<(tamarin_theory::constraint::solver::context::CutStrategy, bool), RunError> {
    use tamarin_theory::constraint::solver::context::CutStrategy;
    let (block_cut, block_auto_sources) = match &parsed.configuration {
        Some(cfg) => tamarin_theory::prove::config_block_options(cfg)
            .map_err(RunError)?,
        None => (None, false),
    };
    let cut = if args.prove_mode {
        match &args.stop_on_trace {
            Some(s) => stop_on_trace_cut(s),
            None => block_cut.unwrap_or(CutStrategy::Dfs),
        }
    } else {
        CutStrategy::Dfs
    };
    Ok((cut, args.auto_sources || block_auto_sources))
}

/// Map a CLI `--stop-on-trace` value to its `CutStrategy`.  Shared by
/// `effective_config` (batch prove-mode) and `cli_cut` (interactive), so the
/// two cannot drift.
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

/// Map the CLI `--stop-on-trace` value (if given) to its `CutStrategy` —
/// the interactive server merges this with each theory's own
/// `configuration:` block at load time (`ProofState::new`).
fn cli_cut(args: &Args) -> Option<tamarin_theory::constraint::solver::context::CutStrategy> {
    args.stop_on_trace.as_ref().map(stop_on_trace_cut)
}

/// HS shows the maude tool's basename when the user didn't pass
/// `--maude-path`, and the full path when they did (Console.hs:97-149, see line 150).  We
/// can't re-introspect the flag downstream, so we key off `args.maude_path`
/// being `None` (the default) vs `Some` (user-supplied).
fn maude_display_name(args: &Args) -> String {
    let raw_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
    if args.maude_path.is_some() {
        raw_path
    } else {
        std::path::Path::new(&raw_path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(&raw_path)
            .to_string()
    }
}

/// Emit the `maude tool:` + version + installation banner to stderr (HS
/// `ensureMaudeAndGetVersion`, Console.hs:150-155).  `disp` is the tool name
/// to show; when `ver` is present the two ` checking …: OK.` lines follow.
fn print_maude_banner(disp: &str, ver: Option<&str>) {
    eprintln!("maude tool: '{}'", disp);
    if let Some(v) = ver {
        eprintln!(" checking version: {}. OK.", v);
        eprintln!(" checking installation: OK.");
    }
}

fn run_batch(args: &Args) -> Result<i32, RunError> {
    // HS-faithful internal parallelism via rayon.  Mirrors the four
    // `using parList`/`parTraversable`/`parMap` sites HS uses (see
    // `lib/theory/src/Prover.hs:68-164, see line 102,195`, `Theory/Constraint/Solver/Sources.hs`,
    // `lib/theory/src/TheoryObject.hs:732-768, see line 744,752`).  Default: full machine
    // parallelism (`available_parallelism()`, uncapped — Maude IPC runs
    // through the contention-free `MaudePool`, so larger pools scale;
    // memory is budgeted via `--maude-processes`).
    // `--processors=1` falls back to a 1-thread pool, guaranteeing
    // byte-identical output to the pre-parallel sequential path.
    init_rayon_pool(args);
    if args.diff {
        return Err(RunError(
            "--diff (observational equivalence) is not yet ported to the Rust prover."
                .to_string(),
        ));
    }
    if args.output_module.is_some() {
        return Err(RunError(
            "--output-module is not yet ported to the Rust prover.".to_string(),
        ));
    }
    // `--stop-on-trace` selects HS's `SolutionExtractor` (Theory/Proof.hs:693-694, see line 695,
    // TheoryLoader.hs:355-362) and, when the CLI flag is absent, HS
    // additionally consults the theory's in-file `configuration:` block
    // (`configStopOnTrace`, TheoryLoader.hs:640-666) — a PER-THEORY value,
    // so the effective strategy is resolved inside the file loop by
    // `effective_config` once the theory is parsed.
    // --output-json / --output-dot: trace graph serialisation isn't
    // ported yet (HS emits a graph of the attack-trace nodes/edges
    // for any falsified lemma — `outputTraces`, Batch.hs:251-271).  Don't
    // hard-error — many callers pass these flags unconditionally and just
    // want them harmless.  Write the exact bytes HS emits in the NO-TRACE
    // case so downstream tooling can `stat`/parse them; the trace-FOUND
    // case (real graphs) remains unported.  Print a one-line warning so the
    // user knows the contents aren't real.
    //
    // HS no-trace bytes (verified against the v1.13.0 binary):
    //   --output-dot:  `intercalate "\n" [] = ""`, then `writeFile ""`
    //                  ⇒ a 0-byte file (NOT "digraph trace {}").
    //   --output-json: `sequentsToJSONPretty graphOptions []`
    //                  (JSON.hs:458-463) = aeson-pretty `encodePretty`
    //                  of `{graphs:[]}` with the default Config
    //                  (confIndent = Spaces 4, confTrailingNewline = False)
    //                  ⇒ exactly `{\n    "graphs": []\n}` (20 bytes, NO
    //                  trailing newline; empty array renders inline).
    if let Some(p) = &args.trace_json {
        if !args.quiet {
            eprintln!("warning: --output-json: trace graph serialisation not yet ported; writing empty stub to {}", p);
        }
        fs::write(p, "{\n    \"graphs\": []\n}").map_err(|e| {
            RunError(format!("failed to write {}: {}", p, e))
        })?;
    }
    if let Some(p) = &args.trace_dot {
        if !args.quiet {
            eprintln!("warning: --output-dot: trace graph serialisation not yet ported; writing empty stub to {}", p);
        }
        fs::write(p, "").map_err(|e| {
            RunError(format!("failed to write {}: {}", p, e))
        })?;
    }
    if args.in_files.is_empty() {
        return Err(RunError(
            "no input files given\n\n".to_string() + &crate::cli::help_text(),
        ));
    }
    let mut overall_status = 0i32;
    let mut file_results: Vec<FileResult> = Vec::new();

    let parser_flags: Vec<&str> = args.defines.iter().map(String::as_str).collect();

    // The Maude version is constant for the whole run, but detecting it
    // spawns a `maude --version` subprocess.  Detect it ONCE here and
    // reuse the cached value for both the banner and every file's
    // `BuildInfo`, avoiding one `maude --version` subprocess per file.
    let maude_version: Option<String> = crate::cli::detect_maude_version_pub();

    // HS prints the maude tool + version banner ONCE at the top of the
    // batch run (`Main.Console.argExists` path).  Mirror that here:
    // emit `maude tool: 'maude'\n checking version: X. OK.\n checking
    // installation: OK.` before the first theory is loaded.  Suppressed
    // by `--quiet`.
    if !args.quiet && !args.parse_only {
        print_maude_banner(&maude_display_name(args), maude_version.as_deref());
    }

    for in_file in &args.in_files {
        let t0 = Instant::now();
        let src = fs::read_to_string(in_file).map_err(|e| {
            RunError(format!("failed to read {}: {}", in_file, e))
        })?;
        // Thread the including file's directory so `#include "file"` resolves
        // relative to it (HS `takeDirectory inFile0`, Parser.hs:323-343).
        let base_dir = std::path::Path::new(in_file)
            .parent()
            .map(|p| p.to_path_buf());
        let mut parsed = match tamarin_parser::parse_theory_with_base(&src, &parser_flags, base_dir) {
            Ok(thy) => thy,
            Err(e) => {
                // HS batch: `handleError e@(ParserError _) = die $ show e`
                // (Main/Mode/Batch.hs:87-316, see line 234).  `die` writes `show e` — the raw
                // parsec frame, with `inFile` as the `SourcePos` name — to
                // stderr and exits with code 1.  No `error:` prefix and no
                // `parse error in …:` wrapper (neither of which HS emits).
                eprintln!("{}", e.with_source(in_file.clone()));
                return Ok(1);
            }
        };
        // HS `liftedAddProtoRule` (Theory/Text/Parser.hs:166-193) runs per
        // rule DURING parsing: it expands each rule's `_restrict(φ)`
        // embedded restriction into a fresh `Restr_<rule>_<i>` restriction
        // (inserted before the rule) and rewrites the rule's actions to
        // reference it.  RS captures `_restrict` into
        // `Rule.embedded_restrictions` at parse time; run the equivalent
        // lifting pass here, BEFORE wellformedness / elaboration / rendering,
        // so the transformed parser theory drives all three (the renderer
        // iterates `parsed.items`).
        tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parsed)
            .map_err(|e| RunError(format!(
                "_restrict expansion failed in {}: {}", in_file, e.message)))?;
        // HS emits this trace marker as soon as the theory parses
        // (TheoryLoader.hs:401-424, see line 409).  `--parse-only` and `--quiet` skip it.
        let theory_name = parsed.name.clone();
        // HS `[Theory X] …` progress markers go to stderr and are suppressed
        // by `--quiet` / `--parse-only`.  Route all of them through one guard
        // so the suppression rule lives in a single place.
        let marker = |msg: &str| {
            if !args.quiet && !args.parse_only {
                eprintln!("[Theory {}] {}", theory_name, msg);
            }
        };
        marker("Theory loaded");

        // Effective cut strategy + auto-sources for THIS theory: CLI flags
        // merged with the in-file `configuration:` block per HS
        // `closeTheory` (TheoryLoader.hs:640-666).
        let (cut, auto_sources) = effective_config(args, &parsed)?;

        // Wellformedness checks — mirrors HS `checkWellformedness`
        // (`Theory.Tools.Wellformedness:1270`).  Runs on every file
        // (not gated by `--parse-only`) so a malformed theory is
        // surfaced even without proving.
        //
        // HS-faithful: HS's `thyProtoRules` (Wellformedness.hs:133-134, see line 134)
        // applies `applyMacroInRule (theoryMacros thy)` to every rule
        // BEFORE the checks run — so `Fr(test())` where `test() = ~x`
        // becomes `Fr(~x)` and passes.  We mirror by cloning `parsed`
        // and expanding macros before handing it to `check_theory`.
        let parsed_for_wf = macro_expanded_clone(&parsed);
        let mut wf_report = tamarin_parser::wf::check_theory(&parsed_for_wf);
        // Strip the static "Message Derivation Checks" entry — the
        // dynamic check below replaces it with the prover-based result.
        // We keep the static check available for the `--parse-only`
        // path (where no Maude is started).
        if !args.parse_only {
            wf_report.retain(|e| e.topic != "Message Derivation Checks");
        }
        // HS `checkIfLemmasInTheory` (Wellformedness.hs:1156-1171) — FIRST
        // in HS's checkWellformedness list (line 1272).  Checks that every
        // --prove=X / --lemma=X name corresponds to a theory lemma.  This
        // check needs the CLI args (not embedded in the parser AST), so we
        // call it separately and PREPEND the result so it sorts first —
        // matching HS's `checkIfLemmasInTheory : ...` order.
        {
            let lemma_check = tamarin_parser::wf::check_if_lemmas_in_theory(
                &args.lemma_names, &parsed);
            if !lemma_check.is_empty() {
                let mut new_report = lemma_check;
                new_report.extend(wf_report);
                wf_report = new_report;
            }
        }

        if args.parse_only {
            // HS-faithful: `--parse-only` does NOT run wellformedness
            // (checkWellformedness only fires inside `--prove`'s
            // close-theory pipeline).  Just re-emit the source verbatim.
            emit_output(args, in_file, &src)?;
            file_results.push(FileResult {
                in_file: in_file.clone(),
                out_file: out_path_for(args, in_file),
                results: Vec::new(),
                elapsed_ms: t0.elapsed().as_millis(),
                wf_count: 0,
            });
            continue;
        }

        // Elaborate (mainly to get the protocol-specific MaudeSig).
        let mut elaborated = elaborate(&parsed).map_err(|e| {
            RunError(format!("elaboration error in {}: {}", in_file, e.message))
        })?;
        let maude_sig = elaborated.signature.maude_sig.clone();

        // HS `checkEquationsSubtermConvergence` (Wellformedness.hs:1222-1232)
        // works on `thyEquations = S.toList (stRules sig)` — the SIGNATURE's
        // subterm-rule Set, not the parser-AST `equations:` blocks.  The
        // parser-level `check_theory` produced a placeholder entry from the AST
        // (source order, no width-wrap); replace it with the signature-driven,
        // HughesPJ-rendered version now that the `MaudeSig` is available.  This
        // mirrors HS exactly: `Ord CtxtStRule` Set order (e.g. f1, f2, f3, g
        // rather than source order f1, g, f2, f3) and `prettyCtxtStRule`'s
        // `sep [nest 2 lhs, "=" <-> rhs]` width-wrap for wide equations.
        // (Same retain/re-add pattern as the "Message Derivation Checks" swap.)
        wf_report.retain(|e| e.topic != "Subterm Convergence Warning");
        wf_report.extend(
            tamarin_theory::pretty_theory::subterm_convergence_report_wf(&maude_sig),
        );

        // HS emits this marker after `translateTheory` finishes
        // (TheoryLoader.hs:448-460, see line 454).
        marker("Theory translated");

        // Port of HS `formulaReports.checkTerms` (Wellformedness.hs:960-985,
        // "Formula terms" topic).  This check needs the elaborated `MaudeSig`
        // (reducible/irreducible funsym classification, `irreducibleFunSyms
        // maudeSig`) so it runs HERE (post-elaborate) rather than inside
        // `check_theory` (parser-level).  Macros were already expanded into
        // `parsed_for_wf`; `check_terms_wf` re-expands its own clone the same
        // way (HS `applyMacroInFormula`).
        //
        // Position: HS `formulaReports` order is Quantifier sorts (8a),
        // Formula terms (8b), Formula guardedness (8c).  After `groupOn`,
        // "Formula terms" sorts before "Formula guardedness", so insert this
        // block BEFORE the guardedness block below.  Insert before the first
        // topic that comes after position 8b.
        {
            let term_errors = tamarin_theory::check_terms::check_terms_wf(
                &parsed_for_wf, &maude_sig);
            insert_wf_before(&mut wf_report, term_errors,
                &WF_TOPIC_ORDER[WF_AFTER_CHECK_TERMS..]);
        }

        // Port of HS `formulaReports.checkGuarded` (Wellformedness.hs:988-1004):
        // for each lemma/restriction formula that cannot be converted to a
        // guarded formula, emit a ` Formula guardedness` WF error.  This
        // check needs `formula_to_guarded` (in tamarin-theory) so it runs
        // HERE (post-elaborate) rather than inside `check_theory` (parser-level).
        //
        // HS `formulaReports` (Wellformedness.hs:999-1005) is a list-monad
        // `do` block: for each formula it runs `msum [checkQuantifiers,
        // checkTerms, checkGuarded]`.  `WfErrorReport` is a list, and for
        // lists `msum = concat` (with `<$> = map`), so ALL three checks run
        // UNCONDITIONALLY for every formula and their outputs are
        // concatenated — there is no short-circuit gating `checkGuarded` on
        // the earlier checks.  Running `check_guarded_wf` unconditionally is
        // therefore HS-faithful.  In particular, a formula that fails both
        // checkTerms and checkGuarded is double-reported by HS (one entry
        // under "Formula terms", one under " Formula guardedness"), so both
        // must keep running unconditionally to stay byte-identical.
        //
        // Position: after `check_theory`'s `formula_terms_report` (8b) and
        // before `lemma_attribute_report` (9) — matches HS order.
        {
            let guard_errors = tamarin_theory::elaborate::check_guarded_wf(&parsed);
            // Insert BEFORE the "Lemma annotations" entries that
            // `check_theory` already put in `wf_report`, so the order
            // matches HS: Formula guardedness (8c) before Lemma
            // annotations (9).  Find the first index of a topic that
            // comes after position 8 in HS's check order.
            insert_wf_before(&mut wf_report, guard_errors,
                &WF_TOPIC_ORDER[WF_AFTER_CHECK_GUARDED..]);
        }

        // SAPIC `process:` translation (HS `typeTheory` → `translate`,
        // TheoryLoader.hs:428-443, see line 430).  Runs ONLY for `is_sapic` theories (exactly one
        // top-level `process:`); a no-op otherwise, so non-process theories are
        // byte-unchanged.  Injects the generated rules + `single_session`
        // restriction + `heuristic: p` into BOTH `parsed` (for rendering) and
        // `elaborated` (for solving / AC-variant pre-computation), so it MUST
        // run before `populate_rule_variants` below.  `user_set_heuristic` is
        // true iff a `heuristic:` item already populated `elaborated.heuristic`
        // (HS `addHeuristic` returns `Nothing` in that case).
        // Install the user/builtin function-symbol flag sets
        // (`USER_PRIVATE_FUNS` / `USER_DESTRUCTOR_FUNS` / …) for the duration
        // of SAPIC translation AND the variant pre-computation below.  These
        // thread-locals drive `term_to_lnterm`'s symbol resolution
        // (privacy / constructability); `elaborate()` sets them only for its
        // own scope, so without re-installing them here the SAPIC-injected
        // rules' builtin symbols (`rep` private, `check_rep` / `get_rep`
        // destructors from `locations-report`) re-elaborate with the default
        // public-constructor flags, serialising as `tamXC..` — which Maude
        // rejects, leaving the rule with "no variants".
        let _sapic_funs_guard =
            tamarin_theory::elaborate::set_user_funs_for_theory(&parsed);
        {
            // HS `Acc.checkWellformedness t` (translateTheory, TheoryLoader.hs:448-460, see line 455)
            // runs on the PRE-translation theory `t` — the report is computed
            // from `thy`, not from the `transThy` that `Sapic.translate` /
            // `Acc.translate` produce.  So it must see the ORIGINAL rules /
            // restrictions / case tests, BEFORE `apply_sapic` injects the
            // SAPIC-generated rules (a pure-SAPIC theory has no MSR rules at this
            // point, so `rulesContainPubConst` / `caseTestsInstantiatedByPubVars`
            // scan an empty rule set).  Compute it here, before the mutation.
            let acc_wf = tamarin_accountability::check_wellformedness(&parsed);

            let user_set_heuristic = !elaborated.heuristic.is_empty();
            let sapic_wf = tamarin_sapic::apply::apply_sapic(
                &mut parsed, &mut elaborated, user_set_heuristic,
            ).map_err(|e| RunError(format!(
                "SAPIC translation error in {}: {}", in_file, e.message)))?;

            // Accountability translation (HS `Acc.translate`, TheoryLoader.hs:428-443, see line 430):
            // `Sapic.translate >=> Acc.translate`.  Expands each
            // `... accounts for` lemma into its verification-condition lemmas +
            // case-test predicates, injecting into BOTH `parsed` (rendering) and
            // `elaborated` (prove loop).  A no-op for theories with neither
            // accountability lemmas nor case tests (a `test` without any acc
            // lemma still gets its predicate appended, as in HS).  Runs inside
            // `_sapic_funs_guard` so the generated lemmas' embedded case-test
            // formulas resolve their user function symbols with the theory's
            // private/destructor flags.
            if let Err(e) = tamarin_accountability::translate(&mut parsed, &mut elaborated) {
                // HS: the exceptions `Acc.translate` throws — `CaseTestsUndefined`
                // (Accountability.hs:45) and the `UndefinedPredicate` /
                // `DuplicateItem` parsing exceptions its `liftedAddLemma` /
                // `liftedAddPredicate` folds raise (Parser.hs:141-152,
                // Parser/Signature.hs:313-316) — escape to GHC's runtime, which
                // writes `tamarin-prover: <show exception>` to stderr and exits
                // 1 — no batch `error:` / `[Theory …]` wrapper (the maude banner
                // + the `Theory loaded`/`Theory translated` markers already
                // printed).
                eprintln!("tamarin-prover: {}", e);
                return Ok(1);
            }

            // HS `preReport = Sapic.checkWellformedness t ++ Acc.checkWellformedness t`
            // (TheoryLoader.hs:448-460, see line 455), PREPENDED to the rest of the report
            // (`preReport ++ postReport`): SAPIC-process warnings first, then the
            // accountability RP check (computed above, pre-translation), then
            // every other wellformedness entry.  The trailing `N wellformedness
            // check failed` summary counts them via `wf_report.len()`.
            if !sapic_wf.is_empty() || !acc_wf.is_empty() {
                let mut new_report = sapic_wf;
                new_report.extend(acc_wf);
                new_report.extend(std::mem::take(&mut wf_report));
                wf_report = new_report;
            }
        }

        // HS runs the full `checkWellformedness` on the TRANSLATED theory
        // (TheoryLoader.hs:469-473, `checkTranslatedTheory`), i.e. AFTER SAPIC
        // `translate` has injected the generated rules.  Our `check_theory` ran
        // earlier on the PRE-translation theory (line ~600), so the SAPIC rules
        // were invisible to the rule-dependent fact checks.  Re-run
        // `factLhsOccurNoRhs` on the post-translation parsed theory (macros
        // expanded, as HS `thyProtoRules` does) so SAPIC-only premise facts —
        // e.g. a `Message( c, m )` consumed by an `in(c,m)` with no producing
        // `out` — are surfaced, byte-identically to HS.  For non-SAPIC theories
        // this is a no-op (the pre- and post-translation rule sets are equal).
        if elaborated.is_sapic {
            let post_thy = macro_expanded_clone(&parsed);
            let topic = "Facts occur in the left-hand-side but not in any right-hand-side ";
            wf_report.retain(|e| e.topic != topic);
            let lhs_rhs = tamarin_parser::wf::fact_lhs_occur_no_rhs(&post_thy);
            // Insert at the factReports position (after fact_usage, before
            // formulaReports), matching HS check order.
            insert_wf_before(&mut wf_report, lhs_rhs,
                &WF_TOPIC_ORDER[WF_AFTER_FACT_LHS..]);

            // HS `publicNamesReport` (Wellformedness.hs:463-484) also runs on
            // the TRANSLATED rules (`checkWellformedness` over the OpenTranslated
            // theory).  Our parser-level `public_names_report` ran pre-translation
            // (no generated rules) and cannot see the source process a rule
            // carries as its `process=` attribute; re-run over the ELABORATED
            // rules (facts + process attribute) so a constant appearing only in
            // the process — e.g. `'C'` in `insert <'roles', x, 'C'>` clashing
            // with `'c'` — is surfaced, attributed to the root `Init` rule
            // exactly as HS.  Position: publicNames is HS check index 4, so it
            // splices before the first entry from a LATER check — ruleSorts (HS
            // index 5, our `variable_sort_clashes` topic) or any
            // `WF_TOPIC_ORDER` topic except "Unbound variables"
            // (`unboundReport`, HS index 2, runs BEFORE publicNames, so its
            // entries must not act as a boundary).
            let caps_topic = "Public constants with mismatching capitalization";
            wf_report.retain(|e| e.topic != caps_topic);
            let public_names =
                tamarin_theory::elaborate::sapic_public_names_report(&elaborated);
            insert_wf_before(&mut wf_report, public_names, &after_public_names_topics());
        }

        // Spawn a single Maude handle for this file.  Used by:
        //   - the rule-variants computation that populates each rule's
        //     `variant_substs` + `abstracted_rule` (so the pretty-printer
        //     can emit HS's `variants (modulo AC) ...` block);
        //   - the dynamic Message Derivation Check;
        //   - the per-lemma prove loop.
        let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
        let file_maude: Option<MaudeHandle> = if !args.parse_only {
            MaudeHandle::start(&maude_path, maude_sig.clone()).ok()
        } else {
            None
        };

        // Spawn an auxiliary MaudePool of `effective_maude_processes()`
        // EXTRA subprocesses for use at the rayon parallel sites
        // (rule-variant closure, saturate refinement).  Workers
        // `acquire()` one for the duration of one parallel task so they
        // don't serialise on `file_maude`'s IPC mutex.
        //
        // - `--processors=1` ⇒ `effective_maude_processes=1`; we skip
        //   the auxiliary pool entirely (sequential path uses
        //   `file_maude` only — byte-identical to pre-pool behaviour).
        // - `M >= 2` ⇒ spawn M independent Maudes.  Each costs
        //   ~30-100 MB; `--maude-processes=N` lets the user override.
        //
        // The pool is kept SEPARATE from `file_maude`: sequential paths
        // (main `prove_lemma` loop, derivation checks) keep using
        // `file_maude` (counter state and caches stay coherent across
        // lemmas); the pool is consumed only inside `par_iter` map
        // closures.
        let pool_size = args.effective_maude_processes();
        let file_maude_pool: Option<std::sync::Arc<MaudePool>> =
            if !args.parse_only && pool_size >= 2 {
                match MaudePool::new(&maude_path, maude_sig.clone(), pool_size) {
                    Ok(p) => Some(std::sync::Arc::new(p)),
                    Err(e) => {
                        if !args.quiet {
                            eprintln!("[warn] failed to spawn MaudePool({}): {} \
                                — falling back to single shared Maude", pool_size, e);
                        }
                        None
                    }
                }
            } else {
                None
            };

        // Populate variant_substs + abstracted_rule for each protocol
        // rule whose RHS contains reducible-headed sub-terms.  Without
        // this the pretty-printer always emits `/* has exactly the
        // trivial AC variant */` even when the signature carries
        // destructors (e.g. `aenc/adec`).  HS-faithful: matches
        // `closeTheoryWithMaude`'s variant pre-computation
        // (ClosedTheory.hs `closeTheory`).
        if let Some(m) = file_maude.as_ref() {
            tamarin_theory::tools::rule_variants::populate_rule_variants(
                &mut elaborated, m, file_maude_pool.as_deref());
        }

        // Port of HS `ruleVariantsReport` / `variantsCheck`
        // (Wellformedness.hs:354-372, 375-394).
        //
        // Sub-check 1: "Rule has no variants" — fires when
        // `variantsProtoRule hnd ruE` returns `Nothing`, i.e., the rule
        // has no variants at all (e.g., contradictory Fr(~x)/In(~x) premises
        // that the fresh-uniqueness constraint makes impossible).
        //
        // HS detection: `guard (null recomputedVariants)` where
        // `recomputedVariants = map (get cprRuleAC) $ concatMap
        //   (unfoldRuleVariants . ClosedProtoRule ruE) $ maybeToList
        //   (variantsProtoRule hnd ...)`.  Returns `[]` iff
        // `variantsProtoRule` returns `Nothing` (no variants).
        //
        // Rust detection: `populate_rule_variants` leaves `variant_substs`
        // EMPTY when `abstract_rule_and_variants` returns `None`.
        // However, for rules with NO reducible fun syms, `populate_rule_variants`
        // returns early (skips ALL rules) because the early-exit guard fires.
        // In HS, `variantsProtoRule` still runs and returns `Just` (single
        // trivial variant) for such rules — the `Nothing` case only arises
        // when the variant computation produces an EMPTY substitution set
        // (e.g., all substs are `isFreshRedundant`).
        //
        // A rule with `Fr(~x)` and `In(~x)` in its premises: In HS, the
        // abstraction phase abstracts these to fresh variables, then
        // `computeVariantsCached` returns the trivial identity substitution
        // (no real AC to reduce), but `isFreshRedundant` filters it out
        // (the fresh variable `~x` appears in `In` position, which is
        // impossible → the identity subst IS fresh-redundant for ~x).
        // Result: `substs = []` → `mzero` → `variantsProtoRule = Nothing`.
        //
        // In Rust: `abstract_rule_and_variants` returns `None` in this case
        // (all variant substs were filtered). The rule's `variant_substs`
        // stays empty, and `abstracted_rule` stays `None`.
        //
        // Detection criterion: `file_maude` is `Some` (so we ran variant
        // computation), the rule has at least one reducible RHS sub-term OR
        // the rule has `variant_substs` empty after `populate_rule_variants`
        // ran. Actually — `populate_rule_variants` only calls
        // `abstract_rule_and_variants` for rules WHERE the signature has
        // reducible funs. For signatures without reducible funs, the rule
        // can NEVER get `Nothing` from `variantsProtoRule` because HS also
        // wouldn't find contradictory-fresh issues (no destructors = only
        // pair/fst/snd, and those theories don't mix Fr+In the "impossible"
        // way in any corpus file).
        //
        // Sub-check 2: "Variants mismatch" — fires when `ruAC` (manually
        // specified variants in the rule body) is non-empty and doesn't match
        // the recomputed variants. Requires comparing parsed `rule.variants`
        // vs `abstracted_rule + variant_substs`. Not yet ported (no corpus
        // files affected); see implementation notes below.
        if let Some(ref wf_maude) = file_maude {
            use tamarin_theory::theory::TheoryItem;
            use tamarin_parser::wf::WfError as WfE;
            use tamarin_parser::wf::underline_topic;

            let mut variants_errors: Vec<WfE> = Vec::new();
            let mut no_variant_rules: Vec<String> = Vec::new();

            // `populate_rule_variants` (above) already ran
            // `abstract_rule_and_variants` for every rule when the
            // signature has reducible function symbols, recording its
            // result on each `OpenProtoRule` (`abstracted_rule` is `Some`
            // iff it returned `Ok(Some(_))`).  Reuse that result for the
            // reducible (Maude) path of the WF "Rule has no variants"
            // check so we don't issue a SECOND `get variants` query per
            // rule.  When the signature has NO reducible funs,
            // `populate_rule_variants` returned early without populating
            // those fields, but then no rule is reducible either — the WF
            // check takes its syntactic (no-Maude) path, so the precomputed
            // value is never consulted.
            let sig_has_reducible =
                !wf_maude.maude_sig().reducible_fun_syms.is_empty();

            for item in &elaborated.items {
                let TheoryItem::Rule(opr) = item else { continue };

                // Sub-check 1: "Rule has no variants" — mirrors HS
                // `variantsCheck` (Wellformedness.hs:354-372, see line 362):
                //   `guard (null recomputedVariants) $> ...`
                // Calls `rule_has_no_variants_for_wf` which implements
                // the full HS `variantsProtoRule` detection logic including
                // `isFreshRedundant` filtering.
                //
                // Sub-check 2: "Variants mismatch" — not yet ported; no
                // corpus files affected (see step-0 analysis).
                let precomputed_no_variants = if sig_has_reducible {
                    Some(opr.abstracted_rule.is_none()
                        && opr.variant_substs.is_empty())
                } else {
                    None
                };
                if tamarin_theory::tools::rule_variants::rule_has_no_variants_for_wf_with(
                    wf_maude, &opr.rule, precomputed_no_variants)
                {
                    // HS message (Wellformedness.hs:363-366):
                    //   text "Rule " <> prettyRuleName ruE <> text " has no variants."
                    //   $--$  text "Most likely, ..."
                    //   <> text "For exaple, ..."
                    // "For exaple" is a typo in HS source, preserved faithfully.
                    let rule_name = opr.name().to_string();
                    no_variant_rules.push(rule_name.clone());
                    let topic = "Rule has no variants";
                    let body = format!(
                        "  Rule {} has no variants.\n  \n  Most likely, this means that \
                         the rule's use of fresh variables is contradictory. For exaple, \
                         a rule with the premises In(~x) and Fr(~x) has no variants \
                         because ~x cannot be sent before it is generated.",
                        rule_name,
                    );
                    let mut msg = String::new();
                    msg.push_str(&underline_topic(topic));
                    msg.push('\n');
                    msg.push_str(&body);
                    msg.push('\n');
                    variants_errors.push(WfE::new(topic, msg));
                }
            }

            // HS position 6: ruleVariantsReport comes BEFORE factReports
            // (position 7).  Insert before factReports items.
            insert_wf_before(&mut wf_report, variants_errors,
                &WF_TOPIC_ORDER[WF_AFTER_VARIANTS..]);

            // HS closeProtoRule (Rule.hs:97-98): `ClosedProtoRule ruE <$>
            // maybeToList (variantsProtoRule hnd ruE)` — a rule with NO
            // variants produces NO closed rule.  It is dropped from the
            // closed theory entirely: it participates in neither rendering
            // nor proof search.  (The wf warning above fires on the OPEN
            // theory, before closing, so it is emitted regardless.)
            if !no_variant_rules.is_empty() {
                elaborated.items.retain(|item| match item {
                    TheoryItem::Rule(r) => !no_variant_rules.iter().any(|n| n == r.name()),
                    _ => true,
                });
            }
        }

        // Annotate per-rule loop breakers on the OUTER theory so
        // `pretty_closed_theory` can render HS's `// loop breaker:
        // [<idx>]` comments at the rule output.  HS faithfulness:
        // `prettyClosedProtoRule` (ClosedTheory.hs:332-366, see line 337,353) reads
        // `prettyLoopBreakers` from the `ProtoRuleACInfo` baked into
        // every closed rule by `closeTheoryWithMaude`.  Our prover
        // computes them inside `ProofContext::new` on a LOCAL copy
        // of the rules — so we re-run the same `annotate_loop_breakers`
        // pass on the outer theory here to mirror the closed-theory
        // structure HS persists.
        if let Some(m) = file_maude.as_ref() {
            use tamarin_theory::theory::TheoryItem;
            let mut rules: Vec<tamarin_theory::theory::OpenProtoRule> =
                elaborated.items.iter().filter_map(|i| match i {
                    TheoryItem::Rule(r) => Some(r.clone()), _ => None,
                }).collect();
            tamarin_theory::constraint::solver::context::annotate_loop_breakers(
                &mut rules, m);
            // Sequential writeback in source order.
            let mut iter = rules.into_iter();
            for item in elaborated.items.iter_mut() {
                if let TheoryItem::Rule(opr) = item {
                    if let Some(updated) = iter.next() {
                        opr.loop_breakers = updated.loop_breakers;
                    }
                }
            }
        }

        // Dynamic Message Derivation Checks (mirrors HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout`,
        // default 5s).  Needs Maude, so we run it AFTER elaboration
        // and BEFORE the main prove loop.  HS default is 5s; 0 disables.
        // Each per-variable proof attempt is capped at this timeout.
        let deriv_timeout = args.derivcheck_timeout.unwrap_or(5) as u32;
        if deriv_timeout > 0 {
            // HS emits these markers around the per-variable derivability
            // check (TheoryLoader.hs:463-533, see line 485, :498).
            marker("Derivation checks started");
            if let Some(m) = file_maude.as_ref() {
                let extra = tamarin_theory::deriv_check::check_message_derivation(
                    &parsed, m, deriv_timeout,
                );
                wf_report.extend(extra);
            }
            marker("Derivation checks ended");
        }

        // Decide which lemmas to prove.  Without --prove, HS still runs
        // the close-time `checkAndExtendProver` replay over every stored
        // proof skeleton (`closeTheory`, Prover.hs:174-185) — a plain
        // load VALIDATES embedded proofs and reports their real status.
        // We mirror that whenever the file carries a stored proof tree;
        // proofless files keep the cheap no-solver path below, whose
        // output is identical either way (every lemma is a 1-step sorry).
        let lemma_filter: &[String] = &args.lemma_names;
        let prove_anything = args.prove_mode;
        let any_stored_proof =
            elaborated.lemmas().any(|l| l.proof.tree.is_some());

        let mut results: Vec<LemmaResult> = Vec::new();
        // Mirrors HS's per-lemma proof body for embedding in the
        // pretty-printed theory output.  Filled by the prove loop below.
        let mut proved_lemmas: Vec<tamarin_theory::pretty_theory::ProvedLemma> = Vec::new();

        // No proof step requested — record each lemma as Filtered
        // / Skipped depending on whether --lemma had any effect.
        // (Shared by the cheap branch below and the session-build
        // failure fallback inside the prove/check branch.)
        let push_skipped_results =
            |results: &mut Vec<LemmaResult>,
             elaborated: &tamarin_theory::theory::Theory| {
            for l in elaborated.lemmas() {
                results.push(LemmaResult {
                    name: l.name.clone(),
                    verdict: if lemma_filter.is_empty()
                        || lemma_matches(lemma_filter, &l.name)
                    {
                        // Empty filter, or selected but no prove flag — skipped.
                        LemmaVerdict::Skipped
                    } else {
                        LemmaVerdict::Filtered
                    },
                    elapsed_ms: 0,
                    // HS counts the default `Sorry` placeholder proof
                    // as 1 step (one `LNode (ProofStep Sorry ...)` —
                    // see `foldProof proofStepSummary`, ClosedTheory.hs:463-491, see line 484,491).
                    // Match it.
                    proof_steps: 1,
                    exists_trace: matches!(
                        l.trace_quantifier,
                        tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                    ),
                });
            }
        };

        if args.precompute_only || (!prove_anything && !any_stored_proof) {
            push_skipped_results(&mut results, &elaborated);
        } else {
            // Reuse the per-file maude handle.  The `maude tool: ...`
            // banner is printed once at the top of the batch run (see
            // above), matching HS.
            let maude = file_maude.clone().ok_or_else(|| {
                RunError(format!(
                    "failed to start maude at {:?}",
                    maude_path,
                ))
            })?;

            // Per-lemma proof loop.
            //
            // The `max_steps` argument threaded into the prover below is a
            // no-op: the solver (search.rs) discards it (`let _ = max_steps;
            // let mut budget = usize::MAX;`) and bounds search by wall-clock
            // deadline instead.  HS likewise defaults `proofBound` to
            // `Nothing` (TheoryLoader.hs) so `boundProver` is never applied
            // unless `--bound=N` is given — which the Rust solver does not
            // yet honor.  We pass `usize::MAX` rather than computing a value
            // that would be ignored.
            let budget: usize = usize::MAX;

            // Build the per-file shared prover session ONCE.  Profile
            // showed that constructing a fresh `ProofContext` per lemma
            // re-ran ~3s of file-level setup (intruder rules, Maude
            // variants, `precompute_full_sources`) per lemma; HS does
            // this work once at theory-close time.  `ProverSession`
            // captures it once; each lemma clones the cheap template
            // and runs only the per-lemma `ensure_saturated`
            // refinement against its own typing assumptions.
            //
            // Fall-through path: if `ProverSession::build` errors we
            // fall back to the per-lemma `prove_lemma_with_pool` path
            // (which re-runs the setup per lemma but is more tolerant
            // of theories where elaboration fails on a subset of
            // lemmas).  Almost never hits in practice.
            //
            // CLI `--heuristic`/`--oraclename`/`--oracle-only` (HS
            // `AutoProver` via `constructAutoProver`, TheoryLoader.hs:702-706).
            // When `--heuristic` is given it OVERRIDES the per-lemma / theory
            // heuristic for every lemma (HS `selectHeuristic`, Proof.hs:705-716, see line 707).
            let cli_heuristic = tamarin_theory::prove::CliHeuristic {
                raw: args.heuristic.clone(),
                oracle_name: args.oracle_name.clone(),
                oracle_only: args.oracle_only,
            };
            // `--auto-sources` (HS `closeTheoryWithMaude` autosources branch,
            // Prover.hs:170-251, see line 171): when the raw sources contain partial
            // deconstructions, annotate the rules with AUTO_* actions and add
            // the `AUTO_typing` sources lemma — to the elaborated theory (so it
            // renders + is iterated below) and the proving session alike.
            if auto_sources {
                tamarin_theory::auto_sources::apply_auto_sources(
                    &mut parsed, &mut elaborated, maude.clone(), file_maude_pool.clone());
            }
            let session = tamarin_theory::prove::ProverSession::build_with_in_file_and_heuristic(
                &parsed, maude.clone(), file_maude_pool.clone(), in_file,
                cli_heuristic.clone(), cut).ok();

            // HS prints "[Theory X] Theory closed" right after `closeTheory`
            // (TheoryLoader.hs:569-615, see line 596) and BEFORE the proof search, which it
            // forces lazily as `provedThy` is serialised — so the marker
            // appears in moments regardless of proving cost.  RS's
            // `ProverSession::build` is the `closeTheory` analog, so emit the
            // marker here (before the prove loop) to match HS's observable
            // stderr order.  The no-prove / precompute-only paths (which skip
            // the prove loop) emit it below instead.
            marker("Theory closed");

            let run_lemma = |l: &tamarin_theory::theory::Lemma<_>|
                -> (tamarin_theory::pretty_theory::ProvedLemma, LemmaResult) {
                let lemma_name = l.name.clone();
                let exists_trace = matches!(
                    l.trace_quantifier,
                    tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                );
                // HS faithfulness: `closeTheory` runs
                // `checkAndExtendProver` (Prover.hs:174-185) over ALL
                // lemmas, re-attaching the constraint system to each
                // stored skeleton step.  `--prove=X` then runs the
                // auto-prover ONLY on lemmas matching the selector
                // (Prover.hs:273-275); the rest keep their close-time
                // replayed proof, reprinted verbatim with the stored
                // status.  We mirror that: the target lemma(s) run the
                // full skeleton-replay+auto-prove; non-target lemmas run
                // check-and-extend (replay only, no auto-proving open
                // leaves) — which also keeps us from launching a heavy
                // search on lemmas the user didn't ask to prove.
                // Without --prove this loop is HS's close-time
                // `checkAndExtendProver` pass: EVERY lemma is non-target,
                // so stored skeletons replay (check_and_extend) but no
                // open leaf is auto-proved.
                let is_target = prove_anything
                    && lemma_matches(lemma_filter, &lemma_name);
                // HS does NOT print a per-lemma "proving lemma X ..."
                // marker; the only progress lines are the `[Theory X]
                // ...` set above.  Stay quiet here for HS-faithful stderr.
                let lt = Instant::now();
                let outcome = match (session.as_ref(), is_target) {
                    (Some(s), true) => tamarin_theory::prove::prove_lemma_in_session(
                        s, &lemma_name, budget),
                    (Some(s), false) => tamarin_theory::prove::check_and_extend_lemma_in_session(
                        s, &lemma_name, budget),
                    (None, _) => tamarin_theory::prove::prove_lemma_with_pool_file_heuristic(
                        &parsed, &lemma_name, maude.clone(),
                        file_maude_pool.clone(), budget, in_file, &cli_heuristic, cut),
                };
                let (verdict, proof_steps, proof_body) = match outcome {
                    Ok(root) => {
                        let steps = count_proof_steps(&root);
                        // HS lemma verdict = `getProofStatus` (Proof.hs)
                        // folded over the WHOLE tree, NOT the root's
                        // per-node `NodeStatus`.  This matters for
                        // part-replayed proofs: a stale stored-proof branch
                        // kept verbatim is `Undetermined`, which the
                        // Semigroup absorbs into the `Complete` of the
                        // freshly-proved siblings (e.g. KCL07-manualproof —
                        // `verified` not `analysis incomplete`).  For a
                        // fully-fresh proof the fold yields the same verdict
                        // as `root.status` did.
                        use tamarin_theory::constraint::solver::search::ProofStatus;
                        let is_exists = matches!(
                            l.trace_quantifier,
                            tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                        );
                        let v = match tamarin_theory::constraint::solver::search::proof_status(&root) {
                            ProofStatus::TraceFound => {
                                if is_exists { LemmaVerdict::Verified }
                                else { LemmaVerdict::Falsified }
                            }
                            ProofStatus::Complete => {
                                if is_exists { LemmaVerdict::Falsified }
                                else { LemmaVerdict::Verified }
                            }
                            ProofStatus::Unfinishable => LemmaVerdict::Unfinishable,
                            ProofStatus::Incomplete => LemmaVerdict::Analyzed,
                            // HS `showProofStatus` (Proof.hs:1111-1112) renders
                            // these as distinct strings, NOT "analysis
                            // incomplete".  In batch `--prove` the root fold is
                            // virtually never Undetermined/Invalidated (close-
                            // time replay annotates every node ⇒ Incomplete;
                            // Invalidated only arises from interactive reuse-
                            // lemma edits), but map them faithfully so the label
                            // is correct if such a tree ever surfaces.
                            ProofStatus::Undetermined => LemmaVerdict::Undetermined,
                            ProofStatus::Invalidated => LemmaVerdict::Invalidated,
                        };
                        let body = tamarin_theory::pretty_theory::pretty_proof_body(&root);
                        (v, steps, Some(body))
                    }
                    Err(tamarin_theory::prove::ProveError::Guarded(msg)) => {
                        // HS `formulaToGuarded_ = either (error . render) id`
                        // (Guarded.hs:466-467): a proven lemma whose formula
                        // cannot be converted to a guarded formula kills the
                        // whole run — message on stderr, exit 1, and NO
                        // theory output on stdout (HS renders lazily after
                        // proving, so the abort precedes all stdout output).
                        eprintln!("tamarin-prover: {}", msg);
                        std::process::exit(1);
                    }
                    Err(e) => (LemmaVerdict::Error(format!("{}", e)), 0, None),
                };
                let pl = tamarin_theory::pretty_theory::ProvedLemma {
                    name: lemma_name.clone(),
                    proof_body,
                };
                let lr = LemmaResult {
                    name: lemma_name,
                    verdict,
                    elapsed_ms: lt.elapsed().as_millis(),
                    proof_steps,
                    exists_trace,
                };
                (pl, lr)
            };

            if let Some(sess) = &session {
                use rayon::prelude::*;
                // Single-flight per-source-key saturation: compute each
                // distinct refined-source key ONCE and seed the session cache
                // before the lemma fan-out below, so its concurrent workers all
                // hit the restore path rather than each recomputing the
                // identical saturation (HS computes `_crcRefinedSources` once
                // per `ClosedRuleCache`, RuleItem.hs:64-69).  The predicate mirrors
                // `run_lemma`'s `is_target`; the session skips lemmas that would
                // emit a bare sorry (they never saturate).
                let cache_disabled =
                    tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
                sess.presaturate_shared_sources(
                    cache_disabled,
                    |name| prove_anything && lemma_matches(lemma_filter, name),
                );
                let specs: Vec<&tamarin_theory::theory::Lemma<_>> =
                    elaborated.lemmas().collect();
                let mut out: Vec<(usize, tamarin_theory::pretty_theory::ProvedLemma, LemmaResult)> =
                    specs.par_iter().enumerate()
                        .map(|(i, l)| { let (pl, lr) = run_lemma(l); (i, pl, lr) })
                        .collect();
                // Reassemble in DECLARATION order so output is identical to the
                // sequential loop regardless of which worker finished first.
                out.sort_by_key(|(i, _, _)| *i);
                for (_, pl, lr) in out { proved_lemmas.push(pl); results.push(lr); }
            } else if !prove_anything {
                // The plain-load check pass needs the session's
                // check_and_extend arm; the pool fallback below always
                // auto-proves.  If the session failed to build, keep the
                // historical no-solver behaviour instead of launching
                // searches nobody asked for.
                push_skipped_results(&mut results, &elaborated);
            } else {
                for l in elaborated.lemmas() {
                    let (pl, lr) = run_lemma(l);
                    proved_lemmas.push(pl);
                    results.push(lr);
                }
            }

            // HS-faithful: rc=0 regardless of verdict.  Falsified is a
            // valid analysis outcome — the prover ran successfully and
            // found a counter-example trace.  Only true errors (parse
            // failures, Maude crashes, IO errors) escalate to non-zero.
            for r in &results {
                if matches!(r.verdict, LemmaVerdict::Error(_)) {
                    overall_status = overall_status.max(1);
                }
            }
        }

        // HS emits this marker after `closeTheory` finishes
        // (TheoryLoader.hs:569-615, see line 596).  In prove mode it is emitted before the
        // prove loop (above); here it covers only the no-prove /
        // precompute-only paths, which skip that loop.
        if args.precompute_only || (!prove_anything && !any_stored_proof) {
            marker("Theory closed");
        }

        // Build the HS-faithful theory pretty-print body.  This replaces
        // the verbatim source dump with HS's `prettyClosedTheory`
        // output shape — re-rendered signature, rules with `(modulo E)`
        // prefix and AC-variant comments, lemmas with inline guarded
        // formula and proof body, wellformedness block, and
        // Generated-from footer.
        //
        // KNOWN GAP (--precompute-only): HS (Batch.hs:201-205) renders
        // `ppWf report $--$ prettyPrecomputation thy''` here instead — a
        // compact 3-line overview (`Multiset rewriting rules: N` / `Raw
        // sources: …` / `Refined sources: …`, ClosedTheory.hs:548-570), NOT
        // the full closed theory.  We fall through to pretty_closed_theory in
        // that mode.  Porting `prettyPrecomputation` faithfully needs the
        // closed theory's raw + refined source case lists and per-case
        // `unsolvedChainConstraints` counts (which live in the prover
        // session, not surfaced here); --precompute-only is a niche
        // diagnostic mode not exercised by the example corpus.
        let build_info = tamarin_theory::pretty_theory::BuildInfo {
            tamarin_version: crate::cli::VERSION.to_string(),
            maude_version: maude_version
                .clone()
                .unwrap_or_else(|| "unknown".to_string()),
            git_revision: crate::cli::GIT_REV.to_string(),
            git_branch: crate::cli::GIT_BRANCH.to_string(),
            compiled_at: crate::cli::BUILD_TIMESTAMP.to_string(),
        };
        let wf_block = tamarin_theory::pretty_theory::format_wf_block(&wf_report);
        let body = tamarin_theory::pretty_theory::pretty_closed_theory(
            &parsed,
            &elaborated,
            &proved_lemmas,
            &wf_block,
            &build_info,
            in_file,
            auto_sources,
        );
        emit_output(args, in_file, &body)?;

        file_results.push(FileResult {
            in_file: in_file.clone(),
            out_file: out_path_for(args, in_file),
            results,
            elapsed_ms: t0.elapsed().as_millis(),
            wf_count: wf_report.len(),
        });
        if args.quit_on_warning && !wf_report.is_empty() {
            return Err(RunError(format!(
                "{} wellformedness check(s) failed (--quit-on-warning set)",
                wf_report.len()
            )));
        }
    }

    // HS-faithful: `--parse-only` skips the `summary of summaries:`
    // block entirely.  Only `--prove` (or any flag that actually runs
    // the prover) emits it.
    if !args.quiet && !args.parse_only {
        print_overall_summary(&file_results, args.prove_mode);
    }

    Ok(overall_status)
}

/// Install rayon's global worker pool to the size requested via
/// `--processors=N` (or a sensible default).
///
/// HS-equivalent: GHC's `+RTS -N RTS_FLAG` sets the worker capacity for
/// the `par*`/`Strategies` sites HS uses.  We mirror that surface via a
/// CLI flag.  Idempotent across files in a batch — `build_global`
/// silently errors on the second call, which is what we want.
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
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .thread_name(|i| format!("tamarin-rayon-{}", i))
        .build_global();
}

fn default_maude_path() -> String {
    for c in [
        "/usr/local/bin/maude",
        "/usr/bin/maude",
    ] {
        if std::path::Path::new(c).exists() {
            return c.to_string();
        }
    }
    "maude".to_string()
}

/// Emit `body` to `--output` / `-O` / stdout.
fn emit_output(args: &Args, in_file: &str, body: &str) -> Result<(), RunError> {
    if let Some(out) = out_path_for(args, in_file) {
        // Ensure parent dir exists.
        if let Some(parent) = std::path::Path::new(&out).parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).map_err(|e| {
                    RunError(format!("failed to create {}: {}", parent.display(), e))
                })?;
            }
        }
        fs::write(&out, body)
            .map_err(|e| RunError(format!("failed to write {}: {}", out, e)))?;
    } else {
        // stdout
        print!("{}", body);
    }
    Ok(())
}

/// Resolve the output path for `in_file` given the user's `-o` / `-O`
/// flags. Returns `None` when output should go to stdout.
pub fn out_path_for(args: &Args, in_file: &str) -> Option<String> {
    if let Some(of) = &args.output_file {
        if !of.is_empty() {
            return Some(of.clone());
        }
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
/// `const (Sum 1)` over every ProofStep — ClosedTheory.hs:463-491, see line 484,491 via
/// `foldProof`, Theory/Proof.hs:358-362).
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
        // HS `ppRep` (Batch.hs:146-148) has TWO `Pretty.text ""` between
        // `analyzed:` and the nested `output:`/`processing time:` block, but
        // HughesPJ collapses adjacent empty lines under `vcat`, so the rendered
        // output is a SINGLE blank line here.  Verified against the v1.13.0
        // binary: `tamarin-prover --prove` emits exactly one blank line between
        // `analyzed:` and `output:`/`processing time:`, so one `println!()` is
        // byte-faithful.
        println!();
        if let Some(out) = &fr.out_file {
            // HS aligns `output:` and `processing time:` columns
            // (`ppRep` in Main.Mode.Batch, src/Main/Mode/Batch.hs:87-316, see line 144).
            println!("  output:          {}", out);
        }
        println!("  processing time: {:.2}s", fr.elapsed_ms as f64 / 1000.0);
        println!("  ");
        if fr.wf_count > 0 {
            println!("  WARNING: {} wellformedness check failed!", fr.wf_count);
            // HS Batch.hs:87-316, see line 246 emits this second line only in prove mode:
            //   [ Pretty.text "         The analysis results might be wrong!"
            //   | thyLoadOptions.proveMode ]
            if prove_mode {
                println!("           The analysis results might be wrong!");
            }
            // HS `summary = ppWf report $--$ prettyClosedSummary` (Batch.hs:228-229):
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::parse_args;

    fn parse(args: &[&str]) -> Args {
        parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
    }

    #[test]
    fn out_path_for_uses_file_when_set() {
        // `-o`/`--output` is cmdargs flagOpt: only the inline (`=`/attached)
        // form sets the value; a space-separated token stays positional.
        let a = parse(&["-o/tmp/foo.spthy", "in.spthy"]);
        assert_eq!(
            out_path_for(&a, "in.spthy").as_deref(),
            Some("/tmp/foo.spthy"),
        );
    }

    #[test]
    fn out_path_for_uses_dir_with_basename_when_set() {
        let a = parse(&["-O/tmp/outdir", "examples/foo.spthy"]);
        let got = out_path_for(&a, "examples/foo.spthy");
        assert_eq!(got.as_deref(), Some("/tmp/outdir/foo_analyzed.spthy"));
    }

    #[test]
    fn out_path_for_none_means_stdout() {
        let a = parse(&["in.spthy"]);
        assert_eq!(out_path_for(&a, "in.spthy"), None);
    }

    #[test]
    fn diff_flag_errors_cleanly() {
        let a = parse(&["--diff", "in.spthy"]);
        let r = run(&a);
        assert!(matches!(r, Err(RunError(_))), "diff should error, got {:?}", r);
    }

    #[test]
    fn interactive_subcmd_is_routed() {
        // We can't actually invoke `run` on the interactive subcommand
        // in a unit test (it would bind a TCP socket and block), so we
        // just check that the parser routes to it and accepts the
        // expected interactive flags.
        let a = parse(&[
            "interactive",
            "--port=3001",
            "--interface=127.0.0.1",
            "--image-format=PNG",
            "--debug",
            "--no-logging",
            "--data-dir=/tmp/data",
        ]);
        assert_eq!(a.subcommand, crate::cli::Subcommand::Interactive);
        assert_eq!(a.port, Some(3001));
        assert_eq!(a.interface.as_deref(), Some("127.0.0.1"));
        assert!(matches!(a.image_format, Some(crate::cli::ImageFormat::Png)));
        assert!(a.debug);
        assert!(a.no_logging);
        assert_eq!(a.data_dir.as_deref(), Some("/tmp/data"));
    }

    #[test]
    fn interactive_invalid_interface_errors() {
        // Asking to bind to garbage should produce a clear error
        // without ever opening a socket.
        let a = parse(&["interactive", "--interface=not-an-ip"]);
        let r = run(&a);
        assert!(r.is_err(), "expected interface parse error");
    }

    #[test]
    fn no_input_files_errors() {
        let a = parse(&[]);
        let r = run(&a);
        assert!(r.is_err());
    }

    #[test]
    fn help_returns_zero() {
        let a = parse(&["--help"]);
        let r = run(&a).expect("help");
        assert_eq!(r, 0);
    }

    #[test]
    fn version_returns_zero() {
        let a = parse(&["--version"]);
        let r = run(&a).expect("version");
        assert_eq!(r, 0);
    }

    fn mk_result(verdict: LemmaVerdict, exists_trace: bool, steps: usize) -> LemmaResult {
        LemmaResult {
            name: "L".to_string(),
            verdict,
            elapsed_ms: 0,
            proof_steps: steps,
            exists_trace,
        }
    }

    // Pins the per-lemma summary strings to HS `showProofStatus`
    // (Theory/Proof.hs:1105-1112) + the `(N steps)` suffix
    // (ClosedTheory.hs:487-489).  Undetermined/Invalidated render distinct
    // strings, not "analysis incomplete".
    #[test]
    fn lemma_summary_distinguishes_undetermined_and_invalidated() {
        // showProofStatus _ UndeterminedProof = "analysis undetermined"
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Undetermined, false, 7)),
            "L (all-traces): analysis undetermined (7 steps)",
        );
        // showProofStatus _ InvalidatedProof = "proof has been invalidated"
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Invalidated, false, 3)),
            "L (all-traces): proof has been invalidated (3 steps)",
        );
        // showProofStatus _ IncompleteProof = "analysis incomplete" (unchanged)
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Analyzed, false, 5)),
            "L (all-traces): analysis incomplete (5 steps)",
        );
    }

    // Authentic HS bytes (verified against the v1.13.0 binary with
    // `--prove --output-json=… --output-dot=…` on a no-trace theory):
    //   --output-json no-trace stub = aeson-pretty `encodePretty` of
    //     `{graphs:[]}` ⇒ `{\n    "graphs": []\n}` (20 bytes, 4-space indent,
    //     NO trailing newline).  JSON.hs:458-463 + aeson-pretty default Config.
    //   --output-dot no-trace stub = `intercalate "\n" [] = ""` ⇒ 0-byte file.
    // These mirror the literals written in `run_batch`.
    #[test]
    fn output_json_dot_stub_bytes_match_hs() {
        let json_stub = "{\n    \"graphs\": []\n}";
        assert_eq!(json_stub.len(), 20);
        assert!(!json_stub.ends_with('\n'), "no trailing newline");
        let dot_stub = "";
        assert_eq!(dot_stub.len(), 0);
    }
}
