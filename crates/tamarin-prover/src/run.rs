// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! theory to stdout (HS `prettyOpenTheory`, Batch.hs:91-95 — always stdout,
//! `-o`/`-O` are ignored there); `-m`/`--output-module` (Batch.hs:101-113)
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

use tamarin_parser::wf::{after_variants_topics, insert_wf_before};
use tamarin_term::maude_proc::{MaudeHandle, MaudePool, SharedMaudeCaches};
use tamarin_theory::constraint::system::System;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::macro_expand::macro_expanded_clone;
use tamarin_theory::module::ModuleType;

use crate::cli::{lemma_matches, Args, Subcommand};

thread_local! {
    /// Progress-marker lines the panic hook must print BEFORE a marked HS
    /// `error` block, bridging a laziness gap: GHC leaves ill-formed rule
    /// terms unforced through translation, so `Term.fAppAC: empty argument
    /// list` (Raw.hs:120) escapes only once the close pipeline forces them —
    /// after the `Theory translated` marker and, unless `--no-ndc`, the two
    /// `No Deconstruction Chain checks` markers.  The port's `elaborate`
    /// builds the same terms eagerly, between `Theory loaded` and `Theory
    /// translated`; the batch loop parks the not-yet-printed marker lines
    /// here for the span of that call so the hook can replay HS's sequence.
    static DEFERRED_HS_ERROR_MARKERS: std::cell::Cell<Option<String>> =
        const { std::cell::Cell::new(None) };
}

/// Marker lines the panic hook must emit before its `tamarin-prover: …`
/// report, if any (see [`DEFERRED_HS_ERROR_MARKERS`]); consumed on read.
/// Thread-local, so the hook only sees lines parked by the panicking thread
/// itself — a panic on any other thread reports without a prefix.
pub fn take_deferred_hs_error_markers() -> Option<String> {
    DEFERRED_HS_ERROR_MARKERS.take()
}

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
    let quantifier = if r.exists_trace {
        "exists-trace"
    } else {
        "all-traces"
    };
    let body = match &r.verdict {
        // HS `showProofStatus` (Theory/Proof.hs:1105-1108): a falsified
        // exists-trace lemma is a `CompleteProof` of `ExistsSomeTrace`
        // ("falsified - no trace found"), whereas a falsified all-traces
        // lemma is a `TraceFound` for `ExistsNoTrace` ("falsified - found
        // trace").  The wording therefore depends on the quantifier.
        LemmaVerdict::Falsified if r.exists_trace => {
            format!("falsified - no trace found ({} steps)", r.proof_steps)
        }
        LemmaVerdict::Falsified => format!("falsified - found trace ({} steps)", r.proof_steps),
        LemmaVerdict::Verified => format!("verified ({} steps)", r.proof_steps),
        LemmaVerdict::Analyzed | LemmaVerdict::Skipped | LemmaVerdict::Filtered => {
            format!("analysis incomplete ({} steps)", r.proof_steps)
        }
        // HS `showProofStatus _ UnfinishableProof` (Theory/Proof.hs:1104-1112, see line 1109).
        LemmaVerdict::Unfinishable => format!(
            "analysis cannot be finished (reducible operators in subterms) ({} steps)",
            r.proof_steps
        ),
        // HS `showProofStatus _ UndeterminedProof` (Theory/Proof.hs:1104-1112, see line 1111).
        LemmaVerdict::Undetermined => format!("analysis undetermined ({} steps)", r.proof_steps),
        // HS `showProofStatus _ InvalidatedProof` (Theory/Proof.hs:1104-1112, see line 1112).
        LemmaVerdict::Invalidated => {
            format!("proof has been invalidated ({} steps)", r.proof_steps)
        }
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
        // HS installs one `TamarinMode` per command and `defaultMain` dispatches
        // on the mode BEFORE the mode's own `run` sees `--help`
        // (Console.hs:333-338, 362-372), so each command prints its own help
        // text.  `--help` is answered here, after `parse_args` has fixed the
        // subcommand, for the same reason.
        println!("{}", crate::cli::help_text(args.subcommand));
        return Ok(0);
    }
    if args.show_version {
        // HS (Console.hs:326-330) splits the two streams: the banner +
        // license + `Generated from:` block go to STDOUT, the three maude
        // self-check lines to STDERR (`ensureMaude` -> `hPutStrLn stderr`).
        // version_text() already carries its own trailing newline.
        print!("{}", crate::cli::version_text(&maude_invocation_path(args)));
        eprintln!(
            "{}",
            crate::cli::version_maude_stderr_text(
                &maude_display_name(args),
                &maude_invocation_path(args),
            )
        );
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
fn run_test(args: &Args) -> Result<i32, RunError> {
    println!("Self-testing the tamarin-prover installation.\n");
    println!("*** Testing the availability of the required tools ***");
    let mv = crate::cli::detect_maude_version_at(&maude_invocation_path(args));
    match &mv {
        Some(v) => println!("{}. OK.\n checking installation: OK.", v),
        None => {
            eprintln!("Maude check FAILED — not found on $PATH.");
            return Ok(1);
        }
    }
    // HS `ensureGraphVizDot` (Test.hs:50) reads `dotPath`
    // (Environment.hs:37-38): the `--with-dot` value, else the bare `"dot"`.
    let dot_cmd = args.dot_path.as_deref().unwrap_or("dot");
    let dot = std::process::Command::new(dot_cmd).arg("-V").output();
    // HS `successGraphVizDot = isJust maybeSuccessGraphVizDot` (Test.hs:42-112, see line 51):
    // a missing/unavailable `dot` is a test FAILURE, not a silent skip.
    let success_graphviz = match dot {
        Ok(out) if out.status.success() => {
            let s = String::from_utf8_lossy(&out.stderr);
            println!(
                "GraphViz tool: '{}'\n checking version: {}OK.",
                dot_cmd,
                s.trim()
            );
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

/// HS `testProcess`' failure report (Console.hs:114-121) for the `which`
/// probe: the `reason` line, then the `Detailed results` block echoing the
/// command line (`commandLine`, Console.hs:94-95) and the three captured
/// streams.  `reason` carries its own embedded newlines — HS builds it with
/// `unlines`, and `putStrErrLn` adds one more.  The `stdin:`/`stdout:`/
/// `stderr:` labels are padded to a fixed width, so their trailing spaces
/// survive even when the stream is empty.
fn which_probe_error_report(reason: &str, cmd: &str, out: &str, err: &str) -> String {
    format!(
        "{reason}\nDetailed results from testing 'which'\n command: which {cmd}\n stdin:   \n stdout:  {out}\n stderr:  {err}\n"
    )
}

/// HS `ensureGraphCommand` (Environment.hs:104-115) — the `--with-json`
/// startup probe.  `Checking availablity ...` reproduces the upstream typo
/// and, unlike the maude/dot checks, carries no leading space and no
/// trailing newline (`putStrErr`, Console.hs:109/137).  The verdict is
/// discarded by `Interactive.hs:106`, so this never aborts startup.
fn ensure_graph_command(cmd: &str) {
    eprintln!("Graph rendering command: {}", cmd);
    eprint!("Checking availablity ...");
    let probe = std::process::Command::new("which").arg(cmd).output();
    let out = match probe {
        Ok(out) => out,
        Err(e) => {
            // HS `testProcess`' `IOException` handler (Console.hs:139-149);
            // `maudeTest` is `False` here, so it falls through to the blank
            // line and a `Nothing` verdict.  `putStrErrLn` continues the
            // unterminated `Checking availablity ...` line.
            eprintln!("caught exception while executing:");
            eprintln!("which {}", cmd);
            eprintln!("with input: ");
            eprintln!("Exception: ");
            eprintln!("   {}", e);
            eprintln!();
            return;
        }
    };
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    // HS checks the exit code first (`ignoreExitCode` is `False`), then the
    // `check` predicate `err == ""` (Environment.hs:111-113).  Both failure
    // arms print `errMsg`, whose default message is `unlines ["Command not
    // found"]` (Environment.hs:114-115).
    let reason = if out.status.success() {
        if stderr.is_empty() {
            eprintln!(" OK.");
            return;
        }
        "Command not found\n".to_string()
    } else {
        format!(
            "failed with exit code {}\n\nCommand not found\n",
            out.status.code().unwrap_or(1)
        )
    };
    eprint!(
        "{}",
        which_probe_error_report(&reason, cmd, &stdout, &stderr)
    );
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
        RunError(format!(
            "failed to start maude at {:?}: {:?}",
            maude_path, e
        ))
    })?;
    // HS emits the maude tool/version banner on STDERR (via `ensureMaude`),
    // not stdout — the rule dump alone goes to stdout.  Mirror that.
    if let Some(v) = crate::cli::detect_maude_version_at(&maude_path) {
        print_maude_banner(&maude_path, Some(&v));
    }
    // HS `Main.Mode.Intruder.run` (Intruder.hs:48-53) generates BOTH the DH
    // and the bilinear-pairing variants and emits `dhS ++ bpS`:
    //   - DH: `dhIntruderRules False` (runtime, via Maude).  RS's runtime
    //     generator is byte-faithful (exactly 51 rules); `variants_intruder`
    //     applies `remove_renamings` to drop redundant identity-variants.
    //   - BP: `bpIntruderRules False` (runtime).  Like HS
    //     (Intruder.hs:43-63, see line 50), we start a SECOND Maude handle on
    //     `bp_maude_sig()` and generate the 74 BP rules at runtime via
    //     `bp_intruder_rules(false, ..)`.  This tracks the CURRENT Maude
    //     rather than the stale cached `data/intruder_variants_bp.spthy`
    //     (which production proving still parses via
    //     `mk_bp_intruder_variants`); HS's `variants` command likewise
    //     generates BP at runtime, so the two stay byte-identical.
    let dh_rules = tamarin_theory::intruder_rules::dh_intruder_rules(false, &maude);
    let bp_sig = tamarin_term::maude_sig::bp_maude_sig();
    let bp_maude = MaudeHandle::start(&maude_path, bp_sig).map_err(|e| {
        RunError(format!(
            "failed to start maude at {:?}: {:?}",
            maude_path, e
        ))
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

    if args.in_files.is_empty() {
        // HS `Interactive.run` dispatches on the WORKDIR argument first:
        // without one it is `helpAndExit thisMode (Just "no working directory
        // specified")` (Interactive.hs:76-80) — `error: <msg>` header plus the
        // mode's help on STDOUT, exit 1, before any tool check runs (stderr
        // stays empty; no maude banner).  The HS `--load-json` escape hatch
        // does not apply: this port has no arm for that flag.
        println!(
            "error: no working directory specified\n\n{}",
            crate::cli::help_text(Subcommand::Interactive)
        );
        return Ok(1);
    }

    init_rayon_pool(args);
    // `-c/--open-chains` and `-s/--saturation` apply to interactive-mode
    // theory loads too (HS shares `TheoryLoadOptions` across modes).
    tamarin_theory::constraint::solver::sources::set_cli_solver_limits(
        args.open_chains,
        args.saturation,
    );

    // Oracle exec failures must not kill the server: HS confines the
    // `readProcess` exception to the Warp request thread, so only the
    // triggering request fails.  Batch keeps the `exit(1)` parity path.
    tamarin_theory::constraint::solver::search::ORACLE_ERROR_UNWINDS
        .store(true, std::sync::atomic::Ordering::Relaxed);

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
    // `--with-dot` / `--with-json` — HS stores `readOutputCommand as`
    // (Environment.hs:41-45) as `WebUI.outputCmd` (Interactive.hs:138,
    // Web/Types.hs:152); the graph route then spawns `ocGraphCommand`
    // (Web/Theory.hs:1494-1497 for dot, :1484-1491 for JSON).
    cfg.dot_path = args.dot_path.clone().unwrap_or_else(|| "dot".to_string());
    cfg.json_path = args.json_path.clone();
    // `--no-ndc` — HS captures the CLI's `TheoryLoadOptions` in the
    // `loadTheory thyLoadOptions` closure `withWebUI` runs for every web load
    // (Interactive.hs:135); `addNdcOption` (TheoryLoader.hs:821-826) then writes
    // `ndcCheck` = `not (--no-ndc)` (TheoryLoader.hs:365-366) into each loaded
    // theory's `_deductionChainCheck`.  Set before the eager load below.
    tamarin_server::theory_io::set_ndc_check(!args.no_ndc);

    // Positional args are theory files (Haskell uses a working
    // directory, but we accept either: a single dir arg, or one-or-more
    // .spthy paths).
    let theory_paths: Vec<PathBuf> = collect_theory_paths(&args.in_files)?;

    // HS interactive runs the tool checks BEFORE the banner
    // (Interactive.hs:86-91): `ensureMaudeAndGetVersion` prints the
    // maude block (Console.hs:150-155) and `ensureGraphVizDot` the
    // GraphViz block (Environment.hs:72-87), both on stderr.  Neither is
    // gated on any flag — `--quiet` leaves them in place (see `Args::quiet`).
    print_maude_banner(
        &maude_display_name(args),
        crate::cli::detect_maude_version_at(&maude_invocation_path(args)).as_deref(),
    );
    // HS picks the graph-tool check by `(readOutputCommand as).ocFormat`
    // (Interactive.hs:106-108): `--with-json` selects `ensureGraphCommand`
    // (Environment.hs:104-115) and the `GraphViz tool:` block does not run at
    // all; otherwise `ensureGraphVizDot` (Environment.hs:72-101) runs.  Both
    // results are discarded (`_ <-`), so an unavailable tool never aborts
    // startup.  `--with-json` also overrides `--with-dot` (Environment.hs:41-45).
    let dot_cmd = args.dot_path.as_deref().unwrap_or("dot");
    if let Some(json_cmd) = args.json_path.as_deref() {
        ensure_graph_command(json_cmd);
    } else {
        eprintln!("GraphViz tool: '{}'", dot_cmd);
        // HS lowercases `dot -V`'s stderr banner, strips the trailing
        // newline, and appends ". OK." (Environment.hs:81-87); PNG
        // support = "png" appears in the `dot -T?` error listing.
        if let Ok(out) = std::process::Command::new(dot_cmd).arg("-V").output() {
            let banner = String::from_utf8_lossy(&out.stderr).to_lowercase();
            if banner.contains("graphviz") {
                eprintln!(" checking version: {}. OK.", banner.trim_end_matches('\n'));
                let png_ok = std::process::Command::new(dot_cmd)
                    .arg("-T?")
                    .output()
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
) -> Result<
    (
        tamarin_theory::constraint::solver::context::CutStrategy,
        bool,
    ),
    RunError,
> {
    use tamarin_theory::constraint::solver::context::CutStrategy;
    let (block_cut, block_auto_sources) = match &parsed.configuration {
        Some(cfg) => tamarin_theory::prove::config_block_options(cfg).map_err(RunError)?,
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
    let raw_path = maude_invocation_path(args);
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

/// The maude binary this run invokes: the `--with-maude` path when given,
/// else the probed default.  HS `ensureMaude` reads the same `maudePath`
/// for both the version check and every later maude spawn (Console.hs:
/// 156-161), so the reported version is always the invoked binary's.
fn maude_invocation_path(args: &Args) -> String {
    args.maude_path.clone().unwrap_or_else(default_maude_path)
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

/// Report an `ArgumentError` forced out of `mkTheoryLoadOptions` the way the
/// GHC runtime does: `thyLoadOptions = case mkTheoryLoadOptions as of Left
/// (ArgumentError e) -> error e` (Batch.hs:162-164) raises `error` at
/// Batch.hs:163:33, and the top-level handler prints `tamarin-prover: <msg>`
/// plus the one-frame `HasCallStack` block on stderr — nothing on stdout,
/// exit 1.  The record is forced lazily inside the file loop, so the report
/// lands AFTER the maude banner and BEFORE any `[Theory …]` marker.
fn batch_argument_error(message: &str) -> i32 {
    let g = tamarin_parser::GhcError {
        message: message.to_string(),
        call_site: "src/Main/Mode/Batch.hs:163:33 in main:Main.Mode.Batch".to_string(),
    };
    ghc_exception(&g.display_exception())
}

/// Report an exception that escaped to GHC's runtime the way its top-level
/// handler does: `tamarin-prover: <msg>` on stderr — no batch `error:`
/// prefix, no `[Theory …]` wrapper, nothing on stdout — and exit 1.  Returns
/// that exit code for the caller to propagate.
fn ghc_exception(msg: &str) -> i32 {
    eprintln!("tamarin-prover: {}", msg);
    1
}

/// HS `mkOutPath`'s miss — `-o=` with no `-O` — `die`s with this exact line
/// (Batch.hs:118-123) instead of falling back to stdout: the line on stderr,
/// stdout empty, exit 1.  Returns that exit code for the caller to propagate.
fn missing_output_path() -> i32 {
    eprintln!("Please specify a valid output file/directory");
    1
}

/// HS `writeFileWithDirs` (Utils.hs:20-23): create the target's parent
/// directories, then write `body` VERBATIM.
fn write_file_with_dirs(path: &str, body: &str) -> Result<(), RunError> {
    if let Some(parent) = std::path::Path::new(path).parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .map_err(|e| RunError(format!("failed to create {}: {}", parent.display(), e)))?;
        }
    }
    fs::write(path, body).map_err(|e| RunError(format!("failed to write {}: {}", path, e)))
}

/// HS `traceLabelOptions` (Batch.hs:305-317): the fixed middle segment of an
/// `outputTraces` label.  Batch always feeds it `defaultGraphOptions`
/// (Graph.hs:66-72) and `defaultDotOptions` (Dot.hs:84-87) — Batch.hs:254-255
/// hard-codes both, so no CLI flag (`--no-compress` included) can move it.
/// Every input is a compile-time constant, so the segment is derived once and
/// reused by every label the run emits.
fn trace_label_options() -> &'static str {
    static LABEL: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    LABEL.get_or_init(|| {
        let o = tamarin_server::graph::GraphOptions::default();
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
        // `_doNodeStyle`: RS has no `DotOptions` type — `handlers::dot` renders
        // `CompactBoringNodes` unconditionally, which is `defaultDotOptions`.
        let s6 = "NB";
        format!("{}-{}-{}-{}-{}-{}", s1, s2, s3, s4, s5, s6)
    })
}

/// HS `traceOutputLabel` (Batch.hs:290-303): the digraph id (`--output-dot`)
/// and `jgLabel` (`--output-json`) of one serialised trace.
///
/// There is NO separator between the lemma name and the proof path
/// (Batch.hs:307-308 is `++ lemma._lName ++ intercalate "-" proofPath`).
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

/// HS `outputTraces`' two writers (Batch.hs:262-271), run once per input file
/// inside `processThy`'s close-and-prove branch.  `writeFile`/`BL.writeFile`
/// TRUNCATE, so with several input files the LAST file's traces survive.
///
/// `traces` is the labelled `(label, system)` list in HS's order: lemma
/// declaration order, then `proofSystems`' case-name walk.
fn write_output_traces(args: &Args, traces: Vec<(String, System)>) -> Result<(), RunError> {
    use tamarin_server::graph::{GraphOptions, RenderSystem};
    let opts = GraphOptions::default();
    if let Some(p) = &args.trace_dot {
        // `intercalate "\n" $ map serializeDot labelledSystems`.  Each graph
        // already ends `}\n`, so the separator yields one blank line between
        // graphs; an empty list is `intercalate "\n" [] == ""`, a 0-byte file.
        let graphs: Vec<String> = traces
            .iter()
            .map(|(label, sys)| {
                tamarin_server::handlers::dot::system_to_dot_labeled(sys, &opts, label)
            })
            .collect();
        fs::write(p, graphs.join("\n"))
            .map_err(|e| RunError(format!("failed to write {}: {}", p, e)))?;
    }
    if let Some(p) = &args.trace_json {
        // `sequentsToJSONPretty graphOptions labelledSystems` — one document
        // for all graphs; an empty list is `{"graphs": []}`.  Batch does NOT
        // pre-abbreviate the systems (that is the web proof route only), so
        // the systems cross the clone-for-render boundary as they are.
        let (labels, systems): (Vec<String>, Vec<System>) = traces.into_iter().unzip();
        let rendered: Vec<RenderSystem> =
            systems.into_iter().map(RenderSystem::from_prover).collect();
        let pairs: Vec<(String, &RenderSystem)> = labels.into_iter().zip(rendered.iter()).collect();
        let body = tamarin_server::graph::json::sequents_to_json_pretty(&opts, &pairs);
        fs::write(p, body).map_err(|e| RunError(format!("failed to write {}: {}", p, e)))?;
    }
    Ok(())
}

/// The `-m`/`--output-module` values translate mode actually renders: HS's
/// `ModuleType` minus the three export backends, which are rejected before the
/// file loop.  Narrowing here is what lets the per-file render match
/// exhaustively over the modules that can reach it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TranslateModule {
    Spthy,
    SpthyTyped,
    Msr,
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
    // byte-identical output to a fully sequential run.
    init_rayon_pool(args);
    // `-c/--open-chains` and `-s/--saturation` (HS `TheoryLoadOptions`
    // openChainsLimit/saturationLimit, threaded into every close).
    tamarin_theory::constraint::solver::sources::set_cli_solver_limits(
        args.open_chains,
        args.saturation,
    );
    if args.diff {
        return Err(RunError(
            "--diff (observational equivalence) is not yet ported to the Rust prover.".to_string(),
        ));
    }
    // `--stop-on-trace` selects HS's `SolutionExtractor` (Theory/Proof.hs:693-694, see line 695,
    // TheoryLoader.hs:355-362) and, when the CLI flag is absent, HS
    // additionally consults the theory's in-file `configuration:` block
    // (`configStopOnTrace`, TheoryLoader.hs:640-666) — a PER-THEORY value,
    // so the effective strategy is resolved inside the file loop by
    // `effective_config` once the theory is parsed.

    // `--output-json` / `--output-dot`: HS `outputTraces` (Batch.hs:249-317)
    // serialises the constraint system of every `Finished Solved` proof node.
    // The solver drops each node's `System` after expansion unless told
    // otherwise, so the retention switch has to be flipped for the whole
    // process BEFORE the first lemma is proved.  It is scoped to solved nodes
    // (`set_keep_solved_sys`, not `set_keep_sys`), so a run without these
    // flags pays nothing and a run with them retains only the systems
    // `outputTraces` actually reads.
    let want_traces = args.trace_dot.is_some() || args.trace_json.is_some();
    if want_traces {
        tamarin_theory::constraint::solver::search::set_keep_solved_sys(true);
    }
    if args.in_files.is_empty() {
        // HS `batchMode`'s run: `null inFiles = helpAndExit thisMode (Just "no
        // input files given")` (Batch.hs:90).  `helpAndExit`
        // (Console.hs:341-359) `putStrLn`s the `error: <msg>` header and the
        // mode's help — STDOUT, not stderr — and then `exitFailure`.  Not an
        // error value: HS never routes this through its error channel, and
        // returning one here would send the block to stderr.
        println!(
            "error: no input files given\n\n{}",
            crate::cli::help_text(Subcommand::Batch)
        );
        return Ok(1);
    }
    let mut overall_status = 0i32;
    let mut file_results: Vec<FileResult> = Vec::new();
    // `--parse-only` docs, buffered and printed AFTER the file loop: HS
    // (Batch.hs:91-95) runs `mapM (processThy "") inFiles` to completion
    // BEFORE the `mapM_ (putStrLn . renderDoc) docs` — so a parse error in a
    // later file aborts the run (`die`) with NOTHING printed for the earlier
    // files, and the stderr `[Theory X] Theory loaded` markers all precede
    // the stdout docs.
    let mut parse_only_docs: Vec<String> = Vec::new();
    // `--precompute-only` per-file state (HS Batch.hs:96-100): like
    // `--parse-only`, HS prints every file's doc to stdout AFTER the file
    // loop (`mapM_ (putStrLn . renderDoc)`), ignoring `-o`/`-O` and
    // skipping the summary block.  The doc's stats force the saturation
    // lazily at that renderDoc, so each file's `[Saturating Sources]`
    // stderr trace fires in the PRINT phase (after every file's markers),
    // not during its loop iteration — stash the session + parsed theory +
    // wf-failure count here and defer the stats computation to match.
    let mut precompute_pending: Vec<(
        tamarin_theory::prove::ProverSession,
        tamarin_parser::ast::Theory,
        usize,
    )> = Vec::new();

    let parser_flags: Vec<&str> = args.defines.iter().map(String::as_str).collect();

    // The Maude version is constant for the whole run, but detecting it
    // spawns a `maude --version` subprocess.  Detect it ONCE here — from the
    // binary this run will actually invoke — and reuse the cached value for
    // both the banner and every file's `BuildInfo`, avoiding one
    // `maude --version` subprocess per file.
    let maude_version: Option<String> =
        crate::cli::detect_maude_version_at(&maude_invocation_path(args));

    // HS prints the maude tool + version banner ONCE at the top of the
    // batch run (`Main.Console.argExists` path).  Mirror that here:
    // emit `maude tool: 'maude'\n checking version: X. OK.\n checking
    // installation: OK.` before the first theory is loaded.  `--parse-only`
    // never starts Maude (Batch.hs:91-95), so the banner is skipped there;
    // `--quiet` does NOT suppress it (see `Args::quiet`).
    if !args.parse_only {
        print_maude_banner(&maude_display_name(args), maude_version.as_deref());
    }

    // The deferred `mkTheoryLoadOptions` argument checks (see
    // `batch_argument_error`).  `--partial-evaluation`'s unknown-option
    // rejection (TheoryLoader.hs:354-358) precedes `--output-module`'s
    // (TheoryLoader.hs:373-377) in the record, so it fires first when both
    // values are bad.
    let partial_evaluation: Option<crate::cli::PartialEval> = match &args.partial_evaluation {
        Some(Err(())) => return Ok(batch_argument_error("partial-evaluation: unknown option")),
        Some(Ok(pe)) => Some(pe.clone()),
        None => None,
    };
    // `--output-module`: exact match against the six `show` strings
    // (TheoryLoader.hs:373-377) — anything else, the empty string included,
    // is `ArgumentError "output mode not supported."`.
    let output_module: Option<ModuleType> = match &args.output_module {
        None => None,
        Some(s) => match ModuleType::from_show(s) {
            Some(m) => Some(m),
            None => return Ok(batch_argument_error("output mode not supported.")),
        },
    };
    // Batch.hs:91-113 guard order: parseOnly > precomputeOnly > outModule >
    // normal — `--parse-only -m msr` behaves as plain `--parse-only`, and
    // `--prove -m spthy` does not prove.
    let requested_module: Option<ModuleType> = if args.parse_only || args.precompute_only {
        None
    } else {
        output_module
    };
    let translate_module: Option<TranslateModule> = match requested_module {
        None => None,
        Some(ModuleType::Spthy) => Some(TranslateModule::Spthy),
        Some(ModuleType::SpthyTyped) => Some(TranslateModule::SpthyTyped),
        Some(ModuleType::Msr) => Some(TranslateModule::Msr),
        Some(
            m @ (ModuleType::ProVerifEquivalence | ModuleType::ProVerif | ModuleType::DeepSec),
        ) => {
            return Err(RunError(format!(
                "--output-module={}: the ProVerif / DeepSec export backends are not yet ported to \
                 the Rust prover.",
                m.as_str()
            )));
        }
    };
    let translate_mode = translate_module.is_some();
    // Translate-only docs, buffered and emitted AFTER the file loop
    // (Batch.hs:101-113: `mapM processThy` to completion, then either the
    // `-o`/`-O` writes or `mapM_ (putStrLn . renderDoc)`).
    let mut translate_docs: Vec<String> = Vec::new();

    // The `Generated from:` block's metadata (HS `withVersionAndReport`,
    // TheoryLoader.hs:636-660).  Every field is build- or argv-constant, so
    // one value serves every file's render.
    let build_info = tamarin_theory::pretty_theory::BuildInfo {
        tamarin_version: crate::cli::VERSION.to_string(),
        maude_version: maude_version
            .clone()
            .unwrap_or_else(|| "unknown".to_string()),
        git_revision: crate::cli::GIT_REV.to_string(),
        git_branch: crate::cli::GIT_BRANCH.to_string(),
        compiled_at: crate::cli::BUILD_TIMESTAMP.to_string(),
    };

    for in_file in &args.in_files {
        let t0 = Instant::now();
        let src = match fs::read_to_string(in_file) {
            Ok(s) => s,
            Err(e) => {
                // HS never guards the read: `openFile` throws an IOException
                // that escapes to GHC's runtime, which writes
                // `tamarin-prover: <path>: openFile: <reason>` (the
                // IOException `Show` instance, GHC.IO.Exception) to stderr
                // and exits 1.  Reproduce the three reasons an input path
                // can hit; anything rarer keeps the port's own message.
                // EISDIR is matched by errno: Rust only surfaces read(2)'s
                // failure on a directory, and `ErrorKind::IsADirectory`
                // needs Rust 1.83 (workspace MSRV is 1.78).
                let reason = match e.kind() {
                    std::io::ErrorKind::NotFound => "does not exist (No such file or directory)",
                    std::io::ErrorKind::PermissionDenied => "permission denied (Permission denied)",
                    _ if e.raw_os_error() == Some(21) => "inappropriate type (is a directory)",
                    _ => return Err(RunError(format!("failed to read {}: {}", in_file, e))),
                };
                eprintln!("tamarin-prover: {in_file}: openFile: {reason}");
                return Ok(1);
            }
        };
        // Thread the including file's directory so `#include "file"` resolves
        // relative to it (HS `takeDirectory inFile0`, Parser.hs:323-343).
        let base_dir = std::path::Path::new(in_file)
            .parent()
            .map(|p| p.to_path_buf());
        let mut parsed = match tamarin_parser::parse_theory_with_base(&src, &parser_flags, base_dir)
        {
            Ok(thy) => thy,
            Err(e) => {
                if let Some(g) = &e.ghc_error {
                    // A GHC `error` raised inside the HS parser (e.g. `macro`'s
                    // two rejections, Theory/Text/Parser/Macro.hs:34-38) never
                    // reaches `handleError`: the exception escapes to GHC's
                    // runtime, which writes `tamarin-prover: ` ++
                    // `displayException` — message plus `HasCallStack` frame —
                    // to stderr and exits 1.  No parsec frame, no `SourcePos`
                    // header; the maude banner above has already printed.
                    return Ok(ghc_exception(&g.display_exception()));
                }
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
        // Capture the `_restrict` formulas' free variables per rule BEFORE
        // the lift clears them: HS keeps the formulas on the rule
        // (`preRestriction`) and partial evaluation's rename/dedup depends
        // on their frees (see `restriction_frees_by_rule`) — its only
        // consumer, so the walk runs only under `--partial-evaluation`.  The
        // position is fixed: the frees are gone once the lift below runs.
        let restriction_frees = if partial_evaluation.is_some() {
            tamarin_theory::rule_restriction::restriction_frees_by_rule(&parsed)
        } else {
            Default::default()
        };
        tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parsed).map_err(|e| {
            RunError(format!(
                "_restrict expansion failed in {}: {}",
                in_file, e.message
            ))
        })?;
        // HS emits this trace marker as soon as the theory parses
        // (TheoryLoader.hs:451).
        let theory_name = parsed.name.clone();
        // HS `[Theory X] …` progress markers are `traceM`s (TheoryLoader.hs:451,
        // 496, 581, 594, 696) and land on stderr.  They are NOT gated by
        // `--quiet` (see `Args::quiet`).  `loadTheory`'s `Theory loaded`
        // marker fires in EVERY mode, `--parse-only` included
        // (TheoryLoader.hs:449-452 — Batch.hs's parseOnly branch still calls
        // `loadTheory` via `processThy`); the later translate/close markers
        // are unreachable under `--parse-only` (the branch below `continue`s
        // first).
        let marker = |msg: &str| {
            eprintln!("[Theory {}] {}", theory_name, msg);
        };
        marker("Theory loaded");

        if args.parse_only {
            // HS-faithful `--parse-only` (Batch.hs:91-95 + TheoryLoader.hs:
            // 443-460): parse, emit the marker above, pretty-print the OPEN
            // theory (`prettyOpenTheory`) — no wellformedness, no
            // configuration-block processing (that happens in `closeTheory`,
            // TheoryLoader.hs:640-666), no Maude, no output files (`-o`/`-O`
            // are ignored: the parseOnly branch never consults `writeOutput`),
            // no `summary of summaries`.
            //
            // The elaborated theory here only supplies the parse-time
            // signature + hoisted heuristic/tactic headers + the arity-1
            // fold set — elaboration is RS's signature-construction step
            // (HS builds the same `SignaturePure` during parsing).
            let elaborated = elaborate(&parsed).map_err(|e| {
                RunError(format!("elaboration error in {}: {}", in_file, e.message))
            })?;
            // Formula→guarded conversion inside the lemma/restriction
            // renderers resolves user function symbols through this
            // thread-local (same guard the closed path installs).
            let _user_funs_guard = tamarin_theory::elaborate::set_user_funs_for_theory(&parsed);
            // Parsed `process:` / `let` bodies are converted to SAPIC
            // `PlainProcess` for the Doc-based `prettySapic'` port; the
            // conversion lives in `tamarin-sapic` (dependency direction).
            // `convert_process_with_defs` mirrors HS's PARSER, which inlines
            // each `P(args)` call and wraps it in a `ProcessCall` marker
            // action (Theory/Text/Parser/Sapic.hs:293-312) — `prettySapic'`
            // then prints just `P(args)` for the marker (Process.hs:496).
            let process_defs = tamarin_sapic::inline::collect_process_defs(&parsed);
            let conv = |proc: &tamarin_parser::ast::Process| {
                tamarin_sapic::inline::convert_process_with_defs(proc, &process_defs)
                    .map_err(|e| e.message)
            };
            let body = tamarin_theory::pretty_theory::pretty_open_theory(
                &parsed,
                &elaborated,
                in_file,
                &conv,
            )
            .map_err(|e| {
                RunError(format!(
                    "open-theory rendering of {} failed: {}",
                    in_file, e
                ))
            })?;
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

        // Effective cut strategy + auto-sources for THIS theory: CLI flags
        // merged with the in-file `configuration:` block per HS
        // `closeTheory` (TheoryLoader.hs:640-666).
        let (cut, auto_sources) = effective_config(args, &parsed)?;

        // Wellformedness checks — mirrors HS `checkWellformedness`
        // (`Theory.Tools.Wellformedness:1270`).  Runs on every file that
        // reaches the close pipeline, so a malformed theory is surfaced
        // even without proving.
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
        // (`--parse-only` never reaches this point — it `continue`d above,
        // before any wellformedness runs, matching HS Batch.hs:91-95.)
        wf_report.retain(|e| e.topic != "Message Derivation Checks");
        // HS `checkIfLemmasInTheory` (Wellformedness.hs:1156-1171) — FIRST
        // in HS's checkWellformedness list (line 1272).  Checks that every
        // --prove=X / --lemma=X name corresponds to a theory lemma.  This
        // check needs the CLI args (not embedded in the parser AST), so we
        // call it separately and PREPEND the result so it sorts first —
        // matching HS's `checkIfLemmasInTheory : ...` order.
        {
            let lemma_check =
                tamarin_parser::wf::check_if_lemmas_in_theory(&args.lemma_names, &parsed);
            if !lemma_check.is_empty() {
                let mut new_report = lemma_check;
                new_report.extend(wf_report);
                wf_report = new_report;
            }
        }

        // Elaborate (mainly to get the protocol-specific MaudeSig).  This is
        // where the port first builds LNTerms, so an HS-`error`-class defect
        // (`Term.fAppAC: empty argument list`) panics HERE — but GHC, lazy,
        // surfaces the same error only after `Theory translated` plus (unless
        // `--no-ndc`) the NDC marker pair.  Park those pending lines for the
        // panic hook to replay first, keeping the death sequence byte-equal.
        DEFERRED_HS_ERROR_MARKERS.set(Some({
            let mut lines = format!("[Theory {theory_name}] Theory translated\n");
            if !args.no_ndc {
                for suffix in ["started", "ended"] {
                    lines.push_str(&format!(
                        "[Theory {theory_name}] No Deconstruction Chain checks {suffix}\n"
                    ));
                }
            }
            lines
        }));
        let mut elaborated = elaborate(&parsed)
            .map_err(|e| RunError(format!("elaboration error in {}: {}", in_file, e.message)))?;
        DEFERRED_HS_ERROR_MARKERS.take();
        // HS `addParamsOptions`' `addNdcOption` (TheoryLoader.hs:821-826):
        // `--no-ndc` disables the no-deconstruction-chain check for this theory.
        //
        // HS applies it inside `loadTheory` (TheoryLoader.hs:449-452), which both
        // modes call; the interactive path reaches it through
        // `tamarin_server::theory_io::set_ndc_check` (wired in
        // `run_interactive`), which writes the same field on every web load.
        if args.no_ndc {
            elaborated.options.deduction_chain_check = false;
        }
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
        wf_report.extend(tamarin_theory::pretty_theory::subterm_convergence_report_wf(&maude_sig));

        // HS emits this marker after `translateTheory` finishes
        // (TheoryLoader.hs:448-460, see line 454).
        marker("Theory translated");

        // SAPIC `process:` translation (HS `typeTheory` → `translate`,
        // TheoryLoader.hs:428-443, see line 430).  Runs ONLY for `is_sapic` theories (exactly one
        // top-level `process:`); a no-op otherwise, so non-process theories are
        // byte-unchanged.  Injects the generated rules + `single_session`
        // restriction + `heuristic: p` into BOTH `parsed` (for rendering) and
        // `elaborated` (for solving / AC-variant pre-computation), so it MUST
        // run before `populate_rule_variants` below.  `user_set_heuristic` is
        // true iff a `heuristic:` item already populated `elaborated.heuristic`
        // (HS `addHeuristic` returns `Nothing` in that case).
        // Install the user/builtin function-symbol flag sets (the
        // `CollectedUserFuns` bundle) for the duration of SAPIC translation
        // AND the variant pre-computation below.  That thread-local drives
        // `term_to_lnterm`'s symbol resolution (privacy / constructability);
        // `elaborate()` sets it only for its own scope, so without
        // re-installing it here the SAPIC-injected rules' builtin symbols
        // (`rep` private, `check_rep` / `get_rep` destructors from
        // `locations-report`) re-elaborate with the default
        // public-constructor flags, serialising as `tamXC..` — which Maude
        // rejects, leaving the rule with "no variants".
        let _sapic_funs_guard = tamarin_theory::elaborate::set_user_funs_for_theory(&parsed);
        // The translate-mode render's print options, one per module
        // (`prettyOpenTheoryByModule`, TheoryLoader.hs:783-801).  `Some` iff
        // `-m` is in force: `spthy` and `msr` are fixed, while `spthytyped`
        // carries `Sapic.typeTheory`'s per-file result and is therefore filled
        // by the SAPIC block below, at the position where HS runs the typing.
        // `None` in every other mode.
        let mut print_opts: Option<tamarin_theory::pretty_theory::OpenPrintOpts> =
            match translate_module {
                // `spthy`: the plain open print (`prettyOpenTheory`).
                Some(TranslateModule::Spthy) => {
                    Some(tamarin_theory::pretty_theory::OpenPrintOpts::default())
                }
                // `msr`: drop the TranslationElement set
                // (`prettyOpenTranslatedTheory . removeTranslationItems`).
                Some(TranslateModule::Msr) => Some(tamarin_theory::pretty_theory::OpenPrintOpts {
                    drop_translation_items: true,
                    ..Default::default()
                }),
                Some(TranslateModule::SpthyTyped) | None => None,
            };
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
            // Which translation steps run depends on the output module
            // (`processOpenTheory`, TheoryLoader.hs:470-484): `spthy` is
            // `pure`, `spthytyped` is `Sapic.typeTheory` alone, and `msr` /
            // normal mode run the full `typeTheory >=> translate >=>
            // Acc.translate` pipeline.
            let skip_translation = matches!(
                translate_module,
                Some(TranslateModule::Spthy) | Some(TranslateModule::SpthyTyped)
            );
            let sapic_wf = if skip_translation {
                // `translateTheory`'s preReport (`Sapic.checkWellformedness t`,
                // Warnings.hs:37-38) still runs on the pre-translation process
                // — the same inlined `PlainProcess` `apply_sapic` checks.
                let mut wf: Vec<tamarin_parser::wf::WfError> = Vec::new();
                if elaborated.is_sapic {
                    match tamarin_sapic::apply::sapic_pre_report(&parsed) {
                        Ok(Some((report, _))) => wf = report,
                        // `is_sapic` set with no `TopLevelProcess`.
                        Ok(None) => {}
                        // Same GHC-exception shape as the apply_sapic arm below.
                        Err(e) => return Ok(ghc_exception(&e.message)),
                    }
                }
                if translate_module == Some(TranslateModule::SpthyTyped) {
                    // `Sapic.typeTheory` (`typeTheoryEnv`, Typing.hs:204-226)
                    // over the SAME parsed theory the renderer sees — the
                    // parser AST stays untouched, the typed processes/defs
                    // ride the overlay, and the recomputed `function:` items
                    // are appended in descending key order.
                    match tamarin_sapic::type_theory::type_theory_env(&parsed, &elaborated) {
                        Ok(r) => {
                            print_opts = Some(tamarin_theory::pretty_theory::OpenPrintOpts {
                                typed: Some(r.overlay),
                                extra_function_items: r.fun_items,
                                drop_translation_items: false,
                            })
                        }
                        // HS: `ProcessNotWellformed` / typing exceptions
                        // escape to GHC's runtime — `tamarin-prover: …`,
                        // exit 1.
                        Err(e) => return Ok(ghc_exception(&e.message)),
                    }
                }
                wf
            } else {
                match tamarin_sapic::apply::apply_sapic(
                    &mut parsed,
                    &mut elaborated,
                    user_set_heuristic,
                ) {
                    Ok(w) => w,
                    // HS: exceptions SAPIC `translate` raises — e.g. the
                    // `addProtoRule` name clash on inserting a generated rule
                    // (`duplicate rule: <name>`, OpenTheory.hs:727-733) —
                    // escape to GHC's runtime, which writes
                    // `tamarin-prover: <show exception>` to stderr and exits
                    // 1, exactly like the accountability arm below.
                    Err(e) => return Ok(ghc_exception(&e.message)),
                }
            };

            // Accountability translation (HS `Acc.translate`, TheoryLoader.hs:428-443, see line 430):
            // `Sapic.translate >=> Acc.translate`.  Expands each
            // `... accounts for` lemma into its verification-condition lemmas +
            // case-test predicates, injecting into BOTH `parsed` (rendering) and
            // `elaborated` (prove loop).  A no-op for theories with neither
            // accountability lemmas nor case tests (a `test` without any acc
            // lemma still gets its predicate appended, as in HS).  Runs inside
            // `_sapic_funs_guard` so the generated lemmas' embedded case-test
            // formulas resolve their user function symbols with the theory's
            // private/destructor flags.  Not part of `processOpenTheory`'s
            // `spthy` / `spthytyped` arms, so those translate modes skip it.
            if !skip_translation {
                if let Err(e) = tamarin_accountability::translate(&mut parsed, &mut elaborated) {
                    // HS: the exceptions `Acc.translate` throws — `CaseTestsUndefined`
                    // (Accountability.hs:42-49, see line 45) and the `UndefinedPredicate` /
                    // `DuplicateItem` parsing exceptions its `liftedAddLemma` /
                    // `liftedAddPredicate` folds raise (Parser.hs:141-152,
                    // Parser/Signature.hs:313-316) — escape to GHC's runtime, which
                    // writes `tamarin-prover: <show exception>` to stderr and exits
                    // 1 — no batch `error:` / `[Theory …]` wrapper (the maude banner
                    // + the `Theory loaded`/`Theory translated` markers already
                    // printed).
                    return Ok(ghc_exception(&e.to_string()));
                }
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

        // `-m msr` keeps only the selected lemmas (`processOpenTheory`'s
        // `filterLemma (lemmaSelector thyOpts)` tail, TheoryLoader.hs:475-480
        // + TheoryObject.hs:566-579): `LemmaItem`s not matching the
        // `--prove`/`--lemma` selector are dropped, everything else stays.
        // `lemma_matches` already implements `lemmaSelector`'s `[]` / `[""]`
        // / `["",""]` ⇒ keep-all rules, so this retain is a no-op without a
        // real selector.  Runs BEFORE `post_thy` is cloned so the
        // wellformedness re-runs see the filtered theory, as
        // `checkTranslatedTheory` does.  The `[output=[msr]]` lemma
        // attribute (`lemmaSelectorByModule`) is deliberately NOT honoured
        // here — HS consults it only in `closeTranslatedTheory`
        // (TheoryLoader.hs:706-707), which translate mode never reaches.
        if translate_module == Some(TranslateModule::Msr) {
            parsed.items.retain(|i| match i {
                tamarin_parser::ast::TheoryItem::Lemma(l) => {
                    lemma_matches(&args.lemma_names, &l.name)
                }
                _ => true,
            });
        }

        // HS runs the full `checkWellformedness` on the TRANSLATED theory
        // (TheoryLoader.hs:553-565, `checkTranslatedTheory`), i.e. AFTER SAPIC
        // `translate` has injected the generated rules, whereas our
        // `check_theory` runs earlier on the PRE-translation theory (above,
        // before `apply_sapic`), where the SAPIC rules are invisible to the
        // rule-dependent checks.  The six re-runs and their splice positions
        // are shared with the web load path — see
        // `tamarin_theory::translated_wf`.  The seventh, Maude-dependent
        // "Rule variants" block is batch-only and stays below.
        tamarin_theory::translated_wf::splice_translated_wf_reports(
            &parsed,
            &elaborated,
            &maude_sig,
            &mut wf_report,
        );

        // Spawn a single Maude handle for this file.  Used by:
        //   - the rule-variants computation that populates each rule's
        //     `variant_substs` + `abstracted_rule` (so the pretty-printer
        //     can emit HS's `variants (modulo AC) ...` block);
        //   - the dynamic Message Derivation Check;
        //   - the per-lemma prove loop.
        let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
        // One memo-cache set for this theory session, shared by
        // `file_maude` and every `file_maude_pool` member: an identical
        // query issued from any of these subprocesses reuses the memoized
        // result.  See `SharedMaudeCaches` (maude_proc.rs) for the
        // byte-parity argument and lock-order invariant.
        // (`--parse-only` never reaches here — it `continue`d before any
        // Maude is needed, Batch.hs:91-95.)
        let session_maude_caches = std::sync::Arc::new(SharedMaudeCaches::default());
        let file_maude: Option<MaudeHandle> = MaudeHandle::start_with_caches(
            &maude_path,
            maude_sig.clone(),
            std::sync::Arc::clone(&session_maude_caches),
        )
        .ok();

        // Spawn an auxiliary MaudePool of `effective_maude_processes()`
        // EXTRA subprocesses for use at the rayon parallel sites
        // (rule-variant closure, saturate refinement).  Workers
        // `acquire()` one for the duration of one parallel task so they
        // don't serialise on `file_maude`'s IPC mutex.
        //
        // - `--processors=1` ⇒ `effective_maude_processes=1`; we skip
        //   the auxiliary pool entirely (sequential path uses
        //   `file_maude` only — byte-identical to a single shared Maude).
        // - `M >= 2` ⇒ spawn M independent Maudes.  Each costs
        //   ~30-100 MB; `--maude-processes=N` lets the user override.
        //
        // The pool is kept SEPARATE from `file_maude`: sequential paths
        // (main `prove_lemma` loop, derivation checks) keep using
        // `file_maude` (counter state stays coherent across lemmas); the
        // pool is consumed only inside `par_iter` map closures.  Both
        // consult `session_maude_caches`, so a memo result computed on
        // any of the session's subprocesses is visible to all of them.
        let pool_size = args.effective_maude_processes();
        let file_maude_pool: Option<std::sync::Arc<MaudePool>> = if pool_size >= 2 {
            match MaudePool::new(
                &maude_path,
                maude_sig.clone(),
                pool_size,
                std::sync::Arc::clone(&session_maude_caches),
            ) {
                Ok(p) => Some(std::sync::Arc::new(p)),
                Err(e) => {
                    // RS-only diagnostic (HS has no Maude pool), so
                    // `--quiet` may drop it — see `Args::quiet`.
                    if !args.quiet {
                        eprintln!(
                            "[warn] failed to spawn MaudePool({}): {} \
                                — falling back to single shared Maude",
                            pool_size, e
                        );
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
                &mut elaborated,
                m,
                file_maude_pool.as_deref(),
            );
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
        // Detection criterion: `populate_rule_variants` only calls
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
        // files affected).
        if let Some(ref wf_maude) = file_maude {
            use tamarin_parser::wf::underline_topic;
            use tamarin_parser::wf::WfError as WfE;
            use tamarin_theory::theory::TheoryItem;

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
            let sig_has_reducible = !wf_maude.maude_sig().reducible_fun_syms.is_empty();

            for item in &elaborated.items {
                let TheoryItem::Rule(opr) = item else {
                    continue;
                };

                // Sub-check 1: "Rule has no variants" — mirrors HS
                // `variantsCheck` (Wellformedness.hs:354-372, see line 362):
                //   `guard (null recomputedVariants) $> ...`
                // Calls `rule_has_no_variants_for_wf` which implements
                // the full HS `variantsProtoRule` detection logic including
                // `isFreshRedundant` filtering.
                //
                // Sub-check 2: "Variants mismatch" — not yet ported; no
                // corpus files affected.
                let precomputed_no_variants = if sig_has_reducible {
                    Some(opr.abstracted_rule.is_none() && opr.variant_substs.is_empty())
                } else {
                    None
                };
                if tamarin_theory::tools::rule_variants::rule_has_no_variants_for_wf_with(
                    wf_maude,
                    &opr.rule,
                    precomputed_no_variants,
                ) {
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
            // (position 7) and AFTER unboundReport (position 2), so the
            // anchors are every `WF_TOPIC_ORDER` topic but "Unbound
            // variables".
            insert_wf_before(&mut wf_report, variants_errors, &after_variants_topics());

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
        // structure HS persists.  Translate mode never closes the theory
        // (`translateAndCheckTheory` skips `closeTranslatedTheory`,
        // TheoryLoader.hs:768-781) and the open renderer prints no
        // loop-breaker comments, so the pass is skipped there.
        if let Some(m) = file_maude.as_ref().filter(|_| !translate_mode) {
            annotate_theory_loop_breakers(&mut elaborated, m);
        }

        // Once-per-theory NDC pass (HS `checkCloseIntrRule` inside
        // `checkTranslatedTheory`, TheoryLoader.hs — BEFORE the
        // derivation checks): assemble the intruder cache, run the
        // no-deconstruction-chain check (unless `--no-ndc`), and join
        // the verdicts into the printed signature (`joinNDCinSigWMaude`)
        // so every later rendering — including the no-prove and
        // `--precompute-only` paths — shows `[NDC]` on tagged symbols.
        // The checked cache is a shared handle injected into every
        // `ProofContext` built for this theory below (derivation-check
        // probes, auto-sources scratch contexts, the prover session, the
        // per-lemma fallback), which all reuse this one allocation —
        // mirroring HS's `closeRuleCache` consuming `_thyCache` verbatim.
        // The `No Deconstruction Chain checks started/ended` markers ride the
        // same rule as the sibling `[Theory X]` markers routed through
        // `marker`: printed whenever the stage runs, `--quiet` notwithstanding.
        // `file_maude` is `Some` only when the Maude spawn succeeded, and
        // `--parse-only` `continue`d long before this stage — so the stage
        // and its markers are confined to the close pipeline.
        let ndc_cache: Option<tamarin_theory::constraint::solver::context::IntrRuleCache> =
            file_maude.as_ref().map(|m| {
                let checked = tamarin_theory::close_rule::check_close_intr_rule(
                    m,
                    Some(theory_name.as_str()),
                    elaborated.options.deduction_chain_check,
                );
                // Translate mode discards the NDC-joined signature: HS binds
                // `(postReport, _, _)` from `checkTranslatedTheory` and
                // renders `transThy`, whose signature never received
                // `checkCloseIntrRule`'s `sig'` (TheoryLoader.hs:775-778) —
                // the check RUNS (markers above) but no `[NDC]` attribute may
                // reach the printed `functions:` / `function:` lines.
                if !translate_mode {
                    for f in &checked.ndc_funs {
                        let sig = std::mem::take(&mut elaborated.signature.maude_sig);
                        elaborated.signature.maude_sig = sig
                            .join_ndc_in_sig(*f, tamarin_term::function_symbols::NdcState::IsNdc);
                    }
                }
                checked.cache.into()
            });

        // Dynamic Message Derivation Checks (mirrors HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout`,
        // default 5s).  Needs Maude, so we run it AFTER elaboration
        // and BEFORE the main prove loop.  HS default is 5s; 0 disables.
        // Each per-variable proof attempt is capped at this timeout.
        let deriv_timeout = args.derivcheck_timeout.unwrap_or(5) as u32;
        if deriv_timeout > 0 {
            // HS emits these markers around the per-variable derivability
            // check (TheoryLoader.hs:578-594, see line 581, :594).
            marker("Derivation checks started");
            if let Some(m) = file_maude.as_ref() {
                let extra = tamarin_theory::deriv_check::check_message_derivation(
                    &parsed,
                    m,
                    deriv_timeout,
                    ndc_cache.clone(),
                );
                wf_report.extend(extra);
            }
            marker("Derivation checks ended");
        }

        // `--quit-on-warning` (HS `withVersionAndReport`, TheoryLoader.hs:
        // 643-660, see line 656): a non-empty report throws `WarningError`
        // once the full `preReport ++ postReport` exists — i.e. right here,
        // after the derivation checks.  In the close modes that is after
        // `closeTranslatedTheory` already printed `Theory closed`
        // (TheoryLoader.hs:694 — the closed/proved theory is still an
        // unforced thunk, so neither proving nor auto-sources runs); in
        // translate mode no `Theory closed` is ever printed.  `handleError`
        // (Batch.hs:236-242) then prints the report block on STDOUT and
        // `die`s on stderr — exit 1, NO theory output, NO summary.
        if args.quit_on_warning && !wf_report.is_empty() {
            if !translate_mode {
                marker("Theory closed");
            }
            let mut rep = tamarin_theory::pretty_theory::render_wf_error_report(&wf_report);
            while rep.ends_with('\n') {
                rep.pop();
            }
            // `putStrLn . renderDoc $ vcat` of: blank, the WARNING header,
            // blank (report non-empty here), the report, blank.
            println!("\nWARNING: the following wellformedness checks failed!\n\n{rep}\n");
            eprintln!("quit-on-warning mode selected - aborting on wellformedness errors.");
            return Ok(1);
        }

        // `--partial-evaluation` (HS `closeTranslatedTheory`,
        // TheoryLoader.hs:675-698): `applyPartialEvaluation` (Prover.hs:237-264)
        // runs on the CLOSED theory, between the close and `proveTheory` — it
        // replaces the proto-rules with the abstract interpretation's refined
        // set, splices the abstract-state report in front of them, and
        // re-closes.  Every mode that closes reaches it: a plain load,
        // `--prove` and `--precompute-only` alike.  `--parse-only` never gets
        // here (it `continue`d above, Batch.hs:198-199) and translate mode is
        // excluded — `translateAndCheckTheory` has no `closeTranslatedTheory`
        // call (TheoryLoader.hs:768-781).
        //
        // The returned string is HS's `Debug.Trace` output.  Those traces are
        // lazy thunks forced while the theory is rendered, so on the oracle
        // they appear on stderr AFTER the `[Theory X] Theory closed` marker —
        // hold them here and print them at the marker sites below.
        let mut pe_trace = String::new();
        if let (Some(pe), Some(m)) = (
            partial_evaluation.as_ref().filter(|_| !translate_mode),
            file_maude.as_ref(),
        ) {
            // TheoryLoader.hs:354-358: `SUMMARY` → `Summary`, `VERBOSE` →
            // `Tracing`.  `Silent` is unreachable from the CLI.
            let style = match pe {
                crate::cli::PartialEval::Summary => tamarin_theory::tools::EvaluationStyle::Summary,
                crate::cli::PartialEval::Verbose => tamarin_theory::tools::EvaluationStyle::Tracing,
            };
            pe_trace = tamarin_theory::tools::apply_partial_evaluation(
                &mut parsed,
                &mut elaborated,
                m,
                style,
                &restriction_frees,
            )
            .map_err(|e| RunError(format!("partial evaluation of {} failed: {}", in_file, e)))?;

            // HS's second `closeTheoryWithMaude` (Prover.hs:263).  The refined
            // rules come back as fresh open rules with empty `variant_substs`
            // and `loop_breakers`, so both closing passes of the first close
            // are redone here: the variant pass (the re-emitted rules render
            // their `rule (modulo AC)` blocks) and then the loop-breaker
            // annotation (`addSolvingLoopBreakers` over the re-closed items —
            // the oracle renders `// loop breaker:` comments on PE'd theories
            // whose refined dataflow graph is still cyclic, e.g.
            // loops/Minimal_Loop_Example.spthy).  Variants must be populated
            // first: the breaker relation's `instances` iterate each rule's
            // variant substitutions.  The no-variant drop above is NOT redone:
            // it is name-keyed and touches `elaborated` only, while partial
            // evaluation can give two refined rules the same name — dropping
            // one side would break the positional parsed↔elaborated rule
            // pairing the closed-theory renderer relies on.
            tamarin_theory::tools::rule_variants::populate_rule_variants(
                &mut elaborated,
                m,
                file_maude_pool.as_deref(),
            );
            annotate_theory_loop_breakers(&mut elaborated, m);
        }

        // `[Theory X] Theory closed` (TheoryLoader.hs:569-615, see line 596)
        // followed by `--partial-evaluation`'s `Debug.Trace` lines, which the
        // oracle forces right after the marker
        // (AbstractInterpretation.hs:109-119).  `pe_trace` is empty unless the
        // flag ran and is already newline-terminated.  Both close paths — the
        // prove loop's and the no-prove / precompute-only one — emit this
        // pair; the `--quit-on-warning` abort above precedes partial
        // evaluation and so prints the marker alone.
        let closed_marker = || {
            marker("Theory closed");
            eprint!("{}", pe_trace);
        };

        // Decide which lemmas to prove.  Without --prove, HS still runs
        // the close-time `checkAndExtendProver` replay over every stored
        // proof skeleton (`closeTheory`, Prover.hs:174-185) — a plain
        // load VALIDATES embedded proofs and reports their real status.
        // We mirror that whenever the file carries a stored proof tree;
        // proofless files keep the cheap no-solver path below, whose
        // output is identical either way (every lemma is a 1-step sorry).
        let lemma_filter: &[String] = &args.lemma_names;
        let prove_anything = args.prove_mode;
        let any_stored_proof = elaborated.lemmas().any(|l| l.proof.tree.is_some());
        // The modes that skip the prove loop entirely: `--precompute-only`
        // renders stats instead, and a plain load with no stored skeleton to
        // replay has nothing to run.
        let skips_prove_loop = args.precompute_only || (!prove_anything && !any_stored_proof);

        let mut results: Vec<LemmaResult> = Vec::new();
        // Mirrors HS's per-lemma proof body for embedding in the
        // pretty-printed theory output.  Filled by the prove loop below.
        let mut proved_lemmas: Vec<tamarin_theory::pretty_theory::ProvedLemma> = Vec::new();
        // HS `systemsWithMetadata` (Batch.hs:290-299) for THIS file: the
        // labelled solved systems `outputTraces` serialises, in lemma
        // declaration order.  Empty unless `--output-dot`/`--output-json`
        // asked for them.
        let mut trace_systems: Vec<(String, System)> = Vec::new();

        // No proof step requested — record each lemma as Filtered
        // / Skipped depending on whether --lemma had any effect.
        // (Shared by the cheap branch below and the session-build
        // failure fallback inside the prove/check branch.)
        let push_skipped_results =
            |results: &mut Vec<LemmaResult>, elaborated: &tamarin_theory::theory::Theory| {
                for l in elaborated.lemmas() {
                    results.push(LemmaResult {
                        name: l.name.clone(),
                        verdict: if lemma_filter.is_empty() || lemma_matches(lemma_filter, &l.name)
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

        // `--auto-sources` (HS `closeTheoryWithMaude` autosources branch,
        // Prover.hs:170-251, see line 171): when the raw sources contain
        // partial deconstructions, annotate the rules with AUTO_* actions and
        // add the `AUTO_typing` sources lemma.  HS applies this on EVERY
        // theory close — the plain-load echo and the proving pipeline alike —
        // so it runs before the load/prove branch below, mutating both
        // `parsed` (for rendering) and `elaborated` (for lemma iteration and
        // the proving session).  Auto-sources needs Maude (HS runs it in the
        // `WithMaude` reader), so a missing handle is an error, same as the
        // prove path's.  Translate mode skips it: `translateAndCheckTheory`
        // never calls `closeTheoryWithMaude`, so `--auto-sources` is inert
        // there (no `AUTO_typing` lemma, no AUTO_* annotations) even though
        // the flag is still read.
        if auto_sources && !translate_mode {
            let m = file_maude
                .clone()
                .ok_or_else(|| RunError(format!("failed to start maude at {:?}", maude_path)))?;
            tamarin_theory::auto_sources::apply_auto_sources(
                &mut parsed,
                &mut elaborated,
                m,
                file_maude_pool.clone(),
                ndc_cache.as_ref(),
            );
        }

        // Translate mode never proves and never replays stored skeletons —
        // `translateAndCheckTheory` skips `closeTranslatedTheory`'s
        // `proveTheory` entirely (TheoryLoader.hs:768-781) — so it takes the
        // cheap arm regardless of `--prove` / stored proofs.
        if translate_mode || skips_prove_loop {
            push_skipped_results(&mut results, &elaborated);
        } else {
            // Reuse the per-file maude handle.  The `maude tool: ...`
            // banner is printed once at the top of the batch run (see
            // above), matching HS.
            let maude = file_maude
                .clone()
                .ok_or_else(|| RunError(format!("failed to start maude at {:?}", maude_path,)))?;

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
            let session = tamarin_theory::prove::ProverSession::build_with_in_file_and_heuristic(
                &parsed,
                maude.clone(),
                file_maude_pool.clone(),
                in_file,
                cli_heuristic.clone(),
                cut,
                ndc_cache.as_ref(),
            )
            .ok();

            // HS prints "[Theory X] Theory closed" right after `closeTheory`
            // (TheoryLoader.hs:569-615, see line 596) and BEFORE the proof search, which it
            // forces lazily as `provedThy` is serialised — so the marker
            // appears in moments regardless of proving cost.  RS's
            // `ProverSession::build` is the `closeTheory` analog, so emit the
            // marker here (before the prove loop) to match HS's observable
            // stderr order.  The no-prove / precompute-only paths (which skip
            // the prove loop) emit it below instead.
            closed_marker();

            let run_lemma = |l: &tamarin_theory::theory::Lemma<_>| -> (
                tamarin_theory::pretty_theory::ProvedLemma,
                LemmaResult,
                Vec<(String, System)>,
            ) {
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
                let is_target = prove_anything && lemma_matches(lemma_filter, &lemma_name);
                // HS does NOT print a per-lemma "proving lemma X ..."
                // marker; the only progress lines are the `[Theory X]
                // ...` set above.  Stay quiet here for HS-faithful stderr.
                let lt = Instant::now();
                let outcome = match (session.as_ref(), is_target) {
                    (Some(s), true) => {
                        tamarin_theory::prove::prove_lemma_in_session(s, &lemma_name, budget)
                    }
                    (Some(s), false) => tamarin_theory::prove::check_and_extend_lemma_in_session(
                        s,
                        &lemma_name,
                        budget,
                    ),
                    (None, _) => tamarin_theory::prove::prove_lemma_with_pool_file_heuristic(
                        &parsed,
                        &lemma_name,
                        maude.clone(),
                        file_maude_pool.clone(),
                        budget,
                        in_file,
                        &cli_heuristic,
                        cut,
                        ndc_cache.as_ref(),
                    ),
                };
                // HS `systemsWithMetadata` (Batch.hs:290-299) reads the proof
                // tree of every lemma, so the collection has to happen here —
                // the tree is consumed for its solved `System`s once verdict
                // and proof body are rendered.  Both arms above feed it: a
                // stored `SOLVED` proof surfaces through
                // `check_and_extend_lemma_in_session`, which is why
                // `_analyzed` theories carry traces without `--prove`.
                let mut lemma_traces: Vec<(String, System)> = Vec::new();
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
                        let v =
                            match tamarin_theory::constraint::solver::search::proof_status(&root) {
                                ProofStatus::TraceFound => {
                                    if is_exists {
                                        LemmaVerdict::Verified
                                    } else {
                                        LemmaVerdict::Falsified
                                    }
                                }
                                ProofStatus::Complete => {
                                    if is_exists {
                                        LemmaVerdict::Falsified
                                    } else {
                                        LemmaVerdict::Verified
                                    }
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
                        if want_traces {
                            for (path, sys) in
                                tamarin_theory::constraint::solver::search::into_solved_systems(
                                    root,
                                )
                            {
                                lemma_traces.push((
                                    trace_output_label(&theory_name, &lemma_name, &path),
                                    sys,
                                ));
                            }
                        }
                        (v, steps, Some(body))
                    }
                    Err(tamarin_theory::prove::ProveError::Guarded(msg)) => {
                        // HS `formulaToGuarded_ = either (error . render) id`
                        // (Guarded.hs:466-467): a proven lemma whose formula
                        // cannot be converted to a guarded formula kills the
                        // whole run — message on stderr, exit 1, and NO
                        // theory output on stdout (HS renders lazily after
                        // proving, so the abort precedes all stdout output).
                        std::process::exit(ghc_exception(&msg));
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
                (pl, lr, lemma_traces)
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
                let cache_disabled = tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE");
                sess.presaturate_shared_sources(cache_disabled, |name| {
                    prove_anything && lemma_matches(lemma_filter, name)
                });
                let specs: Vec<&tamarin_theory::theory::Lemma<_>> = elaborated.lemmas().collect();
                let mut out: Vec<(
                    usize,
                    tamarin_theory::pretty_theory::ProvedLemma,
                    LemmaResult,
                    Vec<(String, System)>,
                )> = specs
                    .par_iter()
                    .enumerate()
                    .map(|(i, l)| {
                        let (pl, lr, tr) = run_lemma(l);
                        (i, pl, lr, tr)
                    })
                    .collect();
                // Reassemble in DECLARATION order so output is identical to the
                // sequential loop regardless of which worker finished first.
                // That order is also HS `getLemmas thy`'s (Batch.hs:292), which
                // is what `outputTraces` serialises the graphs in.
                out.sort_by_key(|(i, _, _, _)| *i);
                for (_, pl, lr, tr) in out {
                    proved_lemmas.push(pl);
                    results.push(lr);
                    trace_systems.extend(tr);
                }
            } else if !prove_anything {
                // The plain-load check pass needs the session's
                // check_and_extend arm; the pool fallback below always
                // auto-proves.  If the session failed to build, keep the
                // no-solver behaviour instead of launching searches nobody
                // asked for.
                push_skipped_results(&mut results, &elaborated);
            } else {
                for l in elaborated.lemmas() {
                    let (pl, lr, tr) = run_lemma(l);
                    proved_lemmas.push(pl);
                    results.push(lr);
                    trace_systems.extend(tr);
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
        // precompute-only paths, which skip that loop.  Translate mode never
        // closes — `translateAndCheckTheory` has no `closeTranslatedTheory`
        // call, so its `traceM` (TheoryLoader.hs:694) never fires and the
        // stderr stream ends with the derivation-check markers.
        if !translate_mode && skips_prove_loop {
            closed_marker();
        }

        if args.precompute_only {
            // HS `--precompute-only` (Batch.hs:96-100, 201-206): the file's
            // doc is `ppWf report $--$ prettyPrecomputation thy''` — the
            // wellformedness WARNING line and a compact 3-line stats
            // overview — NOT the full closed theory.  The stats need the
            // closed theory's saturated sources, so build the prover
            // session (the `closeTheory` analog) here — in-loop, like HS's
            // eager close — but defer forcing the sources to the print
            // phase below, where HS's lazy renderDoc forces them.
            let maude = file_maude
                .clone()
                .ok_or_else(|| RunError(format!("failed to start maude at {:?}", maude_path)))?;
            let cli_heuristic = tamarin_theory::prove::CliHeuristic {
                raw: args.heuristic.clone(),
                oracle_name: args.oracle_name.clone(),
                oracle_only: args.oracle_only,
            };
            let session = tamarin_theory::prove::ProverSession::build_with_in_file_and_heuristic(
                &parsed,
                maude,
                file_maude_pool.clone(),
                in_file,
                cli_heuristic,
                cut,
                ndc_cache.as_ref(),
            )
            .map_err(|e| RunError(e.to_string()))?;
            let wf_len = wf_report.len();
            precompute_pending.push((session, parsed, wf_len));
        } else if let Some(opts) = print_opts {
            // Translate-only render (`prettyOpenTheoryByModule`,
            // TheoryLoader.hs:783-801, followed by `withVersionAndReport`'s
            // two trailing comment items, TheoryLoader.hs:636-660).  The doc
            // is BUFFERED — Batch.hs:101-113 processes every file before any
            // doc is printed or written.  `_sapic_funs_guard` is still held
            // here, so formula→guarded conversion inside the lemma renderers
            // resolves user symbols exactly as the parse-only path does.
            let wf_block = tamarin_theory::pretty_theory::format_wf_block(&wf_report);
            let process_defs = tamarin_sapic::inline::collect_process_defs(&parsed);
            let conv = |proc: &tamarin_parser::ast::Process| {
                tamarin_sapic::inline::convert_process_with_defs(proc, &process_defs)
                    .map_err(|e| e.message)
            };
            let body = tamarin_theory::pretty_theory::pretty_open_theory_by_module(
                &parsed,
                &elaborated,
                in_file,
                &conv,
                &opts,
                &wf_block,
                &build_info,
            )
            .map_err(|e| {
                RunError(format!(
                    "open-theory rendering of {} failed: {}",
                    in_file, e
                ))
            })?;
            translate_docs.push(body);
        } else {
            // HS `outputTraces` (Batch.hs:224-225) runs in `processThy`'s
            // close-and-prove `else` — the ONLY branch that reaches it.
            // `--parse-only` (Batch.hs:198-200), `--precompute-only`
            // (:202-208) and `-m` (:210-220) all return first, so they leave
            // the target paths untouched, as does a run with no input files
            // (`helpAndExit`, Batch.hs:90) and `--diff` (the `bitraverse`
            // `Right` arm is `pure ()`; RS rejects `--diff` before the loop).
            // It precedes the theory render, matching HS's force order: the
            // write is an `IO` action inside `processThy`, while the doc is
            // rendered later in `Batch.hs`'s output phase.
            if want_traces {
                write_output_traces(args, trace_systems)?;
            }
            // Build the HS-faithful theory pretty-print body.  This replaces
            // the verbatim source dump with HS's `prettyClosedTheory`
            // output shape — re-rendered signature, rules with `(modulo E)`
            // prefix and AC-variant comments, lemmas with inline guarded
            // formula and proof body, wellformedness block, and
            // Generated-from footer.
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
            // HS normal mode: `writeOutput` is true whenever `-o`/`-O` was
            // given (Batch.hs:167), and a `mkOutPath` miss — `-o=` with no
            // `-O` — `die`s with this exact line (Batch.hs:118-123) instead
            // of falling back to stdout: markers printed, stdout empty, rc 1.
            // (HS processes every file before dying; with several input
            // files this port dies after the first, an accepted divergence —
            // the condition is argv-constant, so no file output differs.)
            if (args.output_file.is_some() || args.output_dir.is_some())
                && out_path_for(args, in_file).is_none()
            {
                return Ok(missing_output_path());
            }
            emit_output(args, in_file, &body)?;
        }

        file_results.push(FileResult {
            in_file: in_file.clone(),
            out_file: out_path_for(args, in_file),
            results,
            elapsed_ms: t0.elapsed().as_millis(),
            wf_count: wf_report.len(),
        });
    }

    // HS-faithful: `--parse-only` and `--precompute-only` return from
    // `Batch.hs:91-100` before `ppRep` runs, so they skip the `summary of
    // summaries:` block entirely and instead print each file's doc via
    // `mapM_ (putStrLn . renderDoc)` — one trailing newline per doc, always
    // to stdout (`-o`/`-O` ignored), after ALL files were processed.
    // Every other batch run emits the summary on stdout, `--quiet`
    // notwithstanding (see `Args::quiet`).
    if args.parse_only {
        for doc in &parse_only_docs {
            println!("{}", doc);
        }
    } else if args.precompute_only {
        // HS precompute arm (Batch.hs:96-100): same deferred
        // `mapM_ (putStrLn . renderDoc)` shape as `--parse-only` — all
        // docs to stdout after the file loop, no summary block.  Forcing
        // each file's stats here (traces, then its doc) reproduces HS's
        // renderDoc-time stderr order — see `precompute_pending`.
        for (session, parsed, wf_len) in &precompute_pending {
            // HS prints the trace lines only under `showSaturationSteps`
            // (on in this mode alone).  Scope the flag tightly around the
            // forcing so no other phase can emit trace lines.
            //
            // DELIBERATE DIVERGENCE (--auto-sources only): HS also traces
            // the redundant cache closes inside its auto-sources branch
            // (`closeTheoryWithMaude` forces `cache items` for the trigger
            // check and `cache itemsModAC` inside `addAutoSourcesLemma`,
            // CloseRule.hs:56-110), emitting 4 sequences where RS emits
            // the 2 that produce the reported sources (final raw +
            // refined).  Stdout stats match byte-for-byte; matching the
            // extra sequences would mean re-running those redundant
            // saturations.
            tamarin_theory::constraint::solver::sources::set_show_saturation_steps(true);
            let stats = session.precomputation_stats(parsed);
            tamarin_theory::constraint::solver::sources::set_show_saturation_steps(false);
            let stats = stats.map_err(|e| RunError(e.to_string()))?;
            // HS `casesInfo` (ClosedTheory.hs:563-570).
            let chain_info = |n: usize| -> String {
                if n == 0 {
                    "deconstructions complete".to_string()
                } else {
                    format!("{n} partial deconstructions left")
                }
            };
            let mut doc = String::new();
            // `ppWf` (Batch.hs:244-246) joined by `$--$`: exactly one blank
            // line between the WARNING and the stats, nothing when the
            // report is empty.  The prove-mode "might be wrong!" second
            // line never applies here.
            if *wf_len > 0 {
                doc.push_str(&format!(
                    "WARNING: {} wellformedness check failed!\n\n",
                    wf_len
                ));
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
    } else if translate_mode {
        // Translate-only output phase (Batch.hs:101-113): every file was
        // processed above; now either write the docs to `-o`/`-O` or print
        // them to stdout.  NO `summary of summaries:` block in this mode.
        if args.output_file.is_some() || args.output_dir.is_some() {
            // `mapM mkOutPath inFiles` (Batch.hs:106-110): resolve EVERY
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
                write_file_with_dirs(out, doc)?;
            }
        } else {
            for doc in &translate_docs {
                // `mapM_ (putStrLn . renderDoc) docs` — exactly one trailing
                // newline per doc.
                println!("{}", doc);
            }
        }
    } else {
        print_overall_summary(&file_results, args.prove_mode);
    }

    Ok(overall_status)
}

/// Run `annotate_loop_breakers` over the theory's rules, in place and in
/// source order.  Used by the first close (mirroring the breaker pass of HS
/// `closeTheoryWithMaude`) and again by the `--partial-evaluation` re-close
/// (`applyPartialEvaluation`'s second `closeTheoryWithMaude`, Prover.hs:240).
fn annotate_theory_loop_breakers(
    elaborated: &mut tamarin_theory::theory::Theory,
    m: &tamarin_term::maude_proc::MaudeHandle,
) {
    use tamarin_theory::theory::TheoryItem;
    let mut rules: Vec<&mut tamarin_theory::theory::OpenProtoRule> = elaborated
        .items
        .iter_mut()
        .filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .collect();
    tamarin_theory::constraint::solver::context::annotate_loop_breakers(&mut rules, m);
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
/// file (`writeFileWithDirs`, Utils.hs:20-23) and `putStrLn`s it to stdout
/// (Batch.hs:127-133), and `renderDoc` of a closed theory ends at `end` with
/// no newline.  `body` carries the stdout form (one trailing newline), so the
/// file write drops it — oracle-verified: a v1.13.0 `--output=FILE` run ends
/// the file with the bytes `end`.
fn emit_output(args: &Args, in_file: &str, body: &str) -> Result<(), RunError> {
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

    /// Byte-exact against the oracle's `--with-json=/no/such/jsonbin`
    /// interactive startup transcript (HS `testProcess`' `errMsg`,
    /// Console.hs:114-121, with `ensureGraphCommand`'s default message,
    /// Environment.hs:114-115).  The `stdin:`/`stdout:`/`stderr:` labels keep
    /// their padding spaces on empty streams.
    #[test]
    fn which_probe_failure_report_is_byte_exact() {
        let got = which_probe_error_report(
            "failed with exit code 1\n\nCommand not found\n",
            "/no/such/jsonbin",
            "",
            "",
        );
        assert_eq!(
            got,
            "failed with exit code 1\n\
             \n\
             Command not found\n\
             \n\
             Detailed results from testing 'which'\n \
             command: which /no/such/jsonbin\n \
             stdin:   \n \
             stdout:  \n \
             stderr:  \n"
        );
    }

    #[test]
    fn which_probe_report_echoes_captured_streams() {
        let got = which_probe_error_report(
            "Command not found\n",
            "jsonbin",
            "/usr/bin/jsonbin\n",
            "warn\n",
        );
        assert_eq!(
            got,
            "Command not found\n\
             \n\
             Detailed results from testing 'which'\n \
             command: which jsonbin\n \
             stdin:   \n \
             stdout:  /usr/bin/jsonbin\n\n \
             stderr:  warn\n\n"
        );
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
        assert!(
            matches!(r, Err(RunError(_))),
            "diff should error, got {:?}",
            r
        );
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
        // without ever opening a socket.  A WORKDIR must be present: without
        // one the mode help-and-exits before looking at `--interface`
        // (Interactive.hs:76-80), returning `Ok(1)` rather than an error.
        let a = parse(&["interactive", "--interface=not-an-ip", "/tmp"]);
        let r = run(&a);
        assert!(r.is_err(), "expected interface parse error");
    }

    #[test]
    fn no_input_files_is_help_and_exit_not_an_error() {
        // HS `helpAndExit` (Console.hs:341-359) prints to STDOUT and
        // `exitFailure`s; it never builds an error value, so neither does this.
        // The bytes and streams are pinned end-to-end in
        // `tests/help_output.rs::no_input_files_reprints_the_help_after_an_error_line_on_stdout`.
        let a = parse(&[]);
        assert_eq!(run(&a).expect("help-and-exit is not an error"), 1);
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
        // showProofStatus _ IncompleteProof = "analysis incomplete"
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Analyzed, false, 5)),
            "L (all-traces): analysis incomplete (5 steps)",
        );
    }

    // HS `traceLabelOptions` (Batch.hs:305-317) is a CONSTANT in batch mode:
    // `defaultGraphOptions` (SL2 / AS False / CL False / A True / C True,
    // Graph.hs:66-72) and `defaultDotOptions`' `CompactBoringNodes`
    // (Dot.hs:84-87) are hard-coded at Batch.hs:254-255.  Pinned against the
    // v1.13.0 oracle's `digraph` lines.
    #[test]
    fn trace_label_options_is_the_batch_constant() {
        assert_eq!(trace_label_options(), "SL2-AS0-CL0-A1-C1-NB");
    }

    // `traceOutputLabel` (Batch.hs:290-303): `"trace_" ++ thyName ++ "_" ++
    // options ++ "_" ++ lemmaName ++ intercalate "-" proofPath` — with NO
    // separator before the path.  HS's single-case methods use the empty case
    // name, so the leading dash comes from `intercalate` after an empty first
    // element; the oracle's `prove_sr.dot` digraph id is exactly the second
    // case below.
    #[test]
    fn trace_output_label_has_no_separator_before_the_path() {
        assert_eq!(
            trace_output_label("T", "L", &[]),
            "trace_T_SL2-AS0-CL0-A1-C1-NB_L",
        );
        assert_eq!(
            trace_output_label("SingleRecv", "chain", &["".into(), "Send".into()]),
            "trace_SingleRecv_SL2-AS0-CL0-A1-C1-NB_chain-Send",
        );
        assert_eq!(
            trace_output_label("T", "L", &["".into(), "c1".into(), "c2".into()]),
            "trace_T_SL2-AS0-CL0-A1-C1-NB_L-c1-c2",
        );
    }

    // `intercalate "\n" $ map serializeDot labelledSystems` (Batch.hs:263):
    // every graph already ends `}\n`, so the separator leaves exactly one
    // blank line between graphs and the document ends `}\n`; an empty list is
    // `intercalate "\n" [] == ""`, i.e. a 0-byte file.
    #[test]
    fn dot_graph_join_reproduces_hs_intercalate() {
        let empty: Vec<String> = Vec::new();
        assert_eq!(empty.join("\n"), "");
        let two = [
            "digraph \"a\" {\nx;\n\n}\n".to_string(),
            "digraph \"b\" {\ny;\n\n}\n".to_string(),
        ];
        assert_eq!(
            two.join("\n"),
            "digraph \"a\" {\nx;\n\n}\n\ndigraph \"b\" {\ny;\n\n}\n",
        );
    }
}
