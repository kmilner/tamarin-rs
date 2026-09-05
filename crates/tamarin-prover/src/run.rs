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

use tamarin_term::maude_proc::{MaudeHandle, MaudePool, SharedMaudeCaches};
use tamarin_theory::constraint::system::System;
use tamarin_theory::elaborate::elaborate_with_in_file;
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

#[derive(Debug, PartialEq, Eq)]
pub enum RunError {
    /// An ordinary CLI/runtime error, rendered with the port's `error:` prefix.
    Regular(String),
    /// An exception which escapes to Haskell's top-level runtime handler.
    GhcException(String),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Regular(message) | Self::GhcException(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for RunError {}

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

/// Outcome of proving a single lemma. Mirrors the columns of Haskell's
/// `summary of summaries:` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LemmaVerdict {
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
    };
    format!("{} ({}): {}", r.name, quantifier, body)
}

/// The verdict a whole-tree `ProofStatus` fold means for a lemma of the given
/// quantifier.
///
/// `TraceFound` and `Complete` swap sense with the quantifier: a found trace
/// VERIFIES an exists-trace lemma and FALSIFIES an all-traces one, and a
/// complete proof does the reverse (HS `showProofStatus`,
/// Theory/Proof.hs:1104-1112).
///
/// In batch `--prove` the fold is virtually never `Undetermined`/`Invalidated`
/// — close-time replay annotates every node ⇒ `Incomplete`, and `Invalidated`
/// only arises from interactive reuse-lemma edits — but both map faithfully so
/// the label is correct if such a tree ever surfaces.
fn lemma_verdict(
    status: tamarin_theory::constraint::solver::search::ProofStatus,
    exists_trace: bool,
) -> LemmaVerdict {
    use tamarin_theory::constraint::solver::search::ProofStatus;
    match status {
        ProofStatus::TraceFound if exists_trace => LemmaVerdict::Verified,
        ProofStatus::TraceFound => LemmaVerdict::Falsified,
        ProofStatus::Complete if exists_trace => LemmaVerdict::Falsified,
        ProofStatus::Complete => LemmaVerdict::Verified,
        ProofStatus::Unfinishable => LemmaVerdict::Unfinishable,
        ProofStatus::Incomplete => LemmaVerdict::Analyzed,
        ProofStatus::Undetermined => LemmaVerdict::Undetermined,
        ProofStatus::Invalidated => LemmaVerdict::Invalidated,
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LemmaResult {
    pub name: String,
    pub verdict: LemmaVerdict,
    /// Proof-tree node count — matches HS's "(N steps)" in
    /// `--prove` output (`foldProof proofStepSummary`, ClosedTheory.hs:463-491, see line 484,491,
    /// summing one per ProofStep via `foldProof`, Theory/Proof.hs:358-362).
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
    use tamarin_parser::LemmaAttr;

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
    let (theory, aliases) =
        tamarin_parser::parse_theory_with_manifest(&source, &flags, root.clone(), args.diff)
            .map_err(|error| RunError::Regular(error.to_string()))?;

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
            alias
                .staged
                .as_deref()
                .map_or_else(String::new, &path_field)
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
                    staged.as_deref().map_or_else(String::new, &path_field)
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
                    staged.as_deref().map_or_else(String::new, &path_field)
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

/// `tamarin-prover test` — mirror HS's installation self-test
/// (`Main.Mode.Test`).  HS runs:
///   1. Maude version check.
///   2. GraphViz `dot` version check.
///   3. `Term.tests`, the unification HUnit suite (Test.hs:88-89).
///
/// Only (1) and (2) are ported.  Without (3), neither its
/// `*** Testing the unification infrastructure ***` topic line nor its HUnit
/// progress counter appears, and the summary reads `All tool checks
/// successful.` rather than HS's `All tests successful.`, which would claim a
/// suite ran.  Returns rc=0 on Maude/dot reachable, rc=1 otherwise.
fn run_test(args: &Args) -> Result<i32, RunError> {
    println!("Self-testing the tamarin-prover installation.\n");
    println!("*** Testing the availability of the required tools ***");
    // HS `ensureMaude` (Test.hs:46) runs its two probes through `testProcess`,
    // so the whole maude block lands on STDERR — the `***` topic lines around
    // it are the only part of this section on stdout.  A maude that cannot be
    // started aborts the run inside the probe, so `success_maude` is `false`
    // only for a maude that ran but failed a check.
    let (success_maude, _) = ensure_maude(args, &maude_invocation_path(args));
    // Test.hs:49 — a bare `putStrLn ""` separates the two tool blocks.
    println!();
    // HS `ensureGraphVizDot` (Test.hs:50) reads `dotPath`
    // (Environment.hs:37-38): the `--with-dot` value, else the bare `"dot"`.
    let dot_cmd = args.dot_path.as_deref().unwrap_or("dot");
    // HS `successGraphVizDot = isJust maybeSuccessGraphVizDot` (Test.hs:42-112, see line 51):
    // a missing/unavailable `dot` is a test FAILURE, not a silent skip.
    let success_graphviz = crate::probe::ensure_graph_viz_dot(dot_cmd).is_some();
    println!("\n*** TEST SUMMARY ***");
    // HS `success = successMaude && successGraphVizDot && successTerm`
    // (Test.hs:42-112, see line 96); on failure it warns and `exitFailure` (Test.hs:97-105).
    if success_maude && success_graphviz {
        println!("All tool checks successful.");
        println!("The tamarin-prover should work as intended.\n");
        // Test.hs:100 is `putStrLn "\n           :-) happy proving (-:\n"`, so
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
/// needing a `.spthy` file (Intruder.hs:44-53).
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
    // handle (Intruder.hs:45), so the tool block — stderr only, the rule dump
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
    // HS `Main.Mode.Intruder.run` (Intruder.hs:44-53) starts TWO SEPARATE
    // Maude handles — one on `dhMaudeSig`, one on `bpMaudeSig` — and
    // generates `dhIntruderRules False` then `bpIntruderRules False`, then
    // emits `dhS ++ bpS`.  We mirror the DH handle on `dh_maude_sig()` ALONE
    // (NOT merged with bp): merging exposes pmult/em to Maude during the DH
    // variant query and could perturb DH variant enumeration.  The DH
    // generator is hardcoded `False` in HS, not the --diff flag, so we pass
    // `false`.
    let maude = start_maude(tamarin_term::maude_sig::dh_maude_sig())?;
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
    let bp_maude = start_maude(tamarin_term::maude_sig::bp_maude_sig())?;
    let bp_rules = tamarin_theory::intruder_rules::bp_intruder_rules(false, &bp_maude);
    // HS `putStrLn (dhS ++ bpS)` where each block is `renderDoc .
    // prettyIntruderVariants` (Theory/Model/Rule.hs:1464-1466):
    // blank-line-separated `rule (modulo AC) NAME:` rules with HughesPJ body
    // wrapping (`sep`/`fsep` at the standard width) and NO trailing newline —
    // so the DH and BP blocks abut (the DH `d_inv` body directly precedes the
    // BP `c_pmult` header with no separating newline).  `putStrLn` appends the
    // single trailing newline.
    let dh_s = tamarin_theory::pretty_formula::pretty_intruder_variants(&dh_rules);
    let bp_s = tamarin_theory::pretty_formula::pretty_intruder_variants(&bp_rules);
    print!("{}{}", dh_s, bp_s);
    println!();
    // HS `writeRules` (Intruder.hs:57-62): with `-O`/`--Output` the two blocks
    // ALSO go to `<outDir>/data/intruder_variants_{dh,bp}.spthy`
    // (`dhIntruderVariantsFile`/`bpIntruderVariantsFile`,
    // TheoryLoader.hs:853-858) — each block alone, without the newline
    // `putStrLn` gave the stdout dump.  `writeFileWithDirs` creates the `data`
    // level; a bare `-O` records `""`, which `</>` resolves against the cwd.
    if let Some(out_dir) = &args.output_dir {
        for (rel, body) in [
            ("data/intruder_variants_dh.spthy", &dh_s),
            ("data/intruder_variants_bp.spthy", &bp_s),
        ] {
            let path = PathBuf::from(out_dir).join(rel);
            if let Err(io) = write_file_with_dirs(&path.to_string_lossy(), body) {
                return Ok(ghc_exception(&io));
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

    // Resolve data dir. Without an explicit flag, look for `data/`
    // alongside the working directory or its ancestors — the same
    // search the server already exposes via `resolve_data_dir`.
    let data_dir = tamarin_server::handlers::static_files::resolve_data_dir(
        args.data_dir.clone().map(PathBuf::from),
    );
    // Try to discover a sibling frontend/dist for the bundled UI assets.
    let frontend_dist = guess_frontend_dist(&data_dir);

    let mut cfg =
        tamarin_server::ServerConfig::new(bind_addr, data_dir, maude_invocation_path(args));
    cfg.frontend_dist = frontend_dist;
    // `--bound` is accepted here but NOT routed anywhere: HS interactive
    // stores it in the App autoprover's `apBound`, which every autoprove
    // route then REPLACES with the URL's bound (`getAutoProverR`'s `adapt`,
    // Web/Handler.hs:1235-1249) — so the CLI value is dead in this mode.
    // `-d/--derivcheck-timeout` — same default expression as the batch
    // path's derivation-check block (default 5).
    cfg.derivcheck_timeout = args.derivcheck_timeout.unwrap_or(5);
    cfg.solver_parameters =
        tamarin_theory::constraint::solver::sources::IntegerParameters::with_overrides(
            args.open_chains,
            args.saturation,
        );
    // CLI `--stop-on-trace` — merged with each theory's `configuration:`
    // block at load time (`ProofState::new`), HS `closeTheory` precedence.
    cfg.stop_on_trace = cli_cut(args);
    // `--with-dot` / `--with-json` — HS stores `readOutputCommand as`
    // (Environment.hs:41-45) as `WebUI.outputCmd` (Interactive.hs:138,
    // Web/Types.hs:152); the graph route then spawns `ocGraphCommand` —
    // `dot` args for `OutDot` (Web/Theory.hs:1494-1497), `<cmd> <img>
    // <json>` for `OutJSON` (Web/Theory.hs:1484-1491).  `--with-json` wins
    // when both are given, exactly as `readOutputCommand` prefers it.
    cfg.dot_path = args.dot_path.clone().unwrap_or_else(|| "dot".to_string());
    cfg.json_path = args.json_path.clone();
    // `--no-ndc` — HS captures the CLI's `TheoryLoadOptions` in the
    // `loadTheory thyLoadOptions` closure `withWebUI` runs for every web load
    // (Interactive.hs:135); `addNdcOption` (TheoryLoader.hs:821-826) then writes
    // `ndcCheck` = `not (--no-ndc)` (TheoryLoader.hs:365-366) into each loaded
    // theory's `_deductionChainCheck`.  Set before the eager load below.
    cfg.ndc_check = !args.no_ndc;
    // `--prove` / `--lemma` — `addLemmaToProve` (TheoryLoader.hs:835-838) is
    // the `addNdcOption` sibling in that same `addParamsOptions`, and
    // `theoryLoadFlags` (TheoryLoader.hs:94-107) is part of this mode's flag
    // set (Interactive.hs:70), so the selection reaches every web load's
    // `_lemmasToProve`.
    cfg.lemmas_to_prove = args.lemma_names.clone();
    // `-D/--defines` + `--quit-on-warning` — the rest of `toParserFlags
    // thyOpts` (TheoryLoader.hs:285-291) in that same captured closure, so
    // every web load (startup, upload, reload) evaluates `#ifdef` blocks
    // exactly as batch does.  The `["diff" | diffMode]` element is
    // deliberately omitted: HS's diff mode also switches to the
    // `diffTheory` PARSER, which the port does not implement, and passing
    // the flag alone would parse a hybrid neither pipeline recognises.
    let mut parser_flags: Vec<String> = args.defines.clone();
    if args.quit_on_warning {
        parser_flags.push("quit-on-warning".to_string());
    }
    cfg.parser_flags = parser_flags;

    // Positional args are theory files (Haskell uses a working
    // directory, but we accept either: a single dir arg, or one-or-more
    // .spthy paths).
    let theory_paths: Vec<PathBuf> = collect_theory_paths(&args.in_files)?;

    // HS interactive runs the tool checks BEFORE the banner
    // (Interactive.hs:103-108): `ensureMaudeAndGetVersion` prints the
    // maude block (Console.hs:151-185) and `ensureGraphVizDot` the
    // GraphViz block (Environment.hs:72-87), both on stderr.  Neither is
    // gated on any flag — `--quiet` leaves them in place (see `Args::quiet`).
    // The version data feeds HS's `__versionPrettyPrint__` argument, which
    // this port's web UI does not surface, so only the probe's stderr and its
    // abort-on-missing-maude matter here.
    let _ = ensure_maude(args, &cfg.maude_path);
    // HS picks the graph-tool check by `(readOutputCommand as).ocFormat`
    // (Interactive.hs:106-108): `--with-json` selects `ensureGraphCommand`
    // (Environment.hs:104-115) and the `GraphViz tool:` block does not run at
    // all; otherwise `ensureGraphVizDot` (Environment.hs:72-101) runs.  Both
    // results are discarded (`_ <-`), so an unavailable tool never aborts
    // startup.  `--with-json` also overrides `--with-dot` (Environment.hs:41-45).
    let dot_cmd = args.dot_path.as_deref().unwrap_or("dot");
    if let Some(json_cmd) = args.json_path.as_deref() {
        let _ = crate::probe::ensure_graph_command(json_cmd);
    } else {
        let _ = crate::probe::ensure_graph_viz_dot(dot_cmd);
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
    // The banner's URL is HS `serverUrl` (Interactive.hs:187-190): the
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
    runtime
        .block_on(tamarin_server::serve(cfg, theory_paths))
        .map_err(|e| RunError::Regular(format!("server error: {}", e)))?;
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

/// The effective per-theory cut strategy: the CLI `--stop-on-trace` wins;
/// with the flag absent the theory's `configuration:` block is consulted
/// (HS `configStopOnTrace` precedence, TheoryLoader.hs:759-763).  An
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
    match &opts.stop_on_trace {
        Some(s) => Ok(stop_on_trace_cut(s)),
        None => match block.stop_on_trace.as_deref() {
            Some(raw) => tamarin_theory::prove::parse_stop_on_trace(raw)
                .map_err(|e| RunError::Regular(format!("configuration block: {}", e))),
            None => Ok(CutStrategy::Dfs),
        },
    }
}

/// Map a CLI `--stop-on-trace` value to its `CutStrategy`.  Shared by
/// `effective_cut` (batch prove-mode) and `cli_cut` (interactive), so the
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

/// HS `ensureMaude` (Console.hs:151-185) on the binary this run invokes — the
/// probe every mode but `--parse-only` runs first.
///
/// The name HS reports is `maudePath as` (Console.hs:84-85, read back at :163):
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
/// for both the version check and every later maude spawn (Console.hs:
/// 156-161), so the reported version is always the invoked binary's.
fn maude_invocation_path(args: &Args) -> String {
    args.maude_path.clone().unwrap_or_else(default_maude_path)
}

/// Report an exception that escaped to GHC's runtime the way its top-level
/// handler does: `tamarin-prover: <msg>` on stderr — no batch `error:`
/// prefix, no `[Theory …]` wrapper, nothing on stdout — and exit 1.  Returns
/// that exit code for the caller to propagate.
fn ghc_exception(msg: &str) -> i32 {
    eprintln!("tamarin-prover: {}", msg);
    1
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
fn report_open_file_error(in_file: &str, e: &std::io::Error) -> i32 {
    let reason = if e.kind() == std::io::ErrorKind::IsADirectory {
        "inappropriate type (is a directory)".to_string()
    } else {
        io_exception_reason(e)
    };
    eprintln!("tamarin-prover: {in_file}: openFile: {reason}");
    1
}

/// Report a non-UTF-8 input the way GHC's runtime does.
///
/// The file OPENED, so this failure is not `openFile`'s but the decoder's,
/// raised from `hGetContents` and naming the first byte it rejected in decimal
/// (GHC.IO.Encoding.Failure).  `valid_up_to` indexes exactly that byte — the
/// start of the offending sequence, so a truncated `c3 28` reports 195.
fn report_decode_error(in_file: &str, e: &std::string::FromUtf8Error) -> i32 {
    let bad = e
        .as_bytes()
        .get(e.utf8_error().valid_up_to())
        .copied()
        .unwrap_or_default();
    ghc_exception(&format!(
        "{in_file}: hGetContents: invalid argument \
         (cannot decode byte sequence starting from {bad})"
    ))
}

/// HS `mkOutPath`'s miss — `-o=` with no `-O` — `die`s with this exact line
/// (Batch.hs:119-123) instead of falling back to stdout: the line on stderr,
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
/// Shared with [`report_open_file_error`], which prefixes the same tail with
/// its own `openFile` frame.
///
/// The errnos remain explicit because GHC's buckets differ from Rust's
/// `ErrorKind` classifications (for example EROFS and ELOOP).
fn io_exception_reason(e: &std::io::Error) -> String {
    let errno = e.raw_os_error();
    let ioe_type = match errno {
        // EPERM, EACCES, EROFS
        Some(1) | Some(13) | Some(30) => Some("permission denied"),
        // ENOENT
        Some(2) => Some("does not exist"),
        // EEXIST
        Some(17) => Some("already exists"),
        // ENOTDIR, EISDIR
        Some(20) | Some(21) => Some("inappropriate type"),
        // EINVAL, ENAMETOOLONG, ELOOP
        Some(22) | Some(36) | Some(40) => Some("invalid argument"),
        // ENOSPC, EMLINK, EDQUOT
        Some(28) | Some(31) | Some(122) => Some("resource exhausted"),
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

/// HS `writeFileWithDirs` (Main/Utils.hs:20-23): create the target's parent
/// directories, then write `body` VERBATIM.  Neither step is guarded there,
/// so a failure escapes as the [`write_io_exception`] text — returned here for
/// the caller to report through [`ghc_exception`].
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

/// HS `traceLabelOptions` (Batch.hs:305-317): the fixed middle segment of an
/// `outputTraces` label.  Batch always feeds it `defaultGraphOptions`
/// (Graph.hs:66-72) and `defaultDotOptions` (Theory/Constraint/System/Dot.hs:84-87) — Batch.hs:254-255
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

/// HS `traceOutputLabel` (Batch.hs:290-303): the digraph id (`--output-dot`)
/// and `jgLabel` (`--output-json`) of one serialised trace.
///
/// There is NO separator between the lemma name and the proof path
/// (Batch.hs:302-303 is `++ lemma._lName ++ intercalate "-" proofPath`).
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

/// HS `outputTraces`' two writers (Batch.hs:262-272), run once per input file
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

/// HS `TheoryLoadOptions` (TheoryLoader.hs:224-252) — the batch pipeline's
/// argument record, built once per run by [`mk_theory_load_options`].
///
/// Field order follows HS's record (`mkTheoryLoadOptions`,
/// TheoryLoader.hs:295-395).  All flag validation happens at clap
/// parse time; HS fields with no consumer between this record's
/// construction and the end of the batch run stay on [`Args`]:
/// `proofBound` (`--bound`, read directly by the prove loop),
/// `verboseMode`, `maudePath` (the banner needs the raw
/// user-supplied/None distinction), `diffMode`, and the ProVerif/DeepSec export knobs
/// (backends unported).
#[derive(Debug, Clone)]
struct TheoryLoadOptions {
    /// HS `proveMode`.
    prove_mode: bool,
    /// HS `lemmaNames` (`--prove` ++ `--lemma`).
    lemma_names: Vec<String>,
    /// HS `stopOnTrace` (clap-validated; per-theory merge in
    /// [`effective_cut`]).
    stop_on_trace: Option<crate::cli::StopOnTrace>,
    /// HS folds `--heuristic`/`--oraclename` into one `Heuristic` value here
    /// (TheoryLoader.hs:337-351); the port keeps both raw and defers the
    /// interpretation to `tamarin_theory::prove::CliHeuristic`.
    heuristic: Option<String>,
    oracle_name: Option<String>,
    /// HS `oracleOnly`.
    oracle_only: bool,
    /// HS `partialEvaluation` (TheoryLoader.hs:354-358).
    partial_evaluation: Option<crate::cli::PartialEval>,
    /// HS `defines` (forwarded to the parser as `-D` flags).
    defines: Vec<String>,
    /// HS `quitOnWarning`.
    quit_on_warning: bool,
    /// HS `autoSources` (CLI value only; OR-combined with the theory's
    /// `configuration:` block in the file loop).
    auto_sources: bool,
    /// HS `outputModule` (TheoryLoader.hs:373-377).
    output_module: Option<ModuleType>,
    /// HS `parseOnlyMode`.
    parse_only_mode: bool,
    /// HS `precomputeOnlyMode`.
    precompute_only_mode: bool,
    /// HS `derivationChecks` with its default already resolved
    /// (`derivDefault = 5`, TheoryLoader.hs:391-393; 0 disables).
    derivation_checks: u32,
    /// HS `ndcCheck` — enabled by default, `--no-ndc` clears it
    /// (TheoryLoader.hs:365-366).
    ndc_check: bool,
    /// HS `openChain`/`saturation`, carried into each prover context.
    parameters: tamarin_theory::constraint::solver::sources::IntegerParameters,
}

/// Port of HS `mkTheoryLoadOptions` (TheoryLoader.hs:295-395): assemble the
/// record from the parsed argv.  clap has already validated the enum-valued
/// flags (`--stop-on-trace`, `--partial-evaluation`, `--output-module`), so
/// only `--heuristic=` (an explicit empty ranking) can still fail here.
fn mk_theory_load_options(args: &Args) -> Result<TheoryLoadOptions, RunError> {
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
        stop_on_trace: args.stop_on_trace.clone(),
        heuristic: args.heuristic.clone(),
        oracle_name: args.oracle_name.clone(),
        oracle_only: args.oracle_only,
        partial_evaluation: args.partial_evaluation.clone(),
        defines: args.defines.clone(),
        quit_on_warning: args.quit_on_warning,
        auto_sources: args.auto_sources,
        output_module,
        parse_only_mode: args.parse_only,
        precompute_only_mode: args.precompute_only,
        derivation_checks: args.derivcheck_timeout.unwrap_or(5),
        ndc_check: !args.no_ndc,
        parameters: tamarin_theory::constraint::solver::sources::IntegerParameters::with_overrides(
            args.open_chains,
            args.saturation,
        ),
    })
}

/// HS `[Theory X] …` progress marker (`traceM`, TheoryLoader.hs:451, 496,
/// 581, 594, 696) — stderr, NOT gated by `--quiet` (see [`Args::quiet`]).
fn theory_marker(theory_name: &str, msg: &str) {
    eprintln!("[Theory {}] {}", theory_name, msg);
}

/// No proof step requested — record each lemma as Filtered / Skipped
/// depending on whether --lemma had any effect.  (Shared by translate mode,
/// the no-prove / precompute-only close path, and the session-build failure
/// fallback inside the prove branch.)
fn skipped_results(
    elaborated: &tamarin_theory::theory::Theory,
    lemma_filter: &[String],
) -> Vec<LemmaResult> {
    elaborated
        .lemmas()
        .map(|l| LemmaResult {
            name: l.name.clone(),
            // `lemma_matches` is `lemmaSelector` whole, empty-filter arm
            // included, so it alone decides selection here.
            verdict: if lemma_matches(lemma_filter, &l.name) {
                // Selected (or no filter at all) but no prove flag — skipped.
                LemmaVerdict::Skipped
            } else {
                LemmaVerdict::Filtered
            },
            // HS counts the default `Sorry` placeholder proof
            // as 1 step (one `LNode (ProofStep Sorry ...)` —
            // see `foldProof proofStepSummary`, ClosedTheory.hs:463-491, see line 484,491).
            // Match it.
            proof_steps: 1,
            exists_trace: matches!(
                l.trace_quantifier,
                tamarin_theory::theory::TraceQuantifier::ExistsTrace,
            ),
        })
        .collect()
}

/// What [`TheoryPipeline::close_translated_theory`] hands back to the
/// render/output phase: the per-lemma summary rows, the proof bodies for the
/// closed-theory render, and the labelled solved systems `--output-dot` /
/// `--output-json` serialise.
struct ClosedOutcome {
    results: Vec<LemmaResult>,
    proved_lemmas: Vec<tamarin_theory::pretty_theory::ProvedLemma>,
    trace_systems: Vec<(String, System)>,
}

/// One input file's loading state, threaded through the HS-named loading
/// stages.  The stage methods mirror HS's two pipelines
/// (TheoryLoader.hs:718-781):
///
///   closeTheory             = translateTheory >=> removeTranslationItems
///                             >=> checkTranslatedTheory
///                             >=> closeTranslatedTheory >=> withVersionAndReport
///   translateAndCheckTheory = the same minus closeTranslatedTheory
///
/// `run_batch`'s file loop drives them as: parse → [`Self::translate_theory`]
/// → [`Self::check_translated_theory`] → mode split — the open-theory render
/// for `-m` translate mode, [`Self::close_translated_theory`] + the closed
/// render otherwise.  `withVersionAndReport`'s `--quit-on-warning` raise sits
/// in the loop between the check and the mode split (its report/version
/// comment items are attached by the renderers).
struct TheoryPipeline<'a> {
    args: &'a Args,
    opts: &'a TheoryLoadOptions,
    /// Which of HS's two pipelines this file runs: `Some` selects
    /// `translateAndCheckTheory` and the module the open render uses, `None`
    /// selects `closeTheory`.  Resolved once per run in [`run_batch`] — it is
    /// NOT `opts.output_module`, which the `--parse-only` / `--precompute-only`
    /// guards outrank (Batch.hs:91-113); every stage below reads this field so
    /// no arm can re-derive the answer differently.
    translate_module: Option<TranslateModule>,
    /// Elaborated typed theory.  Behind `Arc` so the `ProverSession` shares
    /// it without a copy; the translate/check stages mutate it through
    /// `Arc::make_mut` while this pipeline holds the only reference.
    elaborated: std::sync::Arc<tamarin_theory::theory::Theory>,
    wf_report: Vec<tamarin_theory::wellformedness::WfError>,
    /// The theory's `MaudeSig`, cloned from `elaborated` before SAPIC
    /// translation runs; drives the per-file Maude spawns.
    maude_sig: tamarin_term::maude_sig::MaudeSig,
    /// Effective per-theory cut strategy + auto-sources: CLI flags merged
    /// with the in-file `configuration:` block ([`effective_cut`] /
    /// `configAutoSources`).
    cut: tamarin_theory::constraint::solver::context::CutStrategy,
    auto_sources: bool,
    /// The maude binary this run invokes (`--with-maude` or the probed
    /// default), resolved once per run and reused by every spawn and
    /// spawn-failure message.
    maude_path: &'a str,
    file_maude: Option<MaudeHandle>,
    file_maude_pool: Option<std::sync::Arc<MaudePool>>,
    ndc_cache: Option<tamarin_theory::constraint::solver::context::IntrRuleCache>,
    /// NDC-tagged function symbols from `check_close_intr_rule`, held for
    /// `close_translated_theory` to join into the signature — HS's
    /// `closeTheory` adopts `checkTranslatedTheory`'s `sign'` while
    /// `translateAndCheckTheory` binds `(postReport, _, _)` and discards it
    /// (TheoryLoader.hs:775-778).
    ndc_funs: Vec<tamarin_term::function_symbols::FunSym>,
}

impl TheoryPipeline<'_> {
    /// `[Theory X] MSG` stderr marker for this file's theory.
    fn marker(&self, msg: &str) {
        theory_marker(&self.elaborated.name, msg);
    }

    /// `[Theory X] Theory closed` (TheoryLoader.hs:668-715, see line 696)
    /// followed by `--partial-evaluation`'s `Debug.Trace` lines, which the
    /// oracle forces right after the marker
    /// (AbstractInterpretation.hs:109-119).  `pe_trace` is empty unless the
    /// flag ran and is already newline-terminated.  Both close paths — the
    /// prove loop's and the no-prove / precompute-only one — emit this pair;
    /// the `--quit-on-warning` abort (loop-side) precedes partial evaluation
    /// and so prints the marker alone.
    fn closed_marker(&self, pe_trace: &str) {
        self.marker("Theory closed");
        eprint!("{pe_trace}");
    }

    /// This file's Maude handle, or the spawn-failure error every close-time
    /// stage reports.  `file_maude` is `Some` whenever the per-file spawn in
    /// [`Self::check_translated_theory`] succeeded.
    fn require_maude(&self) -> Result<MaudeHandle, RunError> {
        self.file_maude.clone().ok_or_else(|| {
            RunError::Regular(format!("failed to start maude at {:?}", self.maude_path))
        })
    }

    /// The CLI half of HS `constructAutoProver` (TheoryLoader.hs:802-810).
    /// When `--heuristic` is given it OVERRIDES the per-lemma / theory
    /// heuristic for every lemma (HS `selectHeuristic`, Theory/Proof.hs:705-716, see
    /// line 707).
    fn cli_heuristic(&self) -> tamarin_theory::prove::CliHeuristic {
        tamarin_theory::prove::CliHeuristic {
            raw: self.opts.heuristic.clone(),
            oracle_name: self.opts.oracle_name.clone(),
            oracle_only: self.opts.oracle_only,
        }
    }

    /// Build this file's shared prover session — the `closeTheory` analog,
    /// which does the file-level setup (intruder rules, Maude variants,
    /// `precompute_full_sources`) ONCE, as HS does at theory-close time.
    /// Both close-time consumers go through here:
    /// [`Self::close_translated_theory`]'s prove loop and
    /// `--precompute-only`'s stats.
    fn build_prover_session(
        &self,
        maude: MaudeHandle,
        cli_heuristic: tamarin_theory::prove::CliHeuristic,
    ) -> Result<tamarin_theory::prove::ProverSession, tamarin_theory::prove::ProveError> {
        tamarin_theory::prove::ProverSession::build(
            self.elaborated.clone(),
            maude,
            tamarin_theory::prove::ProverSessionOptions {
                maude_pool: self.file_maude_pool.clone(),
                cli_heuristic,
                cut: self.cut,
                ndc_cache: self.ndc_cache.clone(),
                parameters: self.opts.parameters,
                sys_retention: if wants_trace_output(self.args) {
                    tamarin_theory::constraint::solver::search::SysRetention::KeepSolved
                } else {
                    tamarin_theory::constraint::solver::search::SysRetention::DropAll
                },
                show_saturation_steps: true,
                loop_breakers_prepared: true,
            },
        )
    }

    /// HS `translateTheory` (TheoryLoader.hs:487-502) plus the
    /// `removeTranslationItems` / lemma-filter behaviour its
    /// `processOpenTheory` dispatch implies (TheoryLoader.hs:470-484): emit
    /// the `Theory translated` marker, run the per-module SAPIC typing /
    /// translation and the accountability translation, and open the report
    /// with the pre-translation
    /// `Sapic.checkWellformedness ++ Acc.checkWellformedness`.
    ///
    /// `Err` is a process exit code whose message is already on stderr (the
    /// GHC-exception shape).
    fn translate_theory(&mut self) -> Result<(), i32> {
        let translate_module = self.translate_module;
        // HS emits this marker at the top of `translateTheory`
        // (TheoryLoader.hs:487-502, see line 496).
        self.marker("Theory translated");

        // SAPIC `process:` translation (HS `typeTheory` → `translate`,
        // TheoryLoader.hs:468-485, see line 472).  Runs ONLY for `is_sapic` theories (exactly one
        // top-level `process:`); a no-op otherwise, so non-process theories are
        // byte-unchanged.  Injects the generated rules + `single_session`
        // restriction + `heuristic: p` into `elaborated`, which the renderers,
        // the solver and the AC-variant pre-computation all read, so it MUST
        // run before the variant pre-computation in
        // `check_translated_theory`.  `user_set_heuristic` is
        // true iff a `heuristic:` item already populated `elaborated.heuristic`
        // (HS `addHeuristic` returns `Nothing` in that case).
        {
            // HS `Acc.checkWellformedness t` (translateTheory, TheoryLoader.hs:487-502, see line 497)
            // runs on the PRE-translation theory `t` — the report is computed
            // from `thy`, not from the `transThy` that `Sapic.translate` /
            // `Acc.translate` produce.  So it must see the ORIGINAL rules /
            // restrictions / case tests, BEFORE `apply_sapic` injects the
            // SAPIC-generated rules (a pure-SAPIC theory has no MSR rules at this
            // point, so `rulesContainPubConst` / `caseTestsInstantiatedByPubVars`
            // scan an empty rule set).  Compute it here, before the mutation.
            let acc_wf = tamarin_accountability::check_wellformedness(&self.elaborated);

            let user_set_heuristic = !self.elaborated.heuristic.is_empty();
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
                let wf: Vec<tamarin_theory::wellformedness::WfError> = if self.elaborated.is_sapic()
                {
                    tamarin_sapic::apply::sapic_pre_report(&self.elaborated)
                } else {
                    Vec::new()
                };
                if translate_module == Some(TranslateModule::SpthyTyped) {
                    // `Sapic.typeTheory` (`typeTheoryEnv`, Typing.hs:204-226):
                    // the typed and renamed processes replace the parse-time
                    // ones in place, and the recomputed `function:` items
                    // replace the source-positioned ones at the end of the
                    // item list.
                    if let Err(e) = tamarin_sapic::type_theory::type_theory_env(
                        std::sync::Arc::make_mut(&mut self.elaborated),
                    ) {
                        // HS: `ProcessNotWellformed` / typing exceptions
                        // escape to GHC's runtime — `tamarin-prover: …`,
                        // exit 1.
                        return Err(ghc_exception(&e.message));
                    }
                }
                wf
            } else {
                match tamarin_sapic::apply::apply_sapic(
                    std::sync::Arc::make_mut(&mut self.elaborated),
                    user_set_heuristic,
                ) {
                    Ok(w) => w,
                    // HS: exceptions SAPIC `translate` raises — e.g. the
                    // `addProtoRule` name clash on inserting a generated rule
                    // (`duplicate rule: <name>`, OpenTheory.hs:727-733) —
                    // escape to GHC's runtime, which writes
                    // `tamarin-prover: <show exception>` to stderr and exits
                    // 1, exactly like the accountability arm below.
                    Err(e) => return Err(ghc_exception(&e.message)),
                }
            };

            // Accountability translation (HS `Acc.translate`, TheoryLoader.hs:468-485, see line 472):
            // `Sapic.translate >=> Acc.translate`.  Expands each
            // `... accounts for` lemma into its verification-condition lemmas +
            // case-test predicates, appending them to `elaborated`, which the
            // renderers and the prove loop read.  A no-op for theories with neither
            // accountability lemmas nor case tests (a `test` without any acc
            // lemma still gets its predicate appended, as in HS).  Runs inside
            // the user-funs guard so the generated lemmas' embedded case-test
            // formulas resolve their user function symbols with the theory's
            // private/destructor flags.  Not part of `processOpenTheory`'s
            // `spthy` / `spthytyped` arms, so those translate modes skip it.
            if !skip_translation
                && let Err(e) = tamarin_accountability::translate(std::sync::Arc::make_mut(
                    &mut self.elaborated,
                ))
            {
                // HS: the exceptions `Acc.translate` throws — `CaseTestsUndefined`
                // (lib/accountability/src/Accountability.hs:42-49, see line 45) and the `UndefinedPredicate` /
                // `DuplicateItem` parsing exceptions its `liftedAddLemma` /
                // `liftedAddPredicate` folds raise (Theory/Text/Parser.hs:141-152,
                // Parser/Signature.hs:328-331) — escape to GHC's runtime, which
                // writes `tamarin-prover: <show exception>` to stderr and exits
                // 1 — no batch `error:` / `[Theory …]` wrapper (the maude banner
                // + the `Theory loaded`/`Theory translated` markers already
                // printed).
                return Err(ghc_exception(&e.to_string()));
            }

            // HS `preReport = Sapic.checkWellformedness t ++ Acc.checkWellformedness t`
            // (TheoryLoader.hs:487-502, see line 497), the FRONT of the report
            // (`preReport ++ postReport`, TheoryLoader.hs:726-732): SAPIC-process
            // warnings first, then the accountability RP check (computed above,
            // pre-translation).  `check_translated_theory` appends `postReport`
            // behind them.  The trailing `N wellformedness check failed` summary
            // counts them via `wf_report.len()`.
            self.wf_report.extend(sapic_wf);
            self.wf_report.extend(acc_wf);
        }

        // `-m msr` keeps only the selected lemmas (`processOpenTheory`'s
        // `filterLemma (lemmaSelector thyOpts)` tail, TheoryLoader.hs:475-480
        // + TheoryObject.hs:567-580): `LemmaItem`s not matching the
        // `--prove`/`--lemma` selector are dropped, everything else stays.
        // `lemma_matches` already implements `lemmaSelector`'s `[]` / `[""]`
        // / `["",""]` ⇒ keep-all rules, so this retain is a no-op without a
        // real selector.  Runs BEFORE the wellformedness re-runs in
        // `check_translated_theory` so they see the filtered theory, as
        // `checkTranslatedTheory` does.  The `[output=[msr]]` lemma
        // attribute (`lemmaSelectorByModule`) is deliberately NOT honoured
        // here — HS consults it only in `closeTranslatedTheory`
        // (TheoryLoader.hs:702-703), which translate mode never reaches.
        if translate_module == Some(TranslateModule::Msr) {
            let lemma_names: &[String] = &self.opts.lemma_names;
            std::sync::Arc::make_mut(&mut self.elaborated)
                .items
                .retain(|i| match i {
                    tamarin_theory::theory::TheoryItem::Lemma(l) => {
                        lemma_matches(lemma_names, &l.name)
                    }
                    _ => true,
                });
        }

        Ok(())
    }

    /// HS `checkTranslatedTheory` (TheoryLoader.hs:553-615): the per-file
    /// Maude spawn (the `SignatureWithMaude` analog), the rule-variant
    /// pre-computation, the wellformedness pass over the TRANSLATED theory,
    /// the once-per-theory NDC pass, and the dynamic Message Derivation
    /// Checks.  The NDC-joined signature is NOT applied here: `ndc_funs` is
    /// stashed for `close_translated_theory`, mirroring how HS's `closeTheory`
    /// adopts this stage's `sign'` while `translateAndCheckTheory` discards
    /// it.
    ///
    /// [`Self::translate_module`] gates only the loop-breaker annotation —
    /// see the comment at that block.
    fn check_translated_theory(&mut self) -> Result<(), RunError> {
        // Spawn a single Maude handle for this file.  Used by:
        //   - the rule-variants computation that populates each rule's
        //     `variant_substs` + `abstracted_rule` (so the pretty-printer
        //     can emit HS's `variants (modulo AC) ...` block);
        //   - the dynamic Message Derivation Check;
        //   - the per-lemma prove loop.
        //
        // One memo-cache set for this theory session, shared by
        // `file_maude` and every `file_maude_pool` member: an identical
        // query issued from any of these subprocesses reuses the memoized
        // result.  See `SharedMaudeCaches` (maude_proc.rs) for the
        // byte-parity argument and lock-order invariant.
        // (`--parse-only` never reaches here — it `continue`d before any
        // Maude is needed, Batch.hs:91-95.)
        let session_maude_caches = std::sync::Arc::new(SharedMaudeCaches::default());
        self.file_maude = MaudeHandle::start_with_caches(
            self.maude_path,
            self.maude_sig.clone(),
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
        let pool_size = self.args.effective_maude_processes();
        self.file_maude_pool = if pool_size >= 2 {
            match MaudePool::new(
                self.maude_path,
                self.maude_sig.clone(),
                pool_size,
                std::sync::Arc::clone(&session_maude_caches),
            ) {
                Ok(p) => Some(std::sync::Arc::new(p)),
                Err(e) => {
                    // RS-only diagnostic (HS has no Maude pool), so
                    // `--quiet` may drop it — see `Args::quiet`.
                    if !self.args.quiet {
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

        // Close protocol rules in the same shared order as the web loader:
        // variants, post-translation wellformedness, zero-variant filtering,
        // then loop breakers. Translate mode runs the first three but does not
        // persist breaker annotations on its open theory.
        let translate_mode = self.translate_module.is_some();
        if let Some(m) = self.file_maude.as_ref() {
            self.wf_report
                .extend(tamarin_theory::tools::rule_variants::prepare_theory_rules(
                    std::sync::Arc::make_mut(&mut self.elaborated),
                    m,
                    self.file_maude_pool.as_deref(),
                    !translate_mode,
                )?);
        } else {
            self.wf_report
                .extend(tamarin_theory::wellformedness::check_wellformedness(
                    &self.elaborated,
                    None,
                ));
        }

        // `showSaturation` is the last argument of `closeTheoryWithMaude`
        // (CloseRule.hs:57), and exactly two closes pass `False`: the NDC
        // deduction check (`closeTheoryWithMaude sig t False False`,
        // CloseRule.hs:246,251) and the message-derivation check
        // (`closeTheoryWithMaude sig t sources False`,
        // MessageDerivationChecks.hs:42). Both are what this method runs, so
        // the trace is silent across it; the close contexts below enable it
        // for the close proper.

        // Once-per-theory NDC pass (HS `checkCloseIntrRule` inside
        // `checkTranslatedTheory`, TheoryLoader.hs — BEFORE the
        // derivation checks): assemble the intruder cache, run the
        // no-deconstruction-chain check (unless `--no-ndc`), and stash the
        // tagged symbols for the close pipeline's `joinNDCinSigWMaude`
        // (see the `ndc_funs` field doc — the join is close-only, so no
        // `[NDC]` attribute can reach translate mode's printed
        // `functions:` / `function:` lines).
        // The checked cache is a shared handle injected into every
        // `ProofContext` built for this theory (derivation-check
        // probes, auto-sources scratch contexts, the prover session, the
        // per-lemma fallback), which all reuse this one allocation —
        // mirroring HS's `closeRuleCache` consuming `_thyCache` verbatim.
        // The `No Deconstruction Chain checks started/ended` markers ride the
        // same rule as the sibling `[Theory X]` markers: printed whenever the
        // stage runs, `--quiet` notwithstanding.
        // `file_maude` is `Some` only when the Maude spawn succeeded, and
        // `--parse-only` `continue`d long before this stage.
        if let Some(m) = self.file_maude.as_ref() {
            let checked = tamarin_theory::close_rule::check_close_intr_rule(
                m,
                Some(self.elaborated.name.as_str()),
                self.elaborated.options.deduction_chain_check,
                &self.elaborated.intruder_rules,
                self.opts.parameters,
            )?;
            self.ndc_funs = checked.ndc_funs;
            self.ndc_cache = Some(checked.cache.into());
        }

        // Dynamic Message Derivation Checks (mirrors HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout`,
        // default 5s).  Needs Maude, so we run it AFTER elaboration
        // and BEFORE the main prove loop.  HS default is 5s; 0 disables.
        // Each per-variable proof attempt is capped at this timeout.
        let deriv_timeout = self.opts.derivation_checks;
        if deriv_timeout > 0 {
            // HS emits these markers around the per-variable derivability
            // check (TheoryLoader.hs:578-594, see line 581, :594).
            self.marker("Derivation checks started");
            if let Some(m) = self.file_maude.as_ref() {
                let extra = tamarin_theory::deriv_check::check_message_derivation(
                    &self.elaborated,
                    m,
                    deriv_timeout,
                    self.ndc_cache.clone(),
                    self.opts.parameters,
                )?;
                self.wf_report.extend(extra);
            }
            self.marker("Derivation checks ended");
        }
        Ok(())
    }

    /// HS `closeTranslatedTheory` (TheoryLoader.hs:668-715) plus the parts of
    /// `closeTheoryWithMaude` the port runs at close time: adopt the
    /// NDC-joined signature, apply `--partial-evaluation`
    /// (`applyPartialEvaluation`'s second close), apply `--auto-sources`, and
    /// run the per-lemma prove / stored-proof replay loop (HS `proveTheory`)
    /// with its `Theory closed` marker.  Translate mode never calls this —
    /// `translateAndCheckTheory` has no `closeTranslatedTheory` call
    /// (TheoryLoader.hs:768-781) — so `--partial-evaluation` and
    /// `--auto-sources` are inert there even though the flags are still read.
    fn close_translated_theory(&mut self) -> Result<ClosedOutcome, RunError> {
        let in_file = self.elaborated.in_file.clone();
        let want_traces = wants_trace_output(self.args);

        // The close proper: HS's `closeTranslatedTheory` (TheoryLoader.hs:679),
        // `Prover.closeTheory` (Prover.hs:51) and `applyPartialEvaluation`
        // (Prover.hs:238-242, see line 242) all pass `showSaturation = True`, so every
        // saturation from here on — auto-sources, the prover session, the
        // `--precompute-only` forcing that runs after the per-file loop —
        // traces.
        //

        // Adopt the NDC verdicts into the printed signature
        // (`joinNDCinSigWMaude`): `check_translated_theory` stashed the
        // tagged symbols, and only the close pipeline applies them — HS's
        // `closeTheory` threads `checkTranslatedTheory`'s `sign'` into
        // `closeTranslatedTheory`, so every later rendering — including the
        // no-prove and `--precompute-only` paths — shows `[NDC]` on tagged
        // symbols.
        for f in &self.ndc_funs {
            let elab = std::sync::Arc::make_mut(&mut self.elaborated);
            let sig = std::mem::take(&mut elab.signature);
            elab.signature =
                sig.join_ndc_in_sig(*f, tamarin_term::function_symbols::NdcState::IsNdc);
        }

        // `--auto-sources` (HS `closeTheoryWithMaude` autosources branch,
        // CloseRule.hs:56-137, see line 58): when the raw sources contain
        // partial deconstructions, unfold every rule into its AC-variant
        // rules (`unfoldRuleVariants`), annotate them with AUTO_* actions and
        // add the `AUTO_typing` sources lemma.  HS applies this on EVERY
        // theory close, and the FIRST close runs BEFORE partial evaluation
        // (`closeTheoryWithMaude sign t autoSources True` builds `closedThy`,
        // TheoryLoader.hs:675-683, and `applyPartialEvaluation` consumes it).
        // PE itself reads only the untouched `cprRuleE` half of the closed
        // rules (`getProtoRuleEs`, ClosedTheory.hs:87-89 — kept as `rule_e`
        // on annotated/unfolded rules), so its refined rules come out
        // AUTO-free; the PE branch below then re-applies auto-sources,
        // mirroring the re-close, and it is THAT pass which unfolds and
        // annotates the refined rules.  Auto-sources
        // needs Maude (HS runs it in the `WithMaude` reader), so a missing
        // handle is an error, same as the prove path's.
        if self.auto_sources {
            let m = self.require_maude()?;
            tamarin_theory::auto_sources::apply_auto_sources(
                std::sync::Arc::make_mut(&mut self.elaborated),
                m,
                self.file_maude_pool.clone(),
                self.ndc_cache.as_ref(),
                self.opts.parameters,
            )?;
        }

        // `--partial-evaluation` (HS `closeTranslatedTheory`,
        // TheoryLoader.hs:675-698): `applyPartialEvaluation` (Prover.hs:237-264)
        // runs on the CLOSED theory, between the close and `proveTheory` — it
        // replaces the proto-rules with the abstract interpretation's refined
        // set, splices the abstract-state report in front of them, and
        // re-closes.  Every mode that closes reaches it: a plain load,
        // `--prove` and `--precompute-only` alike.  `--parse-only` never gets
        // here (its branch `continue`d in the file loop, Batch.hs:198-199).
        //
        // The returned string is HS's `Debug.Trace` output.  Those traces are
        // lazy thunks forced while the theory is rendered, so on the oracle
        // they appear on stderr AFTER the `[Theory X] Theory closed` marker —
        // held here and printed at the `closed_marker` sites below.  It stays
        // empty unless the hook runs.
        let mut pe_trace = String::new();
        if let (Some(pe), Some(m)) = (
            self.opts.partial_evaluation.as_ref(),
            self.file_maude.as_ref(),
        ) {
            // TheoryLoader.hs:354-358: `SUMMARY` → `Summary`, `VERBOSE` →
            // `Tracing`.  `Silent` is unreachable from the CLI.
            let style = match pe {
                crate::cli::PartialEval::Summary => tamarin_theory::tools::EvaluationStyle::Summary,
                crate::cli::PartialEval::Verbose => tamarin_theory::tools::EvaluationStyle::Tracing,
            };
            pe_trace = tamarin_theory::tools::apply_partial_evaluation(
                std::sync::Arc::make_mut(&mut self.elaborated),
                m,
                style,
            )
            .map_err(|e| {
                RunError::Regular(format!("partial evaluation of {} failed: {}", in_file, e))
            })?;

            // HS's second `closeTheoryWithMaude` (Prover.hs:237-264, see line 240).  The refined
            // rules come back as fresh open rules with empty `variant_substs`
            // and `loop_breakers`, so both closing passes of the first close
            // are redone here: the variant pass (the re-emitted rules render
            // their `rule (modulo AC)` blocks) and then the loop-breaker
            // annotation (`addSolvingLoopBreakers` over the re-closed items —
            // the oracle renders `// loop breaker:` comments on PE'd theories
            // whose refined dataflow graph is still cyclic, e.g.
            // loops/Minimal_Loop_Example.spthy).  Variants must be populated
            // first: the breaker relation's `instances` iterate each rule's
            // variant substitutions. HS's re-close also reaches
            // `closeProtoRule`, so refined rules whose own variant set is
            // empty must be dropped independently even when several refined
            // items share a name.
            tamarin_theory::tools::rule_variants::reprepare_theory_rules(
                std::sync::Arc::make_mut(&mut self.elaborated),
                m,
                self.file_maude_pool.as_deref(),
            )?;

            // HS's re-close passes `autoSources` again
            // (`applyPartialEvaluation style autoSources`, TheoryLoader.hs:684-688;
            // Prover.hs:238-242), so the REFINED rules are re-probed: their
            // AUTO_* actions are re-derived under the refined names
            // (`AUTO_IN_TERM_…__X___VARIANT_N`), and `addAutoSourcesLemma`'s
            // existing-lemma guard keeps `AUTO_typing` single.
            if self.auto_sources {
                let m2 = self.require_maude()?;
                tamarin_theory::auto_sources::apply_auto_sources(
                    std::sync::Arc::make_mut(&mut self.elaborated),
                    m2,
                    self.file_maude_pool.clone(),
                    self.ndc_cache.as_ref(),
                    self.opts.parameters,
                )?;
            }
        }

        // Decide which lemmas to prove.  Without --prove, HS still runs
        // the close-time `checkAndExtendProver` replay over every stored
        // proof skeleton (`closeTheoryWithMaude`, CloseRule.hs:56-137, see line 71) — a plain
        // load VALIDATES embedded proofs and reports their real status.
        // We mirror that whenever the file carries a stored proof tree;
        // proofless files keep the cheap no-solver path below, whose
        // output is identical either way (every lemma is a 1-step sorry).
        let lemma_filter: &[String] = &self.opts.lemma_names;
        let prove_anything = self.opts.prove_mode;
        let any_stored_proof = self.elaborated.lemmas().any(|l| l.proof.is_some());
        // The modes that skip the prove loop entirely: `--precompute-only`
        // renders stats instead, and a plain load with no stored skeleton to
        // replay has nothing to run.
        let skips_prove_loop =
            self.opts.precompute_only_mode || (!prove_anything && !any_stored_proof);

        let mut results: Vec<LemmaResult> = Vec::new();
        // Mirrors HS's per-lemma proof body for embedding in the
        // pretty-printed theory output.  Filled by the prove loop below.
        let mut proved_lemmas: Vec<tamarin_theory::pretty_theory::ProvedLemma> = Vec::new();
        // HS `systemsWithMetadata` (Batch.hs:274-280) for THIS file: the
        // labelled solved systems `outputTraces` serialises, in lemma
        // declaration order.  Empty unless `--output-dot`/`--output-json`
        // asked for them.
        let mut trace_systems: Vec<(String, System)> = Vec::new();

        if skips_prove_loop {
            results = skipped_results(&self.elaborated, lemma_filter);
            // HS emits the `Theory closed` marker after `closeTheory`
            // finishes (TheoryLoader.hs:668-715, see line 696).  This site
            // covers the no-prove / precompute-only paths, which skip the
            // prove loop; the prove branch below emits it before its loop
            // instead.
            self.closed_marker(&pe_trace);
        } else {
            // Reuse the per-file maude handle.  The `maude tool: ...`
            // banner is printed once at the top of the batch run, matching HS.
            let maude = self.require_maude()?;

            // Per-lemma proof loop.
            //
            // `--bound=N` → HS `apBound = Just N`, which `runAutoProver`
            // (Theory/Proof.hs:730-750#runAutoProver) applies as
            // `boundProofDepth` (Theory/Proof.hs:336-344#boundProofDepth):
            // every proof node at depth N becomes a `sorry /* bound N hit */`
            // leaf.  The bound lives in the AutoProver, so it reaches ONLY
            // lemmas the auto-prover runs on — the `--prove`-selected
            // targets.  Non-target lemmas replay under HS's close-time
            // `checkAndExtendProver (sorryProver Nothing)` (CloseRule.hs:71),
            // which has no AutoProver and hence no bound: they get
            // `usize::MAX` (unbounded, HS `Nothing`).
            let target_bound: usize = self.args.bound.map_or(usize::MAX, |b| b as usize);

            // Each lemma clones the session's cheap template and shares its
            // raw/refined source materialisation.
            let has_target = prove_anything
                && self
                    .elaborated
                    .lemmas()
                    .any(|lemma| lemma_matches(lemma_filter, &lemma.name));
            let cli_heuristic = if has_target {
                self.cli_heuristic()
            } else {
                tamarin_theory::prove::CliHeuristic::default()
            };
            let session = self
                .build_prover_session(maude, cli_heuristic)
                .map_err(RunError::from)?;

            // HS prints "[Theory X] Theory closed" right after `closeTheory`
            // (TheoryLoader.hs:668-715, see line 696) and BEFORE the proof search, which it
            // forces lazily as `provedThy` is serialised — so the marker
            // appears in moments regardless of proving cost.  RS's
            // `ProverSession::build` is the `closeTheory` analog, so emit the
            // marker here (before the prove loop) to match HS's observable
            // stderr order.
            self.closed_marker(&pe_trace);

            let elaborated = &self.elaborated;
            let theory_name = self.elaborated.name.as_str();
            let run_lemma = |l: &tamarin_theory::theory::Lemma| -> Result<
                (
                    tamarin_theory::pretty_theory::ProvedLemma,
                    LemmaResult,
                    Vec<(String, System)>,
                ),
                RunError,
            > {
                let lemma_name = l.name.clone();
                let exists_trace = matches!(
                    l.trace_quantifier,
                    tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                );
                // HS faithfulness: `closeTheory` runs
                // `checkAndExtendProver` (CloseRule.hs:56-137, see line 71) over ALL
                // lemmas, re-attaching the constraint system to each
                // stored skeleton step.  `--prove=X` then runs the
                // auto-prover ONLY on lemmas matching the selector
                // (`proveTheory`, CloseRule.hs:142-163, see line 158); the
                // rest keep their close-time
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
                let outcome = if is_target {
                    tamarin_theory::prove::prove_lemma_in_session(
                        &session,
                        &lemma_name,
                        target_bound,
                    )
                } else {
                    tamarin_theory::prove::check_and_extend_lemma_in_session(
                        &session,
                        &lemma_name,
                        usize::MAX,
                    )
                };
                // HS `systemsWithMetadata` (Batch.hs:274-280) reads the proof
                // tree of every lemma, so the collection has to happen here —
                // the tree is consumed for its solved `System`s once verdict
                // and proof body are rendered.  Both arms above feed it: a
                // stored `SOLVED` proof surfaces through
                // `check_and_extend_lemma_in_session`, which is why
                // `_analyzed` theories carry traces without `--prove`.
                let mut lemma_traces: Vec<(String, System)> = Vec::new();
                let root = outcome.map_err(RunError::from)?;
                let (verdict, proof_steps, proof_body) = {
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
                    let v = lemma_verdict(
                        tamarin_theory::constraint::solver::search::proof_status(&root),
                        exists_trace,
                    );
                    let body = tamarin_theory::pretty_theory::pretty_proof_body(&root);
                    if want_traces {
                        for (path, sys) in
                            tamarin_theory::constraint::solver::search::into_solved_systems(root)
                        {
                            lemma_traces
                                .push((trace_output_label(theory_name, &lemma_name, &path), sys));
                        }
                    }
                    (v, steps, Some(body))
                };
                let pl = tamarin_theory::pretty_theory::ProvedLemma {
                    name: lemma_name.clone(),
                    proof_body,
                };
                let lr = LemmaResult {
                    name: lemma_name,
                    verdict,
                    proof_steps,
                    exists_trace,
                };
                Ok((pl, lr, lemma_traces))
            };

            // Fallible theories stay ordered so an oracle/guarded error cannot
            // be trapped behind other unbounded work. Fully internal,
            // guardable theories retain the indexed parallel fast path; Rayon
            // preserves declaration order when collecting this iterator.
            let lemmas: Vec<_> = elaborated.lemmas().collect();
            let ordered = session.guarded_lemmas_may_fail()
                || lemmas.iter().any(|lemma| {
                    prove_anything
                        && lemma_matches(lemma_filter, &lemma.name)
                        && session.lemma_ranking_may_fail(&lemma.name)
                });
            let lemma_results: Vec<_> = if ordered {
                lemmas
                    .into_iter()
                    .map(run_lemma)
                    .collect::<Result<Vec<_>, RunError>>()?
            } else {
                // Source saturation uses its own pool, so workers can wait on
                // the shared lazy cache without starving its nested work.
                use rayon::prelude::*;
                lemmas
                    .par_iter()
                    .map(|lemma| run_lemma(lemma))
                    .collect::<Result<Vec<_>, RunError>>()?
            };
            for (pl, lr, tr) in lemma_results {
                proved_lemmas.push(pl);
                results.push(lr);
                trace_systems.extend(tr);
            }
        }

        Ok(ClosedOutcome {
            results,
            proved_lemmas,
            trace_systems,
        })
    }
}

fn run_batch(args: &Args) -> Result<i32, RunError> {
    init_rayon_pool(args);
    if args.diff {
        return Err(RunError::Regular(
            "--diff (observational equivalence) is not yet ported to the Rust prover.".to_string(),
        ));
    }
    // `--stop-on-trace` selects HS's `SolutionExtractor` (Theory/Proof.hs:693-694,
    // TheoryLoader.hs:397-405) and, when the CLI flag is absent, HS
    // additionally consults the theory's in-file `configuration:` block
    // (`configStopOnTrace`, TheoryLoader.hs:740-765) — a PER-THEORY value,
    // so the effective strategy is resolved inside the file loop by
    // `effective_cut` once the theory is parsed.

    if args.in_files.is_empty() {
        return Err(RunError::Regular("no input files given".to_string()));
    }
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
    // not during its loop iteration — stash the session and the wf-failure
    // count here and defer the stats computation to match.
    let mut precompute_pending: Vec<(tamarin_theory::prove::ProverSession, usize)> = Vec::new();

    // The maude binary this run invokes is argv-constant, and resolving the
    // default probes the filesystem — resolve it ONCE here and lend it to the
    // version check and to every file's pipeline state.
    let maude_path = maude_invocation_path(args);

    // HS runs `ensureMaudeAndGetVersion` ONCE at the top of the batch run
    // (Batch.hs:97/102/115), before the first theory is loaded: it writes the
    // tool block to stderr and returns the version data every file's
    // `Generated from:` block reports.  `--parse-only` is the one branch that
    // does NOT run it (Batch.hs:91-95), so no probe and no banner there;
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

    let opts: TheoryLoadOptions = mk_theory_load_options(args)?;

    // HS `toParserFlags` (TheoryLoader.hs:285-291): `["diff" | diffMode] ++
    // defines ++ ["quit-on-warning" | quitOnWarning]`.  Structural parity
    // only: the `#ifdef` formula atom is `FAtom <$> try identifier`
    // (Theory/Text/Parser.hs:204-207), which cannot spell a hyphen, so no
    // parseable atom ever matches the "quit-on-warning" element (verified
    // against the oracle: even an explicit `-D=quit-on-warning` activates
    // no `#ifdef quit-on-warning` block).  The `"diff"` element IS
    // matchable upstream (`#ifdef diff`) but unreachable here: the port
    // rejects `--diff` before this point.
    let mut parser_flags: Vec<&str> = opts.defines.iter().map(String::as_str).collect();
    if opts.quit_on_warning {
        parser_flags.push("quit-on-warning");
    }

    // Batch.hs:91-113 guard order: parseOnly > precomputeOnly > outModule >
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
    // (Batch.hs:101-113: `mapM processThy` to completion, then either the
    // `-o`/`-O` writes or `mapM_ (putStrLn . renderDoc)`).
    let mut translate_docs: Vec<String> = Vec::new();

    // The `Generated from:` block's metadata (HS `withVersionAndReport`,
    // TheoryLoader.hs:636-660).  Every field is build- or argv-constant, so
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
                Err(e) => return Ok(report_decode_error(in_file, &e)),
            },
            Err(e) => return Ok(report_open_file_error(in_file, &e)),
        };
        // Thread the including file's directory so `#include "file"` resolves
        // relative to it (HS `takeDirectory inFile0`, Theory/Text/Parser.hs:323-343).
        let base_dir = std::path::Path::new(in_file)
            .parent()
            .map(|p| p.to_path_buf());
        let parsed = match tamarin_parser::parse_theory_with_base(&src, &parser_flags, base_dir) {
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
                // (Batch.hs:189-317, see line 235).  `die` writes `show e` — the raw
                // parsec frame, with `inFile` as the `SourcePos` name — to
                // stderr and exits with code 1.  No `error:` prefix and no
                // `parse error in …:` wrapper (neither of which HS emits).
                eprintln!("{}", e.with_source(in_file.clone()));
                return Ok(1);
            }
        };
        // HS emits this trace marker as soon as the theory parses
        // (TheoryLoader.hs:451).
        let theory_name = parsed.name.clone();
        // HS `[Theory X] …` progress markers land on stderr and are NOT
        // gated by `--quiet` (see `theory_marker`).  `loadTheory`'s `Theory
        // loaded` marker fires in EVERY mode, `--parse-only` included
        // (TheoryLoader.hs:449-452 — Batch.hs's parseOnly branch still calls
        // `loadTheory` via `processThy`); the later translate/close markers
        // are unreachable under `--parse-only` (the branch below `continue`s
        // first).
        theory_marker(&theory_name, "Theory loaded");

        if opts.parse_only_mode {
            // HS-faithful `--parse-only` (Batch.hs:91-95 + TheoryLoader.hs:
            // 443-460): parse, emit the marker above, pretty-print the OPEN
            // theory (`prettyOpenTheory`) — no wellformedness, no
            // configuration-block processing (that happens in `closeTheory`,
            // TheoryLoader.hs:740-765), no Maude, no output files (`-o`/`-O`
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

        // The in-file `configuration:` block, processed as HS `closeTheory`
        // does (TheoryLoader.hs:740-765): `--auto-sources` is OR-combined
        // (`configAutoSources`, TheoryLoader.hs:764-765); the cut strategy
        // follows `configStopOnTrace` precedence ([`effective_cut`]).  A
        // malformed block is a plain error up front (HS defers it through
        // laziness; we don't replicate that choreography — with one
        // boundary kept: only the CLOSE pipeline consumes the block.
        // Translate mode (`-m`) runs HS `translateAndCheckTheory`, which
        // never processes the block at all, so a `-m` run must succeed on
        // a theory whose block would kill a close run (oracle-verified
        // rc 0 with full output).  An unreadable `--stop-on-trace` VALUE
        // is validated whenever `--prove` was given, which is eager-er
        // than HS's laziness in one corner: HS exits 0 when no selected
        // lemma ever forces the value (e.g. a non-matching `--prove=X`);
        // the port reports the bad block anyway.
        let config_block = if translate_module.is_none() {
            parsed
                .configuration
                .as_deref()
                .map(tamarin_theory::prove::parse_config_block)
                .unwrap_or_default()
        } else {
            tamarin_theory::prove::ConfigBlock::default()
        };
        if let Some(msg) = &config_block.flag_error {
            return Err(RunError::Regular(format!("configuration block: {}", msg)));
        }
        let auto_sources = opts.auto_sources || config_block.auto_sources;
        let cut = effective_cut(&opts, &config_block)?;

        // Elaborate (mainly to get the protocol-specific MaudeSig).  This is
        // where the port first builds LNTerms, so an HS-`error`-class defect
        // (`Term.fAppAC: empty argument list`) panics HERE — but GHC, lazy,
        // surfaces the same error only after `Theory translated` plus (unless
        // `--no-ndc`) the NDC marker pair.  Park those pending lines for the
        // panic hook to replay first, keeping the death sequence byte-equal.
        DEFERRED_HS_ERROR_MARKERS.set(Some({
            let mut lines = format!("[Theory {theory_name}] Theory translated\n");
            if opts.ndc_check {
                for suffix in ["started", "ended"] {
                    lines.push_str(&format!(
                        "[Theory {theory_name}] No Deconstruction Chain checks {suffix}\n"
                    ));
                }
            }
            lines
        }));
        let mut elaborated = elaborate_with_in_file(&parsed, in_file).map_err(|e| {
            RunError::Regular(format!("elaboration error in {}: {}", in_file, e.message))
        })?;
        DEFERRED_HS_ERROR_MARKERS.take();

        // Everything downstream of `elaborate` reads the internal theory; the
        // parser AST ends here.
        drop(parsed);
        // HS `addParamsOptions`' `addNdcOption` (TheoryLoader.hs:821-826):
        // `--no-ndc` disables the no-deconstruction-chain check for this theory.
        //
        // HS applies it inside `loadTheory` (TheoryLoader.hs:449-452), which both
        // modes call; the interactive path reaches it through
        // the server load configuration, which writes the same field on every
        // web load.
        if !opts.ndc_check {
            elaborated.options.deduction_chain_check = false;
        }
        // The same `addParamsOptions`' `addLemmaToProve`
        // (TheoryLoader.hs:835-838): the `--prove=X` / `--lemma=X` values
        // become the theory's own
        // `_lemmasToProve`, which `checkIfLemmasInTheory` reads back
        // (Wellformedness.hs:1168).  The interactive path writes the same
        // field through the server load configuration.
        elaborated.options.lemmas_to_prove = opts.lemma_names.clone();
        let maude_sig = elaborated.signature.clone();

        // The per-file pipeline state.  From here the loop follows HS's
        // stage names: `translate_theory` → `check_translated_theory` →
        // (mode split) `close_translated_theory` or the open render.
        let mut st = TheoryPipeline {
            args,
            opts: &opts,
            translate_module,
            elaborated: std::sync::Arc::new(elaborated),
            wf_report: Vec::new(),
            maude_sig,
            cut,
            auto_sources,
            maude_path: &maude_path,
            file_maude: None,
            file_maude_pool: None,
            ndc_cache: None,
            ndc_funs: Vec::new(),
        };

        if let Err(code) = st.translate_theory() {
            return Ok(code);
        }

        st.check_translated_theory()?;

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
        if opts.quit_on_warning && !st.wf_report.is_empty() {
            if translate_module.is_none() {
                st.marker("Theory closed");
            }
            let mut rep = tamarin_theory::pretty_theory::render_wf_error_report(&st.wf_report);
            while rep.ends_with('\n') {
                rep.pop();
            }
            // `putStrLn . renderDoc $ vcat` of: blank, the WARNING header,
            // blank (report non-empty here), the report, blank.
            println!("\nWARNING: the following wellformedness checks failed!\n\n{rep}\n");
            eprintln!("quit-on-warning mode selected - aborting on wellformedness errors.");
            return Ok(1);
        }

        // Per-file summary rows for `file_results`.  Translate mode records
        // skipped rows too, though its output phase never prints a summary.
        let results: Vec<LemmaResult> = match translate_module {
            Some(module) => {
                // HS `translateAndCheckTheory` never closes, never proves
                // and never replays stored skeletons — it skips
                // `closeTranslatedTheory`'s `proveTheory` entirely
                // (TheoryLoader.hs:768-781) — so every lemma is a skipped
                // summary row.
                let results = skipped_results(&st.elaborated, &opts.lemma_names);

                // Translate-only render (`prettyOpenTheoryByModule`,
                // TheoryLoader.hs:783-801, followed by `withVersionAndReport`'s
                // two trailing comment items, TheoryLoader.hs:636-660).  The doc
                // is BUFFERED — Batch.hs:101-113 processes every file before any
                // doc is printed or written.
                //
                // `spthy` and `spthytyped` share `prettyOpenTheory` and differ
                // only in the theory value `translate_theory` left behind;
                // `msr` renders every translation item as empty.
                let wf_block = tamarin_theory::pretty_theory::format_wf_block(&st.wf_report);
                let body = match module {
                    TranslateModule::Msr => {
                        tamarin_theory::pretty_theory::pretty_open_translated_theory_by_module(
                            &st.elaborated,
                            &wf_block,
                            &build_info,
                        )
                    }
                    TranslateModule::Spthy | TranslateModule::SpthyTyped => {
                        tamarin_theory::pretty_theory::pretty_open_theory_by_module(
                            &st.elaborated,
                            &wf_block,
                            &build_info,
                        )
                    }
                };
                translate_docs.push(body);
                results
            }
            None => {
                let closed = st.close_translated_theory()?;

                if opts.precompute_only_mode {
                    // HS `--precompute-only` (Batch.hs:96-100, 201-206): the file's
                    // doc is `ppWf report $--$ prettyPrecomputation thy''` — the
                    // wellformedness WARNING line and a compact 3-line stats
                    // overview — NOT the full closed theory.  The stats need the
                    // closed theory's saturated sources, so build the prover
                    // session (the `closeTheory` analog) here — in-loop, like HS's
                    // eager close — but defer forcing the sources to the print
                    // phase below, where HS's lazy renderDoc forces them.
                    let maude = st.require_maude()?;
                    let session = st
                        .build_prover_session(maude, tamarin_theory::prove::CliHeuristic::default())
                        .map_err(RunError::from)?;
                    let wf_len = st.wf_report.len();
                    precompute_pending.push((session, wf_len));
                } else {
                    // HS `outputTraces` (Batch.hs:224-226) runs in `processThy`'s
                    // close-and-prove `else` — the ONLY branch that reaches it.
                    // `--parse-only` (Batch.hs:198-200), `--precompute-only`
                    // (:202-208) and `-m` (:210-220) all return first, so they leave
                    // the target paths untouched, as does a run with no input files
                    // (`helpAndExit`, Batch.hs:90) and `--diff` (the `bitraverse`
                    // `Right` arm is `pure ()`; RS rejects `--diff` before the loop).
                    // It precedes the theory render, matching HS's force order: the
                    // write is an `IO` action inside `processThy`, while the doc is
                    // rendered later in `Batch.hs`'s output phase.
                    if wants_trace_output(args)
                        && let Err(io) = write_output_traces(args, closed.trace_systems)
                    {
                        return Ok(ghc_exception(&io));
                    }
                    // Build the HS-faithful theory pretty-print body.  This replaces
                    // the verbatim source dump with HS's `prettyClosedTheory`
                    // output shape — re-rendered signature, rules with `(modulo E)`
                    // prefix and AC-variant comments, lemmas with inline guarded
                    // formula and proof body, wellformedness block, and
                    // Generated-from footer.
                    let wf_block = tamarin_theory::pretty_theory::format_wf_block(&st.wf_report);
                    let body = tamarin_theory::pretty_theory::pretty_closed_theory(
                        &st.elaborated,
                        &closed.proved_lemmas,
                        &wf_block,
                        &build_info,
                    );
                    // HS normal mode: `writeOutput` is true whenever `-o`/`-O` was
                    // given (Batch.hs:168), and a `mkOutPath` miss — `-o=` with no
                    // `-O` — `die`s with this exact line (Batch.hs:119-123) instead
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
                        return Ok(ghc_exception(&io));
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
    // `Batch.hs:91-100` before `ppRep` runs, so they skip the `summary of
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
        // HS precompute arm (Batch.hs:96-100): same deferred
        // `mapM_ (putStrLn . renderDoc)` shape as `--parse-only` — all
        // docs to stdout after the file loop, no summary block.  Forcing
        // each file's stats here (traces, then its doc) reproduces HS's
        // renderDoc-time stderr order — see `precompute_pending`.
        for (session, wf_len) in &precompute_pending {
            // The trace is already armed: each file's `close_translated_theory`
            // left it on, matching HS, where this forcing happens inside the
            // same `showSaturation = True` close.
            let stats = session.precomputation_stats().map_err(RunError::from)?;
            // HS `casesInfo` (ClosedTheory.hs:563-570).
            let chain_info = |n: usize| -> String {
                if n == 0 {
                    "deconstructions complete".to_string()
                } else {
                    format!("{n} partial deconstructions left")
                }
            };
            let mut doc = String::new();
            // `ppWf` (Batch.hs:244-247) joined by `$--$`: exactly one blank
            // line between the WARNING and the stats, nothing when the
            // report is empty.  Under `--prove` the vcat gains HS's
            // 9-space-indented "might be wrong!" second line —
            // `proveMode` and `precomputeOnlyMode` are set independently
            // (TheoryLoader.hs:325,381), so the combination is reachable.
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
                if let Err(io) = write_file_with_dirs(out, doc) {
                    return Ok(ghc_exception(&io));
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
/// CloseRule.hs:81, Prover.hs:105, Theory/Constraint/Solver/Sources.hs:362,
/// TheoryObject.hs:759,767).  We mirror that surface via a CLI flag.
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
    // Doc on a worker (HS `parMap rdeepseq ppItem`, TheoryObject.hs:767), and
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
/// file (`writeFileWithDirs`, Main/Utils.hs:20-23) and `putStrLn`s it to stdout
/// (Batch.hs:127-133), and `renderDoc` of a closed theory ends at `end` with
/// no newline.  `body` carries the stdout form (one trailing newline), so the
/// file write drops it — oracle-verified: a v1.13.0 `--output=FILE` run ends
/// the file with the bytes `end`.
///
/// `Err` is the [`write_io_exception`] text for the caller to report through
/// [`ghc_exception`].
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
        // HS `ppRep` (Batch.hs:145-156, see line 148,149) has TWO `Pretty.text ""` between
        // `analyzed:` and the nested `output:`/`processing time:` block, but
        // HughesPJ collapses adjacent empty lines under `vcat`, so the rendered
        // output is a SINGLE blank line here.  Verified against the v1.13.0
        // binary: `tamarin-prover --prove` emits exactly one blank line between
        // `analyzed:` and `output:`/`processing time:`, so one `println!()` is
        // byte-faithful.
        println!();
        if let Some(out) = &fr.out_file {
            // HS aligns `output:` and `processing time:` columns
            // (`ppRep`, Batch.hs:145-156, see line 151,152).
            println!("  output:          {}", out);
        }
        println!("  processing time: {:.2}s", fr.elapsed_ms as f64 / 1000.0);
        println!("  ");
        if fr.wf_count > 0 {
            println!("  WARNING: {} wellformedness check failed!", fr.wf_count);
            // HS Batch.hs:87-316, see line 247 emits this second line only in prove mode:
            //   [ Pretty.text "         The analysis results might be wrong!"
            //   | thyLoadOptions.proveMode ]
            if prove_mode {
                println!("           The analysis results might be wrong!");
            }
            // HS `summary = ppWf report $--$ prettyClosedSummary` (Batch.hs:228-231, see line 229):
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

    /// A scratch path under the system temp dir.  The name of the path holds
    /// the pid of the test binary.  The filesystem tests below assert on the
    /// errnos that the files they seed raise.  Two concurrent runs of this
    /// binary must therefore not share those files.  A second worktree or a
    /// second `cargo test` is such a run.
    fn scratch(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("tamarin_rs_{}_{}", name, std::process::id()))
    }

    #[test]
    fn out_path_for_uses_file_when_set() {
        let a = parse(&["-o=/tmp/foo.spthy", "in.spthy"]);
        assert_eq!(
            out_path_for(&a, "in.spthy").as_deref(),
            Some("/tmp/foo.spthy"),
        );
    }

    #[test]
    fn out_path_for_uses_dir_with_basename_when_set() {
        let a = parse(&["-O=/tmp/outdir", "examples/foo.spthy"]);
        let got = out_path_for(&a, "examples/foo.spthy");
        assert_eq!(got.as_deref(), Some("/tmp/outdir/foo_analyzed.spthy"));
    }

    #[test]
    fn out_path_for_none_means_stdout() {
        let a = parse(&["in.spthy"]);
        assert_eq!(out_path_for(&a, "in.spthy"), None);
        // `-o` with no value records the empty sentinel.  There is no `-O` to
        // derive a name from, so this is the miss case of HS `mkOutPath`.
        // `None` here makes the caller `die` with
        // `Please specify a valid output file/directory` (Batch.hs:119-123).
        // The caller does not fall back to stdout.
        let a = parse(&["-o", "in.spthy"]);
        assert_eq!(a.output_file.as_deref(), Some(""));
        assert_eq!(out_path_for(&a, "in.spthy"), None);
        // `-O` with no value is the other empty sentinel.  It does resolve.
        // HS joins the name with `""` through `</>`, and that leaves a
        // cwd-relative name.
        let a = parse(&["-O", "examples/foo.spthy"]);
        assert_eq!(
            out_path_for(&a, "examples/foo.spthy").as_deref(),
            Some("foo_analyzed.spthy"),
        );
    }

    // The `--stop-on-trace` method table exists three times — the clap
    // `ValueEnum` (cli.rs), `stop_on_trace_cut` here, and the
    // `configuration:`-block reader `parse_stop_on_trace` (tamarin-theory
    // prove.rs) — where HS has one (`stopOnTrace`, TheoryLoader.hs:397-405)
    // serving both argv and the block.  This pin is the coupling: every
    // name the CLI accepts must map to the same `CutStrategy` the block
    // reader gives it, so an arm edited in one table cannot drift silently.
    #[test]
    fn stop_on_trace_cut_agrees_with_the_config_block_reader() {
        for name in ["dfs", "bfs", "seqdfs", "sorry", "none"] {
            let a = parse(&[&format!("--stop-on-trace={name}"), "x.spthy"]);
            let cli = stop_on_trace_cut(a.stop_on_trace.as_ref().expect("parsed"));
            let block = tamarin_theory::prove::parse_stop_on_trace(name)
                .unwrap_or_else(|e| panic!("block reader rejects {name}: {e}"));
            assert_eq!(
                cli, block,
                "CLI and configuration-block tables drifted on {name}"
            );
        }
    }

    // `createDirectoryIfMissing True` blames the level whose `mkdir` raised,
    // not the level it was asked for.  Oracle-verified against the pinned
    // v1.13.0 binary with `-o`:
    //   -o/nonexistentdir/sub/deep/x.spthy
    //     -> /nonexistentdir: createDirectory: permission denied (Permission denied)
    //   -o<regular-file>/sub/x.spthy
    //     -> <regular-file>/sub: createDirectory: inappropriate type (Not a directory)
    // The two rows differ because only ENOENT sends `createDirs` up a level.
    #[test]
    fn create_dirs_blames_the_level_whose_mkdir_failed() {
        // An unwritable root: the deepest reachable ancestor is the blamed one.
        let (dir, e) = create_dirs(std::path::Path::new("/nonexistentdir/sub/deep"))
            .expect_err("/ is not writable in the test environment");
        assert_eq!(dir, std::path::Path::new("/nonexistentdir"));
        assert!(
            matches!(
                e.kind(),
                std::io::ErrorKind::PermissionDenied | std::io::ErrorKind::ReadOnlyFilesystem
            ),
            "unexpected error kind: {:?}",
            e.kind()
        );

        // ENOTDIR is not ENOENT, so the walk stops where it hit — one level
        // BELOW the regular file, not at the file itself.
        let file = scratch("create_dirs_pin");
        fs::write(&file, "").expect("seed a regular file");
        let (dir, e) = create_dirs(&file.join("sub")).expect_err("a file is not a directory");
        assert_eq!(dir, file.join("sub"));
        assert_eq!(e.raw_os_error(), Some(20), "ENOTDIR");

        // The file itself is the blamed level when it IS the target.
        let (dir, e) = create_dirs(&file).expect_err("a file is not a directory");
        assert_eq!(dir, file);
        assert_eq!(e.raw_os_error(), Some(17), "EEXIST");
        assert_eq!(
            write_io_exception(&dir.to_string_lossy(), "createDirectory", &e),
            format!(
                "{}: createDirectory: already exists (File exists)",
                file.display()
            ),
        );
        let _ = fs::remove_file(&file);

        // An existing directory is a no-op, however deep.
        let root = scratch("create_dirs_pin_d");
        create_dirs(&root.join("a/b")).expect("mkdir -p");
        create_dirs(&root.join("a/b")).expect("second pass is a no-op");
        let _ = fs::remove_dir_all(&root);
    }

    // An explicit `--heuristic=` names zero rankings and is the one value
    // clap can't reject for us; a bare `--heuristic` records the default
    // `s` and is fine.
    #[test]
    fn mk_theory_load_options_rejects_empty_heuristic() {
        let a = parse(&["--heuristic=", "x.spthy"]);
        let e = mk_theory_load_options(&a).unwrap_err();
        assert!(
            e.to_string().contains("at least one ranking must be given"),
            "{e}",
        );
        let a = parse(&["--heuristic", "x.spthy"]);
        assert!(mk_theory_load_options(&a).is_ok());
    }

    // GHC renders an `openFile` failure from the errno, bar the directory
    // check it makes itself: `errnoToIOError`'s `IOErrorType` then
    // `strerror`.  Pinned against the oracle's own bytes for the five errnos
    // an input path reaches.
    #[test]
    fn open_file_reasons_follow_errno_to_io_error() {
        let cases = [
            (2, "does not exist (No such file or directory)"),
            (13, "permission denied (Permission denied)"),
            (20, "inappropriate type (Not a directory)"),
            (36, "invalid argument (File name too long)"),
            (40, "invalid argument (Too many levels of symbolic links)"),
        ];
        for (errno, expected) in cases {
            assert_eq!(
                io_exception_reason(&std::io::Error::from_raw_os_error(errno)),
                expected,
                "errno {errno}",
            );
        }
        // An errno outside the table has no `IOErrorType` to name.  The
        // message from Rust therefore stands complete.  It keeps the
        // ` (os error N)` suffix, which a mapped reason strips.  The
        // `ends_with` check makes the equality meaningful.  It shows that the
        // suffix is present and can be dropped.
        let unmapped = std::io::Error::from_raw_os_error(42);
        assert!(unmapped.to_string().ends_with(" (os error 42)"));
        assert_eq!(io_exception_reason(&unmapped), unmapped.to_string());
    }

    #[test]
    fn mk_theory_load_options_accepts_valid_values() {
        let a = parse(&[
            "--partial-evaluation=Verbose",
            "-m=msr",
            "-c=7",
            "-s=3",
            "x.spthy",
        ]);
        let o = mk_theory_load_options(&a).expect("valid values");
        assert_eq!(o.partial_evaluation, Some(crate::cli::PartialEval::Verbose),);
        assert_eq!(o.output_module, Some(ModuleType::Msr));
        // HS `derivDefault = 5` (TheoryLoader.hs:391-393) is resolved into
        // the record; `ndcCheck` defaults on.
        assert_eq!(o.derivation_checks, 5);
        assert!(o.ndc_check);
        assert_eq!(o.parameters.open_chains_limit(), 7);
        assert_eq!(o.parameters.saturation_limit(), 3);
        let a = parse(&["--no-ndc", "-d=0", "x.spthy"]);
        let o = mk_theory_load_options(&a).expect("valid values");
        assert_eq!(o.derivation_checks, 0);
        assert!(!o.ndc_check);
        assert_eq!(o.output_module, None);
        assert_eq!(o.partial_evaluation, None);
    }

    // `run_batch` refuses `--diff` at its top.  It does so before the maude
    // probe and before it opens the input.  The input named here does not
    // exist.  A rejection placed below either of those steps would therefore
    // report the missing input instead.  Below the probe it would report it
    // only as an `Ok(rc)` from `report_open_file_error`.
    #[test]
    fn diff_flag_errors_cleanly() {
        let a = parse(&["--diff", "/nonexistent/in.spthy"]);
        let RunError::Regular(msg) = run(&a).expect_err("--diff must not run") else {
            panic!("expected a regular error");
        };
        assert!(msg.contains("--diff"), "{msg}");
        assert!(msg.contains("not yet ported"), "{msg}");
    }

    #[test]
    fn interactive_invalid_interface_errors() {
        // A request to bind to garbage is an error that names the flag, made
        // without ever opening a socket.  A WORKDIR must be present: without
        // one the mode errors out before it looks at `--interface`.  That is
        // why this test asserts the message, not only that an error occurs.
        let a = parse(&["interactive", "--interface=not-an-ip", "/tmp"]);
        let RunError::Regular(msg) = run(&a).expect_err("expected interface parse error") else {
            panic!("expected a regular error");
        };
        assert!(msg.contains("--interface=\"not-an-ip\""), "{msg}");
        assert!(msg.contains("--interface=\"*4\""), "{msg}");
    }

    #[test]
    fn no_input_files_is_an_error() {
        // clap's `arg_required_else_help` catches a fully-bare argv, but a
        // flags-only argv reaches `run_batch`, which reports it plainly.  The
        // test asserts the complete message.  That equality is the pin.  HS
        // reprints the entire help here, and canonical clap does not.  A help
        // document printed around the phrase would pass a `contains` check.
        let a = parse(&["--quiet"]);
        let e = run(&a).unwrap_err();
        assert_eq!(e.to_string(), "no input files given");
    }

    fn mk_result(verdict: LemmaVerdict, exists_trace: bool, steps: usize) -> LemmaResult {
        LemmaResult {
            name: "L".to_string(),
            verdict,
            proof_steps: steps,
            exists_trace,
        }
    }

    // Pins the per-lemma summary strings to HS `showProofStatus`
    // (Theory/Proof.hs:1105-1112) + the `(N steps)` suffix
    // (ClosedTheory.hs:487-489).  Undetermined/Invalidated render distinct
    // strings, not "analysis incomplete".  The wording for a falsified lemma
    // depends on the quantifier.  That branch is the one branch of this
    // function whose two arms are a plausible copy-paste of each other.
    #[test]
    fn lemma_summary_line_per_proof_status() {
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
        // showProofStatus ExistsNoTrace (TraceFound) = "falsified - found trace"
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Falsified, false, 9)),
            "L (all-traces): falsified - found trace (9 steps)",
        );
        // showProofStatus ExistsSomeTrace (CompleteProof) = "falsified - no
        // trace found".  The summary uses the `exists-trace` quantifier label.
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Falsified, true, 9)),
            "L (exists-trace): falsified - no trace found (9 steps)",
        );
        assert_eq!(
            format_lemma_summary_line(&mk_result(LemmaVerdict::Verified, true, 2)),
            "L (exists-trace): verified (2 steps)",
        );
    }

    // HS `traceLabelOptions` (Batch.hs:305-317) is a CONSTANT in batch mode:
    // `defaultGraphOptions` (SL2 / AS False / CL False / A True / C True,
    // Graph.hs:66-72) and `defaultDotOptions`' `CompactBoringNodes`
    // (Theory/Constraint/System/Dot.hs:84-87) are hard-coded at Batch.hs:254-255.  Pinned against the
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

    // `intercalate "\n" $ map serializeDot labelledSystems` (Batch.hs:265)
    // driven through [`write_output_traces`] itself, so the pin fails when the
    // writer changes rather than when `Vec::join` does: every graph already
    // ends `}\n`, so the separator leaves exactly one blank line between
    // graphs and the document ends `}\n`.  An empty list is
    // `intercalate "\n" [] == ""`, a 0-byte dot file, next to
    // `sequentsToJSONPretty`'s `{"graphs": []}`.  Needs no Maude: an empty
    // `System` renders its preamble and nothing else.
    #[test]
    fn write_output_traces_joins_graphs_the_way_hs_intercalates() {
        use tamarin_theory::constraint::system::System;
        let dir = scratch("write_output_traces");
        fs::create_dir_all(&dir).expect("mkdir");
        let dot = dir.join("t.dot");
        let json = dir.join("t.json");
        let a = parse_args(&[
            format!("--output-dot={}", dot.display()),
            format!("--output-json={}", json.display()),
            "x.spthy".to_string(),
        ])
        .expect("parse");

        write_output_traces(&a, Vec::new()).expect("empty write");
        assert_eq!(fs::read_to_string(&dot).expect("dot file"), "");
        assert_eq!(
            fs::read_to_string(&json).expect("json file"),
            "{\n    \"graphs\": []\n}",
        );

        write_output_traces(
            &a,
            vec![
                ("a".to_string(), System::empty()),
                ("b".to_string(), System::empty()),
            ],
        )
        .expect("two-graph write");
        let body = fs::read_to_string(&dot).expect("dot file");
        assert!(body.starts_with("digraph \"a\" {\n"), "{body}");
        assert_eq!(
            body.matches("}\n\ndigraph \"b\" {\n").count(),
            1,
            "graphs must abut across exactly one blank line:\n{body}",
        );
        assert!(body.ends_with("\n\n}\n"), "{body}");
        // Both labels reach the JSON document too — the writers share the
        // labelled list.
        let json_body = fs::read_to_string(&json).expect("json file");
        assert!(json_body.contains("\"jgLabel\": \"a\","), "{json_body}");
        assert!(json_body.contains("\"jgLabel\": \"b\","), "{json_body}");
        let _ = fs::remove_dir_all(&dir);
    }
}
