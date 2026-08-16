// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Command-line interface for the Rust tamarin-prover port.
//!
//! Parsing is canonical `clap` — deliberately NOT a byte-level emulation of
//! the Haskell binary's `cmdargs` front end.  Flag NAMES and VALUE semantics
//! stay compatible with the Haskell CLI, so existing invocations (and the
//! oracle-pinned differential rows in `tests/fixtures/cli_refs/cases.tsv`,
//! whose argv is fed to BOTH binaries) keep meaning the same thing; parse
//! errors, `--help`, and `--version` are clap's own.  Run OUTPUT byte-parity
//! with the oracle is unaffected — it never depended on the CLI front end.
//!
//! Three `cmdargs` behaviours are kept because dropping them would silently
//! change what an argv MEANS, not just how an error reads:
//!
//! * **`=`-only values** (`require_equals`): every flag HS declares as
//!   `flagOpt` takes its value only via `=` — `--prove file.spthy` proves
//!   everything in `file.spthy`, `--lemma reach f.spthy` filters nothing
//!   and reads TWO input files, `-D A` defines nothing.  This covers
//!   `--prove[=L]`, `--lemma[=L]`, `-D/--defines[=X]`, `-b/--bound[=N]`,
//!   `--heuristic[=R]`, `--stop-on-trace[=M]`, `--partial-evaluation[=S]`,
//!   `-c/-s/-d`, `-o/-O/-m`, `--with-maude/dot/json`, `--oraclename[=F]`,
//!   `--replication-bound[=N]`, and interactive `-p/--port[=N]`,
//!   `-i/--interface=IP`, `--image-format=F`.
//! * **A bare optional-value flag records the Haskell default**, and some of
//!   those defaults are load-bearing: bare `--prove` selects every lemma,
//!   bare `--heuristic` records `s` (which then *overrides* the theory's own
//!   `heuristic:` header for every lemma), bare `-b` bounds at depth 5, bare
//!   `-o` derives the output path from the input, bare `--with-json` switches
//!   the interactive graph pipeline to the `json` command.
//! * **A repeated scalar flag is last-occurrence-wins**
//!   (`args_override_self`, HS `findArg`) — scripts compose flag lists, so
//!   a later `--derivcheck-timeout` must override an earlier one, not
//!   error.  The repeatable flags (`--prove`/`--lemma`/`-D`) append.
//!
//! The flags with no HS `flagOpt` history (`--output-json/--output-dot`,
//! `--processors`, `--maude-processes`, `--data-dir`) take ordinary clap
//! values: `=`, attached, or space-separated.
//!
//! Loader and tool flags are `global`, so they work before or after a
//! subcommand name (HS's interactive mode shares the loader flag set);
//! the interactive web flags are scoped to their command, and the
//! batch-only output flags conflict with every subcommand (clap would
//! otherwise accept `-o=x interactive` and silently drop the `-o` — see
//! [`parse_args`]).  `test-prover` is a hidden alias of `test`.
//!
//! Known loud deltas from HS, deliberate: glued short values (`-b10`,
//! `-DFOO`) are rejected (spell them `-b=10`, `-D=FOO`); numeric flags
//! are range-checked at parse time where HS accepts any `read @Int`
//! result — `-b=-1`/`-b=2^32`, `-d=2^32` (HS: a large timeout), and
//! `-c`/`-s` outside `0..=i64::MAX` (HS wraps out-of-range and honours
//! negatives) are all rc-2 rejections here, never silent truncations;
//! and the unported-feature flags HS still accepts (`--load-json`,
//! `--browser`, `--proverif-no-{source-lemmas,multiset,precise}`) are
//! unknown arguments here, carried over from the pre-clap parser's
//! deliberate omission.
//!
//! The run pipeline consumes the flat [`Args`] struct; [`parse_args`] builds
//! it from the clap tree.  `--quiet`, `--verbose`, `--proverif-no-*`,
//! `--replication-bound`, `--image-format`, `--debug`, `--no-logging`,
//! and `--no-compress` are accepted but have no effect on output, and
//! `--diff` errors at run time (see each field's doc).

use clap::{Args as ClapArgs, Parser, Subcommand as ClapSubcommand, ValueEnum};

/// `--stop-on-trace` methods (HS `SolutionExtractor`; the value names match
/// the Haskell spellings, matched case-insensitively as HS lowercases).
#[derive(Debug, Clone, PartialEq, Eq, ValueEnum)]
pub enum StopOnTrace {
    Dfs,
    Bfs,
    #[value(name = "seqdfs")]
    SeqDfs,
    Sorry,
    None,
}

/// `--partial-evaluation` styles (HS `summary` / `verbose`).
#[derive(Debug, Clone, PartialEq, Eq, ValueEnum)]
pub enum PartialEval {
    Summary,
    Verbose,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Subcommand {
    /// The default batch mode (prove + emit theory).
    #[default]
    Batch,
    /// `interactive` — web UI.
    Interactive,
    /// `variants` — intruder-rule variants.
    Variants,
    /// `test` — self-test.
    Test,
}

/// Image format used for graph rendering in interactive mode.  Accepted for
/// compatibility; rendering currently always produces SVG.
#[derive(Debug, Clone, PartialEq, Eq, ValueEnum)]
pub enum ImageFormat {
    Png,
    Svg,
}

/// Parsed command-line options — the flat contract the run pipeline
/// consumes.  Built from the clap tree by [`parse_args`].
#[derive(Debug, Clone, Default)]
pub struct Args {
    pub subcommand: Subcommand,

    /// Positional `.spthy` files (batch/test) or the workdir/theories
    /// (interactive).
    pub in_files: Vec<String>,

    // Lemma selection.
    /// True iff any `--prove` (with or without value) was passed.
    pub prove_mode: bool,
    /// Names / prefixes from `--prove` or `--lemma`. An empty entry
    /// (e.g. bare `--prove`) means "all lemmas".
    pub lemma_names: Vec<String>,

    // Theory-load options.
    pub stop_on_trace: Option<StopOnTrace>,
    pub bound: Option<u32>,
    pub heuristic: Option<String>,
    pub partial_evaluation: Option<PartialEval>,
    pub defines: Vec<String>,
    pub diff: bool,
    pub quit_on_warning: bool,
    /// `--no-ndc`: deactivate the no-deconstruction-chain (NDC) check
    /// (enabled by default).
    pub no_ndc: bool,
    pub auto_sources: bool,
    pub oracle_name: Option<String>,
    pub oracle_only: bool,
    /// `--quiet`: accepted, but it suppresses nothing the oracle emits — HS
    /// registers the flag and never reads it, so the maude banner, the
    /// `[Theory X] …` markers and the summary block all print regardless.
    /// It gates only Rust-side diagnostics with no oracle counterpart.
    pub quiet: bool,
    pub verbose: bool,
    pub open_chains: Option<u64>,
    pub saturation: Option<u64>,
    pub derivcheck_timeout: Option<u32>,
    pub proverif_no_reuse_lemmas: bool,
    pub proverif_no_restrictions: bool,
    pub replication_bound: Option<u32>,
    pub no_compress: bool,
    pub parse_only: bool,
    pub precompute_only: bool,

    /// `--processors=N` — size of the rayon worker pool used for
    /// HS-faithful internal parallelism (rule-variant closure,
    /// per-source saturate change-detection, per-item pretty-print).
    /// `None` = use default (`available_parallelism()` — full machine).
    /// `Some(1)` = single-threaded, byte-identical to sequential output.
    pub processors: Option<usize>,

    /// `--maude-processes=M` — size of the pool of Maude subprocesses
    /// the rayon workers borrow from at parallel sites.  Each
    /// subprocess costs ~30-100 MB resident.  Default is
    /// `max(1, processors)`; `M=1` forces all workers to share one
    /// Maude (byte-identical to sequential).
    pub maude_processes: Option<usize>,

    // Output options.
    pub output_file: Option<String>,
    pub output_dir: Option<String>,
    pub output_module: Option<String>,
    pub trace_json: Option<String>,
    pub trace_dot: Option<String>,

    // Tool paths.
    pub maude_path: Option<String>,
    pub dot_path: Option<String>,
    pub json_path: Option<String>,

    // Interactive-mode flags.
    /// `-p/--port` (default 3001 when absent or bare).
    pub port: Option<u16>,
    pub interface: Option<String>,
    pub image_format: Option<ImageFormat>,
    pub debug: bool,
    pub no_logging: bool,
    pub data_dir: Option<String>,
}

/// Theory-load flags, shared by batch and interactive (HS's interactive mode
/// includes the same `theoryLoadFlags` set).  All `global`, so they are
/// accepted before or after a subcommand name.
#[derive(Debug, Clone, ClapArgs)]
struct LoadOpts {
    /// Prove the selected lemmas (bare `--prove`: all lemmas; `=NAME` exact,
    /// `=PREFIX*` by prefix; repeatable)
    #[arg(long, global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "", value_name = "LEMMA")]
    prove: Vec<String>,

    /// Restrict what `--prove` proves (`=NAME` exact or `=PREFIX*`;
    /// repeatable)
    #[arg(long, global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "", value_name = "LEMMA")]
    lemma: Vec<String>,

    /// Cut the search when a trace is found (bare flag: dfs)
    #[arg(long = "stop-on-trace", global = true, value_enum, ignore_case = true,
          num_args = 0..=1, require_equals = true, default_missing_value = "dfs",
          value_name = "METHOD")]
    stop_on_trace: Option<StopOnTrace>,

    /// Bound the proof-search depth at N; nodes at that depth become
    /// `sorry /* bound N hit */` (bare flag: 5)
    #[arg(short = 'b', long, global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "5", value_name = "N")]
    bound: Option<u32>,

    /// Goal-ranking sequence; overrides the theory's own heuristic
    /// (bare flag: `s`, the smart ranking)
    #[arg(long, global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "s", value_name = "RANKING")]
    heuristic: Option<String>,

    /// Apply partial evaluation before proving (bare flag: summary)
    #[arg(long = "partial-evaluation", global = true, value_enum, ignore_case = true,
          num_args = 0..=1, require_equals = true, default_missing_value = "summary",
          value_name = "STYLE")]
    partial_evaluation: Option<PartialEval>,

    /// Preprocessor `#define` symbol (`-D=X`; repeatable)
    #[arg(short = 'D', long = "defines", global = true, num_args = 0..=1,
          require_equals = true, default_missing_value = "",
          value_name = "SYMBOL")]
    defines: Vec<String>,

    /// Observational-equivalence mode (not yet ported; errors)
    #[arg(long, global = true)]
    diff: bool,

    /// Abort on wellformedness warnings
    #[arg(long = "quit-on-warning", global = true)]
    quit_on_warning: bool,

    /// Skip the no-deconstruction-chain check
    #[arg(long = "no-ndc", global = true)]
    no_ndc: bool,

    /// Auto-generate sources lemmas for theories with partial deconstructions
    #[arg(long = "auto-sources", global = true)]
    auto_sources: bool,

    /// Oracle script for `--heuristic=o` rankings (bare flag: the default
    /// oracle name resolution)
    #[arg(long = "oraclename", global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "", value_name = "FILE")]
    oracle_name: Option<String>,

    /// Stop when the oracle/tactic ranks no goals
    #[arg(long = "oracle-only", global = true)]
    oracle_only: bool,

    /// Suppress Rust-side diagnostics that have no oracle counterpart
    #[arg(long, global = true)]
    quiet: bool,

    /// Accepted for compatibility (the oracle's verbose trace has no port)
    #[arg(short = 'v', long, global = true)]
    verbose: bool,

    /// Cap on open chain constraints during source precomputation
    /// (bare flag: 10)
    // The `..=i64::MAX` range keeps every accepted value exactly what the
    // solver's i64 limit stores — no value can silently truncate (HS wraps
    // via `read @Int` and honours negatives; out-of-range is rc 2 here,
    // see the module doc's loud-delta list).  Same for `-s` below.
    #[arg(short = 'c', long = "open-chains", global = true, num_args = 0..=1,
          require_equals = true, default_missing_value = "10", value_name = "N",
          value_parser = clap::value_parser!(u64).range(..=i64::MAX as u64))]
    open_chains: Option<u64>,

    /// Cap on source-saturation iterations (bare flag: 5)
    #[arg(short = 's', long, global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "5", value_name = "N",
          value_parser = clap::value_parser!(u64).range(..=i64::MAX as u64))]
    saturation: Option<u64>,

    /// Per-variable message-derivation-check timeout in seconds; 0 disables
    /// (bare flag: 5)
    // Typed `u32` because 0 is the disable sentinel downstream
    // (`TheoryLoadOptions::derivation_checks`): a wider type narrowed later
    // could truncate 2^32 onto the sentinel and silently skip the checks.
    // HS reads a 64-bit Int; oversized values are loud rc-2 here.
    #[arg(short = 'd', long = "derivcheck-timeout", global = true, num_args = 0..=1,
          require_equals = true, default_missing_value = "5", value_name = "SECONDS")]
    derivcheck_timeout: Option<u32>,

    /// Accepted for compatibility (ProVerif export is not ported)
    #[arg(long = "proverif-no-reuse-lemmas", global = true)]
    proverif_no_reuse_lemmas: bool,

    /// Accepted for compatibility (ProVerif export is not ported)
    #[arg(long = "proverif-no-restrictions", global = true)]
    proverif_no_restrictions: bool,

    /// Accepted for compatibility (DeepSec export is not ported;
    /// bare flag: 3)
    #[arg(long = "replication-bound", global = true, num_args = 0..=1,
          require_equals = true, default_missing_value = "3", value_name = "N")]
    replication_bound: Option<u32>,
}

/// External-tool paths and Rust-side parallelism knobs; `global` like the
/// loader flags (every mode probes maude, interactive also renders graphs).
#[derive(Debug, Clone, ClapArgs)]
struct ToolOpts {
    /// Path to the maude binary (bare flag: `maude` on $PATH)
    #[arg(long = "with-maude", global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "maude", value_name = "PATH")]
    maude_path: Option<String>,

    /// GraphViz binary for interactive graph rendering (bare flag: `dot`)
    #[arg(long = "with-dot", global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "dot", value_name = "PATH")]
    dot_path: Option<String>,

    /// Render interactive graphs via `<PATH> <img> <json>` instead of dot
    /// (bare flag: `json`)
    #[arg(long = "with-json", global = true, num_args = 0..=1, require_equals = true,
          default_missing_value = "json", value_name = "PATH")]
    json_path: Option<String>,

    /// Rayon worker-pool size (default: all cores; 1 = sequential output)
    #[arg(long, global = true, value_parser = positive_usize, value_name = "N")]
    processors: Option<usize>,

    /// Maude subprocess-pool size for parallel sites (default: one per
    /// worker)
    #[arg(long = "maude-processes", global = true, value_parser = positive_usize,
          value_name = "N")]
    maude_processes: Option<usize>,
}

/// Batch-only output flags (top-level command only).
#[derive(Debug, Clone, ClapArgs)]
struct BatchOpts {
    /// Accepted for compatibility (HS: uncompressed sequent visualization;
    /// nothing reads it here)
    #[arg(long = "no-compress")]
    no_compress: bool,

    /// Pretty-print the parsed theory and exit (no wellformedness, no
    /// Maude, no proving)
    #[arg(long = "parse-only")]
    parse_only: bool,

    /// Run the source precomputation only and print its statistics
    #[arg(long = "precompute-only")]
    precompute_only: bool,

    /// Write the resulting theory to FILE (bare -o: derive the name from
    /// the input file)
    #[arg(short = 'o', long = "output", num_args = 0..=1, require_equals = true,
          default_missing_value = "", value_name = "FILE")]
    output_file: Option<String>,

    /// Write resulting theories into DIR (bare -O: the current directory)
    #[arg(short = 'O', long = "Output", num_args = 0..=1, require_equals = true,
          default_missing_value = "", value_name = "DIR")]
    output_dir: Option<String>,

    /// Translate-only output module (bare -m: spthy)
    #[arg(short = 'm', long = "output-module", num_args = 0..=1, require_equals = true,
          default_missing_value = "spthy",
          value_parser = ["spthy", "spthytyped", "msr", "proverifequiv",
                          "proverif", "deepsec"],
          value_name = "MODULE")]
    output_module: Option<String>,

    /// Write JSON serializations of every solved constraint system to FILE
    #[arg(long = "output-json", alias = "oj", value_name = "FILE")]
    trace_json: Option<String>,

    /// Write DOT graphs of every solved constraint system to FILE
    #[arg(long = "output-dot", alias = "od", value_name = "FILE")]
    trace_dot: Option<String>,
}

/// `interactive`-only web flags.
#[derive(Debug, Clone, ClapArgs)]
struct InteractiveOpts {
    /// Port to listen on (bare flag or absent: 3001)
    #[arg(short = 'p', long, num_args = 0..=1, require_equals = true,
          default_missing_value = "3001", value_name = "PORT")]
    port: Option<u16>,

    /// Interface to bind: `-i=IP`, or "*"/"*4"/"*6" for all interfaces
    /// (default 127.0.0.1)
    #[arg(short = 'i', long, require_equals = true, value_name = "INTERFACE")]
    interface: Option<String>,

    /// Graph image format (accepted; rendering currently always uses SVG)
    #[arg(
        long = "image-format",
        value_enum,
        ignore_case = true,
        require_equals = true,
        value_name = "FORMAT"
    )]
    image_format: Option<ImageFormat>,

    /// Accepted for compatibility (HS web debug output has no port)
    #[arg(long)]
    debug: bool,

    /// Accepted for compatibility (the port installs no HTTP request
    /// logger to turn off)
    #[arg(long = "no-logging")]
    no_logging: bool,

    /// Directory with the static web assets (default: auto-detected `data/`)
    #[arg(long = "data-dir", value_name = "DIR")]
    data_dir: Option<String>,
}

#[derive(Debug, Parser)]
#[command(
    name = "tamarin-rs",
    version = VERSION,
    long_version = LONG_VERSION,
    about = "Security protocol analysis and verification (Rust port of the Tamarin prover)",
    arg_required_else_help = true,
    // A repeated scalar flag is last-occurrence-wins, matching HS cmdargs
    // (`findArg` reads the head of a prepend-updated list).  Without this,
    // clap hard-errors on duplicates — which would break flag composition
    // like a sweep script appending its own flags after user EXTRA_FLAGS.
    args_override_self = true
)]
struct Cli {
    #[command(subcommand)]
    cmd: Option<Cmd>,

    #[command(flatten)]
    load: LoadOpts,

    #[command(flatten)]
    tools: ToolOpts,

    #[command(flatten)]
    batch: BatchOpts,

    /// `.spthy` theory files to process
    #[arg(value_name = "FILES")]
    files: Vec<String>,
}

#[derive(Debug, ClapSubcommand)]
#[command(args_override_self = true)]
enum Cmd {
    /// Serve the interactive web UI
    Interactive {
        #[command(flatten)]
        web: InteractiveOpts,

        /// Theory files, or a directory of them, to serve
        #[arg(value_name = "WORKDIR")]
        workdir: Vec<String>,
    },

    /// Dump the DH and bilinear-pairing intruder-rule variants
    Variants {
        /// Also write the two variant files under DIR/data/
        #[arg(short = 'O', long = "Output", num_args = 0..=1, require_equals = true,
              default_missing_value = "", value_name = "DIR")]
        output_dir: Option<String>,
    },

    /// Self-test the installation (maude and GraphViz probes)
    #[command(alias = "test-prover")]
    Test {
        /// Accepted for compatibility; ignored
        #[arg(value_name = "FILES")]
        files: Vec<String>,
    },
}

/// Positive-integer parser for `--processors` / `--maude-processes`.
fn positive_usize(s: &str) -> Result<usize, String> {
    let n: usize = s
        .parse()
        .map_err(|_| format!("expected a positive integer, got {s:?}"))?;
    if n == 0 {
        return Err("must be >= 1".to_string());
    }
    Ok(n)
}

/// Parse an argv (without the binary name) into [`Args`].
///
/// The `Err` is clap's — the caller renders it with
/// [`clap::Error::exit`], which also handles `--help`/`--version`
/// (printed to stdout, exit 0).
pub fn parse_args(raw: &[String]) -> Result<Args, clap::Error> {
    let cli =
        Cli::try_parse_from(std::iter::once("tamarin-rs".to_string()).chain(raw.iter().cloned()))?;

    // Batch-only output flags are top-level (not `global`), so clap accepts
    // them BEFORE a subcommand word — and would then silently drop them
    // (the subcommands never read them).  A parsed flag must never be
    // discarded, so reject the combination instead.
    if cli.cmd.is_some() {
        let offending = [
            (cli.batch.no_compress, "--no-compress"),
            (cli.batch.parse_only, "--parse-only"),
            (cli.batch.precompute_only, "--precompute-only"),
            (cli.batch.output_file.is_some(), "-o/--output"),
            (cli.batch.output_dir.is_some(), "-O/--Output"),
            (cli.batch.output_module.is_some(), "-m/--output-module"),
            (cli.batch.trace_json.is_some(), "--output-json"),
            (cli.batch.trace_dot.is_some(), "--output-dot"),
        ]
        .iter()
        .find_map(|(given, name)| given.then_some(*name));
        if let Some(flag) = offending {
            return Err(clap::Error::raw(
                clap::error::ErrorKind::ArgumentConflict,
                format!("{flag} is a batch-mode flag and cannot be used with a subcommand\n"),
            ));
        }
    }

    let mut args = Args {
        prove_mode: !cli.load.prove.is_empty(),
        lemma_names: {
            let mut v = cli.load.prove;
            v.extend(cli.load.lemma);
            v
        },
        stop_on_trace: cli.load.stop_on_trace,
        bound: cli.load.bound,
        heuristic: cli.load.heuristic,
        partial_evaluation: cli.load.partial_evaluation,
        defines: cli.load.defines,
        diff: cli.load.diff,
        quit_on_warning: cli.load.quit_on_warning,
        no_ndc: cli.load.no_ndc,
        auto_sources: cli.load.auto_sources,
        oracle_name: cli.load.oracle_name,
        oracle_only: cli.load.oracle_only,
        quiet: cli.load.quiet,
        verbose: cli.load.verbose,
        open_chains: cli.load.open_chains,
        saturation: cli.load.saturation,
        derivcheck_timeout: cli.load.derivcheck_timeout,
        proverif_no_reuse_lemmas: cli.load.proverif_no_reuse_lemmas,
        proverif_no_restrictions: cli.load.proverif_no_restrictions,
        replication_bound: cli.load.replication_bound,
        no_compress: cli.batch.no_compress,
        parse_only: cli.batch.parse_only,
        precompute_only: cli.batch.precompute_only,
        processors: cli.tools.processors,
        maude_processes: cli.tools.maude_processes,
        output_file: cli.batch.output_file,
        output_dir: cli.batch.output_dir,
        output_module: cli.batch.output_module,
        trace_json: cli.batch.trace_json,
        trace_dot: cli.batch.trace_dot,
        maude_path: cli.tools.maude_path,
        dot_path: cli.tools.dot_path,
        json_path: cli.tools.json_path,
        ..Args::default()
    };

    match cli.cmd {
        None => {
            args.subcommand = Subcommand::Batch;
            args.in_files = cli.files;
        }
        Some(Cmd::Interactive { web, workdir }) => {
            args.subcommand = Subcommand::Interactive;
            args.in_files = workdir;
            args.port = web.port;
            args.interface = web.interface;
            args.image_format = web.image_format;
            args.debug = web.debug;
            args.no_logging = web.no_logging;
            args.data_dir = web.data_dir;
        }
        Some(Cmd::Variants { output_dir }) => {
            args.subcommand = Subcommand::Variants;
            args.output_dir = output_dir;
        }
        Some(Cmd::Test { files }) => {
            args.subcommand = Subcommand::Test;
            args.in_files = files;
        }
    }
    Ok(args)
}

impl Args {
    /// Effective rayon pool size: `--processors`, else full machine.
    pub fn effective_processors(&self) -> usize {
        self.processors.unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        })
    }

    /// Effective Maude subprocess-pool size: `--maude-processes`, else one
    /// per worker (`effective_processors`), forced to 1 when sequential.
    pub fn effective_maude_processes(&self) -> usize {
        let workers = self.effective_processors();
        if workers <= 1 {
            return 1;
        }
        self.maude_processes.unwrap_or(workers).max(1)
    }
}

/// Does the lemma name match the user's `--prove`/`--lemma` filter?
///
/// Mirrors HS `lemmaSelector` (TheoryLoader.hs:418-432): the empty
/// filter `[]`, the single-empty filter `[""]`, and the double-empty
/// filter `["",""]` all mean "all lemmas".  Otherwise we run
/// `any lemmaMatches filter` where a pattern ending in `*` matches by
/// prefix (with the `*` dropped) and any other pattern (including a
/// bare `""`) matches only by exact name.  Note this is NOT "drop all
/// empties": three or more bare entries (e.g. `["","",""]`) fall
/// through to the `any` arm and match nothing, exactly like HS.
pub fn lemma_matches(filter: &[String], lemma_name: &str) -> bool {
    match filter.len() {
        0 => return true,
        1 if filter[0].is_empty() => return true,
        2 if filter[0].is_empty() && filter[1].is_empty() => return true,
        _ => {}
    }
    filter.iter().any(|pat| {
        if let Some(prefix) = pat.strip_suffix('*') {
            lemma_name.starts_with(prefix)
        } else {
            pat == lemma_name
        }
    })
}

// =============================================================================
// Build metadata
// =============================================================================

/// The crate version; also spliced into the `Generated from:` block of
/// emitted theories (`pretty_theory::BuildInfo`).
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Git revision + branch + build timestamp, populated by `build.rs`.
pub const GIT_REV: &str = env!("TAMARIN_GIT_REV");
pub const GIT_BRANCH: &str = env!("TAMARIN_GIT_BRANCH");
pub const BUILD_TIMESTAMP: &str = env!("TAMARIN_BUILD_TIMESTAMP");

/// `--version` detail: version plus the build provenance `build.rs` records.
const LONG_VERSION: &str = concat!(
    env!("CARGO_PKG_VERSION"),
    "\ngit revision ",
    env!("TAMARIN_GIT_REV"),
    " (branch ",
    env!("TAMARIN_GIT_BRANCH"),
    ")\ncompiled at ",
    env!("TAMARIN_BUILD_TIMESTAMP"),
);

#[cfg(test)]
#[path = "cli_tests.rs"]
mod cli_tests;
