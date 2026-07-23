// Currently GPL 3.0 until granted permission by the following authors:
//   kevinmorio, arcz, meiersi, jdreier, addap, Nynko, rkunnema,
//   felixlinker, yavivanov, ValentinYuri, gilcu3, beschmi, Azurios-git,
//   rsasse, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Prover.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Text/Parser/Proof.hs,
//   lib/theory/src/TheoryObject.hs, src/Main/Console.hs,
//   src/Main/Environment.hs, src/Main/Mode/Batch.hs,
//   src/Main/Mode/Interactive.hs, src/Main/TheoryLoader.hs

//! Command-line argument parsing for `tamarin-prover` (Rust port).
//!
//! Mirrors the surface of the Haskell `tamarin-prover` CLI as defined
//! in `src/Main/Console.hs`, `src/Main/Mode/Batch.hs` and
//! `src/Main/TheoryLoader.hs`. We use a small hand-rolled parser
//! rather than pulling in `clap` so the binary stays dependency-light.
//!
//! What we currently support (batch / prove pipeline):
//!
//!   --prove[=LEMMA]            select a lemma (or prefix*) to prove. Repeatable.
//!   --lemma[=LEMMA]            (synonym for --prove without proving — kept for parity)
//!   --stop-on-trace=DFS|BFS|SEQDFS|SORRY|NONE
//!                              trace-search policy (HS SolutionExtractor:
//!                              CutDFS default / CutBFS /
//!                              CutSingleThreadDFS / CutAfterSorry /
//!                              CutNothing), routed in prove-mode; when the
//!                              flag is absent the theory's in-file
//!                              `configuration:` block is consulted
//!                              (run.rs `effective_config`).  Without
//!                              --prove every value parses and is ignored,
//!                              as in HS.
//!   --bound=N, -bN             proof-depth bound
//!   --saturation=N, -sN        saturation iterations (parsed, not yet routed)
//!   --heuristic=...            heuristic ranking sequence (overrides per-lemma)
//!   --partial-evaluation=...   partial-evaluation mode (parsed, not yet routed)
//!   -D|--defines=STRING        preprocessor `#define` flags. Repeatable.
//!   --diff                     observational-equivalence mode (errors: not yet ported)
//!   --quit-on-warning          treat wellformedness warnings as fatal
//!   --auto-sources             auto-generate sources lemmas
//!   --oraclename=FILE          oracle script for --heuristic oracle rankings
//!   --oracle-only              oracle-only mode (quit-on-empty-oracle)
//!   --quiet                    suppress chatter on stderr
//!   --verbose, -v              verbose proof-search output
//!   --parse-only               parse + pretty-print, no analysis
//!   --precompute-only          run precomputation only
//!   --open-chains=N, -cN       open-chain bound (parsed, not yet routed)
//!   --derivcheck-timeout=N -dN message-derivation check timeout
//!   --no-reuse                 do not export reuse lemmas (parsed, not yet routed)
//!   --no-restrictions          do not export restrictions (parsed, not yet routed)
//!   --replication-bound=N      DeepSec replication bound (parsed, not yet routed)
//!   --no-compress              do not compress sequents (parsed, not yet routed)
//!   --output=FILE, -oFILE      write the analyzed theory to FILE
//!   --Output=DIR, -ODIR        write analyzed theory to DIR/<basename>_analyzed.spthy
//!   --output-module=MODULE -mMODULE  output module selector (errors: not yet ported)
//!   --output-json=FILE, --oj   serialize traces to JSON (writes empty stub + warns; not yet ported)
//!   --output-dot=FILE, --od    serialize traces to dot (writes empty stub + warns; not yet ported)
//!   --with-maude=PATH          path to `maude` (default: looked up via PATH)
//!   --with-dot=PATH            path to GraphViz `dot` (parsed, not yet routed)
//!   --with-json=PATH           path to JSON renderer (parsed, not yet routed)
//!   -h|-?|--help               print help and exit
//!   -V|--version               print version and exit
//!
//! Subcommands:
//!
//!   variants      dump the DH/BP intruder-rule variants
//!   test          install self-check (maude + GraphViz `dot` availability)
//!
//! `interactive` subcommand flags (mirrors `Main/Mode/Interactive.hs`):
//!
//!   --port=N, -pN              port to listen on (default 3001)
//!   --interface=ADDR, -iADDR   interface to listen on (default 127.0.0.1)
//!   --image-format=PNG|SVG     image format used for graphs (default SVG)
//!   --debug                    show server debugging output
//!   --no-logging               suppress web server logs
//!   --data-dir=DIR             override path to the bundled `data/` directory
//!
//! The Haskell CLI uses `cmdargs`'s `flagOpt` for almost every value
//! flag, so each accepts a bare `--foo` (which records the flag's
//! documented default) or `--foo=VALUE` / `-fVALUE` — but NOT a
//! space-separated `--foo VALUE` (that next token stays positional,
//! exactly as the HS binary treats `--bound 5 t.spthy` -> `5` is a file).
//! The only exceptions are `--output-json`/`--output-dot`, which are
//! `flagReq` and DO consume the following token (Batch.hs:79-80).

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StopOnTrace {
    Dfs,
    Bfs,
    SeqDfs,
    Sorry,
    None,
}

impl StopOnTrace {
    fn parse(s: &str) -> Result<Self, String> {
        match s.to_ascii_lowercase().as_str() {
            "dfs" => Ok(StopOnTrace::Dfs),
            "bfs" => Ok(StopOnTrace::Bfs),
            "seqdfs" => Ok(StopOnTrace::SeqDfs),
            "sorry" => Ok(StopOnTrace::Sorry),
            "none" => Ok(StopOnTrace::None),
            other => Err(format!("unknown stop-on-trace method: {}", other)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialEval {
    Summary,
    Verbose,
}

impl PartialEval {
    fn parse(s: &str) -> Result<Self, String> {
        match s.to_ascii_lowercase().as_str() {
            "summary" => Ok(PartialEval::Summary),
            "verbose" => Ok(PartialEval::Verbose),
            // Mirror HS TheoryLoader.hs:320: `ArgumentError "partial-evaluation: unknown option"`.
            _ => Err("partial-evaluation: unknown option".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subcommand {
    /// The default batch mode (prove + emit theory).
    Batch,
    /// `interactive` — web UI.
    Interactive,
    /// `variants` — intruder-rule variants.
    Variants,
    /// `test` — self-test.
    Test,
}

/// Image format used for graph rendering in interactive mode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImageFormat {
    Png,
    Svg,
}

impl ImageFormat {
    fn parse(s: &str) -> Result<Self, String> {
        match s.to_ascii_lowercase().as_str() {
            "png" => Ok(ImageFormat::Png),
            "svg" => Ok(ImageFormat::Svg),
            other => Err(format!("image-format must be PNG|SVG (got {:?})", other)),
        }
    }
}

/// Parsed command-line options.
#[derive(Debug, Clone)]
pub struct Args {
    pub subcommand: Subcommand,

    /// Positional `.spthy` files.
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
    pub auto_sources: bool,
    pub oracle_name: Option<String>,
    pub oracle_only: bool,
    pub quiet: bool,
    pub verbose: bool,
    pub open_chains: Option<u64>,
    pub saturation: Option<u64>,
    pub derivcheck_timeout: Option<u64>,
    pub no_reuse: bool,
    pub no_restrictions: bool,
    pub replication_bound: Option<u32>,
    pub no_compress: bool,
    pub parse_only: bool,
    pub precompute_only: bool,

    /// `--processors=N` — size of the rayon worker pool used for
    /// HS-faithful internal parallelism (rule-variant closure,
    /// per-source saturate change-detection, per-item pretty-print).
    /// `None` = use default (`available_parallelism()` — full machine).
    /// `Some(1)` = single-threaded, byte-identical to sequential output.
    /// Mirrors HS's `+RTS -N RTS_FLAG` in spirit — see
    /// `lib/theory/src/Prover.hs:68-164, see line 102,195`, `Theory/Constraint/Solver/Sources.hs:355-384, see line 362`,
    /// `lib/theory/src/TheoryObject.hs:732-768, see line 744,752`.
    pub processors: Option<usize>,

    /// `--maude-processes=M` — size of the pool of Maude subprocesses
    /// the rayon workers borrow from at parallel sites.  Each
    /// subprocess costs ~30-100 MB resident; too many → OOM on small
    /// VMs.  Default is `max(1, processors)` (a 1:1 workers:maudes
    /// ratio; forced to 1 when `--processors=1`), balancing throughput
    /// against memory.  `M=1` forces all workers to share one Maude
    /// (pre-pool behaviour, byte-identical to sequential).  When
    /// `--processors=1` we force `M=1` automatically (no point in a
    /// pool with no parallelism).  HS uses a single Maude per
    /// ClosedTheory — this pool is a Rust-specific implementation
    /// improvement to remove the IPC mutex contention bottleneck.
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

    // Interactive-mode flags (mirror src/Main/Mode/Interactive.hs).
    pub port: Option<u16>,
    pub interface: Option<String>,
    pub image_format: Option<ImageFormat>,
    pub debug: bool,
    pub no_logging: bool,
    pub data_dir: Option<String>,

    // Meta.
    pub show_help: bool,
    pub show_version: bool,
}

impl Default for Args {
    fn default() -> Self {
        Args {
            subcommand: Subcommand::Batch,
            in_files: Vec::new(),
            prove_mode: false,
            lemma_names: Vec::new(),
            stop_on_trace: None,
            bound: None,
            heuristic: None,
            partial_evaluation: None,
            defines: Vec::new(),
            diff: false,
            quit_on_warning: false,
            auto_sources: false,
            oracle_name: None,
            oracle_only: false,
            quiet: false,
            verbose: false,
            open_chains: None,
            saturation: None,
            derivcheck_timeout: None,
            no_reuse: false,
            no_restrictions: false,
            replication_bound: None,
            no_compress: false,
            parse_only: false,
            precompute_only: false,
            processors: None,
            maude_processes: None,
            output_file: None,
            output_dir: None,
            output_module: None,
            trace_json: None,
            trace_dot: None,
            maude_path: None,
            dot_path: None,
            json_path: None,
            port: None,
            interface: None,
            image_format: None,
            debug: false,
            no_logging: false,
            data_dir: None,
            show_help: false,
            show_version: false,
        }
    }
}

#[derive(Debug)]
pub enum CliError {
    /// User-facing message (already formatted).
    Msg(String),
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Msg(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for CliError {}

/// Drop GHC RTS sections from an argv slice, mirroring what the Haskell
/// binary's runtime does before the program sees its arguments
/// (ghc rts/RtsFlags.c `setupRtsFlags`): `+RTS` opens a section and
/// `-RTS` closes one (both removed along with everything between; an
/// unclosed `+RTS` swallows the rest), `--RTS` is removed and everything
/// after it passes through verbatim, and `--` ends RTS processing with
/// itself and the remainder kept.  The RTS flags themselves (e.g. `-N16`)
/// are discarded — core counts are set with `--processors` here.
fn strip_rts_args(raw: &[String]) -> Vec<String> {
    let mut out = Vec::with_capacity(raw.len());
    let mut in_rts = false;
    for (i, a) in raw.iter().enumerate() {
        match a.as_str() {
            "--RTS" => {
                out.extend(raw[i + 1..].iter().cloned());
                break;
            }
            "--" => {
                out.extend(raw[i..].iter().cloned());
                break;
            }
            "+RTS" => in_rts = true,
            "-RTS" => in_rts = false,
            _ if !in_rts => out.push(a.clone()),
            _ => {}
        }
    }
    out
}

/// Parse a raw argv-style slice (program name NOT included).
pub fn parse_args(raw: &[String]) -> Result<Args, CliError> {
    // Strip `+RTS ... -RTS` first so command lines written for the
    // Haskell binary run here unchanged (its RTS removes these before
    // the program ever sees argv).
    let filtered = strip_rts_args(raw);
    let raw = filtered.as_slice();

    let mut args = Args::default();

    // Subcommand detection: if the first non-option token is a known
    // subcommand name, route to it. Otherwise stay in batch mode.
    let mut i = 0;
    if let Some(first) = raw.first() {
        match first.as_str() {
            "interactive" => {
                args.subcommand = Subcommand::Interactive;
                i = 1;
            }
            "variants" => {
                args.subcommand = Subcommand::Variants;
                i = 1;
            }
            "test" | "test-prover" => {
                args.subcommand = Subcommand::Test;
                i = 1;
            }
            _ => {}
        }
    }

    // A few short flags take a separate-token value (`-b N`, `-s N`,
    // `-o FILE`, etc.). We dispatch on full-name so all such cases
    // are explicit.

    let mut positional: Vec<String> = Vec::new();
    while i < raw.len() {
        let a = &raw[i];
        if a == "--" {
            // Everything after is positional.
            for x in &raw[(i + 1)..] {
                positional.push(x.clone());
            }
            break;
        }

        // Long flag.
        if let Some(rest) = a.strip_prefix("--") {
            let (key, val_inline) = split_eq(rest);
            match key {
                "help" => args.show_help = true,
                "version" => args.show_version = true,
                "prove" => {
                    args.prove_mode = true;
                    if let Some(v) = val_inline {
                        args.lemma_names.push(v.to_string());
                    } else {
                        // bare --prove → match-everything sentinel
                        args.lemma_names.push(String::new());
                    }
                }
                "lemma" => {
                    if let Some(v) = val_inline {
                        args.lemma_names.push(v.to_string());
                    } else {
                        args.lemma_names.push(String::new());
                    }
                }
                // flagOpt "dfs" — bare flag records the default "dfs", which
                // equals the Rust default; absent leaves None (same behaviour).
                "stop-on-trace" => {
                    let v = flag_opt(val_inline, "dfs");
                    args.stop_on_trace = Some(StopOnTrace::parse(&v).map_err(CliError::Msg)?);
                }
                // flagOpt "5" (TheoryLoader.hs:105-110).  Load-bearing: HS
                // `proofBound = parseIntArg (findArg "bound") Nothing Just`, so
                // bare `--bound` records the default "5" => Some(5) (bounded
                // search) while an absent `--bound` stays None (unbounded).
                "bound" => {
                    let v = flag_opt(val_inline, "5");
                    args.bound = Some(parse_int(&v, "bound")?);
                }
                "heuristic" => {
                    // flagOpt default = head of defaultRankings False; that
                    // default rebuilds the Rust default downstream, so a bare
                    // flag is behaviourally equal to absent — leave None.
                    // Routed: when set, this OVERRIDES the per-lemma / theory
                    // heuristic for every lemma (HS `selectHeuristic`:
                    // `apDefaultHeuristic <|> pcHeuristic`, Proof.hs:705-716, see line 707).
                    if let Some(v) = val_inline {
                        args.heuristic = Some(v.to_string());
                    }
                }
                "partial-evaluation" => {
                    let v = flag_opt(val_inline, "summary");
                    args.partial_evaluation = Some(PartialEval::parse(&v).map_err(CliError::Msg)?);
                }
                "defines" => {
                    // flagOpt "" — bare `-D`/`--defines` records the empty
                    // string default (a no-op #define), matching HS.
                    args.defines.push(flag_opt(val_inline, ""));
                }
                "diff" => args.diff = true,
                "quit-on-warning" => args.quit_on_warning = true,
                "auto-sources" => args.auto_sources = true,
                "oraclename" => {
                    // Routed: sets the oracle relPath on every oracle ranking
                    // in the `--heuristic` chain (HS `mapOracleRanking
                    // (maybeSetOracleRelPath oraclename)`, TheoryLoader.hs:262-353, see line 305).
                    // `Just "" -> Nothing` is handled at resolution time.
                    args.oracle_name = Some(flag_opt(val_inline, ""));
                }
                // Routed: `--oracle-only` sets quitOnEmpty on every oracle /
                // tactic ranking in the selected heuristic (HS `setQuitOnEmpty`,
                // Proof.hs:712-716).
                "oracle-only" => args.oracle_only = true,
                "quiet" => args.quiet = true,
                "verbose" => args.verbose = true,
                "open-chains" => {
                    let v = flag_opt(val_inline, "10");
                    args.open_chains = Some(parse_int(&v, "open-chains")?);
                }
                "saturation" => {
                    let v = flag_opt(val_inline, "5");
                    args.saturation = Some(parse_int(&v, "saturation")?);
                }
                "derivcheck-timeout" => {
                    let v = flag_opt(val_inline, "5");
                    args.derivcheck_timeout = Some(parse_int(&v, "derivcheck-timeout")?);
                }
                "no-reuse" => args.no_reuse = true,
                "no-restrictions" => args.no_restrictions = true,
                "replication-bound" => {
                    let v = flag_opt(val_inline, "3");
                    args.replication_bound = Some(parse_int(&v, "replication-bound")?);
                }
                "no-compress" => args.no_compress = true,
                "parse-only" => args.parse_only = true,
                "precompute-only" => args.precompute_only = true,
                "processors" => {
                    args.processors =
                        Some(parse_positive_usize(&mut i, raw, val_inline, "processors")?);
                }
                "maude-processes" => {
                    args.maude_processes = Some(parse_positive_usize(
                        &mut i,
                        raw,
                        val_inline,
                        "maude-processes",
                    )?);
                }
                // Output flags.  output / Output / output-module are flagOpt
                // (Batch.hs:76-78): only `=VALUE` or a bare flag (records the
                // default ""/""/"spthy"); they never consume the next token.
                "output" => {
                    args.output_file = Some(flag_opt(val_inline, ""));
                }
                // The long form in Haskell is `--Output` (capital O) for the
                // directory variant (Batch.hs:44-84, see line 77 registers only `Output`/`O`);
                // there is no `--output-dir` alias, so it falls through to the
                // unknown-flag arm, exactly as HS does.
                "Output" => {
                    args.output_dir = Some(flag_opt(val_inline, ""));
                }
                "output-module" => {
                    args.output_module = Some(flag_opt(val_inline, "spthy"));
                }
                // output-json / output-dot are flagReq (Batch.hs:79-80): they
                // REQUIRE a value and DO consume a separate next token.
                "output-json" | "oj" => {
                    let v = take_val(&mut i, raw, val_inline, "output-json")?;
                    args.trace_json = Some(v);
                }
                "output-dot" | "od" => {
                    let v = take_val(&mut i, raw, val_inline, "output-dot")?;
                    args.trace_dot = Some(v);
                }
                // toolFlags are flagOpt (Environment.hs:31-33): defaults
                // maude/dot/json; bare flag records the default, no token.
                "with-maude" => {
                    args.maude_path = Some(flag_opt(val_inline, "maude"));
                }
                "with-dot" => {
                    args.dot_path = Some(flag_opt(val_inline, "dot"));
                }
                "with-json" => {
                    args.json_path = Some(flag_opt(val_inline, "json"));
                }
                // Interactive-mode flags are flagOpt (Interactive.hs:53-56),
                // so they never consume a separate token — only `=VALUE`.  A
                // bare flag records the empty-string default; HS then reads
                // port leniently (Interactive.hs:134-139, falls back to
                // defaultPort) and interface defaults to 127.0.0.1
                // (Interactive.hs:68-166, see line 143), so an empty value behaves like absent.
                "port" => {
                    if let Some(v) = val_inline {
                        if !v.is_empty() {
                            args.port = Some(parse_int(v, "port")?);
                        }
                    }
                }
                "interface" => {
                    args.interface = Some(flag_opt(val_inline, ""));
                }
                "image-format" => {
                    if let Some(v) = val_inline {
                        if !v.is_empty() {
                            args.image_format = Some(ImageFormat::parse(v).map_err(CliError::Msg)?);
                        }
                    }
                }
                "debug" => args.debug = true,
                "no-logging" => args.no_logging = true,
                "data-dir" => {
                    let v = take_val(&mut i, raw, val_inline, "data-dir")?;
                    args.data_dir = Some(v);
                }
                other => {
                    return Err(CliError::Msg(format!("unknown flag: --{}", other)));
                }
            }
            i += 1;
            continue;
        }

        // Short flag(s). cmdargs in Haskell uses single-letter -X aliases.
        if let Some(rest) = a.strip_prefix('-') {
            if rest.is_empty() {
                // bare `-` — treat as positional (stdin convention)
                positional.push(a.clone());
                i += 1;
                continue;
            }
            // GNU-style clustering of boolean short flags, mirroring
            // System.Console.CmdArgs.Explicit (`-vh` sets both verbose
            // and help; HS `verbose`/`help`/`version` are all
            // no-argument `flagNone`/`flagHelpSimple`/`flagVersion`).
            // We walk the cluster char-by-char: a boolean short consumes
            // exactly one char and we continue with the rest; the first
            // value-taking short consumes the remainder of the token as
            // its inline value (e.g. `-b12`, `-vb12`) and ends the cluster.
            // All the value-taking shorts here are cmdargs `flagOpt`, so they
            // do NOT consume the next (space-separated) token; a bare short
            // (`-b`) records the flag's default.  Verified against the HS
            // binary: `-b 5 t.spthy` keeps `5` positional (`5: openFile: does
            // not exist`); `-b5` is inline; bare `-b` uses default 5.
            for (idx, key) in rest.char_indices() {
                // Bytes after this char in the token form a potential
                // inline value for a value-taking flag.  Strip a single
                // leading `=` to keep `-b=12` working.
                let after = &rest[idx + key.len_utf8()..];
                let inline_raw = after.strip_prefix('=').unwrap_or(after);
                let inline: Option<&str> = if inline_raw.is_empty() {
                    None
                } else {
                    Some(inline_raw)
                };
                match key {
                    'h' | '?' => {
                        args.show_help = true;
                        continue;
                    }
                    'V' => {
                        args.show_version = true;
                        continue;
                    }
                    'v' => {
                        args.verbose = true;
                        continue;
                    }
                    'b' => {
                        let v = flag_opt(inline, "5");
                        args.bound = Some(parse_int(&v, "bound")?);
                    }
                    's' => {
                        let v = flag_opt(inline, "5");
                        args.saturation = Some(parse_int(&v, "saturation")?);
                    }
                    'c' => {
                        let v = flag_opt(inline, "10");
                        args.open_chains = Some(parse_int(&v, "open-chains")?);
                    }
                    'd' => {
                        let v = flag_opt(inline, "5");
                        args.derivcheck_timeout = Some(parse_int(&v, "derivcheck-timeout")?);
                    }
                    'D' => {
                        args.defines.push(flag_opt(inline, ""));
                    }
                    'o' => {
                        args.output_file = Some(flag_opt(inline, ""));
                    }
                    'O' => {
                        args.output_dir = Some(flag_opt(inline, ""));
                    }
                    'm' => {
                        args.output_module = Some(flag_opt(inline, "spthy"));
                    }
                    'p' => {
                        if let Some(v) = inline {
                            args.port = Some(parse_int(v, "port")?);
                        }
                    }
                    'i' => {
                        args.interface = Some(flag_opt(inline, ""));
                    }
                    other => {
                        return Err(CliError::Msg(format!("unknown short flag: -{}", other)));
                    }
                }
                // A value-taking flag consumed the remainder of the
                // token (and possibly the next token); stop scanning
                // this cluster.
                break;
            }
            i += 1;
            continue;
        }

        // Positional.
        positional.push(a.clone());
        i += 1;
    }
    args.in_files = positional;

    Ok(args)
}

impl Args {
    /// Resolve `--processors` (or its default).  Default = full
    /// machine parallelism (`available_parallelism()`); Maude IPC mutex
    /// contention is mediated by the `MaudePool` (`--maude-processes`),
    /// so every core can be used.
    pub fn effective_processors(&self) -> usize {
        match self.processors {
            Some(n) => n.max(1),
            None => std::thread::available_parallelism()
                .map(|p| p.get())
                .unwrap_or(1),
        }
    }

    /// Resolve `--maude-processes` (or its default).
    ///
    /// Default = `max(1, effective_processors())` — a 1:1
    /// workers:maudes ratio.  Lemma-level parallelism (B1) plus the
    /// within-lemma fan-out both draw Maude handles from this pool
    /// concurrently, so a half-size pool would be exhausted, forcing the
    /// fan-out to fall back to the single shared subprocess (serialised
    /// IPC).  At 1:1 the
    /// Maude-bound theories keep more queries in flight (gcm ~-8%,
    /// Yubikey ~-12% @16c; output-identical — Maude is stateless so pool
    /// size never affects results).  Costs ~30-100 MB per extra
    /// subprocess on real protocols; tight-RAM users can dial it back
    /// with `--maude-processes=N`.  Going ABOVE `procs` over-subscribes
    /// and regresses (measured), so do not raise the default further.
    ///
    /// When `--processors=1`, force pool size 1 (no parallelism to
    /// exploit; saves spawn cost).
    pub fn effective_maude_processes(&self) -> usize {
        let procs = self.effective_processors();
        if procs == 1 {
            return 1;
        }
        match self.maude_processes {
            Some(n) => n.max(1),
            None => procs.max(1),
        }
    }
}

fn split_eq(s: &str) -> (&str, Option<&str>) {
    match s.find('=') {
        Some(i) => (&s[..i], Some(&s[(i + 1)..])),
        None => (s, None),
    }
}

/// Resolve a `cmdargs` `flagOpt` value: the inline `=VALUE` if present,
/// otherwise the flag's documented default string (recorded when the bare
/// flag is given).  A `flagOpt` flag NEVER consumes a separate following
/// token — that token stays positional.  This mirrors
/// `System.Console.CmdArgs.Explicit.flagOpt`, used by HS for `--bound`,
/// `--output`, `--with-maude`, etc.  Verified against the installed HS
/// binary: `tamarin-prover --bound 5 t.spthy` treats `5` as a positional
/// file (`5: openFile: does not exist`), while bare `--bound` uses default 5.
fn flag_opt(inline: Option<&str>, default: &str) -> String {
    inline.unwrap_or(default).to_string()
}

fn take_val(
    i: &mut usize,
    raw: &[String],
    inline: Option<&str>,
    name: &str,
) -> Result<String, CliError> {
    if let Some(v) = inline {
        return Ok(v.to_string());
    }
    let next = raw
        .get(*i + 1)
        .cloned()
        .ok_or_else(|| CliError::Msg(format!("flag --{} requires a value", name)))?;
    if next.starts_with('-') {
        return Err(CliError::Msg(format!(
            "flag --{} requires a value (got {:?})",
            name, next
        )));
    }
    *i += 1;
    Ok(next)
}

fn parse_int<T: std::str::FromStr>(s: &str, name: &str) -> Result<T, CliError> {
    s.parse::<T>()
        .map_err(|_| CliError::Msg(format!("{}: expected integer, got {:?}", name, s)))
}

/// Take a flag's value, parse it as a `usize`, and reject `0` with a
/// `--<name> must be >= 1` error.  Shared by the `--processors` and
/// `--maude-processes` arms, which are otherwise identical.
fn parse_positive_usize(
    i: &mut usize,
    raw: &[String],
    inline: Option<&str>,
    name: &str,
) -> Result<usize, CliError> {
    let v = take_val(i, raw, inline, name)?;
    let n: usize = parse_int(&v, name)?;
    if n == 0 {
        return Err(CliError::Msg(format!("--{} must be >= 1", name)));
    }
    Ok(n)
}

/// Does the lemma name match the user's `--prove`/`--lemma` filter?
///
/// Mirrors HS `lemmaSelector` (TheoryLoader.hs:378-389): the empty
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
// Help / version text
// =============================================================================

/// The version string the binary prints in response to `--version`.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Git revision + branch + build timestamp, populated by `build.rs`.
pub const GIT_REV: &str = env!("TAMARIN_GIT_REV");
pub const GIT_BRANCH: &str = env!("TAMARIN_GIT_BRANCH");
pub const BUILD_TIMESTAMP: &str = env!("TAMARIN_BUILD_TIMESTAMP");

/// The STDOUT half of `--version` output.  Mirrors HS `--version` handling
/// (Console.hs:326-330): `putStrLn versionStr` emits the banner + license to
/// stdout, and `putStrLn versionMaude` emits the `Generated from:` block
/// returned by `getVersionIO` (Console.hs:87-92) to stdout.  The maude
/// self-check lines (`maude tool:`, ` checking version:`, ` checking
/// installation:`) go to STDERR — see [`version_maude_stderr_text`] — because
/// `ensureMaude` writes them with `hPutStrLn stderr` (Console.hs:151-185, see line 153) and
/// `testProcess` via `putStrErr = hPutStr stderr` (Console.hs:97-149, see line 109,136-137).
///
/// `versionStr` is built with `unlines` (Console.hs:219-220, see line 221), so it ends in `\n`;
/// `putStrLn` then appends a second `\n`, yielding the blank line that
/// precedes `Generated from:`.  We reproduce that blank line here exactly.
/// The reported maude version comes from `getVersionIO`'s argument, which is
/// `ensureMaude`'s `out` (the raw `maude --version` output, Console.hs:156-161).
pub fn version_text() -> String {
    let mv = detect_maude_version_pub().unwrap_or_else(|| "unknown version".to_string());
    format!(
        // versionStr: banner + license (Console.hs:220-231), unlines-terminated,
        // then putStrLn's extra newline gives the blank line before the block.
        "tamarin-prover {VERSION}, (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, 2010-2023\n\
         \n\
         This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you\n\
         are welcome to redistribute it according to its LICENSE, see\n\
         'https://github.com/tamarin-prover/tamarin-prover/blob/master/LICENSE'.\n\
         \n\
         Generated from:\n\
         Tamarin version {VERSION}\n\
         Maude version {mv}\n\
         Git revision: {GIT_REV}, branch: {GIT_BRANCH}\n\
         Compiled at: {BUILD_TIMESTAMP}\n",
    )
}

/// The STDERR half of `--version` output: the three maude self-check lines
/// `ensureMaude` writes via `hPutStrLn stderr` / `testProcess` (Console.hs:
/// 151-165).  ` checking version: ` carries the *maude* version followed by
/// `. OK.` (`Right (strip out ++ ". OK.")`, Console.hs:151-185, see line 165); ` checking
/// installation: ` carries `OK.` (Console.hs:151-185, see line 171).  Returned without a
/// trailing newline so the caller can `eprintln!` it as one block.
pub fn version_maude_stderr_text() -> String {
    let maude_version = detect_maude_version_pub();
    let maude_ok = maude_version.is_some();
    let mv = maude_version.unwrap_or_else(|| "unknown".to_string());
    let ok = if maude_ok { "OK." } else { "FAILED." };
    format!(
        "maude tool: 'maude'\n\
         \x20checking version: {mv}. {ok}\n\
         \x20checking installation: {ok}",
    )
}

/// Probe `maude --version` on `PATH` and return the trimmed version
/// string when Maude is reachable, `None` otherwise.
///
/// Mirrors HS `maudePath = fromMaybe "maude" . findArg "withMaude"`
/// (Console.hs:84-85): when no `--with-maude` is supplied, HS probes the
/// bare `maude` binary on `PATH` — it never consults hardcoded
/// developer-box paths.  Use [`detect_maude_version_at`] to honor an
/// explicit `--with-maude` path.
pub fn detect_maude_version_pub() -> Option<String> {
    detect_maude_version_at("maude")
}

/// Probe `<path> --version` and return the trimmed version string when
/// the binary is reachable, `None` otherwise.  A caller that has an
/// explicit `--with-maude` path can pass it here so the reported version
/// matches the binary the prover will actually invoke (HS `ensureMaude`
/// uses `maudePath`).  No current caller does — the only caller is
/// [`detect_maude_version_pub`], which probes the bare `maude` binary.
pub fn detect_maude_version_at(path: &str) -> Option<String> {
    if let Ok(out) = std::process::Command::new(path).arg("--version").output() {
        if out.status.success() {
            let s = String::from_utf8_lossy(&out.stdout);
            // Maude prints just the version number, e.g. "3.5.1".
            let v = s.trim().to_string();
            if !v.is_empty() {
                return Some(v);
            }
        }
    }
    None
}

pub fn help_text() -> String {
    let mut s = String::new();
    s.push_str("tamarin-prover [COMMAND] ... [OPTIONS] FILES\n");
    s.push_str("  Security protocol analysis and verification (Rust port).\n");
    s.push('\n');
    s.push_str("Commands:\n");
    s.push_str("  interactive  Start a web-server to construct proofs interactively.\n");
    s.push_str("  variants     Compute intruder-rule variants.\n");
    s.push_str("  test         Self-test.\n");
    s.push('\n');
    s.push_str("Interactive-mode flags (used with the `interactive` subcommand):\n");
    s.push_str("  -p --port=PORT                        Port to listen on (default 3001).\n");
    s.push_str(
        "  -i --interface=INTERFACE              Interface to listen on (default 127.0.0.1).\n",
    );
    s.push_str("     --image-format=PNG|SVG             Image format for graphs (default SVG).\n");
    s.push_str("     --debug                            Show server debugging output.\n");
    s.push_str("     --no-logging                       Suppress web server logs.\n");
    s.push_str(
        "     --data-dir=DIR                     Override path to the bundled `data/` dir.\n",
    );
    s.push('\n');
    s.push_str("Lemma selection / proof options:\n");
    s.push_str("     --prove[=LEMMAPREFIX*|LEMMANAME]   Prove the named lemma(s). Repeatable.\n");
    s.push_str("     --lemma[=LEMMAPREFIX*|LEMMANAME]   Restrict to lemma(s) by name/prefix.\n");
    s.push_str("     --stop-on-trace=DFS|BFS|SEQDFS|SORRY|NONE   Trace search policy.\n");
    s.push_str("  -b --bound=INT                        Bound proof depth.\n");
    s.push_str("     --heuristic=...                    Heuristic ranking sequence.\n");
    s.push_str("  -s --saturation=N                     Saturation iterations.\n");
    s.push_str("  -c --open-chains=N                    Open-chain bound.\n");
    s.push_str("  -d --derivcheck-timeout=N             Derivation check timeout.\n");
    s.push_str("     --auto-sources                     Auto-generate sources lemmas.\n");
    s.push_str("     --oraclename=FILE                  Oracle file path.\n");
    s.push_str("     --oracle-only                      Stop if oracle ranks no goals.\n");
    s.push_str("     --partial-evaluation=SUMMARY|VERBOSE   Partial-evaluation mode.\n");
    s.push('\n');
    s.push_str("Parser options:\n");
    s.push_str("  -D --defines=STRING                   Define pseudo-preprocessor flag.\n");
    s.push_str("     --diff                             Diff (observational equivalence) mode.\n");
    s.push_str("     --quit-on-warning                  Treat wellformedness warnings as fatal.\n");
    s.push_str("     --parse-only                       Just parse + pretty-print.\n");
    s.push_str("     --precompute-only                  Just run precomputation.\n");
    s.push_str(
        "     --processors=N                     Rayon worker count for internal parallelism.\n",
    );
    s.push_str("                                        Default: available_parallelism() (full machine).\n");
    s.push_str(
        "                                        N=1 → byte-identical to sequential output.\n",
    );
    s.push_str(
        "     --maude-processes=M                Maude subprocesses in the per-task pool.\n",
    );
    s.push_str(
        "                                        Default: processors (1:1 with the worker pool,\n",
    );
    s.push_str("                                        or 1 when --processors=1).  Each costs\n");
    s.push_str(
        "                                        ~30-100 MB RAM; lower if memory is tight.\n",
    );
    s.push_str(
        "                                        M=1 → single Maude (pre-pool behaviour).\n",
    );
    s.push('\n');
    s.push_str("Output:\n");
    s.push_str("  -o --output=FILE                      Write analyzed theory to FILE.\n");
    s.push_str("  -O --Output=DIR                       Write to DIR/<basename>_analyzed.spthy.\n");
    s.push_str("  -m --output-module=MOD                Output module selector.\n");
    s.push_str("     --output-json=FILE                 Serialize traces to JSON.\n");
    s.push_str("     --output-dot=FILE                  Serialize traces to dot.\n");
    s.push('\n');
    s.push_str("Tools:\n");
    s.push_str("     --with-maude=PATH                  Path to `maude` binary.\n");
    s.push_str("     --with-dot=PATH                    Path to `dot`.\n");
    s.push_str("     --with-json=PATH                   Path to JSON tool.\n");
    s.push('\n');
    s.push_str("Misc:\n");
    s.push_str("     --quiet                            Suppress progress output.\n");
    s.push_str("  -v --verbose                          Verbose proof-search output.\n");
    s.push_str("     --no-reuse                         Do not export reuse lemmas.\n");
    s.push_str("     --no-restrictions                  Do not export restrictions.\n");
    s.push_str("     --replication-bound=N              Replication bound for DeepSec.\n");
    s.push_str("     --no-compress                      Do not compress sequents.\n");
    s.push_str("  -h --help                             Display this help.\n");
    s.push_str("  -V --version                          Print version.\n");
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Args {
        parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
    }

    #[test]
    fn default_is_batch() {
        let a = parse(&[]);
        assert_eq!(a.subcommand, Subcommand::Batch);
        assert!(a.in_files.is_empty());
        assert!(!a.prove_mode);
    }

    #[test]
    fn positional_file() {
        let a = parse(&["foo.spthy", "bar.spthy"]);
        assert_eq!(a.in_files, vec!["foo.spthy", "bar.spthy"]);
    }

    #[test]
    fn prove_with_value() {
        let a = parse(&["--prove=secrecy", "x.spthy"]);
        assert!(a.prove_mode);
        assert_eq!(a.lemma_names, vec!["secrecy".to_string()]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
    }

    #[test]
    fn prove_bare_means_all() {
        let a = parse(&["--prove", "x.spthy"]);
        assert!(a.prove_mode);
        assert_eq!(a.lemma_names, vec!["".to_string()]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
    }

    #[test]
    fn prove_all_is_unknown_flag() {
        // HS has no `--prove-all`; theoryLoadFlags (TheoryLoader.hs:85-193)
        // defines only `prove`/`lemma`.  Verified on the installed HS binary:
        // `tamarin-prover --prove-all t1.spthy` -> `Unknown flag: --prove-all`.
        let r = parse_args(&["--prove-all".to_string(), "x.spthy".to_string()]);
        assert!(r.is_err());
        // Bare `--prove` still sets prove_mode and pushes the match-all sentinel.
        let a = parse(&["--prove", "x.spthy"]);
        assert!(a.prove_mode);
        assert_eq!(a.lemma_names, vec!["".to_string()]);
    }

    #[test]
    fn prove_repeated() {
        let a = parse(&["--prove=foo", "--prove=bar*", "x.spthy"]);
        assert_eq!(a.lemma_names, vec!["foo", "bar*"]);
    }

    #[test]
    fn rts_sections_are_stripped() {
        // GHC removes `+RTS ... -RTS` before the program sees argv
        // (rts/RtsFlags.c), so an HS-style invocation parses the same here.
        let a = parse(&["+RTS", "-N16", "-RTS", "--prove", "x.spthy"]);
        assert!(a.prove_mode);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
        assert_eq!(a.processors, None);
        // Unclosed `+RTS` swallows the rest; a stray `-RTS` is a no-op.
        let a = parse(&["--prove", "x.spthy", "+RTS", "-N4"]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
        let a = parse(&["-RTS", "x.spthy"]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
        // `--RTS` ends RTS processing: the rest passes through verbatim,
        // so a later `+RTS` reaches the parser as a plain positional.
        let a = parse(&["--RTS", "x.spthy", "+RTS"]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string(), "+RTS".to_string()]);
        // `--` also ends RTS processing and is kept for the parser.
        let a = parse(&["+RTS", "-N4", "-RTS", "--", "x.spthy"]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
    }

    #[test]
    fn maude_path_inline() {
        // with-maude is flagOpt (Environment.hs:29-34, see line 33); only `=VALUE` sets it.
        let a = parse(&["--with-maude=/opt/maude/maude"]);
        assert_eq!(a.maude_path.as_deref(), Some("/opt/maude/maude"));
        // A space-separated token is NOT consumed: it stays positional and
        // the flag records its default "maude".  Mirrors HS flagOpt.
        let a = parse(&["--with-maude", "/opt/maude/maude"]);
        assert_eq!(a.maude_path.as_deref(), Some("maude"));
        assert_eq!(a.in_files, vec!["/opt/maude/maude".to_string()]);
    }

    #[test]
    fn output_file_and_dir() {
        // flagOpt inline forms set the value.
        let a = parse(&["-oout.spthy", "input.spthy"]);
        assert_eq!(a.output_file.as_deref(), Some("out.spthy"));
        assert_eq!(a.in_files, vec!["input.spthy".to_string()]);
        let a = parse(&["-Ooutdir", "input.spthy"]);
        assert_eq!(a.output_dir.as_deref(), Some("outdir"));
        let a = parse(&["--output=foo.spthy"]);
        assert_eq!(a.output_file.as_deref(), Some("foo.spthy"));
        let a = parse(&["--Output=bar"]);
        assert_eq!(a.output_dir.as_deref(), Some("bar"));
        // Space-separated `-o out.spthy`: HS keeps `out.spthy` positional
        // (verified: `-o out.spthy t.spthy` -> `out.spthy: openFile: does
        // not exist`) and the flag records its empty default.
        let a = parse(&["-o", "out.spthy", "input.spthy"]);
        assert_eq!(a.output_file.as_deref(), Some(""));
        assert_eq!(
            a.in_files,
            vec!["out.spthy".to_string(), "input.spthy".to_string()]
        );
    }

    #[test]
    fn output_dir_alias_is_unknown_flag() {
        // HS registers only `--Output`/`-O` (Batch.hs:44-84, see line 77); there is no
        // `--output-dir` alias.  Verified on the HS binary:
        // `tamarin-prover --output-dir=foo t.spthy` -> `Unknown flag: --output-dir`.
        assert!(parse_args(&["--output-dir=foo".to_string()]).is_err());
        // `--Output=foo` still sets the directory.
        let a = parse(&["--Output=foo"]);
        assert_eq!(a.output_dir.as_deref(), Some("foo"));
    }

    #[test]
    fn quiet_and_verbose_flags() {
        let a = parse(&["--quiet", "--verbose"]);
        assert!(a.quiet);
        assert!(a.verbose);
    }

    #[test]
    fn bound_inline_short_and_long() {
        // bound is flagOpt "5" (TheoryLoader.hs:105-110): inline forms set it.
        let a = parse(&["-b12"]);
        assert_eq!(a.bound, Some(12));
        let a = parse(&["--bound=99"]);
        assert_eq!(a.bound, Some(99));
    }

    #[test]
    fn bound_space_separated_is_positional() {
        // Load-bearing flagOpt behaviour, verified on the HS binary:
        // `--bound 5 t.spthy` -> `5: openFile: does not exist` (the `5` is a
        // POSITIONAL file, not the bound).  The bare `--bound` records the
        // flagOpt default "5" => Some(5).
        let a = parse(&["--bound", "5", "t.spthy"]);
        assert_eq!(a.bound, Some(5)); // default, not the next token
        assert_eq!(a.in_files, vec!["5".to_string(), "t.spthy".to_string()]);
        // Same for the short form.
        let a = parse(&["-b", "5", "t.spthy"]);
        assert_eq!(a.bound, Some(5));
        assert_eq!(a.in_files, vec!["5".to_string(), "t.spthy".to_string()]);
    }

    #[test]
    fn bound_bare_vs_absent() {
        // HS `proofBound = parseIntArg (findArg "bound") Nothing Just`:
        // absent `--bound` => None (unbounded), bare `--bound` => Some(5)
        // (bounded with the flagOpt default).
        let absent = parse(&["t.spthy"]);
        assert_eq!(absent.bound, None);
        let bare = parse(&["--bound", "t.spthy"]);
        assert_eq!(bare.bound, Some(5));
        assert_eq!(bare.in_files, vec!["t.spthy".to_string()]);
    }

    #[test]
    fn saturation_inline_short_and_long() {
        let a = parse(&["-s7"]);
        assert_eq!(a.saturation, Some(7));
        let a = parse(&["--saturation=4"]);
        assert_eq!(a.saturation, Some(4));
    }

    #[test]
    fn open_chains_inline_short_and_long() {
        let a = parse(&["-c20"]);
        assert_eq!(a.open_chains, Some(20));
        let a = parse(&["--open-chains=11"]);
        assert_eq!(a.open_chains, Some(11));
    }

    #[test]
    fn heuristic_passthrough() {
        let a = parse(&["--heuristic=S"]);
        assert_eq!(a.heuristic.as_deref(), Some("S"));
    }

    #[test]
    fn stop_on_trace_known() {
        let a = parse(&["--stop-on-trace=DFS"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::Dfs));
        let a = parse(&["--stop-on-trace=BFS"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::Bfs));
        let a = parse(&["--stop-on-trace=SeqDFS"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::SeqDfs));
        let a = parse(&["--stop-on-trace=NONE"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::None));
    }

    #[test]
    fn stop_on_trace_unknown_is_err() {
        let r = parse_args(&["--stop-on-trace=banana".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn diff_flag_parsed() {
        let a = parse(&["--diff", "x.spthy"]);
        assert!(a.diff);
    }

    #[test]
    fn quit_on_warning_parsed() {
        let a = parse(&["--quit-on-warning"]);
        assert!(a.quit_on_warning);
    }

    #[test]
    fn defines_repeatable() {
        let a = parse(&["-DFLAG_A", "--defines=FLAG_B"]);
        assert_eq!(a.defines, vec!["FLAG_A", "FLAG_B"]);
    }

    #[test]
    fn parse_only_and_precompute_only() {
        let a = parse(&["--parse-only"]);
        assert!(a.parse_only);
        let a = parse(&["--precompute-only"]);
        assert!(a.precompute_only);
    }

    #[test]
    fn interactive_subcommand_recognised() {
        let a = parse(&["interactive", "x.spthy"]);
        assert_eq!(a.subcommand, Subcommand::Interactive);
    }

    #[test]
    fn variants_subcommand_recognised() {
        let a = parse(&["variants"]);
        assert_eq!(a.subcommand, Subcommand::Variants);
    }

    #[test]
    fn test_subcommand_recognised() {
        let a = parse(&["test"]);
        assert_eq!(a.subcommand, Subcommand::Test);
    }

    #[test]
    fn help_short_and_long() {
        let a = parse(&["--help"]);
        assert!(a.show_help);
        let a = parse(&["-h"]);
        assert!(a.show_help);
        let a = parse(&["-?"]);
        assert!(a.show_help);
    }

    #[test]
    fn version_short_and_long() {
        let a = parse(&["--version"]);
        assert!(a.show_version);
        let a = parse(&["-V"]);
        assert!(a.show_version);
    }

    #[test]
    fn output_module_parsed() {
        // output-module is flagOpt "spthy" (Batch.hs:44-84, see line 78): inline only.
        let a = parse(&["-mmsr"]);
        assert_eq!(a.output_module.as_deref(), Some("msr"));
        let a = parse(&["--output-module=msr"]);
        assert_eq!(a.output_module.as_deref(), Some("msr"));
        // Bare `-m` records the default "spthy".
        let a = parse(&["-m", "x.spthy"]);
        assert_eq!(a.output_module.as_deref(), Some("spthy"));
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
    }

    #[test]
    fn output_dot_and_json_are_flag_req() {
        // output-json/output-dot are flagReq (Batch.hs:79-80): they DO consume
        // the next space-separated token, unlike the flagOpt family.  Verified
        // on the HS binary: `--output-json trace.json t.spthy` writes trace.json.
        let a = parse(&["--output-dot=trace.dot", "--output-json=trace.json"]);
        assert_eq!(a.trace_dot.as_deref(), Some("trace.dot"));
        assert_eq!(a.trace_json.as_deref(), Some("trace.json"));
        let a = parse(&["--output-json", "trace.json", "t.spthy"]);
        assert_eq!(a.trace_json.as_deref(), Some("trace.json"));
        assert_eq!(a.in_files, vec!["t.spthy".to_string()]);
    }

    #[test]
    fn auto_sources_flag_parsed() {
        let a = parse(&["--auto-sources"]);
        assert!(a.auto_sources);
    }

    #[test]
    fn oracle_flags_parsed() {
        let a = parse(&["--oraclename=./my.oracle", "--oracle-only"]);
        assert_eq!(a.oracle_name.as_deref(), Some("./my.oracle"));
        assert!(a.oracle_only);
    }

    #[test]
    fn ddash_routes_to_positional() {
        let a = parse(&["--", "--prove", "weird-name"]);
        assert_eq!(a.in_files, vec!["--prove", "weird-name"]);
        assert!(!a.prove_mode);
    }

    #[test]
    fn unknown_long_flag_is_err() {
        let r = parse_args(&["--nonsense".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn unknown_short_flag_is_err() {
        let r = parse_args(&["-Z".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn lemma_matches_exact() {
        let f = vec!["foo".to_string()];
        assert!(lemma_matches(&f, "foo"));
        assert!(!lemma_matches(&f, "bar"));
    }

    #[test]
    fn lemma_matches_prefix_star() {
        let f = vec!["secrecy*".to_string()];
        assert!(lemma_matches(&f, "secrecy_alice"));
        assert!(lemma_matches(&f, "secrecy"));
        assert!(!lemma_matches(&f, "auth"));
    }

    #[test]
    fn lemma_matches_empty_filter_matches_all() {
        let f: Vec<String> = vec![];
        assert!(lemma_matches(&f, "anything"));
        let f = vec![String::new()];
        assert!(lemma_matches(&f, "anything"));
    }

    #[test]
    fn lemma_matches_any_in_filter() {
        let f = vec!["foo".to_string(), "bar*".to_string()];
        assert!(lemma_matches(&f, "foo"));
        assert!(lemma_matches(&f, "barbaric"));
        assert!(!lemma_matches(&f, "baz"));
    }

    #[test]
    fn lemma_matches_two_empties_match_all() {
        // HS lemmaSelector special-cases `["", ""]` to True.
        let f = vec![String::new(), String::new()];
        assert!(lemma_matches(&f, "anything"));
    }

    #[test]
    fn lemma_matches_three_empties_match_nothing() {
        // HS lemmaSelector only special-cases null/[""]/["",""]; three
        // bare entries fall through to `any lemmaMatches` and an empty
        // pattern only matches a lemma literally named "".
        let f = vec![String::new(), String::new(), String::new()];
        assert!(!lemma_matches(&f, "anything"));
        assert!(lemma_matches(&f, ""));
    }

    #[test]
    fn clustered_boolean_shorts() {
        // GNU-style clustering: `-vh` sets both verbose and help.
        let a = parse(&["-vh"]);
        assert!(a.verbose);
        assert!(a.show_help);
        let a = parse(&["-hV"]);
        assert!(a.show_help);
        assert!(a.show_version);
    }

    #[test]
    fn clustered_bool_then_value_short() {
        // A value-taking short ends the cluster, consuming the rest as
        // its inline value: `-vb12` = verbose + bound 12.
        let a = parse(&["-vb12"]);
        assert!(a.verbose);
        assert_eq!(a.bound, Some(12));
    }

    #[test]
    fn partial_eval_unknown_message() {
        let r = parse_args(&["--partial-evaluation=banana".to_string()]);
        match r {
            Err(CliError::Msg(m)) => {
                assert_eq!(m, "partial-evaluation: unknown option");
            }
            _ => panic!("expected error"),
        }
    }

    #[test]
    fn maude_processes_parsed() {
        let a = parse(&["--maude-processes=3", "x.spthy"]);
        assert_eq!(a.maude_processes, Some(3));
    }

    #[test]
    fn maude_processes_zero_rejected() {
        let r = parse_args(&["--maude-processes=0".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn effective_maude_processes_single_processor_forces_one() {
        let a = parse(&["--processors=1", "--maude-processes=8", "x.spthy"]);
        // When processors=1, pool size collapses to 1 regardless of
        // --maude-processes (no parallelism to exploit).
        assert_eq!(a.effective_maude_processes(), 1);
    }

    #[test]
    fn effective_maude_processes_default_is_one_to_one() {
        let a = parse(&["--processors=8", "x.spthy"]);
        // Default is now 1:1 (= processors) so B1 lemma-level + within-lemma
        // fan-out don't exhaust the pool and fall back to the shared Maude.
        assert_eq!(a.effective_maude_processes(), 8);
    }

    #[test]
    fn effective_maude_processes_explicit_override() {
        let a = parse(&["--processors=8", "--maude-processes=2", "x.spthy"]);
        assert_eq!(a.effective_maude_processes(), 2);
    }

    #[test]
    fn version_stdout_has_blank_line_before_generated_from_and_no_maude_lines() {
        // HS (Console.hs:326-330) puts the banner + license + `Generated from:`
        // block on STDOUT.  `putStrLn versionStr` (versionStr ends with the
        // unlines `\n`) produces a blank line before `Generated from:`.  The
        // maude self-check lines must NOT appear on stdout.  Probed against the
        // installed HS binary: stdout ends `...LICENSE'.\n\nGenerated from:`.
        let out = version_text();
        assert!(
            out.contains("'https://github.com/tamarin-prover/tamarin-prover/blob/master/LICENSE'.\n\nGenerated from:\n"),
            "stdout must have a blank line between the license and `Generated from:`\n--- got ---\n{out}"
        );
        assert!(
            !out.contains("maude tool:"),
            "stdout must NOT contain the maude self-check lines"
        );
        assert!(
            !out.contains("checking version:"),
            "stdout must NOT contain the maude self-check lines"
        );
        assert!(
            !out.contains("checking installation:"),
            "stdout must NOT contain the maude self-check lines"
        );
        // The banner is the first line.
        assert!(out.starts_with("tamarin-prover "));
        // getVersionIO's block is present and ends with the compile-time line.
        assert!(out.contains("\nTamarin version "));
        assert!(out.contains("\nMaude version "));
        assert!(out.contains("\nCompiled at: "));
    }

    #[test]
    fn version_stderr_has_the_three_maude_self_check_lines() {
        // HS `ensureMaude` writes these to STDERR via `hPutStrLn stderr` /
        // `testProcess` (Console.hs:151-165).  Probed against the HS binary,
        // stderr is exactly:
        //   maude tool: 'maude'
        //    checking version: 3.5.1. OK.
        //    checking installation: OK.
        let err = version_maude_stderr_text();
        let lines: Vec<&str> = err.lines().collect();
        assert_eq!(
            lines.len(),
            3,
            "stderr block must be exactly three lines: {err:?}"
        );
        assert_eq!(lines[0], "maude tool: 'maude'");
        assert!(
            lines[1].starts_with(" checking version: "),
            "got {:?}",
            lines[1]
        );
        assert!(
            lines[1].ends_with(". OK.") || lines[1].ends_with(". FAILED."),
            "got {:?}",
            lines[1]
        );
        assert!(
            lines[2] == " checking installation: OK."
                || lines[2] == " checking installation: FAILED."
        );
    }
}
