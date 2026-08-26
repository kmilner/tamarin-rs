// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Tests for the clap CLI.
//!
//! The parser is canonical clap, so these tests cover only what is OURS to
//! get wrong: the flag inventory, the kept `cmdargs` semantics (`=`-only
//! values, bare-flag Haskell defaults, last-wins duplicates — see the
//! module doc in `cli.rs`), the batch-flag/subcommand conflict, the
//! clap-tree → [`Args`] flattening, and the pure helpers
//! ([`lemma_matches`], the pool-size arithmetic).  Rendering of parse
//! errors, help, and version is clap's and is not asserted on.

use super::*;

fn parse(args: &[&str]) -> Args {
    parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
}

fn parse_err(args: &[&str]) -> clap::Error {
    parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect_err("parse error")
}

// =========================================================================
// Mode selection
// =========================================================================

#[test]
fn default_is_batch() {
    let a = parse(&["foo.spthy"]);
    assert_eq!(a.subcommand, Subcommand::Batch);
    assert_eq!(a.in_files, vec!["foo.spthy"]);
    assert!(!a.prove_mode);
}

#[test]
fn no_args_shows_help() {
    // `arg_required_else_help`: a bare `tamarin-rs` prints usage rather
    // than silently doing nothing.
    let e = parse_err(&[]);
    assert_eq!(
        e.kind(),
        clap::error::ErrorKind::DisplayHelpOnMissingArgumentOrSubcommand
    );
}

#[test]
fn positional_files() {
    let a = parse(&["foo.spthy", "bar.spthy"]);
    assert_eq!(a.in_files, vec!["foo.spthy", "bar.spthy"]);
}

#[test]
fn interactive_subcommand_recognised() {
    let a = parse(&["interactive", "."]);
    assert_eq!(a.subcommand, Subcommand::Interactive);
    assert_eq!(a.in_files, vec!["."]);
}

#[test]
fn variants_subcommand_recognised() {
    let a = parse(&["variants"]);
    assert_eq!(a.subcommand, Subcommand::Variants);
    let a = parse(&["variants", "-O=out"]);
    assert_eq!(a.output_dir.as_deref(), Some("out"));
}

#[test]
fn test_subcommand_and_its_haskell_alias() {
    assert_eq!(parse(&["test"]).subcommand, Subcommand::Test);
    // The HS binary spells it `test-prover`; kept as a hidden alias.
    assert_eq!(parse(&["test-prover"]).subcommand, Subcommand::Test);
}

#[test]
fn loader_flags_are_global_across_subcommands() {
    // The loader/tool flags work before or after a subcommand name (HS's
    // interactive mode shares the loader flag set).
    let a = parse(&["-b=10", "interactive", "."]);
    assert_eq!(a.subcommand, Subcommand::Interactive);
    assert_eq!(a.bound, Some(10));
    let a = parse(&["interactive", "--heuristic=C", "--with-maude=/x/maude", "."]);
    assert_eq!(a.heuristic.as_deref(), Some("C"));
    assert_eq!(a.maude_path.as_deref(), Some("/x/maude"));
}

#[test]
fn batch_output_flags_are_not_valid_in_interactive_mode() {
    // Batch-only output flags are scoped to the top-level command, not
    // global: `interactive` rejects them.
    let e = parse_err(&["interactive", "-o=out.spthy", "."]);
    assert_eq!(e.kind(), clap::error::ErrorKind::UnknownArgument);
}

#[test]
fn batch_output_flags_before_a_subcommand_conflict() {
    // Top-level batch flags are also rejected BEFORE a subcommand word —
    // clap would otherwise parse them and silently drop them (no
    // subcommand reads them), and a parsed flag must never be discarded.
    // There is one row here per entry of the offending-flag table in
    // `parse_args`.  If an entry is absent from that table, clap drops the
    // flag on that row silently, and the row here catches it.
    for (argv, named) in [
        (&["-o=x", "interactive", "."][..], "-o/--output"),
        (&["-O=x", "variants"][..], "-O/--Output"),
        (&["-m=msr", "test"][..], "-m/--output-module"),
        (&["--parse-only", "test"][..], "--parse-only"),
        (&["--precompute-only", "variants"][..], "--precompute-only"),
        (&["--no-compress", "interactive", "."][..], "--no-compress"),
        (
            &["--output-json=t.json", "interactive", "."][..],
            "--output-json",
        ),
        (&["--output-dot=t.dot", "variants"][..], "--output-dot"),
    ] {
        let e = parse_err(argv);
        assert_eq!(
            e.kind(),
            clap::error::ErrorKind::ArgumentConflict,
            "{argv:?}"
        );
        // The message names the flag that conflicted.  The second column of
        // the table is all that the user can act on.
        assert!(e.to_string().contains(named), "{argv:?}: {e}");
    }
    // The `variants` subcommand's OWN `-O` is fine — it is read.
    assert_eq!(
        parse(&["variants", "-O=out"]).output_dir.as_deref(),
        Some("out")
    );
}

#[test]
fn repeated_scalar_flags_are_last_wins() {
    // HS cmdargs is last-occurrence-wins for scalar flags (`findArg`
    // reads the head of a prepend-updated list); `args_override_self`
    // mirrors that.  The repeatable flags (`--prove`/`--lemma`/`-D`)
    // keep every occurrence, `--prove`/`--lemma` in the reverse order
    // `findArg` reads them off the prepend-built list.
    let a = parse(&["-b=5", "-b=7", "x.spthy"]);
    assert_eq!(a.bound, Some(7));
    let a = parse(&["--heuristic=s", "--heuristic=C", "x.spthy"]);
    assert_eq!(a.heuristic.as_deref(), Some("C"));
    let a = parse(&["--prove=a", "-m=spthy", "-m=msr", "--prove=b", "x.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some("msr"));
    assert_eq!(a.lemma_names, vec!["b", "a"]);
}

#[test]
fn hs_flags_the_port_deliberately_rejects() {
    // HS accepts these five as flags of unported features; the port
    // rejects them outright rather than accepting-and-ignoring, so a user
    // relying on `--load-json` or the ProVerif fine-tuning knobs finds
    // out loudly.  (Deliberate omission carried over from the pre-clap
    // parser, which also answered `Unknown flag` for each.)
    for argv in [
        &["--proverif-no-source-lemmas", "x.spthy"][..],
        &["--proverif-no-multiset", "x.spthy"][..],
        &["--proverif-no-precise", "x.spthy"][..],
        &["interactive", "--load-json=x", "."][..],
        &["interactive", "--browser", "."][..],
    ] {
        let e = parse_err(argv);
        assert_eq!(
            e.kind(),
            clap::error::ErrorKind::UnknownArgument,
            "{argv:?}"
        );
    }
}

// =========================================================================
// Lemma selection
// =========================================================================

#[test]
fn prove_with_value() {
    let a = parse(&["--prove=secrecy", "x.spthy"]);
    assert!(a.prove_mode);
    assert_eq!(a.lemma_names, vec!["secrecy".to_string()]);
    assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
}

#[test]
fn prove_bare_means_all() {
    // THE load-bearing kept semantic (`require_equals`): `--prove
    // file.spthy` proves everything in `file.spthy` — the path must not be
    // swallowed as a lemma selector.
    let a = parse(&["--prove", "x.spthy"]);
    assert!(a.prove_mode);
    assert_eq!(a.lemma_names, vec!["".to_string()]);
    assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
}

#[test]
fn prove_repeated() {
    // `findArg "prove"` reads one flag's values off the prepend-built
    // `Arguments` list, so they arrive in reverse command-line order.
    let a = parse(&["--prove=foo", "--prove=bar*", "x.spthy"]);
    assert_eq!(a.lemma_names, vec!["bar*", "foo"]);
}

#[test]
fn lemma_flag_appends_after_prove_names() {
    // `lemma_names` is HS `findArg "prove" as ++ findArg "lemma" as`, so
    // the `--prove` values come first; `--lemma` alone does not set
    // prove_mode (it only restricts what `--prove` proves).
    let a = parse(&["--prove=a", "--lemma=b", "x.spthy"]);
    assert!(a.prove_mode);
    assert_eq!(a.lemma_names, vec!["a", "b"]);
    let a = parse(&[
        "--prove=p1",
        "--lemma=l1",
        "--prove=p2",
        "--lemma=l2",
        "x.spthy",
    ]);
    assert_eq!(a.lemma_names, vec!["p2", "p1", "l2", "l1"]);
    let a = parse(&["--lemma=b", "x.spthy"]);
    assert!(!a.prove_mode);
    assert_eq!(a.lemma_names, vec!["b"]);
}

#[test]
fn lemma_never_consumes_the_next_token() {
    // `--lemma` is HS cmdargs `flagOpt ""` (TheoryLoader.hs), NOT a
    // required-value flag: `--lemma reach f.spthy` means bare `--lemma`
    // (an empty filter entry) plus TWO input files — the oracle tries to
    // open `reach` as a theory.  Eating `reach` as the value would
    // silently change what the argv means to the two binaries a
    // cases.tsv row feeds.
    let a = parse(&["--lemma", "reach", "x.spthy"]);
    assert_eq!(a.lemma_names, vec![""]);
    assert_eq!(a.in_files, vec!["reach", "x.spthy"]);
}

// =========================================================================
// Optional-value flags: `=` only, bare records the Haskell default
// =========================================================================

#[test]
fn bound_inline_short_and_long() {
    assert_eq!(parse(&["-b=12", "x.spthy"]).bound, Some(12));
    assert_eq!(parse(&["--bound=12", "x.spthy"]).bound, Some(12));
}

#[test]
fn bound_space_separated_is_positional() {
    // `-b 10` is a bare `-b` (default 5) followed by a positional `10` —
    // matching HS, where flagOpt values attach only via `=`.
    let a = parse(&["-b", "10", "x.spthy"]);
    assert_eq!(a.bound, Some(5));
    assert_eq!(a.in_files, vec!["10", "x.spthy"]);
}

#[test]
fn bound_bare_vs_absent() {
    assert_eq!(parse(&["-b", "x.spthy"]).bound, Some(5));
    assert_eq!(parse(&["x.spthy"]).bound, None);
}

#[test]
fn heuristic_bare_vs_absent() {
    // Bare `--heuristic` records `s` — which then OVERRIDES the theory's
    // own `heuristic:` header, unlike an absent flag.
    assert_eq!(
        parse(&["--heuristic", "x.spthy"]).heuristic.as_deref(),
        Some("s")
    );
    assert_eq!(parse(&["x.spthy"]).heuristic, None);
    assert_eq!(
        parse(&["--heuristic=ssC", "x.spthy"]).heuristic.as_deref(),
        Some("ssC")
    );
}

#[test]
fn saturation_and_open_chains_inline_short_and_long() {
    assert_eq!(parse(&["-s=3", "x.spthy"]).saturation, Some(3));
    assert_eq!(parse(&["--saturation=3", "x.spthy"]).saturation, Some(3));
    assert_eq!(parse(&["-c=7", "x.spthy"]).open_chains, Some(7));
    assert_eq!(parse(&["--open-chains=7", "x.spthy"]).open_chains, Some(7));
    // Bare flags record the HS defaults (10 chains, 5 iterations).
    assert_eq!(parse(&["-c", "x.spthy"]).open_chains, Some(10));
    assert_eq!(parse(&["-s", "x.spthy"]).saturation, Some(5));
}

#[test]
fn derivcheck_timeout_zero_disables_and_bare_is_five() {
    assert_eq!(parse(&["-d=0", "x.spthy"]).derivcheck_timeout, Some(0));
    assert_eq!(parse(&["-d", "x.spthy"]).derivcheck_timeout, Some(5));
    assert_eq!(
        parse(&["--derivcheck-timeout=30", "x.spthy"]).derivcheck_timeout,
        Some(30)
    );
}

// The numeric-tightening deltas from the module doc: values HS's
// `read @Int` would wrap or accept as huge are LOUD rc-2 rejections here,
// never silent truncations.  `-d=2^32` would otherwise wrap onto the
// 0-disables sentinel and skip the derivation checks; `-c`/`-s` past
// i64::MAX would wrap negative and be dropped by the solver's `>= 0`
// override guard.
#[test]
fn oversized_numeric_values_are_rejected_loudly() {
    for argv in [
        ["-d=4294967296", "x.spthy"],
        ["-c=9223372036854775808", "x.spthy"],
        ["-s=9223372036854775808", "x.spthy"],
        ["-c=-1", "x.spthy"],
        ["-b=4294967296", "x.spthy"],
        ["-b=-1", "x.spthy"],
        // A value that is not a number at all takes the same rejection path.
        ["-b=not-a-number", "x.spthy"],
    ] {
        let e = parse_err(&argv);
        assert_eq!(
            e.kind(),
            clap::error::ErrorKind::ValueValidation,
            "{argv:?}: {e}"
        );
    }
    // The largest accepted values sit exactly on the type bounds.
    assert_eq!(
        parse(&["-d=4294967295", "x.spthy"]).derivcheck_timeout,
        Some(u32::MAX)
    );
    assert_eq!(parse(&["-b=4294967295", "x.spthy"]).bound, Some(u32::MAX));
    assert_eq!(
        parse(&["-c=9223372036854775807", "x.spthy"]).open_chains,
        Some(i64::MAX as u64)
    );
}

#[test]
fn output_file_and_dir() {
    // Bare `-o` derives the output name from the input (empty sentinel);
    // bare `-O` means the current directory (empty sentinel).
    assert_eq!(
        parse(&["-o=out.spthy", "x.spthy"]).output_file.as_deref(),
        Some("out.spthy")
    );
    assert_eq!(parse(&["-o", "x.spthy"]).output_file.as_deref(), Some(""));
    assert_eq!(
        parse(&["--output=out.spthy", "x.spthy"])
            .output_file
            .as_deref(),
        Some("out.spthy")
    );
    assert_eq!(
        parse(&["-O=dir", "x.spthy"]).output_dir.as_deref(),
        Some("dir")
    );
    assert_eq!(parse(&["-O", "x.spthy"]).output_dir.as_deref(), Some(""));
    assert_eq!(
        parse(&["--Output=dir", "x.spthy"]).output_dir.as_deref(),
        Some("dir")
    );
    assert_eq!(parse(&["x.spthy"]).output_file, None);
}

#[test]
fn output_dir_alias_is_unknown_flag() {
    // The directory flag is `-O`/`--Output` (HS spelling); there is no
    // `--output-dir` (that name would collide with `--output-dot`'s
    // prefix family in HS).
    let e = parse_err(&["--output-dir=x", "t.spthy"]);
    assert_eq!(e.kind(), clap::error::ErrorKind::UnknownArgument);
}

#[test]
fn with_tool_paths_bare_defaults() {
    assert_eq!(
        parse(&["--with-maude=/opt/maude", "x.spthy"])
            .maude_path
            .as_deref(),
        Some("/opt/maude")
    );
    assert_eq!(
        parse(&["--with-maude", "x.spthy"]).maude_path.as_deref(),
        Some("maude")
    );
    assert_eq!(parse(&["x.spthy"]).maude_path, None);
    assert_eq!(
        parse(&["--with-dot", "x.spthy"]).dot_path.as_deref(),
        Some("dot")
    );
    assert_eq!(
        parse(&["--with-json", "x.spthy"]).json_path.as_deref(),
        Some("json")
    );
}

#[test]
fn oracle_flags_parsed() {
    let a = parse(&["--oraclename=my.py", "--oracle-only", "x.spthy"]);
    assert_eq!(a.oracle_name.as_deref(), Some("my.py"));
    assert!(a.oracle_only);
    // Bare `--oraclename` falls back to the default oracle resolution.
    assert_eq!(
        parse(&["--oraclename", "x.spthy"]).oracle_name.as_deref(),
        Some("")
    );
}

#[test]
fn replication_bound_bare_is_three() {
    // Accepted-but-inert (DeepSec export is not ported); the HS bare
    // default is still recorded faithfully.
    assert_eq!(
        parse(&["--replication-bound=7", "x.spthy"]).replication_bound,
        Some(7)
    );
    assert_eq!(
        parse(&["--replication-bound", "x.spthy"]).replication_bound,
        Some(3)
    );
}

// =========================================================================
// Value-enum flags
// =========================================================================

#[test]
fn stop_on_trace_known() {
    assert_eq!(
        parse(&["--stop-on-trace=dfs", "x.spthy"]).stop_on_trace,
        Some(StopOnTrace::Dfs)
    );
    assert_eq!(
        parse(&["--stop-on-trace=BFS", "x.spthy"]).stop_on_trace,
        Some(StopOnTrace::Bfs)
    );
    assert_eq!(
        parse(&["--stop-on-trace=seqdfs", "x.spthy"]).stop_on_trace,
        Some(StopOnTrace::SeqDfs)
    );
    assert_eq!(
        parse(&["--stop-on-trace=sorry", "x.spthy"]).stop_on_trace,
        Some(StopOnTrace::Sorry)
    );
    assert_eq!(
        parse(&["--stop-on-trace=none", "x.spthy"]).stop_on_trace,
        Some(StopOnTrace::None)
    );
    // Bare flag: dfs.
    assert_eq!(
        parse(&["--stop-on-trace", "x.spthy"]).stop_on_trace,
        Some(StopOnTrace::Dfs)
    );
}

#[test]
fn stop_on_trace_unknown_is_err() {
    let e = parse_err(&["--stop-on-trace=zigzag", "x.spthy"]);
    assert_eq!(e.kind(), clap::error::ErrorKind::InvalidValue);
}

#[test]
fn partial_eval_known_values_and_bare_default() {
    // Case-insensitive like HS (`map toLower`); a bare flag records the
    // HS flagOpt default `summary`.
    assert_eq!(
        parse(&["--partial-evaluation=SUMMARY", "x.spthy"]).partial_evaluation,
        Some(PartialEval::Summary)
    );
    assert_eq!(
        parse(&["--partial-evaluation=Verbose", "x.spthy"]).partial_evaluation,
        Some(PartialEval::Verbose)
    );
    assert_eq!(
        parse(&["--partial-evaluation", "x.spthy"]).partial_evaluation,
        Some(PartialEval::Summary)
    );
}

#[test]
fn partial_eval_unknown_value_is_a_parse_error() {
    // Canonical clap: rejected up front.  (HS deferred the rejection to
    // theory-load time — deliberately not replicated.)
    let e = parse_err(&["--partial-evaluation=banana", "x.spthy"]);
    assert_eq!(e.kind(), clap::error::ErrorKind::InvalidValue);
}

#[test]
fn output_module_parsed_and_validated() {
    assert_eq!(
        parse(&["-m=msr", "x.spthy"]).output_module.as_deref(),
        Some("msr")
    );
    assert_eq!(
        parse(&["--output-module=spthytyped", "x.spthy"])
            .output_module
            .as_deref(),
        Some("spthytyped")
    );
    // Bare `-m`: spthy.
    assert_eq!(
        parse(&["-m", "x.spthy"]).output_module.as_deref(),
        Some("spthy")
    );
    assert_eq!(parse(&["x.spthy"]).output_module, None);
    // Canonical clap: an unknown module is rejected up front (HS accepted
    // it at parse time and died at load time).
    let e = parse_err(&["-m=fortran", "x.spthy"]);
    assert_eq!(e.kind(), clap::error::ErrorKind::InvalidValue);
}

// =========================================================================
// Required-value flags
// =========================================================================

#[test]
fn defines_take_values_only_via_equals() {
    // `-D` is HS cmdargs `flagOpt ""` (TheoryLoader.hs): the value
    // attaches via `=` only, and a detached token is a positional input
    // file — the spelling scripts/file_flags.tsv mandates for exactly
    // this reason.  (HS also accepts the glued `-DA`; clap's
    // `require_equals` rejects that spelling loudly, a documented delta.)
    let a = parse(&["-D=A", "--defines=B", "x.spthy"]);
    assert_eq!(a.defines, vec!["A", "B"]);
    let a = parse(&["-D", "A", "x.spthy"]);
    assert_eq!(a.defines, vec![""]);
    assert_eq!(a.in_files, vec!["A", "x.spthy"]);
    assert_eq!(
        parse_err(&["-DB", "x.spthy"]).kind(),
        clap::error::ErrorKind::UnknownArgument
    );
}

#[test]
fn trace_output_flags() {
    let a = parse(&["--output-json=t.json", "--output-dot=t.dot", "x.spthy"]);
    assert_eq!(a.trace_json.as_deref(), Some("t.json"));
    assert_eq!(a.trace_dot.as_deref(), Some("t.dot"));
    // Space-separated values and the HS short aliases work too.
    let a = parse(&["--oj", "t.json", "--od", "t.dot", "x.spthy"]);
    assert_eq!(a.trace_json.as_deref(), Some("t.json"));
    assert_eq!(a.trace_dot.as_deref(), Some("t.dot"));
}

// =========================================================================
// Boolean flags
// =========================================================================

/// Every boolean flag that the top-level command takes.  Each flag comes
/// with the [`Args`] field that [`parse_args`] must set from it.
const BOOL_FLAGS: [(&str, fn(&Args) -> bool); 12] = [
    ("--diff", |a| a.diff),
    ("--quit-on-warning", |a| a.quit_on_warning),
    ("--no-ndc", |a| a.no_ndc),
    ("--auto-sources", |a| a.auto_sources),
    ("--oracle-only", |a| a.oracle_only),
    ("--quiet", |a| a.quiet),
    ("--verbose", |a| a.verbose),
    ("--proverif-no-reuse-lemmas", |a| a.proverif_no_reuse_lemmas),
    ("--proverif-no-restrictions", |a| a.proverif_no_restrictions),
    ("--no-compress", |a| a.no_compress),
    ("--parse-only", |a| a.parse_only),
    ("--precompute-only", |a| a.precompute_only),
];

#[test]
fn each_boolean_flag_sets_its_own_field_and_no_other() {
    // The loop checks the complete row for each flag.  That is what catches
    // a cross-wired field in the flattening from the clap tree to [`Args`].
    // A swap of `quiet: cli.load.verbose` and `verbose: cli.load.quiet`
    // still satisfies any test that passes both flags at once and asserts
    // that both fields are true.
    for (set, _) in BOOL_FLAGS {
        let a = parse(&[set, "x.spthy"]);
        for (other, read) in BOOL_FLAGS {
            assert_eq!(read(&a), set == other, "argv `{set}`, field of `{other}`");
        }
    }
    // An argv with none of these flags leaves every field false.  So the
    // loop above reads the flags, not the defaults.
    let a = parse(&["x.spthy"]);
    for (name, read) in BOOL_FLAGS {
        assert!(!read(&a), "`{name}` set without the flag");
    }
    // `-v` is the one short spelling in the set.
    assert!(parse(&["-v", "x.spthy"]).verbose);
}

// =========================================================================
// Interactive-mode flags
// =========================================================================

#[test]
fn port_inline_bare_and_absent() {
    assert_eq!(parse(&["interactive", "-p=8080", "."]).port, Some(8080));
    assert_eq!(parse(&["interactive", "--port=8080", "."]).port, Some(8080));
    // Bare `-p` records the HS default 3001; absent leaves the run
    // pipeline's own 3001 default to apply.
    assert_eq!(parse(&["interactive", "-p", "."]).port, Some(3001));
    assert_eq!(parse(&["interactive", "."]).port, None);
}

#[test]
fn port_out_of_range_is_err() {
    let e = parse_err(&["interactive", "-p=70000", "."]);
    assert_eq!(e.kind(), clap::error::ErrorKind::ValueValidation);
}

#[test]
fn interface_and_web_flags() {
    // `-i` and `--image-format` are HS cmdargs `flagOpt`s, so their values
    // attach via `=` only — `-i *4` must not eat `*4` (HS reads it as a
    // workdir).  `--data-dir` is a port extension with no HS counterpart
    // and takes ordinary clap values.
    let a = parse(&[
        "interactive",
        "-i=*4",
        "--image-format=PNG",
        "--debug",
        "--no-logging",
        "--data-dir",
        "/srv/data",
        ".",
    ]);
    assert_eq!(a.interface.as_deref(), Some("*4"));
    assert_eq!(a.image_format, Some(ImageFormat::Png));
    assert!(a.debug);
    assert!(a.no_logging);
    assert_eq!(a.data_dir.as_deref(), Some("/srv/data"));
    // A detached `-i` value is rejected loudly, never eaten.
    assert!(parse_args(&["interactive".into(), "-i".into(), "*4".into(), ".".into()]).is_err());
}

// =========================================================================
// Parallelism knobs
// =========================================================================

#[test]
fn maude_processes_parsed() {
    let a = parse(&["--maude-processes", "3", "x.spthy"]);
    assert_eq!(a.maude_processes, Some(3));
}

#[test]
fn zero_pool_sizes_rejected() {
    assert_eq!(
        parse_err(&["--maude-processes=0", "x.spthy"]).kind(),
        clap::error::ErrorKind::ValueValidation
    );
    assert_eq!(
        parse_err(&["--processors=0", "x.spthy"]).kind(),
        clap::error::ErrorKind::ValueValidation
    );
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
    // The default is 1:1 (= processors) so the lemma-level and
    // within-lemma fan-outs don't exhaust the pool and fall back to the
    // shared Maude.
    assert_eq!(a.effective_maude_processes(), 8);
}

#[test]
fn effective_maude_processes_explicit_override() {
    let a = parse(&["--processors=8", "--maude-processes=2", "x.spthy"]);
    assert_eq!(a.effective_maude_processes(), 2);
}

// =========================================================================
// Errors, help, version
// =========================================================================

#[test]
fn unknown_flags_are_err() {
    assert_eq!(
        parse_err(&["--prove-all", "x.spthy"]).kind(),
        clap::error::ErrorKind::UnknownArgument
    );
    assert_eq!(
        parse_err(&["--frobnicate", "x.spthy"]).kind(),
        clap::error::ErrorKind::UnknownArgument
    );
    assert_eq!(
        parse_err(&["-Z", "x.spthy"]).kind(),
        clap::error::ErrorKind::UnknownArgument
    );
}

#[test]
fn ddash_routes_to_positional() {
    let a = parse(&["--", "--weird.spthy"]);
    assert_eq!(a.in_files, vec!["--weird.spthy"]);
}

#[test]
fn help_and_version_are_clap() {
    assert_eq!(
        parse_err(&["--help"]).kind(),
        clap::error::ErrorKind::DisplayHelp
    );
    assert_eq!(
        parse_err(&["-h"]).kind(),
        clap::error::ErrorKind::DisplayHelp
    );
    assert_eq!(
        parse_err(&["--version"]).kind(),
        clap::error::ErrorKind::DisplayVersion
    );
    assert_eq!(
        parse_err(&["-V"]).kind(),
        clap::error::ErrorKind::DisplayVersion
    );
}

// =========================================================================
// lemma_matches (HS lemmaSelector, TheoryLoader.hs:418-432)
// =========================================================================

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
