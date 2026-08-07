// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
    // cmdargs' own rejection, echoed verbatim: `Unknown flag: <name>`, and
    // a `=VALUE` suffix is not part of the name.  Its own variant so the
    // binary can route it to a bare stderr line with no help block.
    for argv in [
        vec!["--nonsense"],
        vec!["--nonsense=5"],
        vec!["t.spthy", "--nonsense"],
    ] {
        let raw: Vec<String> = argv.iter().map(|s| s.to_string()).collect();
        match parse_args(&raw) {
            Err(e @ CliError::UnknownFlag(_)) => {
                assert_eq!(e.to_string(), "Unknown flag: --nonsense", "{argv:?}");
            }
            other => panic!("{argv:?}: expected UnknownFlag, got {other:?}"),
        }
    }
}

#[test]
fn unknown_short_flag_is_err() {
    match parse_args(&["-Z".to_string()]) {
        Err(e @ CliError::UnknownFlag(_)) => assert_eq!(e.to_string(), "Unknown flag: -Z"),
        other => panic!("expected UnknownFlag, got {other:?}"),
    }
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

#[test]
fn version_stdout_has_blank_line_before_generated_from_and_no_maude_lines() {
    // HS (Console.hs:326-330) puts the banner + license + `Generated from:`
    // block on STDOUT.  `putStrLn versionStr` (versionStr ends with the
    // unlines `\n`) produces a blank line before `Generated from:`.  The
    // maude self-check lines must NOT appear on stdout.  Probed against the
    // installed HS binary: stdout ends `...LICENSE'.\n\nGenerated from:`.
    let out = version_text("maude");
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
    let err = version_maude_stderr_text("maude", "maude");
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
        lines[2] == " checking installation: OK." || lines[2] == " checking installation: FAILED."
    );
}
