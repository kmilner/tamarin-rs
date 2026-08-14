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
    // HS registers only `--Output`/`-O` (Batch.hs:44-84, see line 78); there is no
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
fn heuristic_bare_vs_absent() {
    // `flagOpt (prettyGoalRanking (head (defaultRankings False)))`
    // (TheoryLoader.hs:120-125) records `"s"` for a bare `--heuristic`
    // (Constraint/System.hs:526 `SmartRanking False`, :586 its `"s"`
    // identifier).  Absent stays `None`, which is NOT the same thing: a
    // recorded value overrides the theory's own ranking
    // (`apDefaultHeuristic <|> pcHeuristic`).  Oracle-checked on a theory
    // carrying `heuristic: o` with no oracle script beside it —
    // `--prove --heuristic` proves it on both sides (rc 0) because the bare
    // flag displaces the oracle ranking, where the same run without the flag
    // dies on the missing script (rc 1) on both.
    let absent = parse(&["t.spthy"]);
    assert_eq!(absent.heuristic, None);
    let bare = parse(&["--heuristic", "t.spthy"]);
    assert_eq!(bare.heuristic.as_deref(), Some("s"));
    assert_eq!(bare.in_files, vec!["t.spthy".to_string()]);
    // The next token is positional, as for every other flagOpt.
    let spaced = parse(&["--heuristic", "C", "t.spthy"]);
    assert_eq!(spaced.heuristic.as_deref(), Some("s"));
    assert_eq!(
        spaced.in_files,
        vec!["C".to_string(), "t.spthy".to_string()]
    );
    // An explicit empty value is the one HS rejects, in `mk_theory_load_options`.
    assert_eq!(
        parse(&["--heuristic=", "t.spthy"]).heuristic.as_deref(),
        Some("")
    );
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
    // output-module is flagOpt "spthy" (Batch.hs:44-84, see line 79): inline only.
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
fn output_module_never_consumes_the_next_token() {
    // flagOpt: a space-separated value stays POSITIONAL and the flag
    // records its default — `-m msr t.spthy` treats `msr` as a file.
    let a = parse(&["-m", "msr", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some("spthy"));
    assert_eq!(a.in_files, vec!["msr".to_string(), "t.spthy".to_string()]);
    let a = parse(&["--output-module", "msr", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some("spthy"));
    assert_eq!(a.in_files, vec!["msr".to_string(), "t.spthy".to_string()]);
}

#[test]
fn output_module_value_is_unvalidated_at_parse_time() {
    // HS validates in `mkTheoryLoadOptions` (TheoryLoader.hs:373-377), not
    // in cmdargs — `-m=bogus` parses fine and dies later in `run_batch`
    // with the `output mode not supported.` GHC error (Batch.hs:163:33).
    let a = parse(&["-m=bogus", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some("bogus"));
    // `--output-module=` records the EMPTY string (also rejected at run
    // time — `ModuleType::from_show("")` is None).
    let a = parse(&["--output-module=", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some(""));
    let a = parse(&["--output-module=spthytyped", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some("spthytyped"));
}

#[test]
fn short_flag_trailing_equals_is_an_explicit_empty_value() {
    // A SHORT flag's trailing `=` records `""`, exactly as the long form
    // does — it is not a bare `-X`.  Oracle-checked: `-m= t.spthy` dies with
    // `output mode not supported.` (rc 1, empty stdout) where bare `-m` runs
    // the `spthy` translate mode, and `-b=` / `-s=` / `-c=` / `-d=` each die
    // with their `... invalid bound given` instead of taking the default.
    let a = parse(&["-m=", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some(""));
    for (flag, name) in [
        ("-b=", "bound"),
        ("-s=", "saturation"),
        ("-c=", "open-chains"),
        ("-d=", "derivcheck-timeout"),
    ] {
        let e = parse_args(&[flag.to_string(), "t.spthy".to_string()])
            .expect_err("an empty integer value is rejected");
        assert_eq!(e.to_string(), format!("{name}: expected integer, got \"\""));
    }
    // The bare forms still take their documented defaults.
    let a = parse(&["-m", "-b", "-s", "-c", "-d", "t.spthy"]);
    assert_eq!(a.output_module.as_deref(), Some("spthy"));
    assert_eq!(a.bound, Some(5));
    assert_eq!(a.saturation, Some(5));
    assert_eq!(a.open_chains, Some(10));
    assert_eq!(a.derivcheck_timeout, Some(5));
}

#[test]
fn help_spells_out_the_module_type_show_strings() {
    // The `-m` row's placeholder is HS `moduleList` (Batch.hs:82-84),
    // `intercalate "|" $ map show [minBound ..]`.  The help text is a
    // byte-pinned literal (the widest left cell, which sizes the whole
    // description column) while `ModuleType` owns the `show` strings, so the
    // two hand-written spellings are pinned to each other here: adding or
    // removing a module fails this and names both sites.
    let help = help_text(Subcommand::Batch);
    let rows: Vec<&str> = help
        .lines()
        .filter(|l| l.trim_start().starts_with("-m --output-module[="))
        .collect();
    assert_eq!(rows.len(), 1, "expected exactly one -m row, got {rows:?}");
    let placeholder = rows[0]
        .split_once("[=")
        .and_then(|(_, rest)| rest.split_once(']'))
        .map(|(inner, _)| inner)
        .expect("the -m row spells its values as `[=a|b|...]`");
    assert_eq!(
        placeholder.split('|').collect::<Vec<_>>(),
        tamarin_theory::module::ModuleType::ALL
            .map(tamarin_theory::module::ModuleType::as_str)
            .to_vec(),
    );
}

#[test]
fn output_dot_and_json_are_flag_req() {
    // output-json/output-dot are flagReq (Batch.hs:80-81): they DO consume
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
fn output_dot_and_json_swallow_a_flag_shaped_value() {
    // cmdargs hands a `flagReq` whatever token follows, `-` prefix and all.
    // Oracle-verified: `--output-json --prove t.spthy` exits 0 having written
    // a file literally NAMED `--prove`, and `--prove` never took effect.
    let a = parse(&["--output-json", "--prove", "t.spthy"]);
    assert_eq!(a.trace_json.as_deref(), Some("--prove"));
    assert!(!a.prove_mode);
    assert_eq!(a.in_files, vec!["t.spthy".to_string()]);
    let a = parse(&["--od", "--output-dot", "t.spthy"]);
    assert_eq!(a.trace_dot.as_deref(), Some("--output-dot"));
    assert_eq!(a.in_files, vec!["t.spthy".to_string()]);
}

#[test]
fn output_dot_and_json_without_a_value_are_a_cmdargs_rejection() {
    // With no token left at all, `processArgs` rejects the command line
    // itself: `Flag requires argument: <flag>` alone on stderr, rc 1, no help
    // block — the [`CliError::CmdArgsReject`] stream shape.  The flag is
    // echoed as spelled, so the aliases report themselves.  Oracle-verified
    // byte-for-byte for all four spellings.
    for (argv, want) in [
        (
            vec!["--prove", "--output-json"],
            "Flag requires argument: --output-json",
        ),
        (
            vec!["--prove", "--output-dot"],
            "Flag requires argument: --output-dot",
        ),
        (vec!["--prove", "--oj"], "Flag requires argument: --oj"),
        (vec!["--prove", "--od"], "Flag requires argument: --od"),
    ] {
        let owned: Vec<String> = argv.iter().map(|s| s.to_string()).collect();
        match parse_args(&owned) {
            Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(e.to_string(), want),
            other => panic!("{argv:?}: expected CmdArgsReject, got {other:?}"),
        }
    }
}

#[test]
fn port_values_are_recorded_raw_and_never_rejected() {
    // cmdargs records whatever `--port`/`-p` carries — `flagOpt ""`, so the
    // bare flag and `=` record `""` — and HS defers ALL reading to startup
    // (`readPort`, Interactive.hs:168-174: `reads @Int`, stdout notice on a
    // miss, default 3001).  So no value is an argv rejection, unreadable
    // ones included: oracle-verified, `interactive --port=abc wd` starts up
    // after `Unable to read port from argument `abc'. Using default.`
    for (argv, want) in [
        (vec!["interactive", "-p="], ""),
        (vec!["interactive", "--port="], ""),
        (vec!["interactive", "--port"], ""),
        (vec!["interactive", "-p3002"], "3002"),
        (vec!["interactive", "-pabc"], "abc"),
        (vec!["interactive", "--port=3.5"], "3.5"),
    ] {
        assert_eq!(parse(&argv).port.as_deref(), Some(want), "{argv:?}");
    }
    assert_eq!(parse(&["interactive", "."]).port, None);
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
            Err(e @ CliError::CmdArgsReject(_)) => {
                assert_eq!(e.to_string(), "Unknown flag: --nonsense", "{argv:?}");
            }
            other => panic!("{argv:?}: expected CmdArgsReject, got {other:?}"),
        }
    }
}

#[test]
fn unknown_short_flag_is_err() {
    match parse_args(&["-Z".to_string()]) {
        Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(e.to_string(), "Unknown flag: -Z"),
        other => panic!("expected CmdArgsReject, got {other:?}"),
    }
}

#[test]
fn flag_none_rejects_an_explicit_inline_value() {
    // cmdargs `flagNone`: `=VALUE` on a no-argument flag is `Unhandled
    // argument to flag, none expected: <token>` — the WHOLE token for a long
    // flag (`--quiet=` keeps its trailing `=`), just `-v` for a short one.
    // Oracle-verified byte-for-byte for every pair below.
    for (argv, want) in [
        (
            vec!["--diff=x"],
            "Unhandled argument to flag, none expected: --diff=x",
        ),
        (
            vec!["--quiet="],
            "Unhandled argument to flag, none expected: --quiet=",
        ),
        (
            vec!["--parse-only=1"],
            "Unhandled argument to flag, none expected: --parse-only=1",
        ),
        (
            vec!["--verbose=y"],
            "Unhandled argument to flag, none expected: --verbose=y",
        ),
        (
            vec!["-v=x"],
            "Unhandled argument to flag, none expected: -v",
        ),
        (vec!["-v="], "Unhandled argument to flag, none expected: -v"),
        (
            vec!["-?=x"],
            "Unhandled argument to flag, none expected: -?",
        ),
        // In a cluster the `=` rejects the boolean short it follows.
        (
            vec!["-vV="],
            "Unhandled argument to flag, none expected: -V",
        ),
    ] {
        let owned: Vec<String> = argv.iter().map(|s| s.to_string()).collect();
        match parse_args(&owned) {
            Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(e.to_string(), want, "{argv:?}"),
            other => panic!("{argv:?}: expected CmdArgsReject, got {other:?}"),
        }
    }

    // A non-`=` char after a boolean short is NOT a value: cmdargs keeps
    // walking the cluster.  Oracle-verified: `-vV` runs both flags, `-vx` is
    // `Unknown flag: -x`.
    let a = parse(&["-vV"]);
    assert!(a.verbose && a.show_version);
    match parse_args(&["-vx".to_string()]) {
        Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(e.to_string(), "Unknown flag: -x"),
        other => panic!("expected CmdArgsReject, got {other:?}"),
    }
}

#[test]
fn long_flag_prefixes_resolve_when_unambiguous() {
    // cmdargs long-flag matching: an unambiguous prefix of a declared name
    // is that flag.  Oracle-verified: each spelling below drives the HS
    // binary to the same state as its full spelling.
    assert_eq!(parse(&["--bou=5", "t.spthy"]).bound, Some(5));
    assert!(parse(&["--hel"]).show_help);
    assert!(parse(&["--vers"]).show_version);
    assert!(parse(&["--precomp", "t.spthy"]).precompute_only);
    assert!(parse(&["--parse-o", "t.spthy"]).parse_only);
    assert_eq!(
        parse(&["--with-d=x", "t.spthy"]).dot_path.as_deref(),
        Some("x")
    );
    assert_eq!(
        parse(&["--oraclen=zz", "t.spthy"]).oracle_name.as_deref(),
        Some("zz")
    );
    // Interactive declares fewer flags, so prefixes resolve differently
    // there: `--po` reaches `port`, and `--v` is `verbose` alone (batch
    // `--v` is ambiguous with `version`, which interactive does not
    // declare).
    assert_eq!(
        parse(&["interactive", "--po=3005", "x"]).port.as_deref(),
        Some("3005")
    );
    let a = parse(&["interactive", "--v", "x"]);
    assert!(a.verbose && !a.show_version);
}

#[test]
fn ambiguous_long_flag_prefixes_are_rejected_with_the_candidate_list() {
    // Two or more prefix hits reject the command line, listing the mode's
    // candidates in DECLARATION ORDER.  Every string oracle-verified
    // byte-for-byte, including the degenerate `--=x` whose empty key
    // prefixes the mode's entire table.
    for (argv, want) in [
        (
            vec!["--o", "x.spthy"],
            "Ambiguous flag '--o', could be any of: oraclename oracle-only open-chains output \
             output-module output-json output-dot",
        ),
        (
            vec!["--p", "x.spthy"],
            "Ambiguous flag '--p', could be any of: prove partial-evaluation \
             proverif-no-reuse-lemmas proverif-no-source-lemmas proverif-no-restrictions \
             proverif-no-multiset proverif-no-precise parse-only precompute-only",
        ),
        (
            vec!["--q", "x.spthy"],
            "Ambiguous flag '--q', could be any of: quit-on-warning quiet",
        ),
        (
            vec!["--he", "x.spthy"],
            "Ambiguous flag '--he', could be any of: heuristic help",
        ),
        (
            vec!["--v", "x.spthy"],
            "Ambiguous flag '--v', could be any of: verbose version",
        ),
        (
            vec!["--output-", "x.spthy"],
            "Ambiguous flag '--output-', could be any of: output-module output-json output-dot",
        ),
        (
            vec!["--=x", "x.spthy"],
            "Ambiguous flag '--', could be any of: prove lemma stop-on-trace bound heuristic \
             partial-evaluation defines diff quit-on-warning auto-sources oraclename oracle-only \
             quiet verbose open-chains saturation derivcheck-timeout proverif-no-reuse-lemmas \
             proverif-no-source-lemmas proverif-no-restrictions proverif-no-multiset \
             proverif-no-precise replication-bound no-ndc no-compress parse-only precompute-only \
             output Output output-module output-json output-dot with-dot with-json with-maude \
             help version",
        ),
        (
            vec!["interactive", "--i=lo", "."],
            "Ambiguous flag '--i', could be any of: interface image-format",
        ),
        (
            vec!["interactive", "--p=3005", "."],
            "Ambiguous flag '--p', could be any of: port prove partial-evaluation \
             proverif-no-reuse-lemmas proverif-no-source-lemmas proverif-no-restrictions \
             proverif-no-multiset proverif-no-precise",
        ),
        (
            vec!["interactive", "--o", "."],
            "Ambiguous flag '--o', could be any of: oraclename oracle-only open-chains",
        ),
        (
            vec!["variants", "--=x"],
            "Ambiguous flag '--', could be any of: Output help",
        ),
        (
            vec!["test", "--=x"],
            "Ambiguous flag '--', could be any of: with-dot with-json with-maude help",
        ),
    ] {
        let owned: Vec<String> = argv.iter().map(|s| s.to_string()).collect();
        match parse_args(&owned) {
            Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(e.to_string(), want, "{argv:?}"),
            other => panic!("{argv:?}: expected CmdArgsReject, got {other:?}"),
        }
    }
}

#[test]
fn prefix_matching_excludes_short_aliases_extras_and_cross_mode_names() {
    // Single-char names never long-match (`--V` is unknown even though `-V`
    // is version); this port's RS-only flags and cross-mode names are
    // exact-only, so their prefixes stay unknown exactly as the oracle
    // answers.  All oracle-verified.
    for (argv, want) in [
        (vec!["--V", "x.spthy"], "Unknown flag: --V"),
        (vec!["--i", "x.spthy"], "Unknown flag: --i"),
        (vec!["--po", "x.spthy"], "Unknown flag: --po"),
        (vec!["--proc", "x.spthy"], "Unknown flag: --proc"),
        (vec!["--no-r", "x.spthy"], "Unknown flag: --no-r"),
    ] {
        let owned: Vec<String> = argv.iter().map(|s| s.to_string()).collect();
        match parse_args(&owned) {
            Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(e.to_string(), want, "{argv:?}"),
            other => panic!("{argv:?}: expected CmdArgsReject, got {other:?}"),
        }
    }
    // Full spellings from the other mode's table still exact-match — the
    // documented flat-parser looseness is unchanged by prefix matching.
    assert!(parse(&["--debug", "x.spthy"]).debug);
}

#[test]
fn errors_downstream_of_a_prefix_echo_the_users_spelling() {
    // `--output-j` resolves to the flagReq `output-json`, and the
    // missing-argument rejection echoes the SPELLED prefix, not the resolved
    // name.  Oracle-verified: `Flag requires argument: --output-j`.
    match parse_args(&["--prove".to_string(), "--output-j".to_string()]) {
        Err(e @ CliError::CmdArgsReject(_)) => {
            assert_eq!(e.to_string(), "Flag requires argument: --output-j");
        }
        other => panic!("expected CmdArgsReject, got {other:?}"),
    }
}

#[test]
fn mode_names_prefix_match_like_flags() {
    // cmdargs matches the first token against mode names with the same
    // exact-then-unambiguous-prefix rule.  Oracle-verified: `inter`, `i`,
    // `te`, `t`, `va` all route; `interactivee` stays a batch file; the
    // empty token prefixes all three modes and is rejected.
    assert_eq!(parse(&["inter", "."]).subcommand, Subcommand::Interactive);
    assert_eq!(parse(&["i", "."]).subcommand, Subcommand::Interactive);
    assert_eq!(parse(&["te"]).subcommand, Subcommand::Test);
    assert_eq!(parse(&["t"]).subcommand, Subcommand::Test);
    assert_eq!(parse(&["va"]).subcommand, Subcommand::Variants);
    let a = parse(&["interactivee"]);
    assert_eq!(a.subcommand, Subcommand::Batch);
    assert_eq!(a.in_files, vec!["interactivee".to_string()]);
    // This port's own `test-prover` alias is exact-only.
    assert_eq!(parse(&["test-prover"]).subcommand, Subcommand::Test);
    assert_eq!(parse(&["test-pro"]).subcommand, Subcommand::Batch);
    match parse_args(&["".to_string()]) {
        Err(e @ CliError::CmdArgsReject(_)) => assert_eq!(
            e.to_string(),
            "Ambiguous mode '', could be any of: interactive variants test"
        ),
        other => panic!("expected CmdArgsReject, got {other:?}"),
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
fn partial_eval_unknown_value_is_deferred_not_a_parse_error() {
    // HS cmdargs accepts any value; `ArgumentError "partial-evaluation:
    // unknown option"` fires only when `mkTheoryLoadOptions` is forced
    // (TheoryLoader.hs:354-358), after the maude banner — so `parse_args`
    // must succeed and leave the rejection to `run_batch`.
    let a = parse(&["--partial-evaluation=banana", "t.spthy"]);
    assert_eq!(a.partial_evaluation, Some(Err(())));
    assert_eq!(a.in_files, vec!["t.spthy".to_string()]);
}

#[test]
fn partial_eval_known_values_and_bare_default() {
    // Case-insensitive (`map toLower`, TheoryLoader.hs:354); a bare flag
    // records the flagOpt default, which is the lowercase literal
    // `"summary"` (TheoryLoader.hs:126-131).
    let a = parse(&["--partial-evaluation=SUMMARY"]);
    assert_eq!(a.partial_evaluation, Some(Ok(PartialEval::Summary)));
    let a = parse(&["--partial-evaluation=Verbose"]);
    assert_eq!(a.partial_evaluation, Some(Ok(PartialEval::Verbose)));
    let a = parse(&["--partial-evaluation"]);
    assert_eq!(a.partial_evaluation, Some(Ok(PartialEval::Summary)));
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
    // HS (Console.hs:334-337) puts the banner + license and then the
    // `Generated from:` block on STDOUT, with `ensureMaude`'s stderr block
    // between the two `putStrLn`s.  `putStrLn versionStr` (versionStr ends
    // with the unlines `\n`) produces the blank line before `Generated from:`.
    // Probed against the installed HS binary: stdout reads
    // `...LICENSE'.\n\nGenerated from:`.
    let out = format!(
        "{}{}",
        version_banner_text(),
        generated_from_text("3.5.1\n")
    );
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
    assert!(out.contains("\nMaude version 3.5.1\nGit revision: "));
    assert!(out.contains("\nCompiled at: "));
    assert!(out.ends_with('\n'));
}

/// `getVersionIO` splices `ensureMaude`'s version data raw, so the
/// unsupported-maude form — which carries its own suffix and newline — lands
/// on the `Maude version` line unchanged.
#[test]
fn generated_from_splices_the_version_data_verbatim() {
    let out = generated_from_text("3.9 (unsupported)\n");
    assert!(out.contains("\nMaude version 3.9 (unsupported)\nGit revision: "));
    let out = generated_from_text("unknown version\n");
    assert!(out.contains("\nMaude version unknown version\nGit revision: "));
}
