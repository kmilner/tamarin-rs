// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
fn parser_diagnostic_renders_the_source_span_and_note() {
    use codespan_reporting::term::termcolor::Buffer;

    let source = "theory T begin\nbuiltins: hasing\nend\n";
    let error = tamarin_parser::parse_theory(source, &[])
        .expect_err("unknown builtin must fail")
        .with_source("bad.spthy");
    let mut buffer = Buffer::no_color();
    emit_parser_error(&mut buffer, &error, "bad.spthy", source).expect("render diagnostic");
    let rendered = std::str::from_utf8(buffer.as_slice()).expect("UTF-8 diagnostic");

    assert!(rendered.contains("error[parse]: Unknown builtin `hasing`"));
    assert_eq!(rendered.matches("Unknown builtin `hasing`").count(), 1);
    assert!(rendered.contains("bad.spthy:2:11"));
    assert!(rendered.contains("hasing"));
}

#[test]
fn parser_diagnostic_uses_parsec_tab_stops() {
    use codespan_reporting::term::termcolor::Buffer;

    let source = "theory T begin\n\tunknown: x\nend\n";
    let error = tamarin_parser::parse_theory(source, &[])
        .expect_err("unknown item must fail")
        .with_source("bad.spthy");
    let mut buffer = Buffer::no_color();
    emit_parser_error(&mut buffer, &error, "bad.spthy", source).expect("render diagnostic");
    let rendered = std::str::from_utf8(buffer.as_slice()).expect("UTF-8 diagnostic");

    assert!(rendered.contains("bad.spthy:2:9"), "{rendered}");
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
