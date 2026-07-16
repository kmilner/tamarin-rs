//! End-to-end tests for the `tamarin-prover` CLI library.
//!
//! These tests stand up the whole pipeline — parser → elaborator →
//! solver — through the `cli` / `run` entry points used by the
//! binary. They skip themselves silently if a working `maude` binary
//! cannot be located, since CI builds without Maude are still
//! supposed to pass.

use std::path::PathBuf;

use tamarin_prover::{parse_args, run};

fn maude_available() -> bool {
    for c in [
        "/usr/local/bin/maude",
        "/usr/bin/maude",
    ] {
        if std::path::Path::new(c).exists() {
            return true;
        }
    }
    false
}

fn fixture(name: &str) -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("tests");
    p.push("fixtures");
    p.push(name);
    p
}

fn args_from(args: &[&str]) -> tamarin_prover::Args {
    parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
}

#[test]
fn prove_chain_writes_output_with_verified_summary() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    let in_path = fixture("single_recv.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_e2e");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join("single_recv_out.spthy");

    // `-o`/`--output` is a cmdargs `flagOpt` (Batch.hs:76): its value is
    // OPTIONAL and must be ATTACHED — `-o FILE` (space-separated) leaves the
    // flag empty and treats FILE as a positional input (verified vs the HS
    // binary). So pass it inline via `--output=FILE`.
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let args = args_from(&[
        "--prove=chain",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    let code = run(&args).expect("run");
    assert_eq!(code, 0, "expected exit code 0, got {}", code);

    // The proven theory is written to the output file with the chain
    // lemma's proof inline.  HS-faithful: the `summary of summaries`
    // verdict block (verified/analyzed/...) goes to STDOUT, not the `-o`
    // file.  `chain` is an exists-trace lemma satisfied by the example, so
    // its proof ends in `SOLVED // trace found` + `qed` (verified
    // byte-identical to the Haskell binary's output file for this fixture).
    let body = std::fs::read_to_string(&out_path).expect("output written");
    assert!(
        body.contains("theory SingleRecv"),
        "output should contain original theory; got:\n{}",
        body
    );
    assert!(
        body.contains("lemma chain")
            && body.contains("SOLVED // trace found")
            && body.contains("qed"),
        "output file should contain the completed chain proof; got:\n{}",
        body
    );
}

#[test]
fn prove_lemma_filter_excludes_other_lemmas() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    let in_path = fixture("single_recv.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_e2e_filter");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join("single_recv_filter.spthy");

    // Filter to a lemma that doesn't exist — every lemma is filtered
    // out and we still write an output.
    // flagOpt: attach the output value (`--output=FILE`); a space-separated
    // `-o FILE` would treat FILE as a positional input (HS Batch.hs:76).
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let args = args_from(&[
        "--prove=nonexistent",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    let code = run(&args).expect("run");
    assert_eq!(code, 0);
    let body = std::fs::read_to_string(&out_path).expect("output written");
    // The filter excludes every lemma, so `chain` is left unproven in the
    // output file — HS writes it back as `by sorry` (the filtered / `not
    // analyzed` status appears in the stdout summary, not the `-o` file;
    // verified against the Haskell binary for this fixture).
    assert!(
        body.contains("lemma chain") && body.contains("by sorry"),
        "filtered-out lemma should remain `by sorry` in the output; got:\n{}",
        body
    );
}

#[test]
fn parse_only_emits_source_to_stdout() {
    let in_path = fixture("single_recv.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_parseonly");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join("parse_only.spthy");
    // flagOpt: attach the output value (`--output=FILE`); a space-separated
    // `-o FILE` would treat FILE as a positional input (HS Batch.hs:76).
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let args = args_from(&[
        "--parse-only",
        &output_arg,
        in_path.to_str().unwrap(),
    ]);
    let code = run(&args).expect("run");
    assert_eq!(code, 0);
    let body = std::fs::read_to_string(&out_path).expect("output written");
    // No proof has run yet — the source is just echoed back.
    assert!(body.contains("theory SingleRecv"));
    assert!(body.contains("lemma chain"));
}

#[test]
fn output_dir_writes_basename_underscore_analyzed() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let in_path = fixture("single_recv.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_outdir");
    let _ = std::fs::remove_dir_all(&out_dir); // clean prior runs
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    // `-O`/`--Output` is a cmdargs `flagOpt` (Batch.hs:77): its value is
    // OPTIONAL and must be ATTACHED — `-O DIR` (space-separated) leaves the
    // flag at its default and treats DIR as a positional input file (verified
    // against the HS binary). So the value must be inline via `--Output=DIR`.
    let output_arg = format!("--Output={}", out_dir.to_str().unwrap());
    let args = args_from(&[
        "--parse-only", // skip the proof to keep this test fast & maude-light
        &output_arg,
        in_path.to_str().unwrap(),
    ]);
    let code = run(&args).expect("run");
    assert_eq!(code, 0);
    // Expected output: <out_dir>/single_recv_analyzed.spthy
    let expected = out_dir.join("single_recv_analyzed.spthy");
    assert!(
        expected.exists(),
        "expected output file at {:?}",
        expected
    );
}

#[test]
fn no_input_files_returns_error() {
    let args = args_from(&["--prove"]);
    let r = run(&args);
    assert!(r.is_err(), "expected RunError for no input files; got {:?}", r);
}

#[test]
fn diff_flag_is_rejected_with_clear_message() {
    let in_path = fixture("single_recv.spthy");
    let args = args_from(&["--diff", in_path.to_str().unwrap()]);
    let r = run(&args);
    match r {
        Err(e) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains("--diff") || msg.contains("diff"),
                "error should mention --diff: {}",
                msg
            );
        }
        Ok(_) => panic!("expected --diff to error"),
    }
}

#[test]
fn invalid_int_value_for_bound_returns_parse_error() {
    let r = parse_args(&["--bound=not-a-number".to_string()]);
    assert!(r.is_err(), "expected parse error for non-int --bound");
}
