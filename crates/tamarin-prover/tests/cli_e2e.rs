// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return std::path::Path::new(&p).exists();
    }
    for c in ["/usr/local/bin/maude", "/usr/bin/maude"] {
        if std::path::Path::new(c).exists() {
            return true;
        }
    }
    false
}

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
/// Without the flag the prover probes bare `maude` on PATH (HS-faithful),
/// which is absent on CI runners.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
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

    // `-o`/`--output` is a cmdargs `flagOpt` (Batch.hs:44-84, see line 76): its value is
    // OPTIONAL and must be ATTACHED — `-o FILE` (space-separated) leaves the
    // flag empty and treats FILE as a positional input (verified vs the HS
    // binary). So pass it inline via `--output=FILE`.
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend([
        "--prove=chain",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    let args = args_from(&argv);
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
    // HS writes `renderDoc d` VERBATIM to the `-o` file (`writeFileWithDirs`,
    // Batch.hs:127); only the stdout arm goes through `putStrLn` (Batch.hs:133).
    // The file therefore ends with the bytes `end` — no trailing newline
    // (oracle-verified on this fixture and on the `-m` translate captures).
    assert!(
        body.ends_with("end"),
        "-o file must end with `end`, no trailing newline; got tail: {:?}",
        &body[body.len().saturating_sub(8)..]
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
    // `-o FILE` would treat FILE as a positional input (HS Batch.hs:44-84, see line 76).
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend([
        "--prove=nonexistent",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    let args = args_from(&argv);
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
fn parse_only_pretty_prints_open_theory_to_stdout() {
    // Oracle-pinned `--parse-only` behavior (HS Batch.hs:91-95): the parsed
    // OPEN theory is pretty-printed (`prettyOpenTheory`) to STDOUT — always,
    // even with `--output=FILE`, which the parseOnly branch never consults
    // (verified: the HS binary writes no file and prints the doc) — and
    // `loadTheory`'s `[Theory X] Theory loaded` traceM (TheoryLoader.hs:451)
    // lands on stderr.  Needs no Maude.  Bytes captured from the pinned
    // v1.13.0 oracle on tests/fixtures/single_recv.spthy.
    let in_path = fixture("single_recv.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_parseonly");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join("parse_only.spthy");
    let _ = std::fs::remove_file(&out_path);
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .args(["--parse-only", &output_arg, in_path.to_str().unwrap()])
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(0));
    // `-o` is ignored under `--parse-only` (oracle-verified).
    assert!(
        !out_path.exists(),
        "--parse-only must not write the --output file"
    );
    let expected_stdout = "\
theory SingleRecv

begin

// Function signature and definition of the equational theory E

functions: fst/1, pair/2, snd/1
equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2

rule (modulo E) Send:
   [ Fr( ~k ) ] --[ S( ~k ) ]-> [ Out( ~k ) ]

rule (modulo E) Recv:
   [ In( x ) ] --[ R( x ) ]-> [ ]

lemma chain:
  exists-trace \"\u{2203} k #i #j. (S( k ) @ #i) \u{2227} (R( k ) @ #j)\"
/*
guarded formula characterizing all satisfying traces:
\"\u{2203} k #i #j. (S( k ) @ #i) \u{2227} (R( k ) @ #j)\"
*/
by sorry

end
";
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected_stdout);
    assert_eq!(
        String::from_utf8_lossy(&out.stderr),
        "[Theory SingleRecv] Theory loaded\n"
    );
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
    // `-O`/`--Output` is a cmdargs `flagOpt` (Batch.hs:44-84, see line 77): its value is
    // OPTIONAL and must be ATTACHED — `-O DIR` (space-separated) leaves the
    // flag at its default and treats DIR as a positional input file (verified
    // against the HS binary). So the value must be inline via `--Output=DIR`.
    //
    // No `--parse-only` here: the HS parseOnly branch (Batch.hs:91-95) never
    // consults `writeOutput`, so it writes NO files (oracle-verified) — the
    // `-O` naming can only be exercised on the (maude-needing) close path.
    // No `--prove` either, so no lemma is actually proven — this stays fast.
    let output_arg = format!("--Output={}", out_dir.to_str().unwrap());
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend([&output_arg as &str, in_path.to_str().unwrap()]);
    let args = args_from(&argv);
    let code = run(&args).expect("run");
    assert_eq!(code, 0);
    // Expected output: <out_dir>/single_recv_analyzed.spthy
    let expected = out_dir.join("single_recv_analyzed.spthy");
    assert!(expected.exists(), "expected output file at {:?}", expected);
}

#[test]
fn no_input_files_exits_one_without_an_error_value() {
    // HS `batchMode`'s run ends in `helpAndExit thisMode (Just "no input files
    // given")` (Batch.hs:90), which `putStrLn`s the header + help to STDOUT and
    // `exitFailure`s — never an error value, so `run` returns `Ok(1)`.  The
    // stream split and the exact bytes are pinned in
    // `tests/help_output.rs::no_input_files_reprints_the_help_after_an_error_line_on_stdout`.
    let args = args_from(&["--prove"]);
    assert_eq!(run(&args).expect("help-and-exit is not an error"), 1);
}

#[test]
fn unreadable_input_file_prints_ghc_iox_shape() {
    // HS never guards the theory read: `openFile` throws an IOException that
    // escapes to GHC's runtime, which prints `tamarin-prover: <path>:
    // openFile: <reason>` on stderr and exits 1.  Oracle-pinned for a missing
    // path and a directory path; `--parse-only` keeps Maude out of the run
    // (the oracle emits the same error there, minus the banner).
    for (path, reason) in [
        (
            "/nonexistent/no_such_file.spthy".to_string(),
            "does not exist (No such file or directory)",
        ),
        (
            std::env::temp_dir()
                .to_str()
                .expect("utf-8 tmpdir")
                .to_string(),
            "inappropriate type (is a directory)",
        ),
    ] {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .args(["--parse-only", &path])
            .output()
            .expect("run tamarin-rs");
        assert_eq!(out.status.code(), Some(1), "{path}");
        assert!(out.stdout.is_empty(), "{path}");
        assert_eq!(
            String::from_utf8_lossy(&out.stderr),
            format!("tamarin-prover: {path}: openFile: {reason}\n"),
            "{path}"
        );
    }
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

/// A user `functions: em/2` WITHOUT the bilinear-pairing builtin is an
/// ordinary NoEq symbol: the intruder's `c_em` construction rule applies and
/// the trivial exists-trace lemma is `verified`, identically to the same
/// theory with the function renamed.  DELIBERATE DIVERGENCE from HS, whose
/// `naryOpApp` (Theory/Text/Parser/Term.hs:103) captures the NAME `em` as the
/// C-symbol unconditionally and then crashes on the first Maude query over
/// such a term (`tamem` is only declared under `enableBP`) — a documented
/// upstream bug.  Classifying `em` as C while still emitting the NoEq intruder
/// rule would silently FALSIFY this lemma (the two `em` symbols never unify),
/// which is what this test pins against.  With bilinear-pairing enabled, `em`
/// stays the C symbol (`term_to_vterm`'s gate; the bilinear corpus files cover
/// that side).
#[test]
fn user_em_without_bp_builtin_is_a_plain_function() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    let in_path = fixture("em_no_bp.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_e2e_em_no_bp");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join("em_no_bp_out.spthy");

    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend([
        "--prove",
        "--derivcheck-timeout=0",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    let args = args_from(&argv);
    let code = run(&args).expect("run");
    assert_eq!(code, 0, "expected exit code 0, got {}", code);

    let body = std::fs::read_to_string(&out_path).expect("output written");
    assert!(
        body.contains("lemma l") && body.contains("SOLVED // trace found"),
        "em/2 without bilinear-pairing must behave as a plain function \
         (exists-trace provable via c_em); got:\n{}",
        body
    );
    assert!(
        !body.contains("has no variants"),
        "no bogus empty-variant warning may appear; got:\n{}",
        body
    );
}
