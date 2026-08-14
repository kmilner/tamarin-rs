// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end tests for the `tamarin-prover` CLI library.
//!
//! These tests stand up the whole pipeline — parser → elaborator → solver —
//! IN-PROCESS through the `parse_args` / `run` entry points the binary uses,
//! except where only a spawned process can show the stream split or the exit
//! code.  The maude-backed ones skip only when `TAM_ALLOW_NO_MAUDE=1` says a
//! machine deliberately has no Maude; anywhere else an unresolvable maude
//! fails the run (see `common`'s resolution ladder), because a suite that
//! greens identically with and without Maude proves nothing.

mod common;

use common::{fixture, maude_arg, maude_available, normalize_stdout, run_binary};
use std::path::{Path, PathBuf};
use tamarin_prover::{parse_args, run};

fn args_from(args: &[&str]) -> tamarin_prover::Args {
    parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
}

/// Run the CLI in-process on `extra`, with `--with-maude` for the maude the
/// harness resolved threaded ahead of it, and return the exit code.
fn run_cli(extra: &[&str]) -> i32 {
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend_from_slice(extra);
    run(&args_from(&argv)).expect("run")
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
    let code = run_cli(&[
        "--prove=chain",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "expected exit code 0, got {code}");

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
    let code = run_cli(&[
        "--prove=nonexistent",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
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
    let code = run_cli(&[&output_arg, in_path.to_str().unwrap()]);
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
fn non_utf8_input_prints_the_hgetcontents_iox_shape() {
    // A file that OPENS but is not UTF-8 fails one layer later, in the
    // `hGetContents` decoder, which names the first byte it rejected in
    // decimal.  Oracle-pinned byte-for-byte on all three shapes: a lone
    // continuation byte, a truncated two-byte sequence (which reports its LEAD
    // byte, 195), and an invalid byte at EOF.
    let dir = std::env::temp_dir().join("tamarin_rs_non_utf8_input");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    for (name, body, want_byte) in [
        (
            "lone_continuation.spthy",
            b"theory A\nbegin\n\x80\n".to_vec(),
            128,
        ),
        (
            "truncated_pair.spthy",
            b"theory A\nbegin\n\xc3\x28\n".to_vec(),
            195,
        ),
        (
            "bad_at_eof.spthy",
            b"theory A\nbegin\nend\n\xfe".to_vec(),
            254,
        ),
    ] {
        let path = dir.join(name);
        std::fs::write(&path, &body).expect("write fixture");
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .args(["--parse-only", path.to_str().expect("utf-8 path")])
            .output()
            .expect("run tamarin-rs");
        assert_eq!(out.status.code(), Some(1), "{name}");
        assert!(out.stdout.is_empty(), "{name}");
        assert_eq!(
            String::from_utf8_lossy(&out.stderr),
            format!(
                "tamarin-prover: {}: hGetContents: invalid argument \
                 (cannot decode byte sequence starting from {want_byte})\n",
                path.display()
            ),
            "{name}"
        );
    }
}

#[test]
fn a_deferred_argument_error_yields_to_the_first_file_s_open_failure() {
    // `mkTheoryLoadOptions`' `ArgumentError` is an `error` thunk forced inside
    // `processThy`, AFTER `readFile inFile` (Batch.hs:167-169), so a first input
    // file that cannot be OPENED reports its own IOException and the rejection is
    // never reached.  Only the OPEN gets there first: `readFile` is lazy, so a
    // file that opens and merely fails to DECODE raises `hGetContents` later and
    // the rejection still wins.  Oracle-pinned on all three shapes under
    // `--parse-only`, which keeps Maude (and its banner) out of the run.
    let dir = std::env::temp_dir().join("tamarin_rs_deferred_argument_error");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    let readable = dir.join("readable.spthy");
    std::fs::write(&readable, "theory A\nbegin\nend\n").expect("write fixture");
    let non_utf8 = dir.join("non_utf8.spthy");
    std::fs::write(&non_utf8, b"theory A\nbegin\n\x80\nend\n").expect("write fixture");
    let missing = dir.join("no_such_file.spthy");

    let rejection = "tamarin-prover: output mode not supported.\n\
                     CallStack (from HasCallStack):\n  \
                     error, called at src/Main/Mode/Batch.hs:163:33 in main:Main.Mode.Batch\n"
        .to_string();
    for (file, want) in [
        (&readable, rejection.clone()),
        (&non_utf8, rejection.clone()),
        (
            &missing,
            format!(
                "tamarin-prover: {}: openFile: does not exist (No such file or directory)\n",
                missing.display()
            ),
        ),
    ] {
        let path = file.to_str().expect("utf-8 path");
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .args(["--parse-only", "--output-module=bogus", path])
            .output()
            .expect("run tamarin-rs");
        assert_eq!(out.status.code(), Some(1), "{path}");
        assert!(out.stdout.is_empty(), "{path}");
        assert_eq!(String::from_utf8_lossy(&out.stderr), want, "{path}");
    }
}

#[test]
fn closed_stdout_pipe_exits_quietly() {
    // A reader that leaves early (`tamarin-prover --help | head -0`) makes
    // Rust's `println!` PANIC — rc 101 plus a backtrace note on stderr.  GHC
    // treats the same EPIPE as a non-event: `flushStdHandles` swallows it and
    // `runMainIO` still exits 0 with an empty stderr.  Oracle-verified on
    // `--help` and on a full batch run.
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .arg("--help")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn tamarin-rs");
    // Close the read end before the child can drain its buffer.
    drop(child.stdout.take().expect("piped stdout"));
    let out = child.wait_with_output().expect("wait");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        !err.contains("panicked"),
        "a closed stdout must not surface as a Rust panic; got:\n{err}"
    );
    assert_eq!(out.status.code(), Some(0), "stderr was:\n{err}");
    assert_eq!(err, "");
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
    let code = run_cli(&[
        "--prove",
        "--derivcheck-timeout=0",
        &output_arg,
        "--quiet",
        in_path.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "expected exit code 0, got {code}");

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

// ===========================================================================
// Oracle-pinned coverage for the flags nothing else exercised
// ===========================================================================
//
// `--heuristic`, `--saturation`, `--open-chains`, `--oraclename`,
// `--oracle-only`, `--bound` and `--lemma` reached no assertion beyond the
// `--help` byte pin and `Args` parsing: nothing checked that any of them ever
// arrived at the run.  Each test below drives the built binary with one row of
// `tests/fixtures/cli_refs/cases.tsv` and byte-compares its stdout against the
// HASKELL oracle's, captured into `tests/fixtures/cli_refs/<row>.stdout` by
// `scripts/capture_cli_refs.sh`.  That file is the ONLY place the argv lives,
// so a reference can never have been captured with flags the test does not
// pass.
//
// A MISSING reference is a HARD FAILURE naming the capture script, never a
// skip: skip-if-missing would turn this whole block green on a checkout that
// captured nothing, which is exactly the vacuity it exists to prevent.
//
// STDOUT ONLY.  Two stderr streams are known to diverge for reasons unrelated
// to the flag under test, and pinning them would make these tests red on
// arrival: the `[Saturating Sources]` traces (both sides trace, with different
// sequence counts — see the class note in `scripts/sweep_expected.tsv`), and
// HS's `>>>>>>>>>>>>>>>>>>>>>>>> START INPUT … END Oracle call` block
// (`oracleRanking`, ProofMethod.hs:604-620), which the port's `oracle_ranking`
// (tamarin-theory `constraint/solver/goals.rs`) does not emit at all.  Where a
// flag's only observable IS on stderr, the test asserts the PORT's own marker
// line and says so in place.

/// What every hard failure in this block tells the reader to do.  Never
/// "skip": a skipped pin certifies nothing.
const RECAPTURE_HINT: &str = "regenerate the oracle references with \
     `scripts/capture_cli_refs.sh` (it runs the Haskell binary serially under \
     the OOM guard); do NOT disable this test — a skipped pin certifies \
     nothing";

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

/// `tests/fixtures/cli_refs/`: `cases.tsv`, the captured `<name>.stdout`
/// streams, and the `CAPTURED.tsv` provenance the capture script writes.
fn cli_refs_dir() -> PathBuf {
    fixtures_dir().join("cli_refs")
}

/// One row of `cases.tsv`.
struct FlagCase {
    name: String,
    /// Fixture theory under `tests/fixtures/`.
    theory: String,
    /// `-`, `!=<other>` or `=<other>` — how this row's captured bytes must
    /// relate to another row's.  See [`assert_ref_relation`].
    relation: String,
    /// Flags preceding the theory path, `{FIXTURES}` already expanded.
    args: Vec<String>,
}

fn flag_cases() -> Vec<FlagCase> {
    let path = cli_refs_dir().join("cases.tsv");
    let body = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let fixtures = fixtures_dir();
    let fixtures = fixtures.to_str().expect("utf-8 fixtures dir");
    let cases: Vec<FlagCase> = body
        .lines()
        .filter(|l| !l.trim_start().starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            assert_eq!(
                f.len(),
                4,
                "{}: every row needs 4 tab-separated fields \
                 (name/theory/relation/args); got {l:?}",
                path.display()
            );
            FlagCase {
                name: f[0].to_string(),
                theory: f[1].to_string(),
                relation: f[2].to_string(),
                args: f[3]
                    .split_whitespace()
                    .map(|a| a.replace("{FIXTURES}", fixtures))
                    .collect(),
            }
        })
        .collect();
    assert!(
        !cases.is_empty(),
        "{} lists no cases — this block would then assert nothing",
        path.display()
    );
    cases
}

fn flag_case(name: &str) -> FlagCase {
    flag_cases()
        .into_iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("no `{name}` row in cli_refs/cases.tsv"))
}

/// The `#`-prefixed header of `CAPTURED.tsv`: which oracle binary, which
/// fingerprint, which submodule revision, which maude produced the refs.
/// Quoted into every mismatch message, so a diff caused by a re-built oracle
/// is diagnosable without re-running anything.
fn capture_provenance() -> String {
    let path = cli_refs_dir().join("CAPTURED.tsv");
    let body = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}\n{RECAPTURE_HINT}", path.display()));
    body.lines()
        .filter(|l| l.starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The oracle's captured stdout for `name`, normalized the same way the port's
/// is.  Hard-fails — never skips — when the file is missing or empty.
fn pinned_stdout(name: &str) -> String {
    let path = cli_refs_dir().join(format!("{name}.stdout"));
    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "missing oracle reference {}: {e}\n{RECAPTURE_HINT}",
            path.display()
        )
    });
    assert!(
        !raw.is_empty(),
        "oracle reference {} is EMPTY — a zero-byte capture would make the \
         comparison vacuous.\n{RECAPTURE_HINT}",
        path.display()
    );
    normalize_stdout(&raw)
}

/// Enforce the row's `relation` column on the CAPTURED bytes, i.e. on what the
/// ORACLE did.  This is the anti-vacuity half: `!=` proves the flag changed
/// the oracle's own run (so a port that ignored it cannot match both refs),
/// and `=` records on purpose that it did not, so nobody later reads the
/// equality as coverage it is not.
fn assert_ref_relation(name: &str) {
    let case = flag_case(name);
    let (op, other) = match case.relation.as_str() {
        "-" => return,
        r if r.starts_with("!=") => ("!=", &r[2..]),
        r if r.starts_with('=') => ("=", &r[1..]),
        r => panic!("unknown relation {r:?} on cli_refs/cases.tsv row {name}"),
    };
    let this = pinned_stdout(name);
    let that = pinned_stdout(other);
    let provenance = capture_provenance();
    if op == "!=" {
        assert_ne!(
            this, that,
            "cases.tsv says `{name}` must differ from `{other}`, but the \
             oracle produced identical bytes for both — the flag under test \
             changed nothing, so the pin proves nothing.\n{provenance}"
        );
    } else {
        assert_eq!(
            this, that,
            "cases.tsv says `{name}` must equal `{other}`, but the oracle's \
             bytes differ — the flag DOES change the run, so the row's \
             comment and its `=` relation are stale.\n{provenance}"
        );
    }
}

/// Run the row through the built binary and byte-compare stdout with the
/// oracle capture.  Returns `(normalized stdout, raw stderr)`, or `None` when
/// the run was skipped for want of maude (only reachable under
/// `TAM_ALLOW_NO_MAUDE=1`).  The reference is read FIRST, so a missing capture
/// fails even on a machine that would have skipped.
fn run_pinned_case(name: &str) -> Option<(String, String)> {
    let case = flag_case(name);
    let want = pinned_stdout(name);
    if !maude_available() {
        eprintln!("skipping {name}: maude not on path");
        return None;
    }
    let theory = fixtures_dir().join(&case.theory);
    let args: Vec<&str> = case.args.iter().map(String::as_str).collect();
    let inputs: [&Path; 1] = [theory.as_path()];
    let (code, stdout, stderr) = run_binary(&args, &inputs);
    assert_eq!(
        code,
        0,
        "`{name}` ({:?} {}) exited {code}; stderr:\n{stderr}",
        case.args,
        theory.display()
    );
    let got = normalize_stdout(&stdout);
    assert_eq!(
        got,
        want,
        "`{name}` stdout differs from the oracle capture \
         (cli_refs/{name}.stdout); argv was {:?} {}\n{}",
        case.args,
        theory.display(),
        capture_provenance()
    );
    Some((got, stderr))
}

/// `--lemma=NAME` narrows what gets proven.  HS appends `--lemma` values to
/// the SAME `lemmaNames` list `--prove` fills (`TheoryLoader.hs:326`), and
/// `lemmaSelector` (TheoryLoader.hs:419-431) matches a name exactly unless it
/// ends in `*` — so the bare `--prove`'s recorded `""` matches nothing and
/// `reach` alone is proven, leaving `leaks` at `by sorry` / `analysis
/// incomplete`.  The `''` that no lemma matches is also what makes
/// `checkIfLemmasInTheory` (Wellformedness.hs:1156-1171) fire: its
/// `lemmaArgsNames == [[]]` guard only excuses a bare `--prove` on its own, so
/// the pinned bytes carry that wellformedness warning too.
#[test]
fn lemma_flag_selects_which_lemmas_are_proven() {
    assert_ref_relation("basic_lemma_reach");
    // Both halves, so the pin is self-contained: the port has to match the
    // oracle on the unfiltered run AND on the filtered one, and the two
    // references have to differ.
    run_pinned_case("basic_plain");
    run_pinned_case("basic_lemma_reach");
}

/// `-b/--bound=N` above the proof depth is inert: the `=basic_plain` relation
/// records that the oracle treated `-b=10` as a no-op on this fixture (its
/// proofs are 3 steps deep), and the port has to match that non-effect too.
/// The BINDING half — the bound actually truncating a proof — is pinned
/// separately in `bound_flag_at_a_binding_depth_truncates_the_proof`.
///
/// HAPPY PATH ONLY, on purpose.  The `-b`/`-s`/`-c`/`-d` family's ERROR
/// path is a known deliberate divergence — the port rejects an empty value at
/// parse time (`bound: expected integer, got ""`) where the oracle defers to
/// its own `invalid bound given`, which
/// `cli_tests.rs::short_flag_trailing_equals_is_an_explicit_empty_value`
/// records.  An oracle pin over that argv could not be satisfied, so it is
/// deliberately absent here rather than captured and worked around.
#[test]
fn bound_flag_above_the_proof_depth_is_inert() {
    assert_ref_relation("basic_bound_10");
    run_pinned_case("basic_bound_10");
}

/// `-b/--bound=N` at a BINDING depth.  HS wraps the auto-prover in
/// `boundProver` (`runAutoProver`, Theory/Proof.hs:753-760), whose
/// `boundProofDepth` (Theory/Proof.hs:336-344) replaces every proof node at
/// depth N with `sorry /* bound N hit */` — even a node that would have been
/// Solved, since the `0 < n` guard fires before the node is inspected.  On
/// this fixture `-b=1` cuts both lemmas to `simplify` + bound-sorries and the
/// summary flips to `analysis incomplete`, which is what the `!=basic_plain`
/// relation proves the flag did to the oracle's own run.  The port's cut
/// lives in `expand_inner` (tamarin-theory `constraint/solver/search.rs`),
/// before the ID-DFS depth limit and the `is_finished` check.
#[test]
fn bound_flag_at_a_binding_depth_truncates_the_proof() {
    assert_ref_relation("basic_bound_1");
    run_pinned_case("basic_bound_1");
}

/// `--heuristic=i` (`InjRanking False`, `goalRankingIdentifiers`,
/// Constraint/System.hs:584-595) reaches a different proof than the default
/// `s`: on this fixture it closes `secrecy` one step sooner, which is what the
/// `!=chan_plain` relation pins.  The bare-flag and empty-value spellings are
/// covered by the `Args` tests; this covers the value arriving at the solver.
#[test]
fn heuristic_flag_switches_the_goal_ranking() {
    assert_ref_relation("chan_heuristic_i");
    run_pinned_case("chan_heuristic_i");
}

/// `-s/--saturation=N` caps the source-saturation loop
/// (`paramSaturationLimit`, Sources.hs:355-376).
///
/// On a fixture this small the cap changes no PROOF — the `=chan_plain`
/// relation records that — so the stdout pin alone could not tell the flag
/// from a no-op.  The observable is the port's own progress line, asserted
/// directly here rather than pinned against the oracle, because the
/// `[Saturating Sources]` stream is a documented divergence class (see the
/// note in `scripts/sweep_expected.tsv`).
#[test]
fn saturation_flag_caps_the_source_saturation_loop() {
    assert_ref_relation("chan_saturation_1");
    let Some((_, stderr)) = run_pinned_case("chan_saturation_1") else {
        return;
    };
    assert!(
        stderr.contains(
            "[Saturating Sources] Saturation aborted, more than 1 iterations. \
             (Limit can be change with -s=)"
        ),
        "`--saturation=1` must cut the saturation loop short; the port's \
         stderr never said so:\n{stderr}"
    );
    let Some((_, plain_stderr)) = run_pinned_case("chan_plain") else {
        return;
    };
    assert!(
        !plain_stderr.contains("Saturation aborted"),
        "the unflagged run must NOT abort saturation, else the assertion \
         above proves nothing:\n{plain_stderr}"
    );
}

/// `-c/--open-chains=N` caps how many chain constraints the source
/// precomputation will resolve (`openChainsLimit`, Sources.hs:155).  At 0 the
/// chains survive into the proof, which changes the PROOF ITSELF — the
/// `!=chan_plain` relation — so unlike `--saturation` this one is pinned
/// end-to-end on stdout.  The port's own cap message is asserted as well, to
/// name the cause if the proof ever changes for another reason.
#[test]
fn open_chains_flag_caps_the_precomputed_chain_resolution() {
    assert_ref_relation("chan_open_chains_0");
    let Some((_, stderr)) = run_pinned_case("chan_open_chains_0") else {
        return;
    };
    assert!(
        stderr.contains(
            "[Open Chains] Too many chain constraints, stopping precomputation. \
             Open Chains limits (can be changed with -c=): 0"
        ),
        "`--open-chains=0` must report the cap it hit:\n{stderr}"
    );
}

/// `--heuristic=o --oraclename=FILE` routes goal ranking through the named
/// script (`maybeSetOracleRelPath`, TheoryLoader.hs:343-349; `oraclePath`
/// resolves an ABSOLUTE name as given, Constraint/System.hs:573-574).  The
/// fixture oracle ranks the LAST goal first, an order no built-in ranking
/// produces, so `!=chan_plain` cannot hold unless the script really ran.
#[test]
fn oraclename_flag_routes_ranking_through_the_named_script() {
    assert_ref_relation("chan_oracle_pick_last");
    run_pinned_case("chan_oracle_pick_last");
}

/// `--oracle-only` is `quitOnEmpty`: when the oracle names none of a non-empty
/// goal list, `oracleRanking` returns `Just ApplySorry` and the search stops
/// (ProofMethod.hs:604-620) instead of falling through to the unranked goals.
/// Both halves are pinned — same theory, same rank-nothing oracle, one with
/// the flag and one without — and `!=chan_oracle_rank_none` is what proves the
/// flag, not the oracle, made the difference.
#[test]
fn oracle_only_flag_stops_the_search_when_the_oracle_ranks_nothing() {
    assert_ref_relation("chan_oracle_only");
    run_pinned_case("chan_oracle_rank_none");
    run_pinned_case("chan_oracle_only");
}

/// The case table, the captured streams and the capture manifest must describe
/// the SAME set of runs.  Without this, a renamed row leaves its old reference
/// behind (still passing, pinning nothing) and a half-finished capture leaves
/// rows nobody notices.
#[test]
fn cli_ref_cases_files_and_manifest_are_in_sync() {
    let cases = flag_cases();
    let dir = cli_refs_dir();

    let mut names: Vec<&str> = cases.iter().map(|c| c.name.as_str()).collect();
    names.sort_unstable();
    let before = names.len();
    names.dedup();
    assert_eq!(before, names.len(), "duplicate row names in cases.tsv");

    // Every row has a non-empty capture (hard-fails naming the script).
    for c in &cases {
        let _ = pinned_stdout(&c.name);
        assert!(
            fixtures_dir().join(&c.theory).is_file(),
            "row `{}` names a theory that does not exist: {}",
            c.name,
            c.theory
        );
    }

    // No stray captures: a `.stdout` with no row pins nothing and hides the
    // rename that orphaned it.
    let mut orphans: Vec<String> = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("read cli_refs dir") {
        let p = entry.expect("dir entry").path();
        if p.extension().and_then(|e| e.to_str()) != Some("stdout") {
            continue;
        }
        let stem = p
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("utf-8 ref name")
            .to_string();
        if !names.contains(&stem.as_str()) {
            orphans.push(stem);
        }
    }
    orphans.sort();
    assert!(
        orphans.is_empty(),
        "cli_refs holds captures with no cases.tsv row: {orphans:?} — delete \
         them or restore their rows"
    );

    // The manifest lists exactly the rows, with the byte counts it wrote.
    let manifest = dir.join("CAPTURED.tsv");
    let body = std::fs::read_to_string(&manifest)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}\n{RECAPTURE_HINT}", manifest.display()));
    let mut listed: Vec<&str> = Vec::new();
    for line in body
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        let mut f = line.split('\t');
        let name = f.next().expect("manifest name");
        let bytes: u64 = f
            .next()
            .unwrap_or_else(|| panic!("manifest row {name} has no byte count"))
            .parse()
            .unwrap_or_else(|e| panic!("manifest row {name}: bad byte count: {e}"));
        let actual = std::fs::metadata(dir.join(format!("{name}.stdout")))
            .unwrap_or_else(|e| panic!("manifest names {name}, but: {e}\n{RECAPTURE_HINT}"))
            .len();
        assert_eq!(
            bytes, actual,
            "{name}.stdout is {actual} bytes, the capture recorded {bytes} — \
             the file was edited by hand or the capture was interrupted.\n\
             {RECAPTURE_HINT}"
        );
        listed.push(name);
    }
    listed.sort_unstable();
    assert_eq!(
        listed, names,
        "CAPTURED.tsv does not list the same rows as cases.tsv.\n{RECAPTURE_HINT}"
    );
}
