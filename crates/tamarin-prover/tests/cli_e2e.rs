// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

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

use common::{fixture, maude_arg, maude_available, run_binary};
use tamarin_prover::run::RunError;
use tamarin_prover::{parse_args, run};

fn args_from(args: &[&str]) -> tamarin_prover::Args {
    parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
}

fn run_error(extra: &[&str]) -> RunError {
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend_from_slice(extra);
    run(&args_from(&argv)).expect_err("run should fail")
}

/// HS loads every file before it renders any `--precompute-only` doc, and
/// renders them in order, so a file that fails to close stops the output
/// after the earlier files' docs, and after every file's load markers.
#[test]
fn precompute_renders_each_file_before_a_later_file_fails() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    let valid = fixture("single_recv.spthy");
    let failing = fixture("guarded_restriction.spthy");
    for (inputs, docs) in [
        ([valid.as_path(), failing.as_path()], 1),
        ([failing.as_path(), valid.as_path()], 0),
    ] {
        let (code, stdout, stderr) = run_binary(
            &["--precompute-only", "--partial-evaluation=summary"],
            &inputs,
        );
        assert_eq!(code, 1, "{inputs:?}");
        assert_eq!(
            stdout.matches("Multiset rewriting rules:").count(),
            docs,
            "{inputs:?}:\n{stdout}"
        );
        let failure = stderr
            .find("unguarded variable")
            .expect("the guard failure");
        let trace = stderr.find(" partial evaluation: step ");
        assert_eq!(trace.is_some(), docs == 1, "{inputs:?}:\n{stderr}");
        for theory in ["SingleRecv", "GuardedRestriction"] {
            let closed = stderr
                .find(&format!("[Theory {theory}] Theory closed"))
                .unwrap_or_else(|| panic!("{theory} was not loaded:\n{stderr}"));
            assert!(closed < trace.unwrap_or(failure), "{inputs:?}:\n{stderr}");
        }
    }
}

#[test]
fn stored_terminal_replay_emits_a_state_for_each_node() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(maude) = maude_arg() {
        cmd.arg(maude);
    }
    let output = cmd
        .env("TAM_RS_TRACE_STATE", "1")
        .arg(fixture("terminal_replay.spthy"))
        .output()
        .expect("spawn tamarin-rs");
    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).expect("utf-8 stderr");
    let (_, replay_trace) = stderr
        .split_once("[Theory TerminalReplay] Theory closed\n")
        .expect("closed marker before replay trace");
    let states: Vec<_> = replay_trace
        .lines()
        .filter(|line| line.starts_with("[STATE]"))
        .collect();
    assert_eq!(states.len(), 2, "{stderr}");
    assert_ne!(states[0], states[1], "replay emitted the same state twice");
    assert!(
        states[0].contains("nodes=[]"),
        "unexpected root state: {stderr}"
    );
    assert!(
        states[1].contains("nodes=[A,Fresh]"),
        "unexpected child state: {stderr}"
    );
}

#[test]
fn library_returns_batch_failures_instead_of_exiting() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    for (fixture_name, lemma, expected) in [
        ("oracle_missing.spthy", "test", "oracle exec error:"),
        ("guarded_lemma.spthy", "bad", "unguarded variable"),
        ("guarded_restriction.spthy", "ok", "unguarded variable"),
    ] {
        let theory = fixture(fixture_name);
        let error = run_error(&[
            &format!("--prove={lemma}"),
            theory.to_str().expect("fixture path"),
        ]);
        assert!(
            matches!(error, RunError::GhcException(ref message) if message.contains(expected)),
            "unexpected error for {fixture_name}: {error:?}"
        );
    }

    for fixture_name in ["guarded_restriction.spthy", "guarded_source.spthy"] {
        let theory = fixture(fixture_name);
        let error = run_error(&["--precompute-only", theory.to_str().expect("fixture path")]);
        assert!(
            matches!(error, RunError::GhcException(ref message) if message.starts_with("unguarded variable")),
            "unexpected precompute error for {fixture_name}: {error:?}"
        );
    }

    let theory = fixture("single_recv.spthy");
    let error = run_error(&[
        "--prove=chain",
        "--heuristic=z",
        theory.to_str().expect("fixture path"),
    ]);
    assert!(
        matches!(error, RunError::Regular(ref message) if message.contains("unknown goal ranking")),
        "unexpected heuristic error: {error:?}"
    );
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
fn closed_stdout_pipe_exits_quietly() {
    // A reader that leaves early (`tamarin-prover --parse-only x.spthy |
    // head -0`) makes Rust's `println!` PANIC — rc 101 plus a backtrace note
    // on stderr.  GHC treats the same EPIPE as a non-event: `flushStdHandles`
    // swallows it and `runMainIO` still exits 0 with an empty stderr.  The
    // argv must route stdout through the port's own `println!` —
    // `--help`/`--version` are printed by clap, which swallows the write
    // error itself, so they cannot exercise `is_stdout_broken_pipe`.
    //
    // Deterministic EPIPE: stdout is the write half of a socketpair whose
    // peer is closed BEFORE the spawn, so the child's very first stdout
    // write fails — no race against a pipe buffer.  Deleting the panic-hook
    // guard in main.rs makes this rc 101 with a panic report.
    let (theirs, ours) = std::os::unix::net::UnixStream::pair().expect("socketpair");
    drop(ours); // no reader: every child write to stdout now EPIPEs
    let in_path = fixture("single_recv.spthy");
    let child = std::process::Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .args(["--parse-only", in_path.to_str().unwrap()])
        .stdout(std::process::Stdio::from(std::os::fd::OwnedFd::from(
            theirs,
        )))
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn tamarin-rs");
    let out = child.wait_with_output().expect("wait");
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        !err.contains("panicked"),
        "a closed stdout must not surface as a Rust panic; got:\n{err}"
    );
    assert_eq!(out.status.code(), Some(0), "stderr was:\n{err}");
    // `--parse-only` still emits its `[Theory X] Theory loaded` marker on
    // stderr before stdout is first touched; only panic noise is forbidden.
    assert!(
        err.contains("Theory loaded"),
        "expected the pre-write stderr marker, got:\n{err}"
    );
}

#[test]
fn input_manifest_lemma_metadata_uses_preprocessed_theory() {
    let dir = std::env::temp_dir().join(format!("tamarin_lemma_metadata_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let theory = dir.join("root.spthy");
    std::fs::write(dir.join("fragment.inc"), "lemma included: \"T\" by sorry\n").unwrap();
    for (source, flags, expected) in [
        (
            "theory T begin\n#include \"fragment.inc\"\nend",
            vec![],
            "1",
        ),
        (
            "theory T begin lemma inline: \"T\" by sorry end",
            vec![],
            "1",
        ),
        (
            "theory T begin\n/*\nlemma commented: \"T\"\n*/\nend",
            vec![],
            "0",
        ),
        (
            "theory T begin\n#ifdef ACTIVE\nlemma active: \"T\"\n#endif\nend",
            vec![],
            "0",
        ),
        (
            "theory T begin\n#ifdef ACTIVE\nlemma active: \"T\"\n#endif\nend",
            vec!["-D=ACTIVE"],
            "1",
        ),
    ] {
        std::fs::write(&theory, source).unwrap();
        let mut args = flags;
        args.push("input-manifest");
        let (code, stdout, stderr) = run_binary(&args, &[&theory]);
        assert_eq!(code, 0, "{stderr}");
        assert!(
            stdout
                .lines()
                .any(|line| line == format!("M\thas_lemmas\t{expected}")),
            "{stdout}"
        );
    }
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn input_manifest_distinguishes_syntax_rejection_from_missing_inputs() {
    let dir = std::env::temp_dir().join(format!("tamarin_manifest_status_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("root.spthy");
    std::fs::write(dir.join("fragment.inc"), "#include \"missing.spthy\"").unwrap();
    for (source, expected) in [
        ("theory T begin end", 0),
        ("theory T begin ? end", 3),
        // The load's parse-time duplicate-rule check: a conflicting rule is a
        // syntax rejection, while a `let`-written rule equal to its expansion
        // is not.
        (
            "theory T begin rule A: [ ] --> [ Out('a') ] rule A: [ ] --> [ Out('b') ] end",
            3,
        ),
        (
            "theory T begin rule A: [ Fr(~k) ] --> [ Out(<~k, ~k>) ] \
             rule A: let x = ~k in [ Fr(~k) ] --> [ Out(pair(x, ~k)) ] end",
            0,
        ),
        // The check stops where the load stops, at the first declaration
        // that does not elaborate; the load reports that one.
        (
            "theory T begin functions: h/1 equations: h(x) = y \
             rule A: [ ] --> [ Out('a') ] rule A: [ ] --> [ Out('b') ] end",
            0,
        ),
        // The check builds an [AC] symbol applied to nothing as a constant:
        // the fAppAC error belongs to the load, not to the manifest, and a
        // later syntax error is still the one reported.
        (
            "theory T begin functions: f/2 [AC] \
             rule A: [ ] --> [ Out(f()) ] rule A: [ ] --> [ Out(f()) ] end",
            0,
        ),
        (
            "theory T begin functions: f/2 [AC] \
             rule A: [ ] --> [ Out(f()) ] rule A: [ ] --> [ Out(f()) ] ? end",
            3,
        ),
        ("theory T begin #include \"missing.spthy\" end", 1),
        ("theory T begin #include \"fragment.inc\" end", 1),
    ] {
        std::fs::write(&root, source).unwrap();
        let (code, stdout, stderr) = run_binary(&["input-manifest"], &[&root]);
        assert_eq!(code, expected, "{source}: {stderr}");
        if code != 0 {
            assert!(
                stdout.is_empty(),
                "failed manifests must not publish rows: {stdout}"
            );
            assert!(!stderr.is_empty());
        }
        if code == 1 {
            assert!(stderr.contains("missing.spthy"), "{stderr}");
        }
        if code == 3 {
            assert!(
                stderr.contains(&root.to_string_lossy().to_string()),
                "{stderr}"
            );
        }
    }
    let (code, stdout, stderr) = run_binary(&["input-manifest"], &[&dir.join("absent.spthy")]);
    assert_eq!(code, 1, "{stderr}");
    assert!(stdout.is_empty());
    std::fs::remove_dir_all(dir).unwrap();
}
