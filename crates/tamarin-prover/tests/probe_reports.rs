// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Transcript pins for the tool-probe section HS `testProcess`
//! (Console.hs:97-149) writes, driven through the `test` command's
//! `ensureGraphVizDot` caller (Test.hs:50, Environment.hs:72-101) and through
//! `ensureMaude` (Console.hs:151-185), which every mode but `--parse-only`
//! runs first.
//!
//! Every expected stderr block is an oracle capture of the pinned Haskell
//! prover run with the same flags.  The `test` command is the cheap way to
//! reach the dot probes — interactive mode runs the same
//! `ensureGraphVizDot`/`ensureGraphCommand` calls (Interactive.hs:106-108) but
//! then binds a socket and blocks.

use std::path::Path;
use std::process::Command;

mod common;

/// `<binary> test --with-maude=<maude> <extra>` — the subcommand leads, as
/// HS's cmdargs requires.
fn run_test_command(extra: &[&str]) -> (i32, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    cmd.arg("test");
    if let Some(a) = common::maude_arg() {
        cmd.arg(a);
    }
    for e in extra {
        cmd.arg(e);
    }
    let out = cmd.output().expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        String::from_utf8(out.stdout).expect("utf-8 stdout"),
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
    )
}

/// The `test` command's stdout around the tool section: only the `nextTopic`
/// headers and the blank line Test.hs:49 puts between the maude and dot
/// blocks, since every probe line goes to stderr.  HS additionally prints a
/// `*** Testing the unification infrastructure ***` topic for its HUnit suite,
/// which this port does not run.
const FAILED_RUN_STDOUT: &str = "Self-testing the tamarin-prover installation.\n\
                                 \n\
                                 *** Testing the availability of the required tools ***\n\
                                 \n\
                                 \n\
                                 *** TEST SUMMARY ***\n\
                                 \n\
                                 WARNING: Some tests failed.\n\
                                 The tamarin-prover might NOT WORK AS INTENDED.\n\
                                 \n";

/// Oracle (`test --with-dot=/nonexistent/dot`): the tool cannot be started, so
/// `readCreateProcessWithExitCode` throws and `testProcess`' handler prints the
/// exception block — continuing the unterminated ` checking version: ` prefix —
/// followed by the blank line from `putStrErrLn ""`.  The PNG probe never runs.
#[test]
fn missing_dot_reports_the_spawn_exception() {
    if !common::maude_available() {
        eprintln!("skipping: maude not where the run will look for it");
        return;
    }
    let (rc, stdout, stderr) = run_test_command(&["--with-dot=/nonexistent/dot"]);
    assert_eq!(rc, 1);
    assert_eq!(stdout, FAILED_RUN_STDOUT);
    assert_eq!(
        common::strip_maude_banner(&stderr),
        "GraphViz tool: '/nonexistent/dot'\n\
         \x20checking version: caught exception while executing:\n\
         /nonexistent/dot -V\n\
         with input: \n\
         Exception: \n\
         \x20  /nonexistent/dot: readCreateProcessWithExitCode: posix_spawnp: \
         does not exist (No such file or directory)\n\
         \n"
    );
}

/// Oracle (`test --with-dot=/bin/true`): the tool starts and exits 0, but its
/// stderr carries no `graphviz`, so `check` fails with `Left "Error."` and the
/// `Detailed results` block dumps the empty streams.  `ensureGraphVizDot`
/// returns `Nothing`, so the PNG probe is skipped and no blank line follows.
#[test]
fn non_graphviz_dot_reports_the_detailed_results_block() {
    if !common::maude_available() {
        eprintln!("skipping: maude not where the run will look for it");
        return;
    }
    if !Path::new("/bin/true").exists() {
        eprintln!("skipping: no /bin/true to stand in for a non-Graphviz dot");
        return;
    }
    let (rc, stdout, stderr) = run_test_command(&["--with-dot=/bin/true"]);
    assert_eq!(rc, 1);
    assert_eq!(stdout, FAILED_RUN_STDOUT);
    assert_eq!(
        common::strip_maude_banner(&stderr),
        "GraphViz tool: '/bin/true'\n\
         \x20checking version: Error.\n\
         Detailed results from testing '/bin/true'\n\
         \x20command: /bin/true -V\n\
         \x20stdin:   \n\
         \x20stdout:  \n\
         \x20stderr:  \n"
    );
}

/// The success path: `dot -V`'s banner is lowercased, loses its trailing
/// newline to `init` and gains `. OK.`; the PNG probe then reports a bare
/// `OK.`.  Only the version line's tool-and-version text is machine-local, so
/// the pin is on the surrounding shape.
#[test]
fn working_dot_reports_version_and_png_ok() {
    if !common::maude_available() {
        eprintln!("skipping: maude not where the run will look for it");
        return;
    }
    if Command::new("dot").arg("-V").output().is_err() {
        eprintln!("skipping: no dot on PATH");
        return;
    }
    let (rc, _stdout, stderr) = run_test_command(&[]);
    let probe = common::strip_maude_banner(&stderr);
    let lines: Vec<&str> = probe.lines().collect();
    assert_eq!(rc, 0, "expected a clean self-test, got:\n{probe}");
    assert_eq!(
        lines.len(),
        3,
        "expected exactly the three GraphViz lines, got:\n{probe}"
    );
    assert_eq!(lines[0], "GraphViz tool: 'dot'");
    let banner = lines[1]
        .strip_prefix(" checking version: ")
        .and_then(|l| l.strip_suffix(". OK."))
        .unwrap_or_else(|| panic!("unexpected version line: {:?}", lines[1]));
    // `map toLower` runs over the banner (the `. OK.` suffix is appended
    // after), so an upper-case character inside it is a port bug.
    assert_eq!(banner, banner.to_lowercase());
    assert!(
        banner.contains("graphviz"),
        "version line lost the tool banner: {:?}",
        lines[1]
    );
    assert_eq!(lines[2], " checking PNG support: OK.");
}

/// The stderr a maude that cannot be started produces, whatever mode asked for
/// it: `testProcess`' exception block — with NO trailing blank line, because
/// `maudeTest` takes the `error` branch instead of `putStrErrLn ""` — followed
/// by GHC's top-level report of that `error` (Console.hs:147).
const MISSING_MAUDE_STDERR: &str = "maude tool: '/nonexistent/maude'\n\
     \x20checking version: caught exception while executing:\n\
     /nonexistent/maude --version\n\
     with input: \n\
     Exception: \n\
     \x20  /nonexistent/maude: readCreateProcessWithExitCode: posix_spawnp: \
     does not exist (No such file or directory)\n\
     tamarin-prover: Maude is not installed. Ensure Maude is available and on the path.\n\
     CallStack (from HasCallStack):\n\
     \x20 error, called at src/Main/Console.hs:147:9 in main:Main.Console\n";

/// Oracle (`test --with-maude=/nonexistent/maude`): the version probe's spawn
/// throws, and because it is a maude probe the handler raises rather than
/// returning — so the `test` command never reaches its dot block or its
/// summary, and the run exits 1 with the two topic lines already on stdout.
#[test]
fn missing_maude_aborts_the_test_command() {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    let out = cmd
        .args(["test", "--with-maude=/nonexistent/maude"])
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(out.stdout).expect("utf-8 stdout"),
        "Self-testing the tamarin-prover installation.\n\
         \n\
         *** Testing the availability of the required tools ***\n"
    );
    assert_eq!(
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
        MISSING_MAUDE_STDERR
    );
}

/// Oracle (`--with-maude=/nonexistent/maude tiny.spthy`): a batch run's
/// `ensureMaudeAndGetVersion` (Batch.hs:115) aborts in the same place, before
/// the first `[Theory …]` marker, leaving stdout completely empty.
#[test]
fn missing_maude_aborts_a_batch_run() {
    let dir = std::env::temp_dir().join("tamarin_rs_probe_reports_nomaude");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let thy = dir.join("tiny.spthy");
    std::fs::write(
        &thy,
        "theory Tiny\nbegin\n\nrule Init:\n  [ Fr(~x) ] --> [ Out(~x) ]\n\nend\n",
    )
    .expect("write theory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    let out = cmd
        .arg("--with-maude=/nonexistent/maude")
        .arg(&thy)
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(String::from_utf8(out.stdout).expect("utf-8 stdout"), "");
    assert_eq!(
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
        MISSING_MAUDE_STDERR
    );
}

/// `variants` runs the same probe (Intruder.hs:45) and dies the same way,
/// before any variant computation output.
#[test]
fn missing_maude_aborts_the_variants_command() {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    let out = cmd
        .args(["variants", "--with-maude=/nonexistent/maude"])
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
        MISSING_MAUDE_STDERR
    );
}

/// `interactive` probes through `ensureMaudeAndGetVersion`
/// (Interactive.hs:103) and dies before binding any socket — no port
/// juggling needed to test it.
#[test]
fn missing_maude_aborts_interactive_before_binding() {
    let dir = std::env::temp_dir().join("tamarin_rs_probe_reports_nomaude_wd");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    let out = cmd
        .args(["interactive", "--with-maude=/nonexistent/maude"])
        .arg(&dir)
        .output()
        .expect("spawn tamarin-rs");
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
        MISSING_MAUDE_STDERR
    );
}

/// A maude that STARTS but reports an unsupported version is not fatal: the
/// version probe's `Left` reason is `errMsg`, the installation probe still
/// runs, and the run carries on (`ensureMaude`'s `Bool` is discarded
/// everywhere but `test`).  `/bin/echo` stands in: it answers `--version`
/// with coreutils' banner and, run bare, writes nothing to stderr.
#[test]
fn unsupported_maude_reports_but_does_not_abort() {
    if !Path::new("/bin/echo").exists() {
        eprintln!("skipping: no /bin/echo to stand in for an unsupported maude");
        return;
    }
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    let out = cmd
        .args([
            "test",
            "--with-maude=/bin/echo",
            "--with-dot=/nonexistent/dot",
        ])
        .output()
        .expect("spawn tamarin-rs");
    let stderr = String::from_utf8(out.stderr).expect("utf-8 stderr");
    let echo_version = String::from_utf8(
        Command::new("/bin/echo")
            .arg("--version")
            .output()
            .expect("spawn /bin/echo")
            .stdout,
    )
    .expect("utf-8 echo --version");
    assert_eq!(
        stderr,
        format!(
            "maude tool: '/bin/echo'\n\
             \x20checking version: WARNING:\n\
             \n\
             \x20'maude --version' returned unsupported version '{stripped}'\n\
             \x20Please install one of the following versions of Maude: \
             2.7.1, 3.0, 3.1, 3.2.1, 3.2.2, 3.3, 3.3.1, 3.4, 3.5, 3.5.1\n\
             \n\
             Detailed results from testing '/bin/echo'\n\
             \x20command: /bin/echo --version\n\
             \x20stdin:   \n\
             \x20stdout:  {echo_version}\n\
             \x20stderr:  \n\
             \x20checking installation: OK.\n\
             GraphViz tool: '/nonexistent/dot'\n\
             \x20checking version: caught exception while executing:\n\
             /nonexistent/dot -V\n\
             with input: \n\
             Exception: \n\
             \x20  /nonexistent/dot: readCreateProcessWithExitCode: posix_spawnp: \
             does not exist (No such file or directory)\n\
             \n",
            stripped = echo_version.trim_end(),
        )
    );
    // The dot probe ran, so the run reached the summary rather than aborting.
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(out.stdout).expect("utf-8 stdout"),
        FAILED_RUN_STDOUT
    );
}
