// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Transcript pins for the tool-probe section HS `testProcess`
//! (Console.hs) writes, driven through the `test` command's
//! `ensureGraphVizDot` caller (Test.hs, Environment.hs) and through
//! `ensureMaude` (Console.hs), which every mode but `--parse-only`
//! runs first.
//!
//! Every expected stderr block is an oracle capture of the pinned Haskell
//! prover run with the same flags.  The `test` command is the cheap way to
//! reach the dot probes — interactive mode runs the same
//! `ensureGraphVizDot`/`ensureGraphCommand` calls (Interactive.hs) but
//! then binds a socket and blocks.

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
/// headers and the blank line Test.hs puts between the maude and dot
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

/// Oracle (`test --with-dot=true`): the tool starts and exits 0, but its
/// stderr carries no `graphviz`, so `check` fails with `Left "Error."` and the
/// `Detailed results` block dumps the empty streams.  `ensureGraphVizDot`
/// returns `Nothing`, so the PNG probe is skipped and no blank line follows.
#[test]
fn non_graphviz_dot_reports_the_detailed_results_block() {
    if !common::maude_available() {
        eprintln!("skipping: maude not where the run will look for it");
        return;
    }
    let (rc, stdout, stderr) = run_test_command(&["--with-dot=true"]);
    assert_eq!(rc, 1);
    assert_eq!(stdout, FAILED_RUN_STDOUT);
    assert_eq!(
        common::strip_maude_banner(&stderr),
        "GraphViz tool: 'true'\n\
         \x20checking version: Error.\n\
         Detailed results from testing 'true'\n\
         \x20command: true -V\n\
         \x20stdin:   \n\
         \x20stdout:  \n\
         \x20stderr:  \n"
    );
}

/// Oracle command: `test --with-dot=false`.  The tool starts but exits 1.
/// The code consults the exit code before `check` runs at all.  The reason is
/// therefore the `failed with exit code 1` line, followed by
/// `ensureGraphVizDot`'s `errMsg1` (Environment.hs).  This is the only
/// route by which that WARNING block reaches a transcript.  `unlines` has
/// already terminated the block, so a blank line separates it from the
/// `Detailed results` dump.  `ensureGraphVizDot` returns `Nothing`.  The code
/// therefore skips the PNG probe, and no blank line follows.
///
/// This test repeats the WARNING bytes on purpose.  The source constant is
/// private to `probe`.  This transcript pin restates the constant, in the same
/// way that `probe_tests.rs` restates its source-derived pins.
#[test]
fn bad_exit_dot_reports_the_exit_code_reason_line() {
    if !common::maude_available() {
        eprintln!("skipping: maude not where the run will look for it");
        return;
    }
    let (rc, stdout, stderr) = run_test_command(&["--with-dot=false"]);
    assert_eq!(rc, 1);
    assert_eq!(stdout, FAILED_RUN_STDOUT);
    assert_eq!(
        common::strip_maude_banner(&stderr),
        "GraphViz tool: 'false'\n\
         \x20checking version: failed with exit code 1\n\
         \n\
         WARNING:\n\
         \n\
         \x20The dot tool seems not to be provided by Graphviz.\n\
         \x20Graph generation might not work.\n\
         \x20Please download an official version from:\n\
         \x20        http://www.graphviz.org/\n\
         \n\
         Detailed results from testing 'false'\n\
         \x20command: false -V\n\
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
    if !common::dot_available() {
        return;
    }
    let (rc, stdout, stderr) = run_test_command(&[]);
    // batch-tamarin's launch_tamarin_test requires both success markers.
    assert!(stdout.contains("All tests successful"), "{stdout}");
    assert!(
        stdout.contains("The tamarin-prover should work as intended"),
        "{stdout}"
    );
    assert!(
        stdout.contains("Maude/GraphViz availability checks only"),
        "{stdout}"
    );
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
/// by GHC's top-level report of that `error` (Console.hs).
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

/// A maude that cannot be spawned aborts every mode that needs it, before
/// any other work, with the shared HS block on stderr: one row per mode
/// (argv, expected stdout).  The version probe's spawn throws, and because it
/// is a maude probe the handler raises rather than returning, so `test`
/// exits after its two topic lines and never reaches its summary; the batch,
/// `variants` and `interactive` modes print nothing (`interactive` aborts
/// before binding its port).
#[test]
fn missing_maude_aborts_every_mode() {
    let dir = std::env::temp_dir().join("tamarin_rs_probe_reports_nomaude");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let thy = dir.join("tiny.spthy");
    std::fs::write(
        &thy,
        "theory Tiny\nbegin\n\nrule Init:\n  [ Fr(~x) ] --> [ Out(~x) ]\n\nend\n",
    )
    .expect("write theory");
    let thy = thy.to_str().expect("utf-8 path");
    let wd = dir.to_str().expect("utf-8 path");
    let nomaude = "--with-maude=/nonexistent/maude";
    let rows: [(&str, Vec<&str>, &str); 4] = [
        (
            "test",
            vec!["test", nomaude],
            "Self-testing the tamarin-prover installation.\n\
             \n\
             *** Testing the availability of the required tools ***\n",
        ),
        ("batch", vec![nomaude, thy], ""),
        ("variants", vec!["variants", nomaude], ""),
        ("interactive", vec!["interactive", nomaude, wd], ""),
    ];
    for (mode, argv, stdout) in rows {
        let out = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .args(&argv)
            .output()
            .expect("spawn tamarin-rs");
        assert_eq!(out.status.code(), Some(1), "{mode}");
        assert_eq!(
            String::from_utf8(out.stdout).expect("utf-8 stdout"),
            stdout,
            "{mode}"
        );
        assert_eq!(
            String::from_utf8(out.stderr).expect("utf-8 stderr"),
            MISSING_MAUDE_STDERR,
            "{mode}"
        );
    }
}

#[test]
fn unsupported_maude_reports_but_does_not_abort() {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    let out = cmd
        .args(["test", "--with-maude=echo", "--with-dot=/nonexistent/dot"])
        .output()
        .expect("spawn tamarin-rs");
    let stderr = String::from_utf8(out.stderr).expect("utf-8 stderr");
    let echo_version = String::from_utf8(
        Command::new("echo")
            .arg("--version")
            .output()
            .expect("spawn echo")
            .stdout,
    )
    .expect("utf-8 echo --version");
    assert_eq!(
        stderr,
        format!(
            "maude tool: 'echo'\n\
             \x20checking version: WARNING:\n\
             \n\
             \x20'maude --version' returned unsupported version '{stripped}'\n\
             \x20Please install one of the following versions of Maude: \
             2.7.1, 3.0, 3.1, 3.2.1, 3.2.2, 3.3, 3.3.1, 3.4, 3.5, 3.5.1\n\
             \n\
             Detailed results from testing 'echo'\n\
             \x20command: echo --version\n\
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
