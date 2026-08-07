// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Transcript pins for the tool-probe section HS `testProcess`
//! (Console.hs:97-149) writes, driven through the `test` command's
//! `ensureGraphVizDot` caller (Test.hs:50, Environment.hs:72-101).
//!
//! Both expected stderr blocks are oracle captures of the pinned Haskell
//! prover run with the same flags.  The `test` command is the cheap way to
//! reach the probes — interactive mode runs the same
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
