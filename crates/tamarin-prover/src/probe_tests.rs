// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte pins for the report shapes [`super::test_process`] emits.  Every
//! expected string here was lifted from an oracle capture of the pinned
//! Haskell prover, so a template drift fails a unit test rather than a
//! transcript diff.

use super::*;

#[test]
fn command_line_is_unwords_prog_then_args() {
    assert_eq!(command_line("dot", &["-V"]), "dot -V");
    assert_eq!(command_line("which", &["jsonbin"]), "which jsonbin");
    // `unwords ["maude"]` — no trailing space for an empty argument list
    // (HS `ensureMaude`'s installation probe runs `maude` with no arguments).
    assert_eq!(command_line("maude", &[]), "maude");
}

/// Oracle: `interactive --with-json=/no/such/jsonbin` — `which` exits 1, so
/// the reason is the exit-code line plus `ensureGraphCommand`'s `errMsg`
/// (Environment.hs:114-115), which `unlines` already newline-terminated; the
/// extra `putStrErrLn` newline is the blank line before `Detailed results`.
#[test]
fn error_report_matches_which_exit_code_failure() {
    let got = error_report(
        &format!("failed with exit code 1\n\n{ERR_MSG_COMMAND_NOT_FOUND}"),
        "which",
        &["/no/such/jsonbin"],
        "",
        "",
        "",
    );
    assert_eq!(
        got,
        "failed with exit code 1\n\
         \n\
         Command not found\n\
         \n\
         Detailed results from testing 'which'\n\
         \x20command: which /no/such/jsonbin\n\
         \x20stdin:   \n\
         \x20stdout:  \n\
         \x20stderr:  \n"
    );
}

/// Oracle: `interactive --with-dot=/bin/true` — the tool starts and exits 0,
/// but its (empty) stderr has no `graphviz` in it, so `check` returns
/// `Left "Error."` and the WARNING default message never appears.
#[test]
fn error_report_matches_rejected_dot_output() {
    let got = error_report("Error.", "/bin/true", &["-V"], "", "", "");
    assert_eq!(
        got,
        "Error.\n\
         Detailed results from testing '/bin/true'\n\
         \x20command: /bin/true -V\n\
         \x20stdin:   \n\
         \x20stdout:  \n\
         \x20stderr:  \n"
    );
}

/// The captured streams are echoed VERBATIM, trailing newlines included, so a
/// non-empty stream leaves a blank line behind it.
#[test]
fn error_report_echoes_captured_streams() {
    let got = error_report(
        ERR_MSG_COMMAND_NOT_FOUND,
        "which",
        &["jsonbin"],
        "",
        "/usr/bin/jsonbin\n",
        "warn\n",
    );
    assert_eq!(
        got,
        "Command not found\n\
         \n\
         Detailed results from testing 'which'\n\
         \x20command: which jsonbin\n\
         \x20stdin:   \n\
         \x20stdout:  /usr/bin/jsonbin\n\
         \n\
         \x20stderr:  warn\n\
         \n"
    );
}

/// Oracle: `interactive --with-dot=/nonexistent/dot` — the process cannot be
/// started, so `readCreateProcessWithExitCode` throws and the handler prints
/// the exception block plus the trailing blank line.
#[test]
fn exception_report_matches_missing_tool() {
    let got = exception_report(
        "/nonexistent/dot",
        &["-V"],
        "",
        "/nonexistent/dot: readCreateProcessWithExitCode: posix_spawnp: \
         does not exist (No such file or directory)",
    );
    assert_eq!(
        got,
        "caught exception while executing:\n\
         /nonexistent/dot -V\n\
         with input: \n\
         Exception: \n\
         \x20  /nonexistent/dot: readCreateProcessWithExitCode: posix_spawnp: \
         does not exist (No such file or directory)\n\
         \n"
    );
}

/// The stdin echo is the literal input, so a probe that feeds the tool
/// something (HS's ` checking installation: ` sends `quit\n` to maude) shows
/// it — and its newline — on the `with input:` line.
#[test]
fn exception_report_echoes_stdin() {
    let got = exception_report("maude", &[], "quit\n", "boom");
    assert_eq!(
        got,
        "caught exception while executing:\n\
         maude\n\
         with input: quit\n\
         \n\
         Exception: \n\
         \x20  boom\n\
         \n"
    );
}

#[test]
fn spawn_exception_text_reproduces_ghc_ioexception_show() {
    let missing = std::io::Error::from(std::io::ErrorKind::NotFound);
    assert_eq!(
        spawn_exception_text("/nonexistent/dot", &missing),
        "/nonexistent/dot: readCreateProcessWithExitCode: posix_spawnp: \
         does not exist (No such file or directory)"
    );
    let denied = std::io::Error::from(std::io::ErrorKind::PermissionDenied);
    assert_eq!(
        spawn_exception_text("/etc/shadow", &denied),
        "/etc/shadow: readCreateProcessWithExitCode: posix_spawnp: \
         permission denied (Permission denied)"
    );
}

/// `init err' ++ ". OK."`: the banner is lowercased and loses its LAST
/// character (`dot -V`'s trailing newline) before the suffix is appended.
#[test]
fn stderr_contains_builds_the_version_ok_line() {
    assert_eq!(
        stderr_contains("graphviz", "", "DOT - Graphviz version 2.43.0 (0)\n"),
        Ok("dot - graphviz version 2.43.0 (0). OK.".to_string())
    );
}

/// A non-empty `okMsg` replaces the banner entirely — the PNG probe reports
/// just `OK.`, whatever `dot -T?` listed.
#[test]
fn stderr_contains_uses_ok_msg_when_given() {
    let listing = "Format: \"?\" not recognized. Use one of: canon cmap png svg\n";
    assert_eq!(
        stderr_contains("png", "OK.", listing),
        Ok("OK.".to_string())
    );
}

/// A miss is `Left "Error."`, and stdout is never consulted — a tool that
/// prints its banner on stdout still fails the check.
#[test]
fn stderr_contains_misses_are_the_bare_error_reason() {
    assert_eq!(
        stderr_contains("graphviz", "", ""),
        Err("Error.".to_string())
    );
    assert_eq!(
        stderr_contains("png", "OK.", "no formats here\n"),
        Err("Error.".to_string())
    );
}

/// The `unlines`-built default messages, which reach the transcript only via
/// the bad-exit-code reason.
#[test]
fn default_messages_are_byte_exact() {
    assert_eq!(
        ERR_MSG_NOT_GRAPHVIZ,
        "WARNING:\n\
         \n\
         \x20The dot tool seems not to be provided by Graphviz.\n\
         \x20Graph generation might not work.\n\
         \x20Please download an official version from:\n\
         \x20        http://www.graphviz.org/\n"
    );
    assert_eq!(
        ERR_MSG_NO_PNG,
        "WARNING:\n\
         \n\
         \x20The dot tool does not seem to support PNG.\n\
         \x20Graph generation might not work.\n"
    );
    assert_eq!(ERR_MSG_COMMAND_NOT_FOUND, "Command not found\n");
}

/// HS reads `ExitFailure code` off `waitForProcess`; a clean non-zero exit is
/// reported as-is.
#[test]
fn hs_exit_code_reads_the_child_status() {
    let (status, out, err) = read_process_with_exit_code("/bin/sh", &["-c", "exit 3"], "")
        .expect("/bin/sh should be startable");
    assert_eq!(hs_exit_code(&status), 3);
    assert_eq!(out, "");
    assert_eq!(err, "");
}

/// Stdin is delivered, both streams are captured, and a child that never
/// drains its input does not turn the write into an error (HS's
/// `ignoreSigPipe`).
#[test]
fn read_process_captures_both_streams() {
    let (status, out, err) =
        read_process_with_exit_code("/bin/sh", &["-c", "cat; echo oops >&2"], "hello\n")
            .expect("/bin/sh should be startable");
    assert!(status.success());
    assert_eq!(out, "hello\n");
    assert_eq!(err, "oops\n");

    let (status, _, _) = read_process_with_exit_code("/bin/true", &[], "ignored input\n")
        .expect("/bin/true should be startable");
    assert!(status.success());
}

#[test]
fn read_process_surfaces_the_spawn_failure() {
    let e =
        read_process_with_exit_code("/nonexistent/dot", &["-V"], "").expect_err("no such binary");
    assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
}
