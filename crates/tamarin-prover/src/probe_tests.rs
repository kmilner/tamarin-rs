// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte pins for the report shapes [`super::test_process`] emits.  Every
//! expected string here was lifted from an oracle capture of the pinned
//! Haskell prover, so a template drift fails a unit test rather than a
//! transcript diff.

use super::*;

/// The pinned submodule's `src/Main/Console.hs`, embedded at build time, so a
/// submodule bump recompiles this module against the new source.
const CONSOLE_HS: &str = include_str!("../../../tamarin-prover/src/Main/Console.hs");

/// `LINE:COLUMN` of the `error` token on the first line of `hs` holding
/// `needle`, as GHC's `HasCallStack` prints it: both 1-based, the column that
/// of the token itself.
///
/// Matching `error` as a whole word keeps a constructor like `ArgumentError`
/// from being read as the call.
pub(crate) fn error_site(hs: &str, needle: &str) -> String {
    let (idx, line) = hs
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains(needle))
        .unwrap_or_else(|| panic!("no line of the pinned source holds {needle:?}"));
    let col = line
        .match_indices("error")
        .find(|(i, _)| {
            !line[..*i]
                .chars()
                .next_back()
                .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        })
        .map(|(i, _)| line[..i].chars().count() + 1)
        .expect("no `error` token on that line");
    format!("{}:{}", idx + 1, col)
}

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
        false,
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
    let got = exception_report("maude", &[], "quit\n", "boom", false);
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

/// Oracle (`--with-maude=/nonexistent/maude`): with `maudeTest` set the
/// handler raises instead of running `putStrErrLn ""`, so the block ends at
/// the exception line and the abort report follows it immediately.
#[test]
fn exception_report_drops_the_blank_line_for_maude() {
    let got = exception_report(
        "/nonexistent/maude",
        &["--version"],
        "",
        "/nonexistent/maude: readCreateProcessWithExitCode: posix_spawnp: \
         does not exist (No such file or directory)",
        true,
    );
    assert_eq!(
        got,
        "caught exception while executing:\n\
         /nonexistent/maude --version\n\
         with input: \n\
         Exception: \n\
         \x20  /nonexistent/maude: readCreateProcessWithExitCode: posix_spawnp: \
         does not exist (No such file or directory)\n"
    );
}

/// The GHC `error` a failed maude spawn raises, as the oracle prints it under
/// `tamarin-prover: ` (Console.hs:147).
///
/// Both halves are read back out of the pinned source rather than restated.
/// Every other pin of this abort — here and the e2e stderr blocks in
/// `tests/probe_reports.rs` — fixes what the port EMITS, so a submodule bump
/// that moves the `error` or rewords its message leaves them all green while
/// the port prints stale coordinates.  This is the pin that notices.
#[test]
fn maude_abort_is_the_console_hs_error() {
    let raise = CONSOLE_HS
        .lines()
        .find(|l| l.trim_start().starts_with("error \"Maude is not installed"))
        .expect("no maude-missing `error` in the pinned src/Main/Console.hs");
    let message = raise
        .trim_start()
        .trim_start_matches("error ")
        .trim_matches('"');
    assert_eq!(MAUDE_ABORT_MSG, message);
    assert_eq!(
        MAUDE_ABORT_SITE,
        format!(
            "src/Main/Console.hs:{} in main:Main.Console",
            error_site(CONSOLE_HS, "Maude is not installed")
        )
    );
}

/// HS `supportedVersions` (Console.hs:176), read back out of the pinned
/// source for the same reason as the abort pin above: every other test of the
/// version check restates the list (or iterates the constant), so a submodule
/// bump that edits the upstream list — 3.5 and 3.5.1 are recent additions —
/// would otherwise leave the port rejecting a maude the oracle accepts with
/// every test green.
#[test]
fn supported_versions_are_the_console_hs_list() {
    let line = CONSOLE_HS
        .lines()
        .find(|l| l.trim_start().starts_with("supportedVersions ="))
        .expect("no supportedVersions binding in the pinned src/Main/Console.hs");
    let versions: Vec<&str> = line
        .split_once('[')
        .expect("no list literal on the supportedVersions line")
        .1
        .trim_end()
        .strip_suffix(']')
        .expect("supportedVersions list does not close on its own line")
        .split(',')
        .map(|s| s.trim().trim_matches('"'))
        .collect();
    assert_eq!(&SUPPORTED_MAUDE_VERSIONS[..], &versions[..]);
}

/// Oracle (`--with-maude=/bin/echo`): `errMsg` is `unlines`, so it opens with
/// `WARNING:` and a blank line and closes with the version list — the trailing
/// newline is what leaves a blank line before `Detailed results`.  The
/// rejected version is echoed with only TRAILING whitespace stripped, so a
/// multi-line reply keeps its interior newlines.
#[test]
fn maude_version_check_rejects_unsupported_versions() {
    assert_eq!(
        check_maude_version("3.9.0\n"),
        Err("WARNING:\n\
             \n\
             \x20'maude --version' returned unsupported version '3.9.0'\n\
             \x20Please install one of the following versions of Maude: \
             2.7.1, 3.0, 3.1, 3.2.1, 3.2.2, 3.3, 3.3.1, 3.4, 3.5, 3.5.1\n"
            .to_string())
    );
    assert_eq!(
        check_maude_version("first\nsecond\n"),
        Err("WARNING:\n\
             \n\
             \x20'maude --version' returned unsupported version 'first\nsecond'\n\
             \x20Please install one of the following versions of Maude: \
             2.7.1, 3.0, 3.1, 3.2.1, 3.2.2, 3.3, 3.3.1, 3.4, 3.5, 3.5.1\n"
            .to_string())
    );
}

/// Oracle: ` checking version: 3.5.1. OK.` — the stripped version plus
/// `. OK.`, for every version on the supported list.
#[test]
fn maude_version_check_accepts_the_supported_list() {
    for v in SUPPORTED_MAUDE_VERSIONS {
        assert_eq!(
            check_maude_version(&format!("{v}\n")),
            Ok(format!("{v}. OK."))
        );
    }
    // Leading whitespace is NOT stripped — HS's `strip` only drops a suffix.
    assert!(check_maude_version(" 3.5.1\n").is_err());
}

/// The installation probe reads STDERR only: maude's interpreter banner on
/// stdout is irrelevant, anything on stderr becomes the `errMsg` reason.
#[test]
fn maude_install_check_reads_stderr_only() {
    assert_eq!(check_maude_install(""), Ok("OK.".to_string()));
    assert_eq!(
        check_maude_install("Warning: <standard input>, line 1: boom\n"),
        Err("WARNING:\n\
             \n\
             Warning: <standard input>, line 1: boom\n\
             \n\
             \x20Please install one of the following versions of Maude: \
             2.7.1, 3.0, 3.1, 3.2.1, 3.2.2, 3.3, 3.3.1, 3.4, 3.5, 3.5.1\n"
            .to_string())
    );
}

/// HS `errMsg'` (Console.hs:181) — the default message both maude probes pass,
/// reached only through the bad-exit-code reason.
#[test]
fn maude_default_message_names_the_tool() {
    assert_eq!(
        maude_err_msg("'/bin/false' executable not found / does not work"),
        "WARNING:\n\
         \n\
         '/bin/false' executable not found / does not work\n\
         \x20Please install one of the following versions of Maude: \
         2.7.1, 3.0, 3.1, 3.2.1, 3.2.2, 3.3, 3.3.1, 3.4, 3.5, 3.5.1\n"
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
/// reported as-is, and a signalled child is `ExitFailure (-signum)` — the
/// NEGATED number, which is what lands in the `failed with exit code …`
/// reason line for a maude the kernel killed.
#[test]
fn hs_exit_code_reads_the_child_status() {
    let (status, out, err) = read_process_with_exit_code("/bin/sh", &["-c", "exit 3"], "")
        .expect("/bin/sh should be startable");
    assert_eq!(hs_exit_code(&status), 3);
    assert_eq!(out, "");
    assert_eq!(err, "");

    let (status, _, _) = read_process_with_exit_code("/bin/sh", &["-c", "kill -TERM $$"], "")
        .expect("/bin/sh should be startable");
    assert_eq!(status.code(), None, "the shell must die of the signal");
    assert_eq!(hs_exit_code(&status), -15);
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
