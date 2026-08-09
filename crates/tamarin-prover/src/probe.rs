// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Installation self-probes — the port of HS `Main.Console.testProcess`
//! (Console.hs:97-149) and the callers that drive it.
//!
//! HS runs every "is this tool here and does it work?" check through ONE
//! combinator, so all of them share a report shape: an unterminated test-name
//! prefix on stderr, then either the check's own success message or a failure
//! block — the `Detailed results from testing '<prog>'` dump for a bad exit
//! code / rejected output, the `caught exception while executing:` dump when
//! the process cannot be started at all.  [`test_process`] is that combinator;
//! [`ensure_maude`] (Console.hs:151-185), [`ensure_graph_viz_dot`] and
//! [`ensure_graph_command`] are the callers.
//!
//! The maude probes are the only ones whose failure is fatal: `testProcess`'
//! `maudeTest` flag turns a spawn failure into a GHC `error`, so a run whose
//! maude cannot be started stops right there.
//!
//! Everything here writes to STDERR (HS `putStrErr`/`putStrErrLn` and the
//! callers' own `hPutStrLn stderr`), which is why the `test` command's tool
//! section is invisible on stdout.

use std::io::Write;
use std::process::{Command, ExitStatus, Stdio};

#[cfg(test)]
#[path = "probe_tests.rs"]
pub(crate) mod tests;

/// HS `commandLine` (Console.hs:94-95): `unwords $ prog : args`.
fn command_line(prog: &str, args: &[&str]) -> String {
    let mut s = String::from(prog);
    for a in args {
        s.push(' ');
        s.push_str(a);
    }
    s
}

/// HS `testProcess`' `errMsg` block (Console.hs:114-121): the `reason`, then
/// the `Detailed results` block echoing the command line and the three
/// streams.  Every line is `putStrErrLn`-terminated, so `reason` — which HS's
/// default messages build with `unlines`, i.e. already newline-terminated —
/// leaves a blank line before `Detailed results`.  The `stdin:`/`stdout:`/
/// `stderr:` labels are padded to a fixed width, so their trailing spaces
/// survive even when the stream is empty.
fn error_report(
    reason: &str,
    prog: &str,
    args: &[&str],
    inp: &str,
    out: &str,
    err: &str,
) -> String {
    format!(
        "{reason}\n\
         Detailed results from testing '{prog}'\n\
         \x20command: {cmd}\n\
         \x20stdin:   {inp}\n\
         \x20stdout:  {out}\n\
         \x20stderr:  {err}\n",
        cmd = command_line(prog, args),
    )
}

/// HS `testProcess`' `IOException` handler (Console.hs:139-149): the exception
/// block, whose first line continues the unterminated test-name prefix
/// [`test_process`] has already written.  The trailing blank line is
/// `putStrErrLn ""`, which only the `maudeTest = False` branch reaches — a
/// maude probe raises [`MAUDE_ABORT_MSG`] instead, and the oracle's abort
/// report follows the exception line with no blank line between them.
fn exception_report(
    prog: &str,
    args: &[&str],
    inp: &str,
    exception: &str,
    maude_test: bool,
) -> String {
    format!(
        "caught exception while executing:\n\
         {cmd}\n\
         with input: {inp}\n\
         Exception: \n\
         \x20  {exception}\n\
         {tail}",
        cmd = command_line(prog, args),
        tail = if maude_test { "" } else { "\n" },
    )
}

/// GHC's `show` for the `IOException` `readCreateProcessWithExitCode` raises
/// when the child cannot be started: `<file>: <location>: <description>
/// (<strerror>)` (the `Show IOException` instance, GHC.IO.Exception), with
/// `readCreateProcessWithExitCode: posix_spawnp` as the location.  The two
/// reasons a tool path can hit are reproduced from the `ErrorKind`; anything
/// rarer keeps Rust's own message in the `<description>` slot.
fn spawn_exception_text(prog: &str, e: &std::io::Error) -> String {
    let detail = match e.kind() {
        std::io::ErrorKind::NotFound => "does not exist (No such file or directory)".to_string(),
        std::io::ErrorKind::PermissionDenied => "permission denied (Permission denied)".to_string(),
        _ => e.to_string(),
    };
    format!("{prog}: readCreateProcessWithExitCode: posix_spawnp: {detail}")
}

/// The exit code HS sees in `ExitFailure code`.  GHC's `waitForProcess`
/// reports a signal-terminated child as `ExitFailure (-signum)`, which is
/// exactly the case where [`ExitStatus::code`] is `None`.
fn hs_exit_code(status: &ExitStatus) -> i32 {
    #[cfg(unix)]
    let signalled = {
        use std::os::unix::process::ExitStatusExt;
        status.signal().map(|s| -s)
    };
    #[cfg(not(unix))]
    let signalled: Option<i32> = None;
    status.code().or(signalled).unwrap_or(1)
}

/// HS `readProcessWithExitCode` (System.Process): run `prog args` with `inp`
/// on stdin and capture both output streams.  The stdin write is
/// `ignoreSigPipe`d upstream, so a child that exits without draining its input
/// (`dot -V`) is not an error here either.  HS drains the output pipes
/// concurrently with the stdin write; this port writes first and drains
/// after, which is equivalent for the empty `inp` both callers pass.
fn read_process_with_exit_code(
    prog: &str,
    args: &[&str],
    inp: &str,
) -> std::io::Result<(ExitStatus, String, String)> {
    let mut child = Command::new(prog)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(inp.as_bytes());
    }
    let out = child.wait_with_output()?;
    Ok((
        out.status,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

/// HS `testProcess` (Console.hs:97-149) — the single process-probe combinator
/// every installation self-check goes through.
///
/// `check` is HS's `String -> String -> Either String String` over (stdout,
/// stderr): `Err` is HS's `Left`, a failure whose reason heads the
/// [`error_report`] block; `Ok` is HS's `Right`, a message printed on its own
/// line, and the captured stdout is returned.  `test_name` is written WITHOUT
/// a trailing newline, so that message — or the first line of a failure
/// report — continues it.  `default_msg` is used ONLY for the bad-exit-code
/// reason, which is checked before `check` runs unless `ignore_exit_code`.
///
/// `maude_test` is HS's eighth argument: with it set, a spawn failure is not
/// merely reported but raised as the GHC `error` at Console.hs:147, which
/// stops the whole run.
///
/// `prog` is HS's `prog` — the name every report shows — and `exec` is the
/// binary actually spawned.  HS has one string for both, because `maudePath`
/// hands the probes the literal `"maude"` whenever `--with-maude` is absent
/// and lets `PATH` resolve it; the port resolves that default to an absolute
/// path of its own (`run::default_maude_path`) but still reports the name HS
/// would print, so the two differ only in which of two identical binaries is
/// spawned.
///
/// Returns HS's `Maybe String` — `Some(stdout)` exactly when the test passed.
#[allow(clippy::too_many_arguments)]
fn test_process(
    check: impl Fn(&str, &str) -> Result<String, String>,
    default_msg: &str,
    test_name: &str,
    prog: &str,
    exec: &str,
    args: &[&str],
    inp: &str,
    ignore_exit_code: bool,
    maude_test: bool,
) -> Option<String> {
    // `putStrErr testName` then `hFlush stdout; hFlush stderr`
    // (Console.hs:109-111): the flushes keep the probe lines ordered against
    // the caller's own stdout when both streams land in the same file.
    eprint!("{test_name}");
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();

    let (status, out, err) = match read_process_with_exit_code(exec, args, inp) {
        Ok(t) => t,
        Err(e) => {
            let exception = spawn_exception_text(prog, &e);
            eprint!(
                "{}",
                exception_report(prog, args, inp, &exception, maude_test)
            );
            if maude_test {
                // Console.hs:146-147: the maude probes never return from here.
                tamarin_term::term::hs_error(MAUDE_ABORT_MSG, MAUDE_ABORT_SITE.to_string());
            }
            return None;
        }
    };

    // Console.hs:128-133: the exit code is consulted FIRST unless
    // `ignoreExitCode`, and its reason is `defaultMsg` — `check` never runs on
    // that path.
    let reason = if !ignore_exit_code && !status.success() {
        format!(
            "failed with exit code {}\n\n{default_msg}",
            hs_exit_code(&status)
        )
    } else {
        match check(&out, &err) {
            Ok(msg) => {
                eprintln!("{msg}");
                return Some(out);
            }
            Err(msg) => msg,
        }
    };
    eprint!("{}", error_report(&reason, prog, args, inp, &out, &err));
    None
}

/// The message HS applies `error` to when a maude probe cannot start the tool
/// (Console.hs:147).
const MAUDE_ABORT_MSG: &str = "Maude is not installed. Ensure Maude is available and on the path.";

/// The `HasCallStack` frame that abort prints, as the pinned oracle renders
/// it: `error` at Console.hs:147:9, in the `main` package's `Main.Console`.
/// The coordinates are oracle data — refresh them at a submodule bump.
const MAUDE_ABORT_SITE: &str = "src/Main/Console.hs:147:9 in main:Main.Console";

/// HS `ensureMaude`'s `supportedVersions` (Console.hs:176): the ` checking
/// version: ` probe accepts these strings and no others.  2.7.0 and earlier
/// are excluded upstream because their `get variants` command is incompatible.
const SUPPORTED_MAUDE_VERSIONS: [&str; 10] = [
    "2.7.1", "3.0", "3.1", "3.2.1", "3.2.2", "3.3", "3.3.1", "3.4", "3.5", "3.5.1",
];

/// HS `ensureMaude`'s local `errMsg` (Console.hs:180-185) — `unlines` of
/// `WARNING:`, a blank line, the caller's `reason` and the supported-version
/// list, so the result already ends in a newline (which leaves a blank line
/// before the `Detailed results` block that follows it).
fn maude_err_msg(reason: &str) -> String {
    format!(
        "WARNING:\n\
         \n\
         {reason}\n\
         \x20Please install one of the following versions of Maude: {versions}\n",
        versions = SUPPORTED_MAUDE_VERSIONS.join(", "),
    )
}

/// HS `ensureMaude`'s `checkVersion` (Console.hs:164-167): `maude --version`'s
/// stdout with TRAILING whitespace dropped (`reverse . dropWhile isSpace .
/// reverse`) must be one of [`SUPPORTED_MAUDE_VERSIONS`].  The rejected string
/// is echoed into the reason verbatim, however many lines it spans.
fn check_maude_version(out: &str) -> Result<String, String> {
    let stripped = out.trim_end();
    if SUPPORTED_MAUDE_VERSIONS.contains(&stripped) {
        Ok(format!("{stripped}. OK."))
    } else {
        Err(maude_err_msg(&format!(
            " 'maude --version' returned unsupported version '{stripped}'"
        )))
    }
}

/// HS `ensureMaude`'s `checkInstall` (Console.hs:171-172): the interpreter run
/// must leave stderr EMPTY — stdout (maude's banner) is ignored.  Anything on
/// stderr becomes the `errMsg` reason as-is.
fn check_maude_install(err: &str) -> Result<String, String> {
    if err.is_empty() {
        Ok("OK.".to_string())
    } else {
        Err(maude_err_msg(err))
    }
}

/// HS `ensureMaude` (Console.hs:151-185) — the maude probe every mode but
/// `--parse-only` runs first: `test` (Test.hs:46), `variants` (Intruder.hs:45),
/// `interactive` and batch through `ensureMaudeAndGetVersion`
/// (Interactive.hs:103, Batch.hs:97/102/115), and `--version`
/// (Console.hs:336).
///
/// Two [`test_process`] calls with `maudeTest = True`: `maude --version` must
/// report a supported version, and `maude` fed `quit\n` must run the
/// interpreter without writing to stderr.  Because `maudeTest` is set, a maude
/// that cannot be STARTED never returns from here — the run aborts with
/// [`MAUDE_ABORT_MSG`].  A maude that starts but fails a check only returns
/// `false`; every caller but `test` discards that verdict and carries on.
///
/// `maude` is the tool name to report (HS `maudePath`), `exec` the binary to
/// spawn — see [`test_process`].
///
/// Returns HS's `(Bool, String)`: the verdict, and the version data
/// `getVersionIO` puts in the `Generated from:` block — the raw
/// `maude --version` stdout (newline included) when both probes passed, else
/// `unknown version\n` or `<version> (unsupported)\n`.
pub fn ensure_maude(maude: &str, exec: &str) -> (bool, String) {
    eprintln!("maude tool: '{maude}'");
    // HS `errMsg'` (Console.hs:178): one default message shared by both
    // probes, reached only through the bad-exit-code reason.
    let default_msg = maude_err_msg(&format!("'{maude}' executable not found / does not work"));
    let version = test_process(
        |out, _| check_maude_version(out),
        &default_msg,
        " checking version: ",
        maude,
        exec,
        &["--version"],
        "",
        false,
        true,
    );
    let install = test_process(
        |_, err| check_maude_install(err),
        &default_msg,
        " checking installation: ",
        maude,
        exec,
        &[],
        "quit\n",
        false,
        true,
    );
    // Console.hs:156: HS re-runs `maude --version` a third time for the
    // version data.  On the passing path that is the stdout the version probe
    // already returned, so only a failed version probe pays for the rerun.
    let out = match &version {
        Some(out) => out.clone(),
        None => read_process_with_exit_code(exec, &["--version"], "")
            .map(|(_, out, _)| out)
            .unwrap_or_default(),
    };
    if version.is_none() || install.is_none() {
        if out.is_empty() {
            (false, "unknown version\n".to_string())
        } else {
            // HS `init out ++ " (unsupported)\n"` (Console.hs:159): `init`
            // drops the version output's trailing newline.
            let mut unsupported = out;
            unsupported.pop();
            unsupported.push_str(" (unsupported)\n");
            (false, unsupported)
        }
    } else {
        (true, out)
    }
}

/// HS `ensureGraphVizDot`'s `errMsg1` (Environment.hs:88-95) — the default
/// message for a `dot -V` that exits non-zero.  `unlines`, so it ends in a
/// newline.
const ERR_MSG_NOT_GRAPHVIZ: &str = "WARNING:\n\
                                    \n\
                                    \x20The dot tool seems not to be provided by Graphviz.\n\
                                    \x20Graph generation might not work.\n\
                                    \x20Please download an official version from:\n\
                                    \x20        http://www.graphviz.org/\n";

/// HS `ensureGraphVizDot`'s `errMsg2` (Environment.hs:96-101) — the default
/// message for a `dot -T?` that exits non-zero.  Unreachable in practice: the
/// PNG probe passes `ignoreExitCode = True`, and `dot -T?` always fails.
const ERR_MSG_NO_PNG: &str = "WARNING:\n\
                              \n\
                              \x20The dot tool does not seem to support PNG.\n\
                              \x20Graph generation might not work.\n";

/// HS `ensureGraphCommand`'s `errMsg` (Environment.hs:114-115), which doubles
/// as its `check` failure reason.  `unlines`, so it ends in a newline.
const ERR_MSG_COMMAND_NOT_FOUND: &str = "Command not found\n";

/// HS `ensureGraphVizDot`'s local `check` (Environment.hs:81-87): look for
/// `needle` in the LOWERCASED stderr — stdout is ignored.  With an empty
/// `ok_msg` the reported message is `init err' ++ ". OK."`, the lowercased
/// banner with its LAST character dropped (`dot -V`'s trailing newline);
/// otherwise it is `ok_msg` verbatim.  A miss is `Left "Error."` — the
/// `errMsg1`/`errMsg2` WARNING blocks never appear on this path.
fn stderr_contains(needle: &str, ok_msg: &str, err: &str) -> Result<String, String> {
    let lowered = err.to_lowercase();
    if !lowered.contains(needle) {
        return Err("Error.".to_string());
    }
    if !ok_msg.is_empty() {
        return Ok(ok_msg.to_string());
    }
    let mut banner = lowered;
    banner.pop();
    Ok(format!("{banner}. OK."))
}

/// HS `ensureGraphVizDot` (Environment.hs:72-101) — the `--with-dot` probe,
/// run at interactive startup (Interactive.hs:106-107) and by the `test`
/// command (Test.hs:50).  Two [`test_process`] calls: `dot -V`'s stderr banner
/// must mention `graphviz`, and — only if that passed — `dot -T?`'s must list
/// `png`.  The PNG probe ignores the exit code, since `dot -T?` reports the
/// format list by failing.
///
/// Returns HS's `Maybe String`; both callers only look at whether it is
/// `Some`.
pub fn ensure_graph_viz_dot(dot: &str) -> Option<String> {
    eprintln!("GraphViz tool: '{dot}'");
    let dot_exists = test_process(
        |_, err| stderr_contains("graphviz", "", err),
        ERR_MSG_NOT_GRAPHVIZ,
        " checking version: ",
        dot,
        dot,
        &["-V"],
        "",
        false,
        false,
    );
    if dot_exists.is_some() {
        test_process(
            |_, err| stderr_contains("png", "OK.", err),
            ERR_MSG_NO_PNG,
            " checking PNG support: ",
            dot,
            dot,
            &["-T?"],
            "",
            true,
            false,
        )
    } else {
        dot_exists
    }
}

/// HS `ensureGraphCommand` (Environment.hs:104-115) — the `--with-json`
/// startup probe, which shells out to `which` rather than running the tool.
/// `Checking availablity ...` reproduces the upstream typo and, unlike the
/// maude/dot checks, carries no leading space and no trailing newline.  The
/// verdict is discarded by Interactive.hs:106-108, so this never aborts
/// startup.
pub fn ensure_graph_command(cmd: &str) -> Option<String> {
    eprintln!("Graph rendering command: {cmd}");
    test_process(
        |_, err| {
            if err.is_empty() {
                Ok(" OK.".to_string())
            } else {
                Err(ERR_MSG_COMMAND_NOT_FOUND.to_string())
            }
        },
        ERR_MSG_COMMAND_NOT_FOUND,
        "Checking availablity ...",
        "which",
        "which",
        &[cmd],
        "",
        false,
        false,
    )
}
