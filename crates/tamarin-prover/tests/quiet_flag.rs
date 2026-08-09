// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--quiet` is inert: it suppresses nothing the Haskell binary prints.
//!
//! HS registers the flag (`flagNone ["quiet"] (addEmptyArg "quiet")`,
//! TheoryLoader.hs:159-163) and never reads it back — the sole consumer is
//! commented out at TheoryLoader.hs:414-416, and `argExists "quiet"` occurs
//! nowhere else in the tree.  So `ensureMaudeAndGetVersion`'s banner
//! (Console.hs:150-155), the `[Theory X] …` `traceM` markers
//! (TheoryLoader.hs:451, 496, 581, 594, 696; CloseRule.hs:383, 386) and
//! `ppRep`'s `summary of summaries:` block (Batch.hs:87-316) all appear with
//! and without the flag.
//!
//! The pinned oracle (Git revision ef3f0468) confirms it: on [`THEORY`],
//! `--quiet` and unflagged runs produce byte-identical stdout AND stderr.
//! The expectations below are those bytes, minus the three banner lines
//! (machine-local maude path and version), the `Generated from:` block's
//! build info, the analyzed path (a temp dir) and the wall-clock
//! `processing time:` line.

use std::process::Command;

/// A theory that loads, translates and closes, with nothing to prove.
const THEORY: &str = "theory Quiet\nbegin\n\nrule Init:\n  [ ] --[ Start() ]-> [ St() ]\n\n\
                      lemma reachable:\n  exists-trace \"Ex #i. Start()@i\"\n\nend\n";

fn maude_available() -> bool {
    // A `MAUDE_PATH` naming a file that does not exist is a MISCONFIGURATION,
    // not a reason to skip: returning `false` there would report green
    // vacuously on a CI whose image moved maude.
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it or point it at a real maude"
        );
        return true;
    }
    for c in ["/usr/local/bin/maude", "/usr/bin/maude"] {
        if std::path::Path::new(c).exists() {
            return true;
        }
    }
    false
}

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines that
/// follow it (Console.hs:150-155): the path comes from `--with-maude` and the
/// version from the local maude, so only their presence is portable.
fn strip_maude_banner(stderr: &str) -> String {
    let rest: String = stderr
        .split_inclusive('\n')
        .skip_while(|l| l.starts_with("maude tool: '") || l.starts_with(" checking "))
        .collect();
    assert_ne!(
        rest, stderr,
        "expected a `maude tool:` banner on stderr; got:\n{stderr}"
    );
    rest
}

/// `<maude> --version` of the same binary [`run_binary`] hands the prover:
/// `MAUDE_PATH` when set, else the default-path probe list the binary uses.
fn local_maude_version() -> Option<String> {
    let path = std::env::var("MAUDE_PATH").ok().or_else(|| {
        ["/usr/local/bin/maude", "/usr/bin/maude"]
            .iter()
            .find(|c| std::path::Path::new(c).exists())
            .map(|c| c.to_string())
    })?;
    let out = Command::new(&path).arg("--version").output().ok()?;
    let v = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (!v.is_empty()).then_some(v)
}

/// Blank the build-local lines of the `Generated from:` block, the temp-dir
/// input path and the wall-clock measurement, so what remains is comparable
/// across machines.  The `Maude version` line is blanked ONLY when it names
/// the local maude's actual version — a mismatch (e.g. `unknown` because the
/// binary probed the wrong maude) must keep failing the byte comparison.
fn normalize_stdout(stdout: &str) -> String {
    let local_maude = local_maude_version()
        .map(|v| format!("Maude version {v}"))
        .unwrap_or_default();
    stdout
        .lines()
        .filter(|l| !l.starts_with("  processing time: "))
        .map(|l| {
            if l.starts_with("Git revision: ") || l.starts_with("Compiled at: ") {
                "<build info>"
            } else if l.starts_with("analyzed: ") {
                "analyzed: <in file>"
            } else if !local_maude.is_empty() && l == local_maude {
                "Maude version <local maude>"
            } else {
                l
            }
        })
        .fold(String::new(), |mut acc, l| {
            acc.push_str(l);
            acc.push('\n');
            acc
        })
}

/// Run the built binary on [`THEORY`] with `extra` flags, returning
/// `(exit code, normalized stdout, stderr minus the maude banner)`.
fn run_binary(stem: &str, extra: &[&str]) -> (i32, String, String) {
    let dir = std::env::temp_dir().join("tamarin_prover_quiet_flag");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(format!("{stem}.spthy"));
    std::fs::write(&path, THEORY).expect("write theory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    let out = cmd
        .args(extra)
        .arg(&path)
        .output()
        .expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        normalize_stdout(&String::from_utf8(out.stdout).expect("utf-8 stdout")),
        strip_maude_banner(&String::from_utf8(out.stderr).expect("utf-8 stderr")),
    )
}

/// Join oracle-captured lines back into the stream they came from.
fn joined(lines: &[&str]) -> String {
    lines.iter().fold(String::new(), |mut acc, l| {
        acc.push_str(l);
        acc.push('\n');
        acc
    })
}

/// The oracle's `--quiet` stderr for [`THEORY`] after the banner: seven
/// markers, in this order.
const EXPECTED_STDERR: &[&str] = &[
    "[Theory Quiet] Theory loaded",
    "[Theory Quiet] Theory translated",
    "[Theory Quiet] No Deconstruction Chain checks started",
    "[Theory Quiet] No Deconstruction Chain checks ended",
    "[Theory Quiet] Derivation checks started",
    "[Theory Quiet] Derivation checks ended",
    "[Theory Quiet] Theory closed",
];

/// The oracle's `--quiet` stdout for [`THEORY`], normalized by
/// [`normalize_stdout`].  The lone `"  "` line is HS `ppRep`'s separator
/// (Batch.hs:146-148).
const EXPECTED_STDOUT: &[&str] = &[
    "theory Quiet",
    "",
    "begin",
    "",
    "// Function signature and definition of the equational theory E",
    "",
    "functions: fst/1, pair/2, snd/1",
    "equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2",
    "",
    "rule (modulo E) Init:",
    "   [ ] --[ Start( ) ]-> [ St( ) ]",
    "",
    "  /* has exactly the trivial AC variant */",
    "",
    "lemma reachable:",
    "  exists-trace \"\u{2203} #i. Start( ) @ #i\"",
    "/*",
    "guarded formula characterizing all satisfying traces:",
    "\"\u{2203} #i. (Start( ) @ #i)\"",
    "*/",
    "by sorry",
    "",
    "/* All wellformedness checks were successful. */",
    "",
    "/*",
    "Generated from:",
    "Tamarin version 1.13.0",
    "Maude version <local maude>",
    "<build info>",
    "<build info>",
    "*/",
    "",
    "end",
    "",
    "==============================================================================",
    "summary of summaries:",
    "",
    "analyzed: <in file>",
    "",
    "  ",
    "  reachable (exists-trace): analysis incomplete (1 steps)",
    "",
    "==============================================================================",
];

/// `--quiet` keeps the maude banner (stripped here, asserted present) and
/// every `[Theory Quiet] …` marker.
#[test]
fn quiet_keeps_maude_banner_and_theory_markers() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, _, stderr) = run_binary("quiet_markers", &["--quiet"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, joined(EXPECTED_STDERR));
}

/// `--quiet` keeps the whole stdout stream, `summary of summaries:` block
/// included.
#[test]
fn quiet_keeps_summary_of_summaries() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, stderr) = run_binary("quiet_summary", &["--quiet"]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stdout, joined(EXPECTED_STDOUT));
}

/// The flag changes nothing: `--quiet` and a bare run agree on both streams.
#[test]
fn quiet_output_equals_unflagged_output() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (q_code, q_out, q_err) = run_binary("quiet_same", &["--quiet"]);
    let (p_code, p_out, p_err) = run_binary("quiet_same", &[]);
    assert_eq!(q_code, p_code);
    assert_eq!(q_err, p_err);
    assert_eq!(q_out, p_out);
}
