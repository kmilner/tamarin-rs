// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Shared harness for the end-to-end CLI suites: locate maude, run the built
//! binary on a theory, and normalize the machine-local lines out of its
//! output so the remaining bytes can be pinned against the oracle.
//!
//! MAUDE_PATH trap: [`maude_available`] probes ONLY `$MAUDE_PATH` and the two
//! hardcoded absolute paths in [`MAUDE_CANDIDATES`] — never `$PATH`.  On
//! machines whose maude lives elsewhere (e.g.
//! /home/linuxbrew/.linuxbrew/bin/maude) a bare `cargo test` SKIPS every
//! maude-backed pin and reports green; run with
//! `MAUDE_PATH=/path/to/maude cargo test -p tamarin-prover`.
//! [`strip_maude_banner`] is the positive control: it panics when a run that
//! should have started maude produced no banner.

// Each suite pulls in the whole module but uses only part of it.
#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

/// Absolute maude locations probed when `MAUDE_PATH` is unset — the same two
/// the binary's own `default_maude_path` walks, so the harness and the
/// process under test always agree on which maude ran.
pub const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// The maude the binary will invoke: `$MAUDE_PATH` when set, else the first
/// existing candidate.
///
/// A `MAUDE_PATH` that names a file which does not exist is a
/// MISCONFIGURATION, not a reason to skip: silently returning `None` there
/// would turn every maude-backed pin in these suites green on a CI whose
/// image moved maude (`.github/workflows/ci.yml` sets
/// `MAUDE_PATH=/opt/maude/maude`).  Panic instead, so the run goes red.
pub fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?}, or point it at a real maude — skipping \
             every maude-backed pin here would report green vacuously"
        );
        return Some(p);
    }
    MAUDE_CANDIDATES
        .iter()
        .find(|c| Path::new(c).exists())
        .map(|c| c.to_string())
}

/// True when a maude binary exists where the run will look for it.  Every
/// maude-backed pin uses this as a skip-guard.
pub fn maude_available() -> bool {
    maude_path().is_some()
}

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
pub fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

/// `<maude> --version` of the same binary the run hands the prover.
pub fn local_maude_version() -> Option<String> {
    let out = Command::new(maude_path()?).arg("--version").output().ok()?;
    let v = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (!v.is_empty()).then_some(v)
}

/// A file under `crates/tamarin-prover/tests/fixtures/`.
pub fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
}

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines that
/// follow it (Console.hs:150-155) — the path comes from `--with-maude` and the
/// version from the local maude, so only their presence is portable — and
/// ASSERT the banner was there: a run that skipped maude entirely must fail
/// here, not pass vacuously.  Applied per test rather than inside the runners,
/// because `--parse-only` never starts Maude (Batch.hs:91-95) and so prints no
/// banner at all.
pub fn strip_maude_banner(stderr: &str) -> String {
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

/// Blank the build-local lines of the `Generated from:` block, the temp-dir
/// input path and the wall-clock measurement, so what remains is comparable
/// across machines.  The `Maude version` line is blanked ONLY when it names
/// the local maude's actual version — a mismatch (e.g. `unknown` because the
/// binary probed the wrong maude) must keep failing the byte comparison.
pub fn normalize_stdout(stdout: &str) -> String {
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
        .map(|l| format!("{l}\n"))
        .collect()
}

/// Join oracle-captured lines back into the stream they came from.
pub fn joined(lines: &[&str]) -> String {
    lines.join("\n") + "\n"
}

/// Run the built binary on `inputs` with `extra` flags, returning
/// `(exit code, raw stdout, raw stderr)`.  `--with-maude` is threaded from
/// `MAUDE_PATH` when set and precedes every other argument.
pub fn run_binary(extra: &[&str], inputs: &[&Path]) -> (i32, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    for e in extra {
        cmd.arg(e);
    }
    for i in inputs {
        cmd.arg(i);
    }
    let out = cmd.output().expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        String::from_utf8(out.stdout).expect("utf-8 stdout"),
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
    )
}

/// Write `theory` to `<temp>/<dir>/<stem>.spthy` and run [`run_binary`] on it.
/// Each suite passes its own `dir` so concurrent suites cannot collide on a
/// shared stem.
pub fn run_raw(dir: &str, stem: &str, theory: &str, extra: &[&str]) -> (i32, String, String) {
    let dir = std::env::temp_dir().join(dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(format!("{stem}.spthy"));
    std::fs::write(&path, theory).expect("write theory");
    run_binary(extra, &[&path])
}
