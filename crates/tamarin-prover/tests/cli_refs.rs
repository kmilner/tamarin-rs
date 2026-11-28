// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The CLI reference table: every row of `tests/fixtures/cli_refs/cases.tsv`
//! runs the built binary and is compared with the HASKELL oracle's run of the
//! same argv, captured into `cli_refs/<row>.stdout` by
//! `scripts/capture_cli_refs.sh`.
//!
//! Flags are only parsed by the `Args` tests; this table is what shows each
//! one arriving at the run: `--heuristic`, `--saturation`, `--open-chains`,
//! `--oraclename`, `--oracle-only`, `--bound`, `--lemma`, `-D`, `--quiet`,
//! `--partial-evaluation`, `--precompute-only`, `--parse-only` and the
//! `variants` subcommand.  The table is the ONLY place the argv lives, so a
//! reference can never have been captured with flags the test does not pass.
//!
//! What a row pins:
//! * stdout, byte for byte after [`normalize_stdout`], and the exit code;
//! * the `relation` column, on the CAPTURES: `!=other` proves the flag
//!   changed the oracle's own run, `=other` records on purpose that it did
//!   not, so nobody later reads the equality as coverage it is not;
//! * the `stderr` column, on the PORT only: fragments that must (or, with a
//!   leading `!`, must not) appear.  Stderr is not oracle-compared, because
//!   two streams diverge for reasons unrelated to any flag: the
//!   `[Saturating Sources]` traces (different sequence counts, see
//!   `scripts/sweep_expected.tsv`) and HS's `START INPUT … END Oracle call`
//!   block, which the port does not emit.
//!
//! A MISSING reference is a HARD FAILURE naming the capture script, never a
//! skip: skip-if-missing would turn the table green on a checkout that
//! captured nothing.

mod common;

use common::{maude_arg, maude_available, normalize_stdout};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

/// What every hard failure here tells the reader to do.  Never "skip": a
/// skipped pin certifies nothing.
const RECAPTURE_HINT: &str = "regenerate the oracle references with \
     `scripts/capture_cli_refs.sh` (it runs the Haskell binary serially under \
     the OOM guard); do NOT disable this test — a skipped pin certifies \
     nothing";

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

fn cli_refs_dir() -> PathBuf {
    fixtures_dir().join("cli_refs")
}

/// One row of `cases.tsv`.
struct Row {
    name: String,
    /// The input files, in order: none for a subcommand that reads no
    /// theory (`-` in the table).
    inputs: Vec<PathBuf>,
    /// `-`, `!=<other>` or `=<other>`.
    relation: String,
    /// The exit code both engines must return.
    rc: i32,
    /// Flags preceding the inputs, placeholders expanded.
    args: Vec<String>,
    /// Port-only stderr fragments: present, or absent when `!`-prefixed.
    stderr: Vec<String>,
}

/// `{FIXTURES}` is tests/fixtures, `{EXAMPLES}` the submodule's examples.
fn expand(s: &str) -> String {
    let fixtures = fixtures_dir();
    let examples = tamarin_test_support::corpus_root();
    s.replace("{FIXTURES}", fixtures.to_str().expect("utf-8 path"))
        .replace("{EXAMPLES}", examples.to_str().expect("utf-8 path"))
}

fn rows() -> Vec<Row> {
    let path = cli_refs_dir().join("cases.tsv");
    let body = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let rows: Vec<Row> = body
        .lines()
        .filter(|l| !l.trim_start().starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            assert_eq!(
                f.len(),
                6,
                "{}: every row needs 6 tab-separated fields \
                 (name/inputs/relation/rc/args/stderr); got {l:?}",
                path.display()
            );
            let inputs = match f[1] {
                "-" => Vec::new(),
                list => list
                    .split_whitespace()
                    .map(|p| fixtures_dir().join(expand(p)))
                    .collect(),
            };
            let stderr = match f[5] {
                "-" => Vec::new(),
                list => list
                    .split('|')
                    .map(|s| s.trim().replace("\\n", "\n"))
                    .collect(),
            };
            Row {
                name: f[0].to_string(),
                inputs,
                relation: f[2].to_string(),
                rc: f[3]
                    .parse()
                    .unwrap_or_else(|e| panic!("row {}: bad rc {:?}: {e}", f[0], f[3])),
                args: f[4].split_whitespace().map(expand).collect(),
                stderr,
            }
        })
        .collect();
    assert!(
        !rows.is_empty(),
        "{} lists no rows — the table would then assert nothing",
        path.display()
    );
    rows
}

/// The `#`-prefixed header of `CAPTURED.tsv`: which oracle binary, which
/// fingerprint, which submodule revision, which maude produced the refs.
/// Quoted into every mismatch, so a diff caused by a rebuilt oracle is
/// diagnosable without re-running anything.
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

/// The `relation` column, checked on what the ORACLE did.
fn relation_failure(row: &Row) -> Option<String> {
    let (op, other) = match row.relation.as_str() {
        "-" => return None,
        r if r.starts_with("!=") => ("!=", &r[2..]),
        r if r.starts_with('=') => ("=", &r[1..]),
        r => return Some(format!("{}: unknown relation {r:?}", row.name)),
    };
    let same = pinned_stdout(&row.name) == pinned_stdout(other);
    match (op, same) {
        ("!=", true) => Some(format!(
            "{}: cases.tsv says it must differ from `{other}`, but the oracle \
             produced identical bytes — the flag under test changed nothing",
            row.name
        )),
        ("=", false) => Some(format!(
            "{}: cases.tsv says it must equal `{other}`, but the oracle's bytes \
             differ — the row's `=` relation is stale",
            row.name
        )),
        _ => None,
    }
}

/// Run one row through the built binary.  A row with inputs gets the harness's
/// `--with-maude` ahead of its flags; a subcommand that reads no theory finds
/// maude on `$PATH`, as the oracle's does.
fn run_row(row: &Row) -> (i32, String, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if !row.inputs.is_empty() {
        cmd.args(maude_arg());
    } else if let Some(m) = tamarin_test_support::maude_path() {
        let dir = Path::new(&m).parent().expect("maude has a directory");
        let path = std::env::var_os("PATH").unwrap_or_default();
        let joined = std::env::join_paths(
            std::iter::once(dir.to_path_buf()).chain(std::env::split_paths(&path)),
        )
        .expect("joinable PATH");
        cmd.env("PATH", joined);
    }
    let out = cmd
        .args(&row.args)
        .args(&row.inputs)
        .output()
        .expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        String::from_utf8(out.stdout).expect("utf-8 stdout"),
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
    )
}

/// Everything wrong with one row's run, or `None`.
fn row_failure(row: &Row) -> Option<String> {
    let want = pinned_stdout(&row.name);
    let (code, stdout, stderr) = run_row(row);
    let mut problems = Vec::new();
    if code != row.rc {
        problems.push(format!("exited {code}, the oracle {}", row.rc));
    }
    let got = normalize_stdout(&stdout);
    if got != want {
        let line = got
            .lines()
            .zip(want.lines())
            .position(|(g, w)| g != w)
            .unwrap_or_else(|| got.lines().count().min(want.lines().count()));
        problems.push(format!(
            "stdout leaves cli_refs/{}.stdout at line {}:\n    got  {:?}\n    want {:?}",
            row.name,
            line + 1,
            got.lines().nth(line),
            want.lines().nth(line)
        ));
    }
    for fragment in &row.stderr {
        match fragment.strip_prefix('!') {
            Some(absent) if stderr.contains(absent) => {
                problems.push(format!("stderr must not contain {absent:?}"))
            }
            None if !stderr.contains(fragment.as_str()) => {
                problems.push(format!("stderr lacks {fragment:?}"))
            }
            _ => {}
        }
    }
    (!problems.is_empty()).then(|| {
        format!(
            "{} ({:?} {:?}):\n  {}\n  stderr:\n{}",
            row.name,
            row.args,
            row.inputs,
            problems.join("\n  "),
            stderr
        )
    })
}

/// Every row: its relation on the captures, then its run against them.  The
/// rows run on a few threads at once; each run is a separate process.
#[test]
fn every_cli_ref_row_matches_the_oracle() {
    let rows = rows();
    let mut failures: Vec<String> = rows.iter().filter_map(relation_failure).collect();
    // Read every reference before the maude guard, so a missing capture fails
    // even on a machine that would skip.
    for r in &rows {
        let _ = pinned_stdout(&r.name);
    }
    if !maude_available() {
        eprintln!("skipping the runs: maude not on path");
        return;
    }
    let next = AtomicUsize::new(0);
    let found = Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism().map_or(2, |n| n.get().clamp(1, 4));
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| {
                while let Some(row) = rows.get(next.fetch_add(1, Ordering::Relaxed)) {
                    if let Some(f) = row_failure(row) {
                        found.lock().expect("failure list").push(f);
                    }
                }
            });
        }
    });
    failures.extend(found.into_inner().expect("failure list"));
    assert!(
        failures.is_empty(),
        "{} cli_refs row(s) fail:\n\n{}\n\n{}",
        failures.len(),
        failures.join("\n\n"),
        capture_provenance()
    );
}

/// The case table, the captured streams and the capture manifest must describe
/// the same set of runs.  A renamed row leaves its old reference behind, and
/// that reference still passes while it pins nothing; a half-finished capture
/// leaves rows that nobody notices.
#[test]
fn cli_ref_cases_files_and_manifest_are_in_sync() {
    let rows = rows();
    let dir = cli_refs_dir();

    let mut names: Vec<&str> = rows.iter().map(|c| c.name.as_str()).collect();
    names.sort_unstable();
    let before = names.len();
    names.dedup();
    assert_eq!(before, names.len(), "duplicate row names in cases.tsv");

    for r in &rows {
        let _ = pinned_stdout(&r.name);
        for input in &r.inputs {
            assert!(
                input.is_file(),
                "row `{}` names an input that does not exist: {}",
                r.name,
                input.display()
            );
        }
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

    let captured_rev = body
        .lines()
        .find_map(|l| l.strip_prefix("# hs_rev\t"))
        .expect("CAPTURED.tsv has no `# hs_rev` header line")
        .split_whitespace()
        .next()
        .expect("empty `# hs_rev` value");
    assert_eq!(
        captured_rev,
        tamarin_test_support::pinned_oracle_revision(),
        "{RECAPTURE_HINT}"
    );
}
