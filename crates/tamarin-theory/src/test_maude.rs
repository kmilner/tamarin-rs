//! The ONE maude-resolution probe every maude-gated test module in this crate
//! shares — the workspace-idiom equivalent of the integration suites'
//! `tests/common/mod.rs` helpers.  Before it existed each `_tests.rs` carried
//! its own near-identical copy, and the copies drifted (one accepted a
//! set-but-dangling `MAUDE_PATH` that the others assert on).
//!
//! `crates/tamarin-theory/tests/oracle_solver.rs` keeps a mirrored copy: an
//! integration test cannot see a `#[cfg(test)]` module of the library it
//! links.  Keep the two in sync.

/// Absolute maude locations probed when `MAUDE_PATH` is unset — the same
/// pair the rest of the workspace's maude-gated suites walk.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Probed after [`MAUDE_CANDIDATES`] and `$PATH`: this workspace's benchmark
/// toolchain installs maude under linuxbrew, which is not on a default `PATH`.
const MAUDE_BREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The first `maude` on `$PATH`, if any.
fn maude_on_path() -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("maude"))
        .find(|c| c.is_file())
        .map(|c| c.to_string_lossy().into_owned())
}

/// The maude a test runs against: `$MAUDE_PATH` when set, else the first of
/// [`MAUDE_CANDIDATES`], `$PATH`, [`MAUDE_BREW`] that exists.
///
/// A `MAUDE_PATH` naming a file that does not exist is a MISCONFIGURATION,
/// not a reason to skip — returning `None` there would turn every
/// maude-backed test green on a CI whose image moved maude.  Panic instead,
/// so the run goes red.  Resolving nothing at all is the same failure with a
/// wider blast radius, so it panics too: `TAM_ALLOW_NO_MAUDE=1` is the only
/// way to get the old silent skip, and naming it is a deliberate statement
/// that this run is not asserting anything about maude.
pub(crate) fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?}, or point it at a real maude — skipping \
             every maude-backed test would report green vacuously"
        );
        return Some(p);
    }
    if let Some(c) = MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
    {
        return Some((*c).to_string());
    }
    if let Some(p) = maude_on_path() {
        return Some(p);
    }
    if std::path::Path::new(MAUDE_BREW).exists() {
        return Some(MAUDE_BREW.to_string());
    }
    if std::env::var("TAM_ALLOW_NO_MAUDE").as_deref() == Ok("1") {
        return None;
    }
    panic!(
        "no maude found: probed $MAUDE_PATH, {MAUDE_CANDIDATES:?}, $PATH and \
         {MAUDE_BREW}.  Every maude-backed test would otherwise report green \
         having run nothing.  Install maude, point MAUDE_PATH at it, or set \
         TAM_ALLOW_NO_MAUDE=1 to accept the silent skip."
    );
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    /// The only three files in this crate allowed to read `$MAUDE_PATH`: the
    /// shared probe above, the hand-mirror an integration test needs (it
    /// links the library, so it cannot see this `#[cfg(test)]` module), and
    /// the examples' loader.  Crate-relative, `/`-separated.
    const ALLOWED: [&str; 3] = [
        "src/test_maude.rs",
        "tests/oracle_solver.rs",
        "examples/common/mod.rs",
    ];

    /// Every `.rs` file under `root`, recursively.  `std::fs` only — a
    /// discipline scan should not pull a walker dependency into the crate.
    fn rs_files(root: &Path) -> Vec<PathBuf> {
        let mut files = Vec::new();
        let mut stack = vec![root.to_path_buf()];
        while let Some(dir) = stack.pop() {
            for entry in std::fs::read_dir(&dir).expect("read source dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                    files.push(path);
                }
            }
        }
        files
    }

    /// Reading `$MAUDE_PATH` anywhere but [`ALLOWED`] is forbidden: a local
    /// copy of the probe drifts silently, and a copy that reads a dangling
    /// `MAUDE_PATH` as "skip" reports green on a box where nothing
    /// maude-backed ran.
    ///
    /// Two positive controls keep the scan itself from greening while
    /// asserting nothing: it checks that it reached each allowlisted file,
    /// and that a needle still matches inside each.
    #[test]
    fn maude_path_reads_are_confined_to_the_allowlisted_probes() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        // Built by concatenation so this test's own source is not itself a
        // match — the hit counted for `src/test_maude.rs` below then comes
        // from the real probe above, which is what the control asserts.
        // Both `var` and `var_os` spellings, so a rewrite of a probe into the
        // `OsString` API does not walk out of the allowlist.
        let needles = [
            ["var(", "\"", "MAUDE_PATH", "\""].concat(),
            ["var_os(", "\"", "MAUDE_PATH", "\""].concat(),
        ];
        // `examples/` is scanned, but its loader is allowlisted: it panics
        // (`MaudeHandle::start(...).expect`) rather than skipping, so a
        // dangling `MAUDE_PATH` there goes red instead of reporting green
        // having run nothing.
        let mut files = rs_files(&manifest.join("src"));
        files.extend(rs_files(&manifest.join("tests")));
        files.extend(rs_files(&manifest.join("examples")));

        let mut offenders: Vec<String> = Vec::new();
        // Per allowlisted file: how many times the walk reached it, and how
        // many needle matches it holds.
        let mut reached = [0usize; ALLOWED.len()];
        let mut hits = [0usize; ALLOWED.len()];
        for path in &files {
            let rel = path
                .strip_prefix(manifest)
                .expect("scanned file lies under the crate root");
            let text = std::fs::read_to_string(path).expect("read source");
            let count: usize = needles.iter().map(|n| text.matches(n).count()).sum();
            match ALLOWED.iter().position(|a| rel == Path::new(a)) {
                Some(i) => {
                    reached[i] += 1;
                    hits[i] += count;
                }
                None if count > 0 => offenders.push(rel.display().to_string()),
                None => {}
            }
        }

        for (i, allowed) in ALLOWED.iter().enumerate() {
            assert_eq!(
                reached[i], 1,
                "the scan reached {allowed} {} time(s): it walks \
                 <crate>/src, <crate>/tests and <crate>/examples, and a scan \
                 that never opens the files it is meant to police forbids \
                 nothing",
                reached[i]
            );
            assert!(
                hits[i] > 0,
                "no `$MAUDE_PATH` read left in {allowed}: either the probe \
                 moved (point this scan at its new home) or the needles no \
                 longer match the code they are meant to find"
            );
        }

        assert!(
            offenders.is_empty(),
            "these files read `$MAUDE_PATH` directly: {}.  New copies of the \
             probe drift — the audit behind this scan found several that \
             accepted a set-but-dangling MAUDE_PATH and silently skipped, so \
             every maude-backed test they gated reported green having run \
             nothing.  Call `crate::test_maude::maude_path` instead, or, from \
             an integration test (which cannot see a `#[cfg(test)]` module of \
             the library it links), use the documented hand-mirror in \
             `tests/oracle_solver.rs`.",
            offenders.join(", ")
        );
    }
}
