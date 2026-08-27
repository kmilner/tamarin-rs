//! Maude resolution for the workspace's maude-gated tests.
//!
//! Every crate lists this one under `[dev-dependencies]`, so a unit-test
//! module, an integration test and an example all reach the same probe.  That
//! is what a `#[cfg(test)]` module cannot offer: it is invisible to its own
//! crate's integration tests, and `pub(crate)` puts it out of reach of a
//! sibling crate.
//!
//! [`maude_path`] resolves; [`require_maude_path`] and [`maude_available`]
//! add the policy for a machine where nothing resolves.  That policy is to
//! panic.  A silent skip makes `cargo test` green in the same way with maude
//! and without it, so every maude-backed pin certifies nothing.
//! `TAM_ALLOW_NO_MAUDE=1` turns the panic back into a skip, for a machine
//! that genuinely has no maude.

/// Absolute maude locations probed when `MAUDE_PATH` is unset, ahead of
/// `$PATH`.  These two are the pair the port's own `default_maude_path`
/// (tamarin-prover's `run.rs`) walks, so a test that resolves a maude here
/// names the one the binary under test would have picked on its own.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Package-manager prefixes probed after [`MAUDE_CANDIDATES`] and `$PATH`.
/// This workspace's benchmark toolchain installs maude under linuxbrew, and
/// the homebrew prefix is where an arm64 macOS install lands; neither is on
/// the `$PATH` that every shell exports to `cargo test`.
const MAUDE_PREFIXES: [&str; 2] = [
    "/home/linuxbrew/.linuxbrew/bin/maude",
    "/opt/homebrew/bin/maude",
];

/// Environment escape hatch: `TAM_ALLOW_NO_MAUDE=1` turns the panic of
/// [`require_maude_path`] back into a skip.
const ALLOW_NO_MAUDE_ENV: &str = "TAM_ALLOW_NO_MAUDE";

/// The first `maude` on `$PATH`, if any.
fn maude_on_path() -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("maude"))
        .find(|c| c.is_file())
        .map(|c| c.to_string_lossy().into_owned())
}

/// The maude a test runs against: `$MAUDE_PATH` when set, else the first of
/// [`MAUDE_CANDIDATES`], `$PATH`, [`MAUDE_PREFIXES`] that exists.
///
/// A `MAUDE_PATH` naming a file that does not exist is a misconfiguration,
/// not a reason to skip: answering `None` there would turn every
/// maude-backed pin green on a CI whose image moved maude
/// (`.github/workflows/ci.yml` sets `MAUDE_PATH=/opt/maude/maude`).  This
/// panics instead, so the run goes red.
///
/// Resolving nothing anywhere answers `None`.  Callers that need a maude use
/// [`require_maude_path`] or [`maude_available`], which carry the policy for
/// that case; callers that only need an argv — a `--with-maude=` flag, or a
/// path handed to a server config — stay usable in a run that has no maude
/// and no maude-backed pins.
pub fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?} / $PATH / {MAUDE_PREFIXES:?}, or point it \
             at a real maude — skipping every maude-backed test would report \
             green vacuously"
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
    MAUDE_PREFIXES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
        .map(|c| (*c).to_string())
}

/// [`maude_path`] for a caller that needs a maude, so a machine where nothing
/// resolves gets a panic rather than a skipped test.  The answer is `None`
/// only under `TAM_ALLOW_NO_MAUDE=1`, which is a deliberate statement that
/// this run asserts nothing about maude.
pub fn require_maude_path() -> Option<String> {
    if let Some(p) = maude_path() {
        return Some(p);
    }
    assert_eq!(
        std::env::var(ALLOW_NO_MAUDE_ENV).as_deref(),
        Ok("1"),
        "no maude found: $MAUDE_PATH unset, none of {MAUDE_CANDIDATES:?} \
         exists, nothing named `maude` on $PATH, and none of \
         {MAUDE_PREFIXES:?}.  Every maude-backed test would report green \
         having run nothing.  Install maude, point MAUDE_PATH at it, or set \
         {ALLOW_NO_MAUDE_ENV}=1 to accept the silent skip."
    );
    None
}

/// Whether [`require_maude_path`] resolved a maude — the guard a maude-backed
/// test opens with when it has no use for the path itself.
pub fn maude_available() -> bool {
    require_maude_path().is_some()
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    /// The one file in the workspace that may read `$MAUDE_PATH`: this one.
    const PROBE: &str = "crates/tamarin-test-support/src/lib.rs";

    /// Every `.rs` file under `root`, found recursively.  The walk skips
    /// `target` directories.  It uses `std::fs` only, because a discipline
    /// scan must not add a directory-walker dependency to the crate.
    fn rs_files(root: &Path) -> Vec<PathBuf> {
        let mut files = Vec::new();
        let mut stack = vec![root.to_path_buf()];
        while let Some(dir) = stack.pop() {
            for entry in std::fs::read_dir(&dir).expect("read source dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    if path.file_name().and_then(|n| n.to_str()) != Some("target") {
                        stack.push(path);
                    }
                } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                    files.push(path);
                }
            }
        }
        files
    }

    /// No file under `crates/` outside [`PROBE`] may read `$MAUDE_PATH`.
    ///
    /// A hand-rolled copy of the probe drifts without any warning: it walks a
    /// shorter ladder, or it treats a `MAUDE_PATH` pointing at a missing file
    /// as a reason to skip.  Either way the tests it gates pass on a machine
    /// where no maude ran.  The scan walks the whole workspace because any
    /// crate can grow such a copy; a scan of one crate would police one crate.
    ///
    /// Two positive controls stop the scan itself from passing while it
    /// asserts nothing.  It checks that the walk reached [`PROBE`], and that
    /// a needle still matches inside it.
    #[test]
    fn maude_path_is_read_in_one_place() {
        // `<workspace>/crates/tamarin-test-support` -> `<workspace>`.
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
            .ancestors()
            .nth(2)
            .expect("this crate sits at <workspace>/crates/<name>");
        // The needles are built by concatenation, so this test's own source
        // is not a match and the hits counted below come from the probe.
        // There is one needle for the `var` spelling and one for the `var_os`
        // spelling, so the scan still finds a probe that moves to the
        // `OsString` API.
        let needles = [
            ["var(", "\"", "MAUDE_PATH", "\""].concat(),
            ["var_os(", "\"", "MAUDE_PATH", "\""].concat(),
        ];

        let mut offenders: Vec<String> = Vec::new();
        let mut reached = 0usize;
        let mut hits = 0usize;
        for path in rs_files(&workspace.join("crates")) {
            let rel = path
                .strip_prefix(workspace)
                .expect("scanned file lies under the workspace root");
            let text = std::fs::read_to_string(&path).expect("read source");
            let count: usize = needles.iter().map(|n| text.matches(n).count()).sum();
            if rel == Path::new(PROBE) {
                reached += 1;
                hits += count;
            } else if count > 0 {
                offenders.push(rel.display().to_string());
            }
        }

        assert_eq!(
            reached, 1,
            "the scan reached {PROBE} {reached} time(s): it walks every `.rs` \
             file under <workspace>/crates, and a scan that never opens the \
             file it is meant to police forbids nothing"
        );
        assert!(
            hits > 0,
            "no `$MAUDE_PATH` read in {PROBE}: either the probe moved (point \
             this scan at its new home) or the needles do not match the code \
             they are meant to find"
        );
        assert!(
            offenders.is_empty(),
            "these files read `$MAUDE_PATH` directly: {}.  Depend on \
             `tamarin-test-support` under `[dev-dependencies]` and call \
             `maude_path`, `require_maude_path` or `maude_available` instead \
             — a local copy drifts, and the drift shows up as a green run \
             that tested nothing.",
            offenders.join(", ")
        );
    }
}
