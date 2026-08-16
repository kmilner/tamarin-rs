//! The ONE maude-resolution probe every maude-gated test module in this crate
//! shares — the workspace-idiom equivalent of the integration suites'
//! `tests/common/mod.rs` helpers.  Before it existed each `_tests.rs` carried
//! its own near-identical copy, and the copies drifted (one accepted a
//! set-but-dangling `MAUDE_PATH` that the others assert on).
//!
//! `crates/tamarin-theory/tests/oracle_solver.rs` keeps a mirrored copy: an
//! integration test cannot see a `#[cfg(test)]` module of the library it
//! links.  Keep the two in sync.
//!
//! The same structural barrier keeps a handful of copies alive in the other
//! crates (a sibling crate cannot reach this `pub(crate)` module either), so
//! the discipline scan in this file's `tests` module polices the WHOLE
//! workspace rather than this crate alone — its `ALLOWED` array is the roster
//! of sanctioned copies and records what each one owes.

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

    /// Every file in the WORKSPACE allowed to read `$MAUDE_PATH`, and why the
    /// copy has to exist there.  Workspace-relative, `/`-separated.
    ///
    /// Each entry is a structural barrier, not a convenience: a `#[cfg(test)]`
    /// module of a library is invisible to that library's own integration
    /// tests, a `tests/common/mod.rs` is invisible to `src/`, and this
    /// module is `pub(crate)` so no sibling crate can call it.
    ///
    /// - `crates/tamarin-theory/src/test_maude.rs` — the shared probe above.
    /// - `crates/tamarin-theory/tests/oracle_solver.rs` — the integration
    ///   mirror of that probe.
    /// - `crates/tamarin-theory/examples/common/mod.rs` — the examples'
    ///   loader; see [`SKIPS_SILENTLY`] for why it is not in [`MUST_BE_LOUD`].
    /// - `crates/tamarin-server/tests/common/mod.rs` — the server suites'
    ///   harness (its loud half is `maude_available`).
    /// - `crates/tamarin-server/tests/theory_io_ndc.rs` — a single-file pin
    ///   that does not pull in `common`.
    /// - `crates/tamarin-server/src/handlers/proof_tree.rs` — the server
    ///   library's own `#[cfg(test)]` module.
    /// - `crates/tamarin-prover/tests/common/mod.rs` — the CLI e2e harness
    ///   (its loud half is `maude_available`).
    /// - `crates/tamarin-term/src/{maude_proc_tests,norm_tests}.rs` — the
    ///   bottom crate's own `#[cfg(test)]` probes; both are in
    ///   [`SKIPS_SILENTLY`].
    const ALLOWED: [&str; 9] = [
        "crates/tamarin-prover/tests/common/mod.rs",
        "crates/tamarin-server/src/handlers/proof_tree.rs",
        "crates/tamarin-server/tests/common/mod.rs",
        "crates/tamarin-server/tests/theory_io_ndc.rs",
        "crates/tamarin-term/src/maude_proc_tests.rs",
        "crates/tamarin-term/src/norm_tests.rs",
        "crates/tamarin-theory/examples/common/mod.rs",
        "crates/tamarin-theory/src/test_maude.rs",
        "crates/tamarin-theory/tests/oracle_solver.rs",
    ];

    /// The [`ALLOWED`] probes that resolve no maude by PANICKING, and so must
    /// name the `TAM_ALLOW_NO_MAUDE` opt-out that converts the panic back into
    /// a deliberate skip.  This is the settled semantics: unset `MAUDE_PATH`
    /// may fall through the candidate ladder, a SET-but-dangling one must
    /// panic, and resolving nothing at all must panic unless the opt-out is
    /// named.
    const MUST_BE_LOUD: [&str; 6] = [
        "crates/tamarin-prover/tests/common/mod.rs",
        "crates/tamarin-server/src/handlers/proof_tree.rs",
        "crates/tamarin-server/tests/common/mod.rs",
        "crates/tamarin-server/tests/theory_io_ndc.rs",
        "crates/tamarin-theory/src/test_maude.rs",
        "crates/tamarin-theory/tests/oracle_solver.rs",
    ];

    /// The [`ALLOWED`] probes that do NOT carry the loud policy, frozen so the
    /// set can only shrink.  `ALLOWED` minus [`MUST_BE_LOUD`] must equal this
    /// list exactly, in both directions.
    ///
    /// - `crates/tamarin-theory/examples/common/mod.rs` never skips at all: it
    ///   hands whatever it resolved (a bare `maude` when `MAUDE_PATH` is
    ///   unset) to `MaudeHandle::start(..).expect(..)`, so a dangling or
    ///   missing maude aborts the example rather than reporting a green run.
    ///   It has no opt-out because it has nothing to opt out of.
    /// - the two `crates/tamarin-term/src/*_tests.rs` probes DO silently skip
    ///   when nothing resolves, and `norm_tests.rs`'s ladder is the
    ///   narrowest in the workspace (`/usr/local/bin/maude` and a relative
    ///   `maude`, no `$PATH` walk and no linuxbrew prefix), so on a box whose
    ///   maude lives anywhere else its two pins report green having reduced
    ///   nothing.  Listing them here freezes the debt: a tenth copy cannot
    ///   join them without editing this array.
    const SKIPS_SILENTLY: [&str; 3] = [
        "crates/tamarin-term/src/maude_proc_tests.rs",
        "crates/tamarin-term/src/norm_tests.rs",
        "crates/tamarin-theory/examples/common/mod.rs",
    ];

    /// Every `.rs` file under `root`, recursively, skipping `target`
    /// directories.  `std::fs` only — a discipline scan should not pull a
    /// walker dependency into the crate.
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

    /// Reading `$MAUDE_PATH` anywhere in the workspace but [`ALLOWED`] is
    /// forbidden: a local copy of the probe drifts silently, and a copy that
    /// reads a dangling `MAUDE_PATH` as "skip" reports green on a box where
    /// nothing maude-backed ran.
    ///
    /// The scan is workspace-wide because the drift was: the audit behind it
    /// deleted seven copies spread over five crates, and a crate-local scan
    /// would have seen one of them.  It also enforces the semantics, not just
    /// the head-count — every [`MUST_BE_LOUD`] probe has to name the
    /// `TAM_ALLOW_NO_MAUDE` opt-out, and the complement has to be exactly the
    /// [`SKIPS_SILENTLY`] roster, so the silent-skip debt can only shrink.
    ///
    /// Two positive controls keep the scan itself from greening while
    /// asserting nothing: it checks that it reached each allowlisted file,
    /// and that a needle still matches inside each.
    #[test]
    fn maude_path_reads_are_confined_to_the_allowlisted_probes() {
        // `<workspace>/crates/tamarin-theory` -> `<workspace>`.
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
            .ancestors()
            .nth(2)
            .expect("this crate sits at <workspace>/crates/<name>");
        // Built by concatenation so this test's own source is not itself a
        // match — the hit counted for `src/test_maude.rs` below then comes
        // from the real probe above, which is what the control asserts.
        // Both `var` and `var_os` spellings, so a rewrite of a probe into the
        // `OsString` API does not walk out of the allowlist.
        let needles = [
            ["var(", "\"", "MAUDE_PATH", "\""].concat(),
            ["var_os(", "\"", "MAUDE_PATH", "\""].concat(),
        ];
        // Same trick: this array's own source must not satisfy the loud check
        // for a file that does not really carry the opt-out.
        let loud_needle = ["TAM_ALLOW_", "NO_MAUDE"].concat();
        let files = rs_files(&workspace.join("crates"));

        let mut offenders: Vec<String> = Vec::new();
        // Per allowlisted file: how many times the walk reached it, how many
        // needle matches it holds, and whether it names the opt-out.
        let mut reached = [0usize; ALLOWED.len()];
        let mut hits = [0usize; ALLOWED.len()];
        let mut loud = [false; ALLOWED.len()];
        for path in &files {
            let rel = path
                .strip_prefix(workspace)
                .expect("scanned file lies under the workspace root");
            let text = std::fs::read_to_string(path).expect("read source");
            let count: usize = needles.iter().map(|n| text.matches(n).count()).sum();
            match ALLOWED.iter().position(|a| rel == Path::new(a)) {
                Some(i) => {
                    reached[i] += 1;
                    hits[i] += count;
                    loud[i] = text.contains(&loud_needle);
                }
                None if count > 0 => offenders.push(rel.display().to_string()),
                None => {}
            }
        }

        for (i, allowed) in ALLOWED.iter().enumerate() {
            assert_eq!(
                reached[i], 1,
                "the scan reached {allowed} {} time(s): it walks every `.rs` \
                 file under <workspace>/crates, and a scan that never opens \
                 the files it is meant to police forbids nothing",
                reached[i]
            );
            assert!(
                hits[i] > 0,
                "no `$MAUDE_PATH` read left in {allowed}: either the probe \
                 moved (point this scan at its new home) or the needles no \
                 longer match the code they are meant to find"
            );
            let expected_loud = !SKIPS_SILENTLY.contains(allowed);
            assert_eq!(
                MUST_BE_LOUD.contains(allowed),
                expected_loud,
                "{allowed} is listed in neither or both of MUST_BE_LOUD and \
                 SKIPS_SILENTLY: every allowlisted probe belongs to exactly \
                 one of the two"
            );
            assert_eq!(
                loud[i],
                expected_loud,
                "{allowed} {} the TAM_ALLOW_NO_MAUDE opt-out.  A probe that \
                 panics when nothing resolves must offer it (that is the only \
                 sanctioned way to get the silent skip back); a probe listed \
                 in SKIPS_SILENTLY must not pretend to — if this one was just \
                 made strict, move it from SKIPS_SILENTLY to MUST_BE_LOUD",
                if loud[i] { "names" } else { "never names" }
            );
        }

        assert!(
            offenders.is_empty(),
            "these files read `$MAUDE_PATH` directly: {}.  New copies of the \
             probe drift — the audit behind this scan found several that \
             accepted a set-but-dangling MAUDE_PATH and silently skipped, so \
             every maude-backed test they gated reported green having run \
             nothing.  Call `crate::test_maude::maude_path` instead; from an \
             integration test (which cannot see a `#[cfg(test)]` module of \
             the library it links) or another crate (this module is \
             `pub(crate)`), copy one of the ALLOWED probes VERBATIM and add \
             it there, opt-out and all.",
            offenders.join(", ")
        );
    }
}
