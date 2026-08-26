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
//! The same structural barrier keeps a small number of copies alive in the
//! other crates.  A sibling crate cannot reach this `pub(crate)` module
//! either.  So the discipline scan in this file's `tests` module checks the
//! complete workspace, not this crate alone.  Its `ALLOWED` array lists the
//! sanctioned copies.  The array also records the obligation that each copy
//! carries.

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

    /// Every file in the workspace that may read `$MAUDE_PATH`, and why the
    /// copy must exist there.  The paths are workspace-relative and
    /// `/`-separated.
    ///
    /// Each entry exists because of a structural barrier, not for
    /// convenience.  A `#[cfg(test)]` module of a library is not visible to
    /// that library's own integration tests.  A `tests/common/mod.rs` is not
    /// visible to `src/`.  This module is `pub(crate)`, so no sibling crate
    /// can call it.
    ///
    /// - `crates/tamarin-theory/src/test_maude.rs` — the shared probe above.
    /// - `crates/tamarin-theory/tests/intruder_variants_render.rs` — the
    ///   `tamarin-prover variants` byte pin, which generates the DH and BP
    ///   intruder rules through two maude handles of its own.
    /// - `crates/tamarin-theory/tests/oracle_solver.rs` — the integration
    ///   mirror of that probe.
    /// - `crates/tamarin-theory/tests/rule_variants_report.rs` — the
    ///   `ruleVariantsReport` pin, which needs a handle on the probe theory's
    ///   own signature.
    /// - `crates/tamarin-theory/examples/common/mod.rs` — the loader for the
    ///   examples.  See [`SKIPS_SILENTLY`] for why it is not in
    ///   [`MUST_BE_LOUD`].
    /// - `crates/tamarin-server/tests/common/mod.rs` — the harness for the
    ///   server suites.  Its half that panics is `maude_available`.
    /// - `crates/tamarin-server/tests/theory_io_ndc.rs` — a pin in a single
    ///   file that does not use `common`.
    /// - `crates/tamarin-server/src/handlers/proof_tree.rs` — the server
    ///   library's own `#[cfg(test)]` module.
    /// - `crates/tamarin-prover/tests/common/mod.rs` — the harness for the
    ///   end-to-end CLI tests.  Its half that panics is `maude_available`.
    /// - `crates/tamarin-term/src/test_maude.rs` — the bottom crate's own
    ///   shared probe, and the twin of this file.  It is in
    ///   [`SKIPS_SILENTLY`].
    const ALLOWED: [&str; 10] = [
        "crates/tamarin-prover/tests/common/mod.rs",
        "crates/tamarin-server/src/handlers/proof_tree.rs",
        "crates/tamarin-server/tests/common/mod.rs",
        "crates/tamarin-server/tests/theory_io_ndc.rs",
        "crates/tamarin-term/src/test_maude.rs",
        "crates/tamarin-theory/examples/common/mod.rs",
        "crates/tamarin-theory/src/test_maude.rs",
        "crates/tamarin-theory/tests/intruder_variants_render.rs",
        "crates/tamarin-theory/tests/oracle_solver.rs",
        "crates/tamarin-theory/tests/rule_variants_report.rs",
    ];

    /// The [`ALLOWED`] probes that panic when they resolve no maude.  Each of
    /// them must name the `TAM_ALLOW_NO_MAUDE` opt-out.  That opt-out turns
    /// the panic back into a deliberate skip.
    ///
    /// These are the agreed rules.  An unset `MAUDE_PATH` may fall through
    /// the ladder of candidates.  A `MAUDE_PATH` that is set but names a file
    /// that does not exist must panic.  A probe that resolves nothing at all
    /// must also panic, unless the opt-out is named.
    const MUST_BE_LOUD: [&str; 8] = [
        "crates/tamarin-prover/tests/common/mod.rs",
        "crates/tamarin-server/src/handlers/proof_tree.rs",
        "crates/tamarin-server/tests/common/mod.rs",
        "crates/tamarin-server/tests/theory_io_ndc.rs",
        "crates/tamarin-theory/src/test_maude.rs",
        "crates/tamarin-theory/tests/intruder_variants_render.rs",
        "crates/tamarin-theory/tests/oracle_solver.rs",
        "crates/tamarin-theory/tests/rule_variants_report.rs",
    ];

    /// The [`ALLOWED`] probes that do not carry the policy of
    /// [`MUST_BE_LOUD`].  The list is fixed, so the set can only get smaller.
    /// `ALLOWED` minus [`MUST_BE_LOUD`] must equal this list exactly, in both
    /// directions.
    ///
    /// - `crates/tamarin-theory/examples/common/mod.rs` never skips.  It
    ///   passes whatever it resolved to `MaudeHandle::start(..).expect(..)`.
    ///   When `MAUDE_PATH` is unset, that value is a bare `maude`.  So the
    ///   example stops with an error when `MAUDE_PATH` names a file that does
    ///   not exist, and also when no maude is found at all.  It does not
    ///   report a passing run.  The file has no opt-out because it has
    ///   nothing to opt out of.
    /// - `crates/tamarin-term/src/test_maude.rs` asserts when `MAUDE_PATH` is
    ///   set but names a file that does not exist, like the probes that
    ///   panic.  But it still returns `None`, which is a silent skip, when
    ///   its ladder resolves nothing.  This entry records that exception and
    ///   holds the set fixed.  A ninth copy cannot join without an edit to
    ///   this array.
    const SKIPS_SILENTLY: [&str; 2] = [
        "crates/tamarin-term/src/test_maude.rs",
        "crates/tamarin-theory/examples/common/mod.rs",
    ];

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

    /// No file in the workspace outside [`ALLOWED`] may read `$MAUDE_PATH`.
    /// A local copy of the probe can become different from this one without
    /// any warning.  A copy can also treat a `MAUDE_PATH` that points at a
    /// missing file as a reason to skip.  That copy then passes on a machine
    /// where no maude-backed test ran.
    ///
    /// The scan covers the whole workspace because the copies were spread
    /// over the whole workspace.  The audit behind this scan deleted seven
    /// copies in five crates.  A scan of one crate would have found only one
    /// of them.  The scan also checks the semantics, not only the number of
    /// copies.  Every [`MUST_BE_LOUD`] probe must name the
    /// `TAM_ALLOW_NO_MAUDE` opt-out.  The rest must be exactly the
    /// [`SKIPS_SILENTLY`] list, so the number of silent skips can only get
    /// smaller.
    ///
    /// Two positive controls stop the scan itself from passing while it
    /// asserts nothing.  It checks that it reached each allowlisted file.  It
    /// also checks that a needle still matches inside each file.
    #[test]
    fn maude_path_reads_are_confined_to_the_allowlisted_probes() {
        // `<workspace>/crates/tamarin-theory` -> `<workspace>`.
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
            .ancestors()
            .nth(2)
            .expect("this crate sits at <workspace>/crates/<name>");
        // The test builds the needles by concatenation, so its own source is
        // not a match.  The hit counted for `src/test_maude.rs` below then
        // comes from the real probe above.  That is what the control asserts.
        // There is one needle for the `var` spelling and one for the `var_os`
        // spelling.  So the scan still finds a probe that moves to the
        // `OsString` API.
        let needles = [
            ["var(", "\"", "MAUDE_PATH", "\""].concat(),
            ["var_os(", "\"", "MAUDE_PATH", "\""].concat(),
        ];
        // The same method applies here.  This array's own source must not
        // satisfy the opt-out check for a file that does not carry the
        // opt-out.
        let loud_needle = ["TAM_ALLOW_", "NO_MAUDE"].concat();
        let files = rs_files(&workspace.join("crates"));

        let mut offenders: Vec<String> = Vec::new();
        // These arrays hold one entry for each allowlisted file.  They record
        // how many times the walk reached the file, how many needle matches
        // the file holds, and whether the file names the opt-out.
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
