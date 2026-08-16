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
