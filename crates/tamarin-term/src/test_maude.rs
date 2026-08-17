//! The single maude-resolution probe that this crate's maude-gated test
//! modules share.  It is the bottom-crate twin of `tamarin-theory`'s
//! `test_maude`.  That twin also owns the workspace-wide discipline scan
//! that rosters this file.
//!
//! `maude_proc_tests.rs` and `norm_tests.rs` both use this one probe, so
//! their resolution rules cannot drift apart.  A private copy in a single
//! module is easy to get wrong.  Such a copy can accept a `MAUDE_PATH` that
//! is set but dangling.  It can also walk a two-entry ladder whose second
//! entry is a relative `maude` tested with `Path::exists`.  That ladder
//! consults neither `$PATH` nor the linuxbrew prefix.  It answers `None` on
//! any machine that keeps maude outside `/usr/local/bin`.  The tests of that
//! module then pass without reducing any term.

/// The absolute maude locations that this module probes when `MAUDE_PATH` is
/// unset.  The port's own `default_maude_path` (tamarin-prover's `run.rs`)
/// walks the same pair.  It then falls back to the plain command name
/// `maude`.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// This module probes this path after [`MAUDE_CANDIDATES`] and `$PATH`.
/// This workspace's benchmark toolchain installs maude under linuxbrew.
/// That directory is not on a default `PATH`.
const MAUDE_BREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The first `maude` on `$PATH`, if any.
fn maude_on_path() -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join("maude"))
        .find(|c| c.is_file())
        .map(|c| c.to_string_lossy().into_owned())
}

/// The maude these tests run against, or `None` when the machine has none.
///
/// A `MAUDE_PATH` that names a file which does not exist is a
/// misconfiguration.  It is not a reason to skip the tests.  An answer of
/// `None` there would make every maude-backed pin in this crate pass on a CI
/// image that moved maude.  CI sets `MAUDE_PATH` in
/// `.github/workflows/ci.yml`.  This function panics instead, so the run
/// fails.
pub(crate) fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to the \
             probe, or point it at a real maude — skipping every \
             maude-backed pin here would report green vacuously"
        );
        return Some(p);
    }
    MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
        .map(|c| (*c).to_string())
        .or_else(maude_on_path)
        .or_else(|| {
            std::path::Path::new(MAUDE_BREW)
                .exists()
                .then(|| MAUDE_BREW.to_string())
        })
}
