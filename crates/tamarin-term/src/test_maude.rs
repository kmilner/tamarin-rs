//! The ONE maude-resolution probe this crate's maude-gated test modules
//! share — the bottom-crate twin of `tamarin-theory`'s `test_maude`, which
//! also owns the workspace-wide discipline scan that rosters this file.
//!
//! Before it existed `maude_proc_tests.rs` and `norm_tests.rs` carried their
//! own copies and they had drifted apart: the `norm_tests.rs` one accepted a
//! set-but-dangling `MAUDE_PATH` and walked a two-entry ladder whose second
//! entry was a RELATIVE `maude` tested with `Path::exists`, so it consulted
//! neither `$PATH` nor the linuxbrew prefix and answered `None` on any box
//! keeping maude outside `/usr/local/bin` — reporting its pins green having
//! reduced nothing.

/// Absolute maude locations probed when `MAUDE_PATH` is unset — the pair the
/// port's own `default_maude_path` (tamarin-prover's `run.rs`) walks before
/// it falls back to a bare `maude`.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Probed after [`MAUDE_CANDIDATES`] and `$PATH`: this workspace's benchmark
/// toolchain installs maude under linuxbrew, which is not on a default
/// `PATH`.
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
/// A `MAUDE_PATH` naming a file that does not exist is a MISCONFIGURATION,
/// not a reason to skip — answering `None` there would turn every
/// maude-backed pin in this crate green on a CI whose image moved maude
/// (`.github/workflows/ci.yml` sets `MAUDE_PATH`).  Panic instead, so the run
/// goes red.
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
