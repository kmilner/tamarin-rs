// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `System.Timing` from `lib/utils/src/System/Timing.hs`.
//!
//! The original `timed`/`timedIO` rely on Haskell's `deepseq` to force
//! lazy values before measuring. Rust evaluates eagerly, so we just measure
//! the wall-clock duration of running a closure.
//!
//! Retained as a faithful mirror of the upstream Haskell module; the
//! prover does not currently call `timed`.

use std::time::{Duration, Instant};

/// Run `f` and return its result alongside the elapsed wall-clock time.
pub fn timed<F: FnOnce() -> T, T>(f: F) -> (T, Duration) {
    let t0 = Instant::now();
    let value = f();
    (value, t0.elapsed())
}
