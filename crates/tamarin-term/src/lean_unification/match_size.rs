//! Exclude a directional match by comparing rigid sizes.
use super::{Error, LEAN_THREAD};

use tamarin_algebra_sys::tamarin_match_size_excludes;

pub(super) fn excludes(pattern: u64, subject: u64) -> Result<bool, Error> {
    super::initialize()?;
    // SAFETY: the export takes two unboxed UInt64 words and returns a Bool.
    match LEAN_THREAD.with(|_| unsafe { tamarin_match_size_excludes(pattern, subject) }) {
        0 => Ok(false),
        1 => Ok(true),
        other => Err(Error::InvalidStatus(other)),
    }
}
