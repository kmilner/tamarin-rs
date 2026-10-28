//! Opt-in batch supervisor. The same executable runs the proof in a separate
//! process group; the parent samples that group's RSS and owns its lifetime.
//! No allocator hooks or solver changes are needed. This is a sampled stop
//! threshold, not an OS-enforced cap, and does not recover unfinished proofs.

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod unix;

/// Return None in the supervised child or when no limit was requested.
/// Other platforms fail explicitly instead of running without protection.
pub fn run(raw: &[String], limit: Option<u64>) -> Option<std::io::Result<u8>> {
    let limit = limit.filter(|n| *n > 0)?;
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        if unix::is_worker() {
            return None;
        }
        Some(unix::run(raw, limit))
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = (raw, limit);
        Some(Err(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "--memory-limit is supported only on Linux and macOS",
        )))
    }
}
