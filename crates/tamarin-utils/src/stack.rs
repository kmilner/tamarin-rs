//! Stack growth for recursive compiler and parser walks.
//!
//! Stack switching is available on the targets supported by `stacker`'s
//! `psm` backend. On other targets `stacker` executes the closure in place;
//! these helpers cannot add stack.

/// Run `f` with enough native stack for another recursive section.
///
/// These values follow rustc's `ensure_sufficient_stack`: leave a 100 KiB
/// red zone and allocate a 1 MiB segment when it is crossed. AIX needs the
/// larger segment because LLVM does not provide tail-call optimisation there.
#[inline]
pub fn ensure_sufficient_stack<T>(f: impl FnOnce() -> T) -> T {
    let segment = if cfg!(target_os = "aix") {
        16 * 1024 * 1024
    } else {
        1024 * 1024
    };
    stacker::maybe_grow(100 * 1024, segment, f)
}

/// Run a compiler phase with enough stack for recursive temporary values whose
/// derived destructors cannot call [`ensure_sufficient_stack`].
///
/// The 64 MiB red zone matches this project's Rayon and server worker stacks
/// and covers the larger frames used by SAPIC typing and translation. The
/// extra MiB keeps nested phase wrappers on the same freshly allocated stack.
#[inline]
pub fn with_compiler_stack<T>(f: impl FnOnce() -> T) -> T {
    stacker::maybe_grow(64 * 1024 * 1024, 65 * 1024 * 1024, f)
}
