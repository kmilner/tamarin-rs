//! `env_gate!(NAME)` — a cached presence test for a diagnostic env var.
//!
//! Expands to a per-call-site `OnceLock<bool>` that is initialised on first
//! use from `std::env::var(NAME).is_ok()`.  These gates are all diagnostic
//! switches that are set once at process start and never change during a run,
//! so reading them exactly once and caching the boolean is behaviour-
//! preserving — it only removes the repeated per-hit syscall/allocation from
//! hot solver paths.  Presence-only (`is_ok`) gates route through this macro;
//! flags that test a VALUE (e.g. `equation_store`'s
//! `aes_dbg_filter_substantive` `== "substantive"` match) keep hand-rolled
//! `OnceLock` caches, since the macro deliberately has no value hook.
//!
//! The macro is `#[macro_export]`, so it lives at the crate root
//! (`tamarin_utils::env_gate!`) regardless of this module; the module merely
//! holds the definition and this documentation.

/// Cached presence test for a diagnostic environment variable.
///
/// `env_gate!("TAM_DBG_FOO")` evaluates `std::env::var("TAM_DBG_FOO").is_ok()`
/// exactly once (on first reach of that call site) and returns the cached
/// `bool` on every subsequent call.
#[macro_export]
macro_rules! env_gate {
    ($name:expr) => {{
        static GATE: ::std::sync::OnceLock<bool> = ::std::sync::OnceLock::new();
        *GATE.get_or_init(|| ::std::env::var($name).is_ok())
    }};
}
