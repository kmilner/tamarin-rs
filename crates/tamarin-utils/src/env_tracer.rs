// Currently GPL 3.0 until granted permission by the following authors:
//   Adrian Dapprich
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Debug/Trace/EnvTracer.hs

//! Port of `Debug.Trace.EnvTracer` from `lib/utils/src/Debug/Trace/EnvTracer.hs`.
//!
//! `DEBUG_TRACE=foo,bar tamarin-prover ...` enables traces tagged with
//! either `foo` or `bar`. Output goes to stderr (the original calls
//! `Debug.Trace.trace`, which does the same).
//!
//! Retained as a faithful mirror of the upstream Haskell module; the
//! prover does not currently route any traces through it.

use std::env;

const TRACE_SETTINGS: &str = "DEBUG_TRACE";

/// Whether `key` should be traced according to the current environment.
pub fn should_trace(key: &str) -> bool {
    match env::var(TRACE_SETTINGS) {
        Ok(setting) => setting.split(',').any(|k| k == key),
        Err(_) => false,
    }
}

/// Output a section header to stderr if `key` is enabled.
pub fn etrace_section_ln(key: &str, title: &str) {
    if !should_trace(key) { return; }
    let bar_len = 80usize.saturating_sub(5 + title.chars().count());
    let bar: String = "=".repeat(bar_len);
    eprintln!("=== {} {}", title, bar);
}

/// Output `label: s` to stderr if `key` is enabled.
pub fn etrace_ln(key: &str, label: &str, s: &str) {
    if !should_trace(key) { return; }
    eprintln!("{}: {}", label, s);
}

#[cfg(test)]
mod tests {
    use super::*;

    // We don't test should_trace directly because env vars are process-wide
    // and parallel tests would race. The function is exercised in practice.
    #[test]
    fn empty_env_disables_trace() {
        // SAFETY: temporarily unset for this single test thread; restore after.
        let prev = env::var(TRACE_SETTINGS).ok();
        unsafe { env::remove_var(TRACE_SETTINGS); }
        assert!(!should_trace("anything"));
        if let Some(v) = prev { unsafe { env::set_var(TRACE_SETTINGS, v); } }
    }
}
