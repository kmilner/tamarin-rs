// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
    if !should_trace(key) {
        return;
    }
    let bar_len = 80usize.saturating_sub(5 + title.chars().count());
    let bar: String = "=".repeat(bar_len);
    eprintln!("=== {} {}", title, bar);
}

/// Output `label: s` to stderr if `key` is enabled.
pub fn etrace_ln(key: &str, label: &str, s: &str) {
    if !should_trace(key) {
        return;
    }
    eprintln!("{}: {}", label, s);
}

#[cfg(test)]
mod tests {
    use super::*;

    // `DEBUG_TRACE` is process-wide, so every assertion that depends on it
    // lives in this single test rather than racing across parallel ones.
    #[test]
    fn trace_keys_are_whole_comma_separated_fields() {
        // SAFETY: temporarily overwritten for this single test thread; the
        // previous value is restored before returning.
        let prev = env::var(TRACE_SETTINGS).ok();
        unsafe {
            env::remove_var(TRACE_SETTINGS);
        }
        assert!(!should_trace("anything"), "unset must disable tracing");

        unsafe {
            env::set_var(TRACE_SETTINGS, "foo,bar");
        }
        assert!(should_trace("foo"));
        assert!(should_trace("bar"));
        // HS `elem key (splitOn "," setting)` compares whole fields: neither a
        // prefix of a field nor the raw setting itself is a match.
        assert!(!should_trace("fo"));
        assert!(!should_trace("foo,bar"));
        assert!(!should_trace(""));

        // A single unseparated key is one field, not a substring search.
        unsafe {
            env::set_var(TRACE_SETTINGS, "foobar");
        }
        assert!(should_trace("foobar"));
        assert!(!should_trace("foo"));

        match prev {
            Some(v) => unsafe { env::set_var(TRACE_SETTINGS, v) },
            None => unsafe { env::remove_var(TRACE_SETTINGS) },
        }
    }
}
