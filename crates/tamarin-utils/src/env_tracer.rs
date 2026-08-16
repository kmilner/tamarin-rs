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

/// HS `traceSettings` (EnvTracer.hs:22-23#traceSettings).
const TRACE_SETTINGS: &str = "DEBUG_TRACE";

/// HS `shouldTrace`'s body once the lookup is done (EnvTracer.hs:30-32):
/// `Nothing` is `False`, and `Just setting` is whole-field membership of
/// `traceKey` in `splitOn "," setting`.  `setting` is what `lookupEnv`
/// answered.
///
/// Split out from [`should_trace`] so a test can drive the parse from a
/// literal: `DEBUG_TRACE` is process-wide, and a test that wrote it would
/// make every other env-reading test in this crate's test binary flaky.
fn should_trace_setting(setting: Option<&str>, key: &str) -> bool {
    match setting {
        Some(s) => s.split(',').any(|k| k == key),
        None => false,
    }
}

/// Whether `key` should be traced according to the current environment.
pub fn should_trace(key: &str) -> bool {
    should_trace_setting(env::var(TRACE_SETTINGS).ok().as_deref(), key)
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

    /// The variable [`should_trace`] looks up: HS `traceSettings`
    /// (EnvTracer.hs:22-23#traceSettings).  Renaming it would silently
    /// disable every `DEBUG_TRACE=...` invocation upstream documents.
    #[test]
    fn trace_settings_names_the_hs_environment_variable() {
        assert_eq!(TRACE_SETTINGS, "DEBUG_TRACE");
    }

    /// HS `shouldTrace` (EnvTracer.hs:26-32#shouldTrace).  Every expectation
    /// below was run through `split-0.2.5` under the pinned GHC 9.6.7:
    /// `splitOn "," "" == [""]` and `splitOn "," "a,,b" == ["a","","b"]`, so
    /// an empty field is a real field and the empty key matches it.
    ///
    /// Driven through [`should_trace_setting`] rather than `env::set_var`:
    /// `DEBUG_TRACE` is process-wide, so mutating it here would race any
    /// other env-reading test this binary grows.
    #[test]
    fn trace_keys_are_whole_comma_separated_fields() {
        // `Nothing -> False`: no setting disables every key.
        assert!(!should_trace_setting(None, "anything"));
        assert!(!should_trace_setting(None, ""));

        // `Just setting`: membership of the key in `splitOn "," setting`.
        assert!(should_trace_setting(Some("foo,bar"), "foo"));
        assert!(should_trace_setting(Some("foo,bar"), "bar"));
        // Whole fields: neither a prefix of a field nor the raw setting
        // itself is a match.
        assert!(!should_trace_setting(Some("foo,bar"), "fo"));
        assert!(!should_trace_setting(Some("foo,bar"), "foo,bar"));
        assert!(!should_trace_setting(Some("foo,bar"), ""));

        // A single unseparated key is one field, not a substring search.
        assert!(should_trace_setting(Some("foobar"), "foobar"));
        assert!(!should_trace_setting(Some("foobar"), "foo"));

        // `splitOn` never answers an empty list, and it keeps empty fields:
        // `DEBUG_TRACE=` and `DEBUG_TRACE=a,,b` both enable the empty key.
        assert!(should_trace_setting(Some(""), ""));
        assert!(!should_trace_setting(Some(""), "foo"));
        assert!(should_trace_setting(Some("a,,b"), ""));
        assert!(should_trace_setting(Some("a,,b"), "b"));
    }
}
