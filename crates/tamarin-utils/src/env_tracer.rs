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

/// The body of HS `shouldTrace` after the lookup (EnvTracer.hs:30-32).
/// `Nothing` gives `False`.  For `Just setting`, the result is true when
/// `traceKey` is one complete field of `splitOn "," setting`.  `setting` is
/// the answer of `lookupEnv`.
///
/// This function is separate from [`should_trace`] so that a test can run
/// the parse from a literal.  `DEBUG_TRACE` is process-wide.  A test that
/// wrote it would make every other test in this crate's test binary that
/// reads the environment flaky.
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

    /// The variable that [`should_trace`] looks up.  It is HS
    /// `traceSettings` (EnvTracer.hs:22-23#traceSettings).  A different name
    /// disables every `DEBUG_TRACE=...` invocation that upstream documents,
    /// and the user gets no message about it.
    #[test]
    fn trace_settings_names_the_hs_environment_variable() {
        assert_eq!(TRACE_SETTINGS, "DEBUG_TRACE");
    }

    /// HS `shouldTrace` (EnvTracer.hs:26-32#shouldTrace).  A run of
    /// `split-0.2.5` under the pinned GHC 9.6.7 confirms every expectation
    /// below: `splitOn "," "" == [""]` and
    /// `splitOn "," "a,,b" == ["a","","b"]`.  An empty field is therefore a
    /// real field, and the empty key matches it.
    ///
    /// The test calls [`should_trace_setting`] instead of `env::set_var`.
    /// `DEBUG_TRACE` is process-wide.  A change to it here would race any
    /// other test in this binary that reads the environment.
    #[test]
    fn trace_keys_are_whole_comma_separated_fields() {
        // `Nothing -> False`.  With no setting, the function disables
        // every key.
        assert!(!should_trace_setting(None, "anything"));
        assert!(!should_trace_setting(None, ""));

        // `Just setting`.  The key must be a member of `splitOn "," setting`.
        assert!(should_trace_setting(Some("foo,bar"), "foo"));
        assert!(should_trace_setting(Some("foo,bar"), "bar"));
        // The key must match a complete field.  A prefix of a field does not
        // match, and the raw setting itself does not match either.
        assert!(!should_trace_setting(Some("foo,bar"), "fo"));
        assert!(!should_trace_setting(Some("foo,bar"), "foo,bar"));
        assert!(!should_trace_setting(Some("foo,bar"), ""));

        // A setting with no comma is one field.  The comparison is not a
        // substring search.
        assert!(should_trace_setting(Some("foobar"), "foobar"));
        assert!(!should_trace_setting(Some("foobar"), "foo"));

        // `splitOn` never returns an empty list, and it keeps empty fields.
        // `DEBUG_TRACE=` and `DEBUG_TRACE=a,,b` both enable the empty key.
        assert!(should_trace_setting(Some(""), ""));
        assert!(!should_trace_setting(Some(""), "foo"));
        assert!(should_trace_setting(Some("a,,b"), ""));
        assert!(should_trace_setting(Some("a,,b"), "b"));
    }
}
