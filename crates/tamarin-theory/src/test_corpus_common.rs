//! Corpus discovery and parsing shared by this crate's unit and integration
//! test binaries. Each binary gets its own process-local cache, but both
//! compile this implementation.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use tamarin_parser::ast as p;

/// Examples beyond the corpus tests' budget. The accountability lemmas of
/// this family grow geometrically with the session count.
pub const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

pub const SKIP_LISTED: &str = "listed: exceeds corpus-test budget";
pub const SKIP_PARSE: &str = "parser rejects this upstream example";
pub const SKIP_ELAB: &str = "elaboration rejects this upstream example";

/// Reviewed files that cannot reach the elaborated corpus audits.  Keep the
/// path and failed stage together: changes to either require an explicit
/// review instead of being hidden by an aggregate coverage percentage.
pub const EXPECTED_LOAD_SKIPS: &[(&str, &str)] = &[
    ("ccs18-5G/5G-AKA-bindingChannel/5G_AKA.spthy", SKIP_PARSE),
    ("ccs18-5G/5G-AKA-bindingChannel/5G_AKA_fix.spthy", SKIP_PARSE),
    ("ccs18-5G/5G-AKA-nonBindingChannel/5G_AKA.spthy", SKIP_PARSE),
    ("ccs18-5G/5G-AKA-nonBindingChannel/5G_AKA_fix.spthy", SKIP_PARSE),
    ("ccs18-5G/5G-AKA-untraceability/5G_AKA_priv.spthy", SKIP_PARSE),
    ("ccs18-5G/5G-AKA-untraceability/proofs/5G_AKA_priv-attack.spthy", SKIP_PARSE),
    ("features/auto-sources/tamarin-repo/ccs18-5G/5G-AKA-untraceability/5G_AKA_priv-without-SL.spthy", SKIP_PARSE),
    ("features/auto-sources/tamarin-repo/ccs18-5G/5G-AKA-untraceability/5G_AKA_priv.spthy", SKIP_PARSE),
    ("features/predicates/functionappl.spthy", SKIP_PARSE),
    ("regression/trace/issue834-2.spthy", SKIP_PARSE),
    ("regression/trace/issue834-3.spthy", SKIP_PARSE),
    ("sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy", SKIP_LISTED),
    ("sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy", SKIP_LISTED),
    ("sapic/not-working/PKCS11/pkcs11-dynamic-policy.spthy", SKIP_PARSE),
    ("sapic/not-working/envelope/envelope.spthy", SKIP_PARSE),
    ("sapic/not-working/envelope/envelope_allowsattack.spthy", SKIP_PARSE),
    ("sapic/not-working/envelope/envelope_simpler.spthy", SKIP_PARSE),
    ("testParser/Yubikey.spthy", SKIP_PARSE),
    ("testParser/include/include/include/include4.spthy", SKIP_PARSE),
    ("testParser/include/include/include3.spthy", SKIP_PARSE),
    ("testParser/include/includeDiff.spthy", SKIP_PARSE),
    ("testParser/include/include_2.spthy", SKIP_PARSE),
];

pub use tamarin_test_support::corpus_root;

/// `path` relative to the corpus root, as reports name it.
pub fn rel<'a>(path: &'a Path, root: &Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

/// Every `.spthy` file under `root`, in path order.
pub fn spthy_files(root: &Path) -> Vec<PathBuf> {
    let mut files: Vec<_> = walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .map(|entry| entry.into_path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "spthy"))
        .collect();
    files.sort();
    files
}

/// Whether [`BEYOND_BUDGET`] lists `path`.
pub fn beyond_budget(path: &Path, root: &Path) -> bool {
    BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref())
}

/// Detect the gated term operator before choosing the parser mode.  Looking at
/// the source, rather than retrying after an arbitrary default-mode failure,
/// prevents an unrelated parser regression from being hidden by a second
/// parse.  The real lexer supplies word boundaries and skips nested comments,
/// so prose such as `diffuse` and commented-out operators do not select the
/// mode.
fn uses_diff_operator(src: &str) -> bool {
    let mut lexer = tamarin_parser::lexer::Lexer::new(src);
    while !lexer.is_eof() {
        lexer.skip_ws();
        if lexer.peek_symbol("diff") {
            let save = lexer.pos();
            debug_assert!(lexer.symbol("diff"));
            if lexer.peek() == Some('(') {
                return true;
            }
            lexer.set_pos(save);
        }
        lexer.bump();
    }
    false
}

fn parse_source(src: &str, base: Option<PathBuf>) -> Option<p::Theory> {
    let flags = if uses_diff_operator(src) {
        &["diff"][..]
    } else {
        &[][..]
    };
    tamarin_parser::parser::parse_theory_with_base(src, flags, base).ok()
}

/// Read and parse one example file once per test process, resolving includes
/// against its directory and selecting diff mode only when the source contains
/// the gated `diff` term operator.
pub fn parse_file(path: &Path) -> Option<Arc<p::Theory>> {
    type Entry = Arc<OnceLock<Option<Arc<p::Theory>>>>;
    static CACHE: OnceLock<Mutex<BTreeMap<PathBuf, Entry>>> = OnceLock::new();
    let entry = {
        let mut cache = CACHE
            .get_or_init(|| Mutex::new(BTreeMap::new()))
            .lock()
            .unwrap();
        Arc::clone(
            cache
                .entry(path.to_path_buf())
                .or_insert_with(|| Arc::new(OnceLock::new())),
        )
    };
    entry
        .get_or_init(|| {
            let src = std::fs::read_to_string(path).ok()?;
            let base = path.parent().map(Path::to_path_buf);
            std::panic::catch_unwind(|| parse_source(&src, base).map(Arc::new))
                .ok()
                .flatten()
        })
        .clone()
}

#[cfg(test)]
mod tests {
    use super::{parse_source, uses_diff_operator};

    #[test]
    fn corpus_parser_selects_diff_mode_for_a_diff_operator() {
        let src = "theory D begin\nrule R: [ In(x) ] --> [ Out(diff(x, x)) ]\nend\n";
        assert!(tamarin_parser::parser::parse_theory(src, &[]).is_err());
        parse_source(src, None).expect("the diff-gate failure selects diff mode");
    }

    #[test]
    fn diff_mode_detection_honours_tokens_and_comments() {
        assert!(uses_diff_operator("rule R: [ ] --> [ Out(diff (x,y)) ]"));
        assert!(!uses_diff_operator(
            "/* diff(x,y) */ // diff (x,y)\nrule diffuse: [ ] --> [ ]"
        ));
    }

    #[test]
    fn corpus_parser_does_not_mask_an_ordinary_parse_failure_with_diff_mode() {
        // A general syntax error is not evidence that the caller intended
        // diff mode, so it takes only the default parser path.
        let src = "theory D begin\nrule R: [ ] -->\nend\n";
        assert!(!uses_diff_operator(src));
        assert!(parse_source(src, None).is_none());
    }
}
