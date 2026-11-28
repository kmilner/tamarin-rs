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
    ("features/predicates/functionappl.spthy", SKIP_PARSE),
    // Intentional rejection fixtures introduced by the updated upstream pin.
    (
        "regression/negative/issue905-undeclared-em.spthy",
        SKIP_PARSE,
    ),
    ("regression/negative/issue906-end-prefix.spthy", SKIP_PARSE),
    ("regression/negative/issue907-variable-lhs.spthy", SKIP_ELAB),
    (
        "regression/negative/manual-variant-embedded-restriction.spthy",
        SKIP_PARSE,
    ),
    ("regression/negative/missing-end.spthy", SKIP_PARSE),
    // Upstream's `startProofSkeleton` rejects a stored proof that starts
    // with SOLVED.
    ("regression/trace/issue326.spthy", SKIP_PARSE),
    ("regression/trace/issue834-2.spthy", SKIP_PARSE),
    ("regression/trace/issue834-3.spthy", SKIP_PARSE),
    (
        "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
        SKIP_LISTED,
    ),
    (
        "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
        SKIP_LISTED,
    ),
    (
        "sapic/not-working/PKCS11/pkcs11-dynamic-policy.spthy",
        SKIP_PARSE,
    ),
    ("sapic/not-working/envelope/envelope.spthy", SKIP_PARSE),
    (
        "sapic/not-working/envelope/envelope_allowsattack.spthy",
        SKIP_PARSE,
    ),
    (
        "sapic/not-working/envelope/envelope_simpler.spthy",
        SKIP_PARSE,
    ),
    ("testParser/Yubikey.spthy", SKIP_PARSE),
    (
        "testParser/include/include/include/include4.spthy",
        SKIP_PARSE,
    ),
    ("testParser/include/include/include3.spthy", SKIP_PARSE),
    ("testParser/include/includeDiff.spthy", SKIP_PARSE),
    ("testParser/include/include_2.spthy", SKIP_PARSE),
];

pub use tamarin_test_support::corpus_root;

/// The corpus root, or `None` when it is missing and `TAM_ALLOW_NO_CORPUS=1`
/// allows the skip. A missing root otherwise fails the test.
pub fn corpus_root_or_skip(label: &str) -> Option<PathBuf> {
    let root = corpus_root();
    if root.is_dir() {
        return Some(root);
    }
    if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
        eprintln!("{label}: root {} missing, skipped", root.display());
        return None;
    }
    panic!(
        "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
        root.display()
    );
}

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

/// Whether the source uses the gated `diff(...)` term operator, the first
/// evidence of a diff theory.  The real lexer supplies word boundaries and
/// skips nested comments, so prose such as `diffuse` and commented-out
/// operators do not count.
fn uses_diff_operator(src: &str) -> bool {
    let mut lexer = tamarin_parser::lexer::Lexer::new(src);
    while !lexer.is_eof() {
        lexer.skip_ws();
        if lexer.peek_symbol("diff") {
            let save = lexer.pos();
            let consumed = lexer.symbol("diff");
            debug_assert!(consumed);
            if lexer.peek() == Some('(') {
                return true;
            }
            lexer.set_pos(save);
        }
        lexer.bump();
    }
    false
}

/// Whether the example's upstream test manifest (`<file>.test.json`) runs it
/// in diff mode only, every test passing `--diff`.  A diff theory need not
/// contain a `diff(...)` term, so the manifest is the other evidence of the
/// intended mode; a manifest that also runs the file without `--diff` marks a
/// trace theory.
pub(crate) fn manifest_requests_diff(path: &Path) -> bool {
    let mut manifest = path.as_os_str().to_owned();
    manifest.push(".test.json");
    let Ok(text) = std::fs::read_to_string(manifest) else {
        return false;
    };
    let json: serde_json::Value = serde_json::from_str(&text).expect("valid test manifest");
    json["tests"].as_array().is_some_and(|tests| {
        !tests.is_empty()
            && tests.iter().all(|test| {
                test["args"]
                    .as_array()
                    .is_some_and(|args| args.iter().any(|arg| arg == "--diff"))
            })
    })
}

/// Parse in the mode the evidence suggests (`diff`, or a `diff(...)` term),
/// then in the other. The two modes accept disjoint item sets, as in HS, so a
/// file that is valid in either mode loads in exactly that mode; a file valid
/// in neither stays a load skip, which the census ledgers pin.
pub(crate) fn parse_source(src: &str, base: Option<PathBuf>, diff: bool) -> Option<p::Theory> {
    let plain = |base| tamarin_parser::parser::parse_theory_with_base(src, &[], base).ok();
    let diff_mode = |base| tamarin_parser::parser::parse_diff_theory_with_base(src, &[], base).ok();
    if diff || uses_diff_operator(src) {
        diff_mode(base.clone()).or_else(|| plain(base))
    } else {
        plain(base.clone()).or_else(|| diff_mode(base))
    }
}

/// Read and parse one example file once per test process, resolving includes
/// against its directory, in the mode [`parse_source`] settles on.
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
            let diff = manifest_requests_diff(path);
            std::panic::catch_unwind(|| parse_source(&src, base, diff).map(Arc::new))
                .ok()
                .flatten()
        })
        .clone()
}
