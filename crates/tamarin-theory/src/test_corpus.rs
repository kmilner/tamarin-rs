//! Parsed and elaborated corpus caches shared by the in-crate corpus tests.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

pub(crate) use crate::test_corpus_common::{
    beyond_budget, corpus_root, parse_file, rel, spthy_files, EXPECTED_LOAD_SKIPS, SKIP_ELAB,
    SKIP_LISTED, SKIP_PARSE,
};

/// Elaborate a cached parse once per path. Concurrent corpus tests share the
/// result, including a stable description of an elaboration failure or panic.
pub(crate) fn elaborate_file(path: &Path) -> Result<Arc<crate::theory::Theory>, Arc<str>> {
    type Outcome = Result<Arc<crate::theory::Theory>, Arc<str>>;
    type Entry = Arc<OnceLock<Outcome>>;
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
            let parsed = parse_file(path).ok_or_else(|| Arc::from("parse failed"))?;
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::elaborate::elaborate(&parsed)
            })) {
                Ok(Ok(theory)) => Ok(Arc::new(theory)),
                Ok(Err(error)) => Err(Arc::from(error.message)),
                Err(_) => Err(Arc::from("elaboration panicked")),
            }
        })
        .clone()
}
