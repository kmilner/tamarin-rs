//! Shared helpers for the tamarin-parser dev example binaries: corpus-root
//! resolution, `.spthy` collection, the Tamarin oracle runner, and the
//! wellformedness banner scanner.
//!
//! Lives in `examples/common/` (a subdirectory, so cargo does not treat it
//! as an example target); each example pulls it in with `mod common;`.
//! Individual examples use only a subset of these helpers, so each is
//! marked `#[allow(dead_code)]`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The examples corpus root: `$CORPUS_ROOT` if set, else the
/// `tamarin-prover/examples/` directory in the submodule, relative to this
/// crate's manifest.
#[allow(dead_code)]
pub fn corpus_root() -> PathBuf {
    std::env::var("CORPUS_ROOT").map(PathBuf::from).unwrap_or_else(|_| {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
    })
}

/// Collect every `.spthy` file under `root`, sorted by path.
#[allow(dead_code)]
pub fn collect_spthy(root: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spthy"))
        .map(|e| e.path().to_path_buf())
        .collect();
    files.sort();
    files
}

/// Run `bin` (a `tamarin-prover` binary) on `path` with `flags` and return
/// the set of wellformedness topics it emits, or None if the process fails
/// to launch. stdout and stderr are concatenated before scanning.
#[allow(dead_code)]
pub fn run_tamarin(bin: &str, path: &Path, flags: &[String]) -> Option<BTreeSet<String>> {
    let mut cmd = Command::new(bin);
    for f in flags {
        cmd.arg(f);
    }
    cmd.arg(path);
    let out = cmd.output().ok()?;
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some(extract_topics(&combined))
}

/// A wellformedness topic header is a line followed by a line of `=`
/// characters whose length equals (or exceeds) the topic name.
#[allow(dead_code)]
pub fn extract_topics(s: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut prev: Option<&str> = None;
    for line in s.lines() {
        if !line.is_empty() && line.chars().all(|c| c == '=') {
            if let Some(p) = prev {
                let p = p.trim();
                if !p.is_empty() {
                    // Filter banner lines that aren't actual topics.
                    if !p.starts_with("analyzed:")
                        && !p.starts_with("summary of summaries")
                        && !p.contains("Tamarin version")
                        && !p.contains("Maude version")
                        && !p.starts_with("theory ")
                        && !p.starts_with("Generated from:")
                        && !p.starts_with("Compiled at")
                    {
                        out.insert(p.to_string());
                    }
                }
            }
        }
        prev = Some(line);
    }
    out
}
