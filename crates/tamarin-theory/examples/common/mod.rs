//! Shared setup for the dev example binaries: read → parse → elaborate a
//! theory file and boot a Maude handle on its full signature, corpus-root
//! resolution and `.spthy` collection for the corpus walkers, and the Tamarin
//! oracle runner with its wellformedness banner scanner.
//!
//! Lives in `examples/common/` (a subdirectory, so cargo does not treat it
//! as an example target); each example pulls it in with `mod common;`.
//! Individual examples use only a subset of these helpers, so each is
//! marked `#[allow(dead_code)]`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use tamarin_term::maude_proc::MaudeHandle;

/// The examples corpus root: `$CORPUS_ROOT` if set, else the
/// `tamarin-prover/examples/` directory in the submodule, relative to this
/// crate's manifest.
#[allow(dead_code)]
pub fn corpus_root() -> PathBuf {
    std::env::var("CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
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

/// Read, parse, and elaborate `theory_path`, then start Maude on the
/// elaborated signature.  The elaborated signature carries the full
/// `MaudeSig` (aenc/pk/user-declared symbols); booting Maude on the default
/// sig would leave those symbols unparseable and corrupt any downstream
/// unification.
///
/// The binary comes from `tamarin_test_support::maude_path`, and a bare
/// `maude` for the OS to look up on `$PATH` is the last resort.  An example
/// never skips: whatever it resolved goes to `MaudeHandle::start`, and a
/// machine with no maude stops with that error.
#[allow(dead_code)]
pub fn load_theory_with_maude(theory_path: &str) -> (tamarin_theory::theory::Theory, MaudeHandle) {
    let source = std::fs::read_to_string(theory_path).expect("read theory");
    let parsed = tamarin_parser::parse_theory(&source, &[]).expect("parse theory");
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let maude_path = tamarin_test_support::maude_path().unwrap_or_else(|| "maude".to_string());
    let maude = MaudeHandle::start(&maude_path, elaborated.signature.clone()).expect("start maude");
    (elaborated, maude)
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

/// A wellformedness topic header is a non-blank line underlined by a line of
/// nothing but `=` characters; banner sections that share that shape (the
/// `theory …` / `analyzed:` / version headers) are filtered out by name.
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
