// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, arcz, ValentinYuri, Nynko, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   src/Main/Console.hs

//! Embed git revision + build timestamp into the compiled binary so
//! `tamarin-prover --version` can mirror HS's `Generated from:` block.
//! Mirrors HS's compile-time TH (Console.hs `gitVersion`/`compileTime`): the
//! `$(gitHash)`/`$(gitDirty)`/`$(gitBranch)` splices from `Development.GitRev`
//! plus `runIO Data.Time.getCurrentTime`.

// Build script: `println!` is the sanctioned Cargo build-directive channel
// (`cargo:rustc-env=…`, `cargo:rerun-if-changed=…`) — it never touches the
// prover's runtime stdout.  Allow the `disallowed_macros` freeze here.
#![allow(clippy::disallowed_macros)]

use std::process::Command;

fn main() {
    // Git revision (full sha + branch).
    let mut rev = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());
    let branch = Command::new("git")
        .args(["rev-parse", "--abbrev-ref", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    // Dirty-tree suffix, mirroring HS `gitVersion` (Console.hs:200-209): when
    // `$(gitDirty)` is true the SHA is followed by " (with uncommited changes)"
    // (HS's spelling — single 't') *before* the `, branch:` separator. HS's
    // `$(gitDirty)` comes from `Development.GitRev`, which reports dirty when
    // `git status --porcelain` is non-empty — i.e. it also flags untracked
    // files (unlike `git diff-index --quiet HEAD --`). Mirror that: any
    // non-empty porcelain output means dirty. Injecting the suffix into `rev`
    // here feeds both consumers of TAMARIN_GIT_REV — cli.rs `version_text`
    // (`--version`) and pretty_theory.rs `render_generated_from` (the `--prove`
    // Generated-from footer) — so both `Git revision:` lines match HS.
    let dirty = Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| !o.stdout.is_empty())
        .unwrap_or(false);
    if dirty {
        rev.push_str(" (with uncommited changes)");
    }

    // Build timestamp (UTC).  Avoid `Date.now()`-style nondeterminism
    // concerns — this runs at COMPILE time, not at proof time.
    //
    // NOTE: this does NOT byte-match HS's `compileTime` (Console.hs:200-216, see line 213),
    // which is `show =<< getCurrentTime` and emits sub-second precision (up to
    // picoseconds, trailing zeros trimmed) — e.g. `... 08:31:14.64851655 UTC`.
    // `date` only offers `%N` (nanoseconds, fixed width, no trim) so it cannot
    // reproduce GHC `show :: UTCTime`. The `Compiled at:` line is stripped at
    // start-of-line by every parity harness, so it is non-load-bearing.
    let ts = Command::new("date")
        .args(["-u", "+%Y-%m-%d %H:%M:%S UTC"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=TAMARIN_GIT_REV={}", rev);
    println!("cargo:rustc-env=TAMARIN_GIT_BRANCH={}", branch);
    println!("cargo:rustc-env=TAMARIN_BUILD_TIMESTAMP={}", ts);
    // Retrigger the build when the recorded revision can change:
    //  - `.git/HEAD` covers a branch switch (and detached-HEAD moves).
    //  - the concrete ref file (`.git/refs/heads/<branch>`) covers a new
    //    commit on the current branch, which updates that file rather than
    //    `.git/HEAD`. Watching the file (not the `refs/heads` directory) is
    //    what reliably fires on a content change.
    //  - `.git/packed-refs` covers the case where the ref is packed and the
    //    loose ref file is absent (e.g. after `git gc`).
    let git_dir = "../../.git";
    println!("cargo:rerun-if-changed={git_dir}/HEAD");
    // Resolve HEAD's symbolic ref target (e.g. "refs/heads/rust-port") and
    // watch that concrete file. If HEAD is detached or unreadable, the
    // HEAD/packed-refs watches still apply.
    if let Ok(head) = std::fs::read_to_string(format!("{git_dir}/HEAD")) {
        if let Some(ref_path) = head.trim().strip_prefix("ref: ") {
            println!("cargo:rerun-if-changed={git_dir}/{ref_path}");
        }
    }
    println!("cargo:rerun-if-changed={git_dir}/packed-refs");
}
