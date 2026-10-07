//! Initialize a missing upstream checkout before any include_str!/GUI build.
#![allow(clippy::disallowed_macros)] // Cargo build directives.

use std::path::Path;
use std::process::Command;

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let upstream = root.join("tamarin-prover");
    let required = [
        "data/intruder_variants_dh.spthy",
        "data/intruder_variants_bp.spthy",
        "frontend/package.json",
        "frontend/package-lock.json",
        "lib/term/src/Term/Term/Raw.hs",
        "src/Main/Console.hs",
    ];
    for file in required {
        println!("cargo:rerun-if-changed={}", upstream.join(file).display());
    }
    if required.iter().all(|file| upstream.join(file).is_file()) {
        return;
    }
    // Never overwrite a populated checkout, including local edits or an
    // intentionally selected revision. Source archives with the files present
    // above work without Git metadata as well.
    if upstream.exists() {
        assert!(
            upstream.read_dir().expect("read upstream directory").next().is_none(),
            "The tamarin-prover checkout is incomplete. Restore its missing source files before building; Cargo will not overwrite an existing checkout."
        );
    }
    let status = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["submodule", "update", "--init", "--", "tamarin-prover"])
        .status()
        .expect("Install Git to initialize the tamarin-prover submodule");
    assert!(
        status.success() && required.iter().all(|file| upstream.join(file).is_file()),
        "Could not initialize tamarin-prover. Check network access and run git submodule update --init tamarin-prover, then retry Cargo."
    );
}
