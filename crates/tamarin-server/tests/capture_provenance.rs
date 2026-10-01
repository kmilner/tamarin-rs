//! Validate the source identity behind the committed Haskell HTTP captures.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

fn command_stdout(command: &mut Command, description: &str) -> String {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("run {description}: {error}"));
    assert!(
        output.status.success(),
        "{description} failed ({}): {}",
        output.status,
        String::from_utf8_lossy(&output.stderr).trim()
    );
    String::from_utf8(output.stdout)
        .unwrap_or_else(|error| panic!("{description} emitted non-UTF-8 output: {error}"))
        .trim()
        .to_owned()
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root above crates/tamarin-server")
        .to_owned()
}

#[test]
fn haskell_captures_match_oracle_source() {
    let root = workspace_root();
    let submodule = root.join("tamarin-prover");
    assert!(
        submodule.join(".git").exists(),
        "{} is not a git checkout — run ./setup.sh",
        submodule.display()
    );
    let pin = command_stdout(
        Command::new("git")
            .arg("-C")
            .arg(&submodule)
            .args(["rev-parse", "HEAD"]),
        "read the tamarin-prover revision",
    );
    let patch_fingerprint = command_stdout(
        Command::new("bash")
            .args([
                "-c",
                ". \"$1\"; patch_series_fingerprint \"$2\"",
                "capture provenance",
            ])
            .arg(root.join("scripts/gate_common.sh"))
            .arg(&root),
        "fingerprint the Haskell patch series",
    );
    let stamp_path = root.join("crates/tamarin-server/tests/fixtures/haskell-responses/oracle_rev");
    let stamp = std::fs::read_to_string(&stamp_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", stamp_path.display()));
    let fields: BTreeMap<_, _> = stamp
        .lines()
        .map(|line| {
            line.split_once('=')
                .expect("capture stamp uses key=value lines")
        })
        .collect();
    assert_eq!(
        fields.len(),
        2,
        "unexpected fields in {}",
        stamp_path.display()
    );
    assert_eq!(fields.get("pin"), Some(&pin.as_str()));
    assert_eq!(
        fields.get("patch_series_sha256"),
        Some(&patch_fingerprint.as_str()),
        "Haskell captures were produced with a different patch series; \
         regenerate them with tests/capture_haskell_fixtures.sh"
    );
}
