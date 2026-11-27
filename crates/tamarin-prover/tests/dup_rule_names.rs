// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The duplicate-rule guard at translate time.  The parse-time guard is in
//! the parser's parse table.
//!
//! SAPIC's `translate` folds its generated rules through the same guard as
//! the parser (`foldM liftedAddProtoRule`, lib/sapic/src/Sapic.hs), so a
//! user rule named like a generated one (`rule Init` alongside a `process:`)
//! aborts AFTER the `Theory translated` marker.  In HS the thrown
//! `DuplicateItem` escapes to GHC's runtime: the pinned oracle prints exactly
//! `tamarin-prover: duplicate rule: Init` after the markers and exits 1.

mod common;

use common::{maude_available, strip_maude_banner};

/// Run the built binary on `src` under `--quiet` and return `(exit code,
/// stdout, stderr minus the maude banner)`.
fn run_binary(stem: &str, src: &str) -> (i32, String, String) {
    let (code, stdout, stderr) =
        common::run_raw("tamarin_prover_dup_rule_names", stem, src, &["--quiet"]);
    (code, stdout, strip_maude_banner(&stderr))
}

/// A user rule named like a SAPIC-generated one dies at translate time with
/// the oracle's stderr line `tamarin-prover: duplicate rule: Init`, after the
/// load/translate markers, with exit 1 and no theory on stdout (HS: the
/// `addProtoRule` exception escapes to GHC's runtime, which prints
/// `tamarin-prover: <show exception>` — the shape `run.rs`'s SAPIC error arm
/// reproduces).
#[test]
fn sapic_generated_name_clash_aborts_translation() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, _, stderr) = run_binary(
        "sapic_clash",
        "theory T begin\n\n\
         rule Init: [ ] --> [ Out('a') ]\n\n\
         process:\nnew x; out(x)\n\n\
         end\n",
    );
    assert_eq!(code, 1);
    assert!(
        stderr.contains("tamarin-prover: duplicate rule: Init\n"),
        "expected the oracle's `tamarin-prover: duplicate rule: Init` line:\n{stderr}"
    );
    assert!(
        stderr.contains("[Theory T] Theory translated\n"),
        "the clash fires after the `Theory translated` marker:\n{stderr}"
    );
}
