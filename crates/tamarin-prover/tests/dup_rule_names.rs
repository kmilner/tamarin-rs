// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end stderr / exit-code parity for the duplicate-rule guards.
//!
//! Parse time: `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) rejects a
//! second, DIFFERENT rule under an existing name via `addOpenProtoRule`
//! (OpenTheory.hs:691-702); batch mode's `handleError` `die`s on the
//! resulting `ParserError` (Main/Mode/Batch.hs:235) — parsec frame on stderr,
//! exit 1, no stdout.  An identical duplicate is accepted and appended again.
//!
//! Translate time: SAPIC's `translate` folds its generated rules through the
//! same guard (`foldM liftedAddProtoRule`, lib/sapic/src/Sapic.hs:75), so a user rule named
//! like a generated one (`rule Init` alongside a `process:`) aborts AFTER the
//! `Theory translated` marker.  In HS the thrown `DuplicateItem` escapes to
//! GHC's runtime: the pinned oracle (Git revision ef3f0468) prints exactly
//! `tamarin-prover: duplicate rule: Init` after the markers and exits 1.
//!
//! The oracle emits the `maude tool:` banner and the `[Theory X] …` markers
//! on stderr even under `--quiet` (the flag is registered but never read —
//! TheoryLoader.hs:159-163, 414-416).  Expectations below are its `--quiet`
//! stderr minus the three banner lines, whose maude path and version are
//! machine-local.

mod common;

use common::{maude_available, strip_maude_banner};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_dup_rule_names";

/// Run the built binary on `src` under `--quiet` and return `(exit code,
/// stdout, stderr minus the maude banner)`.
fn run_binary(stem: &str, src: &str) -> (i32, String, String) {
    let (code, stdout, stderr) = common::run_raw(TMP_DIR, stem, src, &["--quiet"]);
    (code, stdout, strip_maude_banner(&stderr))
}

/// Two different rules under one name: the parsec frame `die` prints — the
/// `SourcePos` name is the input path, so only the frame's tail is portable.
#[test]
fn duplicate_rule_prints_the_parsec_frame_and_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, _, stderr) = run_binary(
        "dup",
        "theory T begin\n\n\
         rule R1: [ ] --> [ Out('a') ]\n\
         rule R1: [ ] --> [ Out('b') ]\n\n\
         end\n",
    );
    assert_eq!(code, 1);
    assert!(
        stderr.ends_with(
            "dup.spthy\" (line 6, column 1):\n\
             unexpected \"e\"\n\
             expecting \"variants\"\n\
             duplicate rule: R1\n"
        ),
        "unexpected stderr:\n{stderr}"
    );
}

/// An identical duplicate loads with exit 0 and renders BOTH copies.
#[test]
fn identical_duplicate_loads_and_renders_twice() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stdout, _) = run_binary(
        "ident",
        "theory T begin\n\nrule R1: [ ] --> [ ]\nrule R1: [ ] --> [ ]\n\nend\n",
    );
    assert_eq!(code, 0);
    assert_eq!(
        stdout
            .matches("rule (modulo E) R1:\n   [ ] --> [ ]")
            .count(),
        2,
        "expected both R1 copies rendered:\n{stdout}"
    );
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
