// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins HS's `unboundReport` coverage of the rules SAPIC's process
//! translation generates.
//!
//! HS runs its single `checkWellformedness` pass on the TRANSLATED theory
//! (`checkTranslatedTheory`, TheoryLoader.hs:559-565), so `unboundReport`
//! (Wellformedness.hs:514-519) walks the generated rules too.  A variable free
//! only inside a process's embedded `_restrict` is lifted into the generated
//! rule's `Restr_<rule>_<i>( … )` action, where no premise binds it, and so is
//! reported against that rule.
//!
//! Four properties are pinned:
//!   - the generated-rule entries follow every user-rule entry, because SAPIC
//!     appends its rules to `thyItems`;
//!   - the whole group still sorts at HS check index 2, ahead of `factReports`
//!     entries;
//!   - and ahead of `ruleVariantsReport`'s (index 6) "Rule has no variants";
//!   - the variable a `lookup t as v` combinator binds is NOT reported, per
//!     `originatesFromLookup` (Wellformedness.hs:501-510).
//!
//! The expected bytes below are the pinned oracle's (Git revision ef3f0468)
//! output for the four `tests/fixtures/sapic_*.spthy` files, run with
//! `--derivcheck-timeout=0` so the dynamic `MessageDerivationChecks` pass —
//! which would report the same variables under its own topic — stays off.

mod common;

use common::{fixture, maude_available, run_binary};

/// Load `<fixture>.spthy` through the batch pipeline and return the theory it
/// writes out.
fn load(fixture_name: &str) -> String {
    let in_path = fixture(fixture_name);
    let out_dir = std::env::temp_dir().join("tamarin_prover_sapic_wf_unbound");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join(format!("{fixture_name}.out"));

    // `-o`/`--output` is a cmdargs `flagOpt` whose value must be ATTACHED
    // (Batch.hs:44-84, see line 76).
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let (code, _, stderr) = run_binary(
        &["--quiet", "--derivcheck-timeout=0", &output_arg],
        &[&in_path],
    );
    assert_eq!(
        code, 0,
        "expected exit code 0, got {code}; stderr:\n{stderr}"
    );
    std::fs::read_to_string(&out_path).expect("output written")
}

/// Oracle bytes for `sapic_restrict_unbound.spthy`: both user rules in source
/// order, then the rule SAPIC generated for the `_restrict`-carrying MSR step.
/// The two-space lines are HS's `intersperse (text "")` group separators.
const EXPECTED_MIXED: &[&str] = &[
    "/*",
    "WARNING: the following wellformedness checks failed!",
    "",
    "Unbound variables",
    "=================",
    "",
    "  rule `ZUserA' has unbound variables: ",
    "    b",
    "  ",
    "  rule `AUserB' has unbound variables: ",
    "    d",
    "  ",
    "  rule `Evmrestrictkb_0_1' has unbound variables: ",
    "    k.5",
    "*/",
];

/// Oracle bytes for `sapic_restrict_unbound_order.spthy`: the generated-rule
/// entry precedes the `factReports` topics, pinning the check-order position.
const EXPECTED_ORDER: &[&str] = &[
    "/*",
    "WARNING: the following wellformedness checks failed!",
    "",
    "Unbound variables",
    "=================",
    "",
    "  rule `Evmrestrictkb_0_1' has unbound variables: ",
    "    k.5",
    "",
    "Fact arity issues",
    "=================",
];

/// Oracle bytes for `sapic_unbound_before_variants.spthy`: `ruleVariantsReport`
/// is HS check index 6, so its group follows the generated-rule entry.
const EXPECTED_VARIANTS_ORDER: &[&str] = &[
    "/*",
    "WARNING: the following wellformedness checks failed!",
    "",
    "Unbound variables",
    "=================",
    "",
    "  rule `Evmrestrictkb_0_1' has unbound variables: ",
    "    k.5",
    "",
    "Rule has no variants",
    "====================",
    "",
    "  Rule NoVar has no variants.",
];

#[test]
fn sapic_restrict_unbound_follows_user_rules() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let body = load("sapic_restrict_unbound.spthy");
    let expected = EXPECTED_MIXED.join("\n");
    assert!(
        body.contains(&expected),
        "wf report must carry the oracle's `Unbound variables` block with the \
         SAPIC-generated rule after both user rules.\nexpected:\n{expected}\ngot:\n{body}"
    );
}

#[test]
fn sapic_restrict_unbound_sorts_before_fact_reports() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let body = load("sapic_restrict_unbound_order.spthy");
    let expected = EXPECTED_ORDER.join("\n");
    assert!(
        body.contains(&expected),
        "the generated-rule `Unbound variables` group must splice ahead of the \
         `factReports` topics.\nexpected:\n{expected}\ngot:\n{body}"
    );
}

#[test]
fn sapic_restrict_unbound_sorts_before_rule_variants() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let body = load("sapic_unbound_before_variants.spthy");
    let expected = EXPECTED_VARIANTS_ORDER.join("\n");
    assert!(
        body.contains(&expected),
        "the generated-rule `Unbound variables` group must splice ahead of \
         `Rule has no variants`.\nexpected:\n{expected}\ngot:\n{body}"
    );
}

#[test]
fn sapic_lookup_binder_is_not_unbound() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let body = load("sapic_lookup_binder.spthy");
    // The generated `lookupmasv_0_1` rule reads `[ State_1( m.1 ) ] --[ IsIn(
    // m.1, v.1 ) ]-> [ State_11( m.1, v.1 ) ]`, so `v.1` occurs in an action
    // and a conclusion with no premise binding it; `originatesFromLookup`
    // suppresses it and the oracle reports a clean theory.
    assert!(
        body.contains("process=\"lookup m.1 as v.1\""),
        "fixture must still generate the lookup rule\ngot:\n{body}"
    );
    assert!(
        body.contains("/* All wellformedness checks were successful. */"),
        "the `lookup t as v` binder must not be reported unbound\ngot:\n{body}"
    );
}
