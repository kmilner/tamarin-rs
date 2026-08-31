// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins HS `ruleVariantsReport` (Wellformedness.hs:375-382) and the rule drop
//! that shares its verdict.
//!
//! `variantsCheck`'s `guard (null recomputedVariants)` arm
//! (Wellformedness.hs:362-366) fires when `variantsProtoRule` returns
//! `Nothing`.  The canonical shape is a rule with both `Fr(~x)` and `In(~x)`
//! among its premises: `~x` cannot be sent before it is generated, so every
//! candidate substitution is fresh-redundant.  `closeProtoRule`
//! (lib/theory/src/Rule.hs:82-86) then produces no closed rule for it, and the
//! batch driver drops it from the theory on the same verdict.
//!
//! The expected block is the pinned oracle's (Git revision ef3f0468).

use tamarin_parser::parse_theory;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_test_support::require_maude_path;
use tamarin_theory::theory::{Theory, TheoryItem};
use tamarin_theory::tools::rule_variants::{open_rule_has_no_variants, populate_rule_variants};
use tamarin_theory::wellformedness::rules::rule_variants_report;

/// A theory with one rule that has no variants (`NoVar`) and one that has the
/// trivial one (`Ok`).
const SRC: &str = "theory NoVariants\nbegin\n\
                   builtins: symmetric-encryption\n\
                   rule NoVar:\n  [ In(~x), Fr(~x) ] --[ N(~x) ]-> [ ]\n\
                   rule Ok:\n  [ Fr(~k), In(c) ] --[ O(~k) ]-> [ Out(sdec(c, ~k)) ]\n\
                   end\n";

/// The elaborated theory with `populate_rule_variants` applied, as the batch
/// driver hands it to the wellformedness pass, and a handle on its signature.
fn loaded(mp: &str) -> (Theory, MaudeHandle) {
    let parsed = parse_theory(SRC, &[]).expect("parse");
    let mut elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let maude = MaudeHandle::start(mp, elaborated.signature.clone()).expect("start maude");
    populate_rule_variants(&mut elaborated, &maude, None);
    (elaborated, maude)
}

/// The oracle's `Rule has no variants` body, once, for `NoVar` alone.  "For
/// exaple" is spelled that way in the HS source (Wellformedness.hs:366).
#[test]
fn no_variant_rule_is_reported() {
    let Some(mp) = require_maude_path() else {
        return;
    };
    let (thy, maude) = loaded(&mp);
    let report = rule_variants_report(&thy, Some(&maude));
    assert_eq!(report.len(), 1, "only `NoVar` has no variants: {report:?}");
    assert_eq!(report[0].topic, "Rule has no variants");
    assert_eq!(
        report[0].message,
        "Rule has no variants\n====================\n\n  \
         Rule NoVar has no variants.\n  \n  \
         Most likely, this means that the rule's use of fresh variables is \
         contradictory. For exaple, a rule with the premises In(~x) and Fr(~x) \
         has no variants because ~x cannot be sent before it is generated.\n"
    );
}

/// The web load path has no Maude process at wellformedness time and so emits
/// no such block.
#[test]
fn no_maude_reports_nothing() {
    let Some(mp) = require_maude_path() else {
        return;
    };
    let (thy, _maude) = loaded(&mp);
    assert!(rule_variants_report(&thy, None).is_empty());
}

/// HS `closeProtoRule` (lib/theory/src/Rule.hs:82-86) drops a rule with no
/// variants from the closed theory.  The batch driver's `retain` reads this
/// predicate, not the report, so a rule name that `showRuleCaseName` prefixes
/// still matches.
#[test]
fn only_the_no_variant_rule_is_dropped() {
    let Some(mp) = require_maude_path() else {
        return;
    };
    let (mut thy, maude) = loaded(&mp);
    thy.items.retain(|item| match item {
        TheoryItem::Rule(opr) => !open_rule_has_no_variants(&maude, opr),
        _ => true,
    });
    let names: Vec<&str> = thy.rules().map(|opr| opr.name()).collect();
    assert_eq!(names, vec!["Ok"]);
}
