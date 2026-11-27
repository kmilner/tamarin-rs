// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The variant pass's error path: a Maude that dies while variants are
//! computed is an error, never a "Rule has no variants" verdict that would
//! drop the rule.  The report bytes and the rule drop themselves are the
//! `wf_rule_variants` divergence fixture.

use tamarin_parser::parse_theory;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_test_support::require_maude_path;
use tamarin_theory::tools::rule_variants::populate_rule_variants;

/// A theory with one rule that has no variants (`NoVar`) and one that has the
/// trivial one (`Ok`).
const SRC: &str = "theory NoVariants\nbegin\n\
                   builtins: symmetric-encryption\n\
                   rule NoVar:\n  [ In(~x), Fr(~x) ] --[ N(~x) ]-> [ ]\n\
                   rule Ok:\n  [ Fr(~k), In(c) ] --[ O(~k) ]-> [ Out(sdec(c, ~k)) ]\n\
                   end\n";

#[test]
fn variant_transport_failure_is_not_reported_as_no_variants() {
    let Some(mp) = require_maude_path() else {
        return;
    };
    let parsed = parse_theory(SRC, &[]).expect("parse");
    let mut elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let maude = MaudeHandle::start(&mp, elaborated.signature.clone()).expect("start maude");
    maude.kill_subprocess();

    assert!(populate_rule_variants(&mut elaborated, &maude, None).is_err());
    assert_eq!(elaborated.rules().count(), 2);
}
