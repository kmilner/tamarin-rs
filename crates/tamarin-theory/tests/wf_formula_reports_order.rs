// Currently GPL 3.0 until granted permission by the following authors:
//   jdreier, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Tools/Wellformedness.hs,
//   lib/utils/src/Extension/Prelude.hs

//! Pins the ORDER `formulaReports` emits its findings in, end to end —
//! `formula_reports` list order plus `prettyWfErrorReport`'s grouping.
//!
//! HS runs all three arms inside the `annFormulas` loop
//! (`msum [checkQuantifiers, checkTerms, checkGuarded]`,
//! Wellformedness.hs:999-1014, see lines 1002-1004), so the topics INTERLEAVE
//! per formula and a topic REOPENS after an intervening one — `groupOn fst`
//! merges only CONSECUTIVE entries (Extension/Prelude.hs:96-97).  Emitting one
//! whole block per topic instead would collapse the runs into a single header
//! each and reorder the bodies.
//!
//! Expected bytes are the pinned oracle's (Git revision ef3f0468) for the
//! theories below.

use tamarin_parser::parse_theory;
use tamarin_theory::pretty_theory::format_wf_block;

/// Build the wf block the batch / web load pipelines render, running the
/// same `formula_reports` pass they do.
fn wf_block(src: &str) -> String {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let errs =
        tamarin_theory::formula_reports::formula_reports(&thy, &elaborated.signature.maude_sig);
    format_wf_block(&errs)
}

/// The paragraph every `checkTerms` body ends with (Wellformedness.hs:975-983),
/// already at the two-space indent `ppTopic` gives a group's bodies.
const ALLOWED_LINES: &[&str] = &[
    "  The only allowed terms are public constants and bound node and",
    "  message variables. If you encounter free message variables, then",
    "  you might have forgotten a #-prefix. Sort prefixes can only be",
    "  dropped where this is unambiguous. Moreover, reducible function",
    "  symbols are disallowed.",
];

/// Three lemmas where only the middle one is unguardable: `Formula terms`
/// closes and REOPENS around the ` Formula guardedness` group, so the report
/// carries three groups and three headers.
#[test]
fn formula_terms_reopens_after_the_guardedness_group() {
    let src = "theory Interleave\nbegin\n\
               builtins: diffie-hellman\n\
               rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
               lemma l1: \"All x #i. A(x^x) @ i ==> F\"\n\
               lemma l2: \"All z. z = z\"\n\
               lemma l3: \"All y #j. A(y^y) @ j ==> F\"\n\
               end\n";

    let mut expected: Vec<&str> = vec![
        "/*",
        "WARNING: the following wellformedness checks failed!",
        "",
        "Formula terms",
        "=============",
        "",
        "  Lemma `l1' uses terms of the wrong form: `exp(Bound 1,Bound 1)'",
        "  ",
    ];
    expected.extend(ALLOWED_LINES);
    expected.extend([
        "",
        " Formula guardedness",
        "====================",
        "",
        "  Lemma `l2' cannot be converted to a guarded formula:",
        "    universal quantifier without toplevel implication",
        "      \"\u{2200} z. z = z\"",
        "    in the formula",
        "      \"\u{2200} z. z = z\"",
        "",
        "Formula terms",
        "=============",
        "",
        "  Lemma `l3' uses terms of the wrong form: `exp(Bound 1,Bound 1)'",
        "  ",
    ]);
    expected.extend(ALLOWED_LINES);
    expected.push("*/");
    assert_eq!(wf_block(src), expected.join("\n"));
}

/// `L1` trips `checkTerms` AND `checkGuarded`, so its two findings land back
/// to back under different topics; `L2`/`L3`/`L4` then reopen `Formula terms`
/// as ONE group.  This is the shape a per-topic splice cannot produce: it
/// would emit `L1`'s guardedness finding after all four term findings.
#[test]
fn a_formula_tripping_two_arms_splits_the_terms_group() {
    let src = "theory C\nbegin\n\
               builtins: xor, multiset\n\
               lemma L1: \"All #j. K('c') @ i ==> F\"\n\
               lemma L2: \"All #i. Test('b' XOR 'a') @ #i ==> F\"\n\
               lemma L3: \"All #i. Test(('b' ++ 'a') ++ ('c' XOR 'd')) @ #i ==> F\"\n\
               lemma L4: \"All x #i. Test(<x, 'b', ~'n'>) @ #i ==> F\"\n\
               end\n";

    let mut expected: Vec<&str> = vec![
        "/*",
        "WARNING: the following wellformedness checks failed!",
        "",
        "Formula terms",
        "=============",
        "",
        "  Lemma `L1' uses terms of the wrong form: `Free #i'",
        "  ",
    ];
    expected.extend(ALLOWED_LINES);
    expected.extend([
        "",
        " Formula guardedness",
        "====================",
        "",
        "  Lemma `L1' cannot be converted to a guarded formula:",
        "    unguarded variable(s) '#j' in the subformula",
        "      \"\u{2200} #j. (K( 'c' ) @ #i) \u{21D2} (\u{22A5})\"",
        "    in the formula",
        "      \"\u{2200} #j. (K( 'c' ) @ #i) \u{21D2} (\u{22A5})\"",
        "",
        "Formula terms",
        "=============",
        "",
        "  Lemma `L2' uses terms of the wrong form: `Xor('a','b')'",
        "  ",
    ]);
    expected.extend(ALLOWED_LINES);
    expected.extend([
        "  ",
        "  Lemma `L3' uses terms of the wrong form:",
        "    `Union('a','b',Xor('c','d'))'",
        "  ",
    ]);
    expected.extend(ALLOWED_LINES);
    expected.extend([
        "  ",
        "  Lemma `L4' uses terms of the wrong form:",
        "    `pair(Bound 1,pair('b',~'n'))'",
        "  ",
    ]);
    expected.extend(ALLOWED_LINES);
    expected.push("*/");
    assert_eq!(wf_block(src), expected.join("\n"));
}

/// `checkQuantifiers` (Wellformedness.hs:948-957) is the FIRST arm, so a
/// formula tripping it and `checkTerms` reports the quantifier finding first;
/// consecutive quantifier findings share one header.
#[test]
fn quantifier_sorts_leads_and_groups_with_its_run() {
    let src = "theory Q1\nbegin\n\
               rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
               lemma q1: \"All ~n #i. A(~n) @ i ==> F\"\n\
               lemma q2: \"All $a #i. A($a) @ i ==> F\"\n\
               restriction r1: \"All ~m #i. A(~m) @ i ==> F\"\n\
               end\n";
    assert_eq!(
        wf_block(src),
        [
            "/*",
            "WARNING: the following wellformedness checks failed!",
            "",
            "Quantifier sorts",
            "================",
            "",
            "  Lemma `q1' uses quantifiers with wrong sort: (\"n\",LSortFresh)",
            "  ",
            "  Lemma `q2' uses quantifiers with wrong sort: (\"a\",LSortPub)",
            "  ",
            "  Restriction `r1' uses quantifiers with wrong sort: (\"m\",LSortFresh)",
            "*/",
        ]
        .join("\n")
    );
}

/// All three arms on ONE formula, in HS's `msum` order — quantifier sorts,
/// formula terms, formula guardedness — then a second run of quantifier
/// findings from the lemmas that only trip the first arm.
#[test]
fn all_three_arms_of_one_formula_come_out_in_msum_order() {
    let src = "theory Q2\nbegin\n\
               rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
               lemma manybad: \"All ~aaaaaaaaaaaa $bbbbbbbbbbbb ~cccccccccccc \
               $dddddddddddd ~eeeeeeeeeeee $ffffffffffff #i. A(x) @ i ==> F\"\n\
               lemma idx: \"All ~n.1 #i. A(~n.1) @ i ==> F\"\n\
               lemma suff: \"All m:fresh #i. A(m:fresh) @ i ==> F\"\n\
               end\n";
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let errs =
        tamarin_theory::formula_reports::formula_reports(&thy, &elaborated.signature.maude_sig);
    let topics: Vec<&str> = errs.iter().map(|e| e.topic.as_str()).collect();
    assert_eq!(
        topics,
        vec![
            "Quantifier sorts",
            "Formula terms",
            " Formula guardedness",
            "Quantifier sorts",
            "Quantifier sorts",
        ]
    );

    // The reopened run gets its own header; `manybad`'s three findings do not
    // share one.
    let rendered = format_wf_block(&errs);
    assert_eq!(
        rendered
            .matches("Quantifier sorts\n================")
            .count(),
        2,
        "two consecutive runs of the quantifier topic:\n{rendered}"
    );
}
