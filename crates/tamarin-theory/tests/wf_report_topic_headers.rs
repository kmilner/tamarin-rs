// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins the one-header-per-topic layout `prettyWfErrorReport` gives every
//! wellformedness group.
//!
//! HS renders each `groupOn fst` group as
//! `text topic $-$ (nest 2 . vcat . intersperse (text "") $ map snd errs)`
//! (Wellformedness.hs:118-125): the `underlineTopic` header ONCE, then every
//! body indented two spaces and separated by a two-space blank line.  The
//! theories below reach that renderer from both directions — checks whose
//! bodies carry neither header nor indent (`freshFactArguments'`,
//! Wellformedness.hs:569-576; `multRestrictedReport'`,
//! Wellformedness.hs:1047-1064) and a check whose bodies bake the header in
//! (`formulaReports`, Wellformedness.hs:999-1005, see line 1003).
//!
//! Expected bytes are the pinned oracle's (Git revision ef3f0468).

use tamarin_parser::parse_theory;
use tamarin_theory::pretty_theory::format_wf_block;

/// The `/* WARNING … */` comment both load pipelines render.
fn load_wf_block(src: &str) -> String {
    let parsed = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    format_wf_block(&tamarin_theory::wellformedness::check_wellformedness(
        &elaborated,
        None,
    ))
}

/// The `Formula terms` findings of the elaborated theory: the `checkTerms`
/// arm of HS's `formulaReports` loop (Wellformedness.hs:1003), which is the
/// path both load pipelines take.
fn formula_terms_report(src: &str) -> Vec<tamarin_theory::wellformedness::WfError> {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    tamarin_theory::wellformedness::formulas::formula_reports(
        &elaborated,
        &elaborated.signature.maude_sig,
    )
    .into_iter()
    .filter(|e| e.topic == "Formula terms")
    .collect()
}

/// `unboundReport` is HS check index 2 and `lemmaAttributeReport` index 9
/// (Wellformedness.hs:1270-1286), so the unbound group opens the block.
/// Bytes are the pinned oracle's (Git revision ef3f0468) for this theory
/// under `--derivcheck-timeout=0`.
#[test]
fn unbound_group_precedes_a_later_topic() {
    let src = "theory SpliceOrder\nbegin\n\
               rule R: [ ] --[ A( ) ]-> [ Out(~k) ]\n\
               lemma L [reuse]:\n  exists-trace \"Ex #i. A( ) @ #i\"\n\
               end\n";
    assert_eq!(
        load_wf_block(src),
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Unbound variables\n=================\n\n  \
         rule `R' has unbound variables: \n    ~k\n\n\
         Lemma annotations\n=================\n\n  \
         Lemma `L': cannot reuse 'exists-trace' lemmas\n*/"
    );
}

/// `freshFactArguments'` pairs the underlined topic with a bare
/// `text ("rule " ++ quote …) <-> text "fact:" <-> prettyLNFact fa`
/// (Wellformedness.hs:574-576), so header, indent and separator all come from
/// `prettyWfErrorReport`.
#[test]
fn fr_fact_topic_prints_its_underlined_header_once() {
    let src = "theory Fr2Probe begin\n\
               rule T1: [ Fr( pair(a,b) ) ] --[ ]-> []\n\
               rule T2: [ Fr( 'c' ) ] --[ ]-> []\n\
               end\n";
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let report = tamarin_theory::wellformedness::check_wellformedness(&elaborated, None);
    assert_eq!(
        format_wf_block(&report),
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Fr facts must only use a fresh- or a msg-variable\n\
         =================================================\n\n  \
         rule `T1' fact: Fr( <a, b> )\n  \n  rule `T2' fact: Fr( 'c' )\n*/"
    );
}

/// `checkTerms` bodies arrive with the header baked in, one copy per lemma
/// (`formulaReports`, Wellformedness.hs:999-1005, see line 1003), so a two-lemma group
/// keeps only the first copy and separates the bodies with the two-space
/// blank line `intersperse (text "")` renders under `nest 2`.
#[test]
fn formula_terms_group_prints_its_header_once() {
    let src = "theory FTProbe begin\n\
               builtins: diffie-hellman\n\
               rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
               lemma l1: \"All x #i. A(x^x) @ i ==> F\"\n\
               lemma l2: \"All y #j. A(y^y) @ j ==> F\"\n\
               end\n";
    let errs = formula_terms_report(src);
    assert_eq!(errs.len(), 2, "one entry per offending lemma");
    let body = "uses terms of the wrong form: `exp(Bound 1,Bound 1)'\n  \n  \
                The only allowed terms are public constants and bound node and\n  \
                message variables. If you encounter free message variables, then\n  \
                you might have forgotten a #-prefix. Sort prefixes can only be\n  \
                dropped where this is unambiguous. Moreover, reducible function\n  \
                symbols are disallowed.";
    assert_eq!(
        format_wf_block(&errs),
        format!(
            "/*\nWARNING: the following wellformedness checks failed!\n\n\
             Formula terms\n=============\n\n  \
             Lemma `l1' {body}\n  \n  Lemma `l2' {body}\n*/"
        )
    );
}

/// `multRestrictedReport'` also pairs the underlined topic with a body that
/// carries no header (Wellformedness.hs:1047-1064, see line 1050), but that
/// body bakes in `ppTopic`'s `nest 2` itself, because its `prettyProtoRuleE`
/// dumps make their `sep`/`fsep` wrap decisions at the indented column.  Two
/// offending rules therefore land in ONE group whose header appears once and
/// whose bodies are joined by the two-space blank line.
#[test]
fn multiplication_restriction_topic_prints_its_underlined_header() {
    let src = "theory MultProbe begin\n\
               builtins: diffie-hellman\n\
               rule R1: [ In(x), In(y) ] --> [ Out(x*y) ]\n\
               rule R2: [ In(a), In(b) ] --> [ Out(a*b) ]\n\
               end\n";
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let errs = tamarin_theory::wellformedness::mult::mult_restricted_report(
        &elaborated,
        &elaborated.signature.maude_sig,
    );
    assert_eq!(errs.len(), 2, "one entry per offending rule");
    let entry = |name: &str, term: &str, prems: &str| {
        format!(
            "  The following rule is not multiplication restricted:\n    \
             rule (modulo E) {name}:\n       \
             [ {prems} ] --> [ Out( ({term}) ) ]\n  \n  \
             After replacing reducible function symbols in lhs with variables:\n    \
             rule (modulo E) {name}:\n       \
             [ {prems} ] --> [ Out( ({term}) ) ]\n  \n    \
             Terms with multiplication:  ({term})"
        )
    };
    assert_eq!(
        format_wf_block(&errs),
        format!(
            "/*\nWARNING: the following wellformedness checks failed!\n\n\
             Multiplication restriction of rules\n\
             ===================================\n\n{}\n  \n{}\n*/",
            entry("R1", "x*y", "In( x ), In( y )"),
            entry("R2", "a*b", "In( a ), In( b )"),
        )
    );
}

/// The paragraph every `checkTerms` body ends with (Wellformedness.hs:968-973),
/// already at the two-space indent `ppTopic` gives a group's bodies.
const ALLOWED_LINES: &[&str] = &[
    "  The only allowed terms are public constants and bound node and",
    "  message variables. If you encounter free message variables, then",
    "  you might have forgotten a #-prefix. Sort prefixes can only be",
    "  dropped where this is unambiguous. Moreover, reducible function",
    "  symbols are disallowed.",
];

/// Two offending RESTRICTIONS — the shape SAPIC's `let … else` lowering mints,
/// one `Restr_<rule>_<i>` per else-branch, each carrying its branch's
/// right-hand side verbatim.  Both land in `annFormulas`
/// (Wellformedness.hs:1006-1015) back to back, so `groupOn fst` puts them in
/// ONE group under a single header.
///
/// Bytes are the pinned oracle's (Git revision ef3f0468).
#[test]
fn formula_terms_restriction_group_prints_its_header_once() {
    let src = "theory RestrPair\nbegin\n\
               builtins: diffie-hellman\n\
               restriction Restr_letpqrabbc_2__1:\n  \
               \"All #NOW. Restr_letpqrabbc_2__1() @ #NOW ==> \
               (All p q r. <<p, q>, r> = <<'a'^'b', 'b'>, 'c'> ==> F)\"\n\
               restriction Restr_letstcde_2_2_1:\n  \
               \"All #NOW. Restr_letstcde_2_2_1() @ #NOW ==> \
               (All s t. <s, t> = <'c'^'d', 'e'> ==> F)\"\n\
               end\n";
    let errs = formula_terms_report(src);
    assert_eq!(errs.len(), 2, "one entry per offending restriction");

    let mut expected: Vec<&str> = vec![
        "/*",
        "WARNING: the following wellformedness checks failed!",
        "",
        "Formula terms",
        "=============",
        "",
        "  Restriction `Restr_letpqrabbc_2__1' uses terms of the wrong form:",
        "    `pair(pair(exp('a','b'),'b'),'c')'",
        "  ",
    ];
    expected.extend(ALLOWED_LINES);
    expected.extend([
        "  ",
        "  Restriction `Restr_letstcde_2_2_1' uses terms of the wrong form:",
        "    `pair(exp('c','d'),'e')'",
        "  ",
    ]);
    expected.extend(ALLOWED_LINES);
    expected.push("*/");
    assert_eq!(format_wf_block(&errs), expected.join("\n"));
}

/// Two offending LEMMAS whose bodies wrap differently — `L2` has two offenders,
/// so its `fsep` breaks the comma-punctuated list over two lines while `L1`'s
/// single offender takes one.  Both sit in the same group, so the header and
/// the `intersperse (text "")` separator must not track the body layout.
///
/// Bytes are the pinned oracle's (Git revision ef3f0468).
#[test]
fn formula_terms_lemma_group_prints_its_header_once() {
    let src = "theory EmCTier\nbegin\n\
               builtins: bilinear-pairing\n\
               functions: f/2, aaa/2\n\
               rule R1:\n  \
               [ Fr(~a), Fr(~b) ]\n\
               --[ Test(em(~a, ~b) * f(~a, ~b)), Test2(em(~a, ~b) * aaa(~a, ~b)) ]->\n  \
               [ Out(em(~a, ~b) * f(~a, ~b)) ]\n\
               lemma L1:\n  \
               \"All #i. Test(em('g', 'h') * f('g', 'h')) @ #i ==> F\"\n\
               lemma L2:\n  \
               \"All x y #i. Test2(em(x, y) * aaa(x, y)) @ #i ==> \
               Ex #j. Test(em(x, y) * f(x, y)) @ #j\"\n\
               end\n";
    let errs = formula_terms_report(src);
    assert_eq!(errs.len(), 2, "one entry per offending lemma");

    let mut expected: Vec<&str> = vec![
        "/*",
        "WARNING: the following wellformedness checks failed!",
        "",
        "Formula terms",
        "=============",
        "",
        "  Lemma `L1' uses terms of the wrong form:",
        "    `Mult(f('g','h'),em('g','h'))'",
        "  ",
    ];
    expected.extend(ALLOWED_LINES);
    expected.extend([
        "  ",
        "  Lemma `L2' uses terms of the wrong form:",
        "    `Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))',",
        "    `Mult(f(Bound 3,Bound 2),em(Bound 2,Bound 3))'",
        "  ",
    ]);
    expected.extend(ALLOWED_LINES);
    expected.push("*/");
    assert_eq!(format_wf_block(&errs), expected.join("\n"));
}
