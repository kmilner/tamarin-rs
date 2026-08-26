// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins the LAYOUT of the ` Formula guardedness` report body.
//!
//! HS throws a `Doc`, not a string (Guarded.hs:471-566): the
//! unguarded-variable list is an `fsep` (Guarded.hs:507-514) and each quoted
//! formula is `nest 2 . doubleQuotes . prettyLNFormula` (Guarded.hs:476-477).
//! `checkGuarded`'s `nest 2 err` and `prettyWfErrorReport`'s `nest 2`
//! (Wellformedness.hs:124-125) lay both out at nesting 4 and 6, and the report is
//! rendered with the plain `render`, so the widths are HughesPJ's default
//! 100/67 — a long name list and a long formula both wrap.
//!
//! Expected bytes are the pinned oracle's (Git revision ef3f0468) for the
//! theories below.

use tamarin_parser::parse_theory;
use tamarin_theory::pretty_theory::format_wf_block;

fn wf_block(src: &str) -> String {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let errs = tamarin_theory::wellformedness::formulas::formula_reports(
        &elaborated,
        &elaborated.signature.maude_sig,
    );
    format_wf_block(&errs)
}

/// A formula too wide for the report's nesting: both quotes of it wrap at the
/// `sep`s `prettyLFormula` puts between the quantifier prefix, the antecedent
/// and the conjuncts.
#[test]
fn the_quoted_formula_wraps_at_the_report_nesting() {
    let src = "theory GuardWrap\nbegin\n\
               rule R: [ In(x) ] --[ AA(x, x), BB(x) ]-> [ ]\n\
               lemma with_predicate:\n\
               \"All xx yy zz #i. AA(xx, yy) @ i ==> \
               (Ex #ii #jj. AA(xx, yy) @ ii & BB(zz) @ jj & #ii < #jj) & \
               (Ex #ii #jj. AA(zz, yy) @ ii & BB(xx) @ jj & #ii < #jj)\"\n\
               end\n";

    let quoted = [
        "      \"\u{2200} xx yy zz #i.",
        "        (AA( xx, yy ) @ #i) \u{21D2}",
        "        ((\u{2203} #ii #jj.",
        "           ((AA( xx, yy ) @ #ii) \u{2227} (BB( zz ) @ #jj)) \u{2227} (#ii < #jj)) \u{2227}",
        "         (\u{2203} #ii #jj.",
        "           ((AA( zz, yy ) @ #ii) \u{2227} (BB( xx ) @ #jj)) \u{2227} (#ii < #jj)))\"",
    ];
    let mut expected = vec![
        "/*",
        "WARNING: the following wellformedness checks failed!",
        "",
        " Formula guardedness",
        "====================",
        "",
        "  Lemma `with_predicate' cannot be converted to a guarded formula:",
        "    unguarded variable(s) 'zz' in the subformula",
    ];
    expected.extend(quoted);
    expected.push("    in the formula");
    expected.extend(quoted);
    expected.push("*/");

    assert_eq!(wf_block(src), expected.join("\n"));
}

/// A name list too wide for the report's nesting: `fsep` breaks it between
/// names, and the trailing "in the subformula" words break with it.
#[test]
fn the_unguarded_name_list_wraps_between_names() {
    let vars: Vec<String> = (1..=25).map(|i| format!("x{}", i)).collect();
    let src = format!(
        "theory GuardWrapMany\nbegin\n\
         rule R: [ In(x) ] --[ AA(x) ]-> [ ]\n\
         lemma many:\n\"All {} #i. AA(x1) @ i ==> F\"\nend\n",
        vars.join(" ")
    );

    let quoted = [
        "      \"\u{2200} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18",
        "         x19 x20 x21 x22 x23 x24 x25 #i.",
        "        (AA( x1 ) @ #i) \u{21D2} (\u{22A5})\"",
    ];
    let mut expected = vec![
        "/*",
        "WARNING: the following wellformedness checks failed!",
        "",
        " Formula guardedness",
        "====================",
        "",
        "  Lemma `many' cannot be converted to a guarded formula:",
        "    unguarded variable(s) 'x2', 'x3', 'x4', 'x5', 'x6', 'x7', 'x8',",
        "    'x9', 'x10', 'x11', 'x12', 'x13', 'x14', 'x15', 'x16', 'x17',",
        "    'x18', 'x19', 'x20', 'x21', 'x22', 'x23', 'x24', 'x25' in the",
        "    subformula",
    ];
    expected.extend(quoted);
    expected.push("    in the formula");
    expected.extend(quoted);
    expected.push("*/");

    assert_eq!(wf_block(&src), expected.join("\n"));
}
