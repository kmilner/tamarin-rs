// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of HS `formulaReports` (Wellformedness.hs:996-1015) — the
//! wellformedness pass over every lemma / restriction formula.
//!
//! HS runs it as ONE list-monad loop:
//!
//! ```text
//! formulaReports thy = do
//!     (header, fm) <- annFormulas
//!     msum [ ((,) (underlineTopic "Quantifier sorts"))     <$> checkQuantifiers header fm
//!          , ((,) (underlineTopic "Formula terms"))        <$> checkTerms header maudeSig fm
//!          , ((,) (underlineTopic " Formula guardedness")) <$> checkGuarded header fm
//!          ]
//! ```
//!
//! Two consequences the report bytes depend on:
//!
//!   * `WfErrorReport = [WfError]`, so the list monad's `msum` is `concat`
//!     and `<$>` is `map`: all three checks run UNCONDITIONALLY for every
//!     formula and their findings are concatenated.  A formula that trips
//!     both `checkTerms` and `checkGuarded` is reported twice.
//!   * The three topics are emitted PER FORMULA, so they interleave in item
//!     order, and a topic REOPENS after an intervening one.  Since
//!     `prettyWfErrorReport` groups with `groupOn fst = groupBy ((==) `on`
//!     fst)` (Extension/Prelude.hs:96-97), which only merges CONSECUTIVE
//!     entries, each run gets its own underlined header — e.g. `Formula
//!     terms` / ` Formula guardedness` / `Formula terms` for three lemmas
//!     where only the middle one is unguardable.  Splicing all findings of
//!     one topic together instead would collapse those runs into a single
//!     header and reorder the bodies.
//!
//! `annFormulas` is `lemmas <|> restrictions`, and `<|>` on lists is `++`,
//! so it is ALL lemmas (theory order) followed by ALL restrictions (theory
//! order) — not a single interleaved item walk.
//!
//! The formulas the three arms read are macro- and predicate-expanded:
//! `annFormulas` applies `applyMacroInFormula (theoryMacros thy)` itself, and
//! predicates are inlined at PARSE time
//! (`liftedAddLemma`→`expandLemma`→`expandFormula`, Theory/Text/Parser.hs:145-147;
//! `liftedAddRestriction`→`expandRestriction`, lines 132-134).  The elaborated
//! [`Lemma::formula`](crate::theory::Lemma::formula) and
//! [`Restriction::formula`](crate::restriction::ProtoRestriction::formula) are
//! that formula: `elaborate` inlines the predicates and applies the theory's
//! macros as it builds each item, so all three checks see the inlined
//! predicate bodies — including their terms and their quantifiers.

use tamarin_term::lterm::LSort;

use crate::formula::LNFormula;
use crate::pretty_hpj::{fsep, punctuate, Doc};
use crate::theory::{Theory, TheoryItem};

use super::check_terms::{check_terms, WF_WIDTH};
use super::{underline_topic, WfError};

/// HS `underlineTopic "Quantifier sorts"` (Wellformedness.hs:1002).
const QUANTIFIER_TOPIC: &str = "Quantifier sorts";

/// HS `annFormulas` (Wellformedness.hs:1006-1014): the annotated formulas
/// `formulaReports` checks, as `(header, formula)` pairs.  `<|>` on lists is
/// `++`, so this is ALL lemmas in theory order followed by ALL restrictions
/// in theory order.  Headers are HS's `"Lemma " ++ quote name` /
/// `"Restriction " ++ quote name`.
fn ann_formulas(thy: &Theory) -> Vec<(String, &LNFormula)> {
    let mut lemmas: Vec<(String, &LNFormula)> = Vec::new();
    let mut restrictions: Vec<(String, &LNFormula)> = Vec::new();
    for item in &thy.items {
        match item {
            TheoryItem::Lemma(l) => lemmas.push((format!("Lemma `{}'", l.name), &l.formula)),
            TheoryItem::Restriction(r) => {
                restrictions.push((format!("Restriction `{}'", r.name), &r.formula))
            }
            _ => {}
        }
    }
    lemmas.extend(restrictions);
    lemmas
}

/// Port of HS `formulaReports` (Wellformedness.hs:996-1015): one pass over
/// `annFormulas` running `checkQuantifiers`, `checkTerms` and `checkGuarded`
/// per formula, so the three topics interleave exactly as HS emits them.
///
/// `thy` is the TRANSLATED theory — HS's single `checkWellformedness` runs on
/// the `OpenTranslatedTheory` (`checkTranslatedTheory`,
/// TheoryLoader.hs:559-565, fed by `closeTheory` at :726-728), so
/// `annFormulas` also covers the restrictions SAPIC's `let … else` / `if`
/// lowering mints and the lemmas the accountability translation appends.
/// `checkTerms` classifies against the theory's own signature (HS `get
/// (sigpMaudeSig . thySignature) thy`, Wellformedness.hs:1003).
pub fn formula_reports(thy: &Theory) -> Vec<WfError> {
    let sig = &thy.signature.maude_sig;
    let mut out: Vec<WfError> = Vec::new();
    for (header, fm) in ann_formulas(thy) {
        // HS `msum [checkQuantifiers, checkTerms, checkGuarded]` = `concat`:
        // every arm runs for every formula, findings concatenated in this
        // order (Wellformedness.hs:1002-1004).
        out.extend(check_quantifiers(&header, fm));
        out.extend(check_terms(sig, &header, fm));
        out.extend(check_guarded_entry(&header, fm));
    }
    out
}

/// Port of HS `checkGuarded` (Wellformedness.hs:988-993): the finding for one
/// annotated formula that fails `formulaToGuarded`.  `header` is HS's
/// `"Lemma `n'"` / `"Restriction `n'"`.
///
/// Message layout, matching HS's `prettyWfErrorReport` + `checkGuarded`:
///
/// ```text
///  Formula guardedness
/// ====================
///
///   {header} cannot be converted to a guarded formula:
///     {error_text}
///       "{sub_formula}"
///     in the formula
///       "{full_formula}"
/// ```
///
/// Indentation: 2 (`prettyWfErrorReport`'s `nest 2`) + 2 (`checkGuarded`'s
/// `nest 2 err`) + 2 (`ppFormula`'s `nest 2`) = 6 spaces for formula text.
fn check_guarded_entry(header: &str, formula: &LNFormula) -> Option<WfError> {
    use crate::pretty_formula::{doublequoted_nested_doc_default_width, lnformula_doc};
    use crate::pretty_hpj as hpj;

    let e = match crate::guarded::formula_to_guarded(formula) {
        Ok(_) => return None,
        Err(e) => e,
    };

    let full_formula_doc = lnformula_doc(formula);

    // HS `ppFormula f0` (Guarded.hs:513, :562) quotes the innermost failing
    // quantifier; `ppError`'s own `ppFormula fmOrig` (Guarded.hs:479) quotes
    // the whole formula.  A failure outside a quantifier quotes the whole
    // formula in both places.
    let sub_formula_doc = e
        .subject_formula
        .as_ref()
        .map(lnformula_doc)
        .unwrap_or_else(|| full_formula_doc.clone());

    // The `underlineTopic` of " Formula guardedness" includes the trailing
    // newline; the blank line after it is `ppTopic`'s `$-$` in
    // `prettyWfErrorReport`.
    let topic = " Formula guardedness";
    let mut msg = String::new();
    msg.push_str(&underline_topic(topic));
    msg.push('\n');
    msg.push_str("  ");
    msg.push_str(header);
    msg.push_str(" cannot be converted to a guarded formula:\n");

    // `nest 2` (`prettyWfErrorReport`) + `nest 2 err` (`checkGuarded`) over
    // the thrown message Doc.
    msg.push_str(
        &e.message_doc()
            .nest(4)
            .render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON),
    );
    msg.push('\n');

    // Each formula is `nest 2 . doubleQuotes . prettyLNFormula`
    // (Guarded.hs:476-477) under the two enclosing `nest 2`s, so it is a
    // `Doc` laid out at nesting 6 and wraps at the page width.
    msg.push_str(&doublequoted_nested_doc_default_width(sub_formula_doc, 6));
    msg.push('\n');
    msg.push_str("    in the formula\n");
    msg.push_str(&doublequoted_nested_doc_default_width(full_formula_doc, 6));
    msg.push('\n');

    Some(WfError::new(topic, msg))
}

/// Port of HS `checkQuantifiers` (Wellformedness.hs:948-957): every binder
/// whose sort is not `LSortMsg` / `LSortNode` / `LSortNat` is an offender, so
/// quantifying over a fresh (`~x`) or public (`$x`) variable is flagged.
///
/// The binders are the formula's `(String, LSort)` HINTS, collected by HS's
/// `foldFormula` with `\_ binder rest -> binder : rest` over `const mappend`
/// connectives, i.e. in document order, outermost binder first.
fn check_quantifiers(header: &str, fm: &LNFormula) -> Option<WfError> {
    let mut binders: Vec<&(String, LSort)> = Vec::new();
    collect_binders(fm, &mut binders);

    // HS `show (name, sort)` of the `(String, LSort)` binder, with `LSort`'s
    // derived `Show` ("LSortPub"/"LSortFresh"); the variable's index is not
    // part of the binder pair, so `~n.1` shows as `("n",LSortFresh)`.
    let disallowed: Vec<String> = binders
        .iter()
        .filter_map(|(name, sort)| {
            disallowed_sort_show(*sort).map(|s| format!("(\"{}\",{})", name, s))
        })
        .collect();
    if disallowed.is_empty() {
        return None;
    }

    // fsep $ (text (header ++ " uses quantifiers with wrong sort:"))
    //      : punctuate comma (map (nest 2 . text . show) disallowed)
    let mut items = vec![Doc::text(format!(
        "{} uses quantifiers with wrong sort:",
        header
    ))];
    items.extend(punctuate(
        Doc::text(","),
        disallowed
            .into_iter()
            .map(|d| Doc::text(d).nest(2))
            .collect(),
    ));
    let line = fsep(items).nest(2).render_with(WF_WIDTH, WF_WIDTH);

    // Bake the block (header + `ppTopic`'s `$-$` blank line + nest-2 body)
    // into the message, as the other `formulaReports` arms do; the report
    // renderer sheds the repeated header within a consecutive run.
    let mut msg = underline_topic(QUANTIFIER_TOPIC);
    msg.push('\n');
    msg.push_str(&line);
    Some(WfError::new(QUANTIFIER_TOPIC, msg))
}

/// HS's `show` of the binder's `LSort` when that sort is NOT one of
/// `[LSortMsg, LSortNode, LSortNat]` (Wellformedness.hs:957), else `None`.
/// A bare binder is `LSortMsg`: the sort of a quantified variable comes
/// from its prefix or suffix alone, never from inference.
fn disallowed_sort_show(sort: LSort) -> Option<&'static str> {
    match sort {
        LSort::Pub => Some("LSortPub"),
        LSort::Fresh => Some("LSortFresh"),
        LSort::Msg | LSort::Node | LSort::Nat => None,
    }
}

/// Collect the formula's binder hints in HS `foldFormula` order — a
/// quantifier contributes its own hint before its body's, and a connective
/// its left operand's before its right's.  A source `All x y. …` closes into
/// nested `Qua`s, so its binders come out left to right.
fn collect_binders<'a>(fm: &'a LNFormula, out: &mut Vec<&'a (String, LSort)>) {
    use crate::formula::ProtoFormula;
    match fm {
        ProtoFormula::Tf(_) | ProtoFormula::Atom(_) => {}
        ProtoFormula::Not(f) => collect_binders(f, out),
        ProtoFormula::Conn(_, l, r) => {
            collect_binders(l, out);
            collect_binders(r, out);
        }
        ProtoFormula::Qua(_, hint, body) => {
            out.push(hint);
            collect_binders(body, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    fn reports(src: &str) -> Vec<WfError> {
        let thy = parse_theory(src, &[]).expect("parse");
        let elaborated = crate::elaborate::elaborate(&thy).expect("elaborate");
        formula_reports(&elaborated)
    }

    /// `annFormulas = lemmas <|> restrictions` (Wellformedness.hs:1006-1014):
    /// all lemmas in theory order, then all restrictions — NOT a single
    /// item-order walk.  Bytes pinned to the oracle (Git revision ef3f0468)
    /// for the theory below, whose items alternate restriction / lemma.
    #[test]
    fn ann_formulas_puts_every_lemma_before_every_restriction() {
        let src = "theory Ord2\nbegin\n\
                   builtins: diffie-hellman\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   restriction rA: \"All x #i. A(x^x) @ i ==> F\"\n\
                   lemma lB: \"All y #j. A(y^y) @ j ==> F\"\n\
                   restriction rC: \"All ~q #i. A(~q) @ i ==> F\"\n\
                   lemma lD: \"All ~r #j. A(~r) @ j ==> F\"\n\
                   end\n";
        let errs = reports(src);
        let got: Vec<(&str, &str)> = errs
            .iter()
            .map(|e| {
                let item = e
                    .message
                    .lines()
                    .find(|l| l.starts_with("  Lemma") || l.starts_with("  Restriction"))
                    .expect("body names its item");
                (
                    e.topic.as_str(),
                    item.split_whitespace().nth(1).expect("item name"),
                )
            })
            .collect();
        assert_eq!(
            got,
            vec![
                ("Formula terms", "`lB'"),
                (QUANTIFIER_TOPIC, "`lD'"),
                ("Formula terms", "`rA'"),
                (QUANTIFIER_TOPIC, "`rC'"),
            ]
        );
    }

    /// `msum` = `concat` per formula, so the three topics interleave and a
    /// topic reopens after an intervening one (Wellformedness.hs:999-1005).
    /// Oracle bytes: `Formula terms` / ` Formula guardedness` / `Formula
    /// terms` as THREE groups for this theory.
    #[test]
    fn topics_interleave_per_formula() {
        let src = "theory Interleave\nbegin\n\
                   builtins: diffie-hellman\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   lemma l1: \"All x #i. A(x^x) @ i ==> F\"\n\
                   lemma l2: \"All z. z = z\"\n\
                   lemma l3: \"All y #j. A(y^y) @ j ==> F\"\n\
                   end\n";
        let topics: Vec<String> = reports(src).iter().map(|e| e.topic.clone()).collect();
        assert_eq!(
            topics,
            vec!["Formula terms", " Formula guardedness", "Formula terms"]
        );
    }

    /// A formula tripping two arms is reported by BOTH — `msum` on lists
    /// concatenates, it does not pick the first success.
    #[test]
    fn one_formula_can_trip_several_arms() {
        let src = "theory C\nbegin\n\
                   builtins: xor, multiset\n\
                   lemma L1: \"All #j. K('c') @ i ==> F\"\n\
                   lemma L2: \"All #i. Test('b' XOR 'a') @ #i ==> F\"\n\
                   end\n";
        let topics: Vec<String> = reports(src).iter().map(|e| e.topic.clone()).collect();
        assert_eq!(
            topics,
            vec!["Formula terms", " Formula guardedness", "Formula terms"],
            "L1 trips checkTerms AND checkGuarded, L2 only checkTerms"
        );
    }

    /// `checkQuantifiers` (Wellformedness.hs:948-957) flags fresh- and
    /// public-sorted binders.  Bytes are the pinned oracle's for `q1.spthy`.
    #[test]
    fn quantifier_sorts_flags_fresh_and_pub_binders() {
        let src = "theory Q1\nbegin\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   lemma q1: \"All ~n #i. A(~n) @ i ==> F\"\n\
                   lemma q2: \"All $a #i. A($a) @ i ==> F\"\n\
                   restriction r1: \"All ~m #i. A(~m) @ i ==> F\"\n\
                   end\n";
        let errs = reports(src);
        let bodies: Vec<&str> = errs.iter().map(|e| e.message.as_str()).collect();
        assert_eq!(
            bodies,
            vec![
                "Quantifier sorts\n================\n\n  Lemma `q1' uses quantifiers with wrong sort: (\"n\",LSortFresh)",
                "Quantifier sorts\n================\n\n  Lemma `q2' uses quantifiers with wrong sort: (\"a\",LSortPub)",
                "Quantifier sorts\n================\n\n  Restriction `r1' uses quantifiers with wrong sort: (\"m\",LSortFresh)",
            ]
        );
    }

    /// Node-, message- and nat-sorted binders are allowed
    /// (`[LSortMsg, LSortNode, LSortNat]`, Wellformedness.hs:957), and the
    /// binder's index is not part of the shown pair (`~n.1` → `("n",…)`).
    #[test]
    fn quantifier_sorts_allows_msg_node_binders_and_drops_the_index() {
        let src = "theory Q2\nbegin\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   lemma ok: \"All z #i. A(z) @ i ==> F\"\n\
                   lemma idx: \"All ~n.1 #i. A(~n.1) @ i ==> F\"\n\
                   lemma suff: \"All m:fresh #i. A(m:fresh) @ i ==> F\"\n\
                   end\n";
        let errs = reports(src);
        assert_eq!(errs.len(), 2, "only the fresh-sorted binders are flagged");
        assert!(errs[0]
            .message
            .ends_with("  Lemma `idx' uses quantifiers with wrong sort: (\"n\",LSortFresh)"));
        assert!(errs[1]
            .message
            .ends_with("  Lemma `suff' uses quantifiers with wrong sort: (\"m\",LSortFresh)"));
    }

    /// `fsep`'s wrap at [`WF_WIDTH`]: the whole list moves to the next line
    /// (nested 4) once the header line would overflow.  Bytes pinned to the
    /// oracle for `q2.spthy`'s six-binder lemma.
    #[test]
    fn quantifier_sorts_wraps_its_offender_list() {
        let src = "theory Q3\nbegin\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   lemma manybad: \"All ~aaaaaaaaaaaa $bbbbbbbbbbbb ~cccccccccccc \
                   $dddddddddddd ~eeeeeeeeeeee $ffffffffffff #i. A(x) @ i ==> F\"\n\
                   end\n";
        let errs = reports(src);
        assert_eq!(errs[0].topic, QUANTIFIER_TOPIC);
        assert_eq!(
            errs[0].message,
            "Quantifier sorts\n================\n\n  \
             Lemma `manybad' uses quantifiers with wrong sort:\n    \
             (\"aaaaaaaaaaaa\",LSortFresh), (\"bbbbbbbbbbbb\",LSortPub),\n    \
             (\"cccccccccccc\",LSortFresh), (\"dddddddddddd\",LSortPub),\n    \
             (\"eeeeeeeeeeee\",LSortFresh), (\"ffffffffffff\",LSortPub)"
        );
    }

    /// `annFormulas` applies `applyMacroInFormula (theoryMacros thy)`
    /// (Wellformedness.hs:1007-1014), so a macro call is reported as its
    /// expansion.  Oracle bytes for the theory below (Git revision ef3f0468):
    /// `exp(Bound 1,Bound 1)`, not the `sq` call.
    #[test]
    fn a_macro_call_is_reported_as_its_expansion() {
        let src = "theory MacroFT\nbegin\n\
                   builtins: diffie-hellman\n\
                   macros: sq(x) = x^x\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   lemma lm: \"All x #i. A(sq(x)) @ i ==> F\"\n\
                   end\n";
        let errs = reports(src);
        let topics: Vec<&str> = errs.iter().map(|e| e.topic.as_str()).collect();
        assert_eq!(topics, vec!["Formula terms"]);
        assert!(
            errs[0]
                .message
                .contains("  Lemma `lm' uses terms of the wrong form: `exp(Bound 1,Bound 1)'"),
            "offender is the expanded term: {}",
            errs[0].message
        );
    }

    /// Predicates are inlined at PARSE time in HS, so all three arms see the
    /// predicate body — its terms AND its quantifiers.  Oracle bytes for
    /// `pred.spthy`: `("s",LSortFresh)` and `exp(Bound 3,Bound 3)`.
    #[test]
    fn predicate_bodies_are_checked() {
        let src = "theory PredP\nbegin\n\
                   builtins: diffie-hellman\n\
                   predicates: P(x) <=> (Ex ~s #k. A(x^x) @ k & A(~s) @ k)\n\
                   rule R: [ In(x) ] --[ A(x) ]-> [ Out(x) ]\n\
                   lemma lp: \"All x #i. A(x) @ i ==> P(x)\"\n\
                   end\n";
        let errs = reports(src);
        let topics: Vec<&str> = errs.iter().map(|e| e.topic.as_str()).collect();
        assert_eq!(topics, vec![QUANTIFIER_TOPIC, "Formula terms"]);
        assert!(errs[0]
            .message
            .ends_with("  Lemma `lp' uses quantifiers with wrong sort: (\"s\",LSortFresh)"));
        assert!(
            errs[1].message.contains("`exp(Bound 3,Bound 3)'"),
            "offender is the predicate body's term at its inlined De Bruijn depth: {}",
            errs[1].message
        );
    }
}
