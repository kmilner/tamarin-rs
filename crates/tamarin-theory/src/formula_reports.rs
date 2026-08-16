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
//! The formulas HS reads here are already macro- and predicate-expanded:
//! `applyMacroInFormula (theoryMacros thy)` is applied in `annFormulas`
//! itself, and predicates are inlined at PARSE time
//! (`liftedAddLemma`→`expandLemma`→`expandFormula`, Theory/Text/Parser.hs:145-147;
//! `liftedAddRestriction`→`expandRestriction`, lines 132-134), so all three
//! checks see the inlined predicate bodies — including their terms and
//! their quantifiers.

use tamarin_parser::ast as p;
use tamarin_parser::wf::{underline_topic, WfError};
use tamarin_term::maude_sig::MaudeSig;

use crate::check_terms::{TermChecker, WF_WIDTH};
use crate::pretty_hpj::{fsep, punctuate, Doc};

/// HS `underlineTopic "Quantifier sorts"` (Wellformedness.hs:1002).
const QUANTIFIER_TOPIC: &str = "Quantifier sorts";

/// HS `annFormulas` (Wellformedness.hs:1006-1014): the annotated formulas
/// `formulaReports` checks, as `(header, formula)` pairs.  `<|>` on lists is
/// `++`, so this is ALL lemmas in theory order followed by ALL restrictions
/// in theory order.  Headers are HS's `"Lemma " ++ quote name` /
/// `"Restriction " ++ quote name`.
///
/// Macros must already be expanded by the caller (HS applies
/// `applyMacroInFormula` here).
pub(crate) fn ann_formulas(thy: &p::Theory) -> Vec<(String, &p::Formula)> {
    let mut lemmas: Vec<(String, &p::Formula)> = Vec::new();
    let mut restrictions: Vec<(String, &p::Formula)> = Vec::new();
    for item in &thy.items {
        match item {
            p::TheoryItem::Lemma(l) => lemmas.push((format!("Lemma `{}'", l.name), &l.formula)),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
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
/// `thy` is the TRANSLATED parser theory — HS's single `checkWellformedness`
/// runs on the `OpenTranslatedTheory` (`checkTranslatedTheory`,
/// TheoryLoader.hs:559-565, fed by `closeTheory` at :726-728), so
/// `annFormulas` also covers the restrictions SAPIC's `let … else` / `if`
/// lowering mints and the lemmas the accountability translation appends.
/// `sig` is the elaborated `MaudeSig`, for `checkTerms`'s
/// `irreducibleFunSyms` classification.
pub fn formula_reports(thy: &p::Theory, sig: &MaudeSig) -> Vec<WfError> {
    // Both expansions mirror what HS's formulas have already undergone by
    // the time `formulaReports` reads them (see the module docs): macros via
    // `annFormulas`'s own `applyMacroInFormula`, predicates at parse time.
    // A predicate-expansion error (e.g. an undefined predicate) is surfaced
    // by the elaborate path; here we keep the macro-only form so the checks
    // still run on what they can.
    let mut expanded = thy.clone();
    crate::macro_expand::expand_theory_macros(&mut expanded);
    let _ = crate::predicate_expand::expand_theory_formulas(&mut expanded);

    let terms = TermChecker::new(sig);
    let mut out: Vec<WfError> = Vec::new();
    for (header, fm) in ann_formulas(&expanded) {
        // HS `msum [checkQuantifiers, checkTerms, checkGuarded]` = `concat`:
        // every arm runs for every formula, findings concatenated in this
        // order (Wellformedness.hs:1002-1004).
        out.extend(check_quantifiers(&header, fm));
        out.extend(terms.check(&header, fm));
        out.extend(crate::elaborate::check_guarded_entry(&header, fm));
    }
    out
}

/// Port of HS `checkQuantifiers` (Wellformedness.hs:948-957): every binder
/// whose sort is not `LSortMsg` / `LSortNode` / `LSortNat` is an offender, so
/// quantifying over a fresh (`~x`) or public (`$x`) variable is flagged.
///
/// The binders are collected by HS's `foldFormula` with
/// `\_ binder rest -> binder : rest` over `const mappend` connectives, i.e.
/// in document order, outermost binder first.
fn check_quantifiers(header: &str, fm: &p::Formula) -> Option<WfError> {
    let mut binders: Vec<&p::VarSpec> = Vec::new();
    collect_binders(fm, &mut binders);

    // HS `show (name, sort)` of the `(String, LSort)` binder, with `LSort`'s
    // derived `Show` ("LSortPub"/"LSortFresh"); the variable's index is not
    // part of the binder pair, so `~n.1` shows as `("n",LSortFresh)`.
    let disallowed: Vec<String> = binders
        .iter()
        .filter_map(|v| disallowed_sort_show(v.sort).map(|s| format!("(\"{}\",{})", v.name, s)))
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
/// An untagged binder is `LSortMsg`: the sort of a quantified variable comes
/// from its prefix / suffix alone, never from inference.
fn disallowed_sort_show(sort: p::SortHint) -> Option<&'static str> {
    match sort {
        p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => Some("LSortPub"),
        p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => Some("LSortFresh"),
        p::SortHint::Msg
        | p::SortHint::Node
        | p::SortHint::Nat
        | p::SortHint::Untagged
        | p::SortHint::Suffix(p::SuffixSort::Msg)
        | p::SortHint::Suffix(p::SuffixSort::Node)
        | p::SortHint::Suffix(p::SuffixSort::Nat) => None,
    }
}

/// Collect the formula's binders in HS `foldFormula` order — a quantifier
/// contributes its own binder before its body's, and a connective its left
/// operand's before its right's.
fn collect_binders<'a>(fm: &'a p::Formula, out: &mut Vec<&'a p::VarSpec>) {
    match fm {
        p::Formula::False | p::Formula::True | p::Formula::Atom(_) => {}
        p::Formula::Not(f) => collect_binders(f, out),
        p::Formula::And(l, r)
        | p::Formula::Or(l, r)
        | p::Formula::Implies(l, r)
        | p::Formula::Iff(l, r) => {
            collect_binders(l, out);
            collect_binders(r, out);
        }
        // A multi-variable `All x y. …` is nested `Quant`s in HS, so the
        // binders come out left to right, then the body's.
        p::Formula::Forall(vs, body) | p::Formula::Exists(vs, body) => {
            out.extend(vs.iter());
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
        formula_reports(&thy, &elaborated.signature.maude_sig)
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

    /// Node-, message- and untagged binders are allowed
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
