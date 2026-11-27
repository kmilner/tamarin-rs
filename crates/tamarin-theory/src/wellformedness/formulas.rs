// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of HS `formulaReports` (Wellformedness.hs) — the
//! wellformedness pass over every lemma / restriction formula.
//!
//! For each annotated formula, upstream concatenates the quantifier-sort,
//! formula-term, guardedness and `last`-atom reports, in that order.
//!
//! Two consequences the report bytes depend on:
//!
//!   * `WfErrorReport = [WfError]`, so the list monad's `msum` is `concat`
//!     and `<$>` is `map`: all four checks run UNCONDITIONALLY for every
//!     formula and their findings are concatenated. A formula that trips
//!     several checks receives a report for each.
//!   * The four topics are emitted PER FORMULA, so they interleave in item
//!     order, and a topic REOPENS after an intervening one.  Since
//!     `prettyWfErrorReport` groups with `groupOn fst = groupBy ((==) `on`
//!     fst)` (Extension/Prelude.hs), which only merges CONSECUTIVE
//!     entries, each run gets its own underlined header — e.g. `Formula
//!     terms` / `Formula guardedness` / `Formula terms` for three lemmas
//!     where only the middle one is unguardable.  Splicing all findings of
//!     one topic together instead would collapse those runs into a single
//!     header and reorder the bodies.
//!
//! `annFormulas` is `lemmas <|> restrictions`, and `<|>` on lists is `++`,
//! so it is ALL lemmas (theory order) followed by ALL restrictions (theory
//! order) — not a single interleaved item walk.
//!
//! The formulas the four arms read are macro- and predicate-expanded:
//! `annFormulas` applies `applyMacroInFormula (theoryMacros thy)` itself, and
//! predicates are inlined at PARSE time
//! (`liftedAddLemma`→`expandLemma`→`expandFormula`, Theory/Text/Parser.hs;
//! `liftedAddRestriction`→`expandRestriction`).  The elaborated
//! [`Lemma::formula`](crate::theory::Lemma::formula) and
//! [`Restriction::formula`](crate::restriction::ProtoRestriction::formula) are
//! that formula: `elaborate` inlines the predicates and applies the theory's
//! macros as it builds each item, so all four checks see the inlined
//! predicate bodies — including their terms and their quantifiers.

use tamarin_term::lterm::LSort;

use crate::formula::LNFormula;
use crate::pretty_hpj::{fsep, punctuate, Doc};
use crate::theory::{Theory, TheoryItem};

use super::check_terms::{check_terms, WF_WIDTH};
use super::{underline_topic, WfError};

/// HS `underlineTopic "Quantifier sorts"` (Wellformedness.hs).
const QUANTIFIER_TOPIC: &str = "Quantifier sorts";

/// HS `annFormulas` (Wellformedness.hs): the annotated formulas
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

/// Port of HS `formulaReports` (Wellformedness.hs): one pass over
/// `annFormulas` running `checkQuantifiers`, `checkTerms`, `checkGuarded` and `checkNoLast`
/// per formula, so the four topics interleave exactly as HS emits them.
///
/// `thy` is the TRANSLATED theory — HS's single `checkWellformedness` runs on
/// the `OpenTranslatedTheory` (`checkTranslatedTheory`,
/// TheoryLoader.hs, fed by `closeTheory`), so
/// `annFormulas` also covers the restrictions SAPIC's `let … else` / `if`
/// lowering mints and the lemmas the accountability translation appends.
/// `checkTerms` classifies against the theory's own signature (HS `get
/// (sigpMaudeSig . thySignature) thy`, Wellformedness.hs).
pub fn formula_reports(thy: &Theory) -> Vec<WfError> {
    let sig = &thy.signature;
    let mut out: Vec<WfError> = Vec::new();
    for (header, fm) in ann_formulas(thy) {
        // HS `msum [checkQuantifiers, checkTerms, checkGuarded, checkNoLast]` = `concat`:
        // every arm runs for every formula, findings concatenated in this
        // order (Wellformedness.hs).
        out.extend(check_quantifiers(&header, fm));
        out.extend(check_terms(sig, &header, fm));
        out.extend(check_guarded_entry(&header, fm));
        let mut has_last = false;
        crate::formula::for_each_formula_atom(fm, &mut |atom| {
            has_last |= matches!(atom, crate::atom::ProtoAtom::Last(_));
        });
        if has_last {
            let topic = "Last atom usage";
            out.push(WfError::underlined_block(
                topic,
                Doc::text(format!("{header} contains last atom")),
            ));
        }
    }
    out
}

/// Port of HS `checkGuarded` (Wellformedness.hs): the finding for one
/// annotated formula that fails `formulaToGuarded`.  `header` is HS's
/// `"Lemma `n'"` / `"Restriction `n'"`.
///
/// Message layout, matching HS's `prettyWfErrorReport` + `checkGuarded`:
///
/// ```text
/// Formula guardedness
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
    use crate::pretty_hpj as hpj;

    let e = match crate::guarded::formula_to_guarded(formula) {
        Ok(_) => return None,
        Err(e) => e,
    };

    // The `underlineTopic` of "Formula guardedness" includes the trailing
    // newline; the blank line after it is `ppTopic`'s `$-$` in
    // `prettyWfErrorReport`.
    let topic = "Formula guardedness";
    let mut msg = String::new();
    msg.push_str(&underline_topic(topic));
    msg.push('\n');
    msg.push_str("  ");
    msg.push_str(header);
    msg.push_str(" cannot be converted to a guarded formula:\n");

    // `nest 2` (`prettyWfErrorReport`) + `nest 2 err` (`checkGuarded`) over
    // the thrown message Doc.
    // `full_doc` is HS `ppError`; the report contributes two enclosing
    // `nest 2`s, yielding four spaces for prose and six for quoted formulas.
    msg.push_str(
        &e.full_doc(formula)
            .nest(4)
            .render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON),
    );
    msg.push('\n');

    Some(WfError::new(topic, msg))
}

/// Port of HS `checkQuantifiers` (Wellformedness.hs): every binder
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
/// `[LSortMsg, LSortNode, LSortNat]` (Wellformedness.hs), else `None`.
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
    use crate::formula::{Connective, ProtoFormula, Quantifier};
    fn pattern_exclusion(fm: &LNFormula) -> bool {
        match fm {
            ProtoFormula::Qua(Quantifier::All, _, body) => pattern_exclusion(body),
            ProtoFormula::Conn(Connective::Imp, lhs, rhs) => {
                matches!(
                    lhs.as_ref(),
                    ProtoFormula::Atom(crate::atom::ProtoAtom::EqE(_, _))
                ) && matches!(rhs.as_ref(), ProtoFormula::Tf(false))
            }
            _ => false,
        }
    }
    if pattern_exclusion(fm) {
        return;
    }
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
