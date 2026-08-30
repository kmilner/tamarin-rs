// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HS `factReports` (Wellformedness.hs:579-583): the wellformedness checks
//! over a theory's facts — reserved names, reserved `KU`/`KD`/`K` usage,
//! `Fr` arguments, the special `In`/`Out`/`Fr` tags, the arity /
//! multiplicity / capitalization clash groups, and the facts a rule
//! consumes on the left-hand side that no right-hand side produces.
//!
//! [`theory_facts`] is HS's `theoryFacts` (Wellformedness.hs:593-605): every
//! rule in item order with its facts in `ruleFacts` order, then every lemma
//! with the facts of its formula's `Action` atoms.  A rule fact's cell is
//! `prettyLNFact`, a lemma fact's the derived `show` of a
//! `Fact (VTerm Name (BVar LVar))`.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_term::lterm::{is_fresh_var, is_msg_var};

use super::{
    numbered_index_width, quote, show_rule_case_name, thy_proto_rules, underline_topic, WfError,
    WfReport, WF_LINE_LENGTH, WF_RIBBON,
};
use crate::fact::{
    fact_tag_arity, fact_tag_multiplicity, fact_tag_name, is_k_log_fact, is_proto_fact,
    pretty_lnfact, show_bl_fact, show_fact_tag_derived, Fact, FactTag, LNFact, Multiplicity,
};
use crate::formula::{formula_facts, BLNTerm};
use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{intr_rule_name_string, Rule};
use crate::theory::Theory;

// =============================================================================
// The factReports group
// =============================================================================

/// Port of HS `factReports` (Wellformedness.hs:579-583), in HS's member
/// order.
///
/// `theoryFacts` is one shared binding in HS's `where`, so the cells are
/// built once for the two members that read them.
pub fn fact_reports(thy: &Theory) -> WfReport {
    let facts = theory_facts(thy);
    let mut report = reserved_report(&facts);
    report.extend(reserved_fact_name_rules(thy));
    report.extend(fresh_fact_arguments(thy));
    report.extend(special_facts_usage(thy));
    report.extend(fact_usage(&facts));
    report.extend(fact_lhs_occur_no_rhs(thy));
    report
}

// =============================================================================
// theoryFacts
// =============================================================================

/// One cell of HS `theoryFacts`: the fact as the report renders it, paired
/// with `factInfo fa = (factTag fa, factArity fa, factMultiplicity fa)`
/// (Wellformedness.hs:174-175).
struct FactCell {
    pp: Doc,
    tag: FactTag,
    arity: usize,
    multiplicity: Multiplicity,
}

impl FactCell {
    /// HS `extFactInfo fa = (prettyLNFact fa, factInfo fa)`
    /// (Wellformedness.hs:609).
    fn of_rule_fact(fa: &LNFact) -> Self {
        FactCell {
            pp: pretty_lnfact(fa),
            tag: fa.tag,
            arity: fact_tag_arity(&fa.tag),
            multiplicity: fact_tag_multiplicity(&fa.tag),
        }
    }

    /// HS `theoryFacts`'s `LemmaItem` cell, `(text (show fa), factInfo fa)`
    /// (Wellformedness.hs:602-605).
    fn of_lemma_fact(fa: &Fact<BLNTerm>) -> Self {
        FactCell {
            pp: Doc::text(show_bl_fact(fa)),
            tag: fa.tag,
            arity: fact_tag_arity(&fa.tag),
            multiplicity: fact_tag_multiplicity(&fa.tag),
        }
    }
}

/// HS `show` of `Multiplicity` (Theory/Model/Fact.hs:133-134).
fn show_multiplicity(m: Multiplicity) -> &'static str {
    match m {
        Multiplicity::Persistent => "Persistent",
        Multiplicity::Linear => "Linear",
    }
}

/// HS `ruleFacts` (Wellformedness.hs:585-587): `concatMap (`get` ru) [rPrems,
/// rActs, rConcs]`.
fn rule_facts<I>(ru: &Rule<I>) -> impl Iterator<Item = &LNFact> {
    ru.premises
        .iter()
        .chain(ru.actions.iter())
        .chain(ru.conclusions.iter())
}

/// HS `theoryFacts` (Wellformedness.hs:593-605): each origin — a rule or a
/// lemma — with the facts it contributes.
///
/// A lemma's facts are the `Action` atoms of `_lFormula`, which at
/// wellformedness time is predicate-expanded but not yet macro-expanded
/// (`applyMacroInLemma` runs in `closeTheoryItem`, CloseRule.hs:85);
/// `Lemma::original_formula` is exactly that formula.
///
fn theory_facts(thy: &Theory) -> Vec<(String, Vec<FactCell>)> {
    let mut out: Vec<(String, Vec<FactCell>)> = Vec::new();
    for ru in &thy.intruder_rules {
        out.push((
            format!("Rule {}", quote(&intr_rule_name_string(&ru.info))),
            rule_facts(ru).map(FactCell::of_rule_fact).collect(),
        ));
    }
    for ru in thy_proto_rules(thy) {
        out.push((
            format!("Rule {}", quote(&show_rule_case_name(ru))),
            rule_facts(ru).map(FactCell::of_rule_fact).collect(),
        ));
    }
    for ru in thy.rules().flat_map(|opr| &opr.rule_ac) {
        out.push((
            format!("Rule {}", quote(&show_rule_case_name(ru))),
            rule_facts(ru).map(FactCell::of_rule_fact).collect(),
        ));
    }
    for l in thy.lemmas() {
        let formula = l.original_formula.as_ref().unwrap_or(&l.formula);
        out.push((
            format!("Lemma {}", quote(&l.name)),
            formula_facts(formula)
                .into_iter()
                .map(FactCell::of_lemma_fact)
                .collect(),
        ));
    }
    out
}

/// HS `wrappedText = fsep . map text . words`
/// (Wellformedness.hs:150-151).
fn wrapped_text(s: &str) -> Doc {
    hpj::fsep(s.split_whitespace().map(Doc::text).collect())
}

// =============================================================================
// Reserved fact names
// =============================================================================

/// HS `reservedFactName`'s list (Wellformedness.hs:622): a `ProtoFact`
/// whose lowercased name is one of these is reserved.
const RESERVED_FACT_NAMES: &[&str] = &["fr", "ku", "kd", "out", "in"];

/// HS `show` of `factInfo fa` — the derived `Show` of the `(FactTag, Int,
/// Multiplicity)` triple, each component at precedence 0 inside parentheses.
fn show_derived_fact_info(cell: &FactCell) -> String {
    format!(
        "({},{},{})",
        show_fact_tag_derived(&cell.tag),
        cell.arity,
        show_multiplicity(cell.multiplicity),
    )
}

/// HS `reservedFactName` (Wellformedness.hs:621-624): the body a reserved-named
/// `ProtoFact` contributes, `ppFa $-$ text ("show:" ++ show info)`.
fn reserved_fact_name(cell: &FactCell) -> Option<Doc> {
    let FactTag::Proto(_, name, _) = cell.tag else {
        return None;
    };
    if !RESERVED_FACT_NAMES.contains(&name.to_lowercase().as_str()) {
        return None;
    }
    Some(
        cell.pp
            .clone()
            .above_g(Doc::text(format!("show:{}", show_derived_fact_info(cell)))),
    )
}

/// HS `reservedReport` (Wellformedness.hs:611-619): one entry per origin whose
/// facts include a reserved-named `ProtoFact`.
fn reserved_report(facts: &[(String, Vec<FactCell>)]) -> WfReport {
    let mut out = Vec::new();
    for (origin, cells) in facts {
        let errs: Vec<Doc> = cells.iter().filter_map(reserved_fact_name).collect();
        if errs.is_empty() {
            continue;
        }
        // `foldr1 ($--$) (wrappedText header : map (nest 2) errs)`; `$--$`
        // is `above_blank` (Text/PrettyPrint/Class.hs:112-113).  The outer
        // `nest 2` is `prettyWfErrorReport`'s per-group indent
        // (Wellformedness.hs:118-125), which this topic's bodies carry
        // themselves.
        let mut parts: Vec<Doc> = Vec::with_capacity(errs.len() + 1);
        parts.push(wrapped_text(&format!(
            "The {origin} contains facts with reserved names:"
        )));
        parts.extend(errs.into_iter().map(|d| d.nest(2)));
        let mut body = parts
            .pop()
            .expect("reserved_report: non-empty by construction");
        for d in parts.into_iter().rev() {
            body = hpj::above_blank(d, body);
        }
        out.push(WfError::new(
            "Reserved names",
            body.nest(2).render_with(WF_LINE_LENGTH, WF_RIBBON),
        ));
    }
    out
}

// =============================================================================
// Reserved KU/KD/K-log usage
// =============================================================================

/// HS `reservedFactNameRules'` (Wellformedness.hs:529-550): one entry per rule
/// side that carries a `KUFact`/`KDFact` — plus, in the actions, an
/// `InFact`/`OutFact`/`FreshFact` — or a fact `isKLogFact` holds of.
///
/// `Ded(..)` parses to `DedFact` (`dedLogFact`, Theory/Model/Fact.hs:305-308),
/// which is in none of those sets.
fn reserved_fact_name_rules(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        let lfact: Vec<&LNFact> = ru
            .premises
            .iter()
            .filter(|fa| matches!(fa.tag, FactTag::Ku | FactTag::Kd) || is_k_log_fact(fa))
            .collect();
        let mfact: Vec<&LNFact> = ru
            .actions
            .iter()
            .filter(|fa| {
                matches!(
                    fa.tag,
                    FactTag::Ku | FactTag::Kd | FactTag::In | FactTag::Out | FactTag::Fresh
                ) || is_k_log_fact(fa)
            })
            .collect();
        let rfact: Vec<&LNFact> = ru
            .conclusions
            .iter()
            .filter(|fa| matches!(fa.tag, FactTag::Ku | FactTag::Kd) || is_k_log_fact(fa))
            .collect();
        for (msg, fas) in [
            (" on left-hand-side:", lfact),
            (" on the middle:", mfact),
            (" on the right-hand-side:", rfact),
        ] {
            if fas.is_empty() {
                continue;
            }
            // HS's body is
            //   text ("Rule " ++ quote (showRuleCaseName ru))
            //   <-> text ("contains facts with reserved names"++msg) $-$
            //   nest 2 (fsep $ punctuate comma $ map prettyLNFact fas)
            // — a headerless body, joined with its siblings by
            // `prettyWfErrorReport`'s blank separator under one topic header.
            let cells: Vec<Doc> = fas.iter().map(|fa| pretty_lnfact(fa)).collect();
            out.push(WfError::filled(
                "Reserved names",
                format!(
                    "Rule {} contains facts with reserved names{msg}",
                    quote(&show_rule_case_name(ru))
                ),
                cells,
            ));
        }
    }
    out
}

// =============================================================================
// Special facts misuse
// =============================================================================

/// HS `specialFactsUsage'` (Wellformedness.hs:552-566): an `OutFact` premise
/// or a `FreshFact`/`InFact` conclusion.
fn special_facts_usage(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        let lhsf: Vec<&LNFact> = ru
            .premises
            .iter()
            .filter(|fa| fa.tag == FactTag::Out)
            .collect();
        let rhsf: Vec<&LNFact> = ru
            .conclusions
            .iter()
            .filter(|fa| matches!(fa.tag, FactTag::Fresh | FactTag::In))
            .collect();
        for (msg, fas) in [
            ("uses disallowed facts on left-hand-side:", lhsf),
            ("uses disallowed facts on right-hand-side:", rhsf),
        ] {
            if fas.is_empty() {
                continue;
            }
            // `text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg $-$
            //  nest 2 (fsep $ punctuate comma $ map prettyLNFact fas)`, a
            // headerless body like the `reserved_fact_name_rules` sibling.
            // Note HS's lowercase `"rule "` here.
            let cells: Vec<Doc> = fas.iter().map(|fa| pretty_lnfact(fa)).collect();
            out.push(WfError::filled(
                "Special facts",
                format!("rule {} {msg}", quote(&show_rule_case_name(ru))),
                cells,
            ));
        }
    }
    out
}

// =============================================================================
// Fr facts must use a fresh- or msg-variable
// =============================================================================

/// HS `freshFactArguments'` (Wellformedness.hs:569-576): a single-term
/// `FreshFact` premise whose term is neither a msg- nor a fresh-variable.
///
/// The body carries neither the topic header nor `prettyWfErrorReport`'s
/// `nest 2`: `pretty_theory::render_wf_error_report` prefixes the indent to
/// the rendered lines, so the fact is laid out here at the bare report width.
fn fresh_fact_arguments(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        for fa in &ru.premises {
            if fa.tag != FactTag::Fresh || fa.terms.len() != 1 {
                continue;
            }
            let m = &fa.terms[0];
            if is_msg_var(m) || is_fresh_var(m) {
                continue;
            }
            // `text ("rule " ++ quote (showRuleCaseName ru)) <-> text "fact:"
            //  <-> prettyLNFact fa` (Wellformedness.hs:574-576).
            let body = Doc::text(format!("rule {} fact:", quote(&show_rule_case_name(ru))))
                .beside_sp(pretty_lnfact(fa))
                .render_with(WF_LINE_LENGTH, WF_RIBBON);
            out.push(WfError::new(
                "Fr facts must only use a fresh- or a msg-variable",
                body,
            ));
        }
    }
    out
}

// =============================================================================
// Fact arity / multiplicity / capitalization clashes
// =============================================================================

/// HS `capIssueMsg` (Wellformedness.hs:680-683).
const CAP_ISSUE_MSG: &str = "Fact names are case-sensitive, different capitalizations are \
     considered as different facts, i.e., Fact() is different from FAct(). \n\
     Check the capitalization of your fact names.";
/// HS `arityIssueMsg` (Wellformedness.hs:684-686).
const ARITY_ISSUE_MSG: &str = "Same fact is used with different arities, \
     i.e., Fact('A','B') is different from Fact('A'). \n\
     Check the arguments of your facts.";
/// HS `multipIssueMsg` (Wellformedness.hs:687-689).
const MULTIP_ISSUE_MSG: &str =
    "Same fact is used with different multiplicities, i.e., !Fact() (Persistent fact) exists \
     along with Fact() (Linear) in your rules. \n\
     Check the multiplicity (persistence) of your facts.";

/// One group of HS's `groupOn factIdentifier`: the origin and the cell of
/// every fact whose lowercased fact name is the group's.
type Clash<'a> = Vec<(&'a str, &'a FactCell)>;

/// HS `factUsage` (Wellformedness.hs:636-689): one entry per issue kind that
/// any clash group exhibits, in HS's `capIssues ++ arityIssues ++
/// multipIssues` order.
fn fact_usage(facts: &[(String, Vec<FactCell>)]) -> WfReport {
    // HS `groupOn factIdentifier $ sortOn factIdentifier theoryFacts'`
    // (Wellformedness.hs:639-643): the groups come out in lowercased-name
    // order, and `sortOn` is stable, so each keeps its `theoryFacts` order.
    let mut groups: BTreeMap<String, Clash> = BTreeMap::new();
    for (origin, cells) in facts {
        for cell in cells {
            groups
                .entry(fact_tag_name(&cell.tag).to_lowercase())
                .or_default()
                .push((origin.as_str(), cell));
        }
    }
    let all_clashes: Vec<&Clash<'_>> = groups.values().filter(|g| g.len() > 1).collect();

    let mut out = Vec::new();
    let cap = with_issue(&all_clashes, |c| fact_tag_name(&c.tag));
    if !cap.is_empty() {
        out.push(fact_clash_block(
            "Fact capitalization issues",
            CAP_ISSUE_MSG,
            &cap,
            &|c| format!("capitalization {:?}", fact_tag_name(&c.tag)),
        ));
    }
    let arity = with_issue(&all_clashes, |c| c.arity);
    if !arity.is_empty() {
        out.push(fact_clash_block(
            "Fact arity issues",
            ARITY_ISSUE_MSG,
            &arity,
            &|c| format!("arity {}", c.arity),
        ));
    }
    let multip = with_issue(&all_clashes, |c| c.multiplicity);
    if !multip.is_empty() {
        out.push(fact_clash_block(
            "Fact multiplicity issues",
            MULTIP_ISSUE_MSG,
            &multip,
            &|c| {
                format!(
                    "multiplicity (persistence) {}",
                    show_multiplicity(c.multiplicity)
                )
            },
        ));
    }
    out
}

/// HS `filter hasCapIssue` / `hasArityIssue` / `hasMultipIssue`
/// (Wellformedness.hs:676-678): the groups over which `project` takes more
/// than one distinct value.
fn with_issue<'a, T: Ord>(
    clashes: &[&'a Clash<'a>],
    project: impl Fn(&FactCell) -> T,
) -> Vec<&'a Clash<'a>> {
    clashes
        .iter()
        .copied()
        .filter(|g| {
            g.iter()
                .map(|(_, c)| project(c))
                .collect::<BTreeSet<T>>()
                .len()
                > 1
        })
        .collect()
}

/// HS's `capIssues` / `arityIssues` / `multipIssues` entry
/// (Wellformedness.hs:644-658): the underlined topic and the issue paragraph
/// make up HS's topic string, which `prettyWfErrorReport` prints verbatim
/// before laying out `text "\n" $-$ vcat (map format clashes)` under a
/// `nest 2`.
fn fact_clash_block(
    title: &str,
    intro: &str,
    clashes: &[&Clash<'_>],
    detail: &dyn Fn(&FactCell) -> String,
) -> WfError {
    let mut msg = underline_topic(title);
    msg.push('\n');
    msg.push_str(intro);
    // The newline `$-$` puts between the topic and the body, then the
    // `text "\n"` line the body opens with — two spaces from the `nest 2`,
    // then the newline the text itself carries.
    msg.push_str("\n  \n\n");
    let groups: Vec<Doc> = clashes.iter().map(|c| format_clash(c, detail)).collect();
    msg.push_str(
        &hpj::vcat(groups)
            .nest(2)
            .render_with(WF_LINE_LENGTH, WF_RIBBON),
    );
    msg.push('\n');
    WfError::new(title, msg)
}

/// HS `formatCapIssue` / `formatArityIssue` / `formatMultipIssue`
/// (Wellformedness.hs:660-674), which differ only in `detail`:
/// `text ("Fact `" ++ name ++ "':\n") $-$ nest 2 (numbered' items) $-$ text ""`.
fn format_clash(clash: &Clash<'_>, detail: &dyn Fn(&FactCell) -> String) -> Doc {
    // HS `name clash`: the lowercased `factTagName` of the group's first fact.
    let name = fact_tag_name(&clash[0].1.tag).to_lowercase();
    let items: Vec<Doc> = clash
        .iter()
        .map(|(origin, cell)| {
            Doc::text(format!("{origin}, {}", detail(cell))).above_g(cell.pp.clone().nest(2))
        })
        .collect();
    Doc::text(format!("Fact `{name}':\n"))
        .above_g(hpj::numbered_prime(items).nest(2))
        .above_g(Doc::text_hs(""))
}

// =============================================================================
// Facts occurring in a left-hand side but in no right-hand side
// =============================================================================

/// HS `showFactInfo` (Wellformedness.hs:248-251) over `factInfo fa =
/// (factTag fa, factArity fa, factMultiplicity fa)`
/// (Wellformedness.hs:174-175), which for a `ProtoFact` the tag alone
/// determines.  The leading space is HS's.
fn show_fact_info(f: &LNFact) -> String {
    format!(
        " factName {} arity: {} multiplicity: {}",
        quote(&fact_tag_name(&f.tag)),
        f.arity(),
        show_multiplicity(fact_tag_multiplicity(&f.tag)),
    )
}

/// HS `editDistance` (Utils/Misc.hs:164-174): the Levenshtein distance, over
/// two rows of the dynamic-programming table.
fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let (n, m) = (a.len(), b.len());
    let mut prev: Vec<usize> = (0..=m).collect();
    let mut cur = vec![0usize; m + 1];
    for i in 1..=n {
        cur[0] = i;
        for j in 1..=m {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[m]
}

/// Port of HS `factLhsOccurNoRhs'` (Wellformedness.hs:214-256): every proto
/// PREMISE fact whose `factInfo` no rule's conclusions produce, each paired
/// with the conclusion fact of smallest name edit distance
/// (`mostSimilarName`, Wellformedness.hs:180-210), kept only at distance
/// `<= 3`.
///
/// The single entry bakes in the underlined header and the `numbered'`
/// layout: `numbered (text "")` separates the items by a `text ""` line,
/// which at `prettyWfErrorReport`'s 2-space body nest renders as two spaces.
fn fact_lhs_occur_no_rhs(thy: &Theory) -> Vec<WfError> {
    // The topic's trailing space is HS's source literal
    // (Wellformedness.hs:221).
    let title = "Facts occur in the left-hand-side but not in any right-hand-side ";

    let names: Vec<String> = thy_proto_rules(thy).map(show_rule_case_name).collect();
    // HS `regroup (getFacts rConcs ru)`: every proto conclusion fact with its
    // rule's case name, in item order.  Each fact's `factTagName` is the
    // edit-distance operand below, so it is taken once here rather than once
    // per premise.
    let mut rhs: Vec<(&str, &LNFact, String)> = Vec::new();
    for (ru, name) in thy_proto_rules(thy).zip(&names) {
        for f in &ru.conclusions {
            if is_proto_fact(f) {
                rhs.push((name.as_str(), f, fact_tag_name(&f.tag)));
            }
        }
    }
    let rhs_info: BTreeSet<FactTag> = rhs.iter().map(|(_, f, _)| f.tag).collect();

    let mut orphans: Vec<(&str, &LNFact, Option<(&str, &LNFact)>)> = Vec::new();
    for (ru, name) in thy_proto_rules(thy).zip(&names) {
        for f in &ru.premises {
            if !is_proto_fact(f) {
                continue;
            }
            // HS `removeSame`: a premise whose `factInfo` occurs in some
            // right-hand side is not an orphan.
            if rhs_info.contains(&f.tag) {
                continue;
            }
            // HS `minimalEdFact` is `listToMaybe . sortOn snd`, a STABLE sort,
            // so a tie goes to the earliest right-hand side; `min_by_key`
            // keeps the first minimum too.  `isSimilar` drops it past 3.
            let fact_name = fact_tag_name(&f.tag);
            let suggestion = rhs
                .iter()
                .map(|(rn, rf, rname)| (edit_distance(&fact_name, rname), *rn, *rf))
                .min_by_key(|(d, _, _)| *d)
                .filter(|(d, _, _)| *d <= 3)
                .map(|(_, rn, rf)| (rn, rf));
            orphans.push((name.as_str(), f, suggestion));
        }
    }

    if orphans.is_empty() {
        return Vec::new();
    }

    let mut s = underline_topic(title);
    s.push('\n');
    let w = numbered_index_width(orphans.len());
    for (i, (rule_name, fa, suggestion)) in orphans.iter().enumerate() {
        // HS `showRuleAndFact` (Wellformedness.hs:239-247): `show ruName`
        // wraps the rule name in double quotes.
        let mut line = format!(
            "  {:>w$}. in rule \"{}\": {}",
            i + 1,
            rule_name,
            show_fact_info(fa),
            w = w,
        );
        if let Some((sug_rule, sug_fa)) = suggestion {
            line.push_str(&format!(
                ". Perhaps you want to use the fact in rule \"{}\": {}",
                sug_rule,
                show_fact_info(sug_fa),
            ));
        }
        s.push_str(&line);
        s.push('\n');
        if i + 1 < orphans.len() {
            s.push_str("  \n");
        }
    }

    vec![WfError::new(title, s)]
}

#[cfg(test)]
#[path = "facts_tests.rs"]
mod tests;
