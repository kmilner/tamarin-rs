// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The three rule-walking wellformedness checks of the TRANSLATED theory:
//! HS `unboundReport` (Wellformedness.hs:514-519), `factLhsOccurNoRhs'`
//! (Wellformedness.hs:214-256) and `natWellSortedReport`
//! (Wellformedness.hs:319-333).
//!
//! All three read `thyProtoRules thy` (Wellformedness.hs:133-134) — the
//! macro-applied `oprRuleE` of every rule item of the `OpenTranslatedTheory`.
//! The elaborated [`Theory`]'s rules are that set: `elaborate` applies the
//! theory's macros and `apply_sapic` appends the generated rules, which is
//! the same input [`crate::mult_restricted`] reads.
//!
//! [`unbound_report`]'s body is HS's `text info $-$ nest 2 (prettyVarList
//! vars)` paragraph fill, so it hands its variable cells to
//! [`crate::wf_fill`] and lets the HughesPJ engine break them.
//! [`nat_well_sorted_report`] renders its own `<>` chain at the same width —
//! the style `addComment` bakes the wellformedness comment in with, HughesPJ's
//! library default `lineLength = 100`, `ribbonsPerLine = 1.5`
//! (TheoryObject.hs:717-718).  [`fact_lhs_occur_no_rhs`] builds a block of
//! `text` leaves, which the layout engine cannot break, and so renders it
//! directly.

use std::collections::BTreeSet;

use tamarin_parser::wf::{underline_topic, WfDoc, WfError};
use tamarin_term::function_symbols::{nat_one_sym, AcSym, FunSym};
use tamarin_term::lterm::{frees, frees_list, LNTerm, LSort, LVar};
use tamarin_term::pretty::pretty_nterm;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

use crate::fact::{
    fact_tag_multiplicity, fact_tag_name, is_proto_fact, FactTag, LNFact, Multiplicity,
};
use crate::formula::formula_frees_list;
use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{pretty_proto_rule_name, ProtoRuleE};
use crate::sapic::{Process, ProcessCombinator};
use crate::theory::Theory;

/// `lineLength` of the style HughesPJ's `render` uses, reached from HS
/// through `addComment`'s `render` (TheoryObject.hs:717-718).
const WF_LINE_LENGTH: usize = 100;
/// `ribbonLen = round (100 / 1.5) = 67` for [`WF_LINE_LENGTH`].
const WF_RIBBON: usize = 67;

/// HS `thyProtoRules` (Wellformedness.hs:133-134): the macro-applied E-rule
/// of every rule item, in item order.
fn thy_proto_rules(thy: &Theory) -> impl Iterator<Item = &ProtoRuleE> {
    thy.rules().map(|opr| &opr.rule)
}

/// HS `showRuleCaseName` (Theory/Model/Rule.hs:1337-1340): `render
/// . ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName`, whose
/// protocol-rule arm is all a [`ProtoRuleE`] reaches.
fn show_rule_case_name(ru: &ProtoRuleE) -> String {
    pretty_proto_rule_name(&ru.info.name).render()
}

/// HS `quote cs = '`' : cs ++ "'"` (Wellformedness.hs:164-165).
fn quote(s: &str) -> String {
    format!("`{}'", s)
}

// =============================================================================
// Unbound variables
// =============================================================================

/// HS `isNowNode v = lvarSort v == LSortNode && lvarName v == "NOW"`
/// (Wellformedness.hs:504-505): the `#NOW` node `varNow`
/// (Theory/Model/Restriction.hs:87-88) a rule's `_restrict` formula carries
/// free is bound by no premise.
fn is_now_node(v: &LVar) -> bool {
    v.sort == LSort::Node && v.name == "NOW"
}

/// The variable a `lookup t as v` combinator binds, for a rule whose
/// `process` attribute IS such a combinator — HS `originatesFromLookup`'s
/// `match v (Just (ProcessComb (Lookup _ v') _ _ _)) = v == slvar v'`
/// (Wellformedness.hs:501-503).  The variable reaches the generated rule
/// through that rule's `IsIn( t, v )` action rather than through a premise.
/// Every user-written rule yields `None`: HS's rule-attribute parser discards
/// a written `process=` (`parseAndIgnore`, Theory/Text/Parser/Rule.hs:70-96,
/// see line 74), so the attribute is carried only by SAPIC-generated rules.
fn lookup_binder(ru: &ProtoRuleE) -> Option<LVar> {
    match ru.info.attributes.process.as_ref()? {
        Process::Comb(ProcessCombinator::Lookup(_, v), _, _, _) => Some(v.to_lvar()),
        _ => None,
    }
}

/// HS `unboundCheck`'s `unboundVars` (Wellformedness.hs:505-511): the free
/// variables of the conclusions, the actions and the rule info, minus the
/// premise-bound ones, the `#NOW` node, the pub-sorted ones (which the
/// adversary knows) and the `lookup` binder.
fn unbound_vars(ru: &ProtoRuleE) -> Vec<LVar> {
    // HS `boundVars = S.fromList $ frees (get rPrems ru)` keys on the whole
    // `LVar`, so `~ltk` (fresh) does not bind `ltk` (msg).
    let bound: BTreeSet<LVar> = frees(&ru.premises).into_iter().collect();
    let binder = lookup_binder(ru);
    // HS `frees (get rConcs ru, get rActs ru, get rInfo ru)`, and `frees =
    // sortednub . freesList` (LTerm.hs:613-614), so the three components make
    // one sorted, deduplicated list.  `rInfo`'s own `HasFrees` reaches the
    // `_preRestriction` formulas alone — the rule name and the attributes fold
    // to `mempty` (Theory/Model/Rule.hs:462-473, 491-498).
    let mut vars = frees_list(&ru.conclusions);
    vars.extend(frees_list(&ru.actions));
    for phi in &ru.info.restrictions {
        vars.extend(formula_frees_list(phi));
    }
    vars.sort();
    vars.dedup();
    vars.retain(|v| {
        !(is_now_node(v) || v.sort == LSort::Pub || bound.contains(v) || binder == Some(*v))
    });
    vars
}

/// Port of HS `unboundReport` (Wellformedness.hs:514-519): one entry per
/// offending rule, all under the topic "Unbound variables".  The summary's
/// WARNING count is `length rep` (Batch.hs:246), so the entries stay
/// un-grouped.
///
/// Each entry carries only its body — HS `text info $-$ nest 2 (prettyVarList
/// unboundVars)` (Wellformedness.hs:497-498) — because `prettyWfErrorReport`
/// emits the underlined header once per topic group and nests the bodies by 2
/// (Wellformedness.hs:118-125).  `prettyVarList = fsep . punctuate comma . map
/// prettyLVar` (TheoryObject.hs:858-859) is the paragraph fill
/// [`crate::wf_fill`] lays out, and `prettyLVar = text . show`
/// (LTerm.hs:922-923) makes each cell a leaf.
pub fn unbound_report(thy: &Theory) -> Vec<WfError> {
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        let unbound = unbound_vars(ru);
        if unbound.is_empty() {
            continue;
        }
        let cells: Vec<WfDoc> = unbound.iter().map(|v| WfDoc::Text(v.to_string())).collect();
        out.push(WfError::filled(
            "Unbound variables",
            format!(
                "rule {} has unbound variables: ",
                quote(&show_rule_case_name(ru))
            ),
            cells,
        ));
    }
    out
}

// =============================================================================
// Facts occurring in a left-hand side but in no right-hand side
// =============================================================================

/// HS `show` of `Multiplicity` (Theory/Model/Fact.hs:133-134).
fn show_multiplicity(m: Multiplicity) -> &'static str {
    match m {
        Multiplicity::Persistent => "Persistent",
        Multiplicity::Linear => "Linear",
    }
}

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

/// HS `numbered'`'s index width — `nWidth = length (show n)` for `n` items,
/// each index rendered `flushRight nWidth (show i)`, i.e. left-padded with
/// spaces (Text/PrettyPrint/Class.hs:251-264).
fn numbered_index_width(count: usize) -> usize {
    count.to_string().len()
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
pub fn fact_lhs_occur_no_rhs(thy: &Theory) -> Vec<WfError> {
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

// =============================================================================
// Nat sorts
// =============================================================================

/// HS `viewTerm2`'s `NatOne` (Term/Term/Raw.hs:191-198, see line 198): the
/// nullary application of `natOneSym`, which the source spells `%1`.
fn is_nat_one(t: &LNTerm) -> bool {
    matches!(t, Term::App(FunSym::NoEq(s), ts) if ts.is_empty() && *s == nat_one_sym())
}

/// HS `isNatVar` (LTerm.hs:334-336): a term that is a nat-sorted VARIABLE.
/// A nat literal such as `%'a'` is a `Con` name and so is not one.
fn is_nat_var(t: &LNTerm) -> bool {
    matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Nat)
}

/// The operands of a `%+` application — HS `viewTerm2`'s `FNatPlus list`
/// (Term/Term/Raw.hs:180-188, see line 186), i.e. the AC-flattened, sorted
/// argument list `fAppAC` builds at construction.
fn nat_plus_operands(t: &LNTerm) -> Option<&[LNTerm]> {
    match t {
        Term::App(FunSym::Ac(AcSym::NatPlus), ts) => Some(ts),
        _ => None,
    }
}

/// HS `notOnlyNat` (Wellformedness.hs:296-300): the recursion under `%+`.
/// Everything that is neither `%1`, nor a nat variable, nor a nested `%+` is
/// an offending operand.
fn not_only_nat<'a>(t: &'a LNTerm, out: &mut Vec<&'a LNTerm>) {
    if let Some(ts) = nat_plus_operands(t) {
        for a in ts {
            not_only_nat(a, out);
        }
    } else if !(is_nat_one(t) || is_nat_var(t)) {
        out.push(t);
    }
}

/// HS `nonWellSorted` (Wellformedness.hs:293-303): descend through the term
/// and collect, for every `%+` application, the operands that are not
/// nat-sorted.
fn non_well_sorted<'a>(t: &'a LNTerm, out: &mut Vec<&'a LNTerm>) {
    if let Some(ts) = nat_plus_operands(t) {
        for a in ts {
            not_only_nat(a, out);
        }
        return;
    }
    if is_nat_one(t) {
        return;
    }
    if let Term::App(_, ts) = t {
        for a in ts.iter() {
            non_well_sorted(a, out);
        }
    }
}

/// HS `getRuleTerms` (Wellformedness.hs:332-333): `concatMap factTerms` over
/// the premises, the actions and the conclusions, in that order.
fn rule_terms(ru: &ProtoRuleE) -> impl Iterator<Item = &LNTerm> {
    ru.premises
        .iter()
        .chain(&ru.actions)
        .chain(&ru.conclusions)
        .flat_map(|f| f.terms.iter())
}

/// Port of HS `natWellSortedReport` (Wellformedness.hs:319-333) over its rule
/// terms, through `natSortErrors` (Wellformedness.hs:315-316): one entry per
/// `(term, offending operand)` pair, body `prettyLNTerm err <> text " in term
/// " <> prettyLNTerm t <> text " must be of sort nat"`, with the rule name
/// absent and `t` the whole fact argument.
///
/// `getItemTerms`' other half — the bound terms of the lemma, restriction and
/// predicate formulas (Wellformedness.hs:325-331) — is outside this walk.
pub fn nat_well_sorted_report(thy: &Theory) -> Vec<WfError> {
    // HS builds the report as a plain `Doc`: `prettyWfErrorReport`'s text
    // never passes through the escaping `Document (HtmlDoc d)` instance
    // (Html.hs:102-105), so a pair term inside a body keeps its raw `<`/`>`
    // on the web routes, which render under an active `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        for t in rule_terms(ru) {
            let mut errs: Vec<&LNTerm> = Vec::new();
            non_well_sorted(t, &mut errs);
            for err in errs {
                // `nest 2` is `prettyWfErrorReport`'s per-body indent, baked
                // in so the engine's width decisions are made at the body's
                // true column.
                let body = hpj::hcat(vec![
                    pretty_nterm(err),
                    Doc::text(" in term "),
                    pretty_nterm(t),
                    Doc::text(" must be of sort nat"),
                ]);
                out.push(WfError::new(
                    "Nat Sorts",
                    body.nest(2).render_with(WF_LINE_LENGTH, WF_RIBBON),
                ));
            }
        }
    }
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sapic::{ProcessParsedAnnotation, SapicLVar};
    use crate::theory::TheoryItem;
    use tamarin_term::vterm::var_term;

    /// The elaborated theory for `src`, as a loader holds it before
    /// translation.
    fn elaborated(src: &str) -> Theory {
        let parsed = tamarin_parser::parse_theory(src, &[]).expect("parse");
        crate::elaborate::elaborate(&parsed).expect("elaborate")
    }

    /// The report's bodies joined the way `prettyWfErrorReport` joins a topic
    /// group — `intersperse (text "")` under one header, which at the group's
    /// 2-space nest is a two-space line (Wellformedness.hs:118-125).
    fn bodies(report: &[WfError]) -> String {
        assert!(!report.is_empty(), "empty report");
        report
            .iter()
            .map(|e| match &e.fill {
                Some(fill) => crate::wf_fill::fill_body(fill),
                None => e.message.clone(),
            })
            .collect::<Vec<_>>()
            .join("\n  \n")
    }

    /// A `lookup t as v` combinator over one variable, as the `process`
    /// attribute of a SAPIC-generated rule carries it.
    fn lookup_process(v: LVar) -> crate::sapic::PlainProcess {
        let sv = SapicLVar::untyped(v);
        Process::Comb(
            ProcessCombinator::Lookup(var_term(sv.clone()), sv),
            ProcessParsedAnnotation::default(),
            Box::new(Process::Null(ProcessParsedAnnotation::default())),
            Box::new(Process::Null(ProcessParsedAnnotation::default())),
        )
    }

    /// HS `frees` sorts by `Ord LVar` = `(idx, sort, name)`
    /// (LTerm.hs:546-548), so the list is not in source order: `~nr` (fresh)
    /// precedes the msg-sorted `mi` and `ni`, and `$A` is dropped as
    /// pub-sorted.  Byte-pinned to the pinned oracle (ef3f0468) on
    /// `Out(<ni, ~nr, $A, mi>)`.
    #[test]
    fn unbound_variables_are_listed_in_lvar_order() {
        let thy = elaborated("theory T begin rule R: [ ] --[ ]-> [ Out(<ni, ~nr, $A, mi>) ] end");
        assert_eq!(
            bodies(&unbound_report(&thy)),
            "  rule `R' has unbound variables: \n    ~nr, mi, ni"
        );
    }

    /// A builtin's 0-arity constant is a symbol only while that builtin is
    /// enabled (`nullaryApp`, Theory/Text/Parser/Term.hs:158-163), so the same
    /// bare name is a variable — and an unbound one — in a theory that does
    /// not enable it.
    #[test]
    fn bare_name_of_a_disabled_builtin_constant_is_a_variable() {
        let thy = elaborated("theory T begin rule R: [ ] --[ ]-> [ Out(<zero, true>) ] end");
        assert_eq!(
            bodies(&unbound_report(&thy)),
            "  rule `R' has unbound variables: \n    true, zero"
        );
        let thy = elaborated(
            "theory T begin builtins: xor, signing rule R: [ ] --[ ]-> [ Out(<zero, true>) ] end",
        );
        assert!(
            unbound_report(&thy).is_empty(),
            "with the builtins enabled both names are constants: {:?}",
            unbound_report(&thy)
        );
    }

    /// HS `originatesFromLookup` (Wellformedness.hs:501-503, 506-510): the
    /// variable a `lookup t as v` combinator binds reaches its generated rule
    /// through the `IsIn( t, v )` action, so it is not unbound — while an
    /// otherwise identical rule without the `process` attribute is.  The
    /// parser never mints that attribute, so the generated shape is built by
    /// attaching the process the SAPIC translation writes.
    #[test]
    fn lookup_binder_is_not_unbound() {
        let src = "theory T begin \
                   rule L: [ State_1(m.1) ] --[ IsIn(m.1, v.1) ]-> [ State_11(m.1, v.1) ] \
                   end";
        let mut thy = elaborated(src);
        assert_eq!(
            unbound_report(&thy).len(),
            1,
            "without the lookup attribute v.1 is unbound"
        );
        let binder = LVar::new("v", LSort::Msg, 1);
        for item in thy.items.iter_mut() {
            if let TheoryItem::Rule(r) = item {
                r.rule.info.attributes.process = Some(lookup_process(binder));
            }
        }
        assert!(
            unbound_report(&thy).is_empty(),
            "the lookup binder must be suppressed: {:?}",
            unbound_report(&thy)
        );

        // A DIFFERENT free variable in the same lookup rule is still
        // reported: HS compares the offender against the binder, it does not
        // exempt the whole rule.
        let mut thy = elaborated(
            "theory T begin \
             rule L: [ State_1(m.1) ] --[ IsIn(m.1, v.1) ]-> [ State_11(m.1, v.1, w.2) ] \
             end",
        );
        for item in thy.items.iter_mut() {
            if let TheoryItem::Rule(r) = item {
                r.rule.info.attributes.process = Some(lookup_process(binder));
            }
        }
        let report = unbound_report(&thy);
        assert_eq!(report.len(), 1);
        let Some(tamarin_parser::wf::WfFill::Paragraph { cells, .. }) = report[0].fill.as_ref()
        else {
            panic!("unbound entry carries its cells: {report:?}");
        };
        assert_eq!(
            *cells,
            vec![WfDoc::Text("w.2".to_string())],
            "only the non-binder variable is reported: {report:?}"
        );
    }

    /// This is `underlineTopic` of HS's source-literal topic plus the `$-$`
    /// blank line that opens the body.  The title is 65 characters long, its
    /// trailing space included, so the rule below it is 65 `=` characters.
    const LHS_NO_RHS_HEADER: &str =
        "Facts occur in the left-hand-side but not in any right-hand-side \n\
         =================================================================\n\n";

    /// The suggestion arm picks the right-hand-side fact with the smallest
    /// name distance, not the first one.  `Sesion` is 1 edit from `Session`
    /// and 2 from `Section`, which the source lists earlier.  Byte-pinned to
    /// the pinned oracle (ef3f0468).
    #[test]
    fn fact_lhs_no_rhs_suggests_the_smallest_edit_distance_not_the_first() {
        let thy = elaborated(
            r#"theory T begin
            rule A: [ Sesion(x) ] --[ ]-> [ ]
            rule B: [ ] --[ ]-> [ Section(x) ]
            rule C: [ ] --[ ]-> [ Session(x) ]
        end"#,
        );
        assert_eq!(
            bodies(&fact_lhs_occur_no_rhs(&thy)),
            format!(
                "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Sesion' arity: 1 \
                 multiplicity: Linear. Perhaps you want to use the fact in rule \"C\":  \
                 factName `Session' arity: 1 multiplicity: Linear\n"
            )
        );
    }

    /// HS `isSimilar` keeps the nearest right-hand-side name only at distance
    /// `<= 3` (Wellformedness.hs:192-196).  `Abc` is 4 edits from `Abcdefg`,
    /// the only such name, so the line carries no suggestion.  Byte-pinned to
    /// the pinned oracle (ef3f0468).
    #[test]
    fn fact_lhs_no_rhs_drops_the_suggestion_past_distance_three() {
        let thy = elaborated(
            r#"theory T begin
            rule A: [ Abc(x) ] --[ ]-> [ ]
            rule B: [ ] --[ ]-> [ Abcdefg(x) ]
        end"#,
        );
        assert_eq!(
            bodies(&fact_lhs_occur_no_rhs(&thy)),
            format!(
                "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Abc' arity: 1 \
                 multiplicity: Linear\n"
            )
        );
    }

    /// Both right-hand-side names are 1 edit from `Aaa`, and the tie goes to
    /// the first of them: HS `minimalEdFact` takes `listToMaybe . sortOn snd`
    /// (Wellformedness.hs:200-201), a stable sort.  Byte-pinned to the pinned
    /// oracle (ef3f0468).
    #[test]
    fn fact_lhs_no_rhs_breaks_distance_ties_by_rhs_source_order() {
        let thy = elaborated(
            r#"theory T begin
            rule A: [ Aaa(x) ] --[ ]-> [ ]
            rule B: [ ] --[ ]-> [ Aax(x) ]
            rule C: [ ] --[ ]-> [ Aay(x) ]
        end"#,
        );
        assert_eq!(
            bodies(&fact_lhs_occur_no_rhs(&thy)),
            format!(
                "{LHS_NO_RHS_HEADER}  1. in rule \"A\":  factName `Aaa' arity: 1 \
                 multiplicity: Linear. Perhaps you want to use the fact in rule \"B\":  \
                 factName `Aax' arity: 1 multiplicity: Linear\n"
            )
        );
    }

    /// The only operand the check rejects is the fresh variable `~x`; the
    /// nat-sorted `%a` passes `isNatVar`.  The message carries no rule name
    /// and `t` is the complete fact-argument term, whose `%+` operands print
    /// in `Ord LVar` order rather than source order — `fAppAC` sorts them at
    /// construction.  Byte-pinned to the pinned oracle (ef3f0468) on
    /// `Out(%a %+ ~x)`.
    #[test]
    fn nat_sorts_message_format() {
        let thy = elaborated(
            "theory T begin builtins: natural-numbers \
             rule R: [ Fr(~x) ] --[ ]-> [ Out(%a %+ ~x) ] end",
        );
        assert_eq!(
            bodies(&nat_well_sorted_report(&thy)),
            "  ~x in term (~x%+%a) must be of sort nat"
        );
    }

    /// The check flags a nat *literal* `%'a'`, which is a `Con` name and not
    /// a variable, and leaves the nat variable `%y` beside it — HS `isNatVar`
    /// is true only for a `Lit (Var ..)` of sort nat.  Byte-pinned to the
    /// pinned oracle (ef3f0468).
    #[test]
    fn nat_sorts_flags_nat_literal() {
        let thy = elaborated(
            "theory T begin builtins: natural-numbers \
             rule R: [ Fr(~x) ] --[ ]-> [ Out(%'a' %+ %y) ] end",
        );
        assert_eq!(
            bodies(&nat_well_sorted_report(&thy)),
            "  %'a' in term (%'a'%+%y) must be of sort nat"
        );
    }

    /// Both the offender and the enclosing term print through `prettyLNTerm`
    /// over the canonical term, and `nonWellSorted` walks the canonical
    /// operand list, so an AC chain appears flattened and sorted and several
    /// offenders of one term arrive in that same order.  Byte-pinned to the
    /// pinned oracle (ef3f0468).
    #[test]
    fn nat_sorts_render_ac_terms_canonically() {
        let report = |src: &str| -> String {
            let thy = elaborated(&format!(
                "theory T begin \
                 builtins: multiset, xor, bilinear-pairing, natural-numbers \
                 functions: add/2 [AC], zz/1 \
                 rule R: [ In(<a,b,c>) ] --> [ Out( {src} ) ] end"
            ));
            bodies(&nat_well_sorted_report(&thy))
        };
        assert_eq!(
            report("(a*b)*c %+ %1"),
            "  (a*b*c) in term (%1%+(a*b*c)) must be of sort nat"
        );
        assert_eq!(
            report("add(add(b,a),c) %+ %1"),
            "  (a add b add c) in term (%1%+(a add b add c)) must be of sort nat"
        );
        assert_eq!(
            report("em(b,a) %+ %1"),
            "  em(a, b) in term (%1%+em(a, b)) must be of sort nat"
        );
        assert_eq!(
            report("zz(b*a) %+ %1"),
            "  zz((a*b)) in term (%1%+zz((a*b))) must be of sort nat"
        );
        // `fAppAC _ [a] = a`: the offender is `a`, not `add(a)`.
        assert_eq!(
            report("add(a) %+ %1"),
            "  a in term (a%+%1) must be of sort nat"
        );
        // `exp` is `NoEq`, so it renders unparenthesised.
        assert_eq!(
            report("(a^b) %+ %1"),
            "  a^b in term (a^b%+%1) must be of sort nat"
        );
        // Two offenders under one `%+`, in canonical operand order (the LIT
        // `c` before the `Mult`-headed FAPP) rather than source order.
        assert_eq!(
            report("(a*b) %+ c %+ %1"),
            "  c in term (c%+%1%+(a*b)) must be of sort nat\n  \n  \
             (a*b) in term (c%+%1%+(a*b)) must be of sort nat"
        );
    }

    /// One entry per `(term, offending operand)` pair, so a `%+` with two
    /// rejected operands opens two bodies under the one topic header.
    /// Byte-pinned to the pinned oracle (ef3f0468) on `In( x %+ pair(a,b) )`.
    #[test]
    fn nat_sorts_reports_every_offending_operand_of_a_term() {
        let thy = elaborated(
            "theory T begin builtins: natural-numbers \
             rule Test: [ In( x %+ pair(a,b) ) ] --[ ]-> [] end",
        );
        assert_eq!(
            bodies(&nat_well_sorted_report(&thy)),
            "  x in term (x%+<a, b>) must be of sort nat\n  \n  \
             <a, b> in term (x%+<a, b>) must be of sort nat"
        );
    }

    /// A free variable literally named `True` is unbound: there is no builtin
    /// `True` nullary (only `true`), so the parser leaves it a variable.
    #[test]
    fn variable_named_true_is_unbound() {
        let thy = elaborated("theory T begin rule R: [ ] --[ ]-> [ Out(True) ] end");
        assert_eq!(
            bodies(&unbound_report(&thy)),
            "  rule `R' has unbound variables: \n    True"
        );
    }

    /// `prettyVarList` is HS's `fsep` paragraph fill, so the variable cells
    /// break before the one that would pass the ribbon — 4-column cells:
    /// thirteen fit at 64, fourteen would need 69.  Byte-pinned to the pinned
    /// oracle (ef3f0468).
    #[test]
    fn unbound_variable_list_fills_at_the_report_ribbon() {
        let names: Vec<String> = (1..=20).map(|i| format!("K( a{i:02} )")).collect();
        let thy = elaborated(&format!(
            "theory T begin rule R: [] --[ {} ]-> [] end",
            names.join(", ")
        ));
        assert_eq!(
            bodies(&unbound_report(&thy)),
            "  rule `R' has unbound variables: \n    \
             a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13,\n    \
             a14, a15, a16, a17, a18, a19, a20"
        );
    }

    /// The parser inlines a rule's `let` bindings into the body it builds
    /// (`apply subst (ps0,as0,cs0,rs0)`, Theory/Text/Parser/Rule.hs:119), so
    /// the check reads the substituted facts: `c %+ %1` is nat well sorted
    /// once `c` is the nat variable `%i`.
    #[test]
    fn let_inlining_reaches_the_nat_check() {
        let thy = elaborated(
            "theory T begin builtins: natural-numbers \
             rule Count: let c = %i in [In(<'c', %i>)] --[Count(c %+ %1)]-> [] end",
        );
        assert!(
            nat_well_sorted_report(&thy).is_empty(),
            "the inlined `%i` is nat sorted"
        );
    }
}
