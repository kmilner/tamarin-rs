// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The wellformedness checks that walk a theory's rules.
//!
//! HS `unboundReport` (Wellformedness.hs:514-519), `factLhsOccurNoRhs'`
//! (Wellformedness.hs:214-256) and `natWellSortedReport`
//! (Wellformedness.hs:319-333) read `thyProtoRules thy`
//! (Wellformedness.hs:133-134) — the macro-applied `oprRuleE` of every rule
//! item of the `OpenTranslatedTheory`.  The elaborated [`Theory`]'s rules are
//! that set: `elaborate` applies the theory's macros and `apply_sapic`
//! appends the generated rules, which is the same input [`super::mult`]
//! reads.  [`translated_public_names_report`] (HS `publicNamesReport'`,
//! Wellformedness.hs:463-484) reads them too, including the source
//! subprocess a generated rule carries.
//!
//! [`fresh_names_report`] (HS `freshNamesReport'`, Wellformedness.hs:444-452)
//! and [`variable_sort_clashes`] (HS `ruleSortsReport`,
//! Wellformedness.hs:258-280) read the parser AST, so they carry their own
//! walk over a rule's terms.
//!
//! [`unbound_report`]'s body is HS's `text info $-$ nest 2 (prettyVarList
//! vars)` paragraph fill, so it hands its variable cells to
//! [`WfError::filled`] and lets the HughesPJ engine break them.
//! [`nat_well_sorted_report`] renders its own `<>` chain at the same width —
//! the style `addComment` bakes the wellformedness comment in with, HughesPJ's
//! library default `lineLength = 100`, `ribbonsPerLine = 1.5`
//! (TheoryObject.hs:717-718).  [`fact_lhs_occur_no_rhs`] builds a block of
//! `text` leaves, which the layout engine cannot break, and so renders it
//! directly.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
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

use super::{
    grouped_topic_block, numbered_index_width, render_var, rule_facts, theory_rules,
    underline_topic, WfError, WfReport,
};

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
/// [`WfError::filled`] lays out, and `prettyLVar = text . show`
/// (LTerm.hs:922-923) makes each cell a leaf.
pub fn unbound_report(thy: &Theory) -> Vec<WfError> {
    // Plain mode for the same reason as [`nat_well_sorted_report`]: the body
    // is a `Doc` built and laid out here, and the web routes render under an
    // active `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        let unbound = unbound_vars(ru);
        if unbound.is_empty() {
            continue;
        }
        let cells: Vec<Doc> = unbound.iter().map(|v| Doc::text(v.to_string())).collect();
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
// Helpers — parser-AST variables and name literals
// =============================================================================

/// Recursively collect every variable appearing in a term.
fn term_vars(t: &p::Term, out: &mut Vec<p::VarSpec>) {
    match t {
        p::Term::Var(v) => out.push(v.clone()),
        p::Term::App(_, args) => {
            for a in args {
                term_vars(a, out);
            }
        }
        p::Term::AlgApp(_, a, b) => {
            term_vars(a, out);
            term_vars(b, out);
        }
        p::Term::Pair(items) => {
            for a in items {
                term_vars(a, out);
            }
        }
        p::Term::Diff(a, b) => {
            term_vars(a, out);
            term_vars(b, out);
        }
        p::Term::BinOp(_, a, b) => {
            term_vars(a, out);
            term_vars(b, out);
        }
        p::Term::PatMatch(inner) => term_vars(inner, out),
        p::Term::PubLit(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => {}
    }
}

fn fact_vars(f: &p::Fact) -> Vec<p::VarSpec> {
    let mut v = Vec::new();
    for a in &f.args {
        term_vars(a, &mut v);
    }
    v
}

/// Collect every public-name literal (`'foo'`) and fresh-name literal
/// (`~'foo'`) within a term subtree.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NameKind {
    Pub,
    Fresh,
}

fn term_name_lits(t: &p::Term, out: &mut Vec<(NameKind, String)>) {
    match t {
        p::Term::PubLit(s) => out.push((NameKind::Pub, s.clone())),
        p::Term::FreshLit(s) => out.push((NameKind::Fresh, s.clone())),
        p::Term::App(_, args) => {
            for a in args {
                term_name_lits(a, out);
            }
        }
        p::Term::AlgApp(_, a, b) => {
            term_name_lits(a, out);
            term_name_lits(b, out);
        }
        p::Term::Pair(items) => {
            for a in items {
                term_name_lits(a, out);
            }
        }
        p::Term::Diff(a, b) => {
            term_name_lits(a, out);
            term_name_lits(b, out);
        }
        p::Term::BinOp(_, a, b) => {
            term_name_lits(a, out);
            term_name_lits(b, out);
        }
        p::Term::PatMatch(inner) => term_name_lits(inner, out),
        _ => {}
    }
}

/// Every name literal of a rule, in [`rule_facts`] order.  Both name reports
/// walk `universeBi ru` (`freshNamesReport'` Wellformedness.hs:447,
/// `publicNamesReport'` Wellformedness.hs:475-478) over `thyProtoRules`
/// (:456, :486), so a name occurring only inside a `let` value
/// (`let m = ~'foo' in … Out(m)`) is inlined into the rule body by the parser
/// and surfaces here.
fn rule_name_lits(r: &p::Rule) -> Vec<(NameKind, String)> {
    let mut names = Vec::new();
    for f in rule_facts(r) {
        for t in &f.args {
            term_name_lits(t, &mut names);
        }
    }
    names
}

// =============================================================================
// Fresh public constants — `~'foo'` is forbidden
// =============================================================================

pub fn fresh_names_report(_elab: &Theory, parsed: &p::Theory) -> WfReport {
    // HS `freshNamesReport'` (Wellformedness.hs:444-452): one WfError per
    // offending rule, body = `fsep` of
    //   text ("rule " ++ quote (showRuleCaseName ru) ++ ": fresh public \
    //         constants are not allowed:") : punctuate comma (map (show) names)
    // where `quote cs = '`' : cs ++ "'"` (Wellformedness.hs:164-165, see line 165) and the fresh
    // names render via `show (Name FreshName n) = "~'" ++ n ++ "'"`
    // (LTerm.hs:235-240, see line 236).  Topic is "Fresh public constants"; the umbrella renderer
    // emits the underlineTopic header once and 2-space-nests the bodies
    // (separated by a `  ` blank line) — we bake that whole block into a single
    // WfError so the default `format_wf_block` path reproduces the exact bytes.
    let topic = "Fresh public constants";
    let mut bodies: Vec<String> = Vec::new();
    for r in theory_rules(parsed) {
        // HS `show (Name FreshName n) = "~'" ++ n ++ "'"` for each fresh name,
        // joined by `punctuate comma` (`, `) under the `fsep`.
        let fresh_lits: Vec<String> = rule_name_lits(r)
            .iter()
            .filter_map(|(k, n)| {
                if *k == NameKind::Fresh {
                    Some(format!("~'{}'", n))
                } else {
                    None
                }
            })
            .collect();
        if !fresh_lits.is_empty() {
            // Body only, 2-space `nest 2` indent baked in; HS `quote` form for
            // the rule name (backtick + apostrophe).
            bodies.push(format!(
                "  rule `{}': fresh public constants are not allowed: {}",
                r.name,
                fresh_lits.join(", ")
            ));
        }
    }
    grouped_topic_block(topic, bodies)
}

// =============================================================================
// Public constant capitalization clashes
// =============================================================================

/// The clash-detection + rendering half of HS `publicNamesReport'`
/// (Wellformedness.hs:463-484).  Its caller,
/// [`translated_public_names_report`], harvests the
/// `(showRuleCaseName, pubName)` pairs from the ELABORATED rules — including
/// the `process` attribute HS's `universeBi` walks — which the parser AST
/// stores only as a rendered string.  `pairs` must arrive in rule order
/// (matching HS `thyProtoRules`), first-occurrence-wins: `clashesOn` keeps the
/// earliest `(rule, name)` per distinct public name.
fn public_names_report_from_pairs(pairs: Vec<(String, String)>) -> WfReport {
    if pairs.is_empty() {
        return Vec::new();
    }
    // HS `show` of a (public) Name constant is the quoted form `'name'`.
    let shw = |n: &str| format!("'{}'", n);
    let f = |p: &(String, String)| shw(&p.1).to_lowercase(); // lowerCase.show.snd
    let g = |p: &(String, String)| shw(&p.1); // show.snd
                                              // clashesOn f g: stable-sort by f, group consecutive by f, each group
                                              // sortednubOn g; keep groups with >= 2 distinct g.
    let mut sorted: Vec<(String, String)> = pairs;
    sorted.sort_by_key(|a| f(a));
    let mut clashes: Vec<Vec<(String, String)>> = Vec::new();
    let mut i = 0;
    while i < sorted.len() {
        let key = f(&sorted[i]);
        let mut j = i + 1;
        while j < sorted.len() && f(&sorted[j]) == key {
            j += 1;
        }
        let mut grp: Vec<(String, String)> = sorted[i..j].to_vec();
        grp.sort_by_key(|a| g(a));
        grp.dedup_by(|a, b| g(a) == g(b));
        if grp.len() >= 2 {
            clashes.push(grp);
        }
        i = j;
    }
    if clashes.is_empty() {
        return Vec::new();
    }
    let topic = "Public constants with mismatching capitalization";
    let mut s = String::new();
    s.push_str(&underline_topic(topic));
    s.push('\n');
    s.push_str(
        "Identifiers are case-sensitive, mismatched capitalizations \
        are considered as different, i.e., 'ID' is different from 'id'. \
        Check the capitalization of your identifiers.\n",
    );
    s.push('\n');
    let w = numbered_index_width(clashes.len());
    let items: Vec<String> = clashes
        .iter()
        .enumerate()
        .map(|(k, grp)| {
            // groupOn fst: list each rule's names together.
            let mut parts: Vec<String> = Vec::new();
            let mut m = 0;
            while m < grp.len() {
                let rule = &grp[m].0;
                let mut names = vec![shw(&grp[m].1)];
                let mut n2 = m + 1;
                while n2 < grp.len() && &grp[n2].0 == rule {
                    names.push(shw(&grp[n2].1));
                    n2 += 1;
                }
                parts.push(format!("rule \"{}\":  name {}", rule, names.join(", ")));
                m = n2;
            }
            format!("  {:>w$}. {}", k + 1, parts.join(", "), w = w)
        })
        .collect();
    s.push_str(&items.join("\n  \n"));
    s.push('\n');
    vec![WfError::new(topic, s)]
}

/// Port of HS `publicNamesReport'` (Wellformedness.hs:463-484) over the
/// TRANSLATED theory's rules.  HS runs the FULL `checkWellformedness` on that
/// theory, so `publicNames = universeBi ru` walks each generated rule
/// INCLUDING the source subprocess HS attaches to it — and the parser AST
/// stores that subprocess only as a rendered `process="…"` string, so a
/// constant appearing solely inside the process (the `'C'` in
/// `insert <'roles', x, 'C'>`) is reachable only from the elaborated rule.
/// Walk the ELABORATED rules' facts AND their `process` attribute.
///
/// The root `Init` rule carries the WHOLE process (`base_init` in
/// tamarin-sapic's base_translation.rs; HS `baseInit`,
/// Basetranslation.hs:312-317, see line 313 — the rule's annotation is `anP`, the full
/// process) and is emitted first, so under `clashesOn`'s
/// first-occurrence dedup it wins every public name — reproducing HS's
/// `rule "Init":  name 'C', 'c'` attribution.
pub fn translated_public_names_report(thy: &Theory) -> Vec<WfError> {
    let mut pairs: Vec<(String, String)> = Vec::new();
    for r in thy.items.iter().filter_map(|it| match it {
        crate::theory::TheoryItem::Rule(r) => Some(r),
        _ => None,
    }) {
        // HS `showRuleCaseName ru = prettyProtoRuleName (ruleName ru)`
        // (Theory/Model/Rule.hs:1338-1340) = `prefixIfReserved n` for a
        // `StandRule n`.
        let case_name = crate::rule::prefix_if_reserved(r.name());
        let mut names: Vec<String> = Vec::new();
        for f in r
            .rule
            .premises
            .iter()
            .chain(&r.rule.actions)
            .chain(&r.rule.conclusions)
        {
            for t in f.terms.iter() {
                crate::elaborate::collect_pub_names(t, &mut names);
            }
        }
        if let Some(proc) = &r.rule.info.attributes.process {
            crate::elaborate::collect_process_pub_names(proc, &mut names);
        }
        for n in names {
            pairs.push((case_name.clone(), n));
        }
    }
    public_names_report_from_pairs(pairs)
}

// =============================================================================
// Variable sort/capitalization clashes (within a single rule)
// =============================================================================

/// Within each rule, variables whose names agree modulo case AND share an
/// index, but differ in their full `LVar` (sort or capitalization), clash.
/// Port of HS `sortsClashCheck`/`ruleSortsReport` (Wellformedness.hs:258-280):
/// `clashesOn removeSort id $ frees ru` where `removeSort lv = (lowerCase
/// (lvarName lv), lvarIdx lv)`.  Bare identifiers default to sort `msg`
/// (HS LSortMsg), so `~ltk` (fresh) vs `ltk` (msg) clash.  Runs on the
/// let-substituted rule (HS `thyProtoRules` applies let-subst).
///
/// Emits one `WfError` per offending rule (so the summary's `length rep`
/// WARNING count matches HS, Batch.hs:87-316, see line 245), all sharing the topic
/// "Variable with mismatching sorts or capitalization"; `format_wf_block`
/// renders the header + "Possible reasons" preamble ONCE for the group.
pub fn variable_sort_clashes(_elab: &Theory, parsed: &p::Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(parsed) {
        // Pair each var with its lowercase name ONCE, so the sort/group steps
        // below don't re-allocate a `to_lowercase` string per comparison/probe.
        let mut vars: Vec<(String, p::VarSpec)> = Vec::new();
        for f in rule_facts(r) {
            for v in fact_vars(f) {
                vars.push((v.name.to_lowercase(), v));
            }
        }
        // clashesOn removeSort id: sort+group by (lowercase name, idx).
        // Stable sort over the precomputed lowercase key — identical order to
        // re-lowercasing in the comparator.
        vars.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.idx.cmp(&b.1.idx)));
        let mut clash_groups: Vec<Vec<&p::VarSpec>> = Vec::new();
        let mut i = 0;
        while i < vars.len() {
            let key = (vars[i].0.as_str(), vars[i].1.idx);
            let mut j = i + 1;
            while j < vars.len() && (vars[j].0.as_str(), vars[j].1.idx) == key {
                j += 1;
            }
            // sortednubOn id: sort by HS LVar Ord (idx, sort, name) then dedup.
            let mut grp: Vec<&p::VarSpec> = vars[i..j].iter().map(|(_, v)| v).collect();
            grp.sort_by(|a, b| {
                a.idx
                    .cmp(&b.idx)
                    .then_with(|| a.sort.cmp(&b.sort))
                    .then_with(|| a.name.cmp(&b.name))
            });
            grp.dedup_by(|a, b| a.name == b.name && a.sort == b.sort && a.idx == b.idx);
            if grp.len() >= 2 {
                clash_groups.push(grp);
            }
            i = j;
        }
        if clash_groups.is_empty() {
            continue;
        }
        // Body (headerless): HS snd = `text info $-$ nest 2 (numbered' $ map
        // prettyVarList cs)`, with ppTopic's outer `nest 2` baked in →
        // "  rule `X': \n    1. <vars>".  `numbered'` separates items by a
        // blank `text ""` line, which at 4-space indent renders as "    ".
        let mut body = format!("  rule `{}': \n", r.name);
        let w = numbered_index_width(clash_groups.len());
        let items: Vec<String> = clash_groups
            .iter()
            .enumerate()
            .map(|(k, grp)| {
                let vs: Vec<String> = grp.iter().copied().map(render_var).collect();
                format!("    {:>w$}. {}", k + 1, vs.join(", "), w = w)
            })
            .collect();
        body.push_str(&items.join("\n    \n"));
        out.push(WfError::new(
            "Variable with mismatching sorts or capitalization",
            body,
        ));
    }
    out
}

#[cfg(test)]
#[path = "rules_tests.rs"]
mod tests;
