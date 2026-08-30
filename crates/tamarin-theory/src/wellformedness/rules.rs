// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The wellformedness checks that walk a theory's rules.
//!
//! HS `unboundReport` (Wellformedness.hs:514-519), `freshNamesReport'`
//! (Wellformedness.hs:444-452), `ruleSortsReport`
//! (Wellformedness.hs:275-279) and `natWellSortedReport`
//! (Wellformedness.hs:319-333) read `thyProtoRules thy`
//! (Wellformedness.hs:133-134) — the macro-applied `oprRuleE` of every rule
//! item of the `OpenTranslatedTheory`.  The elaborated [`Theory`]'s rules are
//! that set: `elaborate` applies the theory's macros and `apply_sapic`
//! appends the generated rules, which is the same input [`super::mult`]
//! reads.  [`public_names_report`] (HS `publicNamesReport'`,
//! Wellformedness.hs:463-484) reads them too, including the source
//! subprocess a generated rule carries.
//!
//! The two checks that read a whole rule rather than its facts take HS's own
//! reach: [`fresh_names_report`] walks [`rule_names`], the `universeBi ru`
//! name traversal, and [`rule_sorts_report`] folds
//! [`crate::rule::proto_rule_e_frees`], the `frees` fold that descends into
//! the rule info's `_restrict` formulas.
//!
//! [`unbound_report`]'s body is HS's `text info $-$ nest 2 (prettyVarList
//! vars)` paragraph fill, so it hands its variable cells to
//! [`WfError::filled`] and lets the HughesPJ engine break them.
//! [`nat_well_sorted_report`] renders its own `<>` chain at the same width —
//! the style `addComment` bakes the wellformedness comment in with, HughesPJ's
//! library default `lineLength = 100`, `ribbonsPerLine = 1.5`
//! (TheoryObject.hs:717-718).

use std::collections::BTreeSet;

use tamarin_term::function_symbols::{nat_one_sym, AcSym, FunSym};
use tamarin_term::lterm::{frees, frees_list, sort_of_name, LNTerm, LSort, LVar, Name};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::pretty::pretty_nterm;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

use crate::elaborate::{collect_names, collect_process_names};
use crate::formula::{for_each_formula_term, formula_frees_list};
use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{proto_rule_e_frees, ProtoRuleE};
use crate::sapic::{Process, ProcessCombinator};
use crate::theory::{Theory, TheoryItem};
use crate::tools::rule_variants::open_rule_has_no_variants;

use super::{
    quote, show_rule_case_name, thy_proto_rules, underline_topic, WfError, WfReport,
    WF_LINE_LENGTH, WF_RIBBON,
};

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
    let process: &crate::sapic::PlainProcess = ru.info.attributes.process.as_deref()?;
    match process {
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
pub fn nat_well_sorted_report(thy: &Theory) -> Vec<WfError> {
    // HS builds the report as a plain `Doc`: `prettyWfErrorReport`'s text
    // never passes through the escaping `Document (HtmlDoc d)` instance
    // (Html.hs:102-105), so a pair term inside a body keeps its raw `<`/`>`
    // on the web routes, which render under an active `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    let mut out = Vec::new();
    let mut report_term = |t: &LNTerm| {
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
    };
    for ru in thy_proto_rules(thy) {
        for t in rule_terms(ru) {
            report_term(t);
        }
    }
    for item in &thy.items {
        let formula = match item {
            TheoryItem::Lemma(l) => Some(&l.formula),
            TheoryItem::Restriction(r) => Some(&r.formula),
            TheoryItem::Predicate(p) => Some(&p.formula),
            _ => None,
        };
        if let Some(guarded) = formula.and_then(|f| crate::guarded::formula_to_guarded(f).ok()) {
            for_each_bound_guarded_term(&guarded, &[], &mut report_term);
        }
    }
    out
}

/// HS `boundTerms` (Wellformedness.hs:283-290): open each guarded block's
/// locally nameless binders, then visit the terms of atom bodies. Guard atoms
/// are excluded exactly as in the reference implementation.
fn for_each_bound_guarded_term(
    guarded: &crate::guarded::Guarded,
    binders: &[(u64, LVar)],
    f: &mut dyn FnMut(&LNTerm),
) {
    use crate::guarded::Guarded;
    match guarded {
        Guarded::Atom(atom) => {
            let atom = crate::guarded::subst_bound_atom(binders, atom);
            crate::atom::fold_atom(&atom, &mut |term| {
                let term = crate::guarded::bterm_to_lterm(term);
                f(&term);
            });
        }
        Guarded::Disj(items) | Guarded::Conj(items) => {
            for item in items.iter() {
                for_each_bound_guarded_term(item, binders, f);
            }
        }
        Guarded::GGuarded { vars, body, .. } => {
            let mut extended: Vec<(u64, LVar)> = vars
                .iter()
                .rev()
                .enumerate()
                .map(|(i, (name, sort))| (i as u64, LVar::new(name, *sort, 0)))
                .collect();
            extended.extend_from_slice(binders);
            for_each_bound_guarded_term(body, &extended, f);
        }
    }
}

// =============================================================================
// Helpers — the name literals of a rule
// =============================================================================

/// Every `Name` of a rule, in HS `universeBi ru` order — the `Data`
/// traversal visits a constructor's fields left to right, so the rule info
/// comes first (its attributes, then its `_restrict` formulas —
/// Theory/Model/Rule.hs:421-425) and the premises, conclusions, actions and
/// new variables follow (Theory/Model/Rule.hs:218-225).
fn rule_names(ru: &ProtoRuleE) -> Vec<Name> {
    let mut out = Vec::new();
    // The source subprocess a SAPIC-generated rule carries: HS's `universeBi`
    // descends into it, so a constant that appears only there is a name of
    // the rule.  HS's rule-attribute parser discards a written `process=`
    // (`parseAndIgnore`, Theory/Text/Parser/Rule.hs:70-96, see line 74), so a
    // user rule never carries one.
    if let Some(proc) = &ru.info.attributes.process {
        collect_process_names(proc, &mut out);
    }
    for phi in &ru.info.restrictions {
        for_each_formula_term(phi, &mut |t| collect_names(t, &mut out));
    }
    for fa in ru.premises.iter().chain(&ru.conclusions).chain(&ru.actions) {
        for t in fa.terms.iter() {
            collect_names(t, &mut out);
        }
    }
    for t in &ru.new_vars {
        collect_names(t, &mut out);
    }
    out
}

// =============================================================================
// Fresh public constants — `~'foo'` is forbidden
// =============================================================================

/// Port of HS `freshNamesReport'` (Wellformedness.hs:444-452): one body per
/// rule that mentions a fresh-sorted `Name`, the `~'foo'` literal no `Fr`
/// premise can produce.
///
/// The body is HS's `fsep $ text info : punctuate comma (map (nest 2 . text
/// . show) names)` — ONE paragraph fill whose first cell is the info line, so
/// a name that would overrun the ribbon takes a line of its own at the fill's
/// indent plus 2.  `show (Name FreshName n) = "~'" ++ show n ++ "'"`
/// (LTerm.hs:235-240, see line 236) is [`Name`]'s `Display`, and the `nest 2`
/// `prettyWfErrorReport` applies to every body of a topic group
/// (Wellformedness.hs:118-125) is baked in, because the break decisions
/// depend on the body's absolute column.  [`grouped_topic_block`] joins the
/// rendered bodies under the one `underlineTopic` header.
pub fn fresh_names_report(thy: &Theory) -> WfReport {
    // Plain mode for the same reason as [`nat_well_sorted_report`]: the body
    // is a `Doc` built and laid out here, and the web routes render under an
    // active `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    let topic = "Fresh public constants";
    let mut report = Vec::new();
    for ru in thy_proto_rules(thy) {
        let names: Vec<Name> = rule_names(ru)
            .into_iter()
            .filter(|n| sort_of_name(n) == LSort::Fresh)
            .collect();
        if names.is_empty() {
            continue;
        }
        let mut cells = vec![Doc::text(format!(
            "rule {}: fresh public constants are not allowed:",
            quote(&show_rule_case_name(ru))
        ))];
        cells.extend(hpj::punctuate(
            Doc::char(','),
            names
                .iter()
                .map(|n| Doc::text(n.to_string()).nest(2))
                .collect(),
        ));
        report.push(WfError::new(
            topic,
            hpj::fsep(cells)
                .nest(2)
                .render_with(WF_LINE_LENGTH, WF_RIBBON),
        ));
    }
    report
}

// =============================================================================
// Public constant capitalization clashes
// =============================================================================

/// HS `clashesOn f g xs` (Wellformedness.hs:154-161): stable-sort by `f`,
/// group the consecutive runs equal under `f`, `sortednubOn g` each run
/// (sort by `g`, keep the first element per distinct `g`), and return the
/// runs holding at least two elements.  `f` is taken once per element.
fn clashes_on<A: Clone, B: Ord, C: Ord>(
    f: impl Fn(&A) -> B,
    g: impl Fn(&A) -> C,
    xs: &[A],
) -> Vec<Vec<A>> {
    let mut keyed: Vec<(B, &A)> = xs.iter().map(|a| (f(a), a)).collect();
    keyed.sort_by(|x, y| x.0.cmp(&y.0));
    let mut out = Vec::new();
    let mut i = 0;
    while i < keyed.len() {
        let mut j = i + 1;
        while j < keyed.len() && keyed[j].0 == keyed[i].0 {
            j += 1;
        }
        let mut grp: Vec<A> = keyed[i..j].iter().map(|(_, a)| (*a).clone()).collect();
        grp.sort_by_key(|a| g(a));
        grp.dedup_by(|a, b| g(a) == g(b));
        if grp.len() >= 2 {
            out.push(grp);
        }
        i = j;
    }
    out
}

/// The clash-detection + rendering half of HS `publicNamesReport'`
/// (Wellformedness.hs:463-484).  Its caller,
/// [`public_names_report`], harvests the
/// `(showRuleCaseName, pubName)` pairs from the ELABORATED rules — including
/// the `process` attribute HS's `universeBi` walks — which the parser AST
/// stores only as a rendered string.  `pairs` must arrive in rule order
/// (matching HS `thyProtoRules`), first-occurrence-wins: `clashesOn` keeps the
/// earliest `(rule, name)` per distinct public name.
fn public_names_report_from_pairs(pairs: Vec<(String, String)>) -> WfReport {
    // HS `show` of a (public) Name constant is the quoted form `'name'`.
    let shw = |n: &str| format!("'{}'", n);
    // HS `findClashes = clashesOn (map toLower . show . snd) (show . snd)`
    // (Wellformedness.hs:479).
    let clashes = clashes_on(
        |p: &(String, String)| shw(&p.1).to_lowercase(),
        |p: &(String, String)| shw(&p.1),
        &pairs,
    );
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
    let items: Vec<Doc> = clashes
        .iter()
        .map(|grp| {
            // groupOn fst: list each rule's names together.
            let mut parts: Vec<Doc> = Vec::new();
            let mut m = 0;
            while m < grp.len() {
                let rule = &grp[m].0;
                let mut names = vec![shw(&grp[m].1)];
                let mut n2 = m + 1;
                while n2 < grp.len() && &grp[n2].0 == rule {
                    names.push(shw(&grp[n2].1));
                    n2 += 1;
                }
                parts.push(Doc::text(format!(
                    "rule \"{}\":  name {}",
                    rule,
                    names.join(", ")
                )));
                m = n2;
            }
            hpj::fsep(hpj::punctuate(Doc::char(','), parts)).nest(2)
        })
        .collect();
    s.push_str(
        &hpj::numbered_prime(items)
            .nest(2)
            .render_with(WF_LINE_LENGTH, WF_RIBBON),
    );
    s.push('\n');
    vec![WfError::new(topic, s)]
}

/// Port of HS `publicNamesReport'` (Wellformedness.hs:463-484) over the
/// translated theory's rules.  `publicNames = universeBi ru` is the same
/// whole-rule name walk `freshNamesReport'` uses, [`rule_names`] here, so it
/// reaches the rule info's `_restrict` formulas and the source subprocess HS
/// attaches to a generated rule — the `'C'` in `insert <'roles', x, 'C'>`
/// counts as a name of the rule that carries that process.
///
/// The root `Init` rule carries the WHOLE process (`base_init` in
/// tamarin-sapic's base_translation.rs; HS `baseInit`,
/// Basetranslation.hs:312-317, see line 313 — the rule's annotation is `anP`, the full
/// process) and is emitted first, so under `clashesOn`'s
/// first-occurrence dedup it wins every public name — reproducing HS's
/// `rule "Init":  name 'C', 'c'` attribution.
pub fn public_names_report(thy: &Theory) -> Vec<WfError> {
    let mut pairs: Vec<(String, String)> = Vec::new();
    for ru in thy_proto_rules(thy) {
        let case_name = show_rule_case_name(ru);
        for n in rule_names(ru) {
            if sort_of_name(&n) == LSort::Pub {
                pairs.push((case_name.clone(), n.id.0.to_string()));
            }
        }
    }
    public_names_report_from_pairs(pairs)
}

// =============================================================================
// Variable sort/capitalization clashes (within a single rule)
// =============================================================================

/// HS `prettyVarList = fsep . punctuate comma . map prettyLVar`
/// (TheoryObject.hs:858-859), whose `prettyLVar = text . show`
/// (LTerm.hs:922-923) makes each cell a leaf.
fn pretty_var_list(vars: &[LVar]) -> Doc {
    hpj::fsep(hpj::punctuate(
        Doc::char(','),
        vars.iter().map(|v| Doc::text(v.to_string())).collect(),
    ))
}

/// Port of HS `sortsClashCheck` (Wellformedness.hs:258-272): the variables
/// that agree modulo case and index but differ as `LVar`s clash.  Bare
/// identifiers carry sort `msg`, so `~ltk` (fresh) and `ltk` (msg) are a
/// clash.
///
/// The body is HS's `text info $-$ nest 2 (numbered' $ map prettyVarList cs)`
/// with `prettyWfErrorReport`'s per-body `nest 2`
/// (Wellformedness.hs:118-125) baked in, so the fills break at the body's
/// true column.  The header and the "Possible reasons" paragraph HS carries
/// in the topic string come from the topic itself, through
/// `pretty_theory`'s headerless-preamble table.
fn sorts_clash_check(info: String, vars: &[LVar]) -> Vec<WfError> {
    // HS `clashesOn removeSort id $ frees t` (Wellformedness.hs:259) with
    // `removeSort lv = (lowerCase (lvarName lv), lvarIdx lv)`; the identity
    // projection's `sortednubOn` sorts by `Ord LVar` — the index, then the
    // sort, then the name (LTerm.hs:546-548).
    let clashes = clashes_on(
        |v: &LVar| (v.name.to_lowercase(), v.idx),
        |v: &LVar| *v,
        vars,
    );
    if clashes.is_empty() {
        return Vec::new();
    }
    // `above_g` is HughesPJ's `$+$`, which HS's `$-$` maps to
    // (Text/PrettyPrint/Class.hs:180).
    let body = Doc::text(info)
        .above_g(
            hpj::numbered_prime(clashes.iter().map(|grp| pretty_var_list(grp)).collect()).nest(2),
        )
        .nest(2)
        .render_with(WF_LINE_LENGTH, WF_RIBBON);
    vec![WfError::new(
        "Variable with mismatching sorts or capitalization",
        body,
    )]
}

/// Port of HS `ruleSortsReport` (Wellformedness.hs:275-279): one entry per
/// offending rule, so the summary's `length rep` WARNING count matches HS
/// (Batch.hs:246).  Its input is `frees ru`, which folds the rule info first
/// and so reaches a variable that occurs only in a `_restrict` formula
/// ([`proto_rule_e_frees`]).
pub fn rule_sorts_report(thy: &Theory) -> WfReport {
    // Plain mode for the same reason as [`nat_well_sorted_report`]: the body
    // is a `Doc` built and laid out here, and the web routes render under an
    // active `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    let mut out = Vec::new();
    for ru in thy_proto_rules(thy) {
        out.extend(sorts_clash_check(
            format!("rule {}: ", quote(&show_rule_case_name(ru))),
            &proto_rule_e_frees(ru),
        ));
    }
    out
}

// =============================================================================
// Rule variants
// =============================================================================

/// Port of HS `ruleVariantsReport` (Wellformedness.hs:375-382): HS's
/// `variantsCheck` (Wellformedness.hs:354-372) over every rule item, with a
/// live Maude behind the variant recomputation.
///
/// Only the `guard (null recomputedVariants)` arm (Wellformedness.hs:362-366)
/// is ported.  The other arm, "Variants", compares a `variants (modulo AC)`
/// block written out in the rule body against the recomputed set; no corpus
/// file writes such a block, and the internal rule's `rule_ac` half would have
/// to be re-abstracted to compare it.
///
/// `maude` is `None` on the web load path, which produces no such block.
/// [`open_rule_has_no_variants`] answers from the verdict
/// `populate_rule_variants` recorded on each rule, so the check issues no
/// Maude query of its own; the driver keys the no-variant rule drop off the
/// same predicate (HS `closeProtoRule`, lib/theory/src/Rule.hs:82-86).
pub fn rule_variants_report(thy: &Theory, maude: Option<&MaudeHandle>) -> WfReport {
    let Some(maude) = maude else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for opr in thy.rules() {
        if !open_rule_has_no_variants(maude, opr) {
            continue;
        }
        // HS `text "Rule " <> prettyRuleName ruE <> text " has no variants."
        // $--$ text "Most likely, ..." <> text "For exaple, ..."`
        // (Wellformedness.hs:363-366).  Every piece is a `text`, which
        // HughesPJ never breaks, so the paragraph is one long line and the
        // `$--$` blank line carries the group's `nest 2` indent.  "For exaple"
        // is spelled that way in the HS source.
        let topic = "Rule has no variants";
        let body = format!(
            "  Rule {} has no variants.\n  \n  Most likely, this means that \
             the rule's use of fresh variables is contradictory. For exaple, \
             a rule with the premises In(~x) and Fr(~x) has no variants \
             because ~x cannot be sent before it is generated.",
            show_rule_case_name(&opr.rule),
        );
        let mut msg = underline_topic(topic);
        msg.push('\n');
        msg.push_str(&body);
        msg.push('\n');
        out.push(WfError::new(topic, msg));
    }
    out
}

#[cfg(test)]
#[path = "rules_tests.rs"]
mod tests;
