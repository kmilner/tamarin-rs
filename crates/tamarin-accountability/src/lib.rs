// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Accountability translation for the Tamarin prover (Rust port).
//!
//! Port of `Accountability` + `Accountability.Generation`
//! (lib/accountability/src/Accountability{,/Generation}.hs).  `translate`
//! expands each `lemma <name> [..]: c1, .. accounts for "φ"` into the seven
//! verification-condition lemmas (per `test <c>` case test) and the case-test
//! predicates, injecting them into both the parser-AST theory (rendered by
//! `pretty_closed_theory`) and the elaborated theory (proved by the prove loop).
//! `check_wellformedness` produces the "Accountability (RP check)" report.
//!
//! The driver (`tamarin-prover`) calls `translate` right after the SAPIC stage
//! (case-test formulas may reference user function symbols, whose thread-local
//! flags must be installed) and prepends `check_wellformedness`'s report after
//! the SAPIC warnings.

mod formula;
mod generation;

use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_term::lterm::LSort;

use tamarin_theory::elaborate::elaborate_lemma_attr;
use tamarin_theory::theory::{self as t, Theory, TheoryItem};

use crate::formula::{frees, from_p_formula, to_p_formula, Fm};
use crate::generation::{generate_accountability_lemmas, AccData, CaseTestData};

/// Accountability translation error: HS `AccException`
/// (lib/accountability/src/Accountability.hs:31-39) plus the
/// `ParsingException`s HS `translate` can throw through `liftedAddLemma` /
/// `liftedAddPredicate` (Parser/Exceptions.hs:28-44).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccError {
    /// HS `CaseTestsUndefined`: one or more case tests required by an
    /// accountability lemma are not defined.  Each entry is
    /// `(lemma name, missing case-test identifiers)`.
    CaseTestsUndefined(Vec<(String, Vec<String>)>),
    /// HS `UndefinedPredicate` (thrown by `liftedAddLemma`'s `expandLemma`,
    /// Text/Parser.hs:116-118,145-147, when a generated lemma's formula references an
    /// undefined predicate).  Carries HS's `showFactTagArity` rendering,
    /// `name/arity`.
    UndefinedPredicate(String),
    /// HS `DuplicateItem (LemmaItem _)` (thrown by `liftedAddLemma` when a
    /// generated lemma's name collides with an existing lemma).
    DuplicateLemma(String),
    /// HS `DuplicateItem (PredicateItem _)` (thrown by `liftedAddPredicate`,
    /// Parser/Signature.hs:328-331, when a case-test predicate's fact tag
    /// collides with an existing predicate).  Carries the rendered fact.
    DuplicatePredicate(String),
}

impl std::fmt::Display for AccError {
    /// Mirrors HS `show` of the corresponding exception
    /// (lib/accountability/src/Accountability.hs:36-38 /
    /// Parser/Exceptions.hs:33-44); the driver prefixes `tamarin-prover: ` as
    /// GHC's top-level handler does.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccError::CaseTestsUndefined(el) => {
                write!(
                    f,
                    "The following case tests are undefined but are required in a lemma: \n{}",
                    el.iter()
                        .map(|(name, cs)| format!(
                            "  '{}' required by lemma '{}'",
                            cs.join("', '"),
                            name
                        ))
                        .collect::<Vec<_>>()
                        .join("\n")
                )
            }
            AccError::UndefinedPredicate(tag) => write!(f, "undefined predicate {}", tag),
            AccError::DuplicateLemma(name) => write!(f, "duplicate lemma: {}", name),
            AccError::DuplicatePredicate(fact) => write!(f, "duplicate predicate: {}", fact),
        }
    }
}

// =============================================================================
// Reading the accountability items from the parser-AST theory
// =============================================================================

struct RawAccLemma {
    name: String,
    attributes: Vec<p::LemmaAttr>,
    formula: p::Formula,
    case_test_idents: Vec<String>,
}

struct RawCaseTest {
    name: String,
    formula: p::Formula,
}

/// The theory's case tests (declaration order) and accountability lemmas.
/// Each acc lemma is paired with the number of case tests declared BEFORE it:
/// HS binds `_aCaseTests` when the lemma is parsed (`mapMaybe (flip
/// lookupCaseTest thy)` over the items parsed so far, Text/Parser.hs:276-279), so a
/// case test declared after the lemma is undefined for it.
fn collect_acc_items(parsed: &p::Theory) -> (Vec<RawCaseTest>, Vec<(RawAccLemma, usize)>) {
    let mut case_tests: Vec<RawCaseTest> = Vec::new();
    let mut acc_lemmas: Vec<(RawAccLemma, usize)> = Vec::new();
    for i in &parsed.items {
        match i {
            p::TheoryItem::CaseTest(c) => {
                case_tests.push(RawCaseTest {
                    name: c.name.clone(),
                    formula: c.formula.clone(),
                });
            }
            p::TheoryItem::AccLemma(a) => {
                acc_lemmas.push((
                    RawAccLemma {
                        name: a.name.clone(),
                        attributes: a.attributes.clone(),
                        formula: a.formula.clone(),
                        case_test_idents: a.case_test_idents.clone(),
                    },
                    case_tests.len(),
                ));
            }
            _ => {}
        }
    }
    (case_tests, acc_lemmas)
}

/// HS list difference `xs \\ ys`: remove, for each element of `ys`, its first
/// occurrence in `xs`.
fn list_diff(xs: &[String], ys: &[String]) -> Vec<String> {
    let mut result = xs.to_vec();
    for y in ys {
        if let Some(pos) = result.iter().position(|r| r == y) {
            result.remove(pos);
        }
    }
    result
}

/// HS `undefinedCaseTests` (lib/accountability/src/Accountability.hs:53-58):
/// the ident list `required` vs the resolved-case-test names `defined` (idents
/// that name a defined case test, in order).  Returns the missing idents when
/// the two lists differ.
fn undefined_case_tests(acc: &RawAccLemma, defined_names: &[String]) -> Option<Vec<String>> {
    let required = &acc.case_test_idents;
    let defined: Vec<String> = required
        .iter()
        .filter(|id| defined_names.contains(id))
        .cloned()
        .collect();
    if *required != defined {
        Some(list_diff(required, &defined))
    } else {
        None
    }
}

// =============================================================================
// translate
// =============================================================================

/// Expand the accountability lemmas + case-test predicates into `parsed` and
/// `elaborated` (HS `Accountability.translate`,
/// lib/accountability/src/Accountability.hs:42-49).  A no-op when the theory
/// declares neither accountability lemmas nor case tests, so ordinary
/// theories are byte-unchanged.  Case tests WITHOUT any
/// acc lemma still get their predicates appended (HS `translate` runs its
/// `caseTestToPredicate` fold unconditionally).
pub fn translate(parsed: &mut p::Theory, elaborated: &mut Theory) -> Result<(), AccError> {
    let (case_tests, acc_lemmas) = collect_acc_items(parsed);
    if acc_lemmas.is_empty() && case_tests.is_empty() {
        return Ok(());
    }

    // HS: `unless (null undef) (throwM (CaseTestsUndefined undef))`.  Each
    // lemma only sees the case tests declared before it (`n_before`).
    let undef: Vec<(String, Vec<String>)> = acc_lemmas
        .iter()
        .filter_map(|(a, n_before)| {
            let defined_names: Vec<String> = case_tests[..*n_before]
                .iter()
                .map(|c| c.name.clone())
                .collect();
            undefined_case_tests(a, &defined_names).map(|m| (a.name.clone(), m))
        })
        .collect();
    if !undef.is_empty() {
        return Err(AccError::CaseTestsUndefined(undef));
    }

    // Pre-convert each case test's formula to locally-nameless form once
    // (declaration order, so `[..n_before]` is each lemma's visible scope).
    let case_test_data: Vec<(String, Fm)> = case_tests
        .iter()
        .map(|c| (c.name.clone(), from_p_formula(&c.formula)))
        .collect();

    // Predicate fact tags `(name, arity, persistent)` defined for this theory:
    // every `predicates:` item (HS `theoryPredicates` — position-insensitive at
    // translate time) plus the builtin `Smaller/2` (HS `lookupPredicate`
    // appends `builtinPredicates`, Predicate.hs:77-78).  Backs the
    // `UndefinedPredicate` / `DuplicateItem (PredicateItem _)` error paths;
    // grows as case-test predicates are added (HS folds `thy'` through
    // `liftedAddPredicate`).
    let mut defined_preds: Vec<(String, usize, bool)> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Predicates(ps) => Some(
                ps.iter()
                    .map(|pr| (pr.fact.name.clone(), pr.fact.args.len(), pr.fact.persistent)),
            ),
            _ => None,
        })
        .flatten()
        .collect();
    defined_preds.push(("Smaller".to_string(), 2, false));

    // The predicate DEFINITIONS `expandLemma` substitutes into each generated
    // lemma, in declaration order.  The case-test predicates are appended
    // after the lemma loop, so — as in HS, where `liftedAddLemma` expands
    // against `theoryPredicates thy` at the point of the add — they are not
    // among them.
    let declared_preds: Vec<p::Predicate> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Predicates(ps) => Some(ps.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect();

    // The macro DEFINITIONS `applyMacroInLemma` substitutes into each generated
    // lemma at close time (CloseRule.hs:85), in declaration order.
    let declared_macros: Vec<p::Macro> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Macros(ms) => Some(ms.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect();

    // Existing lemma names (HS `addLemma` guards on `lookupLemma`, which scans
    // `LemmaItem`s only — TheoryObject.hs:461-465); grows as generated lemmas
    // are appended.
    let mut lemma_names: Vec<String> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Lemma(l) => Some(l.name.clone()),
            _ => None,
        })
        .collect();

    // Generate + inject the lemmas, in theory order (HS
    // `foldM liftedAddLemma thy (concat accLemmas)`).
    for (acc, n_before) in &acc_lemmas {
        let scope = &case_test_data[..*n_before];
        let acc_data = AccData {
            name: acc.name.clone(),
            formula: from_p_formula(&acc.formula),
            case_tests: acc
                .case_test_idents
                .iter()
                .filter_map(|id| {
                    scope
                        .iter()
                        .find(|(n, _)| n == id)
                        .map(|(_, f)| CaseTestData {
                            name: id.clone(),
                            formula: f.clone(),
                        })
                })
                .collect(),
        };
        for gen in generate_accountability_lemmas(&acc_data) {
            // HS `liftedAddLemma` first predicate-expands the lemma
            // (`expandLemma`, throws `UndefinedPredicate`), then rejects
            // duplicate names (`DuplicateItem`).
            if let Some(tag) = undefined_predicate(&gen.formula, &defined_preds) {
                return Err(AccError::UndefinedPredicate(tag));
            }
            if lemma_names.iter().any(|n| n == &gen.name) {
                return Err(AccError::DuplicateLemma(gen.name));
            }
            lemma_names.push(gen.name.clone());
            let formula = to_p_formula(&gen.formula);
            inject_lemma(
                parsed,
                elaborated,
                &declared_preds,
                &declared_macros,
                &acc.attributes,
                &gen.name,
                gen.quantifier,
                formula,
            );
        }
    }

    // Case-test predicates (HS `mapMaybe caseTestToPredicate (theoryCaseTests thy)`
    // then `foldM liftedAddPredicate`), appended AFTER all generated lemmas.
    for c in &case_tests {
        if let Some(pred) = case_test_to_predicate(c) {
            let tag = (
                pred.fact.name.clone(),
                pred.fact.args.len(),
                pred.fact.persistent,
            );
            if defined_preds.contains(&tag) {
                return Err(AccError::DuplicatePredicate(render_fact(&pred.fact)));
            }
            defined_preds.push(tag);
            parsed.items.push(p::TheoryItem::Predicates(vec![pred]));
        }
    }

    Ok(())
}

/// Fact tags of the `Pred` atoms in `fm` that match no defined predicate
/// (first offender, rendered as HS `showFactTagArity`: `name/arity`).
fn undefined_predicate(fm: &Fm, defined: &[(String, usize, bool)]) -> Option<String> {
    formula::formula_pred_facts(fm).into_iter().find_map(|f| {
        let known = defined
            .iter()
            .any(|(n, a, p_)| *n == f.name && *a == f.args.len() && *p_ == f.persistent);
        if known {
            None
        } else {
            Some(format!(
                "{}{}/{}",
                if f.persistent { "!" } else { "" },
                f.name,
                f.args.len()
            ))
        }
    })
}

/// Render a predicate fact for the `duplicate predicate:` message (HS
/// `prettyFact prettyLVar`, e.g. `Foo( x, y )`).
fn render_fact(f: &p::Fact) -> String {
    let args = f
        .args
        .iter()
        .map(|t| match t {
            p::Term::Var(v) if v.idx == 0 => v.name.clone(),
            p::Term::Var(v) => format!("{}.{}", v.name, v.idx),
            _ => String::from("_"),
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "{}{}( {} )",
        if f.persistent { "!" } else { "" },
        f.name,
        args
    )
}

/// Append one generated lemma to both theories (HS `addLemma`, which appends at
/// the end of the item list, TheoryObject.hs:461-465).  The elaborated lemma
/// carries the two formulas a closed theory's lemma holds: `_lOriginalFormula`
/// is the one `expandLemma` builds, predicate-expanded against `predicates`
/// (Theory/Text/Parser.hs:141-152), and `_lFormula` is that formula with the
/// theory's macros applied, which `closeTheory` maps over every lemma
/// including the ones this translation added (`applyMacroInLemma`,
/// CloseRule.hs:85, lib/theory/src/Lemma.hs:83-88).  The parser-AST theory the
/// `--parse-only` and `-m msr` renderers walk keeps the surface form.  A
/// formula the expansion or the signature rejects is added to neither theory.
fn inject_lemma(
    parsed: &mut p::Theory,
    elaborated: &mut Theory,
    predicates: &[p::Predicate],
    macros: &[p::Macro],
    attributes: &[p::LemmaAttr],
    name: &str,
    quantifier: p::TraceQuantifier,
    formula: p::Formula,
) {
    let msig = &elaborated.signature.maude_sig;
    let close = |f: &p::Formula| {
        tamarin_theory::formula::from_parser(f, msig)
            .ok()
            .and_then(|syn| tamarin_theory::formula::to_lnformula(&syn))
    };
    let Ok(pred_expanded) = tamarin_theory::predicate_expand::expand_formula(&formula, predicates)
    else {
        return;
    };
    let with_macros = tamarin_theory::macro_expand::apply_macros_formula(macros, &pred_expanded);
    let (Some(original), Some(expanded)) = (close(&pred_expanded), close(&with_macros)) else {
        return;
    };
    let parsed_lemma = p::Lemma {
        name: name.to_string(),
        modulo: None,
        attributes: attributes.to_vec(),
        trace_quantifier: quantifier.clone(),
        formula,
        proof: None,
        // HS `skeletonLemma name "generation" ..` seeds `_lPlaintext` with
        // "generation" (ProofSkeleton.hs:63-64); never rendered by `--prove`.
        plaintext: "generation".to_string(),
    };
    parsed.items.push(p::TheoryItem::Lemma(parsed_lemma));

    let elab_lemma = t::Lemma {
        name: name.to_string(),
        modulo: None,
        attributes: attributes.iter().map(elaborate_lemma_attr).collect(),
        trace_quantifier: match &quantifier {
            p::TraceQuantifier::AllTraces => t::TraceQuantifier::AllTraces,
            p::TraceQuantifier::ExistsTrace => t::TraceQuantifier::ExistsTrace,
        },
        original_formula: Some(original),
        formula: expanded,
        proof: None,
        plaintext: "generation".to_string(),
    };
    elaborated.items.push(TheoryItem::Lemma(elab_lemma));
}

// =============================================================================
// caseTestToPredicate (Items/CaseTestItem.hs:33-36 + mkPredicate,
// Theory/Syntactic/Predicate.hs:38-42)
// =============================================================================

/// HS `caseTestToPredicate` (Items/CaseTestItem.hs:33-36): `Nothing` when the
/// case-test formula has syntactic sugar that `toLNFormula` cannot strip (a
/// predicate atom), otherwise `mkPredicate name formula`.
fn case_test_to_predicate(c: &RawCaseTest) -> Option<p::Predicate> {
    if formula_has_predicate_atom(&c.formula) {
        return None;
    }
    // HS `mkPredicate name formula = Predicate (protoFact Linear (capitalize
    // name) (frees formula)) formula`.  The fact args are the formula's sorted
    // free variables (concrete-sorted).
    let fm = from_p_formula(&c.formula);
    let free_vars = frees(&fm);
    let fact = p::Fact {
        persistent: false,
        name: capitalize(&c.name),
        args: free_vars.into_iter().map(p::Term::Var).collect(),
        annotations: Vec::new(),
    };
    Some(p::Predicate {
        fact,
        formula: c.formula.clone(),
    })
}

/// HS `toLNFormula` returns `Nothing` for a formula carrying syntactic sugar
/// (`Syntactic _`, i.e. a predicate atom).  Detect any `Pred` atom.
fn formula_has_predicate_atom(f: &p::Formula) -> bool {
    match f {
        p::Formula::True | p::Formula::False => false,
        p::Formula::Atom(p::Atom::Pred(_)) => true,
        p::Formula::Atom(_) => false,
        p::Formula::Not(g) => formula_has_predicate_atom(g),
        p::Formula::And(a, b)
        | p::Formula::Or(a, b)
        | p::Formula::Implies(a, b)
        | p::Formula::Iff(a, b) => formula_has_predicate_atom(a) || formula_has_predicate_atom(b),
        p::Formula::Forall(_, body) | p::Formula::Exists(_, body) => {
            formula_has_predicate_atom(body)
        }
    }
}

/// HS `capitalize` (Predicate.hs:39-43, see line 42): upper-case the first character.
fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

// =============================================================================
// checkWellformedness / accRPReport (Generation.hs:324-346)
// =============================================================================

/// HS `Accountability.checkWellformedness` (Generation.hs:345-346): the RP-check
/// report, emitted only when the theory declares accountability lemmas.
pub fn check_wellformedness(parsed: &p::Theory) -> Vec<WfError> {
    let has_acc_lemma = parsed
        .items
        .iter()
        .any(|i| matches!(i, p::TheoryItem::AccLemma(_)));
    if !has_acc_lemma {
        return Vec::new();
    }
    acc_rp_report(parsed)
}

/// HS `accRPReport` (Generation.hs:324-343): the topic + explanation for the
/// RP (BR) syntactic criterion.  Empty when no warning fires.
fn acc_rp_report(parsed: &p::Theory) -> Vec<WfError> {
    let rules = rp_check_rules(parsed);
    let mut warnings: Vec<String> = Vec::new();
    if theory_has_restrictions(parsed) {
        warnings.push("The specification contains at least one restriction.".to_string());
    }
    if rules_contain_pub_const(&rules) {
        warnings.push("The specification contains public names.".to_string());
    }
    if !case_tests_instantiated_by_pub_vars(parsed, &rules) {
        warnings
            .push("At least one case test can be instantiated with non-public names.".to_string());
    }
    if warnings.is_empty() {
        return Vec::new();
    }

    // HS renders `text topic $-$ nest 2 (vcat warnings $--$ detailedExplanation)`
    // (prettyWfErrorReport, Wellformedness.hs:118-125).  `$--$` inserts one blank
    // line; `nest 2` indents every body line — including blanks — by two spaces.
    let mut body_lines: Vec<String> = warnings;
    body_lines.push(String::new());
    for line in DETAILED_EXPLANATION {
        body_lines.push(line.to_string());
    }
    let body = body_lines
        .iter()
        .map(|l| format!("  {}", l))
        .collect::<Vec<_>>()
        .join("\n");
    let message = format!("{ACC_RP_TOPIC}\n{body}");
    vec![WfError::new(ACC_RP_TOPIC, message)]
}

const ACC_RP_TOPIC: &str = "Accountability (RP check)";

/// HS `detailedExplanation` (Generation.hs:337-343), with the leading blank
/// line HS's `$--$` inserts between "Please verify …" and the "For each …"
/// paragraph.  Right single quotation marks (U+2019) are copied verbatim.
const DETAILED_EXPLANATION: &[&str] = &[
    "Please verify manually that your protocol fulfills the following condition:",
    "",
    "For each case test \u{03c4}, traces t, t\u{2019}, and instantiations \u{03c1}, \u{03c1}\u{2019}:",
    "If \u{03c4} holds on t with \u{03c1}, and \u{03c4} single-matches with \u{03c1}\u{2019} on t\u{2019}, then",
    "there exists a trace t\u{2019}\u{2019} such that \u{03c4} single-matches with \u{03c1} on t\u{2019}\u{2019}",
    "and the parties corrupted in t\u{2019}\u{2019} are the same as the parties",
    "corrupted in t\u{2019} renamed from rng(\u{03c1}\u{2019}) to rng(\u{03c1}).",
];

/// HS `not $ null $ theoryRestrictions thy`.
fn theory_has_restrictions(parsed: &p::Theory) -> bool {
    parsed.items.iter().any(|i| {
        matches!(
            i,
            p::TheoryItem::Restriction(_) | p::TheoryItem::LegacyAxiom(_)
        )
    })
}

/// The rules HS's RP check scans, reconstructed from the parser AST: each
/// rule's E-form plus its explicit AC variants (HS `rulesLNFacts` /
/// `rulesActions` read `_oprRuleE` and `_oprRuleAC`, Generation.hs:128-146),
/// with `let` blocks applied — HS substitutes lets into the rule at parse time
/// (Parser/Rule.hs:131-133), while our parser keeps `Rule.let_block` unapplied
/// until elaboration.  Macros stay UNexpanded: HS applies them only at theory
/// close (`closeProtoRule`, src/Rule.hs:82-86), after this check has run.
fn rp_check_rules(parsed: &p::Theory) -> Vec<p::Rule> {
    let mut out = Vec::new();
    for i in &parsed.items {
        if let p::TheoryItem::Rule(r) = i {
            out.push(tamarin_theory::elaborate::apply_let_block(r));
            for v in &r.variants {
                out.push(tamarin_theory::elaborate::apply_let_block(v));
            }
        }
    }
    out
}

/// HS `rulesContainPubConst thy = any termContainsPubConst (rulesLNTerms thy)`
/// (Generation.hs:320-322): any premise/action/conclusion term of any rule is
/// or contains a public constant.
fn rules_contain_pub_const(rules: &[p::Rule]) -> bool {
    rules.iter().any(|r| {
        r.premises
            .iter()
            .chain(&r.actions)
            .chain(&r.conclusions)
            .flat_map(|fa| fa.args.iter())
            .any(term_contains_pub_const)
    })
}

/// HS `termContainsPubConst` (Generation.hs:148-153): a public constant literal
/// (`'x'`) anywhere in the term.
fn term_contains_pub_const(t: &p::Term) -> bool {
    match t {
        p::Term::PubLit(_) => true,
        p::Term::Var(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => false,
        p::Term::App(_, args) | p::Term::Pair(args) => args.iter().any(term_contains_pub_const),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            term_contains_pub_const(a) || term_contains_pub_const(b)
        }
        p::Term::PatMatch(inner) => term_contains_pub_const(inner),
    }
}

/// HS `caseTestsInstantiatedByPubVars` (Generation.hs:314-318): for every
/// case-test action fact and every rule action fact sharing its tag, each free
/// variable of the case-test fact must line up with a public variable in the
/// rule fact.
fn case_tests_instantiated_by_pub_vars(parsed: &p::Theory, rules: &[p::Rule]) -> bool {
    let ct_facts = case_tests_facts(parsed);
    let rule_facts = rules_actions(rules);
    for cf in &ct_facts {
        for rf in &rule_facts {
            if fact_tag_eq(cf, rf) && !free_vars_instantiated_by_pub_vars(&cf.args, &rf.args) {
                return false;
            }
        }
    }
    true
}

/// HS `caseTestsFacts thy` (Generation.hs:120-122): the action facts of every
/// case test's formula (with Free/Bound variable status resolved).
fn case_tests_facts(parsed: &p::Theory) -> Vec<tamarin_theory::guarded_types::GFact> {
    let mut out = Vec::new();
    let (case_tests, _) = collect_acc_items(parsed);
    for c in &case_tests {
        let fm = from_p_formula(&c.formula);
        out.extend(formula::formula_action_facts(&fm));
    }
    out
}

/// HS `rulesActions thy` (Generation.hs:142-146): every rule's action facts.
fn rules_actions(rules: &[p::Rule]) -> Vec<&p::Fact> {
    rules.iter().flat_map(|r| r.actions.iter()).collect()
}

/// HS `FactTag` equality: same name, arity and persistence.
fn fact_tag_eq(cf: &tamarin_theory::guarded_types::GFact, rf: &p::Fact) -> bool {
    cf.name == rf.name && cf.args.len() == rf.args.len() && cf.persistent == rf.persistent
}

/// HS `freeVarsInstantiatedByPubVars` (Generation.hs:308-312): at each position
/// where the case-test fact holds a free variable, the rule fact must hold a
/// public variable.
fn free_vars_instantiated_by_pub_vars(
    c_terms: &[tamarin_theory::guarded_types::GTerm],
    r_terms: &[p::Term],
) -> bool {
    c_terms
        .iter()
        .zip(r_terms.iter())
        .filter(|(c, _)| term_is_free_var(c))
        .all(|(_, r)| is_pub_var(r))
}

/// HS `termIsFreeVar` (Generation.hs:155-160): the term is a single Free
/// variable (a `Bound` variable or non-variable term is not).
fn term_is_free_var(t: &tamarin_theory::guarded_types::GTerm) -> bool {
    matches!(
        t,
        tamarin_theory::guarded_types::GTerm::Var(tamarin_theory::guarded_types::BVar::Free(_))
    )
}

/// HS `isPubVar` (Term/LTerm.hs:328-331, see line 330): a variable of sort `LSortPub` (`$x`).
fn is_pub_var(t: &p::Term) -> bool {
    matches!(t, p::Term::Var(v) if v.sort == LSort::Pub)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A case test carrying a user predicate, so every lemma
    /// `generateAccountabilityLemmas` builds out of it carries the sugar too.
    const SRC: &str = "theory AccPredLemma\n\
begin\n\
predicates:\n  IsBad(a) <=> a = 'bad'\n\
rule L:\n  [ In( <x, a> ) ] --[ Log( x, a ) ]-> [ ]\n\
test badLog:\n  \"Ex #i. Log(x, a)@i & IsBad(a)\"\n\
lemma acc:\n  badLog account for \"All x a #i. Log(x, a)@i ==> not(IsBad(a))\"\n\
end\n";

    /// HS `translate` injects each generated lemma with `liftedAddLemma`
    /// (lib/accountability/src/Accountability.hs:42-49), which
    /// predicate-expands it through `expandLemma`
    /// (Theory/Text/Parser.hs:141-152), so no `Pred` atom reaches the stored
    /// `LNFormula`: `IsBad(a)` is inlined as `a = 'bad'`.
    #[test]
    fn generated_lemmas_are_predicate_expanded_at_injection() {
        let mut parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let mut elaborated =
            tamarin_theory::elaborate::elaborate(&parsed).expect("theory elaborates");
        translate(&mut parsed, &mut elaborated).expect("translation");
        let shown: Vec<String> = elaborated
            .lemmas()
            .map(|l| {
                format!(
                    "{}: {}",
                    l.name,
                    tamarin_theory::pretty_formula::pretty_lnformula(&l.formula)
                )
            })
            .collect();
        assert!(
            shown.len() > 1,
            "the accountability lemma generates lemmas: {shown:?}"
        );
        assert!(
            shown.iter().all(|s| !s.contains("IsBad")),
            "a predicate atom survived injection: {shown:?}"
        );
        assert!(
            shown.iter().any(|s| s.contains("a = 'bad'")),
            "the predicate body is inlined: {shown:?}"
        );
    }

    /// A case test whose formula calls a macro, so every lemma
    /// `generateAccountabilityLemmas` builds carries the call too.
    const MACRO_SRC: &str = "theory AccMacroLemma\n\
begin\n\
macros:\n  tag(x) = <'t', x>\n\
rule L:\n  [ In( <x, a> ) ] --[ Log( tag(x), a ) ]-> [ ]\n\
test badLog:\n  \"Ex #i x. Log(tag(x), a)@i\"\n\
lemma acc:\n  badLog account for \"All a #i x. Log(tag(x), a)@i ==> not(a = 'ok')\"\n\
end\n";

    /// `closeTheory` maps `applyMacroInLemma` over every lemma of the theory,
    /// the injected ones included (CloseRule.hs:85), which stores the
    /// macro-applied formula as `_lFormula` and the formula as injected as
    /// `_lOriginalFormula` (lib/theory/src/Lemma.hs:83-88).  The printer quotes
    /// the original on the header line and converts `_lFormula` for the guarded
    /// block, so the macro call survives in the header and nowhere else.
    #[test]
    fn generated_lemmas_carry_the_macro_applied_formula_beside_the_call() {
        let mut parsed = tamarin_parser::parse_theory(MACRO_SRC, &[]).expect("theory parses");
        let mut elaborated =
            tamarin_theory::elaborate::elaborate(&parsed).expect("theory elaborates");
        translate(&mut parsed, &mut elaborated).expect("translation");
        let shown = |f: &tamarin_theory::formula::LNFormula| {
            tamarin_theory::pretty_formula::pretty_lnformula(f)
        };
        let mut with_call = 0;
        for l in elaborated.lemmas() {
            let formula = shown(&l.formula);
            let original = shown(l.original_formula.as_ref().expect("original formula"));
            if !original.contains("tag(") {
                assert!(
                    !formula.contains("tag("),
                    "a lemma applies a macro its original never called in {}: {formula}",
                    l.name
                );
                continue;
            }
            with_call += 1;
            assert!(
                formula.contains("<'t', x") && !formula.contains("tag("),
                "the macro reached _lFormula unapplied in {}: {formula}",
                l.name
            );
            assert!(
                !original.contains("<'t', x"),
                "_lOriginalFormula lost the macro call in {}: {original}",
                l.name
            );
        }
        assert!(
            with_call > 1,
            "the generated lemmas carry the case test's macro call"
        );
    }
}
