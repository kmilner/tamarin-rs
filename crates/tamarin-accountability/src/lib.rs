// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Accountability translation for the Tamarin prover (Rust port).
//!
//! Port of `Accountability` + `Accountability.Generation`
//! (lib/accountability/src/Accountability{,/Generation}.hs).  `translate`
//! expands each `lemma <name> [..]: c1, .. accounts for "φ"` into the seven
//! verification-condition lemmas (per `test <c>` case test) and the case-test
//! predicates, appending them to the theory.  `check_wellformedness` produces
//! the "Accountability (RP check)" report.
//!
//! The driver (`tamarin-prover`) calls `translate` right after the SAPIC stage
//! (case-test formulas may reference user function symbols, whose thread-local
//! flags must be installed) and prepends `check_wellformedness`'s report after
//! the SAPIC warnings.

mod formula;
mod generation;

use tamarin_term::lterm::{is_pub_const, is_pub_var, BVar, LNTerm};
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;
use tamarin_theory::pretty_hpj::{self as hpj, Doc};
use tamarin_theory::wellformedness::WfError;

use tamarin_theory::fact::{Fact, LNFact};
use tamarin_theory::formula::{formula_facts, formula_frees, to_lnformula, BLNTerm, LNFormula};
use tamarin_theory::predicate::{builtin_predicates, expand_formula, ExpandError, Predicate};
use tamarin_theory::pretty_theory::render_predicate_fact;
use tamarin_theory::rule::ProtoRuleE;
use tamarin_theory::theory::{
    self as t, AccLemma, CaseTest, LNMacro, Theory, TheoryItem, TranslationElement,
};

use crate::generation::{generate_accountability_lemmas, AccData, CaseTestData};

/// Accountability translation error: HS `AccException`
/// (lib/accountability/src/Accountability.hs) plus the
/// `ParsingException`s HS `translate` can throw through `liftedAddLemma` /
/// `liftedAddPredicate` (Parser/Exceptions.hs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccError {
    /// HS `CaseTestsUndefined`: one or more case tests required by an
    /// accountability lemma are not defined.  Each entry is
    /// `(lemma name, missing case-test identifiers)`.
    CaseTestsUndefined(Vec<(String, Vec<String>)>),
    /// HS `UndefinedPredicate` (thrown by `liftedAddLemma`'s `expandLemma`,
    /// Text/Parser.hs, when a generated lemma's formula references an
    /// undefined predicate).
    UndefinedPredicate(ExpandError),
    /// HS `DuplicateItem (LemmaItem _)` (thrown by `liftedAddLemma` when a
    /// generated lemma's name collides with an existing lemma).
    DuplicateLemma(String),
    /// HS `DuplicateItem (PredicateItem _)` (thrown by `liftedAddPredicate`,
    /// Parser/Signature.hs, when a case-test predicate's fact tag
    /// collides with an existing predicate).  Carries the fact as HS
    /// `render (prettyFact prettyLVar fact)` prints it (Exceptions.hs).
    DuplicatePredicate(String),
    /// GHC's `errorEmptyList` from one of `Accountability.Generation`'s
    /// partial folds (`foldr1`/`foldl1`), which a case test without free
    /// variables reaches: HS dies with `Prelude.<fold>: empty list`.
    EmptyList(&'static str),
}

impl std::fmt::Display for AccError {
    /// Mirrors HS `show` of the corresponding exception
    /// (lib/accountability/src/Accountability.hs /
    /// Parser/Exceptions.hs); the driver prefixes `tamarin-prover: ` as
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
            AccError::UndefinedPredicate(e) => write!(f, "{e}"),
            AccError::DuplicateLemma(name) => write!(f, "duplicate lemma: {}", name),
            AccError::DuplicatePredicate(fact) => write!(f, "duplicate predicate: {}", fact),
            AccError::EmptyList(fold) => write!(f, "Prelude.{fold}: empty list"),
        }
    }
}

// =============================================================================
// Reading the accountability items from the theory
// =============================================================================

/// The case-test formulas of the theory, in declaration order (HS
/// `theoryCaseTests`).
fn theory_case_tests(thy: &Theory) -> impl Iterator<Item = &CaseTest> {
    thy.items.iter().filter_map(|i| match i {
        TheoryItem::Translation(TranslationElement::CaseTest(c)) => Some(c),
        _ => None,
    })
}

/// The theory's case tests (declaration order) and accountability lemmas.
/// Each acc lemma is paired with the number of case tests declared BEFORE it:
/// HS binds `_aCaseTests` when the lemma is parsed (`mapMaybe (flip
/// lookupCaseTest thy)` over the items parsed so far, Text/Parser.hs), so a
/// case test declared after the lemma is undefined for it.
fn collect_acc_items(thy: &Theory) -> (Vec<CaseTest>, Vec<(AccLemma, usize)>) {
    let mut case_tests: Vec<CaseTest> = Vec::new();
    let mut acc_lemmas: Vec<(AccLemma, usize)> = Vec::new();
    for i in &thy.items {
        match i {
            TheoryItem::Translation(TranslationElement::CaseTest(c)) => case_tests.push(c.clone()),
            TheoryItem::Translation(TranslationElement::AccLemma(a)) => {
                acc_lemmas.push((a.clone(), case_tests.len()))
            }
            _ => {}
        }
    }
    (case_tests, acc_lemmas)
}

/// HS `undefinedCaseTests` (lib/accountability/src/Accountability.hs):
/// `required \\ defined`, where `defined` keeps the required idents that name
/// a case test declared before the lemma. That difference is just the
/// required idents naming no such case test, in order and with repeats.
fn undefined_case_tests(acc: &AccLemma, declared: &[CaseTest]) -> Option<Vec<String>> {
    let missing: Vec<String> = acc
        .case_test_idents
        .iter()
        .filter(|id| !declared.iter().any(|c| &c.name == *id))
        .cloned()
        .collect();
    (!missing.is_empty()).then_some(missing)
}

// =============================================================================
// translate
// =============================================================================

/// Expand the accountability lemmas + case-test predicates into `thy` (HS
/// `Accountability.translate`,
/// lib/accountability/src/Accountability.hs).  A no-op when the theory
/// declares neither accountability lemmas nor case tests, so ordinary
/// theories are byte-unchanged.  Case tests WITHOUT any
/// acc lemma still get their predicates appended (HS `translate` runs its
/// `caseTestToPredicate` fold unconditionally).
pub fn translate(thy: &mut Theory) -> Result<(), AccError> {
    let (case_tests, acc_lemmas) = collect_acc_items(thy);
    if acc_lemmas.is_empty() && case_tests.is_empty() {
        return Ok(());
    }

    // HS: `unless (null undef) (throwM (CaseTestsUndefined undef))`.  Each
    // lemma only sees the case tests declared before it (`n_before`).
    let undef: Vec<(String, Vec<String>)> = acc_lemmas
        .iter()
        .filter_map(|(a, n_before)| {
            undefined_case_tests(a, &case_tests[..*n_before]).map(|m| (a.name.clone(), m))
        })
        .collect();
    if !undef.is_empty() {
        return Err(AccError::CaseTestsUndefined(undef));
    }

    // The predicate DEFINITIONS `expandLemma` substitutes into each generated
    // lemma, in declaration order.  The case-test predicates are appended
    // after the lemma loop, so — as in HS, where `liftedAddLemma` expands
    // against `theoryPredicates thy` at the point of the add — they are not
    // among them.
    let declared_preds: Vec<Predicate> = thy.predicates().cloned().collect();

    // The macro DEFINITIONS `applyMacroInLemma` substitutes into each generated
    // lemma at close time (CloseRule.hs), in declaration order.
    let declared_macros: Vec<LNMacro> = thy.macros().cloned().collect();

    // Existing lemma names (HS `addLemma` guards on `lookupLemma`, which scans
    // `LemmaItem`s only — TheoryObject.hs); grows as generated lemmas
    // are appended.
    let mut lemma_names: Vec<String> = thy.lemmas().map(|l| l.name.clone()).collect();

    // Generate + inject the lemmas, in theory order (HS
    // `foldM liftedAddLemma thy (concat accLemmas)`).
    for (acc, n_before) in &acc_lemmas {
        let scope = &case_tests[..*n_before];
        let acc_data = AccData {
            name: acc.name.clone(),
            formula: acc.formula.clone(),
            case_tests: acc
                .case_test_idents
                .iter()
                .filter_map(|id| {
                    scope.iter().find(|c| &c.name == id).map(|c| CaseTestData {
                        name: id.clone(),
                        formula: c.formula.clone(),
                    })
                })
                .collect(),
        };
        for generated in generate_accountability_lemmas(&acc_data)? {
            // HS `liftedAddLemma` first predicate-expands the lemma
            // (`expandLemma`, throws `UndefinedPredicate`), then rejects
            // duplicate names (`DuplicateItem`).
            let original = expand_formula(&declared_preds, &generated.formula)
                .map_err(AccError::UndefinedPredicate)?;
            if lemma_names.iter().any(|n| n == &generated.name) {
                return Err(AccError::DuplicateLemma(generated.name));
            }
            lemma_names.push(generated.name.clone());
            inject_lemma(
                thy,
                &declared_macros,
                &acc.attributes,
                acc.heuristic_in_file.as_deref(),
                &generated.name,
                generated.quantifier,
                original,
            );
        }
    }

    // Case-test predicates (HS `mapMaybe caseTestToPredicate (theoryCaseTests thy)`
    // then `foldM liftedAddPredicate`), appended AFTER all generated lemmas.
    // `addPredicate` rejects a fact tag `lookupPredicate` already finds: a
    // declared predicate, the builtin `Smaller` or an earlier case test,
    // comparing the whole fact tag (Predicate.hs).
    let mut defined_preds: std::collections::BTreeSet<_> = thy
        .predicates()
        .chain(&builtin_predicates())
        .map(|pr| pr.fact.tag)
        .collect();
    for c in &case_tests {
        if let Some(pred) = case_test_to_predicate(c) {
            if !defined_preds.insert(pred.fact.tag) {
                return Err(AccError::DuplicatePredicate(render_predicate_fact(
                    &pred.fact,
                )));
            }
            thy.items.push(TheoryItem::Predicate(pred));
        }
    }

    Ok(())
}

/// Append one generated lemma to the theory (HS `addLemma`, which appends at
/// the end of the item list, TheoryObject.hs).  The lemma carries the
/// two formulas a closed theory's lemma holds: `_lOriginalFormula` is the
/// predicate-expanded one `expandLemma` builds (Theory/Text/Parser.hs), and
/// `_lFormula` is that formula with the theory's macros applied, which
/// `closeTheory` maps over every lemma including the ones this translation
/// added (`applyMacroInLemma`, CloseRule.hs, lib/theory/src/Lemma.hs).
fn inject_lemma(
    thy: &mut Theory,
    macros: &[LNMacro],
    attributes: &[t::LemmaAttr],
    heuristic_in_file: Option<&str>,
    name: &str,
    quantifier: t::TraceQuantifier,
    original: LNFormula,
) {
    let expanded = tamarin_theory::formula::apply_macro_in_formula(macros, original.clone());
    let lemma = t::Lemma {
        heuristic_in_file: heuristic_in_file.map(str::to_owned),
        name: name.to_string(),
        attributes: attributes.to_vec(),
        trace_quantifier: quantifier,
        original_formula: Some(original),
        formula: expanded,
        proof: None,
        // HS `skeletonLemma name "generation" ..` seeds `_lPlaintext` with
        // "generation" (ProofSkeleton.hs); never rendered by `--prove`.
        plaintext: "generation".to_string(),
    };
    thy.items.push(TheoryItem::Lemma(lemma));
}

// =============================================================================
// caseTestToPredicate (Items/CaseTestItem.hs + mkPredicate,
// Theory/Syntactic/Predicate.hs)
// =============================================================================

/// HS `caseTestToPredicate` (Items/CaseTestItem.hs): `None` when the
/// case-test formula has syntactic sugar that `toLNFormula` cannot strip (a
/// predicate atom), otherwise `mkPredicate name formula`
/// (Theory/Syntactic/Predicate.hs).
fn case_test_to_predicate(c: &CaseTest) -> Option<Predicate> {
    // `toLNFormula` is `Nothing` while any atom still carries the predicate
    // sugar (Theory/Model/Formula.hs).
    let stripped = to_lnformula(&c.formula)?;
    // The fact args are the formula's sorted free variables.
    let frees = formula_frees(&stripped);
    Some(Predicate::new(&c.name, stripped, frees))
}

// =============================================================================
// checkWellformedness / accRPReport (Generation.hs)
// =============================================================================

/// HS `Accountability.checkWellformedness` (Generation.hs): the RP-check
/// report, emitted only when the theory declares accountability lemmas.
pub fn check_wellformedness(thy: &Theory) -> Vec<WfError> {
    let has_acc_lemma = thy
        .items
        .iter()
        .any(|i| matches!(i, TheoryItem::Translation(TranslationElement::AccLemma(_))));
    if !has_acc_lemma {
        return Vec::new();
    }
    acc_rp_report(thy)
}

/// HS `accRPReport` (Generation.hs): the topic + explanation for the
/// RP (BR) syntactic criterion.  Empty when no warning fires.
fn acc_rp_report(thy: &Theory) -> Vec<WfError> {
    let rules = rp_check_rules(thy);
    let mut warnings: Vec<String> = Vec::new();
    if theory_has_restrictions(thy) {
        warnings.push("The specification contains at least one restriction.".to_string());
    }
    if rules_contain_pub_const(&rules) {
        warnings.push("The specification contains public names.".to_string());
    }
    if !case_tests_instantiated_by_pub_vars(thy, &rules) {
        warnings
            .push("At least one case test can be instantiated with non-public names.".to_string());
    }
    if warnings.is_empty() {
        return Vec::new();
    }

    // HS `vcat warnings $--$ detailedExplanation` (Generation.hs), framed
    // by `prettyWfErrorReport` as `text topic $-$ nest 2 body`
    // (Wellformedness.hs).
    let body = hpj::above_blank(
        hpj::vcat(warnings.into_iter().map(Doc::text).collect()),
        detailed_explanation(),
    );
    vec![WfError::block(ACC_RP_TOPIC, body)]
}

const ACC_RP_TOPIC: &str = "Accountability (RP check)";

/// HS `detailedExplanation` (Generation.hs): the first line, then a
/// `$--$` blank line, then the five `$-$`-joined lines of the condition.
/// Right single quotation marks (U+2019) are copied verbatim.
fn detailed_explanation() -> Doc {
    hpj::above_blank(
        Doc::text("Please verify manually that your protocol fulfills the following condition:"),
        hpj::vcat(
            [
                "For each case test \u{03c4}, traces t, t\u{2019}, and instantiations \u{03c1}, \u{03c1}\u{2019}:",
                "If \u{03c4} holds on t with \u{03c1}, and \u{03c4} single-matches with \u{03c1}\u{2019} on t\u{2019}, then",
                "there exists a trace t\u{2019}\u{2019} such that \u{03c4} single-matches with \u{03c1} on t\u{2019}\u{2019}",
                "and the parties corrupted in t\u{2019}\u{2019} are the same as the parties",
                "corrupted in t\u{2019} renamed from rng(\u{03c1}\u{2019}) to rng(\u{03c1}).",
            ]
            .into_iter()
            .map(Doc::text)
            .collect(),
        ),
    )
}

/// HS `not $ null $ theoryRestrictions thy`.
fn theory_has_restrictions(thy: &Theory) -> bool {
    thy.restrictions().next().is_some()
}

/// The rules HS's RP check scans: each rule's E-form plus its explicit AC
/// variants (HS `rulesLNFacts` / `rulesActions` read `_oprRuleE` and
/// `_oprRuleAC`, Generation.hs).  Macros stay UNexpanded: `rule_e()`
/// is the half `closeProtoRule` keeps unexpanded (lib/theory/src/Rule.hs),
/// and a declared `variants (modulo AC)` block is never macro-applied at all.
fn rp_check_rules(thy: &Theory) -> Vec<&ProtoRuleE> {
    let mut out = Vec::new();
    for r in thy.rules() {
        out.push(r.rule_e());
        out.extend(r.rule_ac.iter());
    }
    out
}

/// HS `rulesContainPubConst thy = any termContainsPubConst (rulesLNTerms thy)`
/// (Generation.hs): any premise/action/conclusion term of any rule is
/// or contains a public constant.
fn rules_contain_pub_const(rules: &[&ProtoRuleE]) -> bool {
    rules.iter().any(|r| {
        r.premises
            .iter()
            .chain(&r.actions)
            .chain(&r.conclusions)
            .flat_map(|fa| fa.terms().iter())
            .any(term_contains_pub_const)
    })
}

/// HS `termContainsPubConst` (Generation.hs): a public constant literal
/// (`'x'`) anywhere in the term.
fn term_contains_pub_const(t: &LNTerm) -> bool {
    match t {
        Term::Lit(_) => is_pub_const(t),
        Term::App(_, args) => args.iter().any(term_contains_pub_const),
    }
}

/// HS `caseTestsInstantiatedByPubVars` (Generation.hs): for every
/// case-test action fact and every rule action fact sharing its tag, each free
/// variable of the case-test fact must line up with a public variable in the
/// rule fact.
fn case_tests_instantiated_by_pub_vars(thy: &Theory, rules: &[&ProtoRuleE]) -> bool {
    let ct_facts = case_tests_facts(thy);
    let rule_facts = rules_actions(rules);
    for cf in &ct_facts {
        for rf in &rule_facts {
            if fact_tag_eq(cf, rf) && !free_vars_instantiated_by_pub_vars(cf.terms(), rf.terms()) {
                return false;
            }
        }
    }
    true
}

/// HS `caseTestsFacts thy` (Generation.hs): the action facts of every
/// case test's formula.  HS `formulaActionFacts` is [`formula_facts`].
fn case_tests_facts(thy: &Theory) -> Vec<&Fact<BLNTerm>> {
    theory_case_tests(thy)
        .flat_map(|c| formula_facts(&c.formula))
        .collect()
}

/// HS `rulesActions thy` (Generation.hs): every rule's action facts.
fn rules_actions<'a>(rules: &[&'a ProtoRuleE]) -> Vec<&'a LNFact> {
    rules.iter().flat_map(|r| r.actions.iter()).collect()
}

/// HS `cTag == rTag` (Generation.hs).
fn fact_tag_eq(cf: &Fact<BLNTerm>, rf: &LNFact) -> bool {
    cf.tag == rf.tag
}

/// HS `freeVarsInstantiatedByPubVars` (Generation.hs): at each position
/// where the case-test fact holds a free variable, the rule fact must hold a
/// public variable.
fn free_vars_instantiated_by_pub_vars(c_terms: &[BLNTerm], r_terms: &[LNTerm]) -> bool {
    c_terms
        .iter()
        .zip(r_terms.iter())
        .filter(|(c, _)| term_is_free_var(c))
        .all(|(_, r)| is_pub_var(r))
}

/// HS `termIsFreeVar` (Generation.hs): the term is a single Free
/// variable (a `Bound` variable or non-variable term is not).
fn term_is_free_var(t: &BLNTerm) -> bool {
    matches!(t, Term::Lit(Lit::Var(BVar::Free(_))))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn included_accountability_heuristic_keeps_its_oracle_origin() {
        let root =
            std::env::temp_dir().join(format!("tamarin_rs_acc_oracle_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("sub")).unwrap();
        let theory_file = root.join("root.spthy");
        let include_file = root.join("sub/inc.spthy");
        std::fs::write(
            &theory_file,
            "theory T begin\n#include \"sub/inc.spthy\"\nend\n",
        )
        .unwrap();
        std::fs::write(
            &include_file,
            "rule L: [ In(<x,a>) ] --[ Log(x,a) ]-> []\n\
             test badLog: \"Ex #i. Log(x,a)@i\"\n\
             lemma acc [heuristic=o, heuristic=o]:\n\
               badLog account for \"All x a #i. Log(x,a)@i ==> not(a = 'ok')\"\n",
        )
        .unwrap();
        std::fs::write(root.join("sub/inc.oracle"), "").unwrap();

        let source = std::fs::read_to_string(&theory_file).unwrap();
        let parsed = tamarin_parser::parse_theory_with_base(&source, &[], Some(root.clone()))
            .expect("theory parses");
        let mut elaborated = tamarin_theory::elaborate::elaborate_with_in_file(
            &parsed,
            theory_file.to_str().unwrap(),
        )
        .expect("theory elaborates");
        translate(&mut elaborated).expect("translation");

        let generated: Vec<_> = elaborated.lemmas().collect();
        assert!(!generated.is_empty());
        for lemma in generated {
            assert_eq!(lemma.heuristic_in_file.as_deref(), include_file.to_str());
            assert_eq!(
                lemma
                    .attributes
                    .iter()
                    .filter_map(|attribute| match attribute {
                        t::LemmaAttr::Heuristic(raw) => Some(raw.as_str()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
                ["o \"inc.oracle\"", "o \"inc.oracle\""]
            );
        }
        std::fs::remove_dir_all(root).unwrap();
    }
}
