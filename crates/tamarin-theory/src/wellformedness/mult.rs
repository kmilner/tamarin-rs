// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Faithful port of HS `multRestrictedReport` / `multRestrictedReport'`
//! (`lib/theory/src/Theory/Tools/Wellformedness.hs:1039-1099`) — the
//! "Multiplication restriction of rules" wellformedness check.
//!
//! HS runs the check over `thyProtoRules thy` (Wellformedness.hs:133-134):
//! every `RuleItem` of the `OpenTranslatedTheory` with the theory's macros
//! applied — so SAPIC-generated rules are included and macro calls are
//! already expanded.  The elaborated [`Theory`]'s rules are that same set
//! (`apply_sapic` injects the generated rules, `elaborate` expands macros),
//! which is why this check lives beside the elaborated theory rather than on
//! the parser AST.  The second input is the elaborated signature's
//! IRREDUCIBLE function symbols (HS `irreducibleFunSyms $ get (sigpMaudeSig .
//! thySignature) thy`), which classify a term head as reducible.
//!
//! Per rule `ru`, HS computes `restrictedFailures ru = (mults, unbound
//! ruAbstr \\ unbound ru)` and emits an entry unless BOTH are empty:
//!
//!   * `mults` — every outermost `*`-headed sub-term of `ru`'s CONCLUSION
//!     facts (HS `multTerms`, which stops descending at a `Mult` node), taken
//!     from the ORIGINAL rule;
//!   * the unbound difference — the non-public variables that occur in the
//!     conclusions but not in the premises of the ABSTRACTED rule and were
//!     not already unbound in `ru`.  Abstraction (`abstractRule`) replaces
//!     each reducible-headed PREMISE sub-term by a fresh `x.<n>` variable, so
//!     a premise like `In( fst(x) )` stops binding `x` and a conclusion
//!     `Out( x )` becomes rhs-only.
//!
//! The rendered entry is the header-less body of HS's `WfError` Doc, laid out
//! by the HughesPJ engine at the width `addComment` renders the whole
//! wellformedness comment with — HS `addComment c = TextItem ("", render c)`
//! (TheoryObject.hs:717-718) uses `Text.PrettyPrint.Class.render`
//! (Text/PrettyPrint/Class.hs:77-78) = HughesPJ's `render`, i.e. the library DEFAULT style
//! (`lineLength = 100`, `ribbonsPerLine = 1.5` ⇒ `ribbon = 67`), NOT the
//! console's 110/73.  That is why the rule dump here wraps two columns
//! earlier than the same rule in the theory body.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_term::function_symbols::{AcSym, FunSym};
use tamarin_term::lterm::{sort_of_lnterm, HasFrees, LNTerm, LSort, LVar};
use tamarin_term::pretty::pretty_nterm;
use tamarin_term::term::{f_app, Term};
use tamarin_term::vterm::Lit;

use crate::fact::LNFact;
use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{pretty_proto_rule_e, ProtoRuleE};
use crate::theory::Theory;

use super::{WfError, WF_LINE_LENGTH, WF_RIBBON};

/// HS `underlineTopic "Multiplication restriction of rules"`
/// (Wellformedness.hs:1047-1051) — stored bare here because
/// `render_wf_error_report` applies `underline_topic` once per group.
const TOPIC: &str = "Multiplication restriction of rules";

/// Port of HS `multRestrictedReport` (Wellformedness.hs:1110-1113):
/// `multRestrictedReport' (irreducibleFunSyms …) (thyProtoRules thy)`.
///
/// `elab` supplies the rules (HS `thyProtoRules`, i.e. macro-applied E-rules of
/// the translated theory) and its own signature the irreducible-symbol
/// classification (HS `irreducibleFunSyms $ get (sigpMaudeSig . thySignature)
/// thy`, Wellformedness.hs:1113).  Each entry's name and attribute block come
/// from the rule it dumps, the way HS's `prettyNamedRule` reads
/// `prettyRuleName ru <> prettyRuleAttributes ru` off the rule
/// (Theory/Model/Rule.hs:1397-1398).
pub fn mult_restricted_report(elab: &Theory) -> Vec<WfError> {
    let irreducible = &elab.signature.maude_sig.irreducible_fun_syms;
    let mut out = Vec::new();
    for opr in elab.rules() {
        let ru = &opr.rule;
        let abstracted = abstract_rule(ru, irreducible);
        // HS `mults = [ mt | Fact _ _ ts <- get rConcs ru, t <- ts,
        //                    mt <- multTerms t ]` — over the ORIGINAL rule.
        let mults: Vec<LNTerm> = ru
            .conclusions
            .iter()
            .flat_map(|f| f.terms.iter())
            .flat_map(mult_terms)
            .collect();
        // HS `unbound ruAbstr \\ unbound ru`: both operands are `frees`
        // results, i.e. sorted+deduped by `Ord LVar`, so the list difference
        // is a set difference that keeps `ruAbstr`'s order.
        let unbounds: Vec<LVar> = unbound(&abstracted)
            .difference(&unbound(ru))
            .copied()
            .collect();
        // HS `case restrictedFailures ru of ([],[]) -> []; …`
        if mults.is_empty() && unbounds.is_empty() {
            continue;
        }
        out.push(WfError::new(
            TOPIC,
            entry_doc(ru, &abstracted, &mults, &unbounds).render_with(WF_LINE_LENGTH, WF_RIBBON),
        ));
    }
    out
}

// =============================================================================
// HS `multTerms` / `unbound`
// =============================================================================

/// HS `multTerms` (Wellformedness.hs:1094-1096):
/// ```text
/// multTerms t@(viewTerm -> FApp (AC Mult) _)  = [t]
/// multTerms   (viewTerm -> FApp _         as) = concatMap multTerms as
/// multTerms _                                 = []
/// ```
/// A `*` node terminates the descent, so nested products inside one are not
/// reported separately.
fn mult_terms(t: &LNTerm) -> Vec<LNTerm> {
    match t {
        Term::App(FunSym::Ac(AcSym::Mult), _) => vec![t.clone()],
        Term::App(_, args) => args.iter().flat_map(mult_terms).collect(),
        Term::Lit(_) => Vec::new(),
    }
}

/// HS `unbound ru = [v | v <- frees (get rConcs ru) \\ frees (get rPrems ru),
/// lvarSort v /= LSortPub]` (Wellformedness.hs:1098-1099).  `frees` is
/// `sortednub . freesList` (Term/LTerm.hs:613-614), which a `BTreeSet` ordered by
/// `Ord LVar` reproduces exactly.
fn unbound(ru: &ProtoRuleE) -> BTreeSet<LVar> {
    let concs = fact_frees(&ru.conclusions);
    let prems = fact_frees(&ru.premises);
    concs
        .difference(&prems)
        .copied()
        .filter(|v| v.sort != LSort::Pub)
        .collect()
}

fn fact_frees(facts: &[LNFact]) -> BTreeSet<LVar> {
    let mut out = BTreeSet::new();
    for f in facts {
        for t in f.terms.iter() {
            t.for_each_free(&mut |v| {
                out.insert(*v);
            });
        }
    }
    out
}

// =============================================================================
// HS `abstractRule`
// =============================================================================

/// HS `abstractRule` (Wellformedness.hs:1066-1071), run in
/// ``(`evalFreshAvoiding` ru) . (`evalBindT` noBindings)``:
///
/// ```text
/// abstractRule ru@(Rule i lhs acts rhs nvs) = …
///     Rule i <$> mapM (traverse abstractTerm)      lhs
///            <*> mapM (traverse replaceAbstracted) acts
///            <*> mapM (traverse replaceAbstracted) rhs
///            <*> (traverse replaceAbstracted)      nvs
/// ```
///
/// HS's binders there are misnamed: `Rule`'s field order is `i ps cs as nvs`
/// (Theory/Model/Rule.hs:218-225), so `lhs` is the premises, `acts` the
/// CONCLUSIONS and `rhs` the ACTIONS.  The effect is that only the PREMISES
/// create bindings; conclusions, actions and new variables merely substitute
/// the ones the premises registered.
fn abstract_rule(ru: &ProtoRuleE, irreducible: &BTreeSet<FunSym>) -> ProtoRuleE {
    // HS `evalFreshAvoiding … ru` starts the (single, name-agnostic) `Fresh`
    // counter at `avoid ru = maybe 0 (succ . snd) (boundsVarIdx ru)`
    // (Term/LTerm.hs:680-686) — one past the largest variable index in the rule,
    // or 0 when the rule has no variables at all.
    let mut next_idx = avoid(ru);
    // HS `BindT` state: `M.Map LNTerm LVar`, so one binding per distinct
    // abstracted term, reused on every later occurrence.
    let mut bindings: BTreeMap<LNTerm, LVar> = BTreeMap::new();

    let mut premises = Vec::with_capacity(ru.premises.len());
    for f in &ru.premises {
        let terms = f
            .terms
            .iter()
            .map(|t| abstract_term(t, irreducible, &mut bindings, &mut next_idx))
            .collect();
        premises.push(LNFact::fresh_annotated(f.tag, f.annotations.clone(), terms));
    }
    let replace_facts = |facts: &[LNFact], bindings: &BTreeMap<LNTerm, LVar>| -> Vec<LNFact> {
        facts
            .iter()
            .map(|f| {
                let terms = f
                    .terms
                    .iter()
                    .map(|t| replace_abstracted(t, bindings))
                    .collect();
                LNFact::fresh_annotated(f.tag, f.annotations.clone(), terms)
            })
            .collect()
    };
    let conclusions = replace_facts(&ru.conclusions, &bindings);
    let actions = replace_facts(&ru.actions, &bindings);
    let new_vars = ru
        .new_vars
        .iter()
        .map(|t| replace_abstracted(t, &bindings))
        .collect();
    ProtoRuleE {
        info: ru.info.clone(),
        premises,
        conclusions,
        actions,
        new_vars,
    }
}

/// HS `avoid` (Term/LTerm.hs:680-681) over a rule's `frees`: `succ` of the largest
/// variable index, `0` for a variable-free rule.  The rule's info contributes
/// no variables (`HasFrees RuleAttributes` folds to `mempty`,
/// Theory/Model/Rule.hs:462-465, and RS lifts `_restrict` formulas out of the
/// rule before elaboration), so premises, conclusions, actions and new
/// variables are the whole domain.
fn avoid(ru: &ProtoRuleE) -> u64 {
    let mut max_idx: Option<u64> = None;
    let mut visit = |v: &LVar| {
        max_idx = Some(max_idx.map_or(v.idx, |m: u64| m.max(v.idx)));
    };
    for facts in [&ru.premises, &ru.conclusions, &ru.actions] {
        for f in facts {
            for t in f.terms.iter() {
                t.for_each_free(&mut visit);
            }
        }
    }
    for t in &ru.new_vars {
        t.for_each_free(&mut visit);
    }
    max_idx.map_or(0, |m| m + 1)
}

/// HS `abstractTerm` (Wellformedness.hs:1073-1076):
/// ```text
/// abstractTerm (viewTerm -> FApp o args) | o `S.member` irreducible =
///     fApp o <$> mapM abstractTerm args
/// abstractTerm (viewTerm -> Lit l) = return $ lit l
/// abstractTerm t = varTerm <$> importBinding (`LVar` sortOfLNTerm t) t "x"
/// ```
/// The catch-all covers exactly the reducible-headed applications: each is
/// replaced by a fresh `x.<n>` of the term's own sort, memoised so equal
/// terms share one variable (HS `importBinding`, Control/Monad/Bind.hs:125-140).
fn abstract_term(
    t: &LNTerm,
    irreducible: &BTreeSet<FunSym>,
    bindings: &mut BTreeMap<LNTerm, LVar>,
    next_idx: &mut u64,
) -> LNTerm {
    match t {
        Term::App(f, args) if irreducible.contains(f) => {
            let mapped = args
                .iter()
                .map(|a| abstract_term(a, irreducible, bindings, next_idx))
                .collect();
            f_app(*f, mapped)
        }
        Term::Lit(_) => t.clone(),
        Term::App(..) => {
            if let Some(v) = bindings.get(t) {
                return Term::Lit(Lit::Var(*v));
            }
            let v = LVar::new("x", sort_of_lnterm(t), *next_idx);
            *next_idx += 1;
            bindings.insert(t.clone(), v);
            Term::Lit(Lit::Var(v))
        }
    }
}

/// HS `replaceAbstracted` (Wellformedness.hs:1078-1086): substitute a term
/// the premises already abstracted, otherwise rebuild it structurally.  The
/// binding lookup happens FIRST, before the head symbol is inspected.
fn replace_abstracted(t: &LNTerm, bindings: &BTreeMap<LNTerm, LVar>) -> LNTerm {
    if let Some(v) = bindings.get(t) {
        return Term::Lit(Lit::Var(*v));
    }
    match t {
        Term::App(f, args) => {
            let mapped = args
                .iter()
                .map(|a| replace_abstracted(a, bindings))
                .collect();
            f_app(*f, mapped)
        }
        Term::Lit(_) => t.clone(),
    }
}

// =============================================================================
// Rendering
// =============================================================================

/// The per-rule body of HS's `WfError` (Wellformedness.hs:1053-1064):
/// ```text
/// text "The following rule is not multiplication restricted:"
///   $-$ nest 2 (prettyProtoRuleE ru)
///   $-$ text ""
///   $-$ text "After replacing reducible function symbols in lhs with variables:"
///   $-$ nest 2 (prettyProtoRuleE (abstractRule ru))
///   $-$ text ""
///   $-$ [nest 2 (text "Terms with multiplication: " <-> prettyLNTermList mults)]
///   $-$ [nest 2 (text "Variables that occur only in rhs: " <-> prettyVarList unbounds)]
/// ```
/// The two trailing lines are `mempty` when their list is empty, and HS's
/// `above_ p _ Empty = p` then drops them without a line of their own.
/// `.nest(2)` at the end is `prettyWfErrorReport`'s per-group `nest 2`
/// (Wellformedness.hs:118-125), baked in here so the HughesPJ width decisions
/// are made at the body's true column.
fn entry_doc(ru: &ProtoRuleE, abstracted: &ProtoRuleE, mults: &[LNTerm], unbounds: &[LVar]) -> Doc {
    // `above_g` is HughesPJ's `$+$` — the NON-overlapping vertical join HS's
    // `$-$` maps to (Text/PrettyPrint/Class.hs:180).  The overlapping `$$` would splice
    // `text "" $$ nest 2 x` onto one line and swallow the blank separators.
    let mut d = Doc::text("The following rule is not multiplication restricted:")
        .above_g(pretty_proto_rule_e(ru).nest(2))
        .above_g(Doc::text_hs(""))
        .above_g(Doc::text(
            "After replacing reducible function symbols in lhs with variables:",
        ))
        .above_g(pretty_proto_rule_e(abstracted).nest(2))
        .above_g(Doc::text_hs(""));
    if !mults.is_empty() {
        // HS `prettyLNTermList = fsep . punctuate comma . map prettyLNTerm`
        // (Wellformedness.hs:146-147).  `<->` is one space, and the text
        // already ends in one — hence the doubled space before the list.
        let list = hpj::fsep(hpj::punctuate(
            Doc::text(","),
            mults.iter().map(pretty_nterm).collect(),
        ));
        d = d.above_g(
            Doc::text("Terms with multiplication: ")
                .beside_sp(list)
                .nest(2),
        );
    }
    if !unbounds.is_empty() {
        // HS `prettyVarList = fsep . punctuate comma . map prettyLVar`
        // (TheoryObject.hs:858-859), and `prettyLVar = text . show`
        // (LTerm.hs:922-923).
        let list = hpj::fsep(hpj::punctuate(
            Doc::text(","),
            unbounds.iter().map(|v| Doc::text(v.to_string())).collect(),
        ));
        d = d.above_g(
            Doc::text("Variables that occur only in rhs: ")
                .beside_sp(list)
                .nest(2),
        );
    }
    d.nest(2)
}
