// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parser-AST level macro expansion.
//!
//! Port of `Term.Macro.applyMacros` (HS: lib/term/src/Term/Macro.hs:40-54)
//! plus the call-sites that drive it:
//!
//!   - `applyMacroInRule`     — lib/theory/src/Theory/Model/Rule.hs:1115-1121
//!   - `applyMacroInFact`     — lib/theory/src/Theory/Model/Fact.hs:323-326
//!   - `applyMacroInFormula`  — lib/theory/src/Theory/Model/Formula.hs:314-316
//!   - `applyMacroInLemma`    — lib/theory/src/Lemma.hs:83-88
//!   - `applyMacroInRestriction` — lib/theory/src/Theory/Model/Restriction.hs:164-166
//!   - `closeProtoRule` calls applyMacroInRule BEFORE variantsProtoRule
//!     — lib/theory/src/Rule.hs:82-87
//!   - `parseLemmaWithMacros`  — lib/theory/src/Theory/Text/Parser.hs:97-105
//!
//! HS works at the typed `LNTerm` / `LNFact` / `LNFormula` level, with
//! macro matching keyed on the `FunSym` (a `NoEq (name, (arity, Private,
//! Destructor, NotNDC))` tuple — Term/Macro.hs:29-30, see line 30).  RS parses lemma/restriction
//! formulas as `parser::ast::Formula` and only converts to `LNFormula`
//! later (via `formula_to_guarded`), so the natural place to expand is
//! the parser AST.  This is observationally faithful: every macro call
//! site is rewritten to its body before either side's typed conversion
//! runs.  The macro fun-syms themselves are still registered in MaudeSig
//! (HS Theory/Text/Parser/Macro.hs:29-47, see line 46 `addMacroSym`) so any unexpanded
//! reference — and Maude — still see them.
//!
//! Recursion semantics mirror HS exactly:
//!   - args are recursively expanded FIRST (Term/Macro.hs:40-54, see line 46),
//!   - then substitution into the body,
//!   - then the EXPANDED body is recursively re-expanded
//!     (Term/Macro.hs:40-54, see line 48 `applyMacros macros (apply subst mout)`).
//!
//! This handles chained / nested macros (e.g. `hashdec` calling `decrypt`
//! in `examples/features/macros/MacroExample.spthy`).

use std::collections::BTreeMap;

use tamarin_parser::ast as p;

/// Apply all macros to a term, recursing into args first and re-expanding
/// the body after substitution.  Mirrors HS `applyMacros` exactly
/// (Term/Macro.hs:40-50).
pub fn apply_macros_term(macros: &[p::Macro], term: &p::Term) -> p::Term {
    match term {
        p::Term::App(name, args) => {
            // Recurse on args first (HS `processedArgs = map (applyMacros macros) args`).
            let processed_args: Vec<p::Term> =
                args.iter().map(|a| apply_macros_term(macros, a)).collect();
            // Match on (name, arity) — HS matches on FunSym which includes
            // arity (Term/Macro.hs:29-30, see line 30 `macroToFunSym (op,args,_) = NoEq (op,
            // (length args, Private, Destructor, NotNDC))` ; matching macros are
            // found via Term/Macro.hs:53-54 `find (\m -> macroToFunSym m == f)`).
            if let Some(m) = find_matching_macro(name, processed_args.len(), macros) {
                // Build the param→arg substitution (by name).
                let mut subst: BTreeMap<String, p::Term> = BTreeMap::new();
                for (param, value) in m.args.iter().zip(processed_args.iter()) {
                    subst.insert(param.name.clone(), value.clone());
                }
                let expanded = subst_term_by_name(&m.body, &subst);
                // Re-expand the EXPANDED body to handle nested macros.
                apply_macros_term(macros, &expanded)
            } else {
                p::Term::App(name.clone(), processed_args)
            }
        }
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::Pair(items) => {
            p::Term::Pair(items.iter().map(|t| apply_macros_term(macros, t)).collect())
        }
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(apply_macros_term(macros, inner))),
        // Literals: no recursion (HS Term/Macro.hs:40-54, see line 51 `Lit l -> lit l`).
        p::Term::Var(_)
        | p::Term::PubLit(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => term.clone(),
    }
}

/// HS `findMatchingMacro f macros = find (\m -> macroToFunSym m == f)`
/// (Term/Macro.hs:53-54).  At parser-AST level a call-site has no FunSym
/// flags so we match by (name, arity) — equivalent for non-clashing
/// macro names since the `macros` parser rejects a name already in the
/// signature (Theory/Text/Parser/Macro.hs:43-44 `fail $ "Conflicting name
/// for macro " ...`) and built-in fun-syms have known fixed arity.
fn find_matching_macro<'a>(
    name: &str,
    arity: usize,
    macros: &'a [p::Macro],
) -> Option<&'a p::Macro> {
    macros
        .iter()
        .find(|m| m.name == name && m.args.len() == arity)
}

/// Apply a name-keyed substitution to a parser term.  HS's typed
/// `apply subst term` (Term/Macro.hs:40-54, see line 48) becomes a structural name-keyed walk.
/// Shared with `predicate_expand` (whose `Subst` newtype wraps the same
/// `BTreeMap<String, p::Term>`), so both stay in lockstep on capture /
/// replacement semantics.
pub(crate) fn subst_term_by_name(t: &p::Term, subst: &BTreeMap<String, p::Term>) -> p::Term {
    match t {
        p::Term::Var(v) => match subst.get(&v.name) {
            Some(replacement) => replacement.clone(),
            None => t.clone(),
        },
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| subst_term_by_name(a, subst)).collect(),
        ),
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(subst_term_by_name(a, subst)),
            Box::new(subst_term_by_name(b, subst)),
        ),
        p::Term::Pair(items) => {
            p::Term::Pair(items.iter().map(|a| subst_term_by_name(a, subst)).collect())
        }
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(subst_term_by_name(a, subst)),
            Box::new(subst_term_by_name(b, subst)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(subst_term_by_name(a, subst)),
            Box::new(subst_term_by_name(b, subst)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(subst_term_by_name(inner, subst))),
        other => other.clone(),
    }
}

/// Shared structural walker: rebuild a fact, mapping `g` over every arg.
/// The single traversal shape behind `apply_macros_fact`,
/// `elaborate::canonicalize_ac_in_pfact`, and `elaborate::rewrite_arity1_fact`
/// (each supplies its own leaf `&Term -> Term`).
pub(crate) fn map_fact_terms(f: &p::Fact, g: &dyn Fn(&p::Term) -> p::Term) -> p::Fact {
    p::Fact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(g).collect(),
        annotations: f.annotations.clone(),
    }
}

/// Shared structural walker: rebuild an atom, mapping `g` over every term and
/// `map_fact_terms` over embedded facts.  See [`map_fact_terms`].
pub(crate) fn map_atom_terms(a: &p::Atom, g: &dyn Fn(&p::Term) -> p::Term) -> p::Atom {
    use p::Atom::*;
    match a {
        Eq(x, y) => Eq(g(x), g(y)),
        Less(x, y) => Less(g(x), g(y)),
        LessMset(x, y) => LessMset(g(x), g(y)),
        Subterm(x, y) => Subterm(g(x), g(y)),
        Action(f, t) => Action(map_fact_terms(f, g), g(t)),
        Last(t) => Last(g(t)),
        Pred(f) => Pred(map_fact_terms(f, g)),
    }
}

/// Shared structural walker: rebuild a formula, mapping `g` over every leaf
/// term while cloning quantifier `VarSpec`s unchanged.  See [`map_fact_terms`].
/// `pub` (not `pub(crate)`): tamarin-sapic's `formula_unpattern` walks with it
/// too.
pub fn map_formula_terms(f: &p::Formula, g: &dyn Fn(&p::Term) -> p::Term) -> p::Formula {
    use p::Formula::*;
    match f {
        False => False,
        True => True,
        Atom(a) => Atom(map_atom_terms(a, g)),
        Not(x) => Not(Box::new(map_formula_terms(x, g))),
        And(x, y) => And(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Or(x, y) => Or(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Implies(x, y) => Implies(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Iff(x, y) => Iff(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Forall(vs, x) => Forall(vs.clone(), Box::new(map_formula_terms(x, g))),
        Exists(vs, x) => Exists(vs.clone(), Box::new(map_formula_terms(x, g))),
    }
}

/// Apply macros to every term in a fact.  Mirrors HS `applyMacroInFact`
/// (Theory/Model/Fact.hs:323-326 `applyMacroInFact mcs (Fact tag annot terms) =
/// let mTerms = map (applyMacros mcs) terms in Fact tag annot mTerms`).
pub fn apply_macros_fact(macros: &[p::Macro], f: &p::Fact) -> p::Fact {
    map_fact_terms(f, &|t| apply_macros_term(macros, t))
}

/// Apply macros to every term in a formula.  Mirrors HS
/// `applyMacroInFormula` (Theory/Model/Formula.hs:314-316) — `mapAtoms (... applyMacros
/// (lnMacrosToBNMacros macros))`.  In RS, parser-AST quantifiers carry
/// `VarSpec`s with names; macro params have their declared names; the
/// substitution-by-name suffices because the body is closed over the
/// param names and call args at every call site, so no quantifier-bound
/// variable in the surrounding formula can ever be a param (the macro
/// definition is independent of the use site).
pub fn apply_macros_formula(macros: &[p::Macro], f: &p::Formula) -> p::Formula {
    map_formula_terms(f, &|t| apply_macros_term(macros, t))
}

/// Apply macros to all items in a theory.  Mirrors HS's call-sites:
///   - rule prems/concs/acts (Theory/Model/Rule.hs:1115-1121 + ClosedTheory.hs:322-323)
///   - lemma formula (lib/theory/src/Lemma.hs:83-88, called from
///     Theory/Text/Parser.hs:97-105, see line 105)
///   - restriction formula (Theory/Model/Restriction.hs:164-166)
///   - embedded restriction in rule (treat as formula)
///   - rule let-block RHS (already inlined into the rule by
///     `apply_let_block` at elaborate time)
///
/// Macros are collected from `TheoryItem::Macros` items in the theory.
/// If no macros are declared, the theory is left unchanged (HS:
/// `applyMacroInFormula [] fm = fm`).
pub fn expand_theory_macros(thy: &mut p::Theory) {
    let macros: Vec<p::Macro> = thy
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Macros(ms) => Some(ms.clone()),
            _ => None,
        })
        .flatten()
        .collect();

    if macros.is_empty() {
        return;
    }

    expand_items(&macros, &mut thy.items);
}

/// Clone a parser theory and expand its macros, mirroring HS `thyProtoRules`'s
/// `applyMacroInRule (theoryMacros thy)`.  Used for the WF re-checks (batch and
/// web load paths) that must see macro-expanded rules.
pub fn macro_expanded_clone(parsed: &p::Theory) -> p::Theory {
    let mut t = parsed.clone();
    expand_theory_macros(&mut t);
    t
}

/// Apply macros to a slice of theory items.  The parser splices `#ifdef`
/// live branches into the top-level stream (like HS's parse-time
/// preprocessing), so a plain walk sees every macro call-site.
fn expand_items(macros: &[p::Macro], items: &mut [p::TheoryItem]) {
    for item in items.iter_mut() {
        match item {
            p::TheoryItem::Rule(r) | p::TheoryItem::IntrRule(r) => {
                expand_rule(macros, r);
            }
            p::TheoryItem::Lemma(l) => {
                l.formula = apply_macros_formula(macros, &l.formula);
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                r.formula = apply_macros_formula(macros, &r.formula);
            }
            // CaseTest / AccLemma are `TranslationItem`s in HS, which
            // `closeTheoryItem` passes through verbatim with NO macro
            // application (CloseRule.hs:82-90, see line 90 `TranslationItem`; added unmacroed
            // via Theory/Text/Parser.hs:153-163, see line 157,163
            // `liftedAddAccLemma`/`liftedAddCaseTest`).
            // They stay `SyntacticLNFormula` and are only `toLNFormula`'d
            // during accountability translation (Items/CaseTestItem.hs:33-37),
            // which does not run macros. So we deliberately do NOT expand them
            // (they fall into the `_ => {}` arm below).
            //
            // Predicates: bodies are themselves formula templates. Apply
            // macros so a predicate body that calls a macro is expanded
            // before predicate-expand inlines it.
            p::TheoryItem::Predicates(ps) => {
                for pred in ps.iter_mut() {
                    pred.formula = apply_macros_formula(macros, &pred.formula);
                    pred.fact = apply_macros_fact(macros, &pred.fact);
                }
            }
            _ => {}
        }
    }
}

fn expand_rule(macros: &[p::Macro], r: &mut p::Rule) {
    for f in &mut r.premises {
        *f = apply_macros_fact(macros, f);
    }
    for f in &mut r.actions {
        *f = apply_macros_fact(macros, f);
    }
    for f in &mut r.conclusions {
        *f = apply_macros_fact(macros, f);
    }
    for phi in &mut r.embedded_restrictions {
        *phi = apply_macros_formula(macros, phi);
    }
    // Let-block: macros can appear on the RHS.  apply_let_block (in
    // elaborate.rs) substitutes these into the body after parsing; we
    // expand on the LHS-and-RHS terms here so a let `x = macro(...)`
    // sees its RHS rewritten before `apply_let_block` substitutes it.
    for b in &mut r.let_block {
        b.value = apply_macros_term(macros, &b.value);
        b.var = apply_macros_term(macros, &b.var);
    }
    // Variants / diff sides are passed through UNCHANGED, matching HS.
    // `variants` is the user-written explicit `variants ...` block (HS
    // OpenProtoRule's ruAC) and `left_right` is the diff `left ... right ...`
    // block (HS DiffProtoRule's sides). `applyMacroInProtoRule` /
    // `applyMacroInDiffProtoRule` (ClosedTheory.hs:318-323, see line 319,323) only run
    // applyMacroInRule on the main rule `ruE` and leave variants/sides intact,
    // so a macro call inside an explicit variant must survive unexpanded.
}

#[cfg(test)]
#[path = "macro_expand_tests.rs"]
mod tests;
