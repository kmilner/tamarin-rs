// Currently GPL 3.0 until granted permission by the following authors:
//   BTom-GH, ValentinYuri, jdreier, meiersi, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Macro.hs, lib/theory/src/ClosedTheory.hs,
//   lib/theory/src/Items/CaseTestItem.hs, lib/theory/src/Lemma.hs,
//   lib/theory/src/Prover.hs, lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Model/Formula.hs,
//   lib/theory/src/Theory/Model/Restriction.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Sapic/Term.hs,
//   lib/theory/src/Theory/Text/Parser.hs,
//   lib/theory/src/Theory/Text/Parser/Macro.hs

//! Parser-AST level macro expansion.
//!
//! Port of `Term.Macro.applyMacros` (HS: lib/term/src/Term/Macro.hs:40-50)
//! plus the call-sites that drive it:
//!
//!   - `applyMacroInRule`     — lib/theory/src/Theory/Model/Rule.hs:1032-1037
//!   - `applyMacroInFact`     — lib/theory/src/Theory/Model/Fact.hs:301-303
//!   - `applyMacroInFormula`  — lib/theory/src/Theory/Model/Formula.hs:311-313
//!   - `applyMacroInLemma`    — lib/theory/src/Lemma.hs:83-88
//!   - `applyMacroInRestriction` — lib/theory/src/Theory/Model/Restriction.hs:163-165
//!   - `closeProtoRule` calls applyMacroInRule BEFORE variantsProtoRule
//!     — lib/theory/src/Rule.hs:96-98
//!   - `parseLemmaWithMacros`  — lib/theory/src/Theory/Text/Parser.hs:97-105
//!
//! HS works at the typed `LNTerm` / `LNFact` / `LNFormula` level, with
//! macro matching keyed on the `FunSym` (a `NoEq (name, (arity, Private,
//! Destructor))` tuple — Macro.hs:30).  RS parses lemma/restriction
//! formulas as `parser::ast::Formula` and only converts to `LNFormula`
//! later (via `formula_to_guarded`), so the natural place to expand is
//! the parser AST.  This is observationally faithful: every macro call
//! site is rewritten to its body before either side's typed conversion
//! runs.  The macro fun-syms themselves are still registered in MaudeSig
//! (HS Parser/Macro.hs:29-49, see line 48 `addMacroSym`) so any unexpanded reference —
//! and Maude — still see them.
//!
//! Recursion semantics mirror HS exactly:
//!   - args are recursively expanded FIRST (Macro.hs:46),
//!   - then substitution into the body,
//!   - then the EXPANDED body is recursively re-expanded
//!     (Macro.hs:48 `applyMacros macros (apply subst mout)`).
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
            // arity (Macro.hs:30 `macroToFunSym (op,args,_) = NoEq (op,
            // (length args, Private, Destructor))` ; matching macros are
            // found via Macro.hs:53-54 `find (\m -> macroToFunSym m == f)`).
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
        p::Term::Pair(items) => p::Term::Pair(
            items.iter().map(|t| apply_macros_term(macros, t)).collect(),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(
            Box::new(apply_macros_term(macros, inner)),
        ),
        // A BARE identifier (no `$~#%` prefix, no `:sort` suffix, no `.idx`)
        // naming a 0-ary macro is a macro CALL: HS's `nullaryApp` parser
        // alternative (Term.hs:143-148) runs before `plit` and matches any
        // arity-0 name in `funSyms ∪ macroNames`, so such an identifier
        // reaches HS's `applyMacros` as `fApp (NoEq (m,(0,..))) []`, never
        // as a variable.  RS's surface parser is signature-less and yields
        // `Var`, so resolve here.  Any sort/index decoration means HS's
        // `symbol` match would have left trailing input and backtracked to
        // `plit` — a genuine variable; leave those (and 0-ary FUNCTION
        // names, which `term_to_lnterm`'s USER_NULLARY_FUNS branch lifts)
        // untouched.
        p::Term::Var(v) => {
            if v.idx == 0 && v.sort == p::SortHint::Untagged && v.typ.is_none() {
                if let Some(m) = find_matching_macro(&v.name, 0, macros) {
                    let expanded = subst_term_by_name(&m.body, &BTreeMap::new());
                    // Re-expand the EXPANDED body to handle nested macros.
                    return apply_macros_term(macros, &expanded);
                }
            }
            term.clone()
        }
        // Literals: no recursion (HS Macro.hs:51 `Lit l -> lit l`).
        p::Term::PubLit(_) | p::Term::FreshLit(_)
        | p::Term::NatLit(_) | p::Term::Number(_) | p::Term::NumberOne
        | p::Term::NatOne | p::Term::DhNeutral => term.clone(),
    }
}

/// HS `findMatchingMacro f macros = find (\m -> macroToFunSym m == f)`
/// (Macro.hs:53-54).  At parser-AST level a call-site has no FunSym
/// flags so we match by (name, arity) — equivalent for non-clashing
/// macro names since `addMacroSym` rejects redefinitions and built-in
/// fun-syms have known fixed arity (parser/Macro.hs:45-49 `case lookup
/// op (stFunSyms ++ macroNames) -> fail`).
fn find_matching_macro<'a>(
    name: &str,
    arity: usize,
    macros: &'a [p::Macro],
) -> Option<&'a p::Macro> {
    macros.iter().find(|m| m.name == name && m.args.len() == arity)
}

/// Apply a name-keyed substitution to a parser term.  HS's typed
/// `apply subst term` (Macro.hs:48) becomes a structural name-keyed walk.
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
        p::Term::Pair(items) => p::Term::Pair(
            items.iter().map(|a| subst_term_by_name(a, subst)).collect(),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(subst_term_by_name(a, subst)),
            Box::new(subst_term_by_name(b, subst)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(subst_term_by_name(a, subst)),
            Box::new(subst_term_by_name(b, subst)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(
            Box::new(subst_term_by_name(inner, subst)),
        ),
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
pub(crate) fn map_formula_terms(f: &p::Formula, g: &dyn Fn(&p::Term) -> p::Term) -> p::Formula {
    use p::Formula::*;
    match f {
        False => False,
        True => True,
        Atom(a) => Atom(map_atom_terms(a, g)),
        Not(x) => Not(Box::new(map_formula_terms(x, g))),
        And(x, y) => And(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g))),
        Or(x, y) => Or(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g))),
        Implies(x, y) => Implies(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g))),
        Iff(x, y) => Iff(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g))),
        Forall(vs, x) => Forall(vs.clone(), Box::new(map_formula_terms(x, g))),
        Exists(vs, x) => Exists(vs.clone(), Box::new(map_formula_terms(x, g))),
    }
}

/// Apply macros to every term in a fact.  Mirrors HS `applyMacroInFact`
/// (Fact.hs:301-303 `applyMacroInFact mcs (Fact tag annot terms) =
/// Fact tag annot (map (applyMacros mcs) terms)`).
pub fn apply_macros_fact(macros: &[p::Macro], f: &p::Fact) -> p::Fact {
    map_fact_terms(f, &|t| apply_macros_term(macros, t))
}

/// Apply macros to every term in a formula.  Mirrors HS
/// `applyMacroInFormula` (Formula.hs:311-313) — `mapAtoms (... applyMacros
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
///   - rule prems/concs/acts (Rule.hs:1032-1037 + ClosedTheory.hs:322-323)
///   - lemma formula (Lemma.hs:83-88, called from Parser.hs:97-105, see line 105)
///   - restriction formula (Restriction.hs:163-165)
///   - embedded restriction in rule (treat as formula)
///   - rule let-block RHS (already inlined into the rule by
///     `apply_let_block` at elaborate time)
///
/// Macros are collected from `TheoryItem::Macros` items in the theory.
/// If no macros are declared, the theory is left unchanged (HS:
/// `applyMacroInFormula [] fm = fm`).
pub fn expand_theory_macros(thy: &mut p::Theory) {
    let macros: Vec<p::Macro> = thy.items.iter().filter_map(|i| match i {
        p::TheoryItem::Macros(ms) => Some(ms.clone()),
        _ => None,
    }).flatten().collect();

    if macros.is_empty() { return; }

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
            // application (Prover.hs:170-251, see line 204 `TranslationItem`; added unmacroed
            // via Parser.hs:153-157, see line 157,163 `liftedAddAccLemma`/`liftedAddCaseTest`).
            // They stay `SyntacticLNFormula` and are only `toLNFormula`'d
            // during accountability translation (Items/CaseTestItem.hs:34-37),
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
    for f in &mut r.premises { *f = apply_macros_fact(macros, f); }
    for f in &mut r.actions { *f = apply_macros_fact(macros, f); }
    for f in &mut r.conclusions { *f = apply_macros_fact(macros, f); }
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
    // `applyMacroInDiffProtoRule` (ClosedTheory.hs:318-319, see line 319,323) only run
    // applyMacroInRule on the main rule `ruE` and leave variants/sides intact,
    // so a macro call inside an explicit variant must survive unexpanded.
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    fn parse(src: &str) -> p::Theory {
        parse_theory(src, &[]).expect("parse")
    }

    #[test]
    fn bare_nullary_macro_name_expands() {
        // HS `nullaryApp` (Term.hs:143-148) parses a BARE arity-0 macro
        // name as a 0-ary application, so `konst` and `konst()` are the
        // same call.  A sorted/indexed variable of the same name is NOT
        // a call.
        let src = "theory T begin\n\
            builtins: hashing\n\
            macros: konst() = h('seed')\n\
            rule R: [ In(konst) ] --[ M(konst.1, konst:pub) ]-> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        // Premise In(konst) → In(h('seed')).
        assert!(matches!(&rule.premises[0].args[0],
            p::Term::App(n, args) if n == "h" && args.len() == 1),
            "got {:?}", rule.premises[0].args[0]);
        // konst.1 (indexed) and konst:pub (sorted) stay variables.
        assert!(matches!(&rule.actions[0].args[0],
            p::Term::Var(v) if v.name == "konst" && v.idx == 1),
            "got {:?}", rule.actions[0].args[0]);
        assert!(matches!(&rule.actions[0].args[1],
            p::Term::Var(v) if v.name == "konst"
                && v.sort != p::SortHint::Untagged),
            "got {:?}", rule.actions[0].args[1]);
    }

    #[test]
    fn simple_term_macro_replaces_call() {
        // macro `id(x) = x`; call `id(a)` → `a`.
        let src = "theory T begin\n\
            macros: id(x) = x\n\
            rule R: [ In(id(a)) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        // Premise was In(id(a)); after expansion: In(a).
        let arg = &rule.premises[0].args[0];
        assert!(matches!(arg, p::Term::Var(v) if v.name == "a"), "got {:?}", arg);
    }

    #[test]
    fn nested_macro_is_re_expanded() {
        // hashdec(x, y) = h(decrypt(x, y)); decrypt(x, y) = adec(x, y).
        // Expanding hashdec(a, b) should produce h(adec(a, b)).
        let src = "theory T begin\n\
            builtins: hashing, asymmetric-encryption\n\
            macros: decrypt(x, y) = adec(x, y), hashdec(x, y) = h(decrypt(x, y))\n\
            rule R: [ In(hashdec(a, b)) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        let arg = &rule.premises[0].args[0];
        // Expected: App("h", [App("adec", [Var(a), Var(b)])])
        if let p::Term::App(h_name, h_args) = arg {
            assert_eq!(h_name, "h");
            assert_eq!(h_args.len(), 1);
            if let p::Term::App(adec_name, adec_args) = &h_args[0] {
                assert_eq!(adec_name, "adec");
                assert_eq!(adec_args.len(), 2);
            } else {
                panic!("expected adec, got {:?}", h_args[0]);
            }
        } else {
            panic!("expected h(...), got {:?}", arg);
        }
    }

    #[test]
    fn macro_in_lemma_formula_expands() {
        // Lemma uses a macro that wraps Action(A(m(x))).
        let src = "theory T begin\n\
            macros: m(x) = x\n\
            rule R: [ In(x) ] --[ A(m(x)) ]-> [ ]\n\
            lemma L: exists-trace \"Ex x #i. A(m(x)) @ #i\"\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let lemma = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Lemma(l) => Some(l),
            _ => None,
        }).unwrap();
        // The Action atom's fact's arg should be Var(x) (not App("m", [Var(x)])).
        fn check(f: &p::Formula) {
            match f {
                p::Formula::Exists(_, body) => check(body),
                p::Formula::And(a, b) => { check(a); check(b); }
                p::Formula::Atom(p::Atom::Action(fact, _)) => {
                    assert!(matches!(&fact.args[0], p::Term::Var(v) if v.name == "x"),
                        "got {:?}", fact.args[0]);
                }
                _ => {}
            }
        }
        check(&lemma.formula);
    }

    #[test]
    fn macro_with_pair_body_via_pair_syntax() {
        // m2(x, y) = <x, y>; call m2(a, b) → Pair([a, b]).
        let src = "theory T begin\n\
            macros: m2(x, y) = <x, y>\n\
            rule R: [ In(m2(a, b)) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        let arg = &rule.premises[0].args[0];
        if let p::Term::Pair(items) = arg {
            assert_eq!(items.len(), 2);
        } else {
            panic!("expected Pair, got {:?}", arg);
        }
    }

    #[test]
    fn macro_inside_ifdef_is_expanded() {
        // A rule under a live `#ifdef FLAG` branch is spliced to the top
        // level by the parser, so its macro call-sites are expanded like any
        // other rule's.
        let src = "theory T begin\n\
            macros: id(x) = x\n\
            #ifdef FLAG\n\
            rule R: [ In(id(a)) ] --> [ ]\n\
            #endif\n\
            end\n";
        let mut thy = parse_theory(src, &["FLAG"]).expect("parse");
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|it| match it {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).expect("rule from live ifdef branch at top level");
        let arg = &rule.premises[0].args[0];
        assert!(matches!(arg, p::Term::Var(v) if v.name == "a"), "got {:?}", arg);
    }

    #[test]
    fn case_test_formula_is_not_macro_expanded() {
        // HS keeps CaseTest as a `TranslationItem` and applies NO macros to
        // it (Prover.hs:170-251, see line 204; Parser.hs:159-163, see line 163 `liftedAddCaseTest`). Probed
        // against the real HS prover (v1.13.0) on an equivalent theory: the
        // stored case-test formula prints `Blame( idm(a) )` UNEXPANDED, e.g.
        //   predicate: Blamed( a ) <=> ∃ #i. Blame( idm(a) ) @ #i
        // So after `expand_theory_macros` the case-test formula must still
        // contain the macro call `App("idm", ...)`.
        let src = "theory T begin\n\
            functions: id/1\n\
            macros: idm(x) = id(x)\n\
            rule R: [ In(x) ] --[ Blame(x) ]-> [ Out(x) ]\n\
            test blamed: \"Ex #i. Blame(idm(a)) @ #i\"\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let ct = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::CaseTest(c) => Some(c),
            _ => None,
        }).expect("case test");
        // The Action atom's fact arg must remain App("idm", [Var("a")]).
        fn check(f: &p::Formula) -> bool {
            match f {
                p::Formula::Exists(_, body) | p::Formula::Forall(_, body) => check(body),
                p::Formula::And(a, b) | p::Formula::Or(a, b)
                | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) => check(a) || check(b),
                p::Formula::Not(g) => check(g),
                p::Formula::Atom(p::Atom::Action(fact, _)) => {
                    matches!(fact.args.first(),
                        Some(p::Term::App(name, args)) if name == "idm" && args.len() == 1)
                }
                _ => false,
            }
        }
        assert!(check(&ct.formula),
            "case-test formula was macro-expanded (idm should survive): {:?}",
            ct.formula);
    }

    #[test]
    fn acc_lemma_formula_is_not_macro_expanded() {
        // AccLemma is also a `TranslationItem` (Prover.hs:170-251, see line 204; Parser.hs:153-157, see line 157
        // `liftedAddAccLemma`) and is never macro-expanded. After
        // `expand_theory_macros` the acc-lemma formula must still contain the
        // macro call `App("idm", ...)`.
        let src = "theory T begin\n\
            functions: id/1\n\
            macros: idm(x) = id(x)\n\
            rule R: [ In(x) ] --[ Blame(x), Fin() ]-> [ Out(x) ]\n\
            test blamed: \"Ex #i. Blame(idm(a)) @ #i\"\n\
            lemma acc: blamed accounts for \"All #i. Fin() @ #i ==> Ex #j. Blame(idm(a)) @ #j\"\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let acc = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::AccLemma(a) => Some(a),
            _ => None,
        }).expect("acc lemma");
        fn check(f: &p::Formula) -> bool {
            match f {
                p::Formula::Exists(_, body) | p::Formula::Forall(_, body) => check(body),
                p::Formula::And(a, b) | p::Formula::Or(a, b)
                | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) => check(a) || check(b),
                p::Formula::Not(g) => check(g),
                p::Formula::Atom(p::Atom::Action(fact, _)) => {
                    matches!(fact.args.first(),
                        Some(p::Term::App(name, args)) if name == "idm" && args.len() == 1)
                }
                _ => false,
            }
        }
        assert!(check(&acc.formula),
            "acc-lemma formula was macro-expanded (idm should survive): {:?}",
            acc.formula);
    }

    #[test]
    fn no_macro_means_no_change() {
        let src = "theory T begin\n\
            rule R: [ In(a) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        let before = thy.clone();
        expand_theory_macros(&mut thy);
        assert_eq!(thy, before);
    }
}
