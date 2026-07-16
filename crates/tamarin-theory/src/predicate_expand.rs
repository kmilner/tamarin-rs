//! Port of `Theory.Syntactic.Predicate.expandFormula` —
//! substitutes predicate-atom occurrences in a formula with the body
//! of the matching predicate definition. Uses parser-AST formulas /
//! predicates throughout.
//!
//! A predicate `P(x_1, ..., x_n) <=> phi` is "applied" to a use-site
//! atom `P(t_1, ..., t_n)` by substituting each variable `x_i` in
//! `phi` with the corresponding term `t_i`.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;

#[derive(Debug, Clone)]
pub struct ExpandError {
    pub message: String,
}

impl std::fmt::Display for ExpandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for ExpandError {}

/// Recursively expand every predicate-atom in `formula`. Returns a
/// new formula whose atoms are only `Action`, `Eq`, `Less`, `Subterm`,
/// `Last` — i.e. no `Pred(_)` and no `LessMset(_)` left: the multiset
/// `(<)` operator is rewritten to `∃ z. rhs = lhs ++ z` via the builtin
/// `Smaller` predicate, exactly as HS `expandFormula` does.
pub fn expand_formula(
    formula: &p::Formula,
    predicates: &[p::Predicate],
) -> Result<p::Formula, ExpandError> {
    expand(formula, predicates, &Subst::default())
}

/// Convenience: expand every formula in a theory's lemmas / restrictions
/// against the theory's predicate definitions. Items that don't carry a
/// formula are left unchanged.
///
/// Each formula-bearing item is expanded only against predicates declared
/// EARLIER in the theory (in source order), matching Haskell: there the
/// expansion runs incrementally during parsing (`liftedExpandLemma` /
/// `liftedExpandRestriction` call `expandFormula (theoryPredicates thy)`,
/// Parser.hs / TheoryObject.hs), where `thy` only contains items parsed
/// so far. A lemma textually preceding a predicate definition therefore
/// does NOT see that predicate (Haskell would report `UndefinedPredicate`
/// for a use of it), so we must not pre-collect the full predicate set.
pub fn expand_theory_formulas(thy: &mut p::Theory) -> Result<(), ExpandError> {
    // Predicates accumulated from items seen so far, in source order.
    let mut predicates: Vec<p::Predicate> = Vec::new();

    for item in thy.items.iter_mut() {
        match item {
            // A predicate declaration only becomes visible to items that
            // follow it (HS `preddeclaration` adds it at this point).
            p::TheoryItem::Predicates(ps) => {
                predicates.extend(ps.iter().cloned());
            }
            p::TheoryItem::Lemma(l) => {
                l.formula = expand_formula(&l.formula, &predicates)?;
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                r.formula = expand_formula(&r.formula, &predicates)?;
            }
            // CaseTest / AccLemma are NOT predicate-expanded: HS adds them
            // verbatim via `liftedAddCaseTest` / `liftedAddAccLemma`
            // (Theory/Text/Parser.hs:152-163), which call `addCaseTest` /
            // `addAccLemma` directly with NO `expandFormula` / `expandLemma`.
            // Only `liftedAddLemma` (→ `expandLemma`) and the restriction path
            // (→ `expandRestriction`) expand (TheoryObject.hs:430-446). The
            // case-test / acc-lemma formulas stay `SyntacticLNFormula` with
            // their `Pred` sugar intact; the accountability translation
            // (`caseTestToPredicate`, Items/CaseTestItem.hs:33-37) consumes
            // them later via `toLNFormula`, not here.
            _ => {}
        }
    }
    Ok(())
}

// =============================================================================
// Substitution
// =============================================================================

/// Map from variable name → replacement term. Used when applying a
/// predicate's body to a use-site.
#[derive(Debug, Clone, Default)]
struct Subst {
    /// Indexed by variable name (the parser doesn't track de-Bruijn indices
    /// for formula scopes — we use names directly).
    map: BTreeMap<String, p::Term>,
}

// =============================================================================
// Recursion
// =============================================================================

fn expand(
    f: &p::Formula,
    preds: &[p::Predicate],
    subst: &Subst,
) -> Result<p::Formula, ExpandError> {
    match f {
        p::Formula::True | p::Formula::False => Ok(f.clone()),
        p::Formula::Atom(a) => expand_atom(a, preds, subst),
        p::Formula::Not(g) => Ok(p::Formula::Not(Box::new(expand(g, preds, subst)?))),
        p::Formula::And(a, b) => Ok(p::Formula::And(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Or(a, b) => Ok(p::Formula::Or(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Implies(a, b) => Ok(p::Formula::Implies(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Iff(a, b) => Ok(p::Formula::Iff(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Forall(vs, body) =>
            expand_quantified(vs, body, preds, subst, p::Formula::Forall),
        p::Formula::Exists(vs, body) =>
            expand_quantified(vs, body, preds, subst, p::Formula::Exists),
    }
}

fn strip_shadowed<'a>(subst: &'a Subst, vs: &[p::VarSpec]) -> std::borrow::Cow<'a, Subst> {
    // Common case: no binder shadows a substituted variable, so removing them
    // would be a no-op — borrow the original instead of cloning the whole map.
    if !vs.iter().any(|v| subst.map.contains_key(&v.name)) {
        return std::borrow::Cow::Borrowed(subst);
    }
    let mut out = subst.clone();
    for v in vs { out.map.remove(&v.name); }
    std::borrow::Cow::Owned(out)
}

/// Expand the body of a quantifier, applying CAPTURE-AVOIDING
/// substitution.  Haskell's `expandFormula` works over De-Bruijn-indexed
/// formulas and shifts use-site terms past the body's binders
/// (`compSubst`, Predicate.hs), so a substituted variable can never be
/// captured by an inner quantifier.  Our parser AST is name-based, so we
/// emulate that: when a binder's `(name, sort)` also occurs in the RANGE
/// of the active substitution, that binder would capture the substituted
/// variable — so we alpha-rename the binder to a fresh name first (by
/// adding `binder → fresh` to the subst used for the body, which the
/// normal name-substitution then applies, respecting inner shadowing via
/// `strip_shadowed`).
///
/// Capture keys on `(name, sort)`, NOT name alone, because HS variables
/// are `LVar { lvarName, lvarSort, lvarIdx }` and a substitution
/// (`compSubst`/`substFromList`, Predicate.hs:96-105) maps a `Free LVar`
/// keyed by the WHOLE LVar — so a message var `a` (`LSortMsg`) and a
/// timepoint binder `#a` (`LSortNode`) are DISTINCT variables that cannot
/// capture each other.  At print time HS likewise opens binders with
/// `freshLVar n s` (Formula.hs:276) over a `FreshState` seeded by
/// `avoidPrecise = avoidPreciseVars . frees` (LTerm.hs:681-690); the bound
/// `#a` is not free and the free `a` was abstracted to `x` before
/// printing, so HS renders `#a` (idx 0).  Do NOT key capture by name
/// alone: that makes RS treat a substituted `a` as colliding with `#a`
/// and rename it `#a1`, a divergence from HS (`binding.spthy`).
///
/// Residual print-name gap (rare): HS keeps the original binder hint name
/// (De-Bruijn shift only, Predicate.hs:94-106) and re-renames bound vars
/// fresh at print time, yielding e.g. `z.1` when a free `z` (SAME sort) is
/// in scope.  Our name-based rename mints a NEW base (`z`→`z1`), so the
/// printed binder reads `z1` rather than `z.1` in that one same-sort
/// collision case.  A faithful fix would keep the base name `z` and
/// instead allocate a distinct `idx`; not done here.
fn expand_quantified(
    vs: &[p::VarSpec],
    body: &p::Formula,
    preds: &[p::Predicate],
    subst: &Subst,
    make: fn(Vec<p::VarSpec>, Box<p::Formula>) -> p::Formula,
) -> Result<p::Formula, ExpandError> {
    let new_subst = strip_shadowed(subst, vs);
    let capture = subst_range_vars(&new_subst);
    // A binder collides only with a substituted var of the SAME (name, sort)
    // — HS LVar identity (see fn doc).
    let collides = |v: &p::VarSpec| capture.contains(&(v.name.clone(), sort_key(v.sort)));
    // Fast path: no binder collides with a substituted variable.
    if !vs.iter().any(collides) {
        return Ok(make(vs.to_vec(), Box::new(expand(body, preds, &new_subst)?)));
    }
    // Alpha-rename the colliding binders to fresh names.  The fresh-name
    // avoid-set stays name-based (over-avoiding a name is harmless; renaming
    // only fires on a genuine same-sort collision).
    let mut avoid: std::collections::BTreeSet<String> =
        capture.iter().map(|(n, _)| n.clone()).collect();
    collect_formula_vars(body, &mut avoid);
    for v in vs { avoid.insert(v.name.clone()); }
    let mut new_vs = vs.to_vec();
    let mut body_subst = new_subst.into_owned();
    for v in new_vs.iter_mut() {
        if collides(v) {
            let fresh = fresh_name(&v.name, &avoid);
            avoid.insert(fresh.clone());
            let mut fv = v.clone();
            fv.name = fresh.clone();
            body_subst.map.insert(v.name.clone(), p::Term::Var(fv));
            v.name = fresh;
        }
    }
    Ok(make(new_vs, Box::new(expand(body, preds, &body_subst)?)))
}

/// `(name, sort)` pairs occurring in the RANGE (values) of a substitution —
/// the variables at risk of capture by a binder of the SAME name AND sort.
fn subst_range_vars(subst: &Subst) -> std::collections::BTreeSet<(String, SortKey)> {
    let mut out = std::collections::BTreeSet::new();
    for v in subst.map.values() { collect_term_vars_keyed(v, &mut out); }
    out
}

/// Normalised sort domain matching HS `LSort` variable identity.  HS LVars
/// compare by `(lvarName, lvarSort)`; the message domain (a bare formula
/// var, no prefix) is `LSortMsg`, so `Msg` and the un-prefixed `Untagged`
/// hint collapse to the same key, while `#`/`~`/`$`/`%` are distinct sorts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SortKey { Msg, Pub, Fresh, Node, Nat }

fn sort_key(s: p::SortHint) -> SortKey {
    match s {
        p::SortHint::Msg | p::SortHint::Untagged => SortKey::Msg,
        p::SortHint::Pub => SortKey::Pub,
        p::SortHint::Fresh => SortKey::Fresh,
        p::SortHint::Node => SortKey::Node,
        p::SortHint::Nat => SortKey::Nat,
        p::SortHint::Suffix(p::SuffixSort::Msg) => SortKey::Msg,
        p::SortHint::Suffix(p::SuffixSort::Pub) => SortKey::Pub,
        p::SortHint::Suffix(p::SuffixSort::Fresh) => SortKey::Fresh,
        p::SortHint::Suffix(p::SuffixSort::Node) => SortKey::Node,
        p::SortHint::Suffix(p::SuffixSort::Nat) => SortKey::Nat,
    }
}

/// Collect `(name, sort)` keys of every variable in a term.
fn collect_term_vars_keyed(
    t: &p::Term,
    out: &mut std::collections::BTreeSet<(String, SortKey)>,
) {
    match t {
        p::Term::Var(v) => { out.insert((v.name.clone(), sort_key(v.sort))); }
        p::Term::App(_, args) | p::Term::Pair(args) =>
            args.iter().for_each(|a| collect_term_vars_keyed(a, out)),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            collect_term_vars_keyed(a, out);
            collect_term_vars_keyed(b, out);
        }
        p::Term::PatMatch(inner) => collect_term_vars_keyed(inner, out),
        _ => {}
    }
}

/// Build the builtin `Smaller`/multiset-`(<)` expansion `∃ z. rhs = lhs ++ z`.
///
/// Mirrors HS `builtinPredicates` (Theory/Syntactic/Predicate.hs:58-74):
/// `Smaller(x, y) <=> hinted exists z (Ato (EqE (bvt y) (fAppUnion (fvt x, fvt z))))`,
/// i.e. `∃ z. y = x ++ z` with `lhs = x`, `rhs = y`.  The multiset operator
/// `x (<) y` parses to `Smaller [x, y]` (HS `smallerp`, Formula.hs:30-38), so
/// the same expansion applies with `lhs = x`, `rhs = y`.  `z`'s name is picked
/// capture-avoidingly: a use-site argument may itself mention `z`, which the
/// bound `z` would otherwise capture.
fn smaller_expansion(lhs: &p::Term, rhs: &p::Term) -> p::Formula {
    let mut avoid = std::collections::BTreeSet::new();
    collect_term_vars(lhs, &mut avoid);
    collect_term_vars(rhs, &mut avoid);
    let zname = if avoid.contains("z") {
        fresh_name("z", &avoid)
    } else {
        "z".to_string()
    };
    let z = p::VarSpec {
        name: zname,
        idx: 0,
        sort: p::SortHint::Untagged,
        typ: None,
    };
    let z_term = p::Term::Var(z.clone());
    // HS builds the body union via `fAppUnion (fvt x, fvt z)`
    // (Predicate.hs:64-66), and `fAppUnion = fAppAC Union` SORTS its
    // arguments on construction (Term/Term/Raw.hs:118-122).  Applying the
    // use-site substitution (`x ↦ <lhs>`, `y ↦ <rhs>`) then re-normalises
    // the AC term, re-sorting by `Ord LVar` = (idx, sort, name).  So the
    // displayed union is always AC-sorted, e.g. an existential `z` (idx 0)
    // precedes a use-site abstraction `x.1` (idx 1) → `z++x.1`, NOT
    // `x.1++z`.  Build the union then canonicalise it exactly as the rest
    // of the AC pipeline does (`canonicalize_ac_in_pterm`).
    let sum = crate::elaborate::canonicalize_ac_in_pterm(&p::Term::BinOp(
        p::BinOp::Union,
        Box::new(lhs.clone()),
        Box::new(z_term),
    ));
    p::Formula::Exists(
        vec![z],
        Box::new(p::Formula::Atom(p::Atom::Eq(rhs.clone(), sum))),
    )
}

/// A variant of `base` (e.g. `z` → `z1`) not present in `avoid`.
fn fresh_name(base: &str, avoid: &std::collections::BTreeSet<String>) -> String {
    let mut n = 1u64;
    loop {
        let cand = format!("{}{}", base, n);
        if !avoid.contains(&cand) { return cand; }
        n += 1;
    }
}

fn collect_term_vars(t: &p::Term, out: &mut std::collections::BTreeSet<String>) {
    match t {
        p::Term::Var(v) => { out.insert(v.name.clone()); }
        p::Term::App(_, args) | p::Term::Pair(args) =>
            args.iter().for_each(|a| collect_term_vars(a, out)),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        p::Term::PatMatch(inner) => collect_term_vars(inner, out),
        _ => {}
    }
}

fn collect_atom_vars(a: &p::Atom, out: &mut std::collections::BTreeSet<String>) {
    match a {
        p::Atom::Pred(fact) => fact.args.iter().for_each(|t| collect_term_vars(t, out)),
        p::Atom::Eq(s, t) | p::Atom::Less(s, t)
        | p::Atom::LessMset(s, t) | p::Atom::Subterm(s, t) => {
            collect_term_vars(s, out);
            collect_term_vars(t, out);
        }
        p::Atom::Action(fact, t) => {
            fact.args.iter().for_each(|a| collect_term_vars(a, out));
            collect_term_vars(t, out);
        }
        p::Atom::Last(t) => collect_term_vars(t, out),
    }
}

/// Every variable name (free or bound) anywhere in a formula — used as
/// the avoid-set when minting fresh binder names.
fn collect_formula_vars(f: &p::Formula, out: &mut std::collections::BTreeSet<String>) {
    match f {
        p::Formula::True | p::Formula::False => {}
        p::Formula::Atom(a) => collect_atom_vars(a, out),
        p::Formula::Not(g) => collect_formula_vars(g, out),
        p::Formula::And(a, b) | p::Formula::Or(a, b)
        | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) => {
            collect_formula_vars(a, out);
            collect_formula_vars(b, out);
        }
        p::Formula::Forall(vs, b) | p::Formula::Exists(vs, b) => {
            for v in vs { out.insert(v.name.clone()); }
            collect_formula_vars(b, out);
        }
    }
}

fn expand_atom(
    a: &p::Atom,
    preds: &[p::Predicate],
    subst: &Subst,
) -> Result<p::Formula, ExpandError> {
    match a {
        p::Atom::Pred(fact) => {
            // Substitute the use-site arguments first.
            let sub_args: Vec<p::Term> = fact.args.iter()
                .map(|t| subst_term(t, subst))
                .collect();
            // Look up predicate definition.  HS `lookupPredicate`
            // (Theory/Syntactic/Predicate.hs:76-80) matches on the FULL
            // `FactTag` (`sameName (Fact tag _ _) (Fact tag' _ _) = tag ==
            // tag'`), where `FactTag = ProtoFact Multiplicity String Int`
            // derives `Eq` — so multiplicity (persistent/linear), name AND
            // arity must all match.  An arity- or multiplicity-mismatched
            // use-site simply does not match and falls through to the
            // `UndefinedPredicate` error below.
            match find_predicate(preds, fact) {
                Some(pred) => {
                    // Build a fresh subst from the predicate's parameters
                    // (which the parser stores as terms — typically Var)
                    // to the use-site arguments.
                    let mut new_subst = Subst::default();
                    for (param, value) in pred.fact.args.iter().zip(sub_args.iter()) {
                        if let p::Term::Var(v) = param {
                            new_subst.map.insert(v.name.clone(), value.clone());
                        } else {
                            // Non-variable in predicate parameter list — can't
                            // do simple substitution. Skip.
                            return Err(ExpandError {
                                message: format!("predicate `{}` has non-variable parameter; \
                                    predicate definitions must use plain variables",
                                    fact.name),
                            });
                        }
                    }
                    expand(&pred.formula, preds, &new_subst)
                }
                None => {
                    // No user predicate matched.  HS appends the single
                    // builtin predicate `Smaller` whose fact tag is
                    // `ProtoFact Linear "Smaller" 2` (Predicate.hs:50-67),
                    // so it matches a use-site only when it is LINEAR (not
                    // persistent), named exactly `Smaller`, and arity 2.
                    if !fact.persistent && fact.name == "Smaller" && sub_args.len() == 2 {
                        // Smaller(x, y) <=> ∃ z. y = x ++ z (see smaller_expansion).
                        return Ok(smaller_expansion(&sub_args[0], &sub_args[1]));
                    }
                    // HS `show (UndefinedPredicate facttag)`
                    // (Theory/Text/Parser/Exceptions.hs:33-34) =
                    //   "undefined predicate " ++ showFactTagArity facttag
                    // and `showFactTagArity` (Theory/Model/Fact.hs:519-527) =
                    //   (if persistent then "!" else "") ++ name ++ "/" ++ arity.
                    Err(ExpandError {
                        message: format!(
                            "undefined predicate {}{}/{}",
                            if fact.persistent { "!" } else { "" },
                            fact.name,
                            sub_args.len(),
                        ),
                    })
                }
            }
        }
        // For non-Pred atoms, just substitute through their terms.
        p::Atom::Eq(s, t) => Ok(p::Formula::Atom(p::Atom::Eq(
            subst_term(s, subst), subst_term(t, subst)))),
        p::Atom::Less(s, t) => Ok(p::Formula::Atom(p::Atom::Less(
            subst_term(s, subst), subst_term(t, subst)))),
        // Multiset `s (<) t`.  In HS there is no dedicated atom for this:
        // `smallerp` (Theory/Text/Parser/Formula.hs:30-38) parses `(<)` to
        // `Syntactic . Pred $ protoFact Linear "Smaller" [s, t]`, which
        // `expandFormula` (Predicate.hs:82-93) then rewrites via the builtin
        // `Smaller` predicate to `∃ z. t = s ++ z`.  We mirror that rewrite
        // here so `LessMset` never survives into guarded conversion / solving
        // / pretty-printing — matching HS byte-for-byte (`... ⇒ (∃ z. y =
        // (x++z))`).  Operand order: `s (<) t` ⇒ lhs = s, rhs = t.
        p::Atom::LessMset(s, t) =>
            Ok(smaller_expansion(&subst_term(s, subst), &subst_term(t, subst))),
        p::Atom::Subterm(s, t) => Ok(p::Formula::Atom(p::Atom::Subterm(
            subst_term(s, subst), subst_term(t, subst)))),
        p::Atom::Action(fact, t) => {
            let new_fact = p::Fact {
                persistent: fact.persistent,
                name: fact.name.clone(),
                args: fact.args.iter().map(|a| subst_term(a, subst)).collect(),
                annotations: fact.annotations.clone(),
            };
            Ok(p::Formula::Atom(p::Atom::Action(new_fact, subst_term(t, subst))))
        }
        p::Atom::Last(t) => Ok(p::Formula::Atom(p::Atom::Last(subst_term(t, subst)))),
    }
}

/// Find the predicate whose declared fact has the SAME `FactTag` as the
/// use-site `fact`.  Mirrors HS `lookupPredicate`
/// (Theory/Syntactic/Predicate.hs:76-80):
///   `find (sameName fact . pFact)` with
///   `sameName (Fact tag _ _) (Fact tag' _ _) = tag == tag'`.
/// `FactTag = ProtoFact Multiplicity String Int` derives `Eq`, so the
/// match requires multiplicity (persistent/linear), name, AND arity to
/// all be equal.
fn find_predicate<'a>(preds: &'a [p::Predicate], fact: &p::Fact) -> Option<&'a p::Predicate> {
    preds.iter().find(|pr| {
        pr.fact.persistent == fact.persistent
            && pr.fact.name == fact.name
            && pr.fact.args.len() == fact.args.len()
    })
}

/// Name-keyed term substitution.  Delegates to the shared
/// `macro_expand::subst_term_by_name` (the `Subst` newtype is just a wrapper
/// around the same `BTreeMap<String, p::Term>`), keeping predicate- and
/// macro-expansion substitution in lockstep.
fn subst_term(t: &p::Term, subst: &Subst) -> p::Term {
    crate::macro_expand::subst_term_by_name(t, &subst.map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parser::parse_formula_str;

    fn pred(decl: &str) -> Vec<p::Predicate> {
        // Parse a tiny theory containing only `predicates: <decl>`.
        let src = format!("theory T begin\npredicates: {}\nend", decl);
        let thy = tamarin_parser::parse_theory(&src, &[]).unwrap();
        thy.items.into_iter().filter_map(|it| match it {
            p::TheoryItem::Predicates(ps) => Some(ps),
            _ => None,
        }).flatten().collect()
    }

    #[test]
    fn expand_simple_predicate() {
        // P(x) <=> A(x) @ #i  (note: x is bound in the use-site, #i not).
        let preds = pred("P(x) <=> Ex #i. A(x) @ #i");
        let f = parse_formula_str("All x. P(x)").unwrap();
        let expanded = expand_formula(&f, &preds).unwrap();
        // Should NO LONGER contain a Pred atom.
        assert!(!has_pred_atom(&expanded), "got {:?}", expanded);
    }

    #[test]
    fn expand_undefined_predicate_errors() {
        let preds: Vec<p::Predicate> = Vec::new();
        let f = parse_formula_str("All x. UndefinedPred(x)").unwrap();
        let res = expand_formula(&f, &preds);
        // `UndefinedPred(x)` parses as a `Pred` atom; with no matching
        // predicate, expansion reports `UndefinedPredicate`.  HS renders it
        // (Theory/Text/Parser/Exceptions.hs:33-34 + Fact.hs:519-527) as
        // `undefined predicate <name>/<arity>` (leading `!` if persistent).
        // Probed against the v1.13.0 prover: `... ==> P(x)` reports
        // `undefined predicate P/1`.
        let err = res.expect_err("expected undefined-predicate error");
        assert_eq!(err.message, "undefined predicate UndefinedPred/1");
    }

    #[test]
    fn expand_arity_mismatch_is_undefined_predicate() {
        // HS `lookupPredicate` (Predicate.hs:76-80) matches the FULL
        // `FactTag` (multiplicity + name + arity).  A use-site whose arity
        // differs from the declared predicate does not match and falls
        // through to `UndefinedPredicate`.  Probed against the v1.13.0
        // prover: `predicates: P(x) <=> ...` used as `P(a, b)` reports
        // `undefined predicate P/2` — NOT a bespoke "arity mismatch".
        let preds = pred("P(x) <=> Ex #i. A(x) @ #i");
        let f = parse_formula_str("All a b. P(a, b)").unwrap();
        let err = expand_formula(&f, &preds).expect_err("expected error");
        assert_eq!(err.message, "undefined predicate P/2");
    }

    #[test]
    fn case_test_and_acc_lemma_keep_pred_atoms() {
        // HS adds case-tests / acc-lemmas verbatim (liftedAddCaseTest /
        // liftedAddAccLemma, Theory/Text/Parser.hs:152-163) with NO
        // predicate expansion — their `Pred` sugar stays intact for the
        // accountability translation.  `expand_theory_formulas` must NOT
        // expand them; a regular lemma over the same predicate IS expanded.
        let src = "theory T begin\n\
            predicates: P(x) <=> Ex #i. A(x) @ #i\n\
            test ct:\n  \"P(a)\"\n\
            lemma acc:\n  ct account for\n    \"All x. P(x)\"\n\
            lemma reg:\n  \"All x. P(x)\"\n\
            end";
        let mut thy = tamarin_parser::parse_theory(src, &[]).unwrap();
        expand_theory_formulas(&mut thy).unwrap();
        let mut saw_ct = false;
        let mut saw_acc = false;
        let mut saw_reg = false;
        for item in &thy.items {
            match item {
                p::TheoryItem::CaseTest(c) => {
                    saw_ct = true;
                    assert!(has_pred_atom(&c.formula),
                        "case-test must keep too its Pred atom: {:?}", c.formula);
                }
                p::TheoryItem::AccLemma(a) => {
                    saw_acc = true;
                    assert!(has_pred_atom(&a.formula),
                        "acc-lemma must keep its Pred atom: {:?}", a.formula);
                }
                p::TheoryItem::Lemma(l) => {
                    saw_reg = true;
                    assert!(!has_pred_atom(&l.formula),
                        "regular lemma must be expanded: {:?}", l.formula);
                }
                _ => {}
            }
        }
        assert!(saw_ct && saw_acc && saw_reg,
            "expected all three item kinds (ct={saw_ct}, acc={saw_acc}, reg={saw_reg})");
    }

    #[test]
    fn expand_avoids_variable_capture() {
        // P(x) <=> Ex z #i. Act(x, z) @ #i.  Applying it at use-site P(z)
        // (free z) must NOT let the body's `Ex z` capture the substituted
        // z: the binder is alpha-renamed, so no surviving quantifier binds
        // `z`.  (Without capture-avoidance the body became Act(z, z).)
        let preds = pred("P(x) <=> Ex z #i. Act(x, z) @ #i");
        let f = parse_formula_str("P(z)").unwrap();
        let expanded = expand_formula(&f, &preds).unwrap();
        assert!(!binds_var_named(&expanded, "z"),
            "variable capture: a quantifier still binds `z`: {:?}", expanded);
    }

    #[test]
    fn expand_lessmset_to_smaller_existential() {
        // The multiset `(<)` operator has no dedicated atom in HS: it parses
        // to `Pred Smaller` and `expandFormula` rewrites it to
        // `∃ z. rhs = lhs ++ z`.  Probed against the real HS prover (v1.13.0)
        // on `All x y #i. Foo(x,y)@#i ==> x (<) y`, which prints
        //   ∀ x y #i. (Foo( x, y ) @ #i) ⇒ (∃ z. y = (x++z))
        // so a bare `x (<) y` expands to `∃ z. y = (x++z)`.
        let preds: Vec<p::Predicate> = Vec::new();
        let f = parse_formula_str("x (<) y").unwrap();
        let expanded = expand_formula(&f, &preds).unwrap();
        // `LessMset` must be gone (no `(<)` reaches the pretty-printer).
        assert!(
            !has_lessmset_atom(&expanded),
            "LessMset survived expansion: {:?}",
            expanded
        );
        let printed = crate::pretty_formula::pretty_formula(&expanded);
        assert_eq!(printed, "\u{2203} z. y = (x++z)", "got {:?}", expanded);
        assert!(!printed.contains("(<)"), "still emits (<): {}", printed);
    }

    #[test]
    fn expand_lessmset_capture_avoids_z() {
        // Use-site that mentions `z` must not be captured by the bound `z`.
        let preds: Vec<p::Predicate> = Vec::new();
        let f = parse_formula_str("z (<) y").unwrap();
        let expanded = expand_formula(&f, &preds).unwrap();
        // The bound var is renamed away from `z` (HS would pick a fresh name);
        // the use-site `z` survives in the union term.
        assert!(!has_lessmset_atom(&expanded), "got {:?}", expanded);
    }

    fn has_lessmset_atom(f: &p::Formula) -> bool {
        match f {
            p::Formula::Atom(p::Atom::LessMset(_, _)) => true,
            p::Formula::True | p::Formula::False | p::Formula::Atom(_) => false,
            p::Formula::Not(g) => has_lessmset_atom(g),
            p::Formula::And(a, b) | p::Formula::Or(a, b)
            | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) =>
                has_lessmset_atom(a) || has_lessmset_atom(b),
            p::Formula::Forall(_, b) | p::Formula::Exists(_, b) => has_lessmset_atom(b),
        }
    }

    fn binds_var_named(f: &p::Formula, name: &str) -> bool {
        match f {
            p::Formula::True | p::Formula::False | p::Formula::Atom(_) => false,
            p::Formula::Not(g) => binds_var_named(g, name),
            p::Formula::And(a, b) | p::Formula::Or(a, b)
            | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) =>
                binds_var_named(a, name) || binds_var_named(b, name),
            p::Formula::Forall(vs, b) | p::Formula::Exists(vs, b) =>
                vs.iter().any(|v| v.name == name) || binds_var_named(b, name),
        }
    }

    fn has_pred_atom(f: &p::Formula) -> bool {
        match f {
            p::Formula::Atom(p::Atom::Pred(_)) => true,
            p::Formula::True | p::Formula::False => false,
            p::Formula::Atom(_) => false,
            p::Formula::Not(g) => has_pred_atom(g),
            p::Formula::And(a, b) | p::Formula::Or(a, b)
            | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) => {
                has_pred_atom(a) || has_pred_atom(b)
            }
            p::Formula::Forall(_, b) | p::Formula::Exists(_, b) => has_pred_atom(b),
        }
    }
}
