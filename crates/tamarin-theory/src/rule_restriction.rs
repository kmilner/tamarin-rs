// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of HS `liftedAddProtoRule` (Theory/Text/Parser.hs:166-193) +
//! `fromRuleRestriction` / `rewrite` (Theory/Model/Restriction.hs:90-162).
//!
//! Expands the `_restrict(...)` embedded-restriction construct that the
//! parser captures into `Rule.embedded_restrictions: Vec<Formula>`
//! (parser `ast.rs`).  For each such formula, HS:
//!   1. expands predicate atoms (`liftedExpandFormula`),
//!   2. abstracts every subterm containing free variables into a fresh
//!      `x`/`x.1`/… var (`rewrite`),
//!   3. builds a fresh restriction `Restr_<rule>_<i>` whose body is
//!      `∀ <frees>. (Restr_<rule>_<i>(<free-var terms>) @ #NOW) ⇒ φ'`,
//!   4. inserts that restriction BEFORE the rule, and
//!   5. appends the action `Restr_<rule>_<i>(<original abstracted terms>)`
//!      to the rule's actions.
//!
//! The rule keeps its `_restrict` formulas: HS's `addActions` rebuilds only
//! `rActs` (Theory/Text/Parser.hs:188), so `preRestriction` survives on every
//! closed rule and `elaborate::rule_to_proto_rule_e` carries the same
//! formulas onto `ProtoRuleEInfo.restrictions`.
//!
//! HS performs this DURING parsing (the parser calls `liftedAddProtoRule`
//! per rule, building the `OpenTheory` with restrictions inserted and
//! actions rewritten).  The RS port mirrors that by running this pass over
//! the parser-AST theory `parsed` right after `parse_theory`, so the
//! transformed theory drives BOTH wellformedness/elaboration AND
//! pretty-printing (the renderer iterates the parser AST).
//!
//! We operate on parser-AST `Formula`/`Term`/`Fact` throughout — the same
//! universe `predicate_expand::expand_formula` works in — so the generated
//! restriction flows through `render_parsed_restriction` and the rewritten
//! action through `render_rule` unchanged.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;
use tamarin_term::lterm::LSort;

use crate::predicate_expand::{expand_formula, ExpandError};

/// HS `varNow = LVar "NOW" LSortNode 0` (Theory/Model/Restriction.hs:87-88).
/// The implicit
/// timepoint variable bound by the generated `∀ … #NOW.` restriction.
fn var_now() -> p::VarSpec {
    p::VarSpec {
        name: "NOW".to_string(),
        idx: 0,
        sort: LSort::Node,
        typ: None,
    }
}

/// HS `restrPrefix = "Restr_"` (Theory/Model/Restriction.hs:130-131).
const RESTR_PREFIX: &str = "Restr_";

/// Run the `_restrict` lifting pass over a parsed theory in place.
///
/// Mirrors HS `liftedAddProtoRule` invoked per rule during parsing.  For
/// every `TheoryItem::Rule` carrying `embedded_restrictions`, generate the
/// `Restr_<rule>_<i>` restrictions (inserted immediately before the rule)
/// and append the `Restr_<rule>_<i>` actions to the rule.
///
/// Run it exactly ONCE per parsed theory: the rule keeps its `_restrict`
/// formulas, so a second call generates a second copy of every restriction
/// and appends the actions again.  The production callers are `run.rs`'s
/// per-file pipeline and the web server's `theory_io`.
///
/// Predicate atoms inside each `_restrict` formula are expanded against the
/// theory's `predicate:` declarations first (HS `liftedExpandFormula`).
/// `let` bindings reach the rule body from the parser, so the abstracted
/// terms see their expansions (HS applies `let` in `protoRule`,
/// Theory/Text/Parser/Rule.hs:133).
pub fn lift_rule_restrictions(thy: &mut p::Theory) -> Result<(), ExpandError> {
    // Collect predicate definitions once (declared before the rules).
    let predicates: Vec<p::Predicate> = thy
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Predicates(ps) => Some(ps.clone()),
            _ => None,
        })
        .flatten()
        .collect();
    // Build a new item list, expanding rules-with-restrictions into
    // [generated restrictions..., rewritten rule].  Other items pass
    // through untouched.
    let mut new_items: Vec<p::TheoryItem> = Vec::with_capacity(thy.items.len());
    for item in std::mem::take(&mut thy.items) {
        match item {
            p::TheoryItem::Rule(rule) if !rule.embedded_restrictions.is_empty() => {
                let (restrs, new_rule) = lift_one_rule(rule, &predicates)?;
                // HS adds the restrictions to the theory accumulated so far,
                // THEN adds the rule → restrictions precede the rule.
                for r in restrs {
                    new_items.push(p::TheoryItem::Restriction(r));
                }
                new_items.push(p::TheoryItem::Rule(new_rule));
            }
            other => new_items.push(other),
        }
    }
    thy.items = new_items;
    Ok(())
}

/// Lift one rule's embedded restrictions.  Returns the generated
/// restrictions (in `1..n` order) and the rewritten rule.
///
/// Public so the SAPIC translation (`tamarin_sapic::apply`) can run the same
/// `_restrict` expansion HS `liftedAddProtoRule` performs, over the rules it
/// synthesises, injecting the generated restrictions + rewritten actions into
/// both the parsed and elaborated theories.
pub fn lift_one_rule(
    mut rule: p::Rule,
    predicates: &[p::Predicate],
) -> Result<(Vec<p::Restriction>, p::Rule), ExpandError> {
    let rname = rule.name.clone();
    let n = rule.embedded_restrictions.len();
    let mut restrictions: Vec<p::Restriction> = Vec::with_capacity(n);
    let mut new_actions: Vec<p::Fact> = Vec::with_capacity(n);

    // HS `counter = zip [1..]`: 1-indexed.
    for (i, phi) in rule.embedded_restrictions.iter().enumerate() {
        let idx = i + 1;
        // HS `liftedExpandFormula thy` — expand predicate atoms.
        let expanded = expand_formula(phi, predicates)?;
        // HS `fromRuleRestriction (rname ++ "_" ++ show i) f`.
        let sub_name = format!("{}_{}", rname, idx);
        let (restr, action) = from_rule_restriction(&sub_name, &expanded);
        restrictions.push(restr);
        new_actions.push(action);
    }

    // HS `addActions = modify rActs (++ actions)`: APPEND the restriction
    // actions after the rule's existing actions.  `addActions` rebuilds only
    // `rActs`, so the rule keeps its `_restrict` formulas
    // (Theory/Text/Parser.hs:188).
    rule.actions.extend(new_actions);
    Ok((restrictions, rule))
}

/// HS `fromRuleRestriction rname f` (Theory/Model/Restriction.hs:141-162):
/// produce the
/// generated restriction plus the action fact inserted into the rule.
fn from_rule_restriction(rname: &str, f: &p::Formula) -> (p::Restriction, p::Fact) {
    // HS `rewrite f` returns `(rewritten formula, M.Map LVar Term)`.
    let (rewr_f, subst) = rewrite(f);

    // --- the restriction ----------------------------------------------
    // HS `mkRestriction f' = Restriction (restrPrefix++rname)
    //        (foldr (hinted forAll) f'' (frees f'')) Nothing`
    //   where f'' = (Action #NOW fact) ==> f'
    //         fact = mkFact (getBVarTerms f')
    //         getBVarTerms = map (varTerm.Free) . delete varNow . freesList
    // `frees_list(&rewr_f)` is consumed twice (here and for `action_args`);
    // compute it once since it is a pure function of the unchanged `rewr_f`.
    let rewr_frees = frees_list(&rewr_f);
    let bvar_terms: Vec<p::Term> = rewr_frees
        .iter()
        .filter(|v| !is_var_now(v))
        .cloned()
        .map(p::Term::Var)
        .collect();
    let restr_fact = mk_fact(rname, bvar_terms);
    // f'' = (Restr_<rname>(...) @ #NOW) ⇒ f'
    let now_term = p::Term::Var(var_now());
    let antecedent = p::Formula::Atom(p::Atom::Action(restr_fact, now_term));
    let f2 = p::Formula::Implies(Box::new(antecedent), Box::new(rewr_f.clone()));
    // foldr forAll f'' (frees f''): bind ALL free vars of f'' (sorted,
    // dedup), outermost-first matching HS `foldr`.
    let quant_vars = frees_sorted(&f2);
    let restr_formula = if quant_vars.is_empty() {
        f2
    } else {
        p::Formula::Forall(quant_vars, Box::new(f2))
    };
    let restriction = p::Restriction {
        name: format!("{}{}", RESTR_PREFIX, rname),
        formula: restr_formula,
        attributes: Vec::new(),
    };

    // --- the action fact inserted into the rule -----------------------
    // HS `mkFact $ getVarTerms (rewrSubst f) (rewrF f)` where
    //   getVarTerms subst = map (apply subst . varTerm) . delete varNow . freesList
    // i.e. for each free var of the rewritten formula (minus NOW), look up
    // the ORIGINAL term it abstracted; vars with no entry stay themselves.
    let action_args: Vec<p::Term> = rewr_frees
        .into_iter()
        .filter(|v| !is_var_now(v))
        .map(|v| match subst.get(&var_full_key(&v)) {
            Some(t) => t.clone(),
            None => p::Term::Var(v),
        })
        .collect();
    let action = mk_fact(rname, action_args);

    (restriction, action)
}

/// HS `mkFact = protoFactAnn Linear (restrPrefix ++ rname) S.empty`
/// (Theory/Model/Restriction.hs:162): a linear fact named `Restr_<rname>`.
fn mk_fact(rname: &str, args: Vec<p::Term>) -> p::Fact {
    p::Fact {
        persistent: false,
        name: format!("{}{}", RESTR_PREFIX, rname),
        args,
        annotations: Vec::new(),
    }
}

// =============================================================================
// rewrite (HS Theory/Model/Restriction.hs:90-128)
// =============================================================================

/// A fresh-variable substitution: maps each minted fresh var (by [`VarKey`])
/// to the ORIGINAL term it abstracted.
type RewriteSubst = BTreeMap<VarKey, p::Term>;

/// HS `rewrite f = runState (evalFreshT (traverseFormulaAtom fAt' f) 0) M.empty`
/// (Theory/Model/Restriction.hs:92-128, see line 96): traverse every term of
/// every atom, abstracting
/// subterms that contain free variables into fresh vars.  Returns the
/// rewritten formula and the `{fresh ↦ original}` map.
fn rewrite(f: &p::Formula) -> (p::Formula, RewriteSubst) {
    let mut st = RewriteState {
        counter: 0,
        subst: RewriteSubst::new(),
    };
    let bound: Vec<VarKey> = Vec::new();
    let out = rewrite_formula(f, &bound, &mut st);
    (out, st.subst)
}

struct RewriteState {
    /// HS `evalFreshT … 0` fresh counter: 0 → `x`, 1 → `x.1`, …
    counter: u64,
    subst: RewriteSubst,
}

impl RewriteState {
    /// HS `substitute t' = do v <- freshLVar "x" LSortMsg; … return varTerm (Free v)`.
    /// Mint a fresh `LSortMsg` var, record `{v ↦ t}`, return `Var(v)`.
    fn substitute(&mut self, t: &p::Term) -> p::Term {
        let idx = self.counter;
        self.counter += 1;
        let v = p::VarSpec {
            name: "x".to_string(),
            idx,
            sort: LSort::Msg,
            typ: None,
        };
        self.subst.insert(var_full_key(&v), t.clone());
        p::Term::Var(v)
    }
}

/// Traverse a formula's atoms (HS `traverseFormulaAtom`), rewriting their
/// terms.  `bound` carries the variables (full identity) bound by enclosing
/// quantifiers.
fn rewrite_formula(f: &p::Formula, bound: &[VarKey], st: &mut RewriteState) -> p::Formula {
    use p::Formula::*;
    match f {
        True | False => f.clone(),
        Atom(a) => Atom(rewrite_atom(a, bound, st)),
        Not(g) => Not(Box::new(rewrite_formula(g, bound, st))),
        And(a, b) => And(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Or(a, b) => Or(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Implies(a, b) => Implies(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Iff(a, b) => Iff(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Forall(vs, body) => {
            let mut b2 = bound.to_vec();
            for v in vs {
                b2.push(var_full_key(v));
            }
            Forall(vs.clone(), Box::new(rewrite_formula(body, &b2, st)))
        }
        Exists(vs, body) => {
            let mut b2 = bound.to_vec();
            for v in vs {
                b2.push(var_full_key(v));
            }
            Exists(vs.clone(), Box::new(rewrite_formula(body, &b2, st)))
        }
    }
}

fn rewrite_atom(a: &p::Atom, bound: &[VarKey], st: &mut RewriteState) -> p::Atom {
    use p::Atom::*;
    match a {
        Eq(l, r) => Eq(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        Less(l, r) => Less(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        LessMset(l, r) => LessMset(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        Subterm(l, r) => Subterm(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        Action(fa, t) => {
            let fa2 = p::Fact {
                persistent: fa.persistent,
                name: fa.name.clone(),
                args: fa.args.iter().map(|x| rewrite_term(x, bound, st)).collect(),
                annotations: fa.annotations.clone(),
            };
            Action(fa2, rewrite_term(t, bound, st))
        }
        Last(t) => Last(rewrite_term(t, bound, st)),
        // A `Pred` should never survive predicate expansion, but rewrite it
        // structurally just in case (HS would also traverse it).
        Pred(fa) => {
            let fa2 = p::Fact {
                persistent: fa.persistent,
                name: fa.name.clone(),
                args: fa.args.iter().map(|x| rewrite_term(x, bound, st)).collect(),
                annotations: fa.annotations.clone(),
            };
            Pred(fa2)
        }
    }
}

/// HS `fAt` (Theory/Model/Restriction.hs:99-112): the per-term abstraction.
///   - `Var v`, v free            → substitute (fresh var)
///   - `Var _`, v bound           → keep
///   - `FApp _ as`, any free & no bound → substitute the WHOLE term
///   - `FApp f as`, any free & any bound → recurse into args
///   - otherwise                  → keep
///
/// where free/bound are computed with `varNow` treated as NOT free.
fn rewrite_term(t: &p::Term, bound: &[VarKey], st: &mut RewriteState) -> p::Term {
    match t {
        p::Term::Var(v) => {
            if is_free(v, bound) {
                st.substitute(t)
            } else {
                t.clone()
            }
        }
        // Compound terms: App / Pair / AlgApp / Diff / BinOp.  HS treats
        // every non-Lit as `FApp _ as`; mirror by classifying on the args.
        _ => {
            let args = term_children(t);
            if args.is_empty() {
                // No sub-terms (e.g. literals / nullary App) → keep.
                return t.clone();
            }
            let any_free = args.iter().any(|c| contains_free(c, bound));
            let any_bound = args.iter().any(|c| contains_bound(c, bound));
            if any_free && !any_bound {
                st.substitute(t)
            } else if any_free && any_bound {
                rebuild_term(t, |c| rewrite_term(c, bound, st))
            } else {
                t.clone()
            }
        }
    }
}

/// Identity of a parser-AST variable for bound-tracking: `(name, idx, sort)`.
/// HS builds the de Bruijn body with `quantify x`, which replaces exactly the
/// occurrences satisfying `v == x` (Theory/Model/Formula.hs:347-352), and
/// `Eq LVar` compares index, sort and name (Term/LTerm.hs:541-542); the
/// free/bound split `rewrite` reads (Theory/Model/Restriction.hs:99-112) is
/// the one `quantify` produced.  A body occurrence is bound only when
/// it agrees with the binder in all three components: a node-sorted `#i` and a
/// message-sorted `i` are distinct variables, as are the equation's `k`
/// (idx 0) and the process's `k.1` (idx 1) in a let-destructor restriction.
type VarKey = (String, u64, LSort);

fn var_full_key(v: &p::VarSpec) -> VarKey {
    (v.name.clone(), v.idx, v.sort)
}

/// HS `isFree (Bound _) = False; isFree (Free v) = v /= varNow`.
/// In the parser AST a var is "bound" if it is the very variable (full
/// identity) introduced by an enclosing quantifier; the special `#NOW` node
/// var is treated as not-free.
fn is_free(v: &p::VarSpec, bound: &[VarKey]) -> bool {
    if bound.contains(&var_full_key(v)) {
        return false;
    }
    !is_var_now(v)
}

/// HS `containsVar p t`: does `t` mention a variable satisfying `p`?
fn contains_var(t: &p::Term, bound: &[VarKey], free_pred: bool) -> bool {
    match t {
        p::Term::Var(v) => {
            let free = is_free(v, bound);
            if free_pred {
                free
            } else {
                !free
            }
        }
        _ => term_children(t)
            .iter()
            .any(|c| contains_var(c, bound, free_pred)),
    }
}

fn contains_free(t: &p::Term, bound: &[VarKey]) -> bool {
    contains_var(t, bound, true)
}

fn contains_bound(t: &p::Term, bound: &[VarKey]) -> bool {
    contains_var(t, bound, false)
}

/// Direct sub-terms of a compound term (the `as` in HS `FApp _ as`).
fn term_children(t: &p::Term) -> Vec<&p::Term> {
    match t {
        p::Term::App(_, args) | p::Term::Pair(args) => args.iter().collect(),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            vec![a, b]
        }
        p::Term::PatMatch(inner) => vec![inner.as_ref()],
        _ => Vec::new(),
    }
}

/// Rebuild a compound term, mapping `f` over its direct children.
fn rebuild_term(t: &p::Term, mut f: impl FnMut(&p::Term) -> p::Term) -> p::Term {
    match t {
        p::Term::App(name, args) => p::Term::App(name.clone(), args.iter().map(&mut f).collect()),
        p::Term::Pair(items) => p::Term::Pair(items.iter().map(&mut f).collect()),
        p::Term::AlgApp(name, a, b) => {
            p::Term::AlgApp(name.clone(), Box::new(f(a)), Box::new(f(b)))
        }
        p::Term::Diff(a, b) => p::Term::Diff(Box::new(f(a)), Box::new(f(b))),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(*op, Box::new(f(a)), Box::new(f(b))),
        p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(f(inner))),
        other => other.clone(),
    }
}

// =============================================================================
// frees / freesList over the rewritten formula
// =============================================================================

/// Is this var the special `#NOW` timepoint (HS `varNow`)?
fn is_var_now(v: &p::VarSpec) -> bool {
    v.name == "NOW" && matches!(v.sort, LSort::Node) && v.idx == 0
}

/// NOTE: unlike HS `freesList` (LTerm.hs = `D.toList . freesDList`)
/// which KEEPS duplicates, this dedups by first appearance via `dedup_first`.
/// Safe only because every caller passes a post-`rewrite` formula where each
/// free var is a unique fresh var, so the dedup is a no-op. (HS's sorted-dedup
/// variant `frees` is also in LTerm.hs.)
fn frees_list(f: &p::Formula) -> Vec<p::VarSpec> {
    let mut out: Vec<p::VarSpec> = Vec::new();
    let mut bound: Vec<VarKey> = Vec::new();
    collect_frees_formula(f, &mut bound, &mut out);
    dedup_first(out)
}

/// HS `frees = sortednub . freesList`: sorted (by LVar Ord) and dedup.
fn frees_sorted(f: &p::Formula) -> Vec<p::VarSpec> {
    let mut vs = frees_list(f);
    vs.sort_by(cmp_lvar);
    vs.dedup_by(|a, b| cmp_lvar(a, b) == std::cmp::Ordering::Equal);
    vs
}

fn dedup_first(vs: Vec<p::VarSpec>) -> Vec<p::VarSpec> {
    let mut seen: std::collections::BTreeSet<VarKey> = std::collections::BTreeSet::new();
    let mut out = Vec::with_capacity(vs.len());
    for v in vs {
        if seen.insert(var_full_key(&v)) {
            out.push(v);
        }
    }
    out
}

/// HS `LVar` Ord: `compare idx <> compare sort <> compare name`
/// (LTerm.hs:546-548).  LSort order: Pub < Fresh < Msg < Node < Nat
/// (the derived `Ord`'s constructor order, LTerm.hs:165-170).
fn cmp_lvar(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx
        .cmp(&b.idx)
        .then(a.sort.cmp(&b.sort))
        .then(a.name.cmp(&b.name))
}

fn collect_frees_formula(f: &p::Formula, bound: &mut Vec<VarKey>, out: &mut Vec<p::VarSpec>) {
    use p::Formula::*;
    match f {
        True | False => {}
        Atom(a) => collect_frees_atom(a, bound, out),
        Not(g) => collect_frees_formula(g, bound, out),
        And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
            collect_frees_formula(a, bound, out);
            collect_frees_formula(b, bound, out);
        }
        Forall(vs, body) | Exists(vs, body) => {
            let saved = bound.len();
            for v in vs {
                bound.push(var_full_key(v));
            }
            collect_frees_formula(body, bound, out);
            bound.truncate(saved);
        }
    }
}

fn collect_frees_atom(a: &p::Atom, bound: &[VarKey], out: &mut Vec<p::VarSpec>) {
    use p::Atom::*;
    match a {
        Eq(l, r) | Less(l, r) | LessMset(l, r) | Subterm(l, r) => {
            collect_frees_term(l, bound, out);
            collect_frees_term(r, bound, out);
        }
        Action(fa, t) => {
            for arg in &fa.args {
                collect_frees_term(arg, bound, out);
            }
            collect_frees_term(t, bound, out);
        }
        Last(t) => collect_frees_term(t, bound, out),
        Pred(fa) => {
            for arg in &fa.args {
                collect_frees_term(arg, bound, out);
            }
        }
    }
}

fn collect_frees_term(t: &p::Term, bound: &[VarKey], out: &mut Vec<p::VarSpec>) {
    match t {
        p::Term::Var(v) => {
            if !bound.contains(&var_full_key(v)) {
                out.push(v.clone());
            }
        }
        _ => {
            for c in term_children(t) {
                collect_frees_term(c, bound, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parser::parse_formula_str;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn preds(decl: &str) -> Vec<p::Predicate> {
        // `functions:` declares the symbols the predicate bodies apply —
        // the parser resolves prefix applications through `lookupArity`
        // (like HS) and an undeclared head would reparse as a variable and
        // fail, as in `lift_inserts_restriction_before_rule`'s theory.
        let src = format!(
            "theory T begin\nfunctions: true/0, eq/2\npredicates: {}\nend",
            decl
        );
        let thy = tamarin_parser::parse_theory(&src, &[]).unwrap();
        thy.items
            .into_iter()
            .filter_map(|it| match it {
                p::TheoryItem::Predicates(ps) => Some(ps),
                _ => None,
            })
            .flatten()
            .collect()
    }

    #[test]
    fn minimal_trace() {
        // True(x) <=> (x = true()); restriction True(eq(x,x)).
        let ps = preds("True(x) <=> (x = true())");
        let phi = parse_formula_str("True(eq(x, x))", &pair_maude_sig()).unwrap();
        let expanded = expand_formula(&phi, &ps).unwrap();
        let (restr, action) = from_rule_restriction("A_1", &expanded);
        // Restriction name.
        assert_eq!(restr.name, "Restr_A_1");
        // Action fact name + ORIGINAL args.
        assert_eq!(action.name, "Restr_A_1");
        assert_eq!(action.args.len(), 1);
        // The single abstracted arg is the ORIGINAL eq(x,x).
        match &action.args[0] {
            p::Term::App(n, args) => {
                assert_eq!(n, "eq");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected eq(x,x), got {:?}", other),
        }
        // Restriction formula: ∀ x #NOW. (Restr_A_1(x) @ #NOW) ⇒ (x = true)
        let p::Formula::Forall(vs, body) = &restr.formula else {
            panic!("expected forall, got {:?}", restr.formula);
        };
        // The formula has two binders.  They are the abstracted x (Msg) and
        // #NOW (Node), in the sorted order x then NOW.
        assert_eq!(vs.len(), 2);
        assert_eq!((vs[0].name.as_str(), vs[0].sort), ("x", LSort::Msg));
        assert_eq!((vs[1].name.as_str(), vs[1].sort), ("NOW", LSort::Node));
        // HS `f'' = (Action #NOW fact) ==> f'`.  The generated action is the
        // antecedent, and the rewritten body is the consequent.  A swap of the
        // two keeps the formula an `Implies`, but it inverts the meaning of
        // the restriction.
        let p::Formula::Implies(ante, conseq) = &**body else {
            panic!("expected implication, got {:?}", body);
        };
        assert_eq!(
            **ante,
            p::Formula::Atom(p::Atom::Action(
                p::Fact {
                    persistent: false,
                    name: "Restr_A_1".to_string(),
                    args: vec![p::Term::Var(vs[0].clone())],
                    annotations: Vec::new(),
                },
                p::Term::Var(vs[1].clone()),
            ))
        );
        // The consequent is the body of the predicate.  The complete `eq(x,x)`
        // subterm becomes the fresh `x`.  The nullary constant `true` stays
        // inline as a 0-ary application.  The code never abstracts it.
        assert_eq!(
            **conseq,
            p::Formula::Atom(p::Atom::Eq(
                p::Term::Var(vs[0].clone()),
                p::Term::App("true".to_string(), Vec::new()),
            ))
        );
    }

    #[test]
    fn restriction_binder_identity_is_the_full_variable() {
        // `∀ #i` binds the node-sorted `i` only: the `i` in the message
        // position of `A(i)` is a different variable, stays free, and is
        // abstracted into the fresh `x`.
        let phi = parse_formula_str("All #i. A(i) @ #i", &pair_maude_sig()).unwrap();
        let (rewr, subst) = rewrite(&phi);
        let p::Formula::Forall(binders, body) = &rewr else {
            panic!("expected forall, got {:?}", rewr);
        };
        assert_eq!(
            (binders[0].name.as_str(), binders[0].sort),
            ("i", LSort::Node)
        );
        let p::Formula::Atom(p::Atom::Action(fact, tp)) = &**body else {
            panic!("expected an action atom, got {:?}", body);
        };
        let fresh = p::VarSpec {
            name: "x".to_string(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        };
        assert_eq!(fact.args, vec![p::Term::Var(fresh.clone())]);
        assert_eq!(*tp, p::Term::Var(binders[0].clone()));
        assert_eq!(
            subst.get(&var_full_key(&fresh)),
            Some(&p::Term::Var(p::VarSpec {
                name: "i".to_string(),
                idx: 0,
                sort: LSort::Msg,
                typ: None,
            }))
        );

        // `∀ x:msg` binds the message-sorted `x`, and the bare body `x` is
        // that variable: nothing is abstracted.
        let phi = parse_formula_str("All x:msg #i. A(x) @ #i", &pair_maude_sig()).unwrap();
        let (rewr, subst) = rewrite(&phi);
        assert!(subst.is_empty(), "nothing to abstract, got {:?}", subst);
        assert_eq!(rewr, phi);
    }

    #[test]
    fn lift_inserts_restriction_before_rule() {
        let src = "theory T begin\n\
            functions: true/0, eq/2\n\
            equations: eq(x,x)=x\n\
            predicate: True(x) <=> (x = true())\n\
            rule A:\n  [In(x)] --[ _restrict(True(eq(x,x))) ]-> []\n\
            end";
        let mut thy = tamarin_parser::parse_theory(src, &[]).unwrap();
        lift_rule_restrictions(&mut thy).unwrap();
        // Find rule A and the generated restriction.
        let restr_pos = thy.items.iter().position(|i| {
            matches!(i,
            p::TheoryItem::Restriction(r) if r.name == "Restr_A_1")
        });
        let rule_pos = thy.items.iter().position(|i| {
            matches!(i,
            p::TheoryItem::Rule(r) if r.name == "A")
        });
        let restr_pos = restr_pos.expect("restriction not generated");
        let rule_pos = rule_pos.expect("rule missing");
        // HS adds the generated restrictions to the accumulated theory, and it
        // adds the rule after them.  The restriction is therefore immediately
        // before the rule.
        assert_eq!(restr_pos + 1, rule_pos, "restriction must precede rule");
        // The pass appends the rule action and leaves the `_restrict`
        // formula on the rule.
        let p::TheoryItem::Rule(r) = &thy.items[rule_pos] else {
            panic!("item at {rule_pos} is not the rule");
        };
        assert_eq!(r.embedded_restrictions.len(), 1);
        assert_eq!(r.actions.len(), 1);
        assert_eq!(r.actions[0].name, "Restr_A_1");
        // The action carries the original term, without abstraction.
        assert_eq!(r.actions[0].args.len(), 1);
        assert!(
            matches!(&r.actions[0].args[0], p::Term::App(n, args) if n == "eq" && args.len() == 2),
            "action arg must be the original eq(x,x), got {:?}",
            r.actions[0].args[0]
        );
    }
}
