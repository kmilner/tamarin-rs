// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, jdreier, beschmi, Hong-Thai, PhilipLukertWork,
//   kevinmorio, BTom-GH, rsasse, xaDxelA, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/theory/src/Items/RuleItem.hs,
//   lib/theory/src/OpenTheory.hs, lib/theory/src/Prover.hs,
//   lib/theory/src/Rule.hs, lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/ProofSkeleton.hs

//! Port of Haskell's `--auto-sources` lemma generation
//! (`addAutoSourcesLemma`, `lib/theory/src/OpenTheory.hs:138-538`).
//!
//! When `--auto-sources` is set and the raw sources still contain open
//! chains (partial deconstructions), Tamarin generates a single `sources`
//! lemma that constrains every open-chain input variable: each input
//! subterm is tied to the earlier outputs it can unify with (via Maude) or
//! to the adversary's knowledge (`!KU`). Rules gain `AUTO_IN_*`/`AUTO_OUT_*`
//! action labels so the lemma can refer to those input/output events.
//!
//! This module builds the lemma **formula** as a parser-AST [`p::Formula`]
//! (the form RS stores and renders lemmas in), constructed to render
//! byte-identically to HS's `prettyLNFormula` of the `LNFormula` it builds.
//! The variable binders use HS's names (`x`, `m`/`m1..mn`, `i`, `j`).

use tamarin_parser::ast as p;
use tamarin_term::lterm::LNTerm;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::positions::{at_pos, deepest_prot_subterm, find_pos};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::all_prot_subterms;
use crate::constraint::constraints::{NodeConc, NodePrem};
use crate::constraint::system::System;
use crate::fact::{proto_or_in_fact_view, proto_or_out_fact_view, FactTag, LNFact, Multiplicity};
use crate::rule::{print_fact_position, print_position, rule_name_string, ExtendedPosition};
use crate::theory::{OpenProtoRule, TheoryItem};

/// Bound-variable names, matching HS's quantifier binders in
/// `addAutoSourcesLemma` (`OpenTheory.hs:399-535`).
fn var(name: &str, sort: p::SortHint) -> p::VarSpec {
    p::VarSpec { name: name.to_string(), idx: 0, sort, typ: None }
}
fn var_term(name: &str, sort: p::SortHint) -> p::Term {
    p::Term::Var(var(name, sort))
}

/// `inputFactTerm pos ru terms var` (OpenTheory.hs:138-538, see line 313): a linear proto fact
/// `AUTO_IN_TERM_<pos>_<rule>( terms.. , var )`.
fn input_fact_term(name: &str, terms: Vec<p::Term>, v: p::Term) -> p::Fact {
    let mut args = terms;
    args.push(v);
    p::Fact { persistent: false, name: name.to_string(), args, annotations: Vec::new() }
}

/// `outputFactTerm pos ru terms` (OpenTheory.hs:138-538, see line 333).
fn output_fact_term(name: &str, terms: Vec<p::Term>) -> p::Fact {
    p::Fact { persistent: false, name: name.to_string(), args: terms, annotations: Vec::new() }
}

fn action(fa: p::Fact, tp: p::Term) -> p::Formula {
    p::Formula::Atom(p::Atom::Action(fa, tp))
}
fn less(a: p::Term, b: p::Term) -> p::Formula {
    p::Formula::Atom(p::Atom::Less(a, b))
}
fn and(a: p::Formula, b: p::Formula) -> p::Formula {
    p::Formula::And(Box::new(a), Box::new(b))
}
fn or(a: p::Formula, b: p::Formula) -> p::Formula {
    p::Formula::Or(Box::new(a), Box::new(b))
}
fn implies(a: p::Formula, b: p::Formula) -> p::Formula {
    p::Formula::Implies(Box::new(a), Box::new(b))
}
fn exists(vs: Vec<p::VarSpec>, body: p::Formula) -> p::Formula {
    p::Formula::Exists(vs, Box::new(body))
}
fn forall(vs: Vec<p::VarSpec>, body: p::Formula) -> p::Formula {
    p::Formula::Forall(vs, Box::new(body))
}

const MSG: p::SortHint = p::SortHint::Msg;
const NODE: p::SortHint = p::SortHint::Node;

/// `orKU` (OpenTheory.hs:138-538, see line 484): `∃ j. !KU(x) @ j ∧ j < i`. Here `i` is the
/// input timepoint and `x` the input-term variable.
fn or_ku() -> p::Formula {
    let ku = p::Fact { persistent: true, name: "KU".to_string(), args: vec![var_term("x", MSG)], annotations: Vec::new() };
    exists(
        vec![var("j", NODE)],
        and(action(ku, var_term("j", NODE)), less(var_term("j", NODE), var_term("i", NODE))),
    )
}

/// `toFactsTerm ru p f''` (OpenTheory.hs:138-538, see line 502): `f'' ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i)`.
fn to_facts_term(out_name: &str, inner: p::Formula) -> p::Formula {
    let out = output_fact_term(out_name, vec![var_term("m", MSG)]);
    or(
        inner,
        exists(
            vec![var("j", NODE)],
            and(action(out, var_term("j", NODE)), less(var_term("j", NODE), var_term("i", NODE))),
        ),
    )
}

/// `addForm` protected-subterm case WITH matching outputs (OpenTheory.hs:138-538, see line 419):
/// `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒ (orKU ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i))`.
pub fn term_input_form_with_outputs(in_name: &str, out_name: &str) -> p::Formula {
    let in_fact = input_fact_term(in_name, vec![var_term("m", MSG)], var_term("x", MSG));
    forall(
        vec![var("x", MSG), var("m", MSG), var("i", NODE)],
        implies(
            action(in_fact, var_term("i", NODE)),
            to_facts_term(out_name, or_ku()),
        ),
    )
}

/// `addForm` protected-subterm case with NO matching outputs (OpenTheory.hs:138-538, see line 395):
/// `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒ orKU`.
pub fn term_input_form_no_outputs(in_name: &str) -> p::Formula {
    let in_fact = input_fact_term(in_name, vec![var_term("m", MSG)], var_term("x", MSG));
    forall(
        vec![var("x", MSG), var("m", MSG), var("i", NODE)],
        implies(action(in_fact, var_term("i", NODE)), or_ku()),
    )
}

// ---------------------------------------------------------------------------
// Fact-input cases (AUTO_*_FACT) — HS `addForm (_, Right _, _)` and
// `formulaMultArity` / `toFactsFact` (OpenTheory.hs:443-533).
// ---------------------------------------------------------------------------

/// `listOfM n` (OpenTheory.hs:138-538, see line 380): `["m1", "m2", ..., "mn"]`.
fn list_of_m(n: usize) -> Vec<String> {
    (1..=n).map(|k| format!("m{}", k)).collect()
}

fn input_fact_fact_ast(name: &str, ms: &[p::VarSpec]) -> p::Fact {
    p::Fact {
        persistent: false,
        name: name.to_string(),
        args: ms.iter().map(|v| p::Term::Var(v.clone())).collect(),
        annotations: Vec::new(),
    }
}

/// `addForm (_, Right (_, []), _)` (OpenTheory.hs:138-538, see line 443): no matching outputs →
/// `∀ m1..mn i. AUTO_IN_FACT(m1..mn) @ i ⇒ ⊥`.
fn fact_input_form_no_outputs(in_name: &str, arity: usize) -> p::Formula {
    let ms: Vec<p::VarSpec> = list_of_m(arity).iter().map(|n| var(n, MSG)).collect();
    let in_fact = input_fact_fact_ast(in_name, &ms);
    let mut binders = ms;
    binders.push(var("i", NODE));
    forall(binders, implies(action(in_fact, var_term("i", NODE)), p::Formula::False))
}

/// `addForm (_, Right (_, outs:_), _)` (OpenTheory.hs:138-538, see line 464): with a matching
/// output → `∀ m1..mn i. AUTO_IN_FACT(m1..mn) @ i ⇒ toFactsFact`.
/// `toFactsFact` (OpenTheory.hs): `∃ j. AUTO_OUT_FACT(m1..m{out_arity}) @ j ∧ j < i`
/// — the output fact references the input binders `m1..m{out_arity}`, highest first.
fn fact_input_form_with_outputs(in_name: &str, out_name: &str, in_arity: usize, out_arity: usize) -> p::Formula {
    let ms: Vec<p::VarSpec> = list_of_m(in_arity).iter().map(|n| var(n, MSG)).collect();
    let in_fact = input_fact_fact_ast(in_name, &ms);
    // toFactsFact: AUTO_OUT_FACT( listVarTerm (1 + out_arity) 2 ) — de-Bruijn
    // Bound (1+out_arity)..Bound 2 with j=Bound 0, i=Bound 1. So the output
    // fact references m1..m{out_arity} (the input binders), highest first.
    let out_ms: Vec<p::Term> = (1..=out_arity).map(|k| var_term(&format!("m{}", k), MSG)).collect();
    let out_fact = p::Fact { persistent: false, name: out_name.to_string(), args: out_ms, annotations: Vec::new() };
    let to_facts = exists(
        vec![var("j", NODE)],
        and(action(out_fact, var_term("j", NODE)), less(var_term("j", NODE), var_term("i", NODE))),
    );
    let mut binders = ms;
    binders.push(var("i", NODE));
    forall(binders, implies(action(in_fact, var_term("i", NODE)), to_facts))
}

// ---------------------------------------------------------------------------
// Discovery: walk the open chains, match inputs to outputs (OpenTheory.hs:144-538).
// ---------------------------------------------------------------------------

/// AUTO action facts (with CONCRETE rule terms) to add to a rule, plus the
/// generated source-lemma formula.
pub struct AutoSourcesResult {
    /// One `(rule E-name, action fact)` group per processed chain, in chain
    /// order; each group's facts are in HS `acts` order. HS applies
    /// `addLabels` per chain (foldr-prepend), so the caller must too — apply
    /// each group in order, reverse-iterating within the group and prepending.
    pub annotation_groups: Vec<Vec<(String, LNFact)>>,
    /// The source-lemma formula (parser AST), starting from `⊤`.
    pub formula: p::Formula,
}

fn ac_concs(o: &OpenProtoRule) -> &[LNFact] {
    match &o.abstracted_rule { Some(ar) => &ar.conclusions, None => &o.rule.conclusions }
}
fn ac_prems(o: &OpenProtoRule) -> &[LNFact] {
    match &o.abstracted_rule { Some(ar) => &ar.premises, None => &o.rule.premises }
}

fn ln_proto(name: &str, terms: Vec<LNTerm>) -> LNFact {
    crate::fact::proto_fact(Multiplicity::Linear, name, terms)
}

/// `t `renameAvoiding` avoid_set` (LTerm.hs): rename `t`'s vars to fresh
/// indices that avoid those in `avoid`.
fn rename_avoiding<T: tamarin_term::lterm::HasFrees>(t: T, avoid: &impl tamarin_term::lterm::HasFrees) -> T {
    let mut fresh = tamarin_term::lterm::avoid(avoid);
    tamarin_term::lterm::rename(t, &mut fresh)
}

/// One matched input together with its matching outputs.
enum Matched {
    /// protected-subterm input: deepest prot term, the var, matching (out-rule, out-term).
    Term { protterm: LNTerm, vin: LNTerm, outs: Vec<(usize, LNTerm)> },
    /// non-protected fact input: the fact, matching (out-rule, out-fact).
    Fact { fact: LNFact, outs: Vec<(usize, LNFact)> },
}

/// Build the `(AUTO_IN_*, AUTO_OUT_*)` fact-name pair for a matched input,
/// selecting `print_position` (Term) vs `print_fact_position` (Fact) by the
/// `Matched` variant.  Shared by the addFormula and addLabels loops so the
/// four AUTO_* name templates live in exactly one place.
fn auto_names(m: &Matched, pos: &ExtendedPosition, rin_name: &str) -> (String, String) {
    match m {
        Matched::Term { .. } => {
            let p = print_position(pos);
            (format!("AUTO_IN_TERM_{}_{}", p, rin_name),
             format!("AUTO_OUT_TERM_{}_{}", p, rin_name))
        }
        Matched::Fact { .. } => {
            let p = print_fact_position(pos);
            (format!("AUTO_IN_FACT_{}_{}", p, rin_name),
             format!("AUTO_OUT_FACT_{}_{}", p, rin_name))
        }
    }
}

/// Port of `addAutoSourcesLemma`'s body (OpenTheory.hs:144-538) without the
/// theory-item plumbing: given the protocol rules and the open-chain cases,
/// compute the rule AUTO annotations and the source-lemma formula.
pub fn add_auto_sources_lemma(
    maude: &MaudeHandle,
    rules: &[OpenProtoRule],
    chains: &[((NodeConc, NodePrem), System)],
) -> AutoSourcesResult {
    // allOutConcs: (rule idx, protected output subterm).
    let mut all_out_concs: Vec<(usize, LNTerm)> = Vec::new();
    // allOutConcsNotProt: (rule idx, non-Out conclusion fact).
    let mut all_out_concs_not_prot: Vec<(usize, LNFact)> = Vec::new();
    for (ri, ru) in rules.iter().enumerate() {
        for fa in ac_concs(ru) {
            if let Some(ts) = proto_or_out_fact_view(fa) {
                for t in &ts {
                    for sub in all_prot_subterms(t) {
                        all_out_concs.push((ri, sub));
                    }
                }
            }
            if fa.tag != FactTag::Out {
                all_out_concs_not_prot.push((ri, fa.clone()));
            }
        }
    }

    let mut formula = p::Formula::True;
    let mut annotation_groups: Vec<Vec<(String, LNFact)>> = Vec::new();
    let mut done: Vec<(String, ExtendedPosition)> = Vec::new();

    for ((conc, _prem), source) in chains {
        // v = head $ getFactTerms $ nodeConcFact conc source
        let Some(c_rule) = source.node_rule_safe(&conc.0) else { continue };
        let Some(conc_fact) = c_rule.conclusions.get(conc.1 .0) else { continue };
        let Some(v) = conc_fact.terms.first().cloned() else { continue };

        // unsolved premises of this source (for the fact-case guard).
        let unsolved_prem_keys: Vec<NodePrem> =
            source.unsolved_premises().into_iter().map(|(np, _)| np).collect();

        // inputRules: for each (nodeid, pid, tidx, term) in allPrems containing v.
        // Each element is (input-rule-idx, Left term | Right fact, position).
        enum InRule { Term(LNTerm), Fact(LNFact) }
        let mut input_rules: Vec<(usize, InRule, ExtendedPosition)> = Vec::new();
        for (nodeid, pid, tidx, term) in source.all_prems() {
            let Some(positions) = find_pos(&v, &term) else { continue };
            let Some(rule_sys) = source.node_rule_safe(&nodeid) else { continue };
            let sys_name = rule_name_string(rule_sys);
            let Some((ri, rule)) = rules.iter().enumerate().find(|(_, r)| r.name() == sys_name) else { continue };
            let Some(premise) = ac_prems(rule).get(pid.0) else { continue };
            let Some(t_prime) = proto_or_in_fact_view(premise) else { continue };
            let Some(t) = t_prime.get(tidx).cloned() else { continue };
            // terms (Left): one per found position.
            for pos in &positions {
                input_rules.push((ri, InRule::Term(t.clone()), (pid, tidx, pos.clone())));
            }
            // facts (Right): proto fact + (pair|AC|msgvar) + premise unsolved.
            let is_proto = matches!(premise.tag, FactTag::Proto(..));
            let t_is_eligible = tamarin_term::term::is_pair(&t)
                || tamarin_term::term::is_ac(&t)
                || tamarin_term::lterm::is_msg_var(&t);
            if is_proto && t_is_eligible && unsolved_prem_keys.contains(&(nodeid.clone(), pid)) {
                for pos in &positions {
                    input_rules.push((ri, InRule::Fact(premise.clone()), (pid, tidx, pos.clone())));
                }
            }
        }

        // premiseTermU: resolve Left terms to (deepest prot subterm, var).
        enum Unify { Term(LNTerm, LNTerm), Fact(LNFact) }
        let mut premise_term_u: Vec<(usize, Unify, ExtendedPosition)> = Vec::new();
        for (ri, inr, pos) in input_rules {
            match inr {
                InRule::Term(y) => {
                    let z = &pos.2;
                    let Some(v_prime) = at_pos(&y, z) else { continue };
                    let Some(prot_prime) = deepest_prot_subterm(&y, z) else { continue };
                    if prot_prime == v_prime { continue; } // HS: skip when prot == var
                    premise_term_u.push((ri, Unify::Term(prot_prime, v_prime), pos));
                }
                InRule::Fact(f) => premise_term_u.push((ri, Unify::Fact(f), pos)),
            }
        }

        // filterFacts + matchingConclusions → inputsAndOutputs.
        let has_subterm_case = premise_term_u.iter().any(|(_, u, _)| matches!(u, Unify::Term(..)));
        let mut matches: Vec<(usize, Matched, ExtendedPosition)> = Vec::new();
        for (ri, u, pos) in &premise_term_u {
            let rin_name = rules[*ri].name().to_string();
            match u {
                Unify::Term(protterm, vin) => {
                    if done.contains(&(rin_name.clone(), pos.clone())) { continue; }
                    let mut outs: Vec<(usize, LNTerm)> = Vec::new();
                    for (rout_i, tout) in &all_out_concs {
                        if rules[*rout_i].name() == rin_name { continue; }
                        let fout = rename_avoiding(tout.clone(), protterm);
                        if maude.unifiable(&[Equal { lhs: protterm.clone(), rhs: fout }]).unwrap_or(false) {
                            outs.push((*rout_i, tout.clone()));
                        }
                    }
                    matches.push((*ri, Matched::Term { protterm: protterm.clone(), vin: vin.clone(), outs }, pos.clone()));
                }
                Unify::Fact(fact) => {
                    if done.contains(&(rin_name.clone(), pos.clone())) || has_subterm_case { continue; }
                    let mut outs: Vec<(usize, LNFact)> = Vec::new();
                    for (rout_i, fout) in &all_out_concs_not_prot {
                        if rules[*rout_i].name() == rin_name { continue; }
                        if crate::fact::fact_tag_name(&fout.tag) != crate::fact::fact_tag_name(&fact.tag) { continue; }
                        let unifout = rename_avoiding(fout.clone(), fact);
                        if crate::rule::unifiable_ln_facts(maude, fact, &unifout).unwrap_or(false) {
                            outs.push((*rout_i, fout.clone()));
                        }
                    }
                    matches.push((*ri, Matched::Fact { fact: fact.clone(), outs }, pos.clone()));
                }
            }
        }

        // addFormula: foldr addForm formula matches (acc .&&. part(m)).
        for (ri, m, pos) in matches.iter().rev() {
            let rin_name = rules[*ri].name();
            let part = match m {
                Matched::Term { outs, .. } => {
                    let (in_name, out_name) = auto_names(m, pos, rin_name);
                    if outs.is_empty() {
                        term_input_form_no_outputs(&in_name)
                    } else {
                        term_input_form_with_outputs(&in_name, &out_name)
                    }
                }
                Matched::Fact { fact, outs } => {
                    let (in_name, out_name) = auto_names(m, pos, rin_name);
                    let in_arity = fact.terms.len();
                    if outs.is_empty() {
                        fact_input_form_no_outputs(&in_name, in_arity)
                    } else {
                        let out_arity = outs[0].1.terms.len();
                        fact_input_form_with_outputs(&in_name, &out_name, in_arity, out_arity)
                    }
                }
            };
            formula = and(formula, part);
        }

        // addLabels + addCases (this chain's acts as one group).
        let mut grp: Vec<(String, LNFact)> = Vec::new();
        for (ri, m, pos) in &matches {
            let rin_name = rules[*ri].name().to_string();
            match m {
                Matched::Term { protterm, vin, outs } => {
                    let (in_name, out_name) = auto_names(m, pos, &rin_name);
                    grp.push((rin_name.clone(), ln_proto(&in_name, vec![protterm.clone(), vin.clone()])));
                    for (rout_i, tout) in outs {
                        grp.push((rules[*rout_i].name().to_string(), ln_proto(&out_name, vec![tout.clone()])));
                    }
                }
                Matched::Fact { fact, outs } => {
                    let (in_name, out_name) = auto_names(m, pos, &rin_name);
                    grp.push((rin_name.clone(), ln_proto(&in_name, fact.terms.clone())));
                    for (rout_i, fout) in outs {
                        grp.push((rules[*rout_i].name().to_string(), ln_proto(&out_name, fout.terms.clone())));
                    }
                }
            }
            done.push((rin_name, pos.clone()));
        }
        annotation_groups.push(grp);
    }

    AutoSourcesResult { annotation_groups, formula }
}

/// Build the AUTO source lemma item (HS `unprovenLemma lemmaName [SourceLemma]
/// AllTraces formula`, OpenTheory.hs:138-538, see line 157).
pub fn build_source_lemma(name: &str, formula: p::Formula) -> crate::theory::Lemma {
    use crate::theory::{Lemma, LemmaAttr, TraceQuantifier};
    Lemma {
        name: name.to_string(),
        modulo: None,
        attributes: vec![LemmaAttr::Sources],
        trace_quantifier: TraceQuantifier::AllTraces,
        formula,
        proof: crate::theory::ProofSkeleton::unproven(),
        // HS `unprovenLemma` seeds `_lPlaintext` with "Unpr_inSkeleton"
        // (`Theory/ProofSkeleton.hs:59-61, see line 61`).
        plaintext: "Unpr_inSkeleton".to_string(),
    }
}

/// Whether the theory already contains a lemma named `name`
/// (HS `find lemma items`, OpenTheory.hs:138-538, see line 146).
pub fn has_lemma_named(items: &[TheoryItem], name: &str) -> bool {
    items.iter().any(|it| matches!(it, TheoryItem::Lemma(l) if l.name == name))
}

/// Add an AUTO action to an open proto rule's AC form. HS adds to
/// `cprRuleAC` only (Rule.hs:1026-1032, see line 1031); for a trivial-variant rule (no
/// abstracted form) that is the rule itself, which renders as
/// `rule (modulo E)` and propagates to its instances.
fn add_action_to_open_rule(o: &mut OpenProtoRule, action: LNFact) {
    if let Some(ar) = o.abstracted_rule.as_mut() {
        ar.add_action(action.clone());
    }
    o.rule.add_action(action);
}

/// Add an AUTO action (as an AST fact) to a parsed rule, prepended unless
/// already present — the parser-AST analogue of HS `addAction` used for the
/// rendered theory.
fn add_action_to_parsed_rule(r: &mut p::Rule, action: &p::Fact) {
    if !r.actions.contains(action) {
        r.actions.insert(0, action.clone());
    }
}

/// Build the parser-AST `AUTO_typing [sources]` lemma for the rendered theory.
fn build_parsed_source_lemma(name: &str, formula: p::Formula) -> p::Lemma {
    p::Lemma {
        name: name.to_string(),
        modulo: None,
        attributes: vec![p::LemmaAttr::Sources],
        trace_quantifier: p::TraceQuantifier::AllTraces,
        formula,
        proof: None,
        plaintext: String::new(),
    }
}

/// Apply `--auto-sources` (HS `closeTheoryWithMaude`'s autosources branch,
/// Prover.hs:171-226).  When the raw sources contain partial deconstructions,
/// annotate the rules with AUTO_* actions and append the `AUTO_typing` sources
/// lemma — to BOTH the parser-AST theory (`parsed`, drives rendering) and the
/// elaborated theory (`elaborated`, drives the prove loop and the
/// trivial-AC-variant render check).  Returns `true` iff anything was added.
pub fn apply_auto_sources(
    parsed: &mut p::Theory,
    elaborated: &mut crate::theory::Theory,
    maude: MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
) -> bool {
    use crate::constraint::solver::context::ProofContext;
    use crate::guarded::formula_to_guarded;

    // Restrictions → guarded (mirrors ProverSession::build; skip on failure).
    let mut restrictions = Vec::new();
    for r in elaborated.restrictions() {
        if let Ok(g) = formula_to_guarded(&r.formula) {
            restrictions.push(g);
        }
    }
    let rules: Vec<OpenProtoRule> = elaborated.rules().cloned().collect();

    // collect open destruction chains across a context's (saturated) source
    // cases.
    fn collect_chains(ctx: &ProofContext) -> Vec<((NodeConc, NodePrem), System)> {
        let mut chains = Vec::new();
        for src in &ctx.full_sources {
            for (_name, sys) in src.cases(ctx) {
                for ch in sys.unsolved_chains() {
                    chains.push((ch, sys.clone()));
                }
            }
        }
        chains
    }

    // GENERATION chains: the RAW (saturated, unrefined) sources — HS
    // `addAutoSourcesLemma` uses `crcRawSources` (RuleItem.hs:64-70, see line 66).
    let ctx_raw = ProofContext::new_with_restrictions_and_pool(
        maude.clone(), pool.clone(), rules.clone(), restrictions.clone());
    let raw_chains = collect_chains(&ctx_raw);

    // TRIGGER: HS `containsPartialDeconstructions` checks the REFINED sources
    // (crcRefinedSources, field 3) — those refined by the theory's existing
    // `[sources]` lemmas. When such lemmas exist they can close the open
    // chains, so the trigger is OFF even though the raw sources still have
    // them (e.g. NSPK3 with a manual `types [sources]` lemma). Build a second
    // context whose typing assumptions are those lemmas and check ITS chains.
    let typing_asms: Vec<crate::guarded::Guarded> = elaborated
        .lemmas()
        .filter(|l| l.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Sources)))
        .filter_map(|l| formula_to_guarded(&l.formula).ok())
        .collect();
    let trigger = if typing_asms.is_empty() {
        // refined == raw
        !raw_chains.is_empty()
    } else {
        let mut ctx_ref = ProofContext::new_with_restrictions_and_pool(
            maude.clone(), pool, rules.clone(), restrictions);
        ctx_ref.typing_assumptions = typing_asms;
        !collect_chains(&ctx_ref).is_empty()
    };
    if !trigger {
        return false;
    }

    let result = add_auto_sources_lemma(&maude, &rules, &raw_chains);

    // addLabels: add the AUTO actions to the matching rules. HS folds the
    // per-rule act list right-to-left over `addActionClosedProtoRule`
    // (prepend-if-absent); iterating the global list in reverse + prepend
    // reproduces that order.  Apply to both the elaborated rule (LNFact) and
    // the parsed rule (AST fact, for rendering).
    for grp in &result.annotation_groups {
        for (rule_name, action) in grp.iter().rev() {
            for item in elaborated.items.iter_mut() {
                if let TheoryItem::Rule(o) = item {
                    if o.name() == rule_name {
                        add_action_to_open_rule(o, action.clone());
                    }
                }
            }
            let ast_action = crate::pretty_theory::lnfact_to_parser(action);
            for item in parsed.items.iter_mut() {
                if let p::TheoryItem::Rule(r) = item {
                    if &r.name == rule_name {
                        add_action_to_parsed_rule(r, &ast_action);
                    }
                }
            }
        }
    }

    // Add the lemma unless one of the same name already exists — to both the
    // elaborated theory (so the prove loop proves it) and the parsed theory
    // (so it renders).
    if !has_lemma_named(&elaborated.items, "AUTO_typing") {
        elaborated.items.push(TheoryItem::Lemma(build_source_lemma("AUTO_typing", result.formula.clone())));
        parsed.items.push(p::TheoryItem::Lemma(build_parsed_source_lemma("AUTO_typing", result.formula)));
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_formula::lemma_header_line;

    // Ground truth: the `AUTO_typing` lemma body emitted by the Haskell
    // prover for examples/features/auto-sources/running-example/running.spthy
    // (HS `--auto-sources`). The formula is `(⊤) ∧ (the term-input form)`.
    #[test]
    fn running_example_auto_typing_renders_byte_identically() {
        let in_name = "AUTO_IN_TERM_1_0_0_1_1__Rule_R";
        let out_name = "AUTO_OUT_TERM_1_0_0_1_1__Rule_R";
        let f = and(
            p::Formula::True,
            term_input_form_with_outputs(in_name, out_name),
        );
        let rendered = lemma_header_line("all-traces", &f);
        let expected = "  all-traces\n  \"(⊤) ∧\n   (∀ x m #i.\n     (AUTO_IN_TERM_1_0_0_1_1__Rule_R( m, x ) @ #i) ⇒\n     ((∃ #j. (!KU( x ) @ #j) ∧ (#j < #i)) ∨\n      (∃ #j. (AUTO_OUT_TERM_1_0_0_1_1__Rule_R( m ) @ #j) ∧ (#j < #i))))\"";
        assert_eq!(rendered, expected);
    }
}
