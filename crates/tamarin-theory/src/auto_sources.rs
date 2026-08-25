// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of Haskell's `--auto-sources` lemma generation
//! (`addAutoSourcesLemma`, `lib/theory/src/OpenTheory.hs:138-538`).
//!
//! When `--auto-sources` is set and the raw sources still contain open
//! chains (partial deconstructions), Tamarin first UNFOLDS every closed
//! rule into its per-AC-variant rules (`itemsModAC = unfoldRules items`,
//! CloseRule.hs:106-110; `unfoldRuleVariants`, lib/theory/src/Rule.hs:63-79
//! — identity for trivial-variant rules) and then generates a single
//! `sources` lemma over the unfolded rule set: each open-chain input
//! subterm is tied to the earlier outputs it can unify with (via Maude) or
//! to the adversary's knowledge (`!KU`). Rules gain `AUTO_IN_*`/`AUTO_OUT_*`
//! action labels so the lemma can refer to those input/output events.
//!
//! This module builds the lemma **formula** as a parser-AST [`p::Formula`]
//! and closes it with [`crate::formula::from_parser`] for the elaborated
//! lemma, constructed to render byte-identically to HS's `prettyLNFormula` of
//! the `LNFormula` it builds.  The variable binders use HS's names (`x`,
//! `m`/`m1..mn`, `i`, `j`).

use crate::constraint::constraints::{NodeConc, NodePrem};
use crate::constraint::system::System;
use crate::fact::{proto_or_in_fact_view, proto_or_out_fact_view, FactTag, LNFact, Multiplicity};
use crate::formula::LNFormula;
use crate::rule::{print_fact_position, print_position, rule_name_string, ExtendedPosition};
use crate::theory::{OpenProtoRule, TheoryItem};
use tamarin_parser::ast as p;
use tamarin_term::lterm::{rename_avoiding, LNTerm, LSort};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::positions::{at_pos, deepest_prot_subterm, find_pos};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::all_prot_subterms;

/// Bound-variable names, matching HS's quantifier binders in
/// `addAutoSourcesLemma` (`OpenTheory.hs:399-535`).
fn var(name: &str, sort: LSort) -> p::VarSpec {
    p::VarSpec {
        name: name.to_string(),
        idx: 0,
        sort,
        typ: None,
    }
}
fn var_term(name: &str, sort: LSort) -> p::Term {
    p::Term::Var(var(name, sort))
}

/// `inputFactTerm pos ru terms var` (OpenTheory.hs:138-538, see line 313): a linear proto fact
/// `AUTO_IN_TERM_<pos>_<rule>( terms.. , var )`.
fn input_fact_term(name: &str, terms: Vec<p::Term>, v: p::Term) -> p::Fact {
    let mut args = terms;
    args.push(v);
    p::Fact {
        persistent: false,
        name: name.to_string(),
        args,
        annotations: Vec::new(),
    }
}

/// `outputFactTerm pos ru terms` (OpenTheory.hs:138-538, see line 333).
fn output_fact_term(name: &str, terms: Vec<p::Term>) -> p::Fact {
    p::Fact {
        persistent: false,
        name: name.to_string(),
        args: terms,
        annotations: Vec::new(),
    }
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

const MSG: LSort = LSort::Msg;
const NODE: LSort = LSort::Node;

/// `orKU` (OpenTheory.hs:138-538, see line 484): `∃ j. !KU(x) @ j ∧ j < i`. Here `i` is the
/// input timepoint and `x` the input-term variable.
fn or_ku() -> p::Formula {
    let ku = p::Fact {
        persistent: true,
        name: "KU".to_string(),
        args: vec![var_term("x", MSG)],
        annotations: Vec::new(),
    };
    exists(
        vec![var("j", NODE)],
        and(
            action(ku, var_term("j", NODE)),
            less(var_term("j", NODE), var_term("i", NODE)),
        ),
    )
}

/// `toFactsTerm ru p f''` (OpenTheory.hs:138-538, see line 502): `f'' ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i)`.
fn to_facts_term(out_name: &str, inner: p::Formula) -> p::Formula {
    let out = output_fact_term(out_name, vec![var_term("m", MSG)]);
    or(
        inner,
        exists(
            vec![var("j", NODE)],
            and(
                action(out, var_term("j", NODE)),
                less(var_term("j", NODE), var_term("i", NODE)),
            ),
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
    forall(
        binders,
        implies(action(in_fact, var_term("i", NODE)), p::Formula::False),
    )
}

/// `addForm (_, Right (_, outs:_), _)` (OpenTheory.hs:138-538, see line 464): with a matching
/// output → `∀ m1..mn i. AUTO_IN_FACT(m1..mn) @ i ⇒ toFactsFact`.
/// `toFactsFact` (OpenTheory.hs): `∃ j. AUTO_OUT_FACT(m1..m{out_arity}) @ j ∧ j < i`
/// — the output fact references the input binders `m1..m{out_arity}`, highest first.
fn fact_input_form_with_outputs(
    in_name: &str,
    out_name: &str,
    in_arity: usize,
    out_arity: usize,
) -> p::Formula {
    let ms: Vec<p::VarSpec> = list_of_m(in_arity).iter().map(|n| var(n, MSG)).collect();
    let in_fact = input_fact_fact_ast(in_name, &ms);
    // toFactsFact: AUTO_OUT_FACT( listVarTerm (1 + out_arity) 2 ) — de-Bruijn
    // Bound (1+out_arity)..Bound 2 with j=Bound 0, i=Bound 1. So the output
    // fact references m1..m{out_arity} (the input binders), highest first.
    let out_ms: Vec<p::Term> = (1..=out_arity)
        .map(|k| var_term(&format!("m{}", k), MSG))
        .collect();
    let out_fact = p::Fact {
        persistent: false,
        name: out_name.to_string(),
        args: out_ms,
        annotations: Vec::new(),
    };
    let to_facts = exists(
        vec![var("j", NODE)],
        and(
            action(out_fact, var_term("j", NODE)),
            less(var_term("j", NODE), var_term("i", NODE)),
        ),
    );
    let mut binders = ms;
    binders.push(var("i", NODE));
    forall(
        binders,
        implies(action(in_fact, var_term("i", NODE)), to_facts),
    )
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
    match &o.abstracted_rule {
        Some(ar) => &ar.conclusions,
        None => &o.rule.conclusions,
    }
}
fn ac_prems(o: &OpenProtoRule) -> &[LNFact] {
    match &o.abstracted_rule {
        Some(ar) => &ar.premises,
        None => &o.rule.premises,
    }
}

fn ln_proto(name: &str, terms: Vec<LNTerm>) -> LNFact {
    crate::fact::proto_fact(Multiplicity::Linear, name, terms)
}

/// One matched input together with its matching outputs.
enum Matched {
    /// protected-subterm input: deepest prot term, the var, matching (out-rule, out-term).
    Term {
        protterm: LNTerm,
        vin: LNTerm,
        outs: Vec<(usize, LNTerm)>,
    },
    /// non-protected fact input: the fact, matching (out-rule, out-fact).
    Fact {
        fact: LNFact,
        outs: Vec<(usize, LNFact)>,
    },
}

/// Build the `(AUTO_IN_*, AUTO_OUT_*)` fact-name pair for a matched input,
/// selecting `print_position` (Term) vs `print_fact_position` (Fact) by the
/// `Matched` variant.  Shared by the addFormula and addLabels loops so the
/// four AUTO_* name templates live in exactly one place.
fn auto_names(m: &Matched, pos: &ExtendedPosition, rin_name: &str) -> (String, String) {
    match m {
        Matched::Term { .. } => {
            let p = print_position(pos);
            (
                format!("AUTO_IN_TERM_{}_{}", p, rin_name),
                format!("AUTO_OUT_TERM_{}_{}", p, rin_name),
            )
        }
        Matched::Fact { .. } => {
            let p = print_fact_position(pos);
            (
                format!("AUTO_IN_FACT_{}_{}", p, rin_name),
                format!("AUTO_OUT_FACT_{}_{}", p, rin_name),
            )
        }
    }
}

/// `ruleName . cprRuleE` — the E-half's name.  Variants of one unfold all
/// share it, which is what makes HS's "we ignore outputs of the same rule"
/// guard (OpenTheory.hs:138-538, see line 292,303) skip SIBLING
/// variants too: the guard compares the `cprRuleE` names, not the
/// `___VARIANT_<i>` AC names (everything else in the lemma computation —
/// AUTO fact names, `addLabels`' targeting, the `done` cases — uses the AC
/// name, `getRuleName (cprRuleAC ru)`).
fn rule_e_name(o: &OpenProtoRule) -> &str {
    match o.rule_e.as_deref() {
        Some(re) => match &re.info.name {
            crate::rule::ProtoRuleName::Stand(n) => n,
            crate::rule::ProtoRuleName::Fresh => "Fresh",
        },
        None => o.name(),
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
        let Some(c_rule) = source.node_rule_safe(&conc.0) else {
            continue;
        };
        let Some(conc_fact) = c_rule.conclusions.get(conc.1 .0) else {
            continue;
        };
        let Some(v) = conc_fact.terms.first().cloned() else {
            continue;
        };

        // unsolved premises of this source (for the fact-case guard).
        let unsolved_prem_keys: Vec<NodePrem> = source
            .unsolved_premises()
            .into_iter()
            .map(|(np, _)| np)
            .collect();

        // inputRules: for each (nodeid, pid, tidx, term) in allPrems containing v.
        // Each element is (input-rule-idx, Left term | Right fact, position).
        enum InRule {
            Term(LNTerm),
            Fact(LNFact),
        }
        let mut input_rules: Vec<(usize, InRule, ExtendedPosition)> = Vec::new();
        for (nodeid, pid, tidx, term) in source.all_prems() {
            let Some(positions) = find_pos(&v, &term) else {
                continue;
            };
            let Some(rule_sys) = source.node_rule_safe(&nodeid) else {
                continue;
            };
            let sys_name = rule_name_string(rule_sys);
            let Some((ri, rule)) = rules.iter().enumerate().find(|(_, r)| r.name() == sys_name)
            else {
                continue;
            };
            let Some(premise) = ac_prems(rule).get(pid.0) else {
                continue;
            };
            let Some(t_prime) = proto_or_in_fact_view(premise) else {
                continue;
            };
            let Some(t) = t_prime.get(tidx).cloned() else {
                continue;
            };
            // terms (Left): one per found position.
            for pos in &positions {
                input_rules.push((ri, InRule::Term(t.clone()), (pid, tidx, pos.clone())));
            }
            // facts (Right): proto fact + (pair|AC|msgvar) + premise unsolved.
            let is_proto = matches!(premise.tag, FactTag::Proto(..));
            let t_is_eligible = tamarin_term::term::is_pair(&t)
                || tamarin_term::term::is_ac(&t)
                || tamarin_term::lterm::is_msg_var(&t);
            if is_proto && t_is_eligible && unsolved_prem_keys.contains(&(nodeid, pid)) {
                for pos in &positions {
                    input_rules.push((ri, InRule::Fact(premise.clone()), (pid, tidx, pos.clone())));
                }
            }
        }

        // premiseTermU: resolve Left terms to (deepest prot subterm, var).
        enum Unify {
            Term(LNTerm, LNTerm),
            Fact(LNFact),
        }
        let mut premise_term_u: Vec<(usize, Unify, ExtendedPosition)> = Vec::new();
        for (ri, inr, pos) in input_rules {
            match inr {
                InRule::Term(y) => {
                    let z = &pos.2;
                    let Some(v_prime) = at_pos(&y, z) else {
                        continue;
                    };
                    let Some(prot_prime) = deepest_prot_subterm(&y, z) else {
                        continue;
                    };
                    if prot_prime == v_prime {
                        continue;
                    } // HS: skip when prot == var
                    premise_term_u.push((ri, Unify::Term(prot_prime, v_prime), pos));
                }
                InRule::Fact(f) => premise_term_u.push((ri, Unify::Fact(f), pos)),
            }
        }

        // filterFacts + matchingConclusions → inputsAndOutputs.
        let has_subterm_case = premise_term_u
            .iter()
            .any(|(_, u, _)| matches!(u, Unify::Term(..)));
        let mut matches: Vec<(usize, Matched, ExtendedPosition)> = Vec::new();
        for (ri, u, pos) in &premise_term_u {
            let rin_name = rules[*ri].name();
            let already_done = || done.iter().any(|(n, p)| n == rin_name && p == pos);
            match u {
                Unify::Term(protterm, vin) => {
                    if already_done() {
                        continue;
                    }
                    let mut outs: Vec<(usize, LNTerm)> = Vec::new();
                    for (rout_i, tout) in &all_out_concs {
                        // same-rule guard on the E-half names (see
                        // `rule_e_name`): sibling variants never match.
                        if rule_e_name(&rules[*rout_i]) == rule_e_name(&rules[*ri]) {
                            continue;
                        }
                        let fout = rename_avoiding(tout.clone(), protterm);
                        if maude
                            .unifiable(&[Equal {
                                lhs: protterm.clone(),
                                rhs: fout,
                            }])
                            .unwrap_or(false)
                        {
                            outs.push((*rout_i, tout.clone()));
                        }
                    }
                    matches.push((
                        *ri,
                        Matched::Term {
                            protterm: protterm.clone(),
                            vin: vin.clone(),
                            outs,
                        },
                        pos.clone(),
                    ));
                }
                Unify::Fact(fact) => {
                    if already_done() || has_subterm_case {
                        continue;
                    }
                    let mut outs: Vec<(usize, LNFact)> = Vec::new();
                    for (rout_i, fout) in &all_out_concs_not_prot {
                        // same-rule guard on the E-half names (see
                        // `rule_e_name`): sibling variants never match.
                        if rule_e_name(&rules[*rout_i]) == rule_e_name(&rules[*ri]) {
                            continue;
                        }
                        if crate::fact::fact_tag_name(&fout.tag)
                            != crate::fact::fact_tag_name(&fact.tag)
                        {
                            continue;
                        }
                        let unifout = rename_avoiding(fout.clone(), fact);
                        if crate::rule::unifiable_ln_facts(maude, fact, &unifout).unwrap_or(false) {
                            outs.push((*rout_i, fout.clone()));
                        }
                    }
                    matches.push((
                        *ri,
                        Matched::Fact {
                            fact: fact.clone(),
                            outs,
                        },
                        pos.clone(),
                    ));
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
                Matched::Term {
                    protterm,
                    vin,
                    outs,
                } => {
                    let (in_name, out_name) = auto_names(m, pos, &rin_name);
                    grp.push((
                        rin_name.clone(),
                        ln_proto(&in_name, vec![protterm.clone(), vin.clone()]),
                    ));
                    for (rout_i, tout) in outs {
                        grp.push((
                            rules[*rout_i].name().to_string(),
                            ln_proto(&out_name, vec![tout.clone()]),
                        ));
                    }
                }
                Matched::Fact { fact, outs } => {
                    let (in_name, out_name) = auto_names(m, pos, &rin_name);
                    grp.push((rin_name.clone(), ln_proto(&in_name, fact.terms.to_vec())));
                    for (rout_i, fout) in outs {
                        grp.push((
                            rules[*rout_i].name().to_string(),
                            ln_proto(&out_name, fout.terms.to_vec()),
                        ));
                    }
                }
            }
            done.push((rin_name, pos.clone()));
        }
        annotation_groups.push(grp);
    }

    AutoSourcesResult {
        annotation_groups,
        formula,
    }
}

/// Build the AUTO source lemma item (HS `unprovenLemma lemmaName [SourceLemma]
/// AllTraces formula`, OpenTheory.hs:138-538, see line 157).  `unprovenLemma`
/// seeds `_lOriginalFormula` with the same formula
/// (Theory/ProofSkeleton.hs:59-61).
pub fn build_source_lemma(name: &str, formula: LNFormula) -> crate::theory::Lemma {
    use crate::theory::{Lemma, LemmaAttr, TraceQuantifier};
    Lemma {
        name: name.to_string(),
        modulo: None,
        attributes: vec![LemmaAttr::Sources],
        trace_quantifier: TraceQuantifier::AllTraces,
        original_formula: Some(formula.clone()),
        formula,
        proof: None,
        // HS `unprovenLemma` seeds `_lPlaintext` with "Unpr_inSkeleton"
        // (`Theory/ProofSkeleton.hs:59-61, see line 61`).
        plaintext: "Unpr_inSkeleton".to_string(),
    }
}

/// Whether the theory already contains a lemma named `name`
/// (HS `find lemma items`, OpenTheory.hs:138-538, see line 146).
pub fn has_lemma_named(items: &[TheoryItem], name: &str) -> bool {
    items
        .iter()
        .any(|it| matches!(it, TheoryItem::Lemma(l) if l.name == name))
}

/// Add an AUTO action to an open proto rule's AC form. HS adds to
/// `cprRuleAC` only (`addActionClosedProtoRule`, lib/theory/src/Rule.hs:97-99);
/// for a trivial-variant rule (no
/// abstracted form) that is the rule itself, which renders as
/// `rule (modulo E)` and propagates to its instances.  The pristine body is
/// snapshotted into `rule_e` first — HS's untouched `cprRuleE` half, which
/// partial evaluation's `getProtoRuleEs` must keep reading (see the field
/// doc).
fn add_action_to_open_rule(o: &mut OpenProtoRule, action: LNFact) {
    if o.rule_e.is_none() {
        o.rule_e = Some(Box::new(o.rule.clone()));
    }
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

/// HS `unfoldRuleVariants` on ONE closed rule (lib/theory/src/Rule.hs:63-79),
/// non-trivial case: for each substitution i (1-based) of the rule's variant
/// disjunction, `freshToFreeAvoiding` it against the AC rule, apply it to
/// (premises, conclusions, actions, new vars), and emit a rule named
/// `<name>___VARIANT_<i>` (a FreshRule keeps its name) whose own variants
/// are `Disj [emptySubstVFresh]`, carrying over the original's attributes
/// and (pre-computed) loop breakers verbatim.
///
/// RS mapping: the AC rule is `abstracted_rule` when present (else the E
/// body IS the AC body), and the disjunction is `variant_substs` — with an
/// unpopulated empty list standing for HS's ever-present trivial
/// `Disj [emptySubstVFresh]` (`trueDisj`, RuleVariants.hs:61-133, see line
/// 119), so a body-divergent rule with no residual substs still unfolds
/// into exactly one `___VARIANT_1` rule (the reproducing case: partial
/// evaluation leaves `rule ≠ abstracted_rule` with a collapsed
/// disjunction).
fn unfold_one_rule_variants(o: &OpenProtoRule) -> Vec<OpenProtoRule> {
    use tamarin_term::lterm::{HasFrees, LVar};
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    let ac: &crate::rule::ProtoRuleE = o.abstracted_rule.as_ref().unwrap_or(&o.rule);
    let trivial_disj = [LNSubstVFresh::empty()];
    let substs: &[LNSubstVFresh] = if o.variant_substs.is_empty() {
        &trivial_disj
    } else {
        &o.variant_substs
    };
    // `freshToFreeAvoiding subst ruAC` allocates above `avoid ruAC`; HS's
    // `HasFrees (Rule ProtoRuleACInfo)` folds the rule INFO first, whose
    // variant-disjunction DOMAIN keys are frees (keys-only,
    // Theory/Model/Rule.hs:291-306, 503-515; SubstVFresh.hs:196-202), so
    // they participate in the bound alongside the body.
    let mut max_idx: Option<u64> = None;
    {
        let mut see = |v: &LVar| {
            max_idx = Some(max_idx.map_or(v.idx, |m| m.max(v.idx)));
        };
        for s in substs {
            for (k, _) in s.iter() {
                see(k);
            }
        }
        ac.for_each_free(&mut see);
    }
    let seed = max_idx.map(|m| m + 1).unwrap_or(0);
    substs
        .iter()
        .enumerate()
        .map(|(i, s)| {
            // Each subst gets its own `evalFreshAvoiding` scope (HS maps
            // `freshToFreeAvoiding` per subst against the same `ruAC`).
            let mut counter = seed;
            let sigma = s.fresh_to_free_avoiding(|n| {
                let b = counter;
                counter += n;
                b
            });
            let mut ru = crate::rule::apply_subst_rule(&sigma, ac);
            // `rName i` (lib/theory/src/Rule.hs:71-73): FreshRule keeps its
            // name; StandRule gains the 1-based `___VARIANT_<i>` suffix.
            ru.info.name = match ru.info.name {
                crate::rule::ProtoRuleName::Fresh => crate::rule::ProtoRuleName::Fresh,
                crate::rule::ProtoRuleName::Stand(name) => crate::rule::ProtoRuleName::Stand(
                    tamarin_term::intern::intern_str(&format!("{}___VARIANT_{}", name, i + 1)),
                ),
            };
            OpenProtoRule {
                rule: ru,
                variant_substs: vec![LNSubstVFresh::empty()],
                abstracted_rule: None,
                loop_breakers: o.loop_breakers.clone(),
                unfolded_variant: true,
                // `toClosedProtoRule` keeps the ORIGINAL rule as every
                // variant's `cprRuleE` (lib/theory/src/Rule.hs:75-76) — the
                // half `getProtoRuleEs` dedups back to one copy.
                rule_e: o.rule_e.clone().or_else(|| Some(Box::new(o.rule.clone()))),
            }
        })
        .collect()
}

/// HS `unfoldRules items` (CloseRule.hs:106-110) over the paired
/// parsed/elaborated theories: replace every closed rule whose AC variant is
/// non-trivial (`isTrivialProtoVariantAC`, shared with the renderer as
/// `pretty_theory::is_trivial_proto_variant_ac`) by its per-variant rules
/// ([`unfold_one_rule_variants`]); trivial-variant rules stay unchanged, so
/// the pass is the identity on a theory whose variants are all trivial.
///
/// BOTH item lists are rewritten in place, mirroring what
/// `mergeOpenProtoRules` + `prettyOpenProtoRuleAsClosedRule` make of the
/// unfolded items at render time (OpenTheory.hs:592-606, 827-851):
///  * ONE variant — the merge yields `OpenProtoRule ruE [ruAC]`, rendered
///    `prettyProtoRuleACasE ruAC` (the AC body under the `___VARIANT_1`
///    name, as if modulo E) — so the parsed slot is REPLACED by the rule
///    regenerated from the variant's LN body (`proto_rule_to_parsed`, as
///    the partial-evaluation splice does).
///  * TWO OR MORE variants — the merge groups them back under their shared
///    `cprRuleE` and renders `prettyProtoRuleE ruE` + a ` variants` block
///    of `rule (modulo AC)` sub-blocks (OpenTheory.hs:845-851) — so the
///    parsed slot KEEPS the original display rule and parks the regenerated
///    variant bodies in its `variants` field
///    (`pretty_theory::render_unfolded_variants_block` renders them).
///
/// Either way the renderer's positional `(name, occurrence)` pairing
/// (`pretty_theory::pair_elaborated_rules`) stays aligned.  A parsed
/// leftover with no elaborated counterpart (the no-variant drop, run.rs)
/// keeps its slot and keeps rendering as nothing.
///
/// Returns `true` iff any rule was unfolded.
fn unfold_rule_variants(parsed: &mut p::Theory, elaborated: &mut crate::theory::Theory) -> bool {
    let macros = crate::pretty_theory::collect_macros(parsed);
    let arity1 = crate::elaborate::arity1_noeq_names(elaborated.signature.maude_sig());

    // Parsed display rules grouped by name in item order: the k-th parsed
    // rule named N displays the k-th elaborated rule named N
    // (`pair_elaborated_rules`' invariant).
    let mut parsed_by_name: tamarin_utils::FastMap<&str, Vec<&p::Rule>> = Default::default();
    for item in &parsed.items {
        if let p::TheoryItem::Rule(r) = item {
            parsed_by_name.entry(r.name.as_str()).or_default().push(r);
        }
    }

    // Decision pass over the elaborated rules in item order: one entry per
    // rule item (`None` = trivial, keep).  `parsed_repl` keys the
    // regenerated parsed rules by the same (name, occurrence) the rewrite
    // below re-derives — replacing the slot for a single variant, nesting
    // them under the kept display rule for two or more (see the fn doc).
    enum ParsedRewrite {
        Replace(Vec<p::Rule>),
        Nest(Vec<p::Rule>),
    }
    let mut elab_repl: Vec<Option<Vec<OpenProtoRule>>> = Vec::new();
    let mut parsed_repl: tamarin_utils::FastMap<(String, usize), ParsedRewrite> =
        Default::default();
    let mut elab_occ: tamarin_utils::FastMap<String, usize> = Default::default();
    for item in &elaborated.items {
        let TheoryItem::Rule(o) = item else { continue };
        let name = o.name().to_string();
        let k = {
            let c = elab_occ.entry(name.clone()).or_default();
            let k = *c;
            *c += 1;
            k
        };
        // HS tests `isTrivialProtoVariantAC ruAC ruE` with `ruE` = the
        // original (display) rule; the parsed item is RS's display half.
        // An elaborated rule nothing displays degenerates to the
        // machinery-only test — synthesise the display from the elaborated
        // body, on which the macro check is inert.
        let trivial = match parsed_by_name.get(name.as_str()).and_then(|g| g.get(k)) {
            Some(pr) => {
                let (dp, da, dc) = crate::pretty_theory::display_fact_rows(pr, &arity1);
                crate::pretty_theory::is_trivial_proto_variant_ac(&dp, &da, &dc, o, &macros)
            }
            None => {
                let pr = crate::elaborate::proto_rule_to_parsed(&o.rule);
                let (dp, da, dc) = crate::pretty_theory::display_fact_rows(&pr, &arity1);
                crate::pretty_theory::is_trivial_proto_variant_ac(&dp, &da, &dc, o, &macros)
            }
        };
        if trivial {
            elab_repl.push(None);
            continue;
        }
        let variants = unfold_one_rule_variants(o);
        let parsed_variants: Vec<p::Rule> = variants
            .iter()
            .map(|v| crate::elaborate::proto_rule_to_parsed(&v.rule))
            .collect();
        let rewrite = if parsed_variants.len() == 1 {
            ParsedRewrite::Replace(parsed_variants)
        } else {
            ParsedRewrite::Nest(parsed_variants)
        };
        parsed_repl.insert((name, k), rewrite);
        elab_repl.push(Some(variants));
    }
    if elab_repl.iter().all(|r| r.is_none()) {
        return false;
    }

    // Elaborated-side rewrite: each rule item takes its replacement run.
    let items = std::mem::take(&mut elaborated.items);
    let mut decisions = elab_repl.into_iter();
    let mut new_items = Vec::with_capacity(items.len());
    for item in items {
        match item {
            TheoryItem::Rule(o) => match decisions.next().expect("one decision per rule item") {
                Some(vs) => new_items.extend(vs.into_iter().map(TheoryItem::Rule)),
                None => new_items.push(TheoryItem::Rule(o)),
            },
            other => new_items.push(other),
        }
    }
    elaborated.items = new_items;

    // Parsed-side rewrite, keyed by the same (name, occurrence).
    let items = std::mem::take(&mut parsed.items);
    let mut occ: tamarin_utils::FastMap<String, usize> = Default::default();
    let mut new_items = Vec::with_capacity(items.len());
    for item in items {
        match item {
            p::TheoryItem::Rule(mut r) => {
                let c = occ.entry(r.name.clone()).or_default();
                let k = *c;
                *c += 1;
                match parsed_repl.remove(&(r.name.clone(), k)) {
                    Some(ParsedRewrite::Replace(vs)) => {
                        new_items.extend(vs.into_iter().map(p::TheoryItem::Rule))
                    }
                    Some(ParsedRewrite::Nest(vs)) => {
                        r.variants = vs;
                        new_items.push(p::TheoryItem::Rule(r));
                    }
                    None => new_items.push(p::TheoryItem::Rule(r)),
                }
            }
            other => new_items.push(other),
        }
    }
    parsed.items = new_items;
    true
}

/// Apply `--auto-sources` (HS `closeTheoryWithMaude`'s autosources branch,
/// CloseRule.hs:56-137, see line 58,106-112).  When the raw sources contain
/// partial deconstructions, unfold every rule into its AC-variant rules
/// ([`unfold_rule_variants`]), annotate them with AUTO_* actions and append
/// the `AUTO_typing` sources
/// lemma — to BOTH the parser-AST theory (`parsed`, drives rendering) and the
/// elaborated theory (`elaborated`, drives the prove loop and the
/// trivial-AC-variant render check).  `ndc_cache` is the theory's
/// once-per-load NDC-checked intruder cache, injected into the scratch
/// contexts below so they reuse the tagged+permuted rules instead of
/// re-running the check.  Returns `true` iff anything was added.
pub fn apply_auto_sources(
    parsed: &mut p::Theory,
    elaborated: &mut crate::theory::Theory,
    maude: MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    ndc_cache: Option<&crate::constraint::solver::context::IntrRuleCache>,
) -> bool {
    use crate::constraint::solver::context::ProofContext;
    use crate::guarded::formula_to_guarded;

    // Both scratch contexts below share the caller's one rule list.
    let ndc_cache = ndc_cache.cloned();

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
    let ctx_raw = ProofContext::new_with_restrictions_pool_forced(
        maude.clone(),
        pool.clone(),
        rules.clone(),
        restrictions.clone(),
        &[],
        ndc_cache.clone(),
    );
    let raw_chains = collect_chains(&ctx_raw);

    // TRIGGER: HS `containsPartialDeconstructions` checks the REFINED sources
    // (crcRefinedSources, field 3) — those refined by the theory's existing
    // `[sources]` lemmas. When such lemmas exist they can close the open
    // chains, so the trigger is OFF even though the raw sources still have
    // them (e.g. NSPK3 with a manual `types [sources]` lemma). Build a second
    // context whose typing assumptions are those lemmas and check ITS chains.
    let typing_asms: Vec<crate::guarded::Guarded> = elaborated
        .lemmas()
        .filter(|l| {
            l.attributes
                .iter()
                .any(|a| matches!(a, crate::theory::LemmaAttr::Sources))
        })
        .filter_map(|l| formula_to_guarded(&l.formula).ok())
        .collect();
    let trigger = if typing_asms.is_empty() {
        // refined == raw
        !raw_chains.is_empty()
    } else {
        let mut ctx_ref = ProofContext::new_with_restrictions_pool_forced(
            maude.clone(),
            pool.clone(),
            rules.clone(),
            restrictions.clone(),
            &[],
            ndc_cache.clone(),
        );
        ctx_ref.typing_assumptions = typing_asms;
        !collect_chains(&ctx_ref).is_empty()
    };
    if !trigger {
        return false;
    }

    // `itemsModAC = unfoldRules items` (CloseRule.hs:106-110): once the
    // trigger fires, every closed rule is replaced by its per-AC-variant
    // rules BEFORE the AUTO lemma is computed, so the AUTO_* names and
    // annotations reference the `___VARIANT_<i>` rules.  The loop breakers
    // were computed before this point and are carried into each variant
    // verbatim.
    let unfolded = unfold_rule_variants(parsed, elaborated);
    // `cache itemsModAC` (CloseRule.hs:112): `addAutoSourcesLemma` reads the
    // rule cache RECOMPUTED over the unfolded rules.  When nothing unfolded,
    // `itemsModAC == items` and the cache has the same value — reuse the
    // original context's chains (and its saturation trace count).
    let (rules, gen_chains) = if unfolded {
        let rules: Vec<OpenProtoRule> = elaborated.rules().cloned().collect();
        let ctx_mod = ProofContext::new_with_restrictions_pool_forced(
            maude.clone(),
            pool,
            rules.clone(),
            restrictions,
            &[],
            ndc_cache,
        );
        let chains = collect_chains(&ctx_mod);
        (rules, chains)
    } else {
        (rules, raw_chains)
    };

    let result = add_auto_sources_lemma(&maude, &rules, &gen_chains);

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
            let ast_action = crate::elaborate::lnfact_to_parser(action);
            for item in parsed.items.iter_mut() {
                if let p::TheoryItem::Rule(r) = item {
                    if &r.name == rule_name {
                        add_action_to_parsed_rule(r, &ast_action);
                    }
                    // A `___VARIANT_<i>` rule of a multi-variant unfold lives
                    // NESTED in its display rule's `variants` field (see
                    // `unfold_rule_variants`); HS annotates the closed
                    // variant's `cprRuleAC`, which the merged display shows.
                    for v in r.variants.iter_mut() {
                        if &v.name == rule_name {
                            add_action_to_parsed_rule(v, &ast_action);
                        }
                    }
                }
            }
        }
    }

    // Add the lemma unless one of the same name already exists — to both the
    // elaborated theory (so the prove loop proves it) and the parsed theory
    // (so it renders).
    if !has_lemma_named(&elaborated.items, "AUTO_typing") {
        // `from_parser` reads the signature, so close the formula before the
        // `&mut` push.  The generated formula carries neither predicate sugar
        // nor a macro call, so `_lFormula` and `_lOriginalFormula` coincide.
        // A formula the signature cannot close adds no lemma to either theory.
        let closed = crate::formula::from_parser(&result.formula, &elaborated.signature.maude_sig)
            .ok()
            .and_then(|syn| crate::formula::to_lnformula(&syn));
        if let Some(ln) = closed {
            elaborated
                .items
                .push(TheoryItem::Lemma(build_source_lemma("AUTO_typing", ln)));
            parsed
                .items
                .push(p::TheoryItem::Lemma(build_parsed_source_lemma(
                    "AUTO_typing",
                    result.formula,
                )));
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_formula::{formula_doc, lemma_header_line_doc};

    /// The `--auto-sources` unfold (`unfoldRuleVariants`,
    /// lib/theory/src/Rule.hs:63-79): a rule with a non-trivial variant
    /// disjunction is replaced — in BOTH the parsed and elaborated item
    /// lists — by one `___VARIANT_<i>` rule per substitution, each carrying
    /// the trivial disjunction, the original's loop breakers, and the
    /// original rule as its `cprRuleE` half; a trivial-variant rule stays
    /// untouched.
    #[test]
    fn unfold_replaces_nontrivial_rules_with_variant_rules() {
        use crate::fact::{fresh_fact, in_fact, out_fact};
        use crate::rule::{PremIdx, ProtoRuleEInfo, Rule};
        use crate::theory::{OpenProtoRule, Theory, TheoryItem};
        use tamarin_term::builtin::{fresh_var, fst, msg_var};
        use tamarin_term::maude_proc::MaudeHandle;
        use tamarin_term::maude_sig::pair_maude_sig;

        let Some(path) = crate::test_maude::maude_path() else {
            eprintln!("skipping: no maude");
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();

        // NT: [In(x)] --> [Out(fst(x))] — `fst` is reducible under the pair
        // signature, so the variant disjunction has the identity AND the
        // projecting substitution (non-trivial).
        let nt_rule = Rule::new(
            ProtoRuleEInfo::standard("NT"),
            vec![in_fact(msg_var("x", 0))],
            vec![out_fact(fst(msg_var("x", 0)))],
            vec![],
        );
        let mut nt = OpenProtoRule::new(nt_rule.clone());
        let (abstr, substs) = crate::tools::rule_variants::abstract_rule_and_variants(&h, &nt.rule)
            .expect("variants")
            .expect("non-trivial variants");
        assert!(
            substs.iter().any(|s| !s.is_empty()),
            "test premise: NT must have a non-trivial disjunction"
        );
        nt.abstracted_rule = Some(abstr);
        nt.variant_substs = substs.clone();
        nt.loop_breakers = vec![PremIdx(0)];

        // TR: [Fr(~k)] --> [Out(~k)] — no reducible sub-term, trivial.
        let tr = OpenProtoRule::new(Rule::new(
            ProtoRuleEInfo::standard("TR"),
            vec![fresh_fact(fresh_var("k", 0))],
            vec![out_fact(fresh_var("k", 0))],
            vec![],
        ));

        let stub = |name: &str| p::Rule {
            name: name.to_string(),
            modulo: None,
            attributes: vec![],
            let_block: vec![],
            premises: vec![],
            actions: vec![],
            conclusions: vec![],
            embedded_restrictions: vec![],
            variants: vec![],
            left_right: None,
        };
        let mut parsed = p::Theory {
            is_diff: false,
            name: "T".to_string(),
            configuration: None,
            items: vec![
                p::TheoryItem::Rule(stub("NT")),
                p::TheoryItem::Rule(stub("TR")),
            ],
        };
        let mut elab: Theory = Theory::new("T", crate::signature::SignaturePure::empty(false));
        elab.items = vec![TheoryItem::Rule(nt), TheoryItem::Rule(tr.clone())];

        assert!(unfold_rule_variants(&mut parsed, &mut elab));

        // Elaborated: NT expands in place into one rule per substitution;
        // TR keeps its slot and its fields.
        let names: Vec<&str> = elab.rules().map(|r| r.name()).collect();
        let mut expect: Vec<String> = (1..=substs.len())
            .map(|i| format!("NT___VARIANT_{}", i))
            .collect();
        expect.push("TR".to_string());
        assert_eq!(names, expect);
        let variants: Vec<&OpenProtoRule> = elab.rules().filter(|r| r.unfolded_variant).collect();
        assert_eq!(variants.len(), substs.len());
        for v in &variants {
            // `Disj [emptySubstVFresh]` + carried breakers + the ORIGINAL
            // rule as the `cprRuleE` half (lib/theory/src/Rule.hs:68-76).
            assert_eq!(v.variant_substs.len(), 1);
            assert!(v.variant_substs[0].is_empty());
            assert!(v.abstracted_rule.is_none());
            assert_eq!(v.loop_breakers, vec![PremIdx(0)]);
            assert_eq!(v.rule_e.as_deref(), Some(&nt_rule));
        }
        // The substitutions were APPLIED: exactly one variant still has the
        // un-narrowed `fst` in its conclusion (the identity variant), and
        // the bodies differ pairwise.
        let has_fst = |r: &OpenProtoRule| {
            r.rule.conclusions.iter().any(|f| {
                f.terms.iter().any(|t| {
                    matches!(t, tamarin_term::term::Term::App(sym, _)
                        if *sym == tamarin_term::function_symbols::FunSym::NoEq(
                            tamarin_term::function_symbols::fst_sym()))
                })
            })
        };
        assert_eq!(variants.iter().filter(|v| has_fst(v)).count(), 1);
        let tr_after = elab.rules().find(|r| r.name() == "TR").unwrap();
        assert_eq!(tr_after, &tr);

        // Parsed: HS's merged display.  `mergeOpenProtoRules` regroups the
        // unfolded rules under their shared `ruE` (OpenTheory.hs:592-606)
        // and `prettyOpenProtoRuleAsClosedRule`'s multi-variant branch
        // prints `prettyProtoRuleE ruE` + a ` variants` block of the AC
        // bodies (OpenTheory.hs:845-851) — so with TWO variants the NT slot
        // KEEPS the display rule and parks the regenerated `___VARIANT_<i>`
        // bodies in its `variants` field; TR's stub is untouched.
        let parsed_names: Vec<&str> = parsed
            .items
            .iter()
            .map(|it| match it {
                p::TheoryItem::Rule(r) => r.name.as_str(),
                other => panic!("expected only rule items, got {:?}", other),
            })
            .collect();
        assert_eq!(parsed_names, ["NT", "TR"]);
        let p::TheoryItem::Rule(nt_parsed) = &parsed.items[0] else {
            unreachable!("first item is NT");
        };
        let nested: Vec<&str> = nt_parsed.variants.iter().map(|v| v.name.as_str()).collect();
        let expect_nested: Vec<String> = (1..=substs.len())
            .map(|i| format!("NT___VARIANT_{}", i))
            .collect();
        assert_eq!(nested, expect_nested);
        assert_eq!(parsed.items.last(), Some(&p::TheoryItem::Rule(stub("TR"))));
    }

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
        let rendered = lemma_header_line_doc("all-traces", formula_doc(&f));
        let expected = "  all-traces\n  \"(⊤) ∧\n   (∀ x m #i.\n     (AUTO_IN_TERM_1_0_0_1_1__Rule_R( m, x ) @ #i) ⇒\n     ((∃ #j. (!KU( x ) @ #j) ∧ (#j < #i)) ∨\n      (∃ #j. (AUTO_OUT_TERM_1_0_0_1_1__Rule_R( m ) @ #j) ∧ (#j < #i))))\"";
        assert_eq!(rendered, expected);
    }
}
