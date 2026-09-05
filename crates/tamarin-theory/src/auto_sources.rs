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
//! This module builds the lemma **formula** as an [`LNFormula`] over De
//! Bruijn binders, the shape `addAutoSourcesLemma` writes out directly. The
//! binder hints use HS's names (`x`, `m`/`m1..mn`, `i`, `j`).

use crate::atom::ProtoAtom;
use crate::constraint::constraints::{NodeConc, NodePrem};
use crate::constraint::system::System;
use crate::fact::{
    proto_or_in_fact_view, proto_or_out_fact_view, Fact, FactTag, LNFact, Multiplicity,
};
use crate::formula::{BLNTerm, LNFormula};
use crate::rule::{print_fact_position, print_position, rule_name_string, ExtendedPosition};
use crate::theory::{OpenProtoRule, TheoryItem};
use tamarin_term::lterm::{rename_avoiding, BVar, LNTerm, LSort};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::positions::{at_pos, deepest_prot_subterm, find_pos};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::all_prot_subterms;
use tamarin_term::vterm::var_term;

const MSG: LSort = LSort::Msg;
const NODE: LSort = LSort::Node;

/// `varTerm (Bound i)`: the occurrence of the binder `i` levels further out,
/// `0` being the innermost one.
fn bound(i: u64) -> BLNTerm {
    var_term(BVar::Bound(i))
}

/// `Qua All (name, sort)` (OpenTheory.hs:395-417).
fn all(name: &str, sort: LSort, body: LNFormula) -> LNFormula {
    LNFormula::for_all((name.to_string(), sort), body)
}

/// `Qua Ex (name, sort)` (OpenTheory.hs:484-501).
fn ex(name: &str, sort: LSort, body: LNFormula) -> LNFormula {
    LNFormula::exists((name.to_string(), sort), body)
}

/// `Ato (Action tp fa)` (OpenTheory.hs:404-412).
fn action(fa: Fact<BLNTerm>, tp: BLNTerm) -> LNFormula {
    LNFormula::Atom(ProtoAtom::Action(tp, fa))
}

/// `Ato (Less a b)` (OpenTheory.hs:500).
fn less(a: BLNTerm, b: BLNTerm) -> LNFormula {
    LNFormula::Atom(ProtoAtom::Less(a, b))
}

/// The four AUTO action facts — `inputFactTerm`, `inputFactFact`,
/// `outputFactTerm` and `outputFactFact` (OpenTheory.hs:313-352): a linear
/// proto fact of the given name over the given terms.
fn auto_fact(name: &str, terms: Vec<BLNTerm>) -> Fact<BLNTerm> {
    Fact::new(
        FactTag::Proto(
            Multiplicity::Linear,
            tamarin_term::intern::intern_str(name),
            terms.len(),
        ),
        terms,
    )
}

/// `orKU` (OpenTheory.hs:484-501): `∃ j. !KU(x) @ j ∧ j < i`, read under the
/// `x`, `m`, `i` prefix that `Bound 3` and `Bound 1` point back into.
fn or_ku() -> LNFormula {
    let ku = Fact::new(FactTag::Ku, vec![bound(3)]);
    ex(
        "j",
        NODE,
        action(ku, bound(0)).and(less(bound(0), bound(1))),
    )
}

/// `toFactsTerm ru p f''` (OpenTheory.hs:502-519):
/// `f'' ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i)`.
fn to_facts_term(out_name: &str, inner: LNFormula) -> LNFormula {
    inner.or(ex(
        "j",
        NODE,
        action(auto_fact(out_name, vec![bound(2)]), bound(0)).and(less(bound(0), bound(1))),
    ))
}

/// `addForm` protected-subterm case with NO matching outputs
/// (OpenTheory.hs:395-417): `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒ orKU`.
pub(crate) fn term_input_form_no_outputs(in_name: &str) -> LNFormula {
    let in_fact = auto_fact(in_name, vec![bound(1), bound(2)]);
    all(
        "x",
        MSG,
        all(
            "m",
            MSG,
            all("i", NODE, action(in_fact, bound(0)).implies(or_ku())),
        ),
    )
}

/// `addForm` protected-subterm case WITH matching outputs
/// (OpenTheory.hs:419-441): `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒
/// (orKU ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i))`.
pub(crate) fn term_input_form_with_outputs(in_name: &str, out_name: &str) -> LNFormula {
    let in_fact = auto_fact(in_name, vec![bound(1), bound(2)]);
    all(
        "x",
        MSG,
        all(
            "m",
            MSG,
            all(
                "i",
                NODE,
                action(in_fact, bound(0)).implies(to_facts_term(out_name, or_ku())),
            ),
        ),
    )
}

// ---------------------------------------------------------------------------
// Fact-input cases (AUTO_*_FACT) — HS `addForm (_, Right _, _)` and
// `formulaMultArity` / `toFactsFact` (OpenTheory.hs:443-483, 520-533).
// ---------------------------------------------------------------------------

/// `listOfM n` (OpenTheory.hs:380-381): `["m1", "m2", ..., "mn"]`.
fn list_of_m(n: usize) -> Vec<String> {
    (1..=n).map(|k| format!("m{}", k)).collect()
}

/// `listVarTerm q s` (OpenTheory.hs:534-535): the occurrences `Bound q` down
/// to `Bound s`.
fn list_var_term(q: u64, s: u64) -> Vec<BLNTerm> {
    (s..=q).rev().map(bound).collect()
}

/// `formulaMultArity nb` (OpenTheory.hs:445-462): the `∀ m1..mn.` prefix with
/// `m1` outermost, wrapped around `∀ i.` and `body`.
fn formula_mult_arity(nb: usize, body: LNFormula) -> LNFormula {
    list_of_m(nb)
        .iter()
        .rev()
        .fold(all("i", NODE, body), |acc, h| all(h, MSG, acc))
}

/// `addForm (_, Right (_, []), _)` (OpenTheory.hs:443-462): no matching
/// outputs → `∀ m1..mn i. AUTO_IN_FACT(m1..mn) @ i ⇒ ⊥`.
fn fact_input_form_no_outputs(in_name: &str, arity: usize) -> LNFormula {
    let in_fact = auto_fact(in_name, list_var_term(arity as u64, 1));
    formula_mult_arity(
        arity,
        action(in_fact, bound(0)).implies(LNFormula::lfalse()),
    )
}

/// `toFactsFact ru p outn` (OpenTheory.hs:520-533): `∃ j. AUTO_OUT_FACT(…) @ j
/// ∧ j < i`, the output fact over the input binders `Bound (1 + arity)` down
/// to `Bound 2`.
fn to_facts_fact(out_name: &str, out_arity: usize) -> LNFormula {
    let out_fact = auto_fact(out_name, list_var_term(1 + out_arity as u64, 2));
    ex(
        "j",
        NODE,
        action(out_fact, bound(0)).and(less(bound(0), bound(1))),
    )
}

/// `addForm (_, Right (_, outs:_), _)` (OpenTheory.hs:464-483): with a
/// matching output → `∀ m1..mn i. AUTO_IN_FACT(m1..mn) @ i ⇒ toFactsFact`.
fn fact_input_form_with_outputs(
    in_name: &str,
    out_name: &str,
    in_arity: usize,
    out_arity: usize,
) -> LNFormula {
    let in_fact = auto_fact(in_name, list_var_term(in_arity as u64, 1));
    formula_mult_arity(
        in_arity,
        action(in_fact, bound(0)).implies(to_facts_fact(out_name, out_arity)),
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
    /// The source-lemma formula, starting from `⊤`.
    pub formula: LNFormula,
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
    match &o.rule_e().info.name {
        crate::rule::ProtoRuleName::Stand(n) => n,
        crate::rule::ProtoRuleName::Fresh => "Fresh",
    }
}

/// Port of `addAutoSourcesLemma`'s body (OpenTheory.hs:144-538) without the
/// theory-item plumbing: given the protocol rules and the open-chain cases,
/// compute the rule AUTO annotations and the source-lemma formula.
pub(crate) fn add_auto_sources_lemma(
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
    let mut rule_by_name: tamarin_utils::FastMap<&str, usize> = Default::default();
    for (ri, rule) in rules.iter().enumerate() {
        rule_by_name.entry(rule.name()).or_insert(ri);
    }

    let mut formula = LNFormula::ltrue();
    let mut annotation_groups: Vec<Vec<(String, LNFact)>> = Vec::new();
    let mut done: tamarin_utils::FastMap<&str, tamarin_utils::FastSet<ExtendedPosition>> =
        Default::default();

    for ((conc, _prem), source) in chains {
        let node_rules = source.node_rule_map();
        // v = head $ getFactTerms $ nodeConcFact conc source
        let Some(c_rule) = node_rules.get(&conc.0) else {
            continue;
        };
        let Some(conc_fact) = c_rule.conclusions.get(conc.1 .0) else {
            continue;
        };
        let Some(v) = conc_fact.terms.first().cloned() else {
            continue;
        };

        // unsolved premises of this source (for the fact-case guard).
        let unsolved_prem_keys: tamarin_utils::FastSet<NodePrem> = source
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
            let Some(rule_sys) = node_rules.get(&nodeid) else {
                continue;
            };
            let sys_name = rule_name_string(rule_sys);
            let Some(&ri) = rule_by_name.get(sys_name.as_str()) else {
                continue;
            };
            let rule = &rules[ri];
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
            let already_done = || {
                done.get(rin_name)
                    .is_some_and(|positions| positions.contains(pos))
            };
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
            formula = formula.and(part);
        }

        // addLabels + addCases (this chain's acts as one group).
        let mut grp: Vec<(String, LNFact)> = Vec::new();
        for (ri, m, pos) in &matches {
            let rin_name = rules[*ri].name();
            match m {
                Matched::Term {
                    protterm,
                    vin,
                    outs,
                } => {
                    let (in_name, out_name) = auto_names(m, pos, rin_name);
                    grp.push((
                        rin_name.to_string(),
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
                    let (in_name, out_name) = auto_names(m, pos, rin_name);
                    grp.push((
                        rin_name.to_string(),
                        ln_proto(&in_name, fact.terms.to_vec()),
                    ));
                    for (rout_i, fout) in outs {
                        grp.push((
                            rules[*rout_i].name().to_string(),
                            ln_proto(&out_name, fout.terms.to_vec()),
                        ));
                    }
                }
            }
            done.entry(rin_name).or_default().insert(pos.clone());
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
pub(crate) fn build_source_lemma(name: &str, formula: LNFormula) -> crate::theory::Lemma {
    use crate::theory::{Lemma, LemmaAttr, TraceQuantifier};
    Lemma {
        heuristic_in_file: None,
        name: name.to_string(),
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
pub(crate) fn has_lemma_named(items: &[TheoryItem], name: &str) -> bool {
    items
        .iter()
        .any(|it| matches!(it, TheoryItem::Lemma(l) if l.name == name))
}

/// Add an AUTO action to an open proto rule's AC form. HS adds to
/// `cprRuleAC` only (`addActionClosedProtoRule`, lib/theory/src/Rule.hs:97-99);
/// for a trivial-variant rule (no
/// abstracted form) that is the rule itself, which renders as
/// `rule (modulo E)` and propagates to its instances.  A rule that still IS
/// its own E half gets the pristine body snapshotted into `rule_e` first —
/// HS's untouched `cprRuleE`, which partial evaluation's `getProtoRuleEs`
/// must keep reading (see the field doc).
fn add_action_to_open_rule(o: &mut OpenProtoRule, action: LNFact) {
    if o.rule_e.is_none() {
        o.rule_e = Some(Box::new(o.rule.clone()));
    }
    if let Some(ar) = o.abstracted_rule.as_mut() {
        ar.add_action(action.clone());
    }
    o.rule.add_action(action);
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
                // `toClosedProtoRule` keeps the ORIGINAL rule as every
                // variant's `cprRuleE` (lib/theory/src/Rule.hs:75-76) — the
                // half `getProtoRuleEs` dedups back to one copy.
                rule_e: Some(Box::new(o.rule_e().clone())),
                // `unfoldRuleVariants` runs on a rule whose variants Maude
                // computed, which `closeProtoRule` reaches only for a rule
                // that declared none (lib/theory/src/Rule.hs:82-86).
                rule_ac: Vec::new(),
            }
        })
        .collect()
}

/// Re-express one closed AC half as the split open representation consumed by
/// [`unfold_one_rule_variants`]. This also covers source-declared
/// `variants (modulo AC)` blocks, whose bodies do not live in
/// `abstracted_rule`/`variant_substs` on their parent.
fn closed_rule_as_open(parent: &OpenProtoRule, ac: &crate::rule::ProtoRuleAC) -> OpenProtoRule {
    let rule = crate::rule::Rule {
        info: crate::rule::ProtoRuleEInfo {
            name: ac.info.name,
            attributes: ac.info.attributes.clone(),
            restrictions: parent.rule.info.restrictions.clone(),
        },
        premises: ac.premises.clone(),
        conclusions: ac.conclusions.clone(),
        actions: ac.actions.clone(),
        new_vars: ac.new_vars.clone(),
    };
    OpenProtoRule {
        rule,
        variant_substs: ac.info.variants.clone(),
        abstracted_rule: None,
        loop_breakers: ac.info.loop_breakers.clone(),
        rule_e: Some(Box::new(parent.rule_e().clone())),
        rule_ac: Vec::new(),
    }
}

/// HS `unfoldRules items` (CloseRule.hs:106-110) over the theory's item
/// list: replace every closed rule whose AC variant is non-trivial
/// (`isTrivialProtoVariantAC`, Theory/Model/Rule.hs:789-793) by its
/// per-variant rules ([`unfold_one_rule_variants`]); trivial-variant rules
/// stay unchanged, so the pass is the identity on a theory whose variants are
/// all trivial.
///
/// The variants take the unfolded rule's slot in item order, each carrying
/// the original as its `cprRuleE` half.  The printer regroups them:
/// `mergeOpenProtoRules` collapses the run sharing one `ruE`
/// (OpenTheory.hs:592-603) and `prettyOpenProtoRuleAsClosedRule` renders a
/// single AC body as `prettyProtoRuleACasE` (under the `___VARIANT_1` name,
/// as if modulo E) and several as `prettyProtoRuleE ruE` plus a ` variants`
/// block of `rule (modulo AC)` sub-blocks (OpenTheory.hs:827-850).
///
/// Returns `true` iff any rule was unfolded.
fn unfold_rule_variants(elaborated: &mut crate::theory::Theory) -> bool {
    // Decision pass over the rules in item order: one entry per rule item
    // (`None` = trivial, keep).
    let mut elab_repl: Vec<Option<Vec<OpenProtoRule>>> = Vec::new();
    for item in &elaborated.items {
        let TheoryItem::Rule(o) = item else { continue };
        // HS `isTrivialProtoVariantAC ruAC ruE` over the closed rules the item
        // closes into (lib/theory/src/Rule.hs:82-86): a rule declaring its own
        // `variants (modulo AC)` blocks yields one closed rule per block, and
        // the item is left alone when every one of them is trivial.
        let closed = crate::theory::closed_rules_ac(o);
        if closed
            .iter()
            .all(|ac| crate::rule::is_trivial_proto_variant_ac(ac, o.rule_e()))
        {
            elab_repl.push(None);
            continue;
        }
        let mut unfolded = Vec::new();
        for ac in &closed {
            let open = closed_rule_as_open(o, ac);
            if crate::rule::is_trivial_proto_variant_ac(ac, o.rule_e()) {
                unfolded.push(open);
            } else {
                unfolded.extend(unfold_one_rule_variants(&open));
            }
        }
        elab_repl.push(Some(unfolded));
    }
    if elab_repl.iter().all(|r| r.is_none()) {
        return false;
    }

    // Each rule item takes its replacement run.
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
    true
}

/// Apply `--auto-sources` (HS `closeTheoryWithMaude`'s autosources branch,
/// CloseRule.hs:56-137, see line 58,106-112).  When the raw sources contain
/// partial deconstructions, unfold every rule into its AC-variant rules
/// ([`unfold_rule_variants`]), annotate them with AUTO_* actions and append
/// the `AUTO_typing` sources lemma.  `ndc_cache` is the theory's
/// once-per-load NDC-checked intruder cache, injected into the scratch
/// contexts below so they reuse the tagged+permuted rules instead of
/// re-running the check.  Returns `true` iff anything was added.
pub fn apply_auto_sources(
    elaborated: &mut crate::theory::Theory,
    maude: MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    ndc_cache: Option<&crate::constraint::solver::context::IntrRuleCache>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> Result<bool, crate::prove::ProveError> {
    use crate::constraint::solver::context::{ProofContext, ProofContextOptions};
    use crate::guarded::formula_to_guarded;

    // Both scratch contexts below share the caller's one rule list.
    let ndc_cache = ndc_cache.cloned();

    let restrictions = elaborated
        .restrictions()
        .map(|r| formula_to_guarded(&r.formula))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| crate::prove::ProveError::Guarded(error.to_string()))?;
    let rules: Vec<OpenProtoRule> = elaborated.rules().cloned().collect();

    // collect open destruction chains across a context's (saturated) source
    // cases.
    fn collect_chains(
        ctx: &ProofContext,
    ) -> Result<Vec<((NodeConc, NodePrem), System)>, crate::prove::ProveError> {
        let mut chains = Vec::new();
        for src in ctx.full_sources.iter() {
            for (_name, sys) in src.cases(ctx)?.iter() {
                for ch in sys.unsolved_chains() {
                    chains.push((ch, sys.clone()));
                }
            }
        }
        Ok(chains)
    }

    // GENERATION chains: the RAW (saturated, unrefined) sources — HS
    // `addAutoSourcesLemma` uses `crcRawSources` (RuleItem.hs:64-70, see line 66).
    let ctx_raw = ProofContext::try_with_options(
        maude.clone(),
        rules.clone(),
        ProofContextOptions {
            maude_pool: pool.clone(),
            restrictions: restrictions.clone(),
            intruder_rules: ndc_cache.clone(),
            parameters,
            show_saturation_steps: true,
            loop_breakers_prepared: true,
            ..Default::default()
        },
    )?;
    let raw_chains = collect_chains(&ctx_raw)?;

    // TRIGGER: HS `containsPartialDeconstructions` checks the REFINED sources
    // (crcRefinedSources, field 3) — those refined by the theory's existing
    // `[sources]` lemmas. When such lemmas exist they can close the open
    // chains, so the trigger is OFF even though the raw sources still have
    // them (e.g. NSPK3 with a manual `types [sources]` lemma). Build a second
    // context whose typing assumptions are those lemmas and check ITS chains.
    let typing_asms: Vec<crate::guarded::Guarded> = elaborated
        .lemmas()
        .filter(|l| l.is_source_assumption())
        .map(|l| formula_to_guarded(&l.formula))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| crate::prove::ProveError::Guarded(error.to_string()))?;
    let trigger = if typing_asms.is_empty() {
        // refined == raw
        !raw_chains.is_empty()
    } else {
        let mut ctx_ref = ProofContext::try_with_options(
            maude.clone(),
            rules.clone(),
            ProofContextOptions {
                maude_pool: pool.clone(),
                restrictions: restrictions.clone(),
                intruder_rules: ndc_cache.clone(),
                parameters,
                show_saturation_steps: true,
                loop_breakers_prepared: true,
                ..Default::default()
            },
        )?;
        ctx_ref.typing_assumptions = typing_asms.into_iter().map(std::sync::Arc::new).collect();
        !collect_chains(&ctx_ref)?.is_empty()
    };
    if !trigger {
        return Ok(false);
    }

    // `itemsModAC = unfoldRules items` (CloseRule.hs:106-110): once the
    // trigger fires, every closed rule is replaced by its per-AC-variant
    // rules BEFORE the AUTO lemma is computed, so the AUTO_* names and
    // annotations reference the `___VARIANT_<i>` rules.  The loop breakers
    // were computed before this point and are carried into each variant
    // verbatim.
    let unfolded = unfold_rule_variants(elaborated);
    // `cache itemsModAC` (CloseRule.hs:112): `addAutoSourcesLemma` reads the
    // rule cache RECOMPUTED over the unfolded rules.  When nothing unfolded,
    // `itemsModAC == items` and the cache has the same value — reuse the
    // original context's chains (and its saturation trace count).
    let (rules, gen_chains) = if unfolded {
        let rules: Vec<OpenProtoRule> = elaborated.rules().cloned().collect();
        let ctx_mod = ProofContext::try_with_options(
            maude.clone(),
            rules.clone(),
            ProofContextOptions {
                maude_pool: pool,
                restrictions,
                intruder_rules: ndc_cache,
                parameters,
                show_saturation_steps: true,
                loop_breakers_prepared: true,
                ..Default::default()
            },
        )?;
        let chains = collect_chains(&ctx_mod)?;
        (rules, chains)
    } else {
        (rules, raw_chains)
    };

    let result = add_auto_sources_lemma(&maude, &rules, &gen_chains);

    // addLabels: add the AUTO actions to the matching rules. HS folds the
    // per-rule act list right-to-left over `addActionClosedProtoRule`
    // (prepend-if-absent); iterating the global list in reverse + prepend
    // reproduces that order.
    for grp in &result.annotation_groups {
        for (rule_name, action) in grp.iter().rev() {
            for item in elaborated.items.iter_mut() {
                if let TheoryItem::Rule(o) = item
                    && o.name() == rule_name
                {
                    add_action_to_open_rule(o, action.clone());
                }
            }
        }
    }

    // Add the lemma unless one of the same name already exists
    // (OpenTheory.hs:145-148).
    if !has_lemma_named(&elaborated.items, "AUTO_typing") {
        elaborated.items.push(TheoryItem::Lemma(build_source_lemma(
            "AUTO_typing",
            result.formula,
        )));
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_formula::{lemma_header_line_doc, lnformula_doc};

    /// The `--auto-sources` unfold (`unfoldRuleVariants`,
    /// lib/theory/src/Rule.hs:63-79): a rule with a non-trivial variant
    /// disjunction is replaced in the item list by one `___VARIANT_<i>` rule
    /// per substitution, each carrying the trivial disjunction, the
    /// original's loop breakers, and the original rule as its `cprRuleE`
    /// half; a trivial-variant rule stays untouched.
    #[test]
    fn unfold_replaces_nontrivial_rules_with_variant_rules() {
        use crate::fact::{fresh_fact, in_fact, out_fact};
        use crate::rule::{PremIdx, ProtoRuleEInfo, Rule};
        use crate::theory::{OpenProtoRule, Theory, TheoryItem};
        use tamarin_term::builtin::{fresh_var, fst, msg_var};
        use tamarin_term::maude_proc::MaudeHandle;
        use tamarin_term::maude_sig::pair_maude_sig;

        let Some(path) = tamarin_test_support::require_maude_path() else {
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

        let mut elab: Theory = Theory::new("T", tamarin_term::maude_sig::minimal_maude_sig(false));
        elab.items = vec![TheoryItem::Rule(nt), TheoryItem::Rule(tr.clone())];

        assert!(unfold_rule_variants(&mut elab));

        // NT expands in place into one rule per substitution; TR keeps its
        // slot and its fields.
        let names: Vec<&str> = elab.rules().map(|r| r.name()).collect();
        let mut expect: Vec<String> = (1..=substs.len())
            .map(|i| format!("NT___VARIANT_{}", i))
            .collect();
        expect.push("TR".to_string());
        assert_eq!(names, expect);
        let variants: Vec<&OpenProtoRule> = elab
            .rules()
            .filter(|r| r.name().starts_with("NT___VARIANT_"))
            .collect();
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

        // `toClosedProtoRule` gives every variant the SAME `ruE`
        // (lib/theory/src/Rule.hs:74-75), which is what lets
        // `mergeOpenProtoRules` collapse the run back into one item
        // (OpenTheory.hs:592-603).
        assert!(variants.windows(2).all(|w| w[0].rule_e() == w[1].rule_e()));
    }

    #[test]
    fn unfold_uses_source_declared_variant_bodies() {
        use crate::fact::{in_fact, out_fact};
        use crate::rule::{ProtoRuleEInfo, Rule};
        use crate::theory::{OpenProtoRule, Theory, TheoryItem};
        use tamarin_term::builtin::msg_var;

        let original = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![in_fact(msg_var("x", 0))],
            vec![out_fact(msg_var("x", 0))],
            vec![],
        );
        let declared = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![in_fact(msg_var("x", 0)), in_fact(msg_var("y", 0))],
            vec![out_fact(msg_var("x", 0))],
            vec![],
        );
        let mut open = OpenProtoRule::new(original.clone());
        open.rule_ac.push(declared.clone());
        let mut theory = Theory::new("T", tamarin_term::maude_sig::minimal_maude_sig(false));
        theory.items.push(TheoryItem::Rule(open));

        assert!(unfold_rule_variants(&mut theory));
        let unfolded = theory.rules().next().expect("unfolded rule");
        assert_eq!(unfolded.name(), "R___VARIANT_1");
        assert_eq!(unfolded.rule.premises, declared.premises);
        assert_eq!(unfolded.rule_e.as_deref(), Some(&original));
    }

    // Ground truth: the `AUTO_typing` lemma body emitted by the Haskell
    // prover for examples/features/auto-sources/running-example/running.spthy
    // (HS `--auto-sources`). The formula is `(⊤) ∧ (the term-input form)`.
    #[test]
    fn running_example_auto_typing_renders_byte_identically() {
        let in_name = "AUTO_IN_TERM_1_0_0_1_1__Rule_R";
        let out_name = "AUTO_OUT_TERM_1_0_0_1_1__Rule_R";
        let f = LNFormula::ltrue().and(term_input_form_with_outputs(in_name, out_name));
        let rendered = lemma_header_line_doc("all-traces", lnformula_doc(&f));
        let expected = "  all-traces\n  \"(⊤) ∧\n   (∀ x m #i.\n     (AUTO_IN_TERM_1_0_0_1_1__Rule_R( m, x ) @ #i) ⇒\n     ((∃ #j. (!KU( x ) @ #j) ∧ (#j < #i)) ∨\n      (∃ #j. (AUTO_OUT_TERM_1_0_0_1_1__Rule_R( m ) @ #j) ∧ (#j < #i))))\"";
        assert_eq!(rendered, expected);
    }
}
