// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of Haskell's `--auto-sources` lemma generation
//! (`addAutoSourcesLemma`, `lib/theory/src/OpenTheory.hs`).
//!
//! When `--auto-sources` is set, Tamarin prepares unfolded, uniquely named
//! rules for a shared preliminary cache. If the refined sources still have
//! open chains, it generates annotations from the raw sources. Unfolding
//! expands each closed rule into its AC variants (`itemsModAC = unfoldRules items`,
//! CloseRule.hs; `unfoldRuleVariants`, lib/theory/src/Rule.hs
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
use crate::tools::rule_variants::unfold_closed_rule;
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

/// `Qua All (name, sort)` (OpenTheory.hs).
fn all(name: &str, sort: LSort, body: LNFormula) -> LNFormula {
    LNFormula::for_all((name.to_string(), sort), body)
}

/// `Qua Ex (name, sort)` (OpenTheory.hs).
fn ex(name: &str, sort: LSort, body: LNFormula) -> LNFormula {
    LNFormula::exists((name.to_string(), sort), body)
}

/// `Ato (Action tp fa)` (OpenTheory.hs).
fn action(fa: Fact<BLNTerm>, tp: BLNTerm) -> LNFormula {
    LNFormula::Atom(ProtoAtom::Action(tp, fa))
}

/// `Ato (Less a b)` (OpenTheory.hs).
fn less(a: BLNTerm, b: BLNTerm) -> LNFormula {
    LNFormula::Atom(ProtoAtom::Less(a, b))
}

/// The four AUTO action facts — `inputFactTerm`, `inputFactFact`,
/// `outputFactTerm` and `outputFactFact` (OpenTheory.hs): a linear
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

/// `orKU` (OpenTheory.hs): `∃ j. !KU(x) @ j ∧ j < i`, read under the
/// `x`, `m`, `i` prefix that `Bound 3` and `Bound 1` point back into.
fn or_ku() -> LNFormula {
    let ku = Fact::new(FactTag::Ku, vec![bound(3)]);
    ex(
        "j",
        NODE,
        action(ku, bound(0)).and(less(bound(0), bound(1))),
    )
}

/// `toFactsTerm ru p f''` (OpenTheory.hs):
/// `f'' ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i)`.
fn to_facts_term(out_name: &str, inner: LNFormula) -> LNFormula {
    inner.or(ex(
        "j",
        NODE,
        action(auto_fact(out_name, vec![bound(2)]), bound(0)).and(less(bound(0), bound(1))),
    ))
}

/// `addForm` protected-subterm case with NO matching outputs
/// (OpenTheory.hs): `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒ orKU`.
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
/// (OpenTheory.hs): `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒
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
// `formulaMultArity` / `toFactsFact` (OpenTheory.hs).
// ---------------------------------------------------------------------------

/// `listOfM n` (OpenTheory.hs): `["m1", "m2", ..., "mn"]`.
fn list_of_m(n: usize) -> Vec<String> {
    (1..=n).map(|k| format!("m{}", k)).collect()
}

/// `listVarTerm q s` (OpenTheory.hs): the occurrences `Bound q` down
/// to `Bound s`.
fn list_var_term(q: u64, s: u64) -> Vec<BLNTerm> {
    (s..=q).rev().map(bound).collect()
}

/// `formulaMultArity nb` (OpenTheory.hs): the `∀ m1..mn.` prefix with
/// `m1` outermost, wrapped around `∀ i.` and `body`.
fn formula_mult_arity(nb: usize, body: LNFormula) -> LNFormula {
    list_of_m(nb)
        .iter()
        .rev()
        .fold(all("i", NODE, body), |acc, h| all(h, MSG, acc))
}

/// `addForm (_, Right (_, []), _)` (OpenTheory.hs): no matching
/// outputs → `∀ m1..mn i. AUTO_IN_FACT(m1..mn) @ i ⇒ ⊥`.
fn fact_input_form_no_outputs(in_name: &str, arity: usize) -> LNFormula {
    let in_fact = auto_fact(in_name, list_var_term(arity as u64, 1));
    formula_mult_arity(
        arity,
        action(in_fact, bound(0)).implies(LNFormula::lfalse()),
    )
}

/// `toFactsFact ru p outn` (OpenTheory.hs): `∃ j. AUTO_OUT_FACT(…) @ j
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

/// `addForm (_, Right (_, outs:_), _)` (OpenTheory.hs): with a
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
// Discovery: walk the open chains, match inputs to outputs (OpenTheory.hs).
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
/// guard (OpenTheory.hs) skip SIBLING
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

/// Port of `addAutoSourcesLemma`'s body (OpenTheory.hs) without the
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
/// AllTraces formula`, OpenTheory.hs).  `unprovenLemma`
/// seeds `_lOriginalFormula` with the same formula
/// (Theory/ProofSkeleton.hs).
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
        // (`Theory/ProofSkeleton.hs`).
        plaintext: "Unpr_inSkeleton".to_string(),
    }
}

/// Whether the theory already contains a lemma named `name`
/// (HS `find lemma items`, OpenTheory.hs).
pub(crate) fn has_lemma_named(items: &[TheoryItem], name: &str) -> bool {
    items
        .iter()
        .any(|it| matches!(it, TheoryItem::Lemma(l) if l.name == name))
}

/// Add an AUTO action to an open proto rule's AC form. HS adds to
/// `cprRuleAC` only (`addActionClosedProtoRule`, lib/theory/src/Rule.hs);
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

/// HS `unfoldRules items` (CloseRule.hs) over the theory's item
/// list: replace every closed rule whose AC variant is non-trivial
/// (`isTrivialProtoVariantAC`, Theory/Model/Rule.hs) by its
/// per-variant rules ([`unfold_closed_rule`]). Explicit members, including
/// trivial ones, each become a separate open rule so cache construction,
/// temporary naming and annotation all use the same executable body.
/// Ordinary computed trivial rules stay unchanged.
///
/// The variants take the unfolded rule's slot in item order, each carrying
/// the original as its `cprRuleE` half.  The printer regroups them:
/// `mergeOpenProtoRules` collapses the run sharing one `ruE`. A separately
/// named singleton stays inside its parent family, just like multiple AC
/// members; only a safe same-name identity family can print as a standalone
/// E rule (OpenTheory.hs).
///
fn unfold_rule_variants(elaborated: &mut crate::theory::Theory) {
    let items = std::mem::take(&mut elaborated.items);
    let mut new_items = Vec::with_capacity(items.len());
    for item in items {
        let TheoryItem::Rule(o) = item else {
            new_items.push(item);
            continue;
        };
        // HS `isTrivialProtoVariantAC ruAC ruE` over the closed rules the item
        // closes into (lib/theory/src/Rule.hs): a rule declaring its own
        // `variants (modulo AC)` blocks yields one closed rule per block, and
        // each member must be represented separately even if it is trivial.
        let closed = crate::theory::closed_rules_ac(&o);
        if o.rule_ac.is_empty()
            && closed
                .iter()
                .all(|ac| crate::rule::is_trivial_proto_variant_ac(ac, o.rule_e()))
        {
            new_items.push(TheoryItem::Rule(o));
            continue;
        }
        new_items.extend(
            closed
                .iter()
                .flat_map(|ac| unfold_closed_rule(&o, ac))
                .map(TheoryItem::Rule),
        );
    }
    elaborated.items = new_items;
}

/// Apply `--auto-sources` (HS `closeTheoryWithMaude`'s autosources branch,
/// CloseRule.hs#closeTheoryWithMaude). The preliminary cache uses unfolded,
/// temporarily named rules. When its refined sources contain partial
/// deconstructions, annotate the public unfolded rules and append
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

    let restrictions = elaborated
        .restrictions()
        .map(|r| formula_to_guarded(&r.formula))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| crate::prove::ProveError::Guarded(error.to_string()))?;
    // Match CloseRule.cachePre: prepare the same unfolded, uniquely named
    // rule set before both trigger refinement and annotation generation.
    // Commit the unfolded public rules only if the trigger fires.
    let mut prepared = elaborated.clone();
    unfold_rule_variants(&mut prepared);
    let rules = auto_source_rule_names(&prepared.rules().cloned().collect::<Vec<_>>());
    let mut ctx = ProofContext::try_with_options(
        maude.clone(),
        rules.clone(),
        ProofContextOptions {
            maude_pool: pool,
            macros: prepared.macros().cloned().collect(),
            restrictions,
            intruder_rules: ndc_cache.cloned(),
            parameters,
            show_saturation_steps: true,
            loop_breakers_prepared: true,
            ..Default::default()
        },
    )?;
    ctx.typing_assumptions = elaborated
        .lemmas()
        .filter(|l| l.is_source_assumption())
        .map(|l| formula_to_guarded(&l.formula).map(std::sync::Arc::new))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| crate::prove::ProveError::Guarded(error.to_string()))?;
    let (raw, refined) = ctx.build_source_sets()?;
    let trigger = refined.iter().any(|source| {
        source
            .cases()
            .expect("saturated source has cases")
            .iter()
            .any(|(_, system)| system.unsolved_chains().next().is_some())
    });
    if !trigger {
        return Ok(false);
    }
    let mut chains = Vec::new();
    for source in raw.iter() {
        for (_, system) in source.cases().expect("saturated source has cases").iter() {
            for chain in system.unsolved_chains() {
                chains.push((chain, system.clone()));
            }
        }
    }
    let result = add_auto_sources_lemma(&maude, &rules, &chains);
    *elaborated = prepared;

    // addLabels: add the AUTO actions to the matching rules. HS folds the
    // per-rule act list right-to-left over `addActionClosedProtoRule`
    // (prepend-if-absent); iterating the global list in reverse + prepend
    // reproduces that order.
    for grp in &result.annotation_groups {
        for (rule_name, action) in grp.iter().rev() {
            for (o, named) in elaborated
                .items
                .iter_mut()
                .filter_map(|item| match item {
                    TheoryItem::Rule(rule) => Some(rule),
                    _ => None,
                })
                .zip(&rules)
            {
                if named.name() == rule_name {
                    add_action_to_open_rule(o, action.clone());
                }
            }
        }
    }

    // Add the lemma unless one of the same name already exists
    // (OpenTheory.hs).
    if !has_lemma_named(&elaborated.items, "AUTO_typing") {
        elaborated.items.push(TheoryItem::Lemma(build_source_lemma(
            "AUTO_typing",
            result.formula,
        )));
    }
    Ok(true)
}

/// Names used only while building the auto-sources cache and routing actions.
/// Public E/AC names stay unchanged; identical repeated rules share a label.
fn auto_source_rule_names(rules: &[OpenProtoRule]) -> Vec<OpenProtoRule> {
    use crate::rule::ProtoRuleName;
    use std::collections::BTreeSet;
    let reserved: BTreeSet<_> = rules
        .iter()
        .flat_map(|r| [r.rule.info.name, r.rule_e().info.name])
        .collect();
    let mut used = BTreeSet::new();
    let mut assigned: Vec<(&OpenProtoRule, ProtoRuleName)> = Vec::new();
    rules
        .iter()
        .map(|rule| {
            let name =
                if let Some((_, name)) = assigned.iter().find(|(original, _)| *original == rule) {
                    *name
                } else {
                    let old = rule.rule.info.name;
                    let name = if used.contains(&old) {
                        (1..)
                            .map(|i| {
                                ProtoRuleName::Stand(tamarin_term::intern::intern_str(&format!(
                                    "{}___AUTO_{i}",
                                    rule.name()
                                )))
                            })
                            .find(|name| !reserved.contains(name) && !used.contains(name))
                            .unwrap()
                    } else {
                        old
                    };
                    used.insert(name);
                    assigned.push((rule, name));
                    name
                };
            let mut named = rule.clone();
            if name != rule.rule.info.name {
                // Changing only the executable half preserves the original family.
                named.rule_e = Some(Box::new(rule.rule_e().clone()));
                named.rule.info.name = name;
                if let Some(abstracted) = &mut named.abstracted_rule {
                    abstracted.info.name = name;
                }
            }
            named
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_formula::{lemma_header_line_doc, lnformula_doc};

    /// The `--auto-sources` unfold (`unfoldRuleVariants`,
    /// lib/theory/src/Rule.hs): a rule with a non-trivial variant
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

        unfold_rule_variants(&mut elab);

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
            // rule as the `cprRuleE` half (lib/theory/src/Rule.hs).
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
        // (lib/theory/src/Rule.hs), which is what lets
        // `mergeOpenProtoRules` collapse the run back into one item
        // (OpenTheory.hs).
        assert!(variants.windows(2).all(|w| w[0].rule_e() == w[1].rule_e()));
    }

    #[test]
    fn temporary_aliases_reach_trivial_abstracted_bodies() {
        let parsed = tamarin_parser::parse_theory(
            r#"theory Aliases begin
            builtins: symmetric-encryption
            rule R: [] --[A()]-> []
            rule Other: [In(sdec('a','b'))] --[B()]-> []
            end"#,
            &[],
        )
        .unwrap();
        let mut theory = crate::elaborate::elaborate(&parsed).unwrap();
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let maude = MaudeHandle::start(&path, theory.signature.clone()).unwrap();
        crate::tools::rule_variants::populate_rule_variants(&mut theory, &maude, None).unwrap();
        let mut rules: Vec<_> = theory.rules().cloned().collect();
        // Model a compiled member colliding with an independent source rule.
        rules[0].rule.info.name = rules[1].rule.info.name;
        assert!(rules[1].abstracted_rule.is_some());
        assert!(crate::theory::closed_rules_ac(&rules[1])
            .iter()
            .all(|ac| crate::rule::is_trivial_proto_variant_ac(ac, rules[1].rule_e())));
        let named = auto_source_rule_names(&rules);
        assert_ne!(named[0].name(), named[1].name());
        assert_eq!(named[1].rule_e(), rules[1].rule_e());
        assert_eq!(
            named[1].abstracted_rule.as_ref().unwrap().info.name,
            named[1].rule.info.name
        );
        let ctx = crate::constraint::solver::context::ProofContext::new(maude, named);
        let rule = &ctx.rules[1];
        assert_eq!(
            rule.abstracted_rule.as_ref().unwrap().info.name,
            rule.rule.info.name
        );
    }

    #[test]
    fn unfold_prepares_trivial_explicit_members_for_annotation() {
        use crate::fact::{in_fact, out_fact, proto_fact};
        use crate::rule::{ProtoRuleEInfo, Rule};
        use crate::theory::Theory;
        use tamarin_term::builtin::msg_var;

        let original = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![in_fact(msg_var("x", 0))],
            vec![out_fact(msg_var("x", 0))],
            vec![],
        );
        let mut member = original.clone();
        member.info.name = crate::rule::ProtoRuleName::Stand("R___VARIANT_1");
        let mut open = OpenProtoRule::new(original.clone());
        // Repeated identical members must retain their order and share labels.
        open.rule_ac = vec![member.clone(), member.clone()];
        let mut theory = Theory::new("T", tamarin_term::maude_sig::minimal_maude_sig(false));
        theory.items.push(TheoryItem::Rule(open));

        unfold_rule_variants(&mut theory);
        let rules: Vec<_> = theory.rules().cloned().collect();
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0], rules[1]);
        for mut rule in auto_source_rule_names(&rules) {
            assert_eq!(rule.name(), "R___VARIANT_1");
            let action = proto_fact(Multiplicity::Linear, "AUTO_OUT", vec![msg_var("x", 0)]);
            add_action_to_open_rule(&mut rule, action.clone());
            let closed = crate::theory::closed_rules_ac(&rule);
            assert_eq!(closed.len(), 1);
            assert!(closed[0].actions.contains(&action));
            assert_eq!(closed[0].premises, member.premises);
            assert_eq!(closed[0].conclusions, member.conclusions);
            assert_eq!(rule.rule_e(), &original);
            assert!(rule.rule_ac.is_empty());
        }
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

        unfold_rule_variants(&mut theory);
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
