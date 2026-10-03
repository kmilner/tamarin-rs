// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.AbstractInterpretation` — abstract interpretation
//! for partial evaluation of multiset rewriting systems — plus the theory
//! rewrite HS performs in `applyPartialEvaluation` (Prover.hs).
//!
//! Algorithm (HS `interpretAbstractly`, AbstractInterpretation.hs):
//! starting from the abstract state `{ Fr(~z), In(z) }`, repeatedly refine
//! every compiled rule against the state (each premise AC-unified via Maude
//! against every state fact with the same tag) and add the refined rules'
//! abstracted conclusions to the state, until the state stabilises.  The
//! final rule list is each refined rule `rename`d so its minimum variable
//! index is 0, deduplicated modulo variable freshness
//! (`eqModuloFreshnessNoAC`, first occurrence wins).
//! Input must be the complete, unfolded family of compiled E-variants, not
//! the original E rules. Family IDs survive refinement and deduplication;
//! export retains the original family whenever recompilation would change a
//! member's instances. Embedded restrictions have already become theory items.
//!
//! A structural subtlety this module must reproduce: a rule carries its
//! `_restrict` formulas in `ProtoRuleEInfo::restrictions` (HS
//! `preRestriction`), `HasFrees (Rule i)` folds over them before the body
//! (Theory/Model/Rule.hs, Theory/Model/Rule.hs) and `Apply
//! ProtoRuleEInfo` is the identity (Theory/Model/Rule.hs).  So a
//! refined rule keeps its ORIGINAL restriction frees unsubstituted, and they
//! floor the final `rename`'s index shift and are bound first by
//! `eqModuloFreshnessNoAC`'s canonicalisation.  [`info_frees`] reads them off
//! the rule.  `HasFrees for Rule<I>` (rule.rs) skips `info`, so the shift and
//! the canonicalisation pass the frees as a separate list and leave the
//! formulas alone: every refinement of one rule carries the same formulas, so
//! they cannot tell two refinements apart. The trace-theory caller now clears
//! these local formulas from compiled members; generic evaluator tests still
//! cover the info-aware traversal contract.
//!
//! Divergences from HS, all deliberate:
//! * **Trace emission**: HS traces via `Debug.Trace` thunks that fire when
//!   the closed theory is rendered — AFTER the `[Theory X] Theory closed`
//!   stderr marker.  [`partial_evaluation`]/[`apply_partial_evaluation`]
//!   therefore RETURN the exact trace bytes instead of `eprint!`ing them;
//!   the caller must emit them right after its "Theory closed" marker to
//!   match HS stderr ordering.
//! * **Rule ordering key**: HS sorts `getProtoRuleEs` under the derived
//!   `Ord (Rule i)` = (info, prems, concs, acts, newVars) with
//!   `Ord ProtoRuleEInfo` = (name, attributes, restrictions).  RS
//!   `SyntacticLNFormula` has no `Ord`, so the restrictions cannot enter a
//!   sort key and this one is (name, prems, concs, acts, new_vars).  The
//!   attribute/restriction tiebreak is unreachable: duplicate rule names are
//!   rejected at parse time, so the name alone already discriminates the
//!   input.

use std::collections::BTreeSet;

use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::{avoid, rename, sort_of_lnterm, HasFrees, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::rewriting::Equal;
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::{f_app, Term};
use tamarin_term::vterm::{var_term, Lit};
use tamarin_utils::fresh::FastFreshState;

use crate::fact::{fresh_fact, in_fact, out_fact, pretty_lnfact, FactTag, LNFact};
use crate::pretty_hpj::{self as hpj, Doc};
use crate::rule::{unify_ln_fact_eqs, ProtoRuleE, ProtoRuleEInfo, Rule};
use crate::theory::{OpenProtoRule, Theory, TheoryItem};

/// How to report on performing a partial evaluation.  HS
/// `EvaluationStyle` (AbstractInterpretation.hs); the CLI maps
/// `SUMMARY` → `Summary` and `VERBOSE` → `Tracing`
/// (TheoryLoader.hs); `Silent` is unreachable from the CLI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvaluationStyle {
    Silent,
    Summary,
    Tracing,
}

// =============================================================================
// absFact / absTerm (AbstractInterpretation.hs)
// =============================================================================

/// Per-fact abstraction state: HS's `evalBind noBindings` +
/// `evalFreshT nothingUsed` pair — a binding map keyed by the WHOLE
/// sub-term and a single fresh counter, both reset for every fact.
struct AbsState {
    counter: u64,
    bindings: Vec<(LNTerm, LNTerm)>,
}

/// HS `absTerm` (AbstractInterpretation.hs): constants survive,
/// `NoEq` applications are recursed into, everything else (variables and
/// AC/C/List applications) is replaced via `importBinding` — identical
/// sub-terms within one fact share the imported variable; a fresh variable
/// carries the sub-term's sort, the variable's own name as hint (or `"z"`
/// for non-variables), and the next per-fact index.
fn abs_term(t: &LNTerm, st: &mut AbsState) -> LNTerm {
    match t {
        Term::Lit(Lit::Con(_)) => t.clone(),
        Term::App(fsym @ FunSym::NoEq(_), args) => {
            let new_args: Vec<LNTerm> = args.iter().map(|a| abs_term(a, st)).collect();
            f_app(*fsym, new_args)
        }
        _ => {
            if let Some((_, v)) = st.bindings.iter().find(|(k, _)| k == t) {
                return v.clone();
            }
            let name = match t {
                Term::Lit(Lit::Var(v)) => v.name,
                _ => "z",
            };
            let v = var_term(LVar::new(name, sort_of_lnterm(t), st.counter));
            st.counter += 1;
            st.bindings.push((t.clone(), v.clone()));
            v
        }
    }
}

/// HS `absFact` (AbstractInterpretation.hs): every `Out` fact
/// collapses to `Out( z )` with `z = LVar "z" LSortMsg 0` (annotations
/// dropped — `outFact` builds a default-annotation fact); any other fact
/// keeps its tag and annotations with the terms abstracted left-to-right
/// under one per-fact binding map / counter.
fn abs_fact(fa: &LNFact) -> LNFact {
    match fa.tag {
        FactTag::Out => out_fact(var_term(LVar::new("z", LSort::Msg, 0))),
        _ => {
            let mut st = AbsState {
                counter: 0,
                bindings: Vec::new(),
            };
            let terms: Vec<LNTerm> = fa.terms.iter().map(|t| abs_term(t, &mut st)).collect();
            LNFact::fresh_annotated(fa.tag, fa.annotations.clone(), terms)
        }
    }
}

// =============================================================================
// interpretAbstractly (AbstractInterpretation.hs)
// =============================================================================

/// HS `refineRule` (AbstractInterpretation.hs), the `FreshT []`
/// nondeterminism made explicit as a DFS: for each premise (in order),
/// choose a state fact with the same tag (state facts visited in sorted
/// `S.toList` order — premise 1 varies SLOWEST) and `rename` it above the
/// branch's fresh counter; at the leaf, E-unify the whole equation list
/// once modulo AC, and for each unifier `freshToFree` it from the branch counter and
/// apply it to the rule.  Branch alternatives never share a counter — each
/// starts from the incoming value (HS `mplus` on `StateT Integer []` runs
/// both alternatives from the same state).
trait EvaluationInfo: Clone + PartialEq {
    fn proto_info(&self) -> &ProtoRuleEInfo;
}

impl EvaluationInfo for ProtoRuleEInfo {
    fn proto_info(&self) -> &ProtoRuleEInfo {
        self
    }
}

impl EvaluationInfo for (usize, ProtoRuleEInfo) {
    fn proto_info(&self) -> &ProtoRuleEInfo {
        &self.1
    }
}

fn refine_rule<I: EvaluationInfo>(
    maude: &MaudeHandle,
    state_facts: &[&LNFact],
    ru: &Rule<I>,
    out: &mut Vec<Rule<I>>,
) -> Result<(), MaudeError> {
    fn go<I: EvaluationInfo>(
        maude: &MaudeHandle,
        state_facts: &[&LNFact],
        ru: &Rule<I>,
        prem_idx: usize,
        counter: FastFreshState,
        eqs: &mut Vec<Equal<LNFact>>,
        out: &mut Vec<Rule<I>>,
    ) -> Result<(), MaudeError> {
        if prem_idx == ru.premises.len() {
            // Leaf: one unification query over the whole equation list
            // (HS `unifyFactEqs eqs`); zero premises yield the trivial
            // unifier, so premise-less rules survive unchanged.
            let unifiers = unify_ln_fact_eqs(maude, eqs)?;
            for u in unifiers {
                let s_fresh = LNSubstVFresh::from_list(u);
                // `freshToFree` allocating from THIS branch's counter
                // (each unifier alternative starts from the same value).
                let mut c = counter.clone();
                let sigma = s_fresh.fresh_to_free_avoiding(|n| c.fresh_idents(n));
                out.push(crate::rule::apply_subst_rule(&sigma, ru));
            }
            return Ok(());
        }
        let prem = &ru.premises[prem_idx];
        for fa in state_facts.iter().filter(|f| f.tag == prem.tag) {
            let mut c = counter.clone();
            let fa_renamed = rename((*fa).clone(), &mut c);
            eqs.push(Equal {
                lhs: prem.clone(),
                rhs: fa_renamed,
            });
            go(maude, state_facts, ru, prem_idx + 1, c, eqs, out)?;
            eqs.pop();
        }
        Ok(())
    }
    // Seed: `evalFreshT (avoid ru)` — the counter starts above the rule's
    // maximum free variable index.  HS's `avoid` folds the rule info too
    // (`HasFrees (Rule i)`, Theory/Model/Rule.hs), so the `_restrict`
    // formulas' frees participate in the bound.
    let body_bound = avoid(ru).fresh_idents(0);
    let info_bound = info_frees(ru).iter().map(|v| v.idx + 1).max().unwrap_or(0);
    let seed = FastFreshState::seeded(body_bound.max(info_bound));
    let mut eqs: Vec<Equal<LNFact>> = Vec::new();
    go(maude, state_facts, ru, 0, seed, &mut eqs, out)
}

/// HS `interpretAbstractly` (AbstractInterpretation.hs) fused with
/// `partialEvaluation`'s `consumeEvaluation` (AbstractInterpretation.hs),
/// instantiated at their single upstream use (`S.Set LNFact` state,
/// `S.insert . absFact` add, `unifyLNFactEqs` unification).
///
/// HS produces a LAZY list of `(state, rules refined against that state)`
/// pairs which `consumeEvaluation` walks, tracing each adjacent pair and
/// keeping only the last.  Materialising that list would hold every
/// iteration's rule vector at once, so the per-step trace is built as the
/// loop runs — same values, same order, same bytes — and only the current
/// state plus the last iteration's rules are retained.
///
/// Returns `(fixpoint state, the rules refined against it, trace)`.  The
/// fixpoint iteration itself contributes no trace line: HS traces adjacent
/// pairs, and the final pair's state equals its predecessor's successor.
fn interpret_abstractly<I: EvaluationInfo>(
    maude: &MaudeHandle,
    style: EvaluationStyle,
    rules: &[Rule<I>],
) -> Result<(BTreeSet<LNFact>, Vec<Rule<I>>, String), MaudeError> {
    let mut st: BTreeSet<LNFact> = BTreeSet::new();
    st.insert(abs_fact(&fresh_fact(var_term(LVar::new(
        "z",
        LSort::Fresh,
        0,
    )))));
    st.insert(abs_fact(&in_fact(var_term(LVar::new("z", LSort::Msg, 0)))));

    let mut trace = String::new();
    let mut step = 0usize;
    loop {
        let mut refined: Vec<Rule<I>> = Vec::new();
        {
            let state_facts: Vec<&LNFact> = st.iter().collect();
            for ru in rules {
                refine_rule(maude, &state_facts, ru, &mut refined)?;
            }
        }
        // Only CONCLUSIONS feed the state (HS `get rConcs`).  `S.insert`
        // REPLACES an existing equal element, and `Eq`/`Ord LNFact` compare
        // tag + terms only (Theory/Model/Fact.hs) while `prettyLNFact`
        // still prints the annotations (Theory/Model/Fact.hs) — so the
        // LAST insertion
        // of a tag/terms-equal fact decides which annotations the report
        // shows.  `BTreeSet::replace` is that semantics; `insert` would keep
        // the first.
        let mut st_next = st.clone();
        for r in &refined {
            for c in &r.conclusions {
                st_next.replace(abs_fact(c));
            }
        }
        if st_next == st {
            return Ok((st, refined, trace));
        }
        // HS `withTrace` over the step from `st` to `st_next`
        // (AbstractInterpretation.hs).
        let added = st_next.len() - st.len();
        match style {
            EvaluationStyle::Silent => {}
            EvaluationStyle::Summary => {
                trace.push_str(&format!(
                    " partial evaluation: step {} added {} facts\n",
                    step, added
                ));
            }
            EvaluationStyle::Tracing => {
                let diff: Vec<Doc> = st_next.difference(&st).map(pretty_lnfact).collect();
                let body = render_default_style(hpj::numbered_prime(diff).nest(2));
                trace.push_str(&format!(
                    " partial evaluation: step {} added {} facts\n\n{}\n\n",
                    step, added, body
                ));
            }
        }
        step += 1;
        st = st_next;
    }
}

// =============================================================================
// eqModuloFreshnessNoAC for rules (Term/LTerm.hs)
// =============================================================================

/// The rule's `_restrict`-formula frees: HS `foldFrees f rstr`
/// (Theory/Model/Rule.hs) over `preRestriction`, in `freesList`
/// order — first occurrence first, duplicates kept, since the caller
/// numbers them by first occurrence.
fn info_frees<I: EvaluationInfo>(r: &Rule<I>) -> Vec<LVar> {
    r.info
        .proto_info()
        .restrictions
        .iter()
        .flat_map(crate::formula::formula_frees_list)
        .collect()
}

/// Canonicalise every free variable of `r` to `LVar "" <sort> <seq-idx>`
/// in `mapFrees` traversal order.  HS traverses the rule INFO first
/// (Theory/Model/Rule.hs), binding the unsubstituted
/// `_restrict`-formula frees
/// before the body (premises, conclusions, actions, new_vars) — so a body
/// variable identical to a restriction free reuses its canon slot, and
/// body-only variables start numbering after them.  `info_vars` carries those
/// info frees as [`rename_rule_from_zero`] shifted them.  Mirrors HS
/// `eqModuloFreshnessNoAC`'s `normIndices`.
fn canon_rule_frees<I: EvaluationInfo>(r: &Rule<I>, info_vars: &[LVar]) -> Rule<I> {
    let mut map: tamarin_utils::FastMap<LVar, LVar> = Default::default();
    let mut ctr: u64 = 0;
    for v in info_vars {
        if !map.contains_key(v) {
            let nv = LVar::new("", v.sort, ctr);
            ctr += 1;
            map.insert(*v, nv);
        }
    }
    r.clone().map_free_with(
        &mut |v| {
            if let Some(nv) = map.get(&v) {
                *nv
            } else {
                let nv = LVar::new("", v.sort, ctr);
                ctr += 1;
                map.insert(v, nv);
                nv
            }
        },
        false,
    )
}

/// HS `nubBy eqModuloFreshnessNoAC` over rules: first occurrence wins;
/// two rules are equal iff their free-canonicalised forms are structurally
/// equal (including `info` — the rule NAME is part of it, so dedup can
/// only merge refinements of the same original rule, which also carry the
/// same unsubstituted `_restrict` formulas).
fn nub_modulo_freshness<I: EvaluationInfo>(rules: Vec<(Rule<I>, Vec<LVar>)>) -> Vec<Rule<I>> {
    let mut kept: Vec<Rule<I>> = Vec::new();
    let mut kept_canon: Vec<Rule<I>> = Vec::new();
    for (r, info_vars) in rules {
        let c = canon_rule_frees(&r, &info_vars);
        if !kept_canon.contains(&c) {
            kept.push(r);
            kept_canon.push(c);
        }
    }
    kept
}

// =============================================================================
// partialEvaluation (AbstractInterpretation.hs)
// =============================================================================

/// HS renders the trace/report docs with the plain `render`
/// (Text/PrettyPrint/Class.hs)
/// = HughesPJ's DEFAULT style: lineLength 100, ribbon `round(100/1.5)` = 67
/// — NOT the console width the theory body uses.
fn render_default_style(d: Doc) -> String {
    d.render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON)
}

/// HS `partialEvaluation` (AbstractInterpretation.hs).  Returns
/// `(abstract state, refined rules, trace)`:
/// * the fixpoint abstract state;
/// * the last iteration's rules, each `rename`d from `nothingUsed` (min
///   var index becomes 0) then deduplicated modulo freshness;
/// * the EXACT stderr trace bytes HS's `Debug.Trace` would produce — one
///   ` partial evaluation: step <i> added <d> facts\n` line per iteration
///   except the last (`Summary`), with the newly-added facts as a
///   `nest 2 (numbered' …)` block appended under `Tracing`; empty for
///   `Silent`.  NOT printed here: HS's trace thunks fire during rendering,
///   after the `[Theory X] Theory closed` marker, so the caller must
///   `eprint!` the returned string at that point.
fn partial_evaluation<I: EvaluationInfo>(
    maude: &MaudeHandle,
    style: EvaluationStyle,
    ru_es: &[Rule<I>],
) -> Result<(BTreeSet<LNFact>, Vec<Rule<I>>, String), MaudeError> {
    let (final_st, final_rules, trace) = interpret_abstractly(maude, style, ru_es)?;
    // `map ((`evalFresh` nothingUsed) . rename)`: per rule, a uniform
    // index shift making the minimum free var index 0.  The minimum is
    // taken over the body frees AND the rule's unsubstituted
    // `_restrict`-formula frees (HS `boundsVarIdx` folds the rule info,
    // Theory/Model/Rule.hs), which HS's `mapFrees` shifts along with
    // the body —
    // the shifted info frees then seed the dedup's canonicalisation.
    let renamed: Vec<(Rule<I>, Vec<LVar>)> =
        final_rules.into_iter().map(rename_rule_from_zero).collect();
    Ok((final_st, nub_modulo_freshness(renamed), trace))
}

/// HS `(`evalFresh` nothingUsed) . rename` over a refined rule
/// (LTerm.hs): compute `boundsVarIdx` over the body frees ∪ the
/// rule's `_restrict`-formula frees, then shift every index uniformly so the
/// minimum becomes 0.  The info frees are shifted too (HS's `mapFrees` maps
/// the info, Theory/Model/Rule.hs) and returned for the dedup's canon
/// pass.
fn rename_rule_from_zero<I: EvaluationInfo>(r: Rule<I>) -> (Rule<I>, Vec<LVar>) {
    let info_vars = info_frees(&r);
    let mut lo: Option<u64> = None;
    let mut see = |idx: u64| {
        lo = Some(lo.map_or(idx, |m: u64| m.min(idx)));
    };
    r.for_each_free(&mut |v| see(v.idx));
    for v in &info_vars {
        see(v.idx);
    }
    let Some(min) = lo else {
        return (r, info_vars);
    };
    // `freshIdents` on `nothingUsed` returns 0, so the shift is `-min`.
    let shifted = r.map_free_with(&mut |v| LVar::new(v.name, v.sort, v.idx - min), true);
    let info_vars = info_vars
        .into_iter()
        .map(|v| LVar::new(v.name, v.sort, v.idx - min))
        .collect();
    (shifted, info_vars)
}

// =============================================================================
// applyPartialEvaluation (Prover.hs)
// =============================================================================

/// The sort key of HS's derived-`Ord (Rule i)` order, minus the unreachable
/// attribute/restriction tiebreak (see the module doc): name, then premises,
/// conclusions, actions, new_vars.
fn proto_rule_key(r: &ProtoRuleE) -> impl Ord + '_ {
    (
        &r.info.name,
        &r.premises,
        &r.conclusions,
        &r.actions,
        &r.new_vars,
    )
}

/// The `text{* … *}` report body (HS `ppAbsState`, Prover.hs),
/// byte-exact: leading space, `$--$`-joined header / `numbered'` fact list
/// / footer, trailing `".\n\n"` from the footer's literal newlines.
#[cfg(test)]
fn abs_state_report(st: &BTreeSet<LNFact>, n_refined: usize, n_orig: usize) -> String {
    abs_state_report_with_retained(st, n_refined, n_orig, 0)
}

fn abs_state_report_with_retained(
    st: &BTreeSet<LNFact>,
    n_refined: usize,
    n_orig: usize,
    retained: usize,
) -> String {
    let header = Doc::text(format!(
        " the abstract state after partial evaluation contains {} facts:",
        st.len()
    ));
    let facts: Vec<Doc> = st.iter().map(pretty_lnfact).collect();
    let kept = if retained == 0 {
        String::new()
    } else {
        format!("Kept {retained} original rule families to preserve their variants on export.\n")
    };
    let footer = Doc::text(format!(
        "This abstract state results in {} refined multiset rewriting rules.\n\
         {}\
         Note that the original number of multiset rewriting rules was {}.\n\n",
        n_refined, kept, n_orig
    ));
    render_default_style(hpj::above_blank(
        hpj::above_blank(header, hpj::numbered_prime(facts)),
        footer,
    ))
}

/// Refine compiled AC members, preserving family ownership independently of
/// names. Keep any family whose refinements are not safe to reopen as E rules.
/// The caller re-closes the resulting theory before proof search.
pub fn apply_partial_evaluation(
    elaborated: &mut Theory,
    maude: &MaudeHandle,
    style: EvaluationStyle,
) -> Result<String, crate::tools::rule_variants::VariantsError> {
    use crate::auto_sources::{closed_rule_as_open, unfold_one_rule_variants};
    use crate::rule::{
        is_trivial_proto_variant_ac, rule_products_outside_exponents, ProtoRuleName,
    };
    use crate::theory::{closed_rules_ac, merge_open_proto_rules};
    use crate::tools::rule_variants::prepare_open_rule_variant;

    let mut originals: Vec<_> = elaborated.rules().map(|r| r.rule_e().clone()).collect();
    if originals.is_empty() {
        return Ok(String::new());
    }
    originals.sort_by(|a, b| proto_rule_key(a).cmp(&proto_rule_key(b)));
    originals.dedup();
    let owner = |rule: &ProtoRuleE| {
        originals
            .iter()
            .position(|r| r == rule)
            .expect("each compiled rule has an original family")
    };
    let mut compiled = Vec::new();
    for parent in elaborated.rules() {
        let mut parent = parent.clone();
        prepare_open_rule_variant(&mut parent, maude)?;
        let family = owner(parent.rule_e());
        for ac in closed_rules_ac(&parent) {
            let open = closed_rule_as_open(&parent, &ac);
            let members = if is_trivial_proto_variant_ac(&ac, parent.rule_e()) {
                vec![open]
            } else {
                unfold_one_rule_variants(&open)
            };
            for member in members {
                let mut rule = member.rule;
                // Embedded restrictions already live as theory items. Their
                // pre-variant variables must not influence refinement.
                rule.info.restrictions.clear();
                compiled.push(Rule {
                    info: (family, rule.info),
                    premises: rule.premises,
                    conclusions: rule.conclusions,
                    actions: rule.actions,
                    new_vars: rule.new_vars,
                });
            }
        }
    }
    let name_string = |name| match name {
        ProtoRuleName::Fresh => "Fresh".to_string(),
        ProtoRuleName::Stand(name) => name.to_string(),
    };
    let reserved: BTreeSet<_> = originals
        .iter()
        .map(|r| name_string(r.info.name))
        .chain(compiled.iter().map(|r| name_string(r.info.1.name)))
        .collect();
    let (state, refined, trace) = partial_evaluation(maude, style, &compiled)?;
    let mut families: Vec<Vec<ProtoRuleE>> = vec![Vec::new(); originals.len()];
    for rule in refined {
        families[rule.info.0].push(Rule {
            info: rule.info.1,
            premises: rule.premises,
            conclusions: rule.conclusions,
            actions: rule.actions,
            new_vars: rule.new_vars,
        });
    }

    // None is KeepOriginal; Some([]) deliberately prunes an unreachable family.
    let mut plans: Vec<Option<Vec<ProtoRuleE>>> = Vec::new();
    for family in families {
        let mut exportable = true;
        for rule in &family {
            if !rule_products_outside_exponents(rule).is_empty() {
                exportable = false;
                break;
            }
            let mut recomputed = OpenProtoRule::new(rule.clone());
            prepare_open_rule_variant(&mut recomputed, maude)?;
            let computed = recomputed
                .abstracted_rule
                .as_ref()
                .unwrap_or(&recomputed.rule);
            let variants = &recomputed.variant_substs;
            if variants.len() != 1
                || !variants[0].is_empty()
                || canon_rule_frees(rule, &[]) != canon_rule_frees(computed, &[])
            {
                exportable = false;
                break;
            }
        }
        plans.push(exportable.then_some(family));
    }
    let retained = plans.iter().filter(|p| p.is_none()).count();
    let mut used: BTreeSet<_> = originals
        .iter()
        .zip(&plans)
        .filter(|(_, p)| p.is_none())
        .map(|(r, _)| name_string(r.info.name))
        .collect();
    let mut reserved = reserved;
    for family in plans.iter_mut().flatten() {
        for rule in family {
            let original = name_string(rule.info.name);
            let name = if used.contains(&original) {
                (1usize..)
                    .map(|n| format!("{original}_PE_{n}"))
                    .find(|name| !reserved.contains(name))
                    .unwrap()
            } else {
                original.clone()
            };
            if name != original {
                rule.info.name = ProtoRuleName::Stand(tamarin_term::intern::intern_str(&name));
            }
            used.insert(name.clone());
            reserved.insert(name);
        }
    }
    let count: usize = plans.iter().flatten().map(Vec::len).sum();
    let body = abs_state_report_with_retained(&state, count, originals.len(), retained);
    let macros: Vec<_> = elaborated.macros().cloned().collect();
    let mut items = Vec::new();
    let mut inserted_report = false;
    // Opening merges adjacent imported members of one original family first.
    for item in merge_open_proto_rules(&elaborated.items) {
        let rule = match item.split_rule() {
            Ok(other) => {
                items.push(other);
                continue;
            }
            Err(rule) => rule,
        };
        if !inserted_report {
            items.push(TheoryItem::Text(("text".into(), body.clone())));
            inserted_report = true;
        }
        match &plans[owner(&rule.rule_e)] {
            None => {
                let expanded = crate::rule::apply_macro_in_rule(&macros, rule.rule_e.clone());
                let mut kept = OpenProtoRule::new(expanded);
                kept.rule_e = Some(Box::new(rule.rule_e.clone()));
                kept.rule_ac = rule
                    .rule_ac
                    .iter()
                    .map(|ac| {
                        let mut member = closed_rule_as_open(&kept, ac).rule;
                        member.info.restrictions.clear();
                        member
                    })
                    .collect();
                items.push(TheoryItem::Rule(kept));
            }
            Some(refinements) => {
                for refinement in refinements {
                    let mut open = OpenProtoRule::new(refinement.clone());
                    open.rule_ac = vec![refinement.clone()];
                    items.push(TheoryItem::Rule(open));
                }
            }
        }
    }
    elaborated.items = items;
    Ok(trace)
}

#[cfg(test)]
#[path = "abstract_interpretation_tests.rs"]
mod tests;
