// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Tools.AbstractInterpretation` — abstract interpretation
//! for partial evaluation of multiset rewriting systems — plus the theory
//! rewrite HS performs in `applyPartialEvaluation` (Prover.hs:237-264).
//!
//! Algorithm (HS `interpretAbstractly`, AbstractInterpretation.hs:44-83):
//! starting from the abstract state `{ Fr(~z), In(z) }`, repeatedly refine
//! every rule against the state (each premise E-unified — via Maude —
//! against every state fact with the same tag) and add the refined rules'
//! abstracted conclusions to the state, until the state stabilises.  The
//! final rule list is each refined rule `rename`d so its minimum variable
//! index is 0, deduplicated modulo variable freshness
//! (`eqModuloFreshnessNoAC`, first occurrence wins).
//!
//! A structural subtlety this module must reproduce: a rule carries its
//! `_restrict` formulas in `ProtoRuleEInfo::restrictions` (HS
//! `preRestriction`), `HasFrees (Rule i)` folds over them before the body
//! (Theory/Model/Rule.hs:291-298, Theory/Model/Rule.hs:491-498) and `Apply
//! ProtoRuleEInfo` is the identity (Theory/Model/Rule.hs:500-501).  So a
//! refined rule keeps its ORIGINAL restriction frees unsubstituted, and they
//! floor the final `rename`'s index shift (a fully-substituted body keeps its
//! refined indices — the oracle renders `In( x.2 )` for
//! features/predicates/minimal.spthy) and are bound first by
//! `eqModuloFreshnessNoAC`'s canonicalisation.  [`info_frees`] reads them off
//! the rule.  `HasFrees for Rule<I>` (rule.rs) skips `info`, so the shift and
//! the canonicalisation pass the frees as a separate list and leave the
//! formulas alone: every refinement of one rule carries the same formulas, so
//! they cannot tell two refinements apart.
//!
//! Divergences from HS, all deliberate:
//! * **Trace emission**: HS traces via `Debug.Trace` thunks that fire when
//!   the closed theory is rendered — AFTER the `[Theory X] Theory closed`
//!   stderr marker.  [`partial_evaluation`]/[`apply_partial_evaluation`]
//!   therefore RETURN the exact trace bytes instead of `eprint!`ing them;
//!   the caller must emit them right after its "Theory closed" marker to
//!   match HS stderr ordering.
//! * **Rule ordering comparator**: HS sorts `getProtoRuleEs` under the
//!   derived `Ord (Rule i)` = (info, prems, concs, acts, newVars) with
//!   `Ord ProtoRuleEInfo` = (name, attributes, restrictions).  RS
//!   `RuleAttributes`/`SyntacticLNFormula` have no `Ord`; the comparator
//!   here uses (name, prems, concs, acts, new_vars).  The attribute/
//!   restriction tiebreak is unreachable: duplicate rule names are rejected
//!   at parse time, so the name alone already discriminates the input.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
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
use crate::rule::{unify_ln_fact_eqs, ProtoRuleE};
use crate::theory::{OpenProtoRule, Theory, TheoryItem};

/// How to report on performing a partial evaluation.  HS
/// `EvaluationStyle` (AbstractInterpretation.hs:86); the CLI maps
/// `SUMMARY` → `Summary` and `VERBOSE` → `Tracing`
/// (TheoryLoader.hs:354-358); `Silent` is unreachable from the CLI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvaluationStyle {
    Silent,
    Summary,
    Tracing,
}

// =============================================================================
// absFact / absTerm (AbstractInterpretation.hs:122-139)
// =============================================================================

/// Per-fact abstraction state: HS's `evalBind noBindings` +
/// `evalFreshT nothingUsed` pair — a binding map keyed by the WHOLE
/// sub-term and a single fresh counter, both reset for every fact.
struct AbsState {
    counter: u64,
    bindings: Vec<(LNTerm, LNTerm)>,
}

/// HS `absTerm` (AbstractInterpretation.hs:131-139): constants survive,
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

/// HS `absFact` (AbstractInterpretation.hs:124-129): every `Out` fact
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
// interpretAbstractly (AbstractInterpretation.hs:44-83)
// =============================================================================

/// HS `refineRule` (AbstractInterpretation.hs:76-83), the `FreshT []`
/// nondeterminism made explicit as a DFS: for each premise (in order),
/// choose a state fact with the same tag (state facts visited in sorted
/// `S.toList` order — premise 1 varies SLOWEST) and `rename` it above the
/// branch's fresh counter; at the leaf, E-unify the whole equation list
/// once, and for each unifier `freshToFree` it from the branch counter and
/// apply it to the rule.  Branch alternatives never share a counter — each
/// starts from the incoming value (HS `mplus` on `StateT Integer []` runs
/// both alternatives from the same state).
fn refine_rule(
    maude: &MaudeHandle,
    state_facts: &[&LNFact],
    ru: &ProtoRuleE,
    out: &mut Vec<ProtoRuleE>,
) -> Result<(), MaudeError> {
    fn go(
        maude: &MaudeHandle,
        state_facts: &[&LNFact],
        ru: &ProtoRuleE,
        prem_idx: usize,
        counter: FastFreshState,
        eqs: &mut Vec<Equal<LNFact>>,
        out: &mut Vec<ProtoRuleE>,
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
    // (`HasFrees (Rule i)`, Theory/Model/Rule.hs:291-298), so the `_restrict`
    // formulas' frees participate in the bound.
    let body_bound = avoid(ru).fresh_idents(0);
    let info_bound = info_frees(ru).iter().map(|v| v.idx + 1).max().unwrap_or(0);
    let seed = FastFreshState::seeded(body_bound.max(info_bound));
    let mut eqs: Vec<Equal<LNFact>> = Vec::new();
    go(maude, state_facts, ru, 0, seed, &mut eqs, out)
}

/// HS `interpretAbstractly` (AbstractInterpretation.hs:44-83) fused with
/// `partialEvaluation`'s `consumeEvaluation` (AbstractInterpretation.hs:100-119),
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
fn interpret_abstractly(
    maude: &MaudeHandle,
    style: EvaluationStyle,
    rules: &[ProtoRuleE],
) -> Result<(BTreeSet<LNFact>, Vec<ProtoRuleE>, String), MaudeError> {
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
        let mut refined: Vec<ProtoRuleE> = Vec::new();
        {
            let state_facts: Vec<&LNFact> = st.iter().collect();
            for ru in rules {
                refine_rule(maude, &state_facts, ru, &mut refined)?;
            }
        }
        // Only CONCLUSIONS feed the state (HS `get rConcs`).  `S.insert`
        // REPLACES an existing equal element, and `Eq`/`Ord LNFact` compare
        // tag + terms only (Theory/Model/Fact.hs:170-174) while `prettyLNFact`
        // still prints the annotations (Theory/Model/Fact.hs:567-574) — so the
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
        // (AbstractInterpretation.hs:109-119).
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
// eqModuloFreshnessNoAC for rules (Term/LTerm.hs:663-670)
// =============================================================================

/// The rule's `_restrict`-formula frees: HS `foldFrees f rstr`
/// (Theory/Model/Rule.hs:491-498) over `preRestriction`, in `freesList`
/// order — first occurrence first, duplicates kept, since the caller
/// numbers them by first occurrence.
fn info_frees(r: &ProtoRuleE) -> Vec<LVar> {
    r.info
        .restrictions
        .iter()
        .flat_map(crate::formula::formula_frees_list)
        .collect()
}

/// Canonicalise every free variable of `r` to `LVar "" <sort> <seq-idx>`
/// in `mapFrees` traversal order.  HS traverses the rule INFO first
/// (Theory/Model/Rule.hs:291-298), binding the unsubstituted
/// `_restrict`-formula frees
/// before the body (premises, conclusions, actions, new_vars) — so a body
/// variable identical to a restriction free reuses its canon slot, and
/// body-only variables start numbering after them.  `info_vars` carries those
/// info frees as [`rename_rule_from_zero`] shifted them.  Mirrors HS
/// `eqModuloFreshnessNoAC`'s `normIndices`.
fn canon_rule_frees(r: &ProtoRuleE, info_vars: &[LVar]) -> ProtoRuleE {
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
fn nub_modulo_freshness(rules: Vec<(ProtoRuleE, Vec<LVar>)>) -> Vec<ProtoRuleE> {
    let mut kept: Vec<ProtoRuleE> = Vec::new();
    let mut kept_canon: Vec<ProtoRuleE> = Vec::new();
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
// partialEvaluation (AbstractInterpretation.hs:86-119)
// =============================================================================

/// HS renders the trace/report docs with the plain `render`
/// (Text/PrettyPrint/Class.hs:77-78)
/// = HughesPJ's DEFAULT style: lineLength 100, ribbon `round(100/1.5)` = 67
/// — NOT the console width the theory body uses.
fn render_default_style(d: Doc) -> String {
    d.render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON)
}

/// HS `partialEvaluation` (AbstractInterpretation.hs:90-119).  Returns
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
fn partial_evaluation(
    maude: &MaudeHandle,
    style: EvaluationStyle,
    ru_es: &[ProtoRuleE],
) -> Result<(BTreeSet<LNFact>, Vec<ProtoRuleE>, String), MaudeError> {
    let (final_st, final_rules, trace) = interpret_abstractly(maude, style, ru_es)?;
    // `map ((`evalFresh` nothingUsed) . rename)`: per rule, a uniform
    // index shift making the minimum free var index 0.  The minimum is
    // taken over the body frees AND the rule's unsubstituted
    // `_restrict`-formula frees (HS `boundsVarIdx` folds the rule info,
    // Theory/Model/Rule.hs:291-298), which HS's `mapFrees` shifts along with
    // the body —
    // the shifted info frees then seed the dedup's canonicalisation.
    let renamed: Vec<(ProtoRuleE, Vec<LVar>)> =
        final_rules.into_iter().map(rename_rule_from_zero).collect();
    Ok((final_st, nub_modulo_freshness(renamed), trace))
}

/// HS `(`evalFresh` nothingUsed) . rename` over a refined rule
/// (LTerm.hs:638-645): compute `boundsVarIdx` over the body frees ∪ the
/// rule's `_restrict`-formula frees, then shift every index uniformly so the
/// minimum becomes 0.  The info frees are shifted too (HS's `mapFrees` maps
/// the info, Theory/Model/Rule.hs:302-306) and returned for the dedup's canon
/// pass.
fn rename_rule_from_zero(r: ProtoRuleE) -> (ProtoRuleE, Vec<LVar>) {
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
// applyPartialEvaluation (Prover.hs:237-264)
// =============================================================================

/// HS derived-`Ord (Rule i)` order, minus the unreachable attribute/
/// restriction tiebreak (see the module doc): name, then premises,
/// conclusions, actions, new_vars.
fn proto_rule_cmp(a: &ProtoRuleE, b: &ProtoRuleE) -> std::cmp::Ordering {
    a.info
        .name
        .cmp(&b.info.name)
        .then_with(|| a.premises.cmp(&b.premises))
        .then_with(|| a.conclusions.cmp(&b.conclusions))
        .then_with(|| a.actions.cmp(&b.actions))
        .then_with(|| a.new_vars.cmp(&b.new_vars))
}

/// The `text{* … *}` report body (HS `ppAbsState`, Prover.hs:257-264),
/// byte-exact: leading space, `$--$`-joined header / `numbered'` fact list
/// / footer, trailing `".\n\n"` from the footer's literal newlines.
fn abs_state_report(st: &BTreeSet<LNFact>, n_refined: usize, n_orig: usize) -> String {
    let header = Doc::text(format!(
        " the abstract state after partial evaluation contains {} facts:",
        st.len()
    ));
    let facts: Vec<Doc> = st.iter().map(pretty_lnfact).collect();
    let footer = Doc::text(format!(
        "This abstract state results in {} refined multiset rewriting rules.\n\
         Note that the original number of multiset rewriting rules was {}.\n\n",
        n_refined, n_orig
    ));
    render_default_style(hpj::above_blank(
        hpj::above_blank(header, hpj::numbered_prime(facts)),
        footer,
    ))
}

/// HS `applyPartialEvaluation` (Prover.hs:237-264), operating on RS's
/// parallel parsed/elaborated theories:
///
/// 1. `ru_es` = the elaborated rules' `ProtoRuleE`s through a Set
///    round-trip (`getProtoRuleEs`, ClosedTheory.hs:87-89) — this is what
///    re-orders the rules ALPHABETICALLY by name.
/// 2. Run [`partial_evaluation`].
/// 3. Splice both item lists: items before the first rule item stay put;
///    at that position insert the `text{*…*}` report item followed by ALL
///    refined rules; every other rule item is removed; later non-rule
///    items follow in order (HS `replaceProtoRules`).  On the parsed side
///    the anchor is the first rule item PRESENT in the elaborated theory —
///    parsed leftovers of rules dropped by the no-variant check
///    (run.rs) have no elaborated counterpart and so render as nothing;
///    HS's closed item list has no such entry, so they cannot anchor the
///    splice either.
/// 4. A theory whose closed form has no rule item gets no report block and
///    is left untouched (HS `replaceProtoRules [] = []`).
///
/// The refined elaborated rules are fresh `OpenProtoRule`s (no variants,
/// no loop breakers): the caller must re-run `populate_rule_variants` and
/// `annotate_loop_breakers` on the rewritten theory — HS's second
/// `closeTheoryWithMaude`.  The parsed and elaborated refined rule items
/// are inserted 1:1 in the same order, which is what keeps the two item
/// streams aligned by `(name, occurrence-ordinal)` once partial evaluation
/// makes rule names non-unique.
///
/// Returns the stderr trace bytes to emit after the "Theory closed"
/// marker (see [`partial_evaluation`]).
pub fn apply_partial_evaluation(
    parsed: &mut p::Theory,
    elaborated: &mut Theory,
    maude: &MaudeHandle,
    style: EvaluationStyle,
) -> Result<String, MaudeError> {
    // HS `getProtoRuleEs` (ClosedTheory.hs:87-89) extracts `cprRuleE` — the
    // E-half that keeps the macro calls as the source writes them
    // (`closeProtoRule`, lib/theory/src/Rule.hs:82-86), that
    // `addActionClosedProtoRule` never annotates
    // (lib/theory/src/Rule.hs:95-99) and that `unfoldRuleVariants` duplicates
    // verbatim across variants (lib/theory/src/Rule.hs:63-79, see line 76) —
    // so when the `--auto-sources` close preceded this call the refinement
    // input carries NO AUTO_* actions, and the Set round-trip below
    // collapses the per-variant duplicates ("we remove duplicates if they
    // exist due to variant unfolding", ClosedTheory.hs:87-89, see line 89).
    // Feeding the annotated `rule` half instead lets the baked AUTO actions
    // reach the second close, whose refined-source trigger they then
    // wrongly satisfy.
    let mut ru_es: Vec<ProtoRuleE> = elaborated.rules().map(|o| o.rule_e().clone()).collect();
    if ru_es.is_empty() {
        // No closed rule item: HS's `replaceProtoRules` never fires and
        // the trivial evaluation produces no trace.
        return Ok(String::new());
    }
    let elab_names: BTreeSet<String> = elaborated.rules().map(|o| o.name().to_string()).collect();
    let Some(p_anchor) = parsed
        .items
        .iter()
        .position(|it| matches!(it, p::TheoryItem::Rule(r) if elab_names.contains(&r.name)))
    else {
        return Ok(String::new());
    };
    let e_anchor = elaborated
        .items
        .iter()
        .position(|it| matches!(it, TheoryItem::Rule(_)))
        .expect("elaborated.rules() non-empty implies a rule item");

    // `getProtoRuleEs`' Set round-trip: sort under the derived rule order,
    // drop exact duplicates.
    ru_es.sort_by(proto_rule_cmp);
    ru_es.dedup_by(|a, b| a == b);

    let (st, refined, trace) = partial_evaluation(maude, style, &ru_es)?;
    let body = abs_state_report(&st, refined.len(), ru_es.len());

    // Parsed-side splice: the report block, then one rule item per refined
    // rule.  Borrows `refined` so the elaborated side can consume it.
    let mut inserted: Vec<p::TheoryItem> = Vec::with_capacity(refined.len() + 1);
    inserted.push(p::TheoryItem::FormalComment {
        header: "text".to_string(),
        body: body.clone(),
    });
    inserted.extend(
        refined
            .iter()
            .map(|r| p::TheoryItem::Rule(crate::elaborate::proto_rule_to_parsed(r))),
    );
    parsed.items = splice_refined(
        std::mem::take(&mut parsed.items),
        p_anchor,
        |it| matches!(it, p::TheoryItem::Rule(_)),
        inserted,
    );

    // Elaborated-side splice (same shape; the refined rules carry empty
    // variant/loop-breaker fields for the caller's re-close).  That re-close
    // is HS's second `closeTheoryWithMaude` (Prover.hs:238-241), which reaches
    // `closeProtoRule` and narrows `applyMacroInRule macros ruE` while keeping
    // the refined rule itself as `cprRuleE` (lib/theory/src/Rule.hs:82-86).
    let macros: Vec<crate::theory::LNMacro> = elaborated.macros().cloned().collect();
    let mut inserted: Vec<TheoryItem> = Vec::with_capacity(refined.len() + 1);
    inserted.push(TheoryItem::Text(("text".to_string(), body)));
    inserted.extend(refined.into_iter().map(|r| {
        let expanded = crate::rule::apply_macro_in_rule(&macros, r.clone());
        let mut opr = OpenProtoRule::new(expanded);
        if opr.rule != r {
            opr.rule_e = Some(Box::new(r));
        }
        TheoryItem::Rule(opr)
    }));
    elaborated.items = splice_refined(
        std::mem::take(&mut elaborated.items),
        e_anchor,
        |it| matches!(it, TheoryItem::Rule(_)),
        inserted,
    );

    Ok(trace)
}

/// HS `replaceProtoRules` as one list rewrite, shared by the parsed and
/// elaborated item lists: keep everything before `anchor` verbatim, put
/// `inserted` (the report block followed by the refined rules) in the
/// anchor's place, then keep the later NON-rule items in order.  `anchor`
/// itself is a rule item, so the `is_rule` filter over the tail drops it
/// along with every later rule item.
fn splice_refined<T>(
    items: Vec<T>,
    anchor: usize,
    is_rule: impl Fn(&T) -> bool,
    inserted: Vec<T>,
) -> Vec<T> {
    let mut out = items;
    let tail = out.split_off(anchor);
    out.reserve(inserted.len() + tail.len());
    out.extend(inserted);
    out.extend(tail.into_iter().filter(|it| !is_rule(it)));
    out
}

#[cfg(test)]
#[path = "abstract_interpretation_tests.rs"]
mod tests;
