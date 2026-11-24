// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.RuleVariants`: the AC variants of protocol rules.
//!
//! [`variants_proto_rule`] is `variantsProtoRule`: abstract the reducible
//! subterms, ask Maude for the variants of the abstracted terms, compose and
//! normalise them, then `simpDisjunction` the result.

use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle, MaudePool};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;

use crate::fact::Fact;
use crate::rule::{ProtoRuleAC, ProtoRuleE};
use crate::theory::{OpenProtoRule, RuleVariants, Theory, TheoryItem};

type LNSubst = Subst<Name, LVar>;

/// HS `unfoldRuleVariants` (Rule.hs) on one closed rule: one rule
/// `<name>___VARIANT_<i>` per variant substitution, each applied after
/// `freshToFreeAvoiding` against the AC rule; an empty disjunction unfolds to
/// no rule.
pub(crate) fn unfold_closed_rule(parent: &OpenProtoRule, ac: &ProtoRuleAC) -> Vec<OpenProtoRule> {
    let o = closed_rule_as_open(parent, ac);
    if crate::rule::is_trivial_proto_variant_ac(ac, parent.rule_e()) {
        return vec![o];
    }
    let ac = &o.rule;
    let substs = o.variant_substs();
    if substs == [LNSubstVFresh::empty()] && ac.info.name != o.rule_e().info.name {
        return vec![o];
    }
    // `freshToFreeAvoiding subst ruAC` allocates above `avoid ruAC`; HS's
    // `HasFrees (Rule ProtoRuleACInfo)` folds the rule INFO first, whose
    // variant-disjunction DOMAIN keys are frees (keys-only,
    // Theory/Model/Rule.hs; SubstVFresh.hs), so
    // they participate in the bound alongside the body.
    let seed = tamarin_term::lterm::avoid(&(substs.to_vec(), ac.clone()));
    substs
        .iter()
        .enumerate()
        .map(|(i, s)| {
            // Each subst gets its own `evalFreshAvoiding` scope (HS maps
            // `freshToFreeAvoiding` per subst against the same `ruAC`).
            let mut fresh = seed.clone();
            let sigma = s.fresh_to_free_avoiding(|n| fresh.fresh_idents(n));
            let mut ru = tamarin_term::apply::Apply::apply(ac.clone(), &sigma);
            // `rName i` (lib/theory/src/Rule.hs): FreshRule keeps its
            // name; StandRule gains the 1-based `___VARIANT_<i>` suffix.
            ru.info.name = crate::rule::rule_variant_name(ru.info.name, i + 1);
            OpenProtoRule {
                variants: RuleVariants::Closed {
                    body: ru.clone(),
                    variants: vec![LNSubstVFresh::empty()],
                },
                rule: ru,
                loop_breakers: o.loop_breakers.clone(),
                // `toClosedProtoRule` keeps the ORIGINAL rule as every
                // variant's `cprRuleE` (lib/theory/src/Rule.hs) — the
                // half `getProtoRuleEs` dedups back to one copy.
                rule_e: Some(Box::new(o.rule_e().clone())),
                // This open rule holds one executable member; its original
                // E rule is retained separately for family regrouping.
                rule_ac: Vec::new(),
            }
        })
        .collect()
}

/// Re-express one closed AC half as the split open representation consumed by
/// [`unfold_closed_rule`]. This also covers source-declared
/// `variants (modulo AC)` blocks, whose bodies do not live in the parent's
/// variants.
pub(crate) fn closed_rule_as_open(
    parent: &OpenProtoRule,
    ac: &crate::rule::ProtoRuleAC,
) -> OpenProtoRule {
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
        variants: RuleVariants::Closed {
            body: rule.clone(),
            variants: ac.info.variants.clone(),
        },
        rule,
        loop_breakers: ac.info.loop_breakers.clone(),
        rule_e: Some(Box::new(parent.rule_e().clone())),
        rule_ac: Vec::new(),
    }
}

#[derive(Debug, Clone)]
pub enum VariantsError {
    Maude(String),
    MissingMaudeForExplicitVariants,
    UnsupportedInput(crate::wellformedness::WfReport),
}

impl std::fmt::Display for VariantsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariantsError::Maude(s) => write!(f, "Maude error: {}", s),
            VariantsError::MissingMaudeForExplicitVariants => write!(
                f,
                "Maude is required to validate explicit rule variants; refusing to load an unchecked family."
            ),
            VariantsError::UnsupportedInput(report) => write!(
                f,
                "{}\nUnsupported rule semantics - aborting before proof search.",
                crate::pretty_theory::render_wf_error_report(report)
            ),
        }
    }
}
impl std::error::Error for VariantsError {}
impl From<crate::tools::equation_store::AddEqsError> for VariantsError {
    fn from(error: crate::tools::equation_store::AddEqsError) -> Self {
        let crate::tools::equation_store::AddEqsError::Maude(message) = error;
        Self::Maude(message)
    }
}

impl From<MaudeError> for VariantsError {
    fn from(e: MaudeError) -> Self {
        VariantsError::Maude(format!("{}", e))
    }
}

/// Compute the variants of every rule, as HS `closeTheoryWithMaude` does.
/// With a pool, rules are processed in parallel on pooled Maude processes;
/// the results are written back in source order either way.
pub fn populate_rule_variants(
    elaborated: &mut Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
) -> Result<(), VariantsError> {
    let outs: Result<Vec<Option<RuleVariants>>, VariantsError> = if let Some(pool) = pool {
        use rayon::prelude::*;
        elaborated
            .items
            .par_iter()
            .map(|item| -> Result<_, VariantsError> {
                let TheoryItem::Rule(opr) = item else {
                    return Ok(None);
                };
                // Per-task Maude from the pool: each rule's variant
                // computation runs on its own subprocess (no IPC mutex
                // contention).
                let pooled = pool.acquire();
                variants_proto_rule(&pooled, &opr.rule).map(Some)
            })
            .collect()
    } else {
        elaborated
            .items
            .iter()
            .map(|item| -> Result<_, VariantsError> {
                let TheoryItem::Rule(opr) = item else {
                    return Ok(None);
                };
                variants_proto_rule(maude, &opr.rule).map(Some)
            })
            .collect()
    };
    // Sequential writeback in source order.
    for (item, out) in elaborated.items.iter_mut().zip(outs?) {
        let TheoryItem::Rule(opr) = item else {
            continue;
        };
        if let Some(variants) = out {
            opr.variants = variants;
        }
    }
    Ok(())
}

/// HS `checkTranslatedTheory`'s rule half: compute variants and report
/// wellformedness on the open theory, and with `reject_unsupported` (close
/// mode) refuse a report carrying a fatal entry. The theory keeps every rule,
/// zero-variant ones included: HS runs the derivation checks and the
/// translate-mode echo on the open theory, and only `closeTheoryWithMaude`
/// ([`crate::closed_theory::close_prepared_theory`]) removes them.
pub fn prepare_theory_rules(
    theory: &mut Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
    reject_unsupported: bool,
) -> Result<crate::wellformedness::WfReport, VariantsError> {
    populate_rule_variants(theory, maude, pool)?;
    let report = crate::wellformedness::check_wellformedness(theory, Some(maude))?;
    let fatal = crate::wellformedness::variants::fatal_wf_errors(&report);
    if reject_unsupported && !fatal.is_empty() {
        return Err(VariantsError::UnsupportedInput(fatal));
    }
    Ok(report)
}

/// Re-close rules produced by partial evaluation. Unlike the initial close,
/// this phase has no additional wellformedness report, but filtering and loop
/// breaker annotation must retain the same ordering.
pub(crate) fn reprepare_theory_rules(
    theory: &mut Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
) -> Result<(), VariantsError> {
    populate_rule_variants(theory, maude, pool)?;
    finish_theory_rules(theory, maude)
}

/// `closeTheoryWithMaude`'s rule step on prepared rules: drop the
/// zero-variant rules, expand the explicit members' macros and annotate the
/// loop breakers.
pub(crate) fn finish_theory_rules(
    theory: &mut Theory,
    maude: &MaudeHandle,
) -> Result<(), VariantsError> {
    retain_rules_with_variants(theory, maude)?;
    let macros: Vec<_> = theory.macros().cloned().collect();
    for item in &mut theory.items {
        if let TheoryItem::Rule(rule) = item {
            rule.expand_variant_macros(&macros);
        }
    }
    crate::constraint::solver::context::annotate_theory_loop_breakers(theory, maude);
    Ok(())
}

/// Compute the variants of a rule that closing has not seen, for a
/// standalone solver context.
pub fn prepare_open_rule_variant(
    rule: &mut OpenProtoRule,
    maude: &MaudeHandle,
) -> Result<(), VariantsError> {
    if rule.variants == RuleVariants::Unprepared {
        rule.variants = variants_proto_rule(maude, &rule.rule)?;
    }
    Ok(())
}

/// HS `variantsProtoRule` (RuleVariants.hs): `NoVariants` for `Nothing`,
/// `Closed` for `Just ruAC`; never `Unprepared`.
pub fn variants_proto_rule(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<RuleVariants, VariantsError> {
    use tamarin_term::function_symbols::FunSym;
    let sig = maude.maude_sig();
    let reducible = |t: &LNTerm| t.any_fun_sym(|f| !sig.irreducible_fun_syms_fast.contains(f));
    let has_reducible = rule
        .premises
        .iter()
        .chain(&rule.actions)
        .chain(&rule.conclusions)
        .flat_map(|fact| fact.terms.iter())
        .chain(rule.new_vars.iter())
        .any(reducible);
    // Rust-only short cut: with nothing reducible, only variables are
    // abstracted, and Maude's only variant of them is the identity, which
    // composes to `{}`. Its `isFreshRedundant` check is syntactic, as
    // normalising irreducible terms removes no variable.
    if !has_reducible {
        if identity_is_fresh_redundant(rule) {
            return Ok(RuleVariants::NoVariants);
        }
        let (body, variants) =
            rename_precise_rule_with_variants(rule.clone(), vec![LNSubstVFresh::empty()]);
        return Ok(RuleVariants::Closed { body, variants });
    }
    let irreducible = sig.irreducible_fun_syms.clone();

    // Avoid clashes with the rule's existing free vars.  HS:
    // `convertRule \`evalFreshTAvoiding\` ru` — Fresh counter starts at
    // (max idx of rule's free vars) + 1.
    let rule_frees = tamarin_term::lterm::frees(rule);
    let avoid_max = rule_frees.iter().map(|v| v.idx).max().unwrap_or(0);
    // `convertRule` runs under `evalFreshTAvoiding ru` (RuleVariants.hs).
    // Share the Maude process while giving each rule its own counter, seeded
    // above all variables in that rule.
    let local_maude_owned = maude.with_fresh_counter_from(avoid_max);
    let maude: &MaudeHandle = &local_maude_owned;

    fn name_hint(t: &LNTerm) -> String {
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => v.name.to_string(),
            _ => "z".to_string(),
        }
    }

    // HS's `BindT` state, `M.Map LNTerm LVar`: one variable per distinct
    // term, and `M.toList` order is term order.
    let mut bindings: std::collections::BTreeMap<LNTerm, LVar> = std::collections::BTreeMap::new();

    // HS-faithful `abstrTerm` (RuleVariants.hs).
    fn abstr_term(
        t: &LNTerm,
        irreducible: &std::collections::BTreeSet<FunSym>,
        bindings: &mut std::collections::BTreeMap<LNTerm, LVar>,
        maude: &MaudeHandle,
    ) -> LNTerm {
        // Irreducible head: recurse into args.
        if let Term::App(f, args) = t
            && irreducible.contains(f)
        {
            return Term::App(
                *f,
                args.iter()
                    .map(|a| abstr_term(a, irreducible, bindings, maude))
                    .collect(),
            );
        }
        // Catch-all: import binding (handles leaf vars AND reducible-head
        // App).  HS: `abstrTerm t = do at <- varTerm <$> importBinding ...`.
        if let Some(v) = bindings.get(t) {
            return Term::Lit(tamarin_term::vterm::Lit::Var(*v));
        }
        let new_idx = maude.reserve_idxs(1);
        let v = LVar {
            name: tamarin_term::intern::intern_str(&name_hint(t)),
            // HS-faithful `abstrTerm` (RuleVariants.hs):
            // `importBinding (\`LVar\` sortOfLNTerm t) t (getHint t)`.
            // `sort_of_lnterm` (lterm.rs) IS HS `sortOfLNTerm`:
            // Con -> sort_of_name (Fresh/Pub/Node/Nat by tag), Var ->
            // v.sort, NatPlus/NatOne -> Nat, _ -> Msg.
            sort: tamarin_term::lterm::sort_of_lnterm(t),
            idx: new_idx,
        };
        bindings.insert(t.clone(), v);
        Term::Lit(tamarin_term::vterm::Lit::Var(v))
    }

    fn abstr_fact(
        f: &Fact<LNTerm>,
        irreducible: &std::collections::BTreeSet<FunSym>,
        bindings: &mut std::collections::BTreeMap<LNTerm, LVar>,
        maude: &MaudeHandle,
    ) -> Fact<LNTerm> {
        // Abstraction rewrite — frees change; recompute the bloom.
        let terms: Vec<LNTerm> = f
            .terms
            .iter()
            .map(|t| abstr_term(t, irreducible, bindings, maude))
            .collect();
        Fact::fresh_annotated(f.tag, f.annotations.clone(), terms)
    }

    // `variantsProtoRule` (RuleVariants.hs) imports all leaf variables before
    // abstracting compound terms. `frees` supplies them in sorted, deduplicated
    // LVar order (index, sort, name); that order determines fresh indices and
    // the subsequent ordering of variant substitutions.
    for v in rule_frees {
        let leaf_term: LNTerm = Term::Lit(tamarin_term::vterm::Lit::Var(v));
        // The result is discarded; the side effect on `bindings` is
        // what matters.
        let _ = abstr_term(&leaf_term, &irreducible, &mut bindings, maude);
    }

    let prems: Vec<Fact<LNTerm>> = rule
        .premises
        .iter()
        .map(|f| abstr_fact(f, &irreducible, &mut bindings, maude))
        .collect();
    let concs: Vec<Fact<LNTerm>> = rule
        .conclusions
        .iter()
        .map(|f| abstr_fact(f, &irreducible, &mut bindings, maude))
        .collect();
    let acts: Vec<Fact<LNTerm>> = rule
        .actions
        .iter()
        .map(|f| abstr_fact(f, &irreducible, &mut bindings, maude))
        .collect();
    let nvs: Vec<LNTerm> = rule
        .new_vars
        .iter()
        .map(|t| abstr_term(t, &irreducible, &mut bindings, maude))
        .collect();

    // Build the abstracted rule.
    let abstracted_rule =
        crate::rule::Rule::new(rule.info.clone(), prems, concs, acts).with_new_vars(nvs);

    // `eqsAbstr = map swap (M.toList bindings)`. The order of
    // `abstractedTerms`, the Maude query, is the original terms' `Ord`, which
    // the `BTreeMap` iteration gives; it decides the AC unifier enumeration.
    let abstraction_pairs: Vec<(LVar, LNTerm)> =
        bindings.iter().map(|(t, v)| (*v, t.clone())).collect();
    let abstraction_subst: LNSubst = Subst::from_list(abstraction_pairs);

    // `abstractedTerms = map snd eqsAbstr` — the ORIGINAL terms.
    let abstracted_terms: Vec<LNTerm> = bindings.keys().cloned().collect();
    let packed = Term::App(FunSym::List, abstracted_terms.into());
    let raw_substs = maude.variants(&packed)?;
    if raw_substs.is_empty() {
        return Ok(RuleVariants::NoVariants);
    }

    // Per variant: `restrictVFresh (frees abstrPsCsAs) $ removeRenamings $
    // normSubstVFresh' $ composeVFresh vsubst abstractionSubst`.
    let abstr_frees = tamarin_term::lterm::frees(&abstracted_rule);

    // `isFreshRedundant` (RuleVariants.hs), applied before composition:
    // drop a variant that puts a freshly introduced term inside a non-Fr
    // premise.
    let raw_substs: Vec<_> = {
        let freshly_introduced: Vec<LNTerm> = rule
            .premises
            .iter()
            .filter(|f| matches!(f.tag, crate::fact::FactTag::Fresh))
            .filter_map(|f| f.terms.first().cloned())
            .collect();
        let premise_terms_for_filter: Vec<LNTerm> = rule
            .premises
            .iter()
            .filter(|f| !matches!(f.tag, crate::fact::FactTag::Fresh))
            .flat_map(|f| f.terms.iter().cloned())
            .collect();
        if freshly_introduced.is_empty() || premise_terms_for_filter.is_empty() {
            raw_substs
        } else {
            // `freshToFreeAvoidingFast sFresh (frees premiseTerms)`: a local
            // supply, so the rule's counter does not advance.
            let filter_base = tamarin_term::lterm::avoid(&premise_terms_for_filter);
            raw_substs
                .into_iter()
                .filter(|pairs| {
                    let s_fresh = LNSubstVFresh::from_list(pairs.clone());
                    let mut fresh = filter_base.clone();
                    let subst = s_fresh.fresh_to_free_avoiding(|n| fresh.fresh_idents(n));
                    let premises: Vec<LNTerm> = premise_terms_for_filter
                        .iter()
                        .map(|t| {
                            let applied = apply_vterm(&subst, t.clone());
                            maude.reduce(&applied).unwrap_or(applied)
                        })
                        .collect();
                    let fresh_terms: Vec<LNTerm> = freshly_introduced
                        .iter()
                        .map(|t| apply_vterm(&subst, t.clone()))
                        .collect();
                    for ft in &fresh_terms {
                        for p in &premises {
                            if tamarin_term::term::is_subterm(ft, p) {
                                return false;
                            }
                        }
                    }
                    true
                })
                .collect()
        }
    };

    let composed_substs: Vec<LNSubstVFresh> = raw_substs
        .into_iter()
        .map(|pairs| {
            let vsubst = LNSubstVFresh::from_list(pairs);
            // composeVFresh vsubst abstractionSubst
            let composed = tamarin_term::subst_vfresh::compose_vfresh(&vsubst, &abstraction_subst);
            // normSubstVFresh' — normalise each range term via Maude.
            let normalised_pairs: Vec<(LVar, LNTerm)> = composed
                .to_list()
                .into_iter()
                .map(|(k, t)| {
                    let n = maude.reduce(&t).unwrap_or(t);
                    (k, n)
                })
                .collect();
            let normalised = LNSubstVFresh::from_list(normalised_pairs);
            // removeRenamings (post-compose, HS RuleVariants.hs)
            let cleaned = normalised.remove_renamings();
            // restrictVFresh (frees abstrPsCsAs)
            cleaned.restrict(&abstr_frees)
        })
        // `variantsProtoRule` (RuleVariants.hs) retains every composed entry,
        // including substitutions that restrict to pure renamings. Fresh
        // redundancy is filtered on the raw Maude variants before composition.
        .collect();

    if composed_substs.is_empty() {
        return Ok(RuleVariants::NoVariants);
    }

    // `simpDisjunction` (RuleVariants.hs) separates the substitution shared
    // by all variants from the residual SplitG disjunction. Apply the shared
    // part to the rule body. The Maude-backed pipeline includes
    // `simpSingleton`, which folds a singleton disjunction into that shared
    // substitution (EquationStore.hs).
    let (common_subst, residual) = crate::tools::equation_store::EquationStore::simp_disjunction(
        maude,
        |_, _| false,
        composed_substs,
    )?;

    // `makeRule`: apply the shared substitution to the rule body, then
    // restrict the residual variants to the body's remaining free variables
    // (`restrictVFresh (frees (prems, concs, acts, newvs))`). A residual that
    // simplified away is `trueDisj = [emptySubstVFresh]`; the `Just []` of a
    // contradictory store stays an empty disjunction.
    let abstracted_rule = tamarin_term::apply::Apply::apply(abstracted_rule, &common_subst);
    let final_substs = match residual {
        None => vec![LNSubstVFresh::empty()],
        Some(substs) => {
            let body_frees = tamarin_term::lterm::frees(&abstracted_rule);
            substs.iter().map(|s| s.restrict(&body_frees)).collect()
        }
    };

    // `renamePrecise` renumbers the rule and the variant domains together.
    let (abstracted_rule, final_substs) =
        rename_precise_rule_with_variants(abstracted_rule, final_substs);

    Ok(RuleVariants::Closed {
        body: abstracted_rule,
        variants: final_substs,
    })
}

/// HS `renamePrecise` of a `Rule ProtoRuleACInfo`: the variant domains are
/// walked before the body, as `HasFrees (Rule i)` folds the info first, and
/// the ranges keep their own fresh namespace (SubstVFresh.hs).
fn rename_precise_rule_with_variants(
    rule: ProtoRuleE,
    substs: Vec<LNSubstVFresh>,
) -> (ProtoRuleE, Vec<LNSubstVFresh>) {
    let (substs, rule) = tamarin_term::bind::rename_precise((substs, rule));
    (rule, substs)
}

/// `isFreshRedundant {}` (RuleVariants.hs): a freshly introduced term
/// occurs in a non-`Fr` premise.
fn identity_is_fresh_redundant(rule: &ProtoRuleE) -> bool {
    let premise_terms: Vec<&LNTerm> = rule
        .premises
        .iter()
        .filter(|f| !matches!(f.tag, crate::fact::FactTag::Fresh))
        .flat_map(|f| f.terms.iter())
        .collect();
    rule.premises
        .iter()
        .filter(|f| matches!(f.tag, crate::fact::FactTag::Fresh))
        .filter_map(|f| f.terms.first())
        .any(|ft| {
            premise_terms
                .iter()
                .any(|p| tamarin_term::term::is_subterm(ft, p))
        })
}

/// `null recomputedVariants` of HS `variantsCheck` (Wellformedness.hs):
/// whether `variantsProtoRule` returns `Nothing` for the rule.
pub fn open_rule_has_no_variants(
    maude: &MaudeHandle,
    opr: &OpenProtoRule,
) -> Result<bool, VariantsError> {
    Ok(match &opr.variants {
        RuleVariants::NoVariants => true,
        RuleVariants::Closed { .. } => false,
        RuleVariants::Unprepared => {
            variants_proto_rule(maude, &opr.rule)? == RuleVariants::NoVariants
        }
    })
}

/// Apply `closeProtoRule`'s zero-variant filter to each rule in place.
///
/// This deliberately inspects each item rather than collecting rule names:
/// partial evaluation may emit several distinct refined rules with the same
/// name, and each has its own variant result.
pub fn retain_rules_with_variants(
    theory: &mut Theory,
    maude: &MaudeHandle,
) -> Result<(), VariantsError> {
    let mut keep = Vec::with_capacity(theory.items.len());
    for item in &theory.items {
        keep.push(match item {
            TheoryItem::Rule(rule) => !open_rule_has_no_variants(maude, rule)?,
            _ => true,
        });
    }
    let mut keep = keep.into_iter();
    theory.items.retain(|_| keep.next().unwrap_or(true));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_term::vterm::Lit;

    use crate::fact::{Fact, FactTag};
    use crate::rule::{ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes};

    use tamarin_test_support::require_maude_path;

    fn empty_rule(name: &str) -> ProtoRuleE {
        let info = ProtoRuleEInfo {
            name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        };
        Rule::new(info, Vec::new(), Vec::new(), Vec::new())
    }

    /// `[Fr(~k)] --> [Out(~k)]` under the pair-only signature has no
    /// reducible operator, so its only variant is the identity: HS's
    /// `trueDisj`, with the body unchanged. A killed Maude shows that the
    /// short cut needs no query.
    #[test]
    fn variants_of_irreducible_rule_are_the_identity() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        h.kill_subprocess();
        // Rule: [Fr(~k)] --> [Out(~k)]
        let k = LVar::new("k", LSort::Fresh, 0);
        let kt: LNTerm = Term::Lit(Lit::Var(k));
        let prem = Fact::new(FactTag::Fresh, vec![kt.clone()]);
        let conc = Fact::new(FactTag::Out, vec![kt.clone()]);
        let info = ProtoRuleEInfo {
            name: ProtoRuleName::Stand("R"),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        };
        let rule = Rule::new(info, vec![prem.clone()], vec![conc.clone()], Vec::new());
        assert_eq!(
            variants_proto_rule(&h, &rule).expect("variants"),
            RuleVariants::Closed {
                body: rule,
                variants: vec![LNSubstVFresh::empty()],
            }
        );
    }

    /// `isFreshRedundant {}`: `[Fr(~k), In(~k)] --> []` has no variants.
    #[test]
    fn identity_of_a_fresh_redundant_rule_is_no_variant() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let k: LNTerm = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let mut rule = empty_rule("R");
        rule.premises = vec![
            Fact::new(FactTag::Fresh, vec![k.clone()]),
            Fact::new(FactTag::In, vec![k]),
        ];
        assert_eq!(
            variants_proto_rule(&h, &rule).expect("variants"),
            RuleVariants::NoVariants
        );
    }

    /// `renamePrecise` numbers each name from zero in the order the walk
    /// reaches it, and the pair puts the variant substitutions ahead of the
    /// rule body, so the substitution's domain key takes `x.0` and the
    /// premise's variable follows at `x.1`.  The range of the substitution is
    /// outside the walk, so the variable there keeps the index it came with.
    #[test]
    fn rename_precise_rule_visits_variant_keys_before_facts() {
        let mvar = |idx| LVar::new("x", LSort::Msg, idx);
        let mterm = |idx| -> LNTerm { Term::Lit(Lit::Var(mvar(idx))) };
        let mut rule = empty_rule("R");
        rule.premises = vec![Fact::new(FactTag::Out, vec![mterm(5)])];
        let substs = vec![LNSubstVFresh::from_list(vec![(mvar(9), mterm(7))])];

        let (renamed, renamed_substs) = rename_precise_rule_with_variants(rule, substs);

        assert_eq!(renamed_substs[0].to_list(), vec![(mvar(0), mterm(7))]);
        assert_eq!(renamed.premises[0].terms[0], mterm(1));
    }

    /// HS keeps `Just []`: an empty disjunction is closed as is, and unfolds
    /// to no rule (`unfoldRuleVariants`, Rule.hs).
    #[test]
    fn empty_variant_disjunction_unfolds_to_no_rule() {
        let mut rule = empty_rule("R");
        rule.premises.push(Fact::new(
            FactTag::In,
            vec![Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)))],
        ));
        let mut open = OpenProtoRule::new(rule.clone());
        open.variants = RuleVariants::Closed {
            body: rule,
            variants: Vec::new(),
        };
        let closed = crate::theory::closed_rules_ac(&open);
        assert!(closed[0].info.variants.is_empty());
        assert!(unfold_closed_rule(&open, &closed[0]).is_empty());
    }

    /// A Maude failure while deciding whether a rule has variants is an
    /// error, not "has variants".
    #[test]
    fn no_variants_check_propagates_transport_failure() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let mut rule = empty_rule("R");
        rule.premises.push(Fact::new(
            FactTag::In,
            vec![tamarin_term::builtin::fst(Term::Lit(Lit::Var(LVar::new(
                "x",
                LSort::Msg,
                0,
            ))))],
        ));
        h.kill_subprocess();
        assert!(open_rule_has_no_variants(&h, &OpenProtoRule::new(rule)).is_err());
    }

    #[test]
    fn open_rule_preparation_propagates_transport_failure() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let mut rule = empty_rule("R");
        rule.premises.push(Fact::new(
            FactTag::Out,
            vec![tamarin_term::builtin::fst(Term::Lit(Lit::Var(LVar::new(
                "x",
                LSort::Msg,
                0,
            ))))],
        ));
        let mut rule = OpenProtoRule::new(rule);
        h.kill_subprocess();

        assert!(prepare_open_rule_variant(&mut rule, &h).is_err());
        assert_eq!(rule.variants, RuleVariants::Unprepared);
    }

    #[test]
    fn zero_variant_filter_treats_duplicate_names_independently() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let mut sig = pair_maude_sig();
        sig.reducible_fun_syms
            .insert(tamarin_term::function_symbols::FunSym::List);
        sig = sig.refresh();
        let h = MaudeHandle::start(&path, sig.clone()).unwrap();

        let mut rule = empty_rule("refined");
        rule.conclusions.push(Fact::new(
            FactTag::Out,
            vec![Term::App(
                tamarin_term::function_symbols::FunSym::List,
                vec![Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)))].into(),
            )],
        ));
        let mut without_variants = OpenProtoRule::new(rule.clone());
        without_variants.variants = RuleVariants::NoVariants;
        let mut with_variants = OpenProtoRule::new(rule.clone());
        with_variants.variants = RuleVariants::Closed {
            body: rule,
            variants: vec![LNSubstVFresh::empty()],
        };

        let mut theory: Theory = Theory::new("T", sig);
        theory.items = vec![
            TheoryItem::Rule(without_variants),
            TheoryItem::Text(("separator".to_string(), String::new())),
            TheoryItem::Rule(with_variants),
        ];

        retain_rules_with_variants(&mut theory, &h).unwrap();
        assert_eq!(theory.items.len(), 2);
        assert!(matches!(theory.items[0], TheoryItem::Text(_)));
        assert!(matches!(
            &theory.items[1],
            TheoryItem::Rule(rule) if matches!(rule.variants, RuleVariants::Closed { .. })
        ));
    }
}
