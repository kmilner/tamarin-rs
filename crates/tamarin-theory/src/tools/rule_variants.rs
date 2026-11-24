// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.RuleVariants`: the AC variants of protocol rules.
//!
//! `abstract_rule_and_variants` is `variantsProtoRule`: abstract the
//! reducible subterms, ask Maude for the variants of the abstracted terms,
//! compose and normalise them, then `simpDisjunction` the result.
//! `variants_proto_rule` runs the same steps without abstraction, for rules
//! with nothing to abstract.

use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle, MaudePool};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;

use crate::fact::Fact;
use crate::rule::{ProtoRuleAC, ProtoRuleACInfo, ProtoRuleE};
use crate::theory::{OpenProtoRule, Theory, TheoryItem};

type LNSubst = Subst<Name, LVar>;

/// HS `unfoldRuleVariants` (Rule.hs) on one closed rule: one rule
/// `<name>___VARIANT_<i>` per variant substitution, each applied after
/// `freshToFreeAvoiding` against the AC rule. An empty disjunction stands for
/// `trueDisj`, so a body-divergent rule still unfolds to one variant.
pub(crate) fn unfold_closed_rule(parent: &OpenProtoRule, ac: &ProtoRuleAC) -> Vec<OpenProtoRule> {
    let o = closed_rule_as_open(parent, ac);
    if crate::rule::is_trivial_proto_variant_ac(ac, parent.rule_e()) {
        return vec![o];
    }
    let ac = &o.rule;
    let trivial_disj = [LNSubstVFresh::empty()];
    let substs: &[LNSubstVFresh] = if o.variant_substs.is_empty() {
        &trivial_disj
    } else {
        &o.variant_substs
    };
    if substs == trivial_disj && ac.info.name != o.rule_e().info.name {
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
                rule: ru,
                variant_substs: vec![LNSubstVFresh::empty()],
                abstracted_rule: None,
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
/// `variants (modulo AC)` blocks, whose bodies do not live in
/// `abstracted_rule`/`variant_substs` on their parent.
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
        rule,
        variant_substs: ac.info.variants.clone(),
        abstracted_rule: None,
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

/// `variantsProtoRule` (RuleVariants.hs) without the abstraction step:
/// Maude's variants of the rule's terms, simplified with `simpDisjunction`
/// and applied by `makeRule`. `Ok(None)` when Maude returns no variant.
pub fn variants_proto_rule(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Option<ProtoRuleAC>, VariantsError> {
    // Pack all rule terms into a single tuple so we get one
    // variants-call per rule.
    let Some(packed) = pack_rule_terms(rule) else {
        // No term arguments at all → no variants beyond the identity.
        return Ok(Some(make_proto_rule_ac(
            rule,
            &LNSubst::default(),
            vec![LNSubstVFresh::empty()],
        )));
    };
    let raw = maude.variants(&packed)?;
    if raw.is_empty() {
        return Ok(None);
    }
    let substs: Vec<LNSubstVFresh> = raw.into_iter().map(LNSubstVFresh::from_list).collect();
    // `simpDisjunction` (RuleVariants.hs) includes `simpSingleton`, folding a
    // singleton variant into the shared substitution applied to the rule body.
    let (common_subst, residual) =
        crate::tools::equation_store::EquationStore::simp_disjunction(maude, |_, _| false, substs)?;
    // HS `trueDisj = [emptySubstVFresh]` (RuleVariants.hs).
    let fresh_substs = residual.unwrap_or_else(|| vec![LNSubstVFresh::empty()]);
    Ok(Some(make_proto_rule_ac(rule, &common_subst, fresh_substs)))
}

/// Pack every term-argument of every fact in `rule` into a single
/// `list(...)` term so it can be passed to `MaudeHandle::variants`.
/// Returns `None` if the rule has no term arguments at all.
fn pack_rule_terms(rule: &ProtoRuleE) -> Option<LNTerm> {
    use tamarin_term::function_symbols::FunSym;
    let mut all = Vec::new();
    for f in &rule.premises {
        all.extend(f.terms.iter().cloned());
    }
    for f in &rule.actions {
        all.extend(f.terms.iter().cloned());
    }
    for f in &rule.conclusions {
        all.extend(f.terms.iter().cloned());
    }
    if all.is_empty() {
        None
    } else {
        Some(Term::App(FunSym::List, all.into()))
    }
}

/// HS `makeRule` (RuleVariants.hs): apply the common substitution to the
/// rule body and restrict each residual substitution to the body's frees.
fn make_proto_rule_ac(
    rule: &ProtoRuleE,
    common_subst: &LNSubst,
    variants: Vec<LNSubstVFresh>,
) -> ProtoRuleAC {
    // Apply commonSubst to the rule body (HS apply subst {ps,cs,as,nvs}).
    let (premises, conclusions, actions, new_vars) = if common_subst.is_empty() {
        (
            rule.premises.clone(),
            rule.conclusions.clone(),
            rule.actions.clone(),
            rule.new_vars.clone(),
        )
    } else {
        let map_facts = |fs: &[Fact<LNTerm>]| -> Vec<Fact<LNTerm>> {
            fs.iter()
                .map(|f| f.clone().map(|t| apply_vterm(common_subst, t)))
                .collect()
        };
        (
            map_facts(&rule.premises),
            map_facts(&rule.conclusions),
            map_facts(&rule.actions),
            rule.new_vars
                .iter()
                .map(|t| apply_vterm(common_subst, t.clone()))
                .collect(),
        )
    };

    // Compute frees of the new rule body and restrict each variant
    // subst to those (HS: `map (restrictVFresh (frees (prems, concs, acts, newvs))) freshSubsts0`).
    let frees_vec = tamarin_term::lterm::frees(&(
        (premises.clone(), conclusions.clone()),
        (actions.clone(), new_vars.clone()),
    ));
    let variants: Vec<LNSubstVFresh> = variants
        .into_iter()
        .map(|s| s.restrict(&frees_vec))
        .collect();

    let info = ProtoRuleACInfo {
        name: rule.info.name,
        attributes: rule.info.attributes.clone(),
        variants,
        loop_breakers: Vec::new(),
    };
    crate::rule::Rule {
        info,
        premises,
        conclusions,
        actions,
        new_vars,
    }
}

/// The variant disjunction of [`variants_proto_rule`], identity variant
/// included (it is the no-narrowing case of the `SplitG` goal); empty when
/// there is no variant.
pub fn variant_substs_for_rule(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Vec<LNSubstVFresh>, VariantsError> {
    let ac = match variants_proto_rule(maude, rule)? {
        Some(ac) => ac,
        None => return Ok(Vec::new()),
    };
    Ok(ac.info.variants)
}

/// Precompute the abstracted rule and variants of every reducible rule, as
/// HS `closeTheoryWithMaude` does. Rules that need only the raw AC query are
/// left to [`prepare_open_rule_variant`], after loop-breaker annotation.
/// With a pool, rules are processed in parallel on pooled Maude processes;
/// the results are written back in source order either way.
pub fn populate_rule_variants(
    elaborated: &mut Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
) -> Result<(), VariantsError> {
    if maude.maude_sig().reducible_fun_syms.is_empty() {
        return Ok(());
    }
    let outs: Result<Vec<Option<(ProtoRuleE, Vec<LNSubstVFresh>)>>, VariantsError> =
        if let Some(pool) = pool {
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
                    abstract_rule_and_variants(&pooled, &opr.rule)
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
                    abstract_rule_and_variants(maude, &opr.rule)
                })
                .collect()
        };
    // Sequential writeback in source order.
    for (item, out) in elaborated.items.iter_mut().zip(outs?) {
        let TheoryItem::Rule(opr) = item else {
            continue;
        };
        if let Some((abstracted, variants)) = out {
            opr.abstracted_rule = Some(abstracted);
            opr.variant_substs = variants;
        }
    }
    Ok(())
}

/// Close the protocol-rule portion of a theory in Haskell's order: compute
/// variants, report wellformedness while zero-variant rules are still present,
/// remove those rules, then optionally annotate loop breakers for a closed
/// theory. Both frontends use this sequence.
pub fn prepare_theory_rules(
    theory: &mut Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
    annotate_breakers: bool,
) -> Result<crate::wellformedness::WfReport, VariantsError> {
    populate_rule_variants(theory, maude, pool)?;
    let report = crate::wellformedness::check_wellformedness(theory, Some(maude))?;
    let fatal = crate::wellformedness::variants::fatal_wf_errors(&report);
    if annotate_breakers && !fatal.is_empty() {
        return Err(VariantsError::UnsupportedInput(fatal));
    }
    finish_theory_rules(theory, maude, annotate_breakers);
    Ok(report)
}

/// Re-close rules produced by partial evaluation. Unlike the initial close,
/// this phase has no additional wellformedness report, but filtering and loop
/// breaker annotation must retain the same ordering.
pub fn reprepare_theory_rules(
    theory: &mut Theory,
    maude: &MaudeHandle,
    pool: Option<&MaudePool>,
) -> Result<(), VariantsError> {
    populate_rule_variants(theory, maude, pool)?;
    finish_theory_rules(theory, maude, true);
    Ok(())
}

/// Enforce the fatal rule checks at the public proving boundary as well as in
/// the frontends. Ordinary wellformedness warnings do not prevent proving.
/// Validation must not consume the session's fresh-variable counter.
pub fn validate_theory_for_proving(
    theory: &Theory,
    maude: &MaudeHandle,
) -> Result<(), VariantsError> {
    let _plain = crate::pretty_hpj::HtmlDocGuard::disable();
    let validation_maude = maude.with_fresh_counter_from(maude.fresh_counter_peek());
    let mut report =
        crate::wellformedness::variants::explicit_variants_report(theory, &validation_maude)?;
    let macros: Vec<_> = theory.macros().cloned().collect();
    for rule in theory.rules() {
        // Closing may replace `rule` by an AC member with supported added
        // products. Check the original E half, but expand its source macros.
        let source = crate::rule::apply_macro_in_rule(&macros, rule.rule_e().clone());
        report.extend(crate::wellformedness::mult::unsupported_products_report([
            &source,
        ]));
    }
    let fatal = crate::wellformedness::variants::fatal_wf_errors(&report);
    if fatal.is_empty() {
        Ok(())
    } else {
        Err(VariantsError::UnsupportedInput(fatal))
    }
}

fn finish_theory_rules(theory: &mut Theory, maude: &MaudeHandle, annotate_breakers: bool) {
    retain_rules_with_variants(theory, maude);
    if annotate_breakers {
        let macros: Vec<_> = theory.macros().cloned().collect();
        for item in &mut theory.items {
            if let TheoryItem::Rule(rule) = item {
                rule.expand_variant_macros(&macros);
            }
        }
        crate::constraint::solver::context::annotate_theory_loop_breakers(theory, maude);
    }
}

fn prepared_rule_variant(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Option<(Option<ProtoRuleE>, Vec<LNSubstVFresh>)>, VariantsError> {
    let reducible = &maude.maude_sig().reducible_fun_syms_fast;
    let has_reducible = rule
        .premises
        .iter()
        .chain(&rule.actions)
        .chain(&rule.conclusions)
        .flat_map(|fact| fact.terms.iter())
        .chain(rule.new_vars.iter())
        .any(|term| term.any_fun_sym(|symbol| reducible.contains(symbol)));
    if !has_reducible {
        if let Some(renamed) = rename_precise_rule_if_changed(rule) {
            return Ok(Some((Some(renamed), vec![LNSubstVFresh::empty()])));
        }
        let variants = variant_substs_for_rule(maude, rule)?;
        return Ok((!variants.is_empty()).then_some((None, variants)));
    }
    match abstract_rule_and_variants(maude, rule) {
        Ok(Some((abstracted, variants))) => Ok(Some((Some(abstracted), variants))),
        // A reducible rule with no variants is deliberately left empty;
        // the frontend reports and removes it while closing the theory.
        Ok(None) => Ok(None),
        Err(error) => Err(error),
    }
}

/// Complete one rule for a solver context. Whole-theory closing precomputes
/// reducible variants, but the raw AC query for an otherwise unchanged rule
/// deliberately stays here: moving it before loop-breaker annotation changes
/// variant/case canonicalization in AC theories.
pub fn prepare_open_rule_variant(
    rule: &mut OpenProtoRule,
    maude: &MaudeHandle,
) -> Result<(), VariantsError> {
    if rule.abstracted_rule.is_some() || !rule.variant_substs.is_empty() {
        return Ok(());
    }
    if let Some((abstracted, variants)) = prepared_rule_variant(maude, &rule.rule)? {
        rule.abstracted_rule = abstracted;
        rule.variant_substs = variants;
    }
    Ok(())
}

pub fn abstract_rule_and_variants(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Option<(ProtoRuleE, Vec<LNSubstVFresh>)>, VariantsError> {
    use tamarin_term::function_symbols::FunSym;
    let irreducible = maude.maude_sig().irreducible_fun_syms.clone();

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

    // Rust-only short cut: with nothing reducible abstracted, the only
    // variant is the identity, so skip Maude. HS still applies
    // `renamePrecise`, which changes the rule only when two variables share
    // a name.
    let has_reducible_abstraction = bindings
        .iter()
        .any(|(t, _)| matches!(t, Term::App(f, _) if !irreducible.contains(f)));
    if !has_reducible_abstraction {
        return Ok(
            rename_precise_rule_if_changed(rule).map(|ac| (ac, vec![LNSubstVFresh::empty()]))
        );
    }

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
        return Ok(None);
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
        return Ok(None);
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

    // Apply common_subst to the abstracted rule's terms.
    let abstracted_rule = if common_subst.is_empty() {
        abstracted_rule
    } else {
        let map_facts = |fs: Vec<Fact<LNTerm>>| -> Vec<Fact<LNTerm>> {
            fs.into_iter()
                .map(|f| f.map(|t| apply_vterm(&common_subst, t)))
                .collect()
        };
        let prems = map_facts(abstracted_rule.premises);
        let concs = map_facts(abstracted_rule.conclusions);
        let acts = map_facts(abstracted_rule.actions);
        let nvs: Vec<LNTerm> = abstracted_rule
            .new_vars
            .into_iter()
            .map(|t| apply_vterm(&common_subst, t))
            .collect();
        crate::rule::Rule::new(rule.info.clone(), prems, concs, acts).with_new_vars(nvs)
    };

    // `trueDisj = [emptySubstVFresh]` for a residual that simplified away.
    // Divergence: HS keeps the `Just []` of a contradictory store as an empty
    // disjunction; here it also becomes `trueDisj` (never seen on the corpus).
    let final_substs: Vec<LNSubstVFresh> = match residual {
        Some(rs) if !rs.is_empty() => rs,
        _ => vec![LNSubstVFresh::empty()],
    };

    // `renamePrecise` renumbers the rule and the variant domains together.
    let (abstracted_rule, final_substs) =
        rename_precise_rule_with_variants(abstracted_rule, final_substs);

    Ok(Some((abstracted_rule, final_substs)))
}

/// HS `renamePrecise` (RuleVariants.hs) of a rule whose variant disjunction
/// is the trivial `[emptySubstVFresh]`: the per-name renumbered rule, or
/// `None` when the rule is already in that normal form.
pub fn rename_precise_rule_if_changed(rule: &ProtoRuleE) -> Option<ProtoRuleE> {
    // The first occurrence of each variable draws its per-name index, as in
    // `renamePrecise`; the rule changes iff some variable's index does.
    let mut state = tamarin_utils::fresh::PreciseFreshState::nothing_used();
    let mut seen = std::collections::BTreeSet::new();
    let changes = tamarin_term::lterm::frees_list(rule)
        .into_iter()
        .filter(|v| seen.insert(*v))
        .any(|v| state.fresh_ident(v.name) != v.idx);
    changes.then(|| rename_precise_rule_with_variants(rule.clone(), vec![LNSubstVFresh::empty()]).0)
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

/// `null recomputedVariants` of HS `variantsCheck` (Wellformedness.hs): does
/// `variantsProtoRule` return `Nothing`, i.e. is every variant
/// fresh-redundant? A rule without reducible subterms has only the identity
/// variant, so the check is syntactic; otherwise it is
/// `abstract_rule_and_variants(..) == Ok(None)`, which a caller that already
/// knows it passes as `reducible_has_no_variants`.
pub fn rule_has_no_variants_for_wf_with(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
    reducible_has_no_variants: Option<bool>,
) -> bool {
    // Without reducible subterms the only variant is `{}`, and
    // `isFreshRedundant {}` is syntactic.
    let has_reducible = {
        let sig = maude.maude_sig();
        let term_has_red =
            |t: &LNTerm| t.any_fun_sym(|f| !sig.irreducible_fun_syms_fast.contains(f));
        rule.premises
            .iter()
            .chain(rule.actions.iter())
            .chain(rule.conclusions.iter())
            .any(|f| f.terms.iter().any(&term_has_red))
            || rule.new_vars.iter().any(term_has_red)
    };

    if !has_reducible {
        // Syntactic `isFreshRedundant {}` check.
        let freshly_introduced: Vec<&LNTerm> = rule
            .premises
            .iter()
            .filter(|f| matches!(f.tag, crate::fact::FactTag::Fresh))
            .filter_map(|f| f.terms.first())
            .collect();
        let premise_terms: Vec<&LNTerm> = rule
            .premises
            .iter()
            .filter(|f| !matches!(f.tag, crate::fact::FactTag::Fresh))
            .flat_map(|f| f.terms.iter())
            .collect();
        if freshly_introduced.is_empty() || premise_terms.is_empty() {
            // No Fr facts or no non-Fr premise terms → identity variant
            // survives → rule HAS a variant.
            return false;
        }
        // isFreshRedundant {} = True iff any fresh term appears in a
        // non-Fr premise (i.e. all identity variants are redundant).
        return freshly_introduced.iter().any(|ft| {
            premise_terms
                .iter()
                .any(|p| tamarin_term::term::is_subterm(ft, p))
        });
    }

    // Path 2: reducible rule — `abstract_rule_and_variants` returns
    // `Ok(None)` when all composed substs are filtered out.  Reuse the
    // precomputed answer when the caller already ran the computation
    // (avoids a duplicate `get variants` Maude round-trip).
    if let Some(no_variants) = reducible_has_no_variants {
        return no_variants;
    }
    matches!(abstract_rule_and_variants(maude, rule), Ok(None))
}

/// [`rule_has_no_variants_for_wf_with`] for a theory rule that
/// [`populate_rule_variants`] has already visited: the reducible-path
/// verdict is read off the [`OpenProtoRule`], so no rule costs a second
/// `get variants` query.
///
/// The whole-theory pass leaves destructor-free rules untouched; the
/// syntactic path of [`rule_has_no_variants_for_wf_with`] answers their
/// fresh-redundancy condition directly.
pub fn open_rule_has_no_variants(maude: &MaudeHandle, opr: &OpenProtoRule) -> bool {
    let reducible_has_no_variants = (!maude.maude_sig().reducible_fun_syms.is_empty())
        .then(|| opr.abstracted_rule.is_none() && opr.variant_substs.is_empty());
    rule_has_no_variants_for_wf_with(maude, &opr.rule, reducible_has_no_variants)
}

/// Apply `closeProtoRule`'s zero-variant filter to each rule in place.
///
/// This deliberately inspects each item rather than collecting rule names:
/// partial evaluation may emit several distinct refined rules with the same
/// name, and each has its own variant result.
pub fn retain_rules_with_variants(theory: &mut Theory, maude: &MaudeHandle) {
    theory.items.retain(|item| match item {
        TheoryItem::Rule(rule) => !open_rule_has_no_variants(maude, rule),
        _ => true,
    });
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

    /// A term-free rule never reaches Maude at all.  `pack_rule_terms`
    /// returns `None`.  The code then wraps the rule with HS's
    /// `trueDisj = [emptySubstVFresh]` (RuleVariants.hs).  The body of
    /// the rule must come through untouched.  `makeRule` applies an empty
    /// `commonSubst`.
    #[test]
    fn variants_of_rule_with_no_terms_is_identity() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let rule = empty_rule("R");
        let ac = variants_proto_rule(&h, &rule).expect("variants").unwrap();
        assert_eq!(ac.info.variants, vec![LNSubstVFresh::empty()]);
        assert_eq!(ac.premises, rule.premises);
        assert_eq!(ac.actions, rule.actions);
        assert_eq!(ac.conclusions, rule.conclusions);
    }

    /// `[Fr(~k)] --> [Out(~k)]` under the pair-only signature has no
    /// reducible operator.  Maude's single variant is therefore the identity.
    /// `simp_disjunction_with_maude` folds that variant into `commonSubst`.
    /// What is left is exactly HS's `trueDisj`, and not a residual
    /// disjunction.  A residual here is the NAXOS_eCK_private
    /// Init_1-vs-Ltk_reveal shape.  In that shape, entries that HS bakes into
    /// the rule body instead survive as a `SplitG` goal.
    #[test]
    fn variants_of_simple_rule_via_maude() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
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
        let ac = variants_proto_rule(&h, &rule).expect("variants").unwrap();
        assert_eq!(ac.info.variants, vec![LNSubstVFresh::empty()]);
        // `commonSubst` is empty too, so `~k` survives verbatim in the body.
        assert_eq!(ac.premises, vec![prem]);
        assert_eq!(ac.conclusions, vec![conc]);
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

    #[test]
    fn whole_theory_pass_defers_unchanged_rules_to_the_context() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let rule = empty_rule("R");
        let mut theory = Theory::new("T", pair_maude_sig());
        theory
            .items
            .push(TheoryItem::Rule(OpenProtoRule::new(rule)));

        populate_rule_variants(&mut theory, &h, None).expect("populate variants");

        let TheoryItem::Rule(rule) = &theory.items[0] else {
            panic!("expected rule")
        };
        assert!(rule.abstracted_rule.is_none());
        assert!(rule.variant_substs.is_empty());
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
            vec![Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)))],
        ));
        let mut rule = OpenProtoRule::new(rule);
        h.kill_subprocess();

        assert!(prepare_open_rule_variant(&mut rule, &h).is_err());
        assert!(rule.abstracted_rule.is_none());
        assert!(rule.variant_substs.is_empty());
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
        let without_variants = OpenProtoRule::new(rule.clone());
        let mut with_variants = OpenProtoRule::new(rule.clone());
        with_variants.abstracted_rule = Some(rule);

        let mut theory: Theory = Theory::new("T", sig);
        theory.items = vec![
            TheoryItem::Rule(without_variants),
            TheoryItem::Text(("separator".to_string(), String::new())),
            TheoryItem::Rule(with_variants),
        ];

        retain_rules_with_variants(&mut theory, &h);
        assert_eq!(theory.items.len(), 2);
        assert!(matches!(theory.items[0], TheoryItem::Text(_)));
        assert!(matches!(
            &theory.items[1],
            TheoryItem::Rule(rule) if rule.abstracted_rule.is_some()
        ));
    }
}
