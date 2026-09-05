// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Tools.RuleVariants` — computes the AC-variants of
//! a protocol rule via the Maude bridge.
//!
//! The Haskell reference does an "abstract → narrow → substitute →
//! simplify" dance:
//!
//! 1. Walk the rule's facts and replace each complex (reducible)
//!    sub-term with a fresh variable, remembering the bindings.
//! 2. Pack the replaced terms into a single tuple and ask Maude for
//!    its variants — `MaudeHandle::variants(packed) -> Vec<MSubst>`.
//! 3. For each variant subst, compose with the abstraction-bindings
//!    subst and renormalise.
//! 4. Simplify via `simp_disjunction_with_maude`.
//! 5. Wrap as a `ProtoRuleAC` with the surviving substitutions stored
//!    in its `variants` field.
//!
//! The full `abstrTerm` machinery (step 1 above) lives in
//! `abstract_rule_and_variants`, which is the HS-faithful production
//! path used by `run.rs` and the constraint solver's `context.rs`.
//! `variants_proto_rule` is a lighter helper that runs steps 2-5
//! directly on the rule's terms (no abstraction).  `variant_substs_for_rule`
//! wraps it for `context.rs`'s non-reducible branch, where there is
//! nothing to abstract.

use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle, MaudePool};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;

use crate::fact::Fact;
use crate::rule::{ProtoRuleAC, ProtoRuleACInfo, ProtoRuleE};
use crate::theory::{OpenProtoRule, Theory, TheoryItem};

type LNSubst = Subst<Name, LVar>;

#[derive(Debug, Clone)]
pub enum VariantsError {
    Maude(String),
}

impl std::fmt::Display for VariantsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariantsError::Maude(s) => write!(f, "Maude error: {}", s),
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

/// `variantsProtoRule`: compute the AC-variants of a protocol rule.
/// Returns `Ok(None)` when Maude reports no non-trivial variants; the
/// caller can keep the rule as-is. Returns `Ok(Some(ac_rule))` with
/// the variant substitutions populated.
///
/// HS-faithful: mirrors `variantsProtoRule` (RuleVariants.hs:61-91):
///
/// ```haskell
/// x <- simpDisjunction hnd (const (const False)) (Disj substs)
/// case x of
///   (commonSubst, Nothing)         -> return $ makeRule abstrPsCsAs commonSubst trueDisj
///   (commonSubst, Just freshSubsts) -> return $ makeRule abstrPsCsAs commonSubst freshSubsts
/// ```
///
/// where `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:61-133, see line
/// 119) and `makeRule` (RuleVariants.hs:110-117) applies `commonSubst` to the
/// rule body and restricts the residual fresh substs to the new
/// frees.
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
    // HS-faithful `simpDisjunction hnd (const (const False)) (Disj substs)`
    // (RuleVariants.hs:61-134, see line 82).  Routes through `simp1`'s full pipeline
    // including `simpSingleton` (EquationStore.hs:411-417, invoked from simp1 at 381) — that pass
    // folds a singleton-variant disj into the free subst, which is
    // what HS's `commonSubst` carries.  Without this, the SplitG
    // residual retains entries that HS bakes into the rule body via
    // `makeRule`'s `apply commonSubst` (RuleVariants.hs:114-117) —
    // which is the root of the NAXOS_eCK_private Init_1-vs-Ltk_reveal
    // divergence.
    let (common_subst, residual) =
        crate::tools::equation_store::EquationStore::simp_disjunction_with_maude(
            substs,
            |_, _| false,
            maude,
        )?;
    // HS `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:61-133, see line 119).
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

/// Build a `ProtoRuleAC` from a `ProtoRuleE` plus the precomputed
/// variants list.
///
/// HS `makeRule` (RuleVariants.hs:110-117) applies `commonSubst` (the
/// free part returned by `simpDisjunction`) to the rule body, then
/// restricts each fresh subst to the rule's surviving frees:
///
/// ```haskell
/// makeRule (ps, cs, as, nvs) subst freshSubsts0 =
///     Rule (ProtoRuleACInfo na attr (Disj freshSubsts) []) prems concs acts newvs
///   where prems = apply subst ps
///         concs = apply subst cs
///         acts  = apply subst as
///         newvs = apply subst nvs
///         freshSubsts = map (restrictVFresh (frees (prems, concs, acts, newvs))) freshSubsts0
/// ```
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
    use tamarin_term::lterm::HasFrees;
    let mut frees_set: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    {
        let mut visit = |v: &LVar| {
            frees_set.insert(*v);
        };
        for f in premises.iter().chain(&conclusions).chain(&actions) {
            for t in f.terms.iter() {
                t.for_each_free(&mut visit);
            }
        }
        for t in &new_vars {
            t.for_each_free(&mut visit);
        }
    }
    let frees_vec: Vec<LVar> = frees_set.into_iter().collect();
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

/// Returns the raw variant substitutions of `rule` (the `Disj LNSubstVFresh`
/// of `RuleACConstrs` in Haskell, taken from `variants_proto_rule`'s
/// `ac.info.variants`) — the substitutions that should be installed as a
/// SplitG goal via `solve_rule_constraints`.
///
/// Haskell-faithful: keeps ALL variants Maude returns (including the
/// identity).  The identity variant corresponds to "destructor doesn't
/// reduce" — e.g. `adec(c, k)` stays as is when `c ≠ aenc(_, pk(k))`.
/// Filtering it out drops the no-narrowing case from the SplitG, so
/// downstream search misses the alternative where the term is irreducible.
///
/// Do NOT filter out pure-renaming variants here either: the raw variant
/// *substitutions* (`Disj LNSubstVFresh` of Haskell's `RuleACConstrs`) need
/// the identity kept — it's what tells `solveRuleConstraints` to install a
/// SplitG with both narrowing and no-narrowing branches.
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

/// Port of Haskell `abstrRule` (RuleVariants.hs:92-108): walks every
/// fact-term in `rule` and replaces each reducible-headed sub-term
/// with a fresh `LVar`.  Returns the abstracted rule plus the
/// variant disjunction whose substs talk about the abstracted rule's
/// fresh vars (after composing Maude's variant substs over the
/// abstraction bindings).
///
/// The variant disjunction returned by Maude on the abstracted form
/// is composed with the abstraction substitution to produce the
/// final SplitG disjunction whose substs talk about the abstracted
/// rule's fresh vars (the z_i).
///
/// Returns `Ok(None)` when no reducible-headed sub-terms exist, in
/// which case `rule` is already canonical and needs no variants.
///
/// Populate the AC representation returned by [`abstract_rule_and_variants`],
/// mirroring HS `closeTheoryWithMaude`'s variant pre-computation
/// (`ClosedTheory.hs` `closeTheory`). Rules whose unchanged form still needs a
/// raw AC query are deliberately left for [`prepare_open_rule_variant`] after
/// loop-breaker annotation. Both the CLI
/// (`--prove`) and the interactive server call this so a theory is
/// "closed" identically on both paths.
///
/// When `pool` is `Some`, rules are narrowed in parallel, each on its
/// own pooled Maude subprocess.  When `pool` is `None`, computation is
/// SEQUENTIAL on the single `maude` handle — a raw [`MaudeHandle`] wraps
/// one child process and is not safe to share across rayon threads.
/// Output is identical either way (writeback is in source order,
/// mirroring HS's `parList rdeepseq`).
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
    let report = crate::wellformedness::check_wellformedness(theory, Some(maude));
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

fn finish_theory_rules(theory: &mut Theory, maude: &MaudeHandle, annotate_breakers: bool) {
    retain_rules_with_variants(theory, maude);
    if annotate_breakers {
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
    use tamarin_term::lterm::HasFrees;
    let irreducible = maude.maude_sig().irreducible_fun_syms.clone();

    // Avoid clashes with the rule's existing free vars.  HS:
    // `convertRule \`evalFreshTAvoiding\` ru` — Fresh counter starts at
    // (max idx of rule's free vars) + 1.
    let mut avoid_max: u64 = 0;
    {
        let mut visit = |v: &LVar| {
            if v.idx > avoid_max {
                avoid_max = v.idx;
            }
        };
        for f in rule
            .premises
            .iter()
            .chain(&rule.actions)
            .chain(&rule.conclusions)
        {
            for t in f.terms.iter() {
                t.for_each_free(&mut visit);
            }
        }
        for t in &rule.new_vars {
            t.for_each_free(&mut visit);
        }
    }
    // HS-faithful: `convertRule \`evalFreshTAvoiding\` ru`
    // (RuleVariants.hs:61-134, see line 64) runs the variant computation in a Fresh monad
    // whose counter starts at `max(ru.idxs)+1` PER RULE.  Without this,
    // RS's global Maude counter keeps climbing across rules, so the
    // variant value vars (allocated via the Maude back-conversion's
    // `evalFreshAvoiding`) end up at much higher idxs than HS's — that's
    // the +12 offset between RS (~ltkS.19/20/21) and HS (~ltkS.7/8/9)
    // for Tutorial.spthy's Serv_1.
    //
    // `with_fresh_counter_from` clones the handle keeping the underlying
    // Maude PROCESS shared but with a fresh PER-CALL counter — exactly
    // HS's evalFreshTAvoiding semantics.
    let local_maude_owned = maude.with_fresh_counter_from(avoid_max);
    let maude: &MaudeHandle = &local_maude_owned;

    fn name_hint(t: &LNTerm) -> String {
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => v.name.to_string(),
            _ => "z".to_string(),
        }
    }

    // Memoization: original term → fresh LVar.  HS: `BindT` state over
    // `M.Map LNTerm LVar` (Bind.hs:54-54,76; RuleVariants.hs:61-133, see line
    // 92,105) ensures
    // each unique LNTerm gets ONE binding, reused on subsequent
    // encounters.  A `BTreeMap` mirrors HS's `M.Map` exactly: O(log n)
    // lookup AND an already term-`Ord`-sorted `M.toList` view (used below
    // as `sorted_bindings`), so no separate sort pass is needed.
    let mut bindings: std::collections::BTreeMap<LNTerm, LVar> = std::collections::BTreeMap::new();

    // HS-faithful `abstrTerm` (RuleVariants.hs:103-109).
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
            // HS-faithful `abstrTerm` (RuleVariants.hs:61-134, see line 104):
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

    // HS-faithful: import ALL leaf vars FIRST (RuleVariants.hs:61-134, see line 95
    // `mapM_ abstrTerm [varTerm v | v <- frees (prems0, concs0, acts0, nvs0)]`).
    // This populates the bindings map so leaf vars get RENAMED to fresh
    // idxs with name preserved (via getHint = lvarName for Var).  Without
    // this, abstractionSubst lacks leaf-var entries and downstream
    // composeVFresh leaves the original rule's free vars unrenamed, which
    // makes Maude's variant-witness allocation collide across variants.
    //
    // HS's `frees` (LTerm.hs:613-614) returns `sortednub . freesList` —
    // a SORT+DEDUP list, ordered by `Ord LVar = idx <> sort <> name`
    // (LTerm.hs:546-548).  Document-order iteration would assign fresh
    // idxs based on which fact mentions a variable first, which decides
    // the FIRST KEY of every Maude variant subst and hence the variants'
    // post-`S.fromList` sort order in HS's `simpDisjunction`.
    //
    // For wireguard's `Handshake_Init`, document order visits `pkR`
    // (premise `!F_StateInvariants(..., pkR, ...)`) before `~ekI`
    // (premise `Fr(~ekI)`), so `pkR` ends up at a smaller fresh idx
    // than `~ekI`; the variants then sort with `pkR` first → the
    // DH_neutral variant lands before the AC-decomposed one.  HS's
    // sorted `frees` puts `~ekI` (Fresh, idx 0, name "ekI") before
    // `pkR` (Msg, idx 0, name "pkR") via `Fresh < Msg` on the LSort
    // partial order, so `~ekI` gets the smaller fresh idx and the
    // AC-decomposed variant lands before DH_neutral — matching HS.
    //
    // HS-faithful `frees`: a BTreeSet sorts insertion by `Ord LVar`
    // and dedupes — exactly `sortednub` semantics.
    let mut leaf_set: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    let mut visit = |v: &LVar| {
        leaf_set.insert(*v);
    };
    for f in rule
        .premises
        .iter()
        .chain(&rule.actions)
        .chain(&rule.conclusions)
    {
        f.terms.iter().for_each(|t| t.for_each_free(&mut visit));
    }
    for t in &rule.new_vars {
        t.for_each_free(&mut visit);
    }
    for v in leaf_set {
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

    // Count reducible-head abstractions: if zero, no useful variants.
    // (With leaf-rename, `bindings` always non-empty when rule has vars.)
    let has_reducible_abstraction = bindings
        .iter()
        .any(|(t, _)| matches!(t, Term::App(f, _) if !irreducible.contains(f)));
    if !has_reducible_abstraction {
        // HS's `variantsProtoRule` has NO such short-circuit: it abstracts
        // every free var and applies `renamePrecise` (RuleVariants.hs:61-134, see line 64,
        // 78) even when the only variant is the identity.  For rules whose
        // vars are already in renamePrecise normal form (the common case)
        // the AC body equals the E body → `isTrivialProtoVariantAC` is True
        // → "has exactly the trivial AC variant", so the short-circuit is
        // faithful.  But when renamePrecise WOULD change a var — e.g. a rule
        // with two free vars sharing a name (`~ltk` and `ltk`), where it
        // disambiguates the second to `ltk.1` — the AC body differs from the
        // E body and HS prints the full `rule (modulo AC) ...` block.  Since
        // there are no reducible sub-terms, the sole variant IS the identity:
        // return `renamePrecise(rule)` with the trivial disjunction directly
        // (no Maude call).  This only diverges from the short-circuit for
        // rules renamePrecise actually rewrites (issue527's Register_pk).
        if rule_renames_under_precise(rule) {
            let (ac, substs) =
                rename_precise_rule_with_variants(rule.clone(), vec![LNSubstVFresh::empty()]);
            return Ok(Some((ac, substs)));
        }
        return Ok(None);
    }

    // Build the abstracted rule.
    let abstracted_rule =
        crate::rule::Rule::new(rule.info.clone(), prems, concs, acts).with_new_vars(nvs);

    // abstractionSubst (HS RuleVariants.hs:70-71):
    //   `eqsAbstr = map swap (M.toList bindings)` — list of (lvar, orig_term).
    //   `abstractionSubst = substFromList eqsAbstr` — FREE Subst.
    //
    // With leaf-rename, this includes BOTH leaf entries `(lv_renamed,
    // Var v_orig)` AND reducible entries `(z_i, complex_term)`.
    //
    // CRITICAL: HS's `bindings :: M.Map LNTerm LVar` is keyed by the
    // ORIGINAL term (`importBinding (\`LVar\` sortOfLNTerm t) t ...`,
    // RuleVariants.hs:61-134, see line 104), and `M.toList bindings` therefore yields the
    // entries SORTED by the original term's `Ord` — NOT by insertion
    // order.  `abstractedTerms = map snd eqsAbstr` (RuleVariants.hs:61-134, see line 69)
    // is consequently a term-`Ord`-sorted list, and it is exactly the
    // payload of the `get variants in MSG : list(cons(...))` Maude query
    // (`fAppList abstractedTerms`, RuleVariants.hs:61-134, see line 72).  A different
    // query-argument order flips downstream AC-symmetric unifier
    // enumeration (e.g. the UM_three_pass `CK_secure_UM3`
    // `R_Complete_case_1↔case_2` arm swap), so `abstractedTerms` must
    // follow HS's ORIGINAL-term `Ord` order — which `bindings.iter()`
    // (a BTreeMap) already yields.  Mirror `M.toList` by iterating the
    // binding entries in
    // ORIGINAL-term key order.  Both `abstractionSubst` (substFromList —
    // itself a Map, so order-insensitive) and `abstractedTerms` (the
    // ordered query payload) read from this sorted view.  `bindings` is a
    // `BTreeMap`, so `.iter()` already yields entries in term-`Ord` key
    // order — exactly `M.toList`'s ordering, no explicit sort needed.
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

    // HS-faithful `msubstToLSubstVFresh` (Maude/Types.hs:137-146, see line 144) returns
    // `removeRenamings $ substFromListVFresh slist` — i.e. EVERY raw Maude
    // variant has its pure-rename entries dropped as part of the
    // back-conversion (Maude/Process.hs:271 `map (msubstToLSubstVFresh bindings)
    // <$> parseVariantsReply`).  So by the time HS's `variantSubsts`
    // (RuleVariants.hs:61-133, see line 71) reach BOTH `isFreshRedundant vsubst`
    // (RuleVariants.hs:61-133, see line 76) AND `composeVFresh vsubst
    // abstractionSubst`
    // (RuleVariants.hs:61-133, see line 74), each `vsubst` is already
    // removeRenamings'd.
    //
    // RS's `MaudeHandle::variants` (maude_proc.rs) does NOT apply
    // `remove_renamings` (unlike `MaudeHandle::unify`, which does), so
    // we clean each variant HERE — once, up front — to match HS.  This puts
    // the H20/`isFreshRedundant` filter (below) and the compose loop on the
    // SAME cleaned form HS uses.  `remove_renamings` filters entries WITHIN
    // each subst (never the list), preserving the Maude-determined variant
    // ordering that the per-variant Ord sort relies on.
    let raw_substs: Vec<Vec<(LVar, LNTerm)>> = raw_substs
        .into_iter()
        .map(|pairs| LNSubstVFresh::from_list(pairs).remove_renamings().to_list())
        .collect();

    // HS pipeline per variant (RuleVariants.hs:73-77):
    //   restrictVFresh (frees abstrPsCsAs) $
    //     removeRenamings $ normSubstVFresh' $
    //     composeVFresh vsubst abstractionSubst
    //
    // The `compose_vfresh` helper mirrors HS's full pipeline:
    // extendWithRenaming + freshToFreeAvoidingFast + compose + freeToFreshRaw.
    // Without this, two variants whose Maude-back-conversion shapes
    // happen to collide end up with structurally-identical range vars
    // and collapse at perform_split (split_case ordering bug).
    let abstr_frees: Vec<LVar> = {
        let mut s: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        {
            let mut visit = |v: &LVar| {
                s.insert(*v);
            };
            for f in abstracted_rule
                .premises
                .iter()
                .chain(&abstracted_rule.actions)
                .chain(&abstracted_rule.conclusions)
            {
                for t in f.terms.iter() {
                    t.for_each_free(&mut visit);
                }
            }
            for t in &abstracted_rule.new_vars {
                t.for_each_free(&mut visit);
            }
        }
        s.into_iter().collect()
    };

    // HS-faithful: filter variants via `isFreshRedundant` (RuleVariants.hs:128-134)
    // BEFORE composition. A variant is redundant if it forces a freshly
    // introduced term (from a Fresh-fact premise) to also appear in a
    // non-Fresh premise after substitution.  These variants represent
    // physically impossible bindings — they require a Fresh nonce to
    // appear simultaneously in two unrelated message positions.
    //
    // Without this filter, RS keeps redundant variants that HS drops,
    // causing the variant disj to retain heterogeneous outer ops across
    // substs (identity variant with `convertpcs(...)` vs reducing variant
    // with `sign(...)`). simp_abstract_fun can't lift heterogeneous ops,
    // so same-image pairs never emerge, simp_identify never fires, no
    // multi-key equivalence classes form, enforce_ku_action_uniqueness
    // never merges. This is the root cause of resolved1's 26-line diff.
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
            let mut frees = std::collections::BTreeSet::new();
            for t in &premise_terms_for_filter {
                t.for_each_free(&mut |v| {
                    frees.insert(*v);
                });
            }
            // HS-faithful: `freshToFreeAvoidingFast sFresh (frees premiseTerms)`
            // (RuleVariants.hs:61-134, see line 131; defined Term/Substitution.hs:77-81) runs `rename` inside `evalFreshAvoiding
            // (frees premiseTerms)` — a LOCAL Fresh scope seeded at
            // `succ (max idx in frees premiseTerms)`.  Witnesses minted by
            // this filter do NOT advance the outer (per-rule) MonadFresh
            // counter (RuleVariants.hs:61-134, see line 64 `convertRule \`evalFreshTAvoiding\` ru`)
            // because `evalFreshAvoiding` nests its OWN Fresh state.
            //
            // Advancing the per-rule Maude counter per filter call would
            // inflate it across all raw variants (e.g. Handshake_Resp:
            // 27→160 pre-simp) and propagate into every downstream
            // avoid_max, producing range-var idxs ~2255 vs HS's ~393.
            //
            // Mirror HS by seeding LOCALLY from `frees premiseTerms` and
            // advancing only a local `counter`.  Maude's global counter
            // stays untouched by this filter.
            let frees_max: u64 = frees.iter().map(|v| v.idx).max().unwrap_or(0);
            let filter_base: u64 = frees_max.saturating_add(1);
            raw_substs
                .into_iter()
                .filter(|pairs| {
                    let s_fresh = LNSubstVFresh::from_list(pairs.clone());
                    let mut counter = filter_base;
                    let subst = s_fresh.fresh_to_free_avoiding(|n| {
                        let b = counter;
                        counter += n;
                        b
                    });
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
                            if contains_subterm(ft, p) {
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
            // `pairs` are already removeRenamings'd (applied once up front,
            // mirroring HS's `msubstToLSubstVFresh`, Maude/Types.hs:137-146, see line 144).  HS's
            // identity variant therefore arrives EMPTY here, so composeVFresh
            // operates on empty s1_0 and adds renamings for the abstraction
            // subst's range vars (the rule's leaves, all at idx 0 from parser)
            // — its uniform shift collapses them ALL to the SAME fresh idx.
            // THAT's how HS gets `{pkA.5, s.5}` (both at idx 5) for the
            // CHECKSIGN identity variant.
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
            // removeRenamings (post-compose, HS RuleVariants.hs:61-134, see line 74)
            let cleaned = normalised.remove_renamings();
            // restrictVFresh (frees abstrPsCsAs)
            cleaned.restrict(&abstr_frees)
        })
        // HS-faithful: `variantsProtoRule` (RuleVariants.hs:72-76) builds the
        // composed `substs` list with NO post-composition renaming filter — the
        // only filter is `not $ isFreshRedundant vsubst` on the RAW Maude variant
        // (applied above as the H20 pass).  Each composed entry is
        //   `restrictVFresh (frees abstrPsCsAs) $ removeRenamings $
        //      normSubstVFresh' $ composeVFresh vsubst abstractionSubst`
        // and is kept verbatim.  Do NOT re-add a `.filter(|s| !s.is_renaming())`
        // here: it drops composed substs that restrict-down to a pure renaming,
        // which are EXACTLY HS's narrowing variants (breaks foo_eligibility `C_2`,
        // soundness bug — the `exec` exists-trace lemma can no longer narrow).
        .collect();

    if composed_substs.is_empty() {
        return Ok(None);
    }

    // Haskell `simpDisjunction hnd (const (const False)) (Disj substs)`
    // splits into (commonSubst, freshSubsts).  commonSubst is the free
    // substitution part that's common to all variants — applied to the
    // abstracted rule.  freshSubsts is the residual SplitG disjunction.
    //
    // Without this split, action terms like `Verify(m)` get abstracted
    // to `Verify(z)` AND every variant binds `z := m` — so the SplitG
    // is just identity but the rule still carries `Verify(z)`, which
    // matches against ANY Verify(_) action goal causing wrong cases.
    //
    // After splitting, `commonSubst` carries `{z := m}` and the rule's
    // action becomes `Verify(m)` again; the SplitG only carries the
    // RESIDUAL disjuncts that differ between variants.
    // HS-faithful: variantsProtoRule (RuleVariants.hs:61-133, see line 81) calls
    // `simpDisjunction hnd ...` with a Maude handle, which routes through
    // `simp1`'s FULL pipeline including `simpSingleton` (EquationStore.hs:411-417, invoked from simp1 at 381).
    // That pass folds a single-variant disj into the free subst — so the
    // residual returned to `makeRule` is `Nothing` and the variant subst
    // content gets baked into the rule body via commonSubst.  RS's
    // the plain (no-Maude-handle) simplification SKIPS simpSingleton; use the
    // `_with_maude` variant here to match HS.  Without it, e.g.
    // JKL_TS1_2004 Init_2 keeps `z.0 → 'g'^lkR; z.1 → 'g'^(lkI*lkR)` in
    // the residual instead of baking them into the rule's `!Sessk(...)`
    // conclusion — diverging Sessk_reveal source-case numbering downstream.
    let (common_subst, residual) =
        crate::tools::equation_store::EquationStore::simp_disjunction_with_maude(
            composed_substs,
            |_, _| false,
            maude,
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

    // HS-faithful `variantsProtoRule` disjunction selection
    // (RuleVariants.hs:87-90):
    //   (commonSubst, Nothing)        -> makeRule abstrPsCsAs commonSubst trueDisj
    //   (commonSubst, Just freshSubsts) -> makeRule abstrPsCsAs commonSubst freshSubsts
    // where `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:61-133, see line
    // 119).
    //
    // When `simpDisjunction` collapses the variant disjunction to a single
    // case (`residual == Nothing`), HS does NOT drop the variant disjunction
    // — it keeps `[emptySubstVFresh]`, the trivial-but-present SplitG.  That
    // disjunction is later added by `solveRuleConstraints`
    // (Reduction.hs:789-797) via `addRuleVariants` → `addDisj`, which bumps
    // `eqsNextSplitId` by 1 at EVERY `labelNodeId` for such a rule even though
    // `simp`'s `simpSingleton` immediately folds the singleton and
    // `removeSolvedSplitGoals` later deletes the orphaned SplitG (the
    // split-id counter bump persists).  Dropping the trivial
    // disjunction here would skip `add_disj`'s `eqsNextSplitId` bump
    // that HS always performs for rules whose variants collapse to
    // identity, shifting every later `splitEqs(N)` render label by -1
    // (spdm121 `Attack_Responder_Requester_Mode_Switch`: HS
    // `splitEqs(4)` vs RS `splitEqs(3)`).
    //
    // Mirror HS exactly: `Nothing -> trueDisj`, `Just fs -> fs` (the
    // pre-simp `removeRenamings`/`isFreshRedundant` already ran on the
    // composed substs at the `composed_substs` build site, matching
    // RuleVariants.hs:72-76; no additional post-simp renaming/range filter,
    // which HS does not have).
    let final_substs: Vec<LNSubstVFresh> = match residual {
        // `simpDisjunction` returning `Just fs` with `fs` non-empty is HS's
        // `(commonSubst, Just freshSubsts)` arm.  A `Just []` cannot arise
        // from a satisfiable disjunction (an unsatisfiable one is carried as
        // `falseEqConstrConj`, not here); treat the degenerate empty case as
        // the collapse (trueDisj) so we never emit an empty SplitG disj.
        Some(rs) if !rs.is_empty() => rs,
        _ => vec![LNSubstVFresh::empty()],
    };

    // HS `variantsProtoRule` returns the abstracted rule whenever the
    // composed-substs list was non-empty (RuleVariants.hs:79-80 only `mzero`s
    // on an EMPTY composed list — handled earlier via `raw_substs.is_empty()`
    // and the composed-substs build).  With `final_substs` now always
    // non-empty (trueDisj at minimum), the abstracted form is always
    // produced, matching HS's `makeRule` for the collapse case.

    // HS-faithful `renamePrecise` wrap (RuleVariants.hs:61-134, see line 64):
    //   `(`Precise.evalFresh` Precise.nothingUsed) . renamePrecise $ ...`
    //
    // Re-numbers all rule + variant subst LVars using PreciseFresh
    // (per-name counter starting from 0).  Without this, the rule's
    // vars keep the unique idxs assigned by abstrRule (via Maude's
    // global counter), which causes downstream `freshen_rule`'s
    // uniform shift to keep them at DIFFERENT idxs — but HS's
    // renamePrecise collapses ALL rule vars to PER-NAME idxs
    // (typically 0 since each name is unique in the rule).
    //
    // This makes BTreeMap key ordering in apply_eq_store match HS's
    // — all rule keys at idx 0 → sorted by name first → CHECKSIGN
    // variant sort order matches HS for test4/test5.
    //
    let (abstracted_rule, final_substs) =
        rename_precise_rule_with_variants(abstracted_rule, final_substs);

    Ok(Some((abstracted_rule, final_substs)))
}

/// HS-faithful `renamePrecise` (RuleVariants.hs:61-134, see line 78) applied to a protocol
/// rule that has NO reducible-headed sub-terms (so no AC-variant narrowing).
/// `variantsProtoRule` runs `renamePrecise` on EVERY closed rule, which
/// re-indexes each variable to a PER-NAME fresh index — packing distinct-named
/// variables that share no index dependency onto the same low index (e.g. a
/// SAPiC `lock` + `v` become `lock.0` + `v.0`, not `lock.0` + `v.1`).  Returns
/// the repacked rule iff `renamePrecise` actually rewrites at least one var;
/// `None` when the rule is already in per-name precise normal form (so the
/// caller can leave `abstracted_rule` unset and use the rule as-is).
///
/// For these rules the variant disjunction is always the trivial
/// `[emptySubstVFresh]` (empty domain), so repacking the rule body cannot
/// misalign any variant substitution.
pub fn rename_precise_rule_if_changed(rule: &ProtoRuleE) -> Option<ProtoRuleE> {
    if !rule_renames_under_precise(rule) {
        return None;
    }
    let (packed, _substs) =
        rename_precise_rule_with_variants(rule.clone(), vec![LNSubstVFresh::empty()]);
    Some(packed)
}

/// Would HS's `renamePrecise` (per-name fresh indices, RuleVariants.hs:61-134, see line 64)
/// rewrite any of this rule's free vars?  True iff some var's renamePrecise
/// index differs from its original — the realistic trigger being two free
/// vars sharing a name (e.g. `~ltk` and `ltk` → the second becomes `ltk.1`).
/// Walks vars in the SAME order as `rename_precise_rule_with_variants` (the
/// variant disjunction has no keys for the trivial-disjunction case, so it
/// reduces to prems, concs, acts, new_vars).
// var->var precise-rename map; keyed lookup only, never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn rule_renames_under_precise(rule: &ProtoRuleE) -> bool {
    use std::collections::HashMap;
    use tamarin_term::lterm::HasFrees;
    use tamarin_utils::fresh::PreciseFreshState;
    let mut vars: Vec<LVar> = Vec::new();
    {
        let mut collect = |v: &LVar| vars.push(*v);
        for f in rule
            .premises
            .iter()
            .chain(&rule.conclusions)
            .chain(&rule.actions)
        {
            for t in f.terms.iter() {
                t.for_each_free(&mut collect);
            }
        }
        for t in &rule.new_vars {
            t.for_each_free(&mut collect);
        }
    }
    let mut state = PreciseFreshState::nothing_used();
    let mut map: HashMap<LVar, LVar> = HashMap::new();
    for v in &vars {
        if map.contains_key(v) {
            continue;
        }
        let idx = state.fresh_ident(v.name);
        if idx != v.idx {
            return true;
        }
        map.insert(
            *v,
            LVar {
                name: v.name,
                sort: v.sort,
                idx,
            },
        );
    }
    false
}

/// Apply HS-style `renamePrecise` to a rule + its variant disjunction substs.
/// Mirrors HS `Precise.evalFresh (renamePrecise x) Precise.nothingUsed`
/// applied to a `Rule ProtoRuleACInfo`, whose variants live INSIDE info.
///
/// The pair hands the substitutions to the walk first because that is where
/// HS reaches them: `HasFrees (Rule i)` folds `info` ahead of the premises,
/// conclusions, actions and new variables (Theory/Model/Rule.hs:291-306), and
/// `HasFrees ProtoRuleACInfo` (Theory/Model/Rule.hs:503-515) reaches the
/// variant disjunction through it, beside a name, attributes and loop
/// breakers that carry no variables.
///
/// `HasFrees (SubstVFresh n LVar)` (SubstVFresh.hs:196-202) sees the DOMAIN
/// keys alone, in the fold and in the map, so a range term neither draws a
/// per-name index nor gets rewritten.  Walking the range would feed extra
/// names to the precise supply and rewrite variables HS leaves alone, moving
/// downstream variable indices and the AC-sorted variant order (symptom on
/// JKL_TS1_2004: `Sessk_reveal_case_3` against HS's `Sessk_reveal_case_4`).
fn rename_precise_rule_with_variants(
    rule: ProtoRuleE,
    substs: Vec<LNSubstVFresh>,
) -> (ProtoRuleE, Vec<LNSubstVFresh>) {
    let (substs, rule) = tamarin_term::bind::rename_precise((substs, rule));
    (rule, substs)
}

/// `findPos`-style subterm check: returns true if `needle` appears
/// anywhere within `haystack` (including as the whole term).  Mirrors
/// HS's `isJust . findPos` used in `isFreshRedundant`.
fn contains_subterm(needle: &LNTerm, haystack: &LNTerm) -> bool {
    use tamarin_term::term::Term;
    if needle == haystack {
        return true;
    }
    if let Term::App(_, args) = haystack {
        for a in args.iter() {
            if contains_subterm(needle, a) {
                return true;
            }
        }
    }
    false
}

/// WF-only check: mirrors HS `variantsCheck` (Wellformedness.hs:354-372)
/// sub-check `guard (null recomputedVariants)`.  Returns `true` iff
/// `variantsProtoRule hnd rule` would return `Nothing` — i.e. the rule
/// has no non-fresh-redundant variants.
///
/// HS faithfulness: `recomputedVariants` is empty iff
/// `variantsProtoRule` returns `Nothing`, which happens when
/// `convertRule`'s `substs` list (RuleVariants.hs:87-91) is empty after
/// `isFreshRedundant` filtering.
///
/// Two paths lead to empty `substs`:
///
/// 1. **Contradiction (no-reducible) path**: the rule has no reducible-
///    headed sub-terms.  Maude returns only identity/renaming variants,
///    which become `{}` after `removeRenamings`.  `isFreshRedundant {}`
///    fires iff any freshly-introduced term `~v` (from `Fr(~v)`) appears
///    as a sub-term of any non-Fr premise term.  For the canonical case
///    `Fr(~x), In(~x)`: `~x` IS in both `freshlyIntroduced` and
///    `premiseTerms` → all variants redundant → `Nothing`.
///
/// 2. **Reducible path**: the rule has reducible-headed terms.  Maude
///    may return non-renaming variants, but after composition and the
///    full `isFreshRedundant` pipeline all may still be filtered.  This
///    is handled by `abstract_rule_and_variants` returning `Ok(None)`.
///
/// `maude` is only needed for path 2; for path 1 the check is purely
/// syntactic.  The function requires a `MaudeHandle` for completeness.
///
/// When the reducible-path result (`abstract_rule_and_variants(..) == Ok(None)`)
/// is ALREADY known — e.g. `populate_rule_variants` computes it once and
/// records it on the rule's `OpenProtoRule` (`abstracted_rule`/`variant_substs`)
/// — pass it as `reducible_has_no_variants` to skip the redundant Maude
/// `get variants` query.  `populate_rule_variants` sets
/// `abstracted_rule = Some(_)` exactly when `abstract_rule_and_variants`
/// returns `Ok(Some(_))`, so the caller supplies
/// `Some(opr.abstracted_rule.is_none() && opr.variant_substs.is_empty())`.
/// The syntactic (non-reducible) path is always recomputed here — it is
/// cheap and makes no Maude call.
pub fn rule_has_no_variants_for_wf_with(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
    reducible_has_no_variants: Option<bool>,
) -> bool {
    // Path 1: syntactic fresh-redundancy check (no Maude call needed).
    //
    // If the rule has NO reducible-headed sub-terms, the only Maude
    // variant is identity/renaming → collapses to `{}` after
    // `removeRenamings`.  `isFreshRedundant {}` = True iff any
    // Fr-introduced term also appears in a non-Fr premise.
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
        return freshly_introduced
            .iter()
            .any(|ft| premise_terms.iter().any(|p| contains_subterm(ft, p)));
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
    /// `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:119).  The body of
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
