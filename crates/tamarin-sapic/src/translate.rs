// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of the top-level SAPIC `translate` orchestration
//! (`lib/sapic/src/Sapic.hs`) and `gen` (sapic/src/Sapic.hs).
//!
//! For a single top-level process, [`translate`]:
//!   1. annotates it — `toAnProcess`, `propagateNames`, the `_transReport`-gated
//!      `translateTermsReport`, `translateLetDestr`, `annotateSecretChannels`,
//!      the `_stateChannelOpt`-gated `annotatePureStates`, then `annotateLocks`;
//!   2. chains the initial rules `baseInit` → `progressInit` →
//!      `reliableChannelInit` → `reportInit`, each gated on its option;
//!   3. walks the process with `gen`, whose per-node translation is
//!      `progressTrans . reliableChannelTrans . baseTrans` under the same
//!      gates;
//!   4. converts every `AnnotatedRule` to a `ProtoRuleE` via `toRule` and, with
//!      progress on, runs `pathCompression` over the result;
//!   5. builds the restrictions — `baseRestr` (set_in/set_notin, eq/not-eq,
//!      `single_session`, `in_event`, the locking family) then `progressRestr`
//!      and `reliableChannelRestr`.
//!
//! The caller ([`crate::apply::apply_sapic`]) injects the rules + restrictions
//! into the theory, and adds `heuristic: p` when the user set none.

use std::collections::BTreeSet;

use tamarin_term::lterm::LVar;

use tamarin_theory::formula::LNFormula;
use tamarin_theory::restriction::Restriction;
use tamarin_theory::rule::ProtoRuleE;
use tamarin_theory::sapic::{GoodAnnotation, PlainProcess, Process, ProcessPosition, SapicLVar};
use tamarin_utils::prelude_ext::nub;

use tamarin_theory::sapic::ProcessCombinator;

use crate::annotation::{to_annotated, ProcessAnnotation};
use crate::base_translation::{
    base_init, base_trans_action, base_trans_comb, base_trans_null, predicate_restrictions,
    single_session_restriction, state_restrictions, RuleBody,
};
use crate::facts::{to_rule, AnnotatedRule, RulePosition, StateKind, TransFact};
use crate::progress_translation::Progress;

/// Per-translation context for the gated progress / reliable / async wrappers
/// (HS `trans` = `progressTrans . reliableChannelTrans . baseTrans` in
/// `sapic/src/Sapic.hs`).  `progress` is set iff `_transProgress`.
struct TransCtx {
    needs_in_ev_res: bool,
    async_channels: bool,
    trans_reliable: bool,
    progress: Option<Progress>,
}

/// `propagateNames` (Facts.hs): push each node's process-names down to
/// its children so every node carries the names of all its ancestors.
pub(crate) fn propagate_names<A: GoodAnnotation>(
    p: Process<A, SapicLVar>,
) -> Process<A, SapicLVar> {
    fn go<A: GoodAnnotation>(
        prefix: Vec<String>,
        p: Process<A, SapicLVar>,
    ) -> Process<A, SapicLVar> {
        let mut names = prefix;
        names.extend(p.annotation().parsed().process_names.iter().cloned());
        match p {
            Process::Null(ann) => Process::Null(set_names(ann, names)),
            Process::Action(a, ann, body) => {
                let ann2 = set_names(ann, names.clone());
                Process::Action(a, ann2, Box::new(go(names, *body)))
            }
            Process::Comb(c, ann, l, r) => {
                let ann2 = set_names(ann, names.clone());
                Process::Comb(
                    c,
                    ann2,
                    Box::new(go(names.clone(), *l)),
                    Box::new(go(names, *r)),
                )
            }
        }
    }
    go(Vec::new(), p)
}

fn set_names<A: GoodAnnotation>(ann: A, names: Vec<String>) -> A {
    let mut parsed = ann.parsed().clone();
    parsed.process_names = names;
    ann.set_parsed(parsed)
}

/// `mapToAnnotatedRule` (sapic/src/Sapic.hs): tag each rule body with its index.
fn map_to_annotated_rule(
    proc: &Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    bodies: Vec<RuleBody>,
) -> Vec<AnnotatedRule<ProcessAnnotation<LVar>>> {
    let equation_patterns: BTreeSet<_> = proc
        .annotation()
        .let_plan
        .iter()
        .enumerate()
        .flat_map(|(i, stage)| {
            stage
                .alternatives
                .iter()
                .filter_map(move |(pattern, reduct)| {
                    reduct
                        .as_ref()
                        .map(|_| (crate::annotation::let_stage_position(p, i), pattern))
                })
        })
        .collect();
    bodies
        .into_iter()
        .enumerate()
        .map(|(i, (prems, acts, concs, restr))| AnnotatedRule {
            matches_destructor_equation: prems.iter().any(|premise| match premise {
                TransFact::FLet(position, term, _) => {
                    equation_patterns.contains(&(position.clone(), term))
                }
                _ => false,
            }),
            process_name: None,
            process: proc.clone(),
            position: RulePosition::Pos(p.clone()),
            prems,
            acts,
            concs,
            restr,
            index: i,
        })
        .collect()
}

/// `gen` (sapic/src/Sapic.hs): emit each node's rules before its continuations,
/// carrying absolute positions and the variables available on each branch.
/// NDC children share their parent's state position through `substStatePos`.
fn generate_rules(
    ctx: &TransCtx,
    proc: &Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, String> {
    match proc {
        Process::Null(_) => {
            // `trans_null` is the identity wrapper for progress/reliable.
            let bodies = base_trans_null(p, tildex);
            Ok(map_to_annotated_rule(proc, p, bodies))
        }
        Process::Action(ac, ann, body) => {
            let (bodies, tildex2) = trans_action(ctx, ac, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut child_pos = p.clone();
            child_pos.push(1);
            let rest = generate_rules(ctx, body, &child_pos, &tildex2)?;
            here.extend(rest);
            Ok(here)
        }
        // NDC special case (sapic/src/Sapic.hs): the NDC node itself emits NO
        // rule; its two children SHARE the parent's state position.  We
        // translate each child at `p++[1]` / `p++[2]` (so rule names carry the
        // correct position suffix), then rewrite the State premise of EVERY
        // generated rule from the child position back to the parent `p`
        // (`substStatePos`).
        Process::Comb(ProcessCombinator::Ndc, _, left, right) => {
            let mut pl = p.clone();
            pl.push(1);
            let mut pr = p.clone();
            pr.push(2);
            let l = generate_rules(ctx, left, &pl, tildex)?;
            let r = generate_rules(ctx, right, &pr, tildex)?;
            let mut out = subst_state_pos_rules(l, &pl, p);
            out.extend(subst_state_pos_rules(r, &pr, p));
            Ok(out)
        }
        // General combinator (sapic/src/Sapic.hs): emit this node's own rules,
        // then recurse into the left child with `tildex'1` and (if present) the
        // right child with `tildex'2`.
        Process::Comb(c, ann, left, right) => {
            let (bodies, tildex_l, tildex_r) = trans_comb(ctx, c, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut pl = p.clone();
            pl.push(1);
            let msrs_l = generate_rules(ctx, left, &pl, &tildex_l)?;
            here.extend(msrs_l);
            if let Some(tx_r) = tildex_r {
                let mut pr = p.clone();
                pr.push(2);
                let msrs_r = generate_rules(ctx, right, &pr, &tx_r)?;
                here.extend(msrs_r);
            }
            Ok(here)
        }
    }
}

/// `trans_action` = `progressTransAct (reliableChannelTransAct baseTransAction)`
/// (sapic/src/Sapic.hs, applied per node).  Reliable wraps the base; progress wraps
/// the result.
fn trans_action(
    ctx: &TransCtx,
    ac: &tamarin_theory::sapic::SapicAction<SapicLVar>,
    ann: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<(Vec<RuleBody>, BTreeSet<LVar>), String> {
    // reliable channel act: overrides base for 'c'/'r' channels, else base.
    let (mut bodies, mut tx1) = if ctx.trans_reliable {
        match crate::reliable_channel::reliable_channel_trans_act(ac, p, tildex)? {
            Some(res) => res,
            None => base_trans_action(ctx.async_channels, ctx.needs_in_ev_res, ac, ann, p, tildex)?,
        }
    } else {
        base_trans_action(ctx.async_channels, ctx.needs_in_ev_res, ac, ann, p, tildex)?
    };
    if let Some(progress) = &ctx.progress {
        bodies = progress.trans_rules(p, bodies);
        progress.extend_vars(p, &mut tx1);
    }
    Ok((bodies, tx1))
}

/// `trans_comb` = `progressTransComb baseTransComb`.  Reliable channels do NOT
/// modify the combinator translation (HS `reliableChannelTrans` keeps `tComb`).
fn trans_comb(
    ctx: &TransCtx,
    c: &tamarin_theory::sapic::ProcessCombinator<SapicLVar>,
    ann: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<(Vec<RuleBody>, BTreeSet<LVar>, Option<BTreeSet<LVar>>), String> {
    // Under progress, an omitted else is still the terminating process 0.
    // Its failure transition must be available instead of forcing the let
    // to succeed merely to discharge the progress restriction.
    let mut progress_ann;
    let ann = if ctx.progress.is_some() && matches!(c, ProcessCombinator::Let { .. }) {
        progress_ann = ann.clone();
        progress_ann.else_branch = true;
        &progress_ann
    } else {
        ann
    };
    let (mut bodies, mut tx1, mut tx2) = base_trans_comb(c, ann, p, tildex)?;
    if let Some(progress) = &ctx.progress {
        bodies = progress.trans_rules(p, bodies);
        progress.extend_vars(p, &mut tx1);
        if let Some(tx2) = &mut tx2 {
            progress.extend_vars(p, tx2);
        }
    }
    Ok((bodies, tx1, tx2))
}

/// `substStatePos p_old p_new` over a list of generated rules
/// (sapic/src/Sapic.hs): rewrite the position of every NON-semistate `State` PREMISE fact
/// from `p_old` to `p_new` (leaving the actual position `p_old==p++[i]` only in
/// the rule NAME, which was already fixed during `gen`).
fn subst_state_pos_rules(
    rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>>,
    p_old: &[i64],
    p_new: &[i64],
) -> Vec<AnnotatedRule<ProcessAnnotation<LVar>>> {
    rules
        .into_iter()
        .map(|mut r| {
            r.prems = r
                .prems
                .into_iter()
                .map(|f| subst_state_pos_fact(f, p_old, p_new))
                .collect();
            r
        })
        .collect()
}

/// `substStatePos` on a single fact (sapic/src/Sapic.hs):
///   State s p' vs | p' == p_old, not (isSemiState s) = State LState p_new vs
///   otherwise = fact
fn subst_state_pos_fact(f: TransFact, p_old: &[i64], p_new: &[i64]) -> TransFact {
    match f {
        TransFact::State(kind, pos, vs) if pos == p_old && !kind.is_semi_state() => {
            TransFact::State(StateKind::LState, p_new.to_vec(), vs)
        }
        other => other,
    }
}

/// `getLockPositions` / `getUnlockPositions` (Basetranslation.hs): the lock
/// variable of every `Lock` (or, with `unlock`, `Unlock`) action that has
/// `pureState=False` and its `lock`/`unlock` annotation, in `pfoldMap` order.
fn lock_positions(p: &Process<ProcessAnnotation<LVar>, SapicLVar>, unlock: bool) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut out = Vec::new();
    tamarin_theory::sapic::for_each_process(p, &mut |proc| {
        let Process::Action(action, an, _) = proc else {
            return;
        };
        if an.pure_state {
            return;
        }
        let var = match action {
            SapicAction::Lock(_) if !unlock => &an.lock,
            SapicAction::Unlock(_) if unlock => &an.unlock,
            _ => return,
        };
        if let Some(v) = var {
            out.push(v.0);
        }
    });
    out
}

/// The result of translating a single top-level process.
pub(crate) struct Translation {
    /// The generated rules, their embedded `_restrict` formulas in
    /// `info.restrictions` (HS `_preRestriction`, sapic/src/Sapic/Facts.hs).
    pub rules: Vec<ProtoRuleE>,
    pub restrictions: Vec<Restriction>,
}

/// Translation options threaded from the theory (HS `_thyOptions`).  Defaults
/// (all-false) select the core linear pipeline (no progress / reliable / report
/// / state-channel passes).
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct TranslateOptions {
    pub trans_progress: bool,
    pub trans_reliable: bool,
    pub async_channels: bool,
    pub compress_events: bool,
    /// `_transReport` (sapic/src/Sapic.hs): gates
    /// `translateTermsReport` (the `report(t)`→`rep(t, loc)` term rewrite)
    /// and `reportInit` (the fixed
    /// `ReportRule`).  Set from the `locations-report` builtin.
    pub trans_report: bool,
    /// `_stateChannelOpt` (OpenTheory.hs, default False): gates the
    /// pure-state / state-channel optimisation — `annotatePureStates`
    /// (sapic/src/Sapic.hs) and
    /// `setforcedInjectiveFacts {L_PureState, L_CellLocked}`
    /// (sapic/src/Sapic.hs).  Set from
    /// `options: translation-state-optimisation`.
    pub state_channel_opt: bool,
}

/// `translate` (sapic/src/Sapic.hs).  `needs_in_ev_res` is HS
/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`.  `opts` carries the
/// `_transProgress` / `_transReliable` / `_asynchronousChannels` /
/// `_compressEvents` gates.
pub(crate) fn translate(
    plain: &PlainProcess,
    needs_in_ev_res: bool,
    st_rules: &std::collections::BTreeSet<tamarin_term::subterm_rule::CtxtStRule>,
    macros: &[tamarin_theory::theory::LNMacro],
    opts: TranslateOptions,
) -> Result<Translation, String> {
    // The annotation chain, innermost first (sapic/src/Sapic.hs): toAnProcess,
    // propagateNames, translateTermsReport, translateLetDestr,
    // annotateSecretChannels, annotatePureStates — then annotateLocks.
    let an_proc_pre: Process<ProcessAnnotation<LVar>, SapicLVar> =
        propagate_names(to_annotated::<LVar>(plain));
    // `checkOps' (._transReport) translateTermsReport`
    // (sapic/src/Sapic.hs): rewrite
    // `report(t)` terms to `rep(t, loc)` under the in-scope `@location`
    // annotation.
    let an_proc_rep = if opts.trans_report {
        crate::report::translate_terms_report(an_proc_pre)
    } else {
        an_proc_pre
    };
    let an_proc_let = crate::let_destructors::translate_let_destr(macros, st_rules, an_proc_rep)?;
    // Substituting a let can expose a channel name through an escaping alias.
    let an_proc_sec = crate::secret_channels::annotate_secret_channels(an_proc_let);
    // State identifiers and generated-plan binders are final after substitution.
    let an_proc_states = if opts.state_channel_opt {
        crate::states::annotate_pure_states(an_proc_sec)
    } else {
        an_proc_sec
    };
    let an_proc = crate::locks::annotate_locks(an_proc_states)?;

    let progress = if opts.trans_progress {
        Some(Progress::new(&an_proc)?)
    } else {
        None
    };

    // initial rules + initial tildex.  HS chains (right-to-left via `=<<`):
    //   baseInit → progressInit → reliableChannelInit → reportInit
    // i.e. reportInit runs LAST, prepending the `ReportRule` to the front.
    let (mut init_rules, mut init_tx) = base_init(&an_proc);
    if let Some(progress) = &progress {
        (init_rules, init_tx) = progress.init(init_rules, init_tx);
    }
    if opts.trans_reliable {
        (init_rules, init_tx) =
            crate::reliable_channel::reliable_channel_init(&an_proc, init_rules, init_tx);
    }
    if opts.trans_report {
        (init_rules, init_tx) = crate::report::report_init(&an_proc, init_rules, init_tx);
    }

    let ctx = TransCtx {
        needs_in_ev_res,
        async_channels: opts.async_channels,
        trans_reliable: opts.trans_reliable,
        progress,
    };
    // protocol rules
    let proto_rules = generate_rules(&ctx, &an_proc, &Vec::new(), &init_tx)?;

    // `map toRule (initRules ++ protoRule)`, then `pathCompression` under
    // progress (sapic/src/Sapic.hs).  Each rule carries its `_restrict`
    // formulas in `_preRestriction`, which `mergeInfo` (Compression.hs)
    // concatenates when it absorbs a rule.
    let mut all = init_rules;
    all.extend(proto_rules);
    let rules: Vec<ProtoRuleE> = all.into_iter().map(to_rule).collect();
    let rules = if opts.trans_progress {
        crate::compression::path_compression(opts.compress_events, rules)
    } else {
        rules
    };

    // restrictions (baseRestr, Basetranslation.hs), in HS order:
    //   [setIn, setNotIn]   if the process `contains isLookup`
    //                       (NoDelete variants unless it also `contains isDelete`)
    //   [resEq, resNotEq]   if the process `contains isEq`  (a CondEq node)
    //   [resSingleSession]  always (hasAccountabilityLemmaWithControl = True)
    // (locking restrictions are handled separately.)
    let mut restrictions = Vec::new();
    // HS `isLookup`/`isDelete` (ProcessUtils.hs) only count
    // `pureState=False` nodes — a pure-state lookup/delete uses the
    // `L_PureState`/`L_CellLocked` facts and needs NO set_in/set_notin
    // restriction, so both closures carry that guard.
    let is_lookup_non_pure = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> bool {
        matches!(proc, Process::Comb(ProcessCombinator::Lookup(_, _), an, _, _) if !an.pure_state)
    };
    let is_delete_non_pure = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> bool {
        matches!(proc,
            Process::Action(tamarin_theory::sapic::SapicAction::Delete(_), an, _)
                if !an.pure_state)
    };
    if tamarin_theory::sapic::process_contains(&an_proc, is_lookup_non_pure) {
        let has_delete = tamarin_theory::sapic::process_contains(&an_proc, is_delete_non_pure);
        restrictions.extend(state_restrictions(has_delete));
    }
    if tamarin_theory::sapic::process_contains(&an_proc, tamarin_theory::sapic::is_eq) {
        restrictions.extend(predicate_restrictions());
    }
    restrictions.push(single_session_restriction());
    // `addIf needsInEvRes [resInEv]` (Basetranslation.hs) — the in_event
    // restriction, AFTER single_session, when a lemma needs it.
    if needs_in_ev_res {
        restrictions.push(crate::base_translation::in_event_restriction());
    }

    // Locking restrictions (baseRestr, Basetranslation.hs), AFTER the
    // hardcoded restrictions, in HS order:
    //   lockingWithUnlock = map (resLocking True)  (nub  getUnlockPositions)
    //   lockingOnlyLock   = map (resLocking False) (getLockPositions \\ getUnlockPositions)
    let unlock_positions = nub(lock_positions(&an_proc, true));
    let lock_positions = lock_positions(&an_proc, false);
    for v in &unlock_positions {
        restrictions.push(crate::base_translation::res_locking(true, v));
    }
    // `getLockPositions anP \\ getUnlockPositions anP` — list-difference: keep
    // each lock var (in order, with duplicates) NOT present in the unlock set.
    for v in &lock_positions {
        if !unlock_positions.contains(v) {
            restrictions.push(crate::base_translation::res_locking(false, v));
        }
    }

    // HS chains (right-to-left via `=<<`):
    //   baseRestr → progressRestr (if progress) → reliableChannelRestr (if reliable)
    if let Some(progress) = &ctx.progress {
        restrictions = progress.restr(&an_proc, restrictions)?;
    }
    if opts.trans_reliable {
        restrictions = crate::reliable_channel::reliable_channel_restr(&an_proc, restrictions);
    }

    Ok(Translation {
        rules,
        restrictions,
    })
}

// =============================================================================
// needsInEvRes (sapic/src/Sapic.hs)
// =============================================================================

/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`
/// (sapic/src/Sapic.hs): does
/// any of the theory's lemmas fall in the fragment that requires the `in_event`
/// restriction?  Each lemma is classified via `lemma_needs_in_ev_res`.
pub(crate) fn needs_in_ev_res(thy: &tamarin_theory::theory::Theory) -> bool {
    thy.lemmas().any(lemma_needs_in_ev_res)
}

/// `lemmaNeedsInEvRes` (sapic/src/Sapic.hs): classify a lemma by its trace
/// quantifier and the (pos, neg) polarity of its formula.
fn lemma_needs_in_ev_res(lem: &tamarin_theory::theory::Lemma) -> bool {
    use tamarin_theory::theory::TraceQuantifier as TQ;
    let (pos, neg) = is_pos_neg_formula(&lem.formula);
    match (&lem.trace_quantifier, pos, neg) {
        (TQ::AllTraces, _, true) => false,      // L- for all-traces
        (TQ::ExistsTrace, true, _) => false,    // L+ for exists-trace
        (TQ::ExistsTrace, false, true) => true, // L- for exists-trace
        (TQ::AllTraces, true, false) => true,   // L+ for all-traces
        _ => true,                              // not in L- and L+
    }
}

/// `isPosNegFormula` (sapic/src/Sapic.hs): determine whether a formula is in the
/// positive (L+) and/or negative (L-) fragment.  Returns `(isPos, isNeg)`.  The
/// only special case is an `Action` atom on the `K` fact, which is `(True,
/// False)` (a `K(..)@t` action is positive but not negative).
fn is_pos_neg_formula(f: &LNFormula) -> (bool, bool) {
    use tamarin_theory::formula::{Connective, ProtoFormula};
    fn and2(a: (bool, bool), b: (bool, bool)) -> (bool, bool) {
        (a.0 && b.0, a.1 && b.1)
    }
    fn swap(a: (bool, bool)) -> (bool, bool) {
        (a.1, a.0)
    }
    match f {
        ProtoFormula::Tf(_) => (true, true),
        ProtoFormula::Atom(a) => is_pos_neg_atom(a),
        ProtoFormula::Not(p) => swap(is_pos_neg_formula(p)),
        ProtoFormula::Conn(Connective::And | Connective::Or, p, q) => {
            and2(is_pos_neg_formula(p), is_pos_neg_formula(q))
        }
        // `Conn Imp p q -> isPosNegFormula $ Not p .||. q`, i.e. the `Or` of the
        // `Not` case — evaluated directly rather than by rebuilding the
        // desugared formula.
        ProtoFormula::Conn(Connective::Imp, p, q) => {
            and2(swap(is_pos_neg_formula(p)), is_pos_neg_formula(q))
        }
        // `Conn Iff p q -> isPosNegFormula $ p .==>. q .&&. q .==>. p` — NOT
        // the `And` of the two `Imp` cases: `.&&.` is infixl 3 and `.==>.` is
        // infixr 1 (Theory/Model/Formula.hs), so the expression parses
        // as `p .==>. ((q .&&. q) .==>. p)`, whose polarity is
        // `and2(swap(fp), and2(swap(fq), fp))`.  The two differ whenever `fq`
        // is asymmetric (a `K(..)@t` atom in `q`): HS keeps the second
        // component `p1 && q1 && p2`, the symmetric reading zeroes it.
        ProtoFormula::Conn(Connective::Iff, p, q) => {
            let (fp, fq) = (is_pos_neg_formula(p), is_pos_neg_formula(q));
            and2(swap(fp), and2(swap(fq), fp))
        }
        ProtoFormula::Qua(_, _, p) => is_pos_neg_formula(p),
    }
}

/// `isPosNegFormula (Ato (Action _ f))` dispatches on `isActualKFact (factTag
/// f)` (sapic/src/Sapic.hs): an action on a
/// protocol fact named `K` is `(True, False)`; every other atom is
/// `(True, True)`.
fn is_pos_neg_atom(
    a: &tamarin_theory::atom::Atom<tamarin_theory::formula::BLNTerm>,
) -> (bool, bool) {
    use tamarin_theory::atom::ProtoAtom;
    use tamarin_theory::fact::FactTag;
    match a {
        ProtoAtom::Action(_, fact) if matches!(fact.tag, FactTag::Proto(_, "K", _)) => {
            (true, false)
        }
        _ => (true, true),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_theory::sapic::ProcessParsedAnnotation;

    #[test]
    fn only_equation_matches_skip_derivation_checks_through_translation_wrappers() {
        for progress in [false, true] {
            for reliable in [false, true] {
                let options = if progress {
                    "options: translation-progress"
                } else {
                    ""
                };
                let (builtin, input, output) = if reliable {
                    ("builtins: reliable-channel", "in('r',x)", "out('r',y)")
                } else {
                    ("", "in(x)", "out(y)")
                };
                let source = format!(
                    "theory T begin {builtin} {options} \
                     functions: d/1 [destructor], wrap/1 equations: d(wrap(x))=x \
                     process: {input}; let y=d(d(x)) in {output} else event Failed() end"
                );
                let parsed = tamarin_parser::parse_theory(&source, &[]).unwrap();
                let mut theory = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
                crate::apply::apply_sapic(&mut theory, false).unwrap();
                let exempt: Vec<_> = theory
                    .rules()
                    .filter(|rule| rule.rule_e().info.attributes.ignore_deriv_checks)
                    .map(|rule| rule.name().to_string())
                    .collect();
                // Each reduction has its own equation match and subsequent user
                // pattern. Neither user patterns nor any failure arm is exempt.
                assert_eq!(
                    exempt,
                    ["letyddx_1_1", "letyddx_5_1"],
                    "progress={progress}, reliable={reliable}"
                );
            }
        }
    }

    #[test]
    fn identical_equation_and_failure_premises_share_derivation_attributes() {
        for progress in [false, true] {
            let options = if progress {
                "options: translation-progress"
            } else {
                ""
            };
            let source = format!(
                "theory T begin {options} functions: d/0 [destructor], ok/0 \
                 equations: d()=ok() \
                 process: let y=d() in event Seen(y) else event Wrong() end"
            );
            let mut theory = tamarin_theory::elaborate::elaborate(
                &tamarin_parser::parse_theory(&source, &[]).unwrap(),
            )
            .unwrap();
            crate::apply::apply_sapic(&mut theory, false).unwrap();
            let exempt: Vec<_> = theory
                .rules()
                .filter(|rule| rule.rule_e().info.attributes.ignore_deriv_checks)
                .map(|rule| rule.name().to_string())
                .collect();
            assert_eq!(exempt, ["letyd_1_", "letyd_2_"], "progress={progress}");
        }
    }

    #[test]
    fn progress_preserves_failure_of_let_with_omitted_else() {
        for progress in [false, true] {
            let option = if progress {
                "options: translation-progress"
            } else {
                ""
            };
            let source = format!(
                "theory T begin {option} process: in(x); let <a,b> = x in event A(a,b) end"
            );
            let mut theory = tamarin_theory::elaborate::elaborate(
                &tamarin_parser::parse_theory(&source, &[]).unwrap(),
            )
            .unwrap();
            crate::apply::apply_sapic(&mut theory, false).unwrap();
            assert_eq!(
                theory
                    .restrictions()
                    .any(|r| r.name.starts_with("Restr_let")),
                progress
            );
        }
    }

    #[test]
    fn propagate_names_preserves_location() {
        // Propagated process names leave the other annotation fields intact.
        let location = tamarin_term::lterm::pub_term("site");
        let ann = ProcessParsedAnnotation {
            process_names: vec!["P".into()],
            location: Some(location.clone()),
            ..ProcessParsedAnnotation::empty()
        };
        let process: PlainProcess = Process::Null(ann);

        let Process::Null(propagated) = propagate_names(process) else {
            unreachable!()
        };
        assert_eq!(propagated.process_names, ["P"]);
        assert_eq!(propagated.location, Some(location));
    }

    /// `name()@#i` as the lemma formula holds it: a `ProtoFact` action atom
    /// over a free node variable.
    fn action_atom(name: &str) -> LNFormula {
        use tamarin_term::lterm::BVar;
        use tamarin_term::vterm::var_term;
        use tamarin_theory::atom::ProtoAtom;
        use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
        use tamarin_theory::formula::ProtoFormula;
        let i = var_term(BVar::Free(LVar::new("i", LSort::Node, 0)));
        ProtoFormula::Atom(ProtoAtom::Action(
            i,
            Fact::new(
                FactTag::Proto(
                    Multiplicity::Linear,
                    tamarin_term::intern::intern_str(name),
                    0,
                ),
                vec![],
            ),
        ))
    }

    /// `Conn Iff p q -> isPosNegFormula $ p .==>. q .&&. q .==>. p`
    /// (sapic/src/Sapic.hs) parses as `p .==>. ((q .&&. q) .==>. p)` (`.&&.` infixl 3
    /// binds tighter than `.==>.` infixr 1, Theory/Model/Formula.hs),
    /// so with `p` symmetric and `q` a `K` atom the polarity is `(F, T)` — the
    /// negative component survives.  The symmetric `(p ==> q) && (q ==> p)`
    /// reading yields `(F, F)` and wrongly makes an all-traces lemma need the
    /// `in_event` restriction.
    #[test]
    fn iff_polarity_follows_hs_fixity_parse() {
        let iff = action_atom("A").iff(action_atom("K"));
        assert_eq!(is_pos_neg_formula(&iff), (false, true));

        let lem = tamarin_theory::theory::Lemma {
            heuristic_in_file: None,
            name: "weird".into(),
            attributes: vec![],
            trace_quantifier: tamarin_theory::theory::TraceQuantifier::AllTraces,
            formula: iff,
            original_formula: None,
            proof: None,
            plaintext: String::new(),
        };
        // HS: (AllTraces, (_, True)) -> False — no in_event restriction.
        assert!(!lemma_needs_in_ev_res(&lem));
    }
}
