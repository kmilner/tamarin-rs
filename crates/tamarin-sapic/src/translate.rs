// Currently GPL 3.0 until granted permission by the following authors:
//   arcz, rkunnema, kevinmorio, yavivanov, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic.hs, lib/sapic/src/Sapic/Basetranslation.hs,
//   lib/sapic/src/Sapic/Facts.hs, lib/sapic/src/Sapic/ProcessUtils.hs,
//   lib/theory/src/OpenTheory.hs

//! Port of the top-level SAPIC `translate` orchestration
//! (`lib/sapic/src/Sapic.hs:45-101`) and `gen` (Sapic.hs:112-153), restricted
//! to the CORE LINEAR pipeline (no progress / reliable / report / states /
//! locks / compression passes).
//!
//! For a single top-level process, `translate`:
//!   1. annotates it (`toAnProcess` + `propagateNames`),
//!   2. computes the initial `Init` rule via `baseInit`,
//!   3. walks the process with `gen` (base translation per node),
//!   4. converts every `AnnotatedRule` to a `ProtoRuleE` via `toRule`,
//!   5. emits the always-on `single_session` restriction (`baseRestr`).
//!
//! The caller (run.rs) injects the rules + restriction into the theory, sets
//! `is_sapic`, and adds `heuristic: p` if the user didn't set one.

use std::collections::BTreeSet;

use tamarin_term::lterm::LVar;

use tamarin_theory::rule::ProtoRuleE;
use tamarin_theory::sapic::{
    GoodAnnotation, PlainProcess, Process, SapicLVar, ProcessPosition,
};

use tamarin_theory::sapic::ProcessCombinator;

use crate::annotation::{to_annotated, ProcessAnnotation};
use crate::base_translation::{
    base_init, base_trans_action, base_trans_comb, base_trans_null, predicate_restrictions,
    single_session_restriction, state_restrictions, RuleBody,
};
use crate::facts::{to_rule, AnnotatedRule, RulePosition, StateKind, TransFact};

type Pos = Vec<i64>;
type PosSet = BTreeSet<Vec<i64>>;

/// Per-translation context for the gated progress / reliable / async wrappers
/// (HS `trans` = `progressTrans . reliableChannelTrans . baseTrans` in
/// `Sapic.hs:98-100`).  The progress function domain / inverse are computed once
/// (HS recomputes `pfFrom`/`pfInv` per node; identical result, computed once
/// here for speed).
struct TransCtx {
    needs_in_ev_res: bool,
    async_channels: bool,
    trans_progress: bool,
    trans_reliable: bool,
    /// progress-function domain `pfFrom anP` (only used when `trans_progress`).
    dom_pf: PosSet,
    /// progress-function inverse `pfInv anP` (only used when `trans_progress`).
    inv_pf: Option<Box<dyn Fn(&[i64]) -> Option<Pos>>>,
}

/// `propagateNames` (Facts.hs:301-313): push each node's process-names down to
/// its children so every node carries the names of all its ancestors.
pub fn propagate_names<A: GoodAnnotation + Clone>(p: Process<A, SapicLVar>) -> Process<A, SapicLVar> {
    fn go<A: GoodAnnotation + Clone>(
        prefix: Vec<String>,
        p: Process<A, SapicLVar>,
    ) -> Process<A, SapicLVar> {
        match p {
            Process::Null(ann) => {
                let mut names = prefix;
                names.extend(ann.parsed().process_names.clone());
                Process::Null(set_names(ann, names))
            }
            Process::Action(a, ann, body) => {
                let mut names = prefix;
                names.extend(ann.parsed().process_names.clone());
                let ann2 = set_names(ann, names.clone());
                Process::Action(a, ann2, Box::new(go(names, *body)))
            }
            Process::Comb(c, ann, l, r) => {
                let mut names = prefix;
                names.extend(ann.parsed().process_names.clone());
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

/// `processAt` over the annotated process (theory-side helper is generic).
fn process_at<'a>(
    p: &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
    pos: &[i64],
) -> Option<&'a Process<ProcessAnnotation<LVar>, SapicLVar>> {
    if pos.is_empty() {
        return Some(p);
    }
    match (p, pos[0]) {
        (Process::Null(_), _) => None,
        (Process::Action(_, _, body), 1) => process_at(body, &pos[1..]),
        (Process::Comb(_, _, l, _), 1) => process_at(l, &pos[1..]),
        (Process::Comb(_, _, _, r), 2) => process_at(r, &pos[1..]),
        _ => None,
    }
}

/// `mapToAnnotatedRule` (Sapic.hs:145-147): tag each rule body with its index.
fn map_to_annotated_rule(
    proc: &Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    bodies: Vec<RuleBody>,
) -> Vec<AnnotatedRule<ProcessAnnotation<LVar>>> {
    bodies
        .into_iter()
        .enumerate()
        .map(|(i, (prems, acts, concs, restr))| AnnotatedRule {
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

/// `gen` (Sapic.hs:112-153).  Handles `Null`, `Action` (incl. the `Rep`
/// replication action), and the `Comb` combinators in scope — `Parallel`,
/// `NDC` (with the `substStatePos` shared-position rewrite), and `CondEq`.
/// `Cond`-with-a-formula / `Lookup` / `Let` are rejected in `base_trans_comb`.
fn gen(
    ctx: &TransCtx,
    an_proc: &Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, String> {
    let proc = process_at(an_proc, p)
        .ok_or_else(|| format!("gen: invalid position {p:?}"))?;
    match proc {
        Process::Null(_) => {
            // `trans_null` is the identity wrapper for progress/reliable.
            let bodies = base_trans_null(p, tildex);
            Ok(map_to_annotated_rule(proc, p, bodies))
        }
        Process::Action(ac, ann, _) => {
            let (bodies, tildex2) = trans_action(ctx, ac, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut child_pos = p.clone();
            child_pos.push(1);
            let rest = gen(ctx, an_proc, &child_pos, &tildex2)?;
            here.extend(rest);
            Ok(here)
        }
        // NDC special case (Sapic.hs:123-127): the NDC node itself emits NO
        // rule; its two children SHARE the parent's state position.  We
        // translate each child at `p++[1]` / `p++[2]` (so rule names carry the
        // correct position suffix), then rewrite the State premise of EVERY
        // generated rule from the child position back to the parent `p`
        // (`substStatePos`).
        Process::Comb(ProcessCombinator::Ndc, _, _, _) => {
            let mut pl = p.clone();
            pl.push(1);
            let mut pr = p.clone();
            pr.push(2);
            let l = gen(ctx, an_proc, &pl, tildex)?;
            let r = gen(ctx, an_proc, &pr, tildex)?;
            let mut out = subst_state_pos_rules(l, &pl, p);
            out.extend(subst_state_pos_rules(r, &pr, p));
            Ok(out)
        }
        // General combinator (Sapic.hs:128-134): emit this node's own rules,
        // then recurse into the left child with `tildex'1` and (if present) the
        // right child with `tildex'2`.
        Process::Comb(c, ann, _, _) => {
            let (bodies, tildex_l, tildex_r) = trans_comb(ctx, c, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut pl = p.clone();
            pl.push(1);
            let msrs_l = gen(ctx, an_proc, &pl, &tildex_l)?;
            here.extend(msrs_l);
            if let Some(tx_r) = tildex_r {
                let mut pr = p.clone();
                pr.push(2);
                let msrs_r = gen(ctx, an_proc, &pr, &tx_r)?;
                here.extend(msrs_r);
            }
            Ok(here)
        }
    }
}

/// `trans_action` = `progressTransAct (reliableChannelTransAct baseTransAction)`
/// (Sapic.hs:98-100, applied per node).  Reliable wraps the base; progress wraps
/// the result.
fn trans_action(
    ctx: &TransCtx,
    ac: &tamarin_theory::sapic::SapicAction<SapicLVar>,
    ann: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<(Vec<RuleBody>, BTreeSet<LVar>), String> {
    // reliable channel act: overrides base for 'c'/'r' channels, else base.
    let (bodies, tx1) = if ctx.trans_reliable {
        match crate::reliable_channel::reliable_channel_trans_act(ac, p, tildex)? {
            Some(res) => res,
            None => base_trans_action(ctx.async_channels, ctx.needs_in_ev_res, ac, ann, p, tildex)?,
        }
    } else {
        base_trans_action(ctx.async_channels, ctx.needs_in_ev_res, ac, ann, p, tildex)?
    };
    if ctx.trans_progress {
        let inv = ctx.inv_pf.as_ref().expect("inv_pf set when trans_progress");
        Ok(crate::progress_translation::progress_trans_act(
            &ctx.dom_pf,
            inv,
            p,
            bodies,
            tx1,
        ))
    } else {
        Ok((bodies, tx1))
    }
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
    let (bodies, tx1, tx2) = base_trans_comb(c, ann, p, tildex)?;
    if ctx.trans_progress {
        let inv = ctx.inv_pf.as_ref().expect("inv_pf set when trans_progress");
        Ok(crate::progress_translation::progress_trans_comb(
            &ctx.dom_pf,
            inv,
            p,
            bodies,
            tx1,
            tx2,
        ))
    } else {
        Ok((bodies, tx1, tx2))
    }
}

/// `substStatePos p_old p_new` over a list of generated rules (Sapic.hs:112-153, see line 124,
/// 140-144): rewrite the position of every NON-semistate `State` PREMISE fact
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

/// `substStatePos` on a single fact (Sapic.hs:142-144):
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

/// `getLockPositions = pfoldMap getLock` (Basetranslation.hs:449-479, see line 473,478): the lock
/// variables of every `Lock` action with `pureState=False` and a `lock`
/// annotation, in `pfoldMap` order, NOT deduplicated.
fn get_lock_positions(
    p: &Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut get_lock = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> Vec<LVar> {
        if let Process::Action(SapicAction::Lock(_), an, _) = proc {
            if !an.pure_state {
                if let Some(v) = &an.lock {
                    return vec![v.0.clone()];
                }
            }
        }
        vec![]
    };
    tamarin_theory::sapic::pfold_map(p, &mut get_lock)
}

/// `nub $ getUnlockPositions` (Basetranslation.hs:449-479, see line 463): the lock variables of
/// every `Unlock` action with `pureState=False` and an `unlock` annotation, in
/// `pfoldMap` order, first-occurrence deduplicated (HS `List.nub`).
fn get_unlock_positions(
    p: &Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut get_unlock = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> Vec<LVar> {
        if let Process::Action(SapicAction::Unlock(_), an, _) = proc {
            if !an.pure_state {
                if let Some(v) = &an.unlock {
                    return vec![v.0.clone()];
                }
            }
        }
        vec![]
    };
    let raw = tamarin_theory::sapic::pfold_map(p, &mut get_unlock);
    // `List.nub` — keep first occurrence, preserve order.
    let mut seen: Vec<LVar> = Vec::new();
    for v in raw {
        if !seen.contains(&v) {
            seen.push(v);
        }
    }
    seen
}

/// The result of translating a single top-level process.
pub struct Translation {
    /// The generated rules, each paired with its embedded `_restrict` formulas
    /// (parser-AST; non-empty only for `if <formula>` arms).  HS attaches these
    /// as the rule's `_preRestriction`; the RS port keeps them alongside the
    /// elaborated rule so `apply_sapic` can run the `_restrict` expansion
    /// (`lift_rule_restrictions`, HS `liftedAddProtoRule`) over both theories.
    pub rules: Vec<(ProtoRuleE, Vec<tamarin_parser::ast::Formula>)>,
    pub restrictions: Vec<tamarin_parser::ast::Restriction>,
}

/// Translation options threaded from the theory (HS `_thyOptions`).  Defaults
/// (all-false) select the core linear pipeline (no progress / reliable / report
/// / state-channel passes).
#[derive(Debug, Clone, Copy, Default)]
pub struct TranslateOptions {
    pub trans_progress: bool,
    pub trans_reliable: bool,
    pub async_channels: bool,
    pub compress_events: bool,
    /// `_transReport` (Sapic.hs:45-101, see line 56, 64): gates `translateTermsReport` (the
    /// `report(t)`→`rep(t, loc)` term rewrite) and `reportInit` (the fixed
    /// `ReportRule`).  Set from the `locations-report` builtin.
    pub trans_report: bool,
    /// `_stateChannelOpt` (OpenTheory.hs:546-547, see line 547, default False): gates the
    /// pure-state / state-channel optimisation — `annotatePureStates`
    /// (Sapic.hs:45-101, see line 57) and `setforcedInjectiveFacts {L_PureState, L_CellLocked}`
    /// (Sapic.hs:45-101, see line 84).  Set from `options: translation-state-optimisation`.
    pub state_channel_opt: bool,
}

/// `translate` (Sapic.hs:45-101).  `needs_in_ev_res` is HS
/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`.  `opts` carries the
/// `_transProgress` / `_transReliable` / `_asynchronousChannels` /
/// `_compressEvents` gates.
pub fn translate(
    plain: &PlainProcess,
    needs_in_ev_res: bool,
    st_rules: &std::collections::BTreeSet<tamarin_term::subterm_rule::CtxtStRule>,
    opts: TranslateOptions,
) -> Result<Translation, String> {
    // annotate: toAnProcess + propagateNames + annotateSecretChannels +
    //   translateLetDestr + annotateLocks (Sapic.hs:54-61).  The pure-state /
    //   report passes are gated off by default (pure-state needs
    //   `--translation-state-optimisation`).  `translateLetDestr` runs
    //   AFTER annotateSecretChannels and BEFORE annotateLocks, eliminating
    //   var-RHS `let`s and annotating destructor / kept `let`s.
    let an_proc_pre: Process<ProcessAnnotation<LVar>, SapicLVar> =
        propagate_names(to_annotated::<LVar>(plain.clone()));
    // annotateSecretChannels (Sapic.hs:45-101, see line 58): attach `secret_channel` to every
    // ChIn/ChOut whose channel is an always-secret fresh variable.  Runs AFTER
    // propagateNames and BEFORE translateLetDestr.  (annotatePureStates is gated
    // off by default — it needs `--translation-state-optimisation`.)
    let an_proc_sec = crate::secret_channels::annotate_secret_channels(an_proc_pre);
    // `checkOps' (._stateChannelOpt) annotatePureStates` (Sapic.hs:45-101, see line 57): the
    // pure-state / state-channel optimisation.  Runs AFTER annotateSecretChannels
    // and BEFORE translateTermsReport / translateLetDestr.  Gated off by default
    // (needs `options: translation-state-optimisation`).
    let an_proc_states = if opts.state_channel_opt {
        crate::states::annotate_pure_states(an_proc_sec)
    } else {
        an_proc_sec
    };
    // `checkOps' (._transReport) translateTermsReport` (Sapic.hs:45-101, see line 56): rewrite
    // `report(t)` terms to `rep(t, loc)` under the in-scope `@location`
    // annotation.  Runs AFTER annotatePureStates, BEFORE translateLetDestr.
    let an_proc_rep = if opts.trans_report {
        crate::report::translate_terms_report(an_proc_states)
    } else {
        an_proc_states
    };
    let an_proc_let = crate::let_destructors::translate_let_destr(st_rules, an_proc_rep);
    let an_proc = crate::locks::annotate_locks(an_proc_let)?;

    // Build the translation context (gated progress/reliable/async wrappers).
    // The progress-function domain / inverse are computed once (HS recomputes
    // them per node; same result).
    let (dom_pf, inv_pf): (PosSet, Option<Box<dyn Fn(&[i64]) -> Option<Pos>>>) =
        if opts.trans_progress {
            let dom = crate::progress_function::pf_from(&an_proc)?;
            let inv = crate::progress_function::pf_inv(&an_proc)?;
            (dom, Some(Box::new(inv)))
        } else {
            (PosSet::new(), None)
        };
    let ctx = TransCtx {
        needs_in_ev_res,
        async_channels: opts.async_channels,
        trans_progress: opts.trans_progress,
        trans_reliable: opts.trans_reliable,
        dom_pf,
        inv_pf,
    };

    // initial rules + initial tildex.  HS chains (right-to-left via `=<<`):
    //   baseInit → progressInit → reliableChannelInit → reportInit
    // i.e. reportInit runs LAST, prepending the `ReportRule` to the front.
    let (mut init_rules, mut init_tx) = base_init(&an_proc);
    if opts.trans_progress {
        let (r, t) = crate::progress_translation::progress_init(&an_proc, init_rules, init_tx)?;
        init_rules = r;
        init_tx = t;
    }
    if opts.trans_reliable {
        let (r, t) =
            crate::reliable_channel::reliable_channel_init(&an_proc, init_rules, init_tx);
        init_rules = r;
        init_tx = t;
    }
    if opts.trans_report {
        let (r, t) = crate::report::report_init(&an_proc, init_rules, init_tx);
        init_rules = r;
        init_tx = t;
    }

    // protocol rules
    let proto_rules = gen(&ctx, &an_proc, &Vec::new(), &init_tx)?;

    // toRule over (initRules ++ protoRules); HS then applies pathCompression
    // (gated on progress) over the ELABORATED rules, BEFORE pairing with the
    // per-rule embedded restrictions.  Path compression operates on
    // `Rule ProtoRuleEInfo` and never touches the embedded `_restrict` formulas
    // (those rules — `Cond` / `let`-else arms — carry no `State_( )`-reachable
    // silent shape that compresses; their `restr` is preserved per-rule below).
    let mut all = init_rules;
    all.extend(proto_rules);
    // The embedded restriction formulas, keyed by rule NAME (compression keeps
    // the first rule's name and never merges `_restrict`-bearing arms — see the
    // `isLetFact`/no-compress guards), so re-pairing by name is faithful.
    // restriction-by-name re-pair map; keyed lookup only, never iterated;
    // std kept (byte-inert) — iteration order never reaches output.
    #[allow(clippy::disallowed_types)]
    let restr_by_name: std::collections::HashMap<String, Vec<tamarin_parser::ast::Formula>> = all
        .iter()
        .filter(|r| !r.restr.is_empty())
        .map(|r| (crate::facts::rule_name(r), r.restr.clone()))
        .collect();
    let elaborated: Vec<ProtoRuleE> = all.iter().map(to_rule).collect();
    let elaborated = if opts.trans_progress {
        crate::compression::path_compression(opts.compress_events, elaborated)
    } else {
        elaborated
    };
    let rules: Vec<(ProtoRuleE, Vec<tamarin_parser::ast::Formula>)> = elaborated
        .into_iter()
        .map(|r| {
            let name = match &r.info.name {
                tamarin_theory::rule::ProtoRuleName::Stand(n) => n.to_string(),
                tamarin_theory::rule::ProtoRuleName::Fresh => "Fresh".to_string(),
            };
            let restr = restr_by_name.get(&name).cloned().unwrap_or_default();
            (r, restr)
        })
        .collect();

    // restrictions (baseRestr, Basetranslation.hs:449-468), in HS order:
    //   [setIn, setNotIn]   if the process `contains isLookup`
    //                       (NoDelete variants unless it also `contains isDelete`)
    //   [resEq, resNotEq]   if the process `contains isEq`  (a CondEq node)
    //   [resSingleSession]  always (hasAccountabilityLemmaWithControl = True)
    // (locking restrictions are handled separately.)
    let mut restrictions = Vec::new();
    // HS `isLookup`/`isDelete` (ProcessUtils.hs:46-52) only count
    // `pureState=False` nodes — a pure-state lookup/delete uses the
    // `L_PureState`/`L_CellLocked` facts and needs NO set_in/set_notin
    // restriction.  (`is_lookup`/`is_delete` in tamarin_theory are generic
    // over the annotation, so we inline the `pure_state` guard here.)
    let is_lookup_non_pure = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> bool {
        matches!(proc, Process::Comb(ProcessCombinator::Lookup(_, _), an, _, _) if !an.pure_state)
    };
    let is_delete_non_pure = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> bool {
        matches!(proc,
            Process::Action(tamarin_theory::sapic::SapicAction::Delete(_), an, _)
                if !an.pure_state)
    };
    if tamarin_theory::sapic::process_contains(&an_proc, is_lookup_non_pure) {
        let has_delete =
            tamarin_theory::sapic::process_contains(&an_proc, is_delete_non_pure);
        restrictions.extend(state_restrictions(has_delete));
    }
    if tamarin_theory::sapic::process_contains(&an_proc, tamarin_theory::sapic::is_eq) {
        restrictions.extend(predicate_restrictions());
    }
    restrictions.push(single_session_restriction());
    // `addIf needsInEvRes [resInEv]` (Basetranslation.hs:449-479, see line 460) — the in_event
    // restriction, AFTER single_session, when a lemma needs it.
    if needs_in_ev_res {
        restrictions.push(crate::base_translation::in_event_restriction());
    }

    // Locking restrictions (baseRestr, Basetranslation.hs:463-468), AFTER the
    // hardcoded restrictions, in HS order:
    //   lockingWithUnlock = map (resLocking True)  (nub  getUnlockPositions)
    //   lockingOnlyLock   = map (resLocking False) (getLockPositions \\ getUnlockPositions)
    let unlock_positions = get_unlock_positions(&an_proc); // nub'd
    let lock_positions = get_lock_positions(&an_proc); // NOT nub'd (HS `getLockPositions`)
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
    if opts.trans_progress {
        restrictions = crate::progress_translation::progress_restr(&an_proc, restrictions)?;
    }
    if opts.trans_reliable {
        restrictions =
            crate::reliable_channel::reliable_channel_restr(&an_proc, restrictions);
    }

    Ok(Translation { rules, restrictions })
}

// =============================================================================
// needsInEvRes (Sapic.hs:45-101, see line 101, 156-181)
// =============================================================================

/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)` (Sapic.hs:45-101, see line 101): does
/// any of the theory's lemmas fall in the fragment that requires the `in_event`
/// restriction?  Each lemma is classified via `lemma_needs_in_ev_res`.
pub fn needs_in_ev_res(lemmas: &[tamarin_parser::ast::Lemma]) -> bool {
    lemmas.iter().any(lemma_needs_in_ev_res)
}

/// `lemmaNeedsInEvRes` (Sapic.hs:175-181): classify a lemma by its trace
/// quantifier and the (pos, neg) polarity of its formula.
fn lemma_needs_in_ev_res(lem: &tamarin_parser::ast::Lemma) -> bool {
    use tamarin_parser::ast::TraceQuantifier as TQ;
    let (pos, neg) = is_pos_neg_formula(&lem.formula);
    match (&lem.trace_quantifier, pos, neg) {
        (TQ::AllTraces, _, true) => false,   // L- for all-traces
        (TQ::ExistsTrace, true, _) => false, // L+ for exists-trace
        (TQ::ExistsTrace, false, true) => true, // L- for exists-trace
        (TQ::AllTraces, true, false) => true,   // L+ for all-traces
        _ => true,                               // not in L- and L+
    }
}

/// `isPosNegFormula` (Sapic.hs:156-169): determine whether a formula is in the
/// positive (L+) and/or negative (L-) fragment.  Returns `(isPos, isNeg)`.  The
/// only special case is an `Action` atom on the `K` fact, which is `(True,
/// False)` (a `K(..)@t` action is positive but not negative).
fn is_pos_neg_formula(f: &tamarin_parser::ast::Formula) -> (bool, bool) {
    use tamarin_parser::ast::Formula::*;
    fn and2(a: (bool, bool), b: (bool, bool)) -> (bool, bool) {
        (a.0 && b.0, a.1 && b.1)
    }
    fn swap(a: (bool, bool)) -> (bool, bool) {
        (a.1, a.0)
    }
    match f {
        True | False => (true, true),
        Atom(a) => is_pos_neg_atom(a),
        Not(p) => swap(is_pos_neg_formula(p)),
        And(p, q) | Or(p, q) => and2(is_pos_neg_formula(p), is_pos_neg_formula(q)),
        // `Conn Imp p q -> isPosNegFormula $ Not p .||. q`.
        Implies(p, q) => {
            let not_p = Not(Box::new((**p).clone()));
            let disj = Or(Box::new(not_p), Box::new((**q).clone()));
            is_pos_neg_formula(&disj)
        }
        // `Conn Iff p q -> isPosNegFormula $ p .==>. q .&&. q .==>. p`.
        Iff(p, q) => {
            let pq = Implies(Box::new((**p).clone()), Box::new((**q).clone()));
            let qp = Implies(Box::new((**q).clone()), Box::new((**p).clone()));
            let conj = And(Box::new(pq), Box::new(qp));
            is_pos_neg_formula(&conj)
        }
        Forall(_, p) | Exists(_, p) => is_pos_neg_formula(p),
    }
}

/// `isPosNegFormula (Ato (Action _ f))` dispatches on `isActualKFact (factTag
/// f)` (Sapic.hs:156-172, see line 159, 167-169): a `K`-fact action is `(True, False)`; every
/// other atom is `(True, True)`.
fn is_pos_neg_atom(a: &tamarin_parser::ast::Atom) -> (bool, bool) {
    use tamarin_parser::ast::Atom;
    match a {
        Atom::Action(fact, _) if fact.name == "K" => (true, false),
        _ => (true, true),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::convert::convert_process;
    use crate::typing::type_and_rename_process;
    use tamarin_parser::ast as p;

    fn typing2_process() -> p::Process {
        let xspec = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: Some("lol".into()),
        };
        let xref = p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        let ffx = p::Term::App(
            "f".into(),
            vec![p::Term::App("f".into(), vec![xref.clone()])],
        );
        p::Process::Action {
            action: p::SapicAction::New(xspec),
            body: Box::new(p::Process::Action {
                action: p::SapicAction::Event(p::Fact {
                    persistent: false,
                    name: "Test".into(),
                    args: vec![xref],
                    annotations: vec![],
                }),
                body: Box::new(p::Process::Action {
                    action: p::SapicAction::ChOut { chan: None, msg: ffx },
                    body: Box::new(p::Process::Null),
                }),
            }),
        }
    }

    #[test]
    fn translate_typing2_produces_five_rules() {
        let plain = convert_process(&typing2_process()).unwrap();
        // No function-typing needed for the rule-count check; type over an
        // empty signature (defaults all funs).
        let sig = tamarin_term::maude_sig::MaudeSig::default();
        let typed = type_and_rename_process(&sig, &[], &plain).unwrap();
        let st_rules = std::collections::BTreeSet::new();
        let tr = translate(&typed, false, &st_rules, TranslateOptions::default()).unwrap();
        // Init + new + event + out + null = 5 rules.
        assert_eq!(tr.rules.len(), 5);
        assert_eq!(tr.restrictions.len(), 1);
        // First rule is "Init".
        assert_eq!(tr.rules[0].0.info.name, tamarin_theory::rule::ProtoRuleName::Stand("Init"));
    }
}
