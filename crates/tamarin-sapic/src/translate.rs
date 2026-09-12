// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of the top-level SAPIC `translate` orchestration
//! (`lib/sapic/src/Sapic.hs:45-101`) and `gen` (sapic/src/Sapic.hs:112-153).
//!
//! For a single top-level process, [`translate`]:
//!   1. annotates it — `toAnProcess`, `propagateNames`,
//!      `annotateSecretChannels`, then the `_stateChannelOpt`-gated
//!      `annotatePureStates` and `_transReport`-gated `translateTermsReport`,
//!      then `translateLetDestr` and `annotateLocks`;
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

use tamarin_theory::formula::{LNFormula, SyntacticLNFormula};
use tamarin_theory::restriction::Restriction;
use tamarin_theory::rule::ProtoRuleE;
use tamarin_theory::sapic::{GoodAnnotation, PlainProcess, Process, ProcessPosition, SapicLVar};
use tamarin_utils::prelude_ext::nub_on;

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
/// `sapic/src/Sapic.hs:98-100`).  The progress function domain / inverse are computed once
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

/// `propagateNames` (Facts.hs:327-341): push each node's process-names down to
/// its children so every node carries the names of all its ancestors.
pub(crate) fn propagate_names<A: GoodAnnotation + Clone>(
    mut p: Process<A, SapicLVar>,
) -> Process<A, SapicLVar> {
    crate::process_walk::walk_mut(&mut p, Vec::<String>::new(), |node, names| {
        let ann = match node {
            Process::Null(ann) | Process::Action(_, ann, _) | Process::Comb(_, ann, _, _) => ann,
        };
        names.extend(ann.parsed().process_names.iter().cloned());
        *ann = set_names(ann.clone(), names.clone());
        Ok::<_, std::convert::Infallible>(true)
    })
    .unwrap();
    p
}

fn set_names<A: GoodAnnotation>(ann: A, names: Vec<String>) -> A {
    let mut parsed = ann.parsed().clone();
    parsed.process_names = names;
    ann.set_parsed(parsed)
}

/// `mapToAnnotatedRule` (sapic/src/Sapic.hs:149-150): tag each rule body with its index.
fn map_to_annotated_rule<'a>(
    proc: &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    bodies: Vec<RuleBody>,
) -> Vec<AnnotatedRule<'a, ProcessAnnotation<LVar>>> {
    bodies
        .into_iter()
        .enumerate()
        .map(|(i, (prems, acts, concs, restr))| AnnotatedRule {
            process_name: None,
            process: proc,
            position: RulePosition::Pos(p.clone()),
            prems,
            acts,
            concs,
            restr,
            index: i,
        })
        .collect()
}

/// `gen` (sapic/src/Sapic.hs:112-153).  Handles `Null`, `Action` (incl. the `Rep`
/// replication action), and the `Comb` combinators in scope — `Parallel`,
/// `NDC` (with the `substStatePos` shared-position rewrite), and `CondEq`.
/// `Cond`-with-a-formula / `Lookup` / `Let` are rejected in `base_trans_comb`.
fn generate_rules<'a>(
    ctx: &TransCtx,
    an_proc: &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<Vec<AnnotatedRule<'a, ProcessAnnotation<LVar>>>, String> {
    enum Task<'a> {
        Visit(
            &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
            ProcessPosition,
            BTreeSet<LVar>,
        ),
        StartBranch(
            &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
            ProcessPosition,
            BTreeSet<LVar>,
            ProcessPosition,
        ),
        Rewrite(usize, ProcessPosition, ProcessPosition),
    }
    let mut tasks = vec![Task::Visit(an_proc, p.clone(), tildex.clone())];
    let mut out: Vec<AnnotatedRule<'a, ProcessAnnotation<LVar>>> = Vec::new();
    while let Some(task) = tasks.pop() {
        let (proc, p, tx) = match task {
            Task::Visit(proc, p, tx) => (proc, p, tx),
            Task::StartBranch(proc, p, tx, parent) => {
                tasks.push(Task::Rewrite(out.len(), p.clone(), parent));
                (proc, p, tx)
            }
            Task::Rewrite(start, old, new) => {
                for rule in &mut out[start..] {
                    for fact in &mut rule.prems {
                        if let TransFact::State(kind, pos, _) = fact
                            && *pos == old
                            && !kind.is_semi_state()
                        {
                            *kind = StateKind::LState;
                            pos.clone_from(&new);
                        }
                    }
                }
                continue;
            }
        };
        match proc {
            Process::Null(_) => {
                out.extend(map_to_annotated_rule(proc, &p, base_trans_null(&p, &tx)))
            }
            Process::Action(ac, ann, body) => {
                let (bodies, next_tx) = trans_action(ctx, ac, ann, &p, &tx)?;
                out.extend(map_to_annotated_rule(proc, &p, bodies));
                let mut child = p;
                child.push(1);
                tasks.push(Task::Visit(body, child, next_tx));
            }
            Process::Comb(ProcessCombinator::Ndc, _, left, right) => {
                // Rewrite after each complete branch, innermost NDC first.
                // Only its output suffix is touched; rule names retain their
                // original positions and left rules still precede right rules.
                let mut pl = p.clone();
                pl.push(1);
                let mut pr = p.clone();
                pr.push(2);
                tasks.push(Task::StartBranch(right, pr, tx.clone(), p.clone()));
                tasks.push(Task::StartBranch(left, pl, tx, p));
            }
            Process::Comb(c, ann, left, right) => {
                let (bodies, tx_l, tx_r) = trans_comb(ctx, c, ann, &p, &tx)?;
                out.extend(map_to_annotated_rule(proc, &p, bodies));
                if let Some(tx_r) = tx_r {
                    let mut pr = p.clone();
                    pr.push(2);
                    tasks.push(Task::Visit(right, pr, tx_r));
                }
                let mut pl = p;
                pl.push(1);
                tasks.push(Task::Visit(left, pl, tx_l));
            }
        }
    }
    Ok(out)
}

/// `trans_action` = `progressTransAct (reliableChannelTransAct baseTransAction)`
/// (sapic/src/Sapic.hs:98-100, applied per node).  Reliable wraps the base; progress wraps
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

/// `getLockPositions = pfoldMap getLock` (Basetranslation.hs:449-479, see line 473,478): the lock
/// variables of every `Lock` action with `pureState=False` and a `lock`
/// annotation, in `pfoldMap` order, NOT deduplicated.
fn get_lock_positions(p: &Process<ProcessAnnotation<LVar>, SapicLVar>) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut out = Vec::new();
    tamarin_theory::sapic::for_each_process(p, &mut |proc| {
        if let Process::Action(SapicAction::Lock(_), an, _) = proc
            && !an.pure_state
            && let Some(v) = &an.lock
        {
            out.push(v.0);
        }
    });
    out
}

/// `nub $ getUnlockPositions` (Basetranslation.hs:449-479, see line 463): the lock variables of
/// every `Unlock` action with `pureState=False` and an `unlock` annotation, in
/// `pfoldMap` order, first-occurrence deduplicated (HS `List.nub`).
fn get_unlock_positions(p: &Process<ProcessAnnotation<LVar>, SapicLVar>) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut raw = Vec::new();
    tamarin_theory::sapic::for_each_process(p, &mut |proc| {
        if let Process::Action(SapicAction::Unlock(_), an, _) = proc
            && !an.pure_state
            && let Some(v) = &an.unlock
        {
            raw.push(v.0);
        }
    });
    nub_on(&raw, |v| *v)
}

/// The result of translating a single top-level process.
pub(crate) struct Translation {
    /// The generated rules, each paired with its embedded `_restrict`
    /// formulas.  HS attaches these as the rule's `_preRestriction`
    /// (sapic/src/Sapic/Facts.hs:376-379); the port pairs them with the rule
    /// here, and `apply_sapic` runs the `_restrict` expansion (HS
    /// `liftedAddProtoRule`) over them.
    pub rules: Vec<(ProtoRuleE, Vec<SyntacticLNFormula>)>,
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
    /// `_transReport` (sapic/src/Sapic.hs:45-101, see line 56, 64): gates
    /// `translateTermsReport` (the `report(t)`→`rep(t, loc)` term rewrite)
    /// and `reportInit` (the fixed
    /// `ReportRule`).  Set from the `locations-report` builtin.
    pub trans_report: bool,
    /// `_stateChannelOpt` (OpenTheory.hs:546-547, see line 547, default False): gates the
    /// pure-state / state-channel optimisation — `annotatePureStates`
    /// (sapic/src/Sapic.hs:45-101, see line 57) and
    /// `setforcedInjectiveFacts {L_PureState, L_CellLocked}`
    /// (sapic/src/Sapic.hs:45-101, see line 84).  Set from
    /// `options: translation-state-optimisation`.
    pub state_channel_opt: bool,
}

/// `translate` (sapic/src/Sapic.hs:45-101).  `needs_in_ev_res` is HS
/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`.  `opts` carries the
/// `_transProgress` / `_transReliable` / `_asynchronousChannels` /
/// `_compressEvents` gates.
pub(crate) fn translate(
    plain: &PlainProcess,
    needs_in_ev_res: bool,
    st_rules: &std::collections::BTreeSet<tamarin_term::subterm_rule::CtxtStRule>,
    opts: TranslateOptions,
) -> Result<Translation, String> {
    // The annotation chain, innermost first (sapic/src/Sapic.hs:55-61): toAnProcess,
    // propagateNames, annotateSecretChannels, annotatePureStates,
    // translateTermsReport, translateLetDestr — then annotateLocks.
    let an_proc_pre: Process<ProcessAnnotation<LVar>, SapicLVar> =
        propagate_names(to_annotated::<LVar>(plain));
    // annotateSecretChannels (sapic/src/Sapic.hs:45-101, see line 58): attach
    // `secret_channel` to every ChIn/ChOut whose channel is an always-secret
    // fresh variable.
    let an_proc_sec = crate::secret_channels::annotate_secret_channels(an_proc_pre);
    // `checkOps' (._stateChannelOpt) annotatePureStates`
    // (sapic/src/Sapic.hs:45-101, see line 57): the
    // pure-state / state-channel optimisation, off unless the theory declares
    // `options: translation-state-optimisation`.
    let an_proc_states = if opts.state_channel_opt {
        crate::states::annotate_pure_states(an_proc_sec)
    } else {
        an_proc_sec
    };
    // `checkOps' (._transReport) translateTermsReport`
    // (sapic/src/Sapic.hs:45-101, see line 56): rewrite
    // `report(t)` terms to `rep(t, loc)` under the in-scope `@location`
    // annotation.
    let an_proc_rep = if opts.trans_report {
        crate::report::translate_terms_report(an_proc_states)
    } else {
        an_proc_states
    };
    let an_proc_let = crate::let_destructors::translate_let_destr(st_rules, an_proc_rep);
    let an_proc_owner = crate::locks::annotate_locks(an_proc_let)?;
    let an_proc = &an_proc_owner;

    // Build the translation context (gated progress/reliable/async wrappers).
    // The progress-function domain / inverse are computed once (HS recomputes
    // them per node; same result).
    let (dom_pf, inv_pf): (PosSet, Option<Box<dyn Fn(&[i64]) -> Option<Pos>>>) =
        if opts.trans_progress {
            let dom = crate::progress_function::pf_from(an_proc)?;
            let inv = crate::progress_function::pf_inv(an_proc)?;
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
    let (mut init_rules, mut init_tx) = base_init(an_proc);
    if opts.trans_progress {
        let (r, t) = crate::progress_translation::progress_init(an_proc, init_rules, init_tx)?;
        init_rules = r;
        init_tx = t;
    }
    if opts.trans_reliable {
        let (r, t) = crate::reliable_channel::reliable_channel_init(an_proc, init_rules, init_tx);
        init_rules = r;
        init_tx = t;
    }
    if opts.trans_report {
        let (r, t) = crate::report::report_init(an_proc, init_rules, init_tx);
        init_rules = r;
        init_tx = t;
    }

    // protocol rules
    let proto_rules = generate_rules(&ctx, an_proc, &Vec::new(), &init_tx)?;

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
    let restr_by_name: std::collections::HashMap<String, Vec<SyntacticLNFormula>> = all
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
    let rules: Vec<(ProtoRuleE, Vec<SyntacticLNFormula>)> = elaborated
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
    // restriction, so both closures carry that guard.
    let is_lookup_non_pure = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> bool {
        matches!(proc, Process::Comb(ProcessCombinator::Lookup(_, _), an, _, _) if !an.pure_state)
    };
    let is_delete_non_pure = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> bool {
        matches!(proc,
            Process::Action(tamarin_theory::sapic::SapicAction::Delete(_), an, _)
                if !an.pure_state)
    };
    if tamarin_theory::sapic::process_contains(an_proc, is_lookup_non_pure) {
        let has_delete = tamarin_theory::sapic::process_contains(an_proc, is_delete_non_pure);
        restrictions.extend(state_restrictions(has_delete));
    }
    if tamarin_theory::sapic::process_contains(an_proc, tamarin_theory::sapic::is_eq) {
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
    let unlock_positions = get_unlock_positions(an_proc); // nub'd
    let lock_positions = get_lock_positions(an_proc); // NOT nub'd (HS `getLockPositions`)
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
        restrictions = crate::progress_translation::progress_restr(an_proc, restrictions)?;
    }
    if opts.trans_reliable {
        restrictions = crate::reliable_channel::reliable_channel_restr(an_proc, restrictions);
    }

    Ok(Translation {
        rules,
        restrictions,
    })
}

// =============================================================================
// needsInEvRes (sapic/src/Sapic.hs:45-101, see line 101, 156-181)
// =============================================================================

/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`
/// (sapic/src/Sapic.hs:45-101, see line 101): does
/// any of the theory's lemmas fall in the fragment that requires the `in_event`
/// restriction?  Each lemma is classified via `lemma_needs_in_ev_res`.
pub(crate) fn needs_in_ev_res(thy: &tamarin_theory::theory::Theory) -> bool {
    thy.lemmas().any(lemma_needs_in_ev_res)
}

/// `lemmaNeedsInEvRes` (sapic/src/Sapic.hs:175-181): classify a lemma by its trace
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

/// `isPosNegFormula` (sapic/src/Sapic.hs:156-172): determine whether a formula is in the
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
    enum Frame<'a> {
        Not,
        Left(Connective, &'a LNFormula),
        Right(Connective, (bool, bool)),
    }
    let mut current = f;
    let mut pending = Vec::new();
    loop {
        let mut result = match current {
            ProtoFormula::Tf(_) => (true, true),
            ProtoFormula::Atom(a) => is_pos_neg_atom(a),
            ProtoFormula::Not(p) => {
                pending.push(Frame::Not);
                current = p;
                continue;
            }
            ProtoFormula::Qua(_, _, p) => {
                current = p;
                continue;
            }
            ProtoFormula::Conn(c, l, r) => {
                pending.push(Frame::Left(*c, r));
                current = l;
                continue;
            }
        };
        loop {
            match pending.pop() {
                None => return result,
                Some(Frame::Not) => result = swap(result),
                Some(Frame::Left(c, r)) => {
                    pending.push(Frame::Right(c, result));
                    current = r;
                    break;
                }
                Some(Frame::Right(c, l)) => {
                    result = match c {
                        Connective::And | Connective::Or => and2(l, result),
                        Connective::Imp => and2(swap(l), result),
                        // Preserve the upstream Iff polarity expression and its association.
                        Connective::Iff => and2(swap(l), and2(swap(result), l)),
                    }
                }
            }
        }
    }
}

/// `isPosNegFormula (Ato (Action _ f))` dispatches on `isActualKFact (factTag
/// f)` (sapic/src/Sapic.hs:156-172, see line 159, 167-169): an action on a
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
    use crate::typing::type_and_rename_process;
    use tamarin_parser::ast as p;
    use tamarin_term::lterm::LSort;
    use tamarin_theory::process_convert::convert_process;
    use tamarin_theory::sapic::ProcessParsedAnnotation;

    fn typing2_process() -> p::Process {
        let xspec = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
            typ: Some("lol".into()),
        };
        let xref = p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
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
                    action: p::SapicAction::ChOut {
                        chan: None,
                        msg: ffx,
                    },
                    body: Box::new(p::Process::Null),
                }),
            }),
        }
    }

    fn core_ctx() -> TransCtx {
        TransCtx {
            needs_in_ev_res: false,
            async_channels: false,
            trans_progress: false,
            trans_reliable: false,
            dom_pf: PosSet::new(),
            inv_pf: None,
        }
    }

    #[test]
    fn nested_ndc_rewrites_complete_branches_without_changing_rule_positions() {
        let ann = ProcessAnnotation::empty;
        let p = Process::Comb(
            ProcessCombinator::Ndc,
            ann(),
            Box::new(Process::Null(ann())).into(),
            Box::new(Process::Comb(
                ProcessCombinator::Ndc,
                ann(),
                Box::new(Process::Null(ann())).into(),
                Box::new(Process::Null(ann())).into(),
            ))
            .into(),
        );
        let rules = generate_rules(&core_ctx(), &p, &vec![], &BTreeSet::new()).unwrap();
        assert_eq!(
            rules.iter().map(|r| r.position.clone()).collect::<Vec<_>>(),
            [
                RulePosition::Pos(vec![1]),
                RulePosition::Pos(vec![2, 1]),
                RulePosition::Pos(vec![2, 2])
            ]
        );
        for rule in rules {
            assert!(
                matches!(&rule.prems[..], [TransFact::State(StateKind::LState, pos, _)] if pos.is_empty())
            );
        }
    }

    #[test]
    fn deep_rule_generation_uses_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut p = Process::Null(ProcessAnnotation::empty());
                for _ in 0..2048 {
                    p = Process::Action(
                        tamarin_theory::sapic::SapicAction::Rep,
                        ProcessAnnotation::empty(),
                        Box::new(p).into(),
                    );
                }
                let rules = generate_rules(&core_ctx(), &p, &vec![], &BTreeSet::new()).unwrap();
                assert_eq!(rules.len(), 4097);
                assert_eq!(
                    rules.last().unwrap().position,
                    RulePosition::Pos(vec![1; 2048])
                );
                drop(rules);
                p.drop_iteratively();
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn propagate_names_preserves_location() {
        // The first patch of upstream #922: setting propagated process names
        // updates only that field of the parsed annotation.
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

    #[test]
    fn translate_typing2_rule_names_and_restriction() {
        // No function-typing needed for the rule-count check; convert and
        // type over an empty signature (defaults all funs).
        let sig = tamarin_term::maude_sig::MaudeSig::default();
        let plain = convert_process(&typing2_process(), &sig).unwrap();
        let typed = type_and_rename_process(&sig, &[], &plain).unwrap();
        let st_rules = std::collections::BTreeSet::new();
        let tr = translate(&typed, false, &st_rules, TranslateOptions::default()).unwrap();
        // The rules are Init, new, event, out and null, in that order.  They
        // use the `<label>_<index>_<position>` naming that HS derives from
        // the pretty-printed head of each node (Facts.hs `toRule`).  The test
        // compares the names, not the count.  So it catches a rule emitted
        // for the wrong node.  It also catches a position suffix that comes
        // from a wrong walk, and a changed emission order.
        let names: Vec<String> = tr
            .rules
            .iter()
            .map(|r| match &r.0.info.name {
                tamarin_theory::rule::ProtoRuleName::Stand(n) => n.to_string(),
                other => panic!("expected a standard rule name, got {other:?}"),
            })
            .collect();
        assert_eq!(
            names,
            [
                "Init",
                "newxlol_0_",
                "eventTestxlol_0_1",
                "outffxlol_0_11",
                "p_0_111"
            ]
        );
        // Every SAPIC theory also gets the `single_session` restriction.
        assert_eq!(tr.restrictions.len(), 1);
        assert_eq!(tr.restrictions[0].name, "single_session");
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
    /// (sapic/src/Sapic.hs:165) parses as `p .==>. ((q .&&. q) .==>. p)` (`.&&.` infixl 3
    /// binds tighter than `.==>.` infixr 1, Theory/Model/Formula.hs:233-235),
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
