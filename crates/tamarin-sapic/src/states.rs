// Currently GPL 3.0 until granted permission by the following authors:
//   charlie-j, rkunnema, arcz, BTom-GH, kevinmorio, Hong-Thai,
//   racoucho1u, Mathias-AURAND, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic.hs, lib/sapic/src/Sapic/States.hs,
//   lib/term/src/Term/Maude/Process.hs,
//   lib/theory/src/Items/OptionItem.hs,
//   lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs

//! Port of `Sapic.States` from `lib/sapic/src/Sapic/States.hs`.
//!
//! The pure-state ("state-channel") optimisation.  When enabled via
//! `options: translation-state-optimisation` (`_stateChannelOpt`,
//! `Items/OptionItem.hs`; parsed as `stateChannelOpt` in
//! `Theory/Text/Parser/Signature.hs`), `annotatePureStates` runs in the SAPIC
//! annotation pipeline (Sapic.hs, gated on `_stateChannelOpt`).  It:
//!
//!   1. declares a fresh `new StateChannel:channel` cell-handle for every
//!      state term whose identifier is fully bound by names
//!      (`addStatesChannels`), attaching `is_state_channel`/`state_channel`
//!      annotations; and
//!   2. marks every `lock`/`lookup`/`insert`/`unlock` on a *pure* state
//!      cell (one accessed only in the lock-protected pure pattern) with
//!      `pure_state = True` (`annotateEachPureStates`), so the base
//!      translation emits the `L_PureState`/`L_CellLocked` linear facts
//!      instead of the classical `Insert`/`IsIn`/`Lock` actions.
//!
//! This mirrors `annotatePureStates` exactly (States.hs:192-235).

use std::collections::{BTreeMap, BTreeSet};

use tamarin_utils::fresh::FastFreshState;

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::sapic::{
    frees_sapic_term, Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm,
};

use crate::annotation::{AnVar, ProcessAnnotation};

type AnnotatedProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// HS `stateChannelName = "StateChannel"` (States.hs:75-76).
const STATE_CHANNEL_NAME: &str = "StateChannel";

/// HS `isBound boundNames t = S.fromList (frees $ toLNTerm t) ⊆ boundNames`
/// (States.hs:27-28): the state term's free variables are all bound by names.
fn is_bound(bound_names: &BTreeSet<LVar>, t: &SapicTerm) -> bool {
    frees_sapic_term(t)
        .into_iter()
        .all(|sv| bound_names.contains(&sv.var))
}

/// HS `getAllStates` (States.hs:34-66): returns `(boundStates, freeStates)`
/// — the set of state terms whose identifier is (resp. is not) fully bound
/// by names.  `Insert`/`Lock`/`Unlock`/`Lookup` contribute their term to one
/// of the two sets; `New v` adds `v` to the bound-name scope.
fn get_all_states(
    p: &AnnotatedProc,
    bound_names: &BTreeSet<LVar>,
) -> (BTreeSet<SapicTerm>, BTreeSet<SapicTerm>) {
    match p {
        // Insert / Lock / Unlock: classify the term, then recurse.
        Process::Action(SapicAction::Insert(t, _), _, body)
        | Process::Action(SapicAction::Lock(t), _, body)
        | Process::Action(SapicAction::Unlock(t), _, body) => {
            let (mut bound, mut free) = get_all_states(body, bound_names);
            if is_bound(bound_names, t) {
                bound.insert(t.clone());
            } else {
                free.insert(t.clone());
            }
            (bound, free)
        }
        // New v: extend the bound-name scope.
        Process::Action(SapicAction::New(v), _, body) => {
            let mut next = bound_names.clone();
            next.insert(v.var.clone());
            get_all_states(body, &next)
        }
        Process::Action(_, _, body) => get_all_states(body, bound_names),
        Process::Null(_) => (BTreeSet::new(), BTreeSet::new()),
        // Lookup t _: classify the term, then union both children.
        Process::Comb(ProcessCombinator::Lookup(t, _), _, l, r) => {
            let (bl, fl) = get_all_states(l, bound_names);
            let (br, fr) = get_all_states(r, bound_names);
            let mut bound: BTreeSet<SapicTerm> = bl.union(&br).cloned().collect();
            let mut free: BTreeSet<SapicTerm> = fl.union(&fr).cloned().collect();
            if is_bound(bound_names, t) {
                bound.insert(t.clone());
            } else {
                free.insert(t.clone());
            }
            (bound, free)
        }
        Process::Comb(_, _, l, r) => {
            let (bl, fl) = get_all_states(l, bound_names);
            let (br, fr) = get_all_states(r, bound_names);
            (
                bl.union(&br).cloned().collect(),
                fl.union(&fr).cloned().collect(),
            )
        }
    }
}

/// `StateMap`: HS `M.Map SapicTerm (AnVar LVar)` (States.hs:73-73).
type StateMap = BTreeMap<SapicTerm, AnVar<LVar>>;

/// HS `addStatesChannels` (States.hs:78-83): seed the fast fresh counter at
/// the existing max `StateChannel` index (`initStateChan`), then descend with
/// `declareStateChannel`.
fn add_states_channels(p: AnnotatedProc) -> AnnotatedProc {
    // `allBoundStates = fst $ getAllStates p ∅`
    let all_bound_states = get_all_states(&p, &BTreeSet::new()).0;
    // `initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $
    //   S.toList $ varsProc p` ; `initStateChan = fromMaybe 0
    //   (M.lookup stateChannelName initState)`.
    // `avoidPreciseVars` stores `idx+1` per name, taking the max; so the seed
    // is `max { idx+1 | (StateChannel, idx) ∈ varsProc p }` (0 if none).
    let init_state_chan = vars_proc(&p)
        .into_iter()
        .filter(|v| v.name == STATE_CHANNEL_NAME)
        .map(|v| v.idx + 1)
        .max()
        .unwrap_or(0);
    let mut fresh = FastFreshState::seeded(init_state_chan);
    let to_declare: Vec<SapicTerm> = all_bound_states.into_iter().collect();
    declare_state_channel(
        &mut fresh,
        p,
        &to_declare,
        &BTreeSet::new(),
        &BTreeMap::new(),
    )
}

/// HS `declareStateChannel` (States.hs:86-114): descend into the process.
/// When every name of a state term is in scope, declare a fresh
/// `StateChannel` cell-handle (`new StateChannel:channel`) and record it in
/// `stateMap`; meanwhile annotate every `Insert`/`Lock`/`Unlock`/`Lookup`
/// with the `state_channel` of its term (`M.lookup t stateMap`).
fn declare_state_channel(
    fresh: &mut FastFreshState,
    p: AnnotatedProc,
    to_declare: &[SapicTerm],
    bound_names: &BTreeSet<SapicLVar>,
    state_map: &StateMap,
) -> AnnotatedProc {
    // `(declarables, undeclarables) = partition (frees ⊆ boundNames) toDeclare`
    let bound_lvars: BTreeSet<LVar> = bound_names.iter().map(|v| v.var.clone()).collect();
    let (declarables, undeclarables): (Vec<SapicTerm>, Vec<SapicTerm>) =
        to_declare.iter().cloned().partition(|t| {
            frees_sapic_term(t)
                .into_iter()
                .all(|sv| bound_lvars.contains(&sv.var))
        });

    if declarables.is_empty() {
        // Nothing new to declare here: recurse, annotating state channels.
        match p {
            Process::Null(an) => Process::Null(an),
            Process::Comb(a, an, pl, pr) => {
                let pl2 = declare_state_channel(fresh, *pl, to_declare, bound_names, state_map);
                let pr2 = declare_state_channel(fresh, *pr, to_declare, bound_names, state_map);
                let an2 = match &a {
                    // `Lookup t _ -> an{ stateChannel = M.lookup t stateMap }`
                    ProcessCombinator::Lookup(t, _) => ProcessAnnotation {
                        state_channel: state_map.get(t).cloned(),
                        ..an
                    },
                    _ => an,
                };
                Process::Comb(a, an2, Box::new(pl2), Box::new(pr2))
            }
            // `ProcessAction (New var) an pr -> recurse with var ∈ boundNames`
            Process::Action(SapicAction::New(var), an, pr) => {
                let mut next = bound_names.clone();
                next.insert(var.clone());
                let pr2 = declare_state_channel(fresh, *pr, to_declare, &next, state_map);
                Process::Action(SapicAction::New(var), an, Box::new(pr2))
            }
            Process::Action(act, an, pr) => {
                let pr2 = declare_state_channel(fresh, *pr, to_declare, bound_names, state_map);
                let an2 = match &act {
                    // Insert/Lock/Unlock: `an{ stateChannel = M.lookup t stateMap }`
                    SapicAction::Insert(t, _) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
                        ProcessAnnotation {
                            state_channel: state_map.get(t).cloned(),
                            ..an
                        }
                    }
                    _ => an,
                };
                Process::Action(act, an2, Box::new(pr2))
            }
        }
    } else {
        // Declare a fresh `StateChannel` for each declarable term here,
        // recurse into the SAME process with the remaining undeclarables and
        // the extended state map, then prefix `new StateChannel:channel`
        // actions.
        let (new_vars, new_map) = new_states(fresh, &declarables, state_map);
        let p2 = declare_state_channel(fresh, p, &undeclarables, bound_names, &new_map);
        add_news(p2, &new_vars)
    }
}

/// HS `addNews` (States.hs:113-114): prefix a `new StateChannel:channel`
/// action (with `is_state_channel = Just term`) for each `(var, term)`.
fn add_news(pr: AnnotatedProc, new_vars: &[(LVar, SapicTerm)]) -> AnnotatedProc {
    let mut out = pr;
    // `addNews pr ((var, term):d) = ProcessAction (New (SapicLVar var
    //   (Just "channel"))) mempty{ isStateChannel = Just term } (addNews pr d)`
    // — fold from the end so the FIRST `(var, term)` ends up outermost.
    for (var, term) in new_vars.iter().rev() {
        let ann = ProcessAnnotation {
            is_state_channel: Some(term.clone()),
            ..ProcessAnnotation::empty()
        };
        out = Process::Action(
            SapicAction::New(SapicLVar::new(var.clone(), Some("channel".to_string()))),
            ann,
            Box::new(out),
        );
    }
    out
}

/// HS `newStates` (States.hs:116-123): mint one fresh `StateChannel` LVar per
/// declarable term, accumulating `(LVar, term)` pairs and the extended map.
/// HS conses each new `(newvar, v)` onto `declared`, so the returned list is
/// in REVERSE declarable order; we replicate that so `add_news` reproduces
/// the same outer-to-inner nesting.
fn new_states(
    fresh: &mut FastFreshState,
    declarables: &[SapicTerm],
    state_map: &StateMap,
) -> (Vec<(LVar, SapicTerm)>, StateMap) {
    let mut declared: Vec<(LVar, SapicTerm)> = Vec::new();
    let mut map = state_map.clone();
    for v in declarables {
        // `newvar <- freshLVar stateChannelName LSortMsg` — fast counter.
        let newvar = LVar {
            name: STATE_CHANNEL_NAME,
            sort: LSort::Msg,
            idx: fresh.fresh_ident(),
        };
        map.insert(v.clone(), AnVar(newvar.clone()));
        // HS conses: `newStates p declarables ((newvar, v):declared) newMap`
        declared.insert(0, (newvar, v.clone()));
    }
    (declared, map)
}

/// HS `existsAttackerUnpure` (States.hs:131-155): true if some state is
/// accessed in a non-pure fashion (a lone insert/lock/unlock/lookup on an
/// unbound identifier).  When true, no state is considered pure.
fn exists_attacker_unpure(p: &AnnotatedProc, bound_names: &BTreeSet<LVar>) -> bool {
    match p {
        // New v: extend the bound-name scope.
        Process::Action(SapicAction::New(v), _, pl) => {
            let mut next = bound_names.clone();
            next.insert(v.var.clone());
            exists_attacker_unpure(pl, &next)
        }
        // insert t; unlock t  (pure write pattern) — skip the pair, recurse.
        Process::Action(SapicAction::Insert(t, _), _, body) if matches!(&**body, Process::Action(SapicAction::Unlock(t2), _, _) if t == t2) => {
            if let Process::Action(SapicAction::Unlock(_), _, pl) = &**body {
                exists_attacker_unpure(pl, bound_names)
            } else {
                unreachable!()
            }
        }
        // lock t; lookup t as _ in .. else 0  (pure read pattern) — recurse.
        Process::Action(SapicAction::Lock(t), _, body)
            if matches!(&**body,
                Process::Comb(ProcessCombinator::Lookup(t2, _), _, _, r)
                    if t == t2 && matches!(&**r, Process::Null(_))) =>
        {
            if let Process::Comb(ProcessCombinator::Lookup(_, _), _, pl, _) = &**body {
                exists_attacker_unpure(pl, bound_names)
            } else {
                unreachable!()
            }
        }
        // Any lone action on an unbound identifier raises the warning.
        Process::Action(SapicAction::Insert(t, _), _, _) if !is_bound(bound_names, t) => true,
        Process::Action(SapicAction::Lock(t), _, _) if !is_bound(bound_names, t) => true,
        Process::Action(SapicAction::Unlock(t), _, _) if !is_bound(bound_names, t) => true,
        Process::Comb(ProcessCombinator::Lookup(t, _), _, _, r)
            if matches!(&**r, Process::Null(_)) && !is_bound(bound_names, t) =>
        {
            true
        }
        Process::Action(_, _, pl) => exists_attacker_unpure(pl, bound_names),
        Process::Comb(_, _, pl, pr) => {
            exists_attacker_unpure(pl, bound_names) || exists_attacker_unpure(pr, bound_names)
        }
        Process::Null(_) => false,
    }
}

/// HS `isPureState` (States.hs:158-187): decide if a state `target` is pure.
/// Returns `(isPure, loneInsert)`; `loneInsert` flags at least one lone
/// insert (the initialisation) for this state.
fn is_pure_state(p: &AnnotatedProc, target: &SapicTerm, lone_insert: bool) -> (bool, bool) {
    match p {
        // insert t; unlock t  — skip the pure write pair.
        Process::Action(SapicAction::Insert(t, _), _, body) if matches!(&**body, Process::Action(SapicAction::Unlock(t2), _, _) if t == t2) => {
            if let Process::Action(SapicAction::Unlock(_), _, pl) = &**body {
                is_pure_state(pl, target, lone_insert)
            } else {
                unreachable!()
            }
        }
        // lock t; lookup t as _ in .. else 0 — skip the pure read pair.
        Process::Action(SapicAction::Lock(t), _, body)
            if matches!(&**body,
                Process::Comb(ProcessCombinator::Lookup(t2, _), _, _, r)
                    if t == t2 && matches!(&**r, Process::Null(_))) =>
        {
            if let Process::Comb(ProcessCombinator::Lookup(_, _), _, pl, _) = &**body {
                is_pure_state(pl, target, lone_insert)
            } else {
                unreachable!()
            }
        }
        // lone insert on target: a second lone insert anywhere ⇒ not pure.
        Process::Action(SapicAction::Insert(t, _), _, pl) if t == target => {
            let (pure_, lone) = is_pure_state(pl, target, lone_insert);
            if lone {
                (false, lone)
            } else {
                (pure_, lone)
            }
        }
        // lone lock/unlock on target ⇒ not pure.
        Process::Action(SapicAction::Lock(t), _, _) if t == target => (false, false),
        Process::Action(SapicAction::Unlock(t), _, _) if t == target => (false, false),
        Process::Action(_, _, pl) => is_pure_state(pl, target, lone_insert),
        // Parallel: pure only if both pure and not both lone; lone = either lone.
        Process::Comb(ProcessCombinator::Parallel, _, pl, pr) => {
            let (pur, lone) = is_pure_state(pl, target, lone_insert);
            let (pur2, lone2) = is_pure_state(pr, target, lone_insert);
            (pur && pur2 && !(lone && lone2), lone || lone2)
        }
        Process::Comb(_, _, pl, pr) => {
            let (pur, lone) = is_pure_state(pl, target, lone_insert);
            let (pur2, lone2) = is_pure_state(pr, target, lone_insert);
            (pur && pur2, lone || lone2)
        }
        Process::Null(_) => (true, false),
    }
}

/// HS `annotatePureStates` (States.hs:192-196).
pub fn annotate_pure_states(p: AnnotatedProc) -> AnnotatedProc {
    if exists_attacker_unpure(&p, &BTreeSet::new()) {
        add_states_channels(p)
    } else if get_all_states(&p, &BTreeSet::new()).0.is_empty() {
        p
    } else {
        let with_channels = add_states_channels(p);
        annotate_each_pure_states(with_channels, &BTreeSet::new())
    }
}

/// HS `annotateEachPureStates` (States.hs:201-235): mark `pure_state` on
/// every `lookup`/`unlock`/`lock`/`insert` on a pure cell, and on every
/// `new StateChannel` whose cell `isPureState` (adding the cell to the
/// `pureStates` set for the body).
fn annotate_each_pure_states(p: AnnotatedProc, pure_states: &BTreeSet<SapicTerm>) -> AnnotatedProc {
    match p {
        Process::Null(an) => Process::Null(an),
        Process::Comb(comb, an, pl, pr) => {
            let pl2 = annotate_each_pure_states(*pl, pure_states);
            let pr2 = annotate_each_pure_states(*pr, pure_states);
            let an2 = match &comb {
                ProcessCombinator::Lookup(t, _) if pure_states.contains(t) => ProcessAnnotation {
                    pure_state: true,
                    ..an
                },
                _ => an,
            };
            Process::Comb(comb, an2, Box::new(pl2), Box::new(pr2))
        }
        Process::Action(ac, an, body) => {
            match &ac {
                // new StateChannel (an.is_state_channel is Some): if the cell is
                // pure, mark pure_state and add cid to pureStates for the body;
                // otherwise HS does NOT recurse into the body.  The clone is needed
                // because `an` is consumed by `..an` below.  A `New(_)` with no
                // state channel recurses into the body unchanged (default `_ =>` arm).
                SapicAction::New(_) => {
                    if let Some(cid) = &an.is_state_channel {
                        let cid = cid.clone();
                        if is_pure_state(&body, &cid, false).0 {
                            let mut next = pure_states.clone();
                            next.insert(cid.clone());
                            let body2 = annotate_each_pure_states(*body, &next);
                            let an2 = ProcessAnnotation {
                                pure_state: true,
                                is_state_channel: Some(cid),
                                ..an
                            };
                            Process::Action(ac, an2, Box::new(body2))
                        } else {
                            // HS does NOT recurse into the body in this branch.
                            Process::Action(ac, an, body)
                        }
                    } else {
                        // No state channel: recurse into the body (matches
                        // the default `_ =>` arm below).
                        let body2 = annotate_each_pure_states(*body, pure_states);
                        Process::Action(ac, an, Box::new(body2))
                    }
                }
                SapicAction::Unlock(t) => {
                    let is_pure = pure_states.contains(t);
                    let body2 = annotate_each_pure_states(*body, pure_states);
                    let an2 = if is_pure {
                        ProcessAnnotation {
                            pure_state: true,
                            ..an
                        }
                    } else {
                        an
                    };
                    Process::Action(ac, an2, Box::new(body2))
                }
                SapicAction::Lock(t) => {
                    let is_pure = pure_states.contains(t);
                    let body2 = annotate_each_pure_states(*body, pure_states);
                    let an2 = if is_pure {
                        ProcessAnnotation {
                            pure_state: true,
                            ..an
                        }
                    } else {
                        an
                    };
                    Process::Action(ac, an2, Box::new(body2))
                }
                SapicAction::Insert(t, _) => {
                    let is_pure = pure_states.contains(t);
                    let body2 = annotate_each_pure_states(*body, pure_states);
                    let an2 = if is_pure {
                        ProcessAnnotation {
                            pure_state: true,
                            ..an
                        }
                    } else {
                        an
                    };
                    Process::Action(ac, an2, Box::new(body2))
                }
                _ => {
                    let body2 = annotate_each_pure_states(*body, pure_states);
                    Process::Action(ac, an, Box::new(body2))
                }
            }
        }
    }
}

/// `varsProc`: every SAPIC variable that occurs anywhere in `p` (HS
/// `varsProc = foldMap singleton`, Process.hs:361-362).  Used only to seed the
/// `StateChannel` fresh counter; we return the underlying `LVar`s.
fn vars_proc(p: &AnnotatedProc) -> Vec<LVar> {
    let mut out: BTreeSet<LVar> = BTreeSet::new();
    fn term_vars(t: &SapicTerm, out: &mut BTreeSet<LVar>) {
        for sv in frees_sapic_term(t) {
            out.insert(sv.var);
        }
    }
    fn fact_vars(f: &tamarin_theory::sapic::SapicLNFact, out: &mut BTreeSet<LVar>) {
        for t in f.terms.iter() {
            term_vars(t, out);
        }
    }
    fn go(p: &AnnotatedProc, out: &mut BTreeSet<LVar>) {
        match p {
            Process::Null(_) => {}
            Process::Action(a, _, body) => {
                match a {
                    SapicAction::New(v) => {
                        out.insert(v.var.clone());
                    }
                    SapicAction::Event(f) => fact_vars(f, out),
                    SapicAction::ChOut { chan, msg } => {
                        if let Some(c) = chan {
                            term_vars(c, out);
                        }
                        term_vars(msg, out);
                    }
                    SapicAction::ChIn {
                        chan,
                        msg,
                        match_vars,
                    } => {
                        if let Some(c) = chan {
                            term_vars(c, out);
                        }
                        term_vars(msg, out);
                        for v in match_vars {
                            out.insert(v.var.clone());
                        }
                    }
                    SapicAction::Insert(a, b) => {
                        term_vars(a, out);
                        term_vars(b, out);
                    }
                    SapicAction::Delete(t) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
                        term_vars(t, out)
                    }
                    SapicAction::ProcessCall(_, ts) => {
                        for t in ts {
                            term_vars(t, out);
                        }
                    }
                    SapicAction::Msr {
                        prems, acts, concs, ..
                    } => {
                        for f in prems.iter().chain(acts).chain(concs) {
                            fact_vars(f, out);
                        }
                    }
                    SapicAction::Rep => {}
                }
                go(body, out);
            }
            Process::Comb(c, _, l, r) => {
                match c {
                    ProcessCombinator::Lookup(t, v) => {
                        term_vars(t, out);
                        out.insert(v.var.clone());
                    }
                    ProcessCombinator::Let {
                        left,
                        right,
                        match_vars,
                    } => {
                        term_vars(left, out);
                        term_vars(right, out);
                        for v in match_vars {
                            out.insert(v.var.clone());
                        }
                    }
                    ProcessCombinator::CondEq(a, b) => {
                        term_vars(a, out);
                        term_vars(b, out);
                    }
                    ProcessCombinator::Cond(_)
                    | ProcessCombinator::Parallel
                    | ProcessCombinator::Ndc => {}
                }
                go(l, out);
                go(r, out);
            }
        }
    }
    go(p, &mut out);
    out.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, Name, NameTag};
    use tamarin_term::vterm::{const_term, var_term};

    fn slv(name: &str, sort: LSort) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, sort, 0))
    }
    fn null() -> AnnotatedProc {
        Process::Null(ProcessAnnotation::empty())
    }
    fn act(a: SapicAction<SapicLVar>, body: AnnotatedProc) -> AnnotatedProc {
        Process::Action(a, ProcessAnnotation::empty(), Box::new(body))
    }

    /// `new s; insert s,'init'; lock s; lookup s as x in (insert s,x; unlock s)
    /// else 0` — `s` is a pure state cell.  After `annotatePureStates`:
    ///   - a `new StateChannel:channel` action is inserted (with
    ///     `is_state_channel = Just s`), and
    ///   - the lock / lookup / insert / unlock are marked `pure_state = True`.
    #[test]
    fn pure_cell_is_detected_and_annotated() {
        // The cell identifier is a fresh VARIABLE bound by `new s` (as in
        // AC.spthy's `new state`), so the term is `var_term(sv)`.
        let sv = slv("s", LSort::Fresh);
        let s = var_term(sv.clone());
        let x = slv("x", LSort::Msg);
        // inner: lookup s as x in (insert s,x; unlock s) else 0
        let lookup_body = act(
            SapicAction::Insert(s.clone(), var_term(x.clone())),
            act(SapicAction::Unlock(s.clone()), null()),
        );
        let lookup = Process::Comb(
            ProcessCombinator::Lookup(s.clone(), x.clone()),
            ProcessAnnotation::empty(),
            Box::new(lookup_body),
            Box::new(null()),
        );
        // new s; insert s,'init'; lock s; <lookup>
        let p = act(
            SapicAction::New(sv),
            act(
                SapicAction::Insert(s.clone(), const_term(Name::new(NameTag::Pub, "init"))),
                act(SapicAction::Lock(s.clone()), lookup),
            ),
        );
        let out = annotate_pure_states(p);

        // Walk: after `new s` we expect the inserted `new StateChannel:channel`.
        let Process::Action(SapicAction::New(_), _, body) = out else {
            panic!("new s")
        };
        let Process::Action(SapicAction::New(chan_var), chan_an, body) = *body else {
            panic!("expected inserted `new StateChannel:channel`")
        };
        assert_eq!(chan_var.var.name, "StateChannel");
        assert_eq!(chan_var.stype, Some("channel".to_string()));
        assert_eq!(chan_an.is_state_channel.as_ref(), Some(&s));
        assert!(chan_an.pure_state, "the StateChannel new is marked pure");

        // insert s,'init' (lone init) — pure.
        let Process::Action(SapicAction::Insert(_, _), ins_an, body) = *body else {
            panic!()
        };
        assert!(ins_an.pure_state);
        // lock s — pure.
        let Process::Action(SapicAction::Lock(_), lock_an, body) = *body else {
            panic!()
        };
        assert!(lock_an.pure_state);
        // lookup s as x — pure.
        let Process::Comb(ProcessCombinator::Lookup(_, _), lk_an, lk_body, _) = *body else {
            panic!()
        };
        assert!(lk_an.pure_state);
        // insert s,x — pure.
        let Process::Action(SapicAction::Insert(_, _), ins2_an, body) = *lk_body else {
            panic!()
        };
        assert!(ins2_an.pure_state);
        // unlock s — pure.
        let Process::Action(SapicAction::Unlock(_), unlock_an, _) = *body else {
            panic!()
        };
        assert!(unlock_an.pure_state);
    }

    /// A state accessed in a non-pure fashion (a lone unbound insert) ⇒ no
    /// pure annotation; `addStatesChannels` still runs but no `pure_state`.
    #[test]
    fn unpure_access_yields_no_pure_annotation() {
        // insert state,'v'  where `state` is a FREE (unbound) public name var:
        // `existsAttackerUnpure` returns true → addStatesChannels only.
        let state_var = var_term(slv("state", LSort::Msg));
        let p = act(
            SapicAction::Insert(state_var, const_term(Name::new(NameTag::Pub, "v"))),
            null(),
        );
        let out = annotate_pure_states(p);
        // No pure_state anywhere.
        fn any_pure(p: &AnnotatedProc) -> bool {
            match p {
                Process::Null(an) => an.pure_state,
                Process::Action(_, an, b) => an.pure_state || any_pure(b),
                Process::Comb(_, an, l, r) => an.pure_state || any_pure(l) || any_pure(r),
            }
        }
        assert!(!any_pure(&out));
    }
}
