// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! This mirrors `annotatePureStates` (States.hs:192-196), with type tags
//! erased only in state identity keys. Process terms retain their type tags.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_utils::fresh::{FastFreshState, MonadFresh};

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::sapic::{
    frees_sapic_term, Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm,
};

use crate::annotation::{AnVar, ProcessAnnotation};
use crate::process_walk::untyped_term;

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

/// The bound-state projection of HS `getAllStates` (States.hs:34-66).
/// Production callers only need states whose identifiers are fully bound by
/// names. `New v` adds `v` to the scope for its body.
fn bound_states(p: &AnnotatedProc, bound_names: &BTreeSet<LVar>) -> BTreeSet<SapicTerm> {
    enum Work<'a> {
        Visit(&'a AnnotatedProc),
        Leave(LVar),
    }
    let mut names = bound_names.clone();
    let mut bound = BTreeSet::new();
    let mut pending = vec![Work::Visit(p)];
    while let Some(work) = pending.pop() {
        match work {
            Work::Leave(v) => {
                names.remove(&v);
            }
            Work::Visit(p) => {
                let state = match p {
                    Process::Action(
                        SapicAction::Insert(t, _) | SapicAction::Lock(t) | SapicAction::Unlock(t),
                        _,
                        _,
                    ) => Some(t),
                    Process::Comb(ProcessCombinator::Lookup(t, _), _, _, _) => Some(t),
                    _ => None,
                };
                if let Some(t) = state
                    && is_bound(&names, t)
                {
                    bound.insert(untyped_term(t));
                }
                match p {
                    Process::Action(SapicAction::New(v), _, body) => {
                        if names.insert(v.var) {
                            pending.push(Work::Leave(v.var));
                        }
                        pending.push(Work::Visit(body));
                    }
                    Process::Action(_, _, body) => pending.push(Work::Visit(body)),
                    Process::Comb(_, _, l, r) => {
                        pending.push(Work::Visit(r));
                        pending.push(Work::Visit(l));
                    }
                    Process::Null(_) => {}
                }
            }
        }
    }
    bound
}

/// `StateMap`: HS `M.Map SapicTerm (AnVar LVar)` (States.hs:73-73).
type StateMap = BTreeMap<SapicTerm, AnVar<LVar>>;

/// HS `addStatesChannels` (States.hs:78-83): seed the fast fresh counter at
/// the existing max `StateChannel` index (`initStateChan`), then descend with
/// `declareStateChannel`.
fn add_states_channels(p: AnnotatedProc, all_bound_states: BTreeSet<SapicTerm>) -> AnnotatedProc {
    // `initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $
    //   S.toList $ varsProc p` ; `initStateChan = fromMaybe 0
    //   (M.lookup stateChannelName initState)`.
    // `avoidPreciseVars` stores `idx+1` per name, taking the max; so the seed
    // is `max { idx+1 | (StateChannel, idx) ∈ varsProc p }` (0 if none).
    let init_state_chan = crate::typing::vars_proc(&p)
        .into_iter()
        .map(|sv| sv.var)
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
    mut p: AnnotatedProc,
    to_declare: &[SapicTerm],
    bound_names: &BTreeSet<LVar>,
    state_map: &StateMap,
) -> AnnotatedProc {
    use std::sync::Arc;
    #[derive(Clone)]
    struct Scope {
        remaining: Arc<[SapicTerm]>,
        bound: Arc<BTreeSet<LVar>>,
        map: Arc<StateMap>,
        skip_nodes: usize,
    }
    let scope = Scope {
        remaining: to_declare.to_vec().into(),
        bound: Arc::new(bound_names.clone()),
        map: Arc::new(state_map.clone()),
        skip_nodes: 0,
    };
    crate::process_walk::walk_mut(&mut p, scope, |p, scope| {
        if scope.skip_nodes > 0 {
            scope.skip_nodes -= 1;
            return Ok::<_, std::convert::Infallible>(true);
        }
        let (declarables, undeclarables): (Vec<_>, Vec<_>) = if scope.remaining.is_empty() {
            (Vec::new(), Vec::new())
        } else {
            scope
                .remaining
                .iter()
                .cloned()
                .partition(|t| is_bound(&scope.bound, t))
        };
        let prefixes = if declarables.is_empty() {
            Vec::new()
        } else {
            let (vars, map) = new_states(fresh, &declarables, &scope.map);
            scope.map = Arc::new(map);
            scope.remaining = undeclarables.into();
            vars
        };
        match p {
            Process::Action(ac, ann, _) => match ac {
                SapicAction::New(v) if !scope.remaining.is_empty() => {
                    Arc::make_mut(&mut scope.bound).insert(v.var);
                }
                SapicAction::Insert(t, _) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
                    ann.state_channel = scope.map.get(&untyped_term(t)).cloned();
                }
                _ => {}
            },
            Process::Comb(ProcessCombinator::Lookup(t, _), ann, _, _) => {
                ann.state_channel = scope.map.get(&untyped_term(t)).cloned();
            }
            _ => {}
        }
        if !prefixes.is_empty() {
            // This callback already processed the original node. Skip it and
            // the remaining inserted prefixes on the way to its children.
            // In particular, synthesized New actions must not bind state names.
            scope.skip_nodes = prefixes.len();
            let original = std::mem::replace(p, Process::Null(ProcessAnnotation::empty()));
            *p = add_news(original, &prefixes);
        }
        Ok(true)
    })
    .unwrap();
    p
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
            SapicAction::New(SapicLVar::new(*var, Some("channel".into()))),
            ann,
            Box::new(out).into(),
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
    let mut declared: Vec<(LVar, SapicTerm)> = Vec::with_capacity(declarables.len());
    let mut map = state_map.clone();
    for v in declarables {
        // `newvar <- freshLVar stateChannelName LSortMsg` — fast counter.
        let newvar = LVar {
            name: STATE_CHANNEL_NAME,
            sort: LSort::Msg,
            idx: fresh.fresh_ident(""),
        };
        map.insert(v.clone(), AnVar(newvar));
        declared.push((newvar, v.clone()));
    }
    // HS conses: `newStates p declarables ((newvar, v):declared) newMap`, so
    // the returned list is in reverse declarable order.
    declared.reverse();
    (declared, map)
}

/// HS `existsAttackerUnpure` (States.hs:131-155): true if some state is
/// accessed in a non-pure fashion (a lone insert/lock/unlock/lookup on an
/// unbound identifier).  When true, no state is considered pure.
fn exists_attacker_unpure(p: &AnnotatedProc, bound_names: &BTreeSet<LVar>) -> bool {
    enum Work<'a> {
        Visit(&'a AnnotatedProc),
        Leave(LVar),
    }
    let mut names = bound_names.clone();
    let mut pending = vec![Work::Visit(p)];
    while let Some(work) = pending.pop() {
        match work {
            Work::Leave(v) => {
                names.remove(&v);
            }
            Work::Visit(p) => match p {
                Process::Action(SapicAction::New(v), _, body) => {
                    if names.insert(v.var) {
                        pending.push(Work::Leave(v.var));
                    }
                    pending.push(Work::Visit(body));
                }
                Process::Action(SapicAction::Insert(t, _), _, body) => {
                    if let Process::Action(SapicAction::Unlock(u), _, rest) = &**body
                        && untyped_term(t) == untyped_term(u)
                    {
                        pending.push(Work::Visit(rest));
                        continue;
                    }
                    if !is_bound(&names, t) {
                        return true;
                    }
                    pending.push(Work::Visit(body));
                }
                Process::Action(SapicAction::Lock(t), _, body) => {
                    if let Process::Comb(ProcessCombinator::Lookup(u, _), _, l, r) = &**body
                        && untyped_term(t) == untyped_term(u)
                        && matches!(&**r, Process::Null(_))
                    {
                        pending.push(Work::Visit(l));
                        continue;
                    }
                    if !is_bound(&names, t) {
                        return true;
                    }
                    pending.push(Work::Visit(body));
                }
                Process::Action(SapicAction::Unlock(t), _, body) => {
                    if !is_bound(&names, t) {
                        return true;
                    }
                    pending.push(Work::Visit(body));
                }
                Process::Comb(ProcessCombinator::Lookup(t, _), _, _, r)
                    if matches!(&**r, Process::Null(_)) && !is_bound(&names, t) =>
                {
                    return true
                }
                Process::Action(_, _, body) => pending.push(Work::Visit(body)),
                Process::Comb(_, _, l, r) => {
                    pending.push(Work::Visit(r));
                    pending.push(Work::Visit(l));
                }
                Process::Null(_) => {}
            },
        }
    }
    false
}

/// HS `isPureState` (States.hs:158-187): decide if a state `target` is pure.
/// Returns `(isPure, loneInsert)`; `loneInsert` flags at least one lone
/// insert (the initialisation) for this state.
fn is_pure_state(p: &AnnotatedProc, target: &SapicTerm, lone_insert: bool) -> (bool, bool) {
    tamarin_utils::stack::ensure_sufficient_stack(|| {
        match p {
            // `insert t; unlock t` — skip the pure write pair.  Otherwise a lone
            // insert on the target: a second lone insert anywhere ⇒ not pure.
            Process::Action(SapicAction::Insert(t, _), _, body) => {
                if let Process::Action(SapicAction::Unlock(t2), _, pl) = &**body
                    && untyped_term(t) == untyped_term(t2)
                {
                    return is_pure_state(pl, target, lone_insert);
                }
                if untyped_term(t) != untyped_term(target) {
                    return is_pure_state(body, target, lone_insert);
                }
                let (pure_, lone) = is_pure_state(body, target, lone_insert);
                if lone {
                    (false, lone)
                } else {
                    (pure_, lone)
                }
            }
            // `lock t; lookup t as _ in .. else 0` — skip the pure read pair.
            // Otherwise a lone lock on the target ⇒ not pure.
            Process::Action(SapicAction::Lock(t), _, body) => {
                if let Process::Comb(ProcessCombinator::Lookup(t2, _), _, pl, r) = &**body
                    && untyped_term(t) == untyped_term(t2)
                    && matches!(&**r, Process::Null(_))
                {
                    return is_pure_state(pl, target, lone_insert);
                }
                if untyped_term(t) == untyped_term(target) {
                    return (false, false);
                }
                is_pure_state(body, target, lone_insert)
            }
            // lone unlock on target ⇒ not pure.
            Process::Action(SapicAction::Unlock(t), _, body) => {
                if untyped_term(t) == untyped_term(target) {
                    (false, false)
                } else {
                    is_pure_state(body, target, lone_insert)
                }
            }
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
    })
}

/// HS `annotatePureStates` (States.hs:192-196).
pub(crate) fn annotate_pure_states(p: AnnotatedProc) -> AnnotatedProc {
    let attacker_unpure = exists_attacker_unpure(&p, &BTreeSet::new());
    let bound = bound_states(&p, &BTreeSet::new());
    if attacker_unpure {
        add_states_channels(p, bound)
    } else if bound.is_empty() {
        p
    } else {
        let with_channels = add_states_channels(p, bound);
        annotate_each_pure_states(with_channels, &BTreeSet::new())
    }
}

/// HS `annotateEachPureStates` (States.hs:201-235): mark `pure_state` on
/// every `lookup`/`unlock`/`lock`/`insert` on a pure cell, and on every
/// `new StateChannel` whose cell `isPureState` (adding the cell to the
/// `pureStates` set for the body).
fn annotate_each_pure_states(
    mut p: AnnotatedProc,
    pure_states: &BTreeSet<SapicTerm>,
) -> AnnotatedProc {
    use std::sync::Arc;
    crate::process_walk::walk_mut(&mut p, Arc::new(pure_states.clone()), |node, scope| {
        match node {
            Process::Action(ac, ann, body) => match ac {
                SapicAction::New(_) => {
                    if let Some(cid) = &ann.is_state_channel {
                        if !is_pure_state(body, cid, false).0 {
                            return Ok(false);
                        }
                        Arc::make_mut(scope).insert(untyped_term(cid));
                        ann.pure_state = true;
                    }
                }
                SapicAction::Unlock(t) | SapicAction::Lock(t) | SapicAction::Insert(t, _)
                    if scope.contains(&untyped_term(t)) =>
                {
                    ann.pure_state = true;
                }
                _ => {}
            },
            Process::Comb(ProcessCombinator::Lookup(t, _), ann, _, _)
                if scope.contains(&untyped_term(t)) =>
            {
                ann.pure_state = true;
            }
            _ => {}
        }
        Ok::<_, std::convert::Infallible>(true)
    })
    .unwrap();
    p
}

#[cfg(test)]
#[path = "states_tests.rs"]
mod tests;
