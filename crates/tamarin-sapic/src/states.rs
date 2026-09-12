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
//! This mirrors `annotatePureStates` exactly (States.hs:192-196).

use std::collections::{BTreeMap, BTreeSet};

use tamarin_utils::fresh::{FastFreshState, MonadFresh};

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
    enum Work<'a> {
        Visit(&'a AnnotatedProc),
        Leave(LVar),
    }
    let mut names = bound_names.clone();
    let mut bound = BTreeSet::new();
    let mut free = BTreeSet::new();
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
                if let Some(t) = state {
                    if is_bound(&names, t) {
                        bound.insert(t.clone());
                    } else {
                        free.insert(t.clone());
                    }
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
    (bound, free)
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
    p: AnnotatedProc,
    to_declare: &[SapicTerm],
    bound_names: &BTreeSet<SapicLVar>,
    state_map: &StateMap,
) -> AnnotatedProc {
    use std::sync::Arc;
    #[derive(Clone)]
    struct Scope {
        remaining: Arc<[SapicTerm]>,
        bound: Arc<BTreeSet<SapicLVar>>,
        map: Arc<StateMap>,
    }
    enum Work {
        Visit(AnnotatedProc, Scope),
        Action(SapicAction<SapicLVar>, ProcessAnnotation<LVar>),
        Comb(ProcessCombinator<SapicLVar>, ProcessAnnotation<LVar>),
        Prefix(Vec<(LVar, SapicTerm)>),
    }
    let scope = Scope {
        remaining: to_declare.to_vec().into(),
        bound: Arc::new(bound_names.clone()),
        map: Arc::new(state_map.clone()),
    };
    let mut pending = vec![Work::Visit(p, scope)];
    let mut output = Vec::new();
    while let Some(work) = pending.pop() {
        match work {
            Work::Visit(p, mut scope) => {
                let (declarables, undeclarables): (Vec<_>, Vec<_>) = if scope.remaining.is_empty() {
                    (Vec::new(), Vec::new())
                } else {
                    let names: BTreeSet<_> = scope.bound.iter().map(|v| v.var).collect();
                    scope
                        .remaining
                        .iter()
                        .cloned()
                        .partition(|t| is_bound(&names, t))
                };
                if !declarables.is_empty() {
                    let (vars, map) = new_states(fresh, &declarables, &scope.map);
                    scope.map = Arc::new(map);
                    scope.remaining = undeclarables.into();
                    pending.push(Work::Prefix(vars));
                    pending.push(Work::Visit(p, scope));
                    continue;
                }
                match p {
                    Process::Null(ann) => output.push(Process::Null(ann)),
                    Process::Action(ac, mut ann, body) => {
                        match &ac {
                            SapicAction::New(v) => {
                                Arc::make_mut(&mut scope.bound).insert(v.clone());
                            }
                            SapicAction::Insert(t, _)
                            | SapicAction::Lock(t)
                            | SapicAction::Unlock(t) => {
                                ann.state_channel = scope.map.get(t).cloned()
                            }
                            _ => {}
                        }
                        pending.push(Work::Action(ac, ann));
                        pending.push(Work::Visit(body.into_inner(), scope));
                    }
                    Process::Comb(c, mut ann, l, r) => {
                        if let ProcessCombinator::Lookup(t, _) = &c {
                            ann.state_channel = scope.map.get(t).cloned();
                        }
                        pending.push(Work::Comb(c, ann));
                        pending.push(Work::Visit(r.into_inner(), scope.clone()));
                        pending.push(Work::Visit(l.into_inner(), scope));
                    }
                }
            }
            Work::Action(ac, ann) => {
                let body = output.pop().unwrap();
                output.push(Process::Action(ac, ann, Box::new(body).into()));
            }
            Work::Comb(c, ann) => {
                let r = output.pop().unwrap();
                let l = output.pop().unwrap();
                output.push(Process::Comb(
                    c,
                    ann,
                    Box::new(l).into(),
                    Box::new(r).into(),
                ));
            }
            Work::Prefix(vars) => {
                let body = output.pop().unwrap();
                output.push(add_news(body, &vars));
            }
        }
    }
    output.pop().unwrap()
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
            SapicAction::New(SapicLVar::new(*var, Some("channel".to_string()))),
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
                        && t == u
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
                        && t == u
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
    enum Frame<'a> {
        Insert,
        Left(bool, &'a AnnotatedProc, bool),
        Right(bool, (bool, bool)),
    }
    let mut current = (p, lone_insert);
    let mut pending = Vec::new();
    loop {
        let (p, lone_insert) = current;
        let mut result = match p {
            Process::Action(SapicAction::Insert(t, _), _, body) => {
                if let Process::Action(SapicAction::Unlock(u), _, rest) = &**body
                    && t == u
                {
                    current = (rest, lone_insert);
                    continue;
                }
                if t == target {
                    pending.push(Frame::Insert);
                }
                current = (body, lone_insert);
                continue;
            }
            Process::Action(SapicAction::Lock(t), _, body) => {
                if let Process::Comb(ProcessCombinator::Lookup(u, _), _, l, r) = &**body
                    && t == u
                    && matches!(&**r, Process::Null(_))
                {
                    current = (l, lone_insert);
                    continue;
                }
                if t == target {
                    (false, false)
                } else {
                    current = (body, lone_insert);
                    continue;
                }
            }
            Process::Action(SapicAction::Unlock(t), _, body) => {
                if t == target {
                    (false, false)
                } else {
                    current = (body, lone_insert);
                    continue;
                }
            }
            Process::Action(_, _, body) => {
                current = (body, lone_insert);
                continue;
            }
            Process::Comb(c, _, l, r) => {
                pending.push(Frame::Left(
                    matches!(c, ProcessCombinator::Parallel),
                    r,
                    lone_insert,
                ));
                current = (l, lone_insert);
                continue;
            }
            Process::Null(_) => (true, false),
        };
        loop {
            match pending.pop() {
                None => return result,
                Some(Frame::Insert) => {
                    if result.1 {
                        result.0 = false;
                    }
                }
                Some(Frame::Left(parallel, r, lone)) => {
                    pending.push(Frame::Right(parallel, result));
                    current = (r, lone);
                    break;
                }
                Some(Frame::Right(parallel, l)) => {
                    result = (
                        l.0 && result.0 && !(parallel && l.1 && result.1),
                        l.1 || result.1,
                    );
                }
            }
        }
    }
}

/// HS `annotatePureStates` (States.hs:192-196).
pub(crate) fn annotate_pure_states(p: AnnotatedProc) -> AnnotatedProc {
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
                        Arc::make_mut(scope).insert(cid.clone());
                        ann.pure_state = true;
                    }
                }
                SapicAction::Unlock(t) | SapicAction::Lock(t) | SapicAction::Insert(t, _)
                    if scope.contains(t) =>
                {
                    ann.pure_state = true;
                }
                _ => {}
            },
            Process::Comb(ProcessCombinator::Lookup(t, _), ann, _, _) if scope.contains(t) => {
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
        Process::Action(a, ProcessAnnotation::empty(), Box::new(body).into())
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
            Box::new(lookup_body).into(),
            Box::new(null()).into(),
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
        let Process::Action(SapicAction::New(chan_var), chan_an, body) = body.into_inner() else {
            panic!("expected inserted `new StateChannel:channel`")
        };
        assert_eq!(chan_var.var.name, "StateChannel");
        assert_eq!(chan_var.stype, Some("channel".to_string()));
        assert_eq!(chan_an.is_state_channel.as_ref(), Some(&s));
        assert!(chan_an.pure_state, "the StateChannel new is marked pure");

        // insert s,'init' (lone init) — pure.
        let Process::Action(SapicAction::Insert(_, _), ins_an, body) = body.into_inner() else {
            panic!()
        };
        assert!(ins_an.pure_state);
        // lock s — pure.
        let Process::Action(SapicAction::Lock(_), lock_an, body) = body.into_inner() else {
            panic!()
        };
        assert!(lock_an.pure_state);
        // lookup s as x — pure.
        let Process::Comb(ProcessCombinator::Lookup(_, _), lk_an, lk_body, _) = body.into_inner()
        else {
            panic!()
        };
        assert!(lk_an.pure_state);
        // insert s,x — pure.
        let Process::Action(SapicAction::Insert(_, _), ins2_an, body) = lk_body.into_inner() else {
            panic!()
        };
        assert!(ins2_an.pure_state);
        // unlock s — pure.
        let Process::Action(SapicAction::Unlock(_), unlock_an, _) = body.into_inner() else {
            panic!()
        };
        assert!(unlock_an.pure_state);
    }

    #[test]
    fn pure_annotations_preserve_sibling_scope_and_prune_impure_bodies() {
        let v = slv("s", LSort::Fresh);
        let s = var_term(v.clone());
        let channel = |cell, body: AnnotatedProc| {
            Process::Action(
                SapicAction::New(v.clone()),
                ProcessAnnotation {
                    is_state_channel: Some(cell),
                    ..ProcessAnnotation::empty()
                },
                Box::new(body).into(),
            )
        };
        let process = Process::Comb(
            ProcessCombinator::Parallel,
            ProcessAnnotation::empty(),
            Box::new(channel(
                s.clone(),
                act(SapicAction::Insert(s.clone(), s.clone()), null()),
            ))
            .into(),
            Box::new(act(SapicAction::Lock(s.clone()), null())).into(),
        );
        let mut expected = process.clone();
        let Process::Comb(_, _, left, _) = &mut expected else {
            unreachable!()
        };
        let Process::Action(_, ann, body) = &mut **left else {
            unreachable!()
        };
        ann.pure_state = true;
        let Process::Action(_, ann, _) = &mut **body else {
            unreachable!()
        };
        ann.pure_state = true;
        assert_eq!(
            annotate_each_pure_states(process, &BTreeSet::new()),
            expected
        );

        // An impure state-channel binder prunes its entire body, including
        // accesses to an inherited pure cell. Existing annotations survive.
        let t = var_term(slv("t", LSort::Fresh));
        let body = act(
            SapicAction::Lock(t.clone()),
            act(SapicAction::Lock(s.clone()), null()),
        );
        let mut process = channel(t, body);
        let Process::Action(_, ann, _) = &mut process else {
            unreachable!()
        };
        ann.pure_state = true;
        let expected = process.clone();
        assert_eq!(annotate_each_pure_states(process, &[s].into()), expected);
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
    fn reference_get_all_states(
        p: &AnnotatedProc,
        bound_names: &BTreeSet<LVar>,
    ) -> (BTreeSet<SapicTerm>, BTreeSet<SapicTerm>) {
        match p {
            // Insert / Lock / Unlock: classify the term, then recurse.
            Process::Action(SapicAction::Insert(t, _), _, body)
            | Process::Action(SapicAction::Lock(t), _, body)
            | Process::Action(SapicAction::Unlock(t), _, body) => {
                let (mut bound, mut free) = reference_get_all_states(body, bound_names);
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
                next.insert(v.var);
                reference_get_all_states(body, &next)
            }
            Process::Action(_, _, body) => reference_get_all_states(body, bound_names),
            Process::Null(_) => (BTreeSet::new(), BTreeSet::new()),
            // Lookup t _: classify the term, then union both children.
            Process::Comb(ProcessCombinator::Lookup(t, _), _, l, r) => {
                let (bl, fl) = reference_get_all_states(l, bound_names);
                let (br, fr) = reference_get_all_states(r, bound_names);
                let (mut bound, mut free) = (bl, fl);
                bound.extend(br);
                free.extend(fr);
                if is_bound(bound_names, t) {
                    bound.insert(t.clone());
                } else {
                    free.insert(t.clone());
                }
                (bound, free)
            }
            Process::Comb(_, _, l, r) => {
                let (mut bound, mut free) = reference_get_all_states(l, bound_names);
                let (br, fr) = reference_get_all_states(r, bound_names);
                bound.extend(br);
                free.extend(fr);
                (bound, free)
            }
        }
    }
    fn reference_exists_attacker_unpure(p: &AnnotatedProc, bound_names: &BTreeSet<LVar>) -> bool {
        match p {
            // New v: extend the bound-name scope.
            Process::Action(SapicAction::New(v), _, pl) => {
                let mut next = bound_names.clone();
                next.insert(v.var);
                reference_exists_attacker_unpure(pl, &next)
            }
            // `insert t; unlock t` (the pure write pattern) skips the pair; any
            // other lone insert on an unbound identifier raises the warning.
            Process::Action(SapicAction::Insert(t, _), _, body) => {
                if let Process::Action(SapicAction::Unlock(t2), _, pl) = &**body
                    && t == t2
                {
                    return reference_exists_attacker_unpure(pl, bound_names);
                }
                !is_bound(bound_names, t) || reference_exists_attacker_unpure(body, bound_names)
            }
            // `lock t; lookup t as _ in .. else 0` (the pure read pattern) skips to
            // the lookup body; any other lone lock on an unbound identifier warns.
            Process::Action(SapicAction::Lock(t), _, body) => {
                if let Process::Comb(ProcessCombinator::Lookup(t2, _), _, pl, r) = &**body
                    && t == t2
                    && matches!(&**r, Process::Null(_))
                {
                    return reference_exists_attacker_unpure(pl, bound_names);
                }
                !is_bound(bound_names, t) || reference_exists_attacker_unpure(body, bound_names)
            }
            Process::Action(SapicAction::Unlock(t), _, body) => {
                !is_bound(bound_names, t) || reference_exists_attacker_unpure(body, bound_names)
            }
            Process::Comb(ProcessCombinator::Lookup(t, _), _, _, r)
                if matches!(&**r, Process::Null(_)) && !is_bound(bound_names, t) =>
            {
                true
            }
            Process::Action(_, _, pl) => reference_exists_attacker_unpure(pl, bound_names),
            Process::Comb(_, _, pl, pr) => {
                reference_exists_attacker_unpure(pl, bound_names)
                    || reference_exists_attacker_unpure(pr, bound_names)
            }
            Process::Null(_) => false,
        }
    }
    fn reference_is_pure_state(
        p: &AnnotatedProc,
        target: &SapicTerm,
        lone_insert: bool,
    ) -> (bool, bool) {
        match p {
            // `insert t; unlock t` — skip the pure write pair.  Otherwise a lone
            // insert on the target: a second lone insert anywhere ⇒ not pure.
            Process::Action(SapicAction::Insert(t, _), _, body) => {
                if let Process::Action(SapicAction::Unlock(t2), _, pl) = &**body
                    && t == t2
                {
                    return reference_is_pure_state(pl, target, lone_insert);
                }
                if t != target {
                    return reference_is_pure_state(body, target, lone_insert);
                }
                let (pure_, lone) = reference_is_pure_state(body, target, lone_insert);
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
                    && t == t2
                    && matches!(&**r, Process::Null(_))
                {
                    return reference_is_pure_state(pl, target, lone_insert);
                }
                if t == target {
                    return (false, false);
                }
                reference_is_pure_state(body, target, lone_insert)
            }
            // lone unlock on target ⇒ not pure.
            Process::Action(SapicAction::Unlock(t), _, body) => {
                if t == target {
                    (false, false)
                } else {
                    reference_is_pure_state(body, target, lone_insert)
                }
            }
            Process::Action(_, _, pl) => reference_is_pure_state(pl, target, lone_insert),
            // Parallel: pure only if both pure and not both lone; lone = either lone.
            Process::Comb(ProcessCombinator::Parallel, _, pl, pr) => {
                let (pur, lone) = reference_is_pure_state(pl, target, lone_insert);
                let (pur2, lone2) = reference_is_pure_state(pr, target, lone_insert);
                (pur && pur2 && !(lone && lone2), lone || lone2)
            }
            Process::Comb(_, _, pl, pr) => {
                let (pur, lone) = reference_is_pure_state(pl, target, lone_insert);
                let (pur2, lone2) = reference_is_pure_state(pr, target, lone_insert);
                (pur && pur2, lone || lone2)
            }
            Process::Null(_) => (true, false),
        }
    }
    #[test]
    fn state_walks_match_recursive_scope_and_pruning() {
        let v = slv("s", LSort::Msg);
        let t = var_term(v.clone());
        let mut p = act(SapicAction::Insert(t.clone(), t.clone()), null());
        for seed in 0..16 {
            p = match seed % 4 {
                0 => act(SapicAction::New(v.clone()), p),
                1 => Process::Comb(
                    ProcessCombinator::Parallel,
                    Default::default(),
                    Box::new(p).into(),
                    Box::new(act(SapicAction::Insert(t.clone(), t.clone()), null())).into(),
                ),
                2 => act(SapicAction::Lock(t.clone()), p),
                _ => Process::Comb(
                    ProcessCombinator::Lookup(t.clone(), v.clone()),
                    Default::default(),
                    Box::new(p).into(),
                    Box::new(null()).into(),
                ),
            };
            for names in [BTreeSet::new(), [v.var].into()] {
                assert_eq!(
                    get_all_states(&p, &names),
                    reference_get_all_states(&p, &names)
                );
                assert_eq!(
                    exists_attacker_unpure(&p, &names),
                    reference_exists_attacker_unpure(&p, &names)
                );
            }
            for lone in [false, true] {
                assert_eq!(
                    is_pure_state(&p, &t, lone),
                    reference_is_pure_state(&p, &t, lone)
                );
            }
        }
    }
    #[test]
    fn deep_state_passes_use_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let v = slv("s", LSort::Msg);
                let t = var_term(v.clone());
                let mut p = act(SapicAction::Insert(t.clone(), t.clone()), null());
                // Repeated binders exercise scope restoration without growing the name set.
                for _ in 0..20_000 {
                    p = act(SapicAction::New(v.clone()), p);
                }
                let (bound, free) = get_all_states(&p, &BTreeSet::new());
                assert!(bound.contains(&t));
                assert!(free.is_empty());
                assert!(!exists_attacker_unpure(&p, &BTreeSet::new()));
                let _ = is_pure_state(&p, &t, false);
                drop(annotate_pure_states(p));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
