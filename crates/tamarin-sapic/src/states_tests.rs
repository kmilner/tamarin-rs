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
    assert_eq!(chan_var.stype.as_deref(), Some("channel"));
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
// Small-tree oracle follows the recursive declaration order directly.
fn reference_declare(
    fresh: &mut FastFreshState,
    p: AnnotatedProc,
    remaining: &[SapicTerm],
    bound: &BTreeSet<SapicLVar>,
    map: &StateMap,
) -> AnnotatedProc {
    let names = bound.iter().map(|v| v.var).collect();
    let (ready, remaining): (Vec<_>, Vec<_>) =
        remaining.iter().cloned().partition(|t| is_bound(&names, t));
    let (prefixes, map) = new_states(fresh, &ready, map);
    let p = match p {
        Process::Null(a) => Process::Null(a),
        Process::Action(ac, mut a, body) => {
            let mut bound = bound.clone();
            match &ac {
                SapicAction::New(v) => {
                    bound.insert(v.clone());
                }
                SapicAction::Insert(t, _) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
                    a.state_channel = map.get(t).cloned();
                }
                _ => {}
            }
            Process::Action(
                ac,
                a,
                Box::new(reference_declare(
                    fresh,
                    body.into_inner(),
                    &remaining,
                    &bound,
                    &map,
                ))
                .into(),
            )
        }
        Process::Comb(c, mut a, l, r) => {
            if let ProcessCombinator::Lookup(t, _) = &c {
                a.state_channel = map.get(t).cloned();
            }
            let l = reference_declare(fresh, l.into_inner(), &remaining, bound, &map);
            let r = reference_declare(fresh, r.into_inner(), &remaining, bound, &map);
            Process::Comb(c, a, Box::new(l).into(), Box::new(r).into())
        }
    };
    add_news(p, &prefixes)
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
                bound_states(&p, &names),
                reference_get_all_states(&p, &names).0
            );
            assert_eq!(
                exists_attacker_unpure(&p, &names),
                reference_exists_attacker_unpure(&p, &names)
            );
        }
        // Multiple immediate declarations, an existing annotated binder,
        // and declarations delayed until a name is bound in one branch.
        let a = const_term(Name::new(NameTag::Pub, "a"));
        let b = const_term(Name::new(NameTag::Pub, "b"));
        let mut annotated = p.clone();
        if let Process::Action(_, ann, _) | Process::Comb(_, ann, _, _) = &mut annotated {
            ann.is_state_channel = Some(a.clone());
        }
        for bound in [
            BTreeSet::new(),
            [v.clone()].into(),
            [v.clone(), SapicLVar::new(v.var, Some("typed".into()))].into(),
        ] {
            let remaining = [a.clone(), b.clone(), t.clone()];
            let map = StateMap::new();
            let mut actual_fresh = FastFreshState::seeded(7);
            let mut expected_fresh = FastFreshState::seeded(7);
            assert_eq!(
                declare_state_channel(
                    &mut actual_fresh,
                    annotated.clone(),
                    &remaining,
                    &bound.iter().map(|v| v.var).collect(),
                    &map
                ),
                reference_declare(
                    &mut expected_fresh,
                    annotated.clone(),
                    &remaining,
                    &bound,
                    &map
                ),
            );
            assert_eq!(actual_fresh.fresh_ident(""), expected_fresh.fresh_ident(""));
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
    tamarin_test_support::on_stack(256 * 1024, || {
        let v = slv("s", LSort::Msg);
        let t = var_term(v.clone());
        let mut p = act(SapicAction::Insert(t.clone(), t.clone()), null());
        // Repeated binders exercise scope restoration without growing the name set.
        for _ in 0..20_000 {
            p = act(SapicAction::New(v.clone()), p);
        }
        assert!(bound_states(&p, &BTreeSet::new()).contains(&t));
        assert!(!exists_attacker_unpure(&p, &BTreeSet::new()));
        let _ = is_pure_state(&p, &t, false);
        drop(annotate_pure_states(p));
    });
}
