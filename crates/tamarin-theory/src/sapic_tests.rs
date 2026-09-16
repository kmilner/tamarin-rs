use super::*;
use tamarin_term::lterm::LSort;

#[test]
fn process_mapping_preserves_payload_and_annotation_order() {
    use std::cell::RefCell;
    let input = Process::Comb(
        ProcessCombinator::Parallel,
        0usize,
        Box::new(Process::Action(
            SapicAction::New(4u32),
            1,
            Box::new(Process::Null(2)).into(),
        ))
        .into(),
        Box::new(Process::Null(3)).into(),
    );
    let log = RefCell::new(Vec::new());
    let output = try_map_process(
        &input,
        &mut |action| {
            log.borrow_mut().push("action".to_string());
            let SapicAction::New(v) = action else {
                unreachable!()
            };
            Ok::<_, ()>(SapicAction::New(v + 1))
        },
        &mut |comb| {
            log.borrow_mut().push("comb".to_string());
            Ok(comb.clone())
        },
        &mut |ann| {
            log.borrow_mut().push(format!("ann{ann}"));
            Ok(ann + 10)
        },
    )
    .unwrap();
    assert_eq!(
        *log.borrow(),
        ["comb", "action", "ann2", "ann1", "ann3", "ann0"]
    );
    assert_eq!(
        output,
        Process::Comb(
            ProcessCombinator::Parallel,
            10,
            Box::new(Process::Action(
                SapicAction::New(5),
                11,
                Box::new(Process::Null(12)).into()
            ))
            .into(),
            Box::new(Process::Null(13)).into(),
        )
    );
}

#[test]
fn deep_process_mapping_cleans_up_after_errors_and_panics() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    struct Counted(Arc<AtomicUsize>);
    impl Drop for Counted {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    tamarin_test_support::on_stack(256 * 1024, || {
        let depth = 100_000;
        let mut left: Process<usize, ()> = Process::Null(0);
        for _ in 0..depth {
            left = Process::Action(SapicAction::Rep, 0, Box::new(left).into());
        }
        let input = Process::Comb(
            ProcessCombinator::Parallel,
            2,
            Box::new(left).into(),
            Box::new(Process::Null(1)).into(),
        );
        for panic in [false, true] {
            let drops = Arc::new(AtomicUsize::new(0));
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                try_map_process(
                    &input,
                    &mut |a| Ok(a.clone()),
                    &mut |c| Ok(c.clone()),
                    &mut |ann| {
                        if *ann == 1 {
                            assert!(!panic, "test mapping callback panic");
                            return Err(());
                        }
                        Ok(Counted(drops.clone()))
                    },
                )
            }));
            if panic {
                assert!(outcome.is_err());
            } else {
                assert!(outcome.unwrap().is_err());
            }
            assert_eq!(drops.load(Ordering::Relaxed), depth + 1);
        }
        let drops = Arc::new(AtomicUsize::new(0));
        let mapped = map_process(&input, &mut Clone::clone, &mut Clone::clone, &mut |_| {
            Counted(drops.clone())
        });
        mapped.drop_iteratively();
        assert_eq!(drops.load(Ordering::Relaxed), depth + 3);
        input.drop_iteratively();
    });
}

/// The whole point of [`SharedProcess`] is that its `Debug` writes what
/// the process's own derived `Debug` writes: the occurrence paths the
/// solver builds from a rule's info embed that rendering, so a different
/// spelling would reorder them.
#[test]
fn shared_process_debug_is_the_process_debug() {
    let inner = Process::Action(
        SapicAction::New(SapicLVar::untyped(LVar::new("x", LSort::Msg, 0))),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    let shared = SharedProcess::new(inner.clone());
    assert_eq!(format!("{:?}", shared), format!("{:?}", inner));
    // The occurrence path embeds the rule attributes' derived `Debug`,
    // which reaches the process as `Option<Arc<SharedProcess>>` — the
    // same `Some(…)` bytes the bare process writes.
    assert_eq!(
        format!("{:?}", Some(std::sync::Arc::new(shared))),
        format!("{:?}", Some(&inner))
    );
}

#[test]
fn position_relations_and_rendering() {
    assert!(descendant(&[1, 2, 3], &[1, 2]));
    assert!(!descendant(&[1, 2], &[1, 2, 3]));
    assert_eq!(pretty_position(&vec![1, 2, 1]), "121");
}

/// `untyped` is HS `SapicLVar v Nothing`. The type tag is absent. It does
/// not hold the spelling of the default type. The difference is visible in
/// two places. `pretty_function_typing_info` prints `defaultSapicTypeS`
/// ("Any") for a `None`. The SAPIC typing pass treats a `Some` as a user
/// declaration that it must respect. `to_lvar` drops whichever tag is
/// present and returns the `LVar` unchanged.
#[test]
fn sapic_lvar_untyped_has_no_type_tag_and_to_lvar_drops_it() {
    let v = LVar::new("x", LSort::Msg, 0);
    let sv = SapicLVar::untyped(v);
    assert_eq!(sv.stype, None);
    assert_eq!(sv.to_lvar(), v);
    // A tagged variable keeps its tag. `to_lvar` still returns the `LVar`
    // without the tag.
    let typed = SapicLVar::new(v, default_sapic_node_type());
    assert_eq!(typed.stype, Some("node".to_string()));
    assert_eq!(typed.to_lvar(), v);
    assert_ne!(typed, sv, "the type tag is part of the variable's identity");
}

/// `toLFormula` maps each free variable to its `LVar` through the atom,
/// the term, the literal and the `BVar`, so a tag disappears wherever it
/// sits, a bound index and its binder hint cross unchanged, and the
/// sugar's fact is reached like any other atom.
#[test]
fn to_lformula_drops_type_tags_and_keeps_bound_indices() {
    use crate::atom::{ProtoAtom, SyntacticSugar};
    use crate::fact::{Fact, FactTag};
    use crate::formula::ProtoFormula;
    use tamarin_term::vterm::var_term;

    let y = LVar::new("y", LSort::Msg, 0);
    let tagged = var_term(BVar::Free(SapicLVar::new(y, Some("foo".to_string()))));
    fn pred<V>(t: VTerm<Name, BVar<V>>) -> SyntacticNFormula<V> {
        ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(
            FactTag::Term,
            vec![t],
        ))))
    }
    let hint = ("x".to_string(), LSort::Msg);
    let fm: SapicFormula = ProtoFormula::exists(
        hint.clone(),
        ProtoFormula::Atom(ProtoAtom::EqE(var_term(BVar::Bound(0)), tagged.clone()))
            .and(pred(tagged)),
    );

    let free = var_term(BVar::Free(y));
    let want: SyntacticLNFormula = ProtoFormula::exists(
        hint,
        ProtoFormula::Atom(ProtoAtom::EqE(var_term(BVar::Bound(0)), free.clone())).and(pred(free)),
    );
    assert_eq!(to_lformula(&fm), want);
}

/// `<>` on the annotation works field by field, but each field behaves
/// differently. The names concatenate from left to right. The location
/// comes from the right side. An inner `at`-location therefore overrides
/// an outer one. Only a `None` on the right keeps the location of the
/// left. The back-substitutions compose.
#[test]
fn parsed_annotation_append_concats_names_and_right_biases_location() {
    let loc =
        |n: &str| tamarin_term::vterm::var_term(SapicLVar::untyped(LVar::new(n, LSort::Msg, 0)));
    let ann =
        |name: &str, location: Option<SapicTerm>, sub: Subst<Name, LVar>| ProcessParsedAnnotation {
            process_names: vec![name.to_string()],
            location,
            back_substitution: sub,
        };
    let sub = |from: &str, to: &str| {
        Subst::from_list([(
            LVar::new(from, LSort::Msg, 0),
            tamarin_term::vterm::var_term(LVar::new(to, LSort::Msg, 0)),
        )])
    };

    let merged =
        ann("A", Some(loc("l1")), sub("y", "z")).append(ann("B", Some(loc("l2")), sub("x", "y")));
    assert_eq!(merged.process_names, vec!["A", "B"]);
    assert_eq!(merged.location, Some(loc("l2")), "location is right-biased");
    // The operation is `compose` (`self . other`), not a union. The left
    // `y ~> z` rewrites the range of the right side, so `x ~> y` becomes
    // `x ~> z`. A union keeps `x ~> y`.
    assert_eq!(
        merged
            .back_substitution
            .image_of(&LVar::new("x", LSort::Msg, 0)),
        Some(&tamarin_term::vterm::var_term(LVar::new(
            "z",
            LSort::Msg,
            0
        )))
    );

    // A `None` on the right keeps the location of the left. A `Some` on
    // the right wins even when the left has no location.
    assert_eq!(
        ann("A", Some(loc("l1")), Subst::empty())
            .append(ann("B", None, Subst::empty()))
            .location,
        Some(loc("l1"))
    );
    assert_eq!(
        ann("A", None, Subst::empty())
            .append(ann("B", Some(loc("l2")), Subst::empty()))
            .location,
        Some(loc("l2"))
    );
    assert_eq!(ProcessParsedAnnotation::empty(), Default::default());
}

fn null_proc() -> PlainProcess {
    Process::null(ProcessParsedAnnotation::empty())
}

fn lock_action(v: &str) -> PlainProcess {
    let term = tamarin_term::vterm::var_term(SapicLVar::untyped(LVar::new(v, LSort::Msg, 0)));
    Process::Action(
        SapicAction::Lock(term),
        ProcessParsedAnnotation::empty(),
        Box::new(null_proc()).into(),
    )
}

#[test]
fn predicate_helpers() {
    assert!(is_lock(&lock_action("k")));
    assert!(!is_unlock(&lock_action("k")));
    assert!(!is_lock(&null_proc()));
}

#[test]
fn process_at_returns_root_and_navigates() {
    let p = lock_action("k");
    assert!(process_at(&p, &[]).is_some());
    // Position [1] selects the action body (a Null).
    assert!(matches!(process_at(&p, &[1]), Some(Process::Null(_))));
    // Going further than the body fails.
    assert!(process_at(&p, &[1, 1]).is_none());
}

#[test]
fn process_contains_finds_locks() {
    let p = lock_action("k");
    assert!(process_contains(&p, is_lock));
    assert!(!process_contains(&null_proc(), is_lock));
    let p: Process<u8, u8> = Process::Comb(
        ProcessCombinator::Parallel,
        2,
        Box::new(Process::Action(
            SapicAction::Rep,
            0,
            Box::new(Process::Null(1)).into(),
        ))
        .into(),
        Box::new(Process::Null(3)).into(),
    );
    let tag = |p: &Process<u8, u8>| match p {
        Process::Null(a) | Process::Action(_, a, _) | Process::Comb(_, a, _, _) => *a,
    };
    let mut order = Vec::new();
    for_each_process(&p, &mut |p| order.push(tag(p)));
    assert_eq!(order, [0, 1, 2, 3]);
    order.clear();
    assert!(process_contains(&p, |p| {
        order.push(tag(p));
        tag(p) == 1
    }));
    assert_eq!(order, [2, 0, 1]);
}

/// A match variable stands for whatever its image binds: a compound image
/// contributes all of its variables, and an image that is itself a
/// variable contributes that one. A variable the substitution does not
/// define survives. `apply_match_vars_with` reaches the same result
/// through a caller-supplied rewrite, which is what lets a caller resolve
/// a variable against a key spelling of its own.
#[test]
fn apply_match_vars_replaces_a_variable_by_the_variables_of_its_image() {
    use tamarin_term::term::f_app_list;
    use tamarin_term::vterm::var_term;

    let v = |n: &str| SapicLVar::untyped(LVar::new(n, LSort::Msg, 0));
    let pair: SapicTerm = f_app_list(vec![var_term(v("a")), var_term(v("b"))]);
    let subst = SapicSubst::from_list([(v("x"), pair), (v("y"), var_term(v("c")))]);
    let vs: BTreeSet<SapicLVar> = [v("x"), v("y"), v("z")].into_iter().collect();
    let want: BTreeSet<SapicLVar> = [v("a"), v("b"), v("c"), v("z")].into_iter().collect();

    assert_eq!(apply_match_vars(&subst, &vs), want);
    assert_eq!(
        apply_match_vars_with(
            |w| subst
                .image_of(w)
                .cloned()
                .unwrap_or_else(|| var_term(w.clone())),
            &vs
        ),
        want
    );
}

/// A process tree is `Eq`, and the comparison descends into the formulas
/// a conditional and an embedded MSR's restrictions carry: two trees built
/// from equal formulas are equal, and one changed atom separates them.
#[test]
fn process_equality_is_structural_over_condition_formulas() {
    use crate::atom::ProtoAtom;
    use crate::formula::ProtoFormula;
    use tamarin_term::vterm::var_term;

    fn requires_eq<T: Eq>(_: &T) {}

    let v = |n: &str| var_term(BVar::Free(SapicLVar::untyped(LVar::new(n, LSort::Msg, 0))));
    let eq = |l: &str, r: &str| -> SapicFormula { ProtoFormula::Atom(ProtoAtom::EqE(v(l), v(r))) };
    let proc = |cond: SapicFormula, rest: SapicFormula| -> PlainProcess {
        Process::Action(
            SapicAction::Msr {
                prems: Vec::new(),
                acts: Vec::new(),
                concs: Vec::new(),
                rest: vec![rest],
                match_vars: BTreeSet::new(),
            },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Comb(
                ProcessCombinator::Cond(cond),
                ProcessParsedAnnotation::empty(),
                Box::new(null_proc()).into(),
                Box::new(null_proc()).into(),
            ))
            .into(),
        )
    };

    let p = proc(eq("x", "y"), eq("a", "b"));
    requires_eq(&p);
    assert_eq!(p, proc(eq("x", "y"), eq("a", "b")));
    assert_ne!(p, proc(eq("x", "z"), eq("a", "b")));
    assert_ne!(p, proc(eq("x", "y"), eq("a", "c")));
}
