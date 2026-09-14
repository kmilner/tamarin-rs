use super::*;
use tamarin_theory::sapic::ProcessParsedAnnotation;

/// Reference `apply subst p` over the whole subtree, including locations,
/// mirroring HS's `apply initSubst p` (Typing.hs:246).
fn rename_process_full(subst: &BTreeMap<LVar, LVar>, p: &PlainProcess) -> PlainProcess {
    tamarin_theory::sapic::map_process(
        p,
        &mut |action| rename_action(subst, action),
        &mut |comb| rename_comb(subst, comb),
        &mut |ann| rename_annotation(subst, ann),
    )
}

fn reference_rename(
    fresh: &mut PreciseFreshState,
    subst: &BTreeMap<LVar, LVar>,
    p: &PlainProcess,
) -> PlainProcess {
    // `let p' = apply initSubst p` — apply the outstanding renaming to the
    // WHOLE subtree (HS Typing.hs:242-261, see line 246); the children inherit the rename, then
    // are descended into with only the NEW fresh subst for this node's binders.
    let p_prime = rename_process_full(subst, p);
    match p_prime {
        Process::Null(ann) => Process::Null(ann),
        Process::Action(ac, ann, body) => {
            let bvars = bindings_act(&ac);
            let (new_subst, inv) = mk_subst(fresh, &bvars);
            let mut ann2 = ann;
            ann2.back_substitution = ann2.back_substitution.compose(&inv);
            let ac1 = rename_action(&new_subst, &ac);
            let body1 = reference_rename(fresh, &new_subst, &body);
            Process::Action(ac1, ann2, Box::new(body1).into())
        }
        Process::Comb(c, ann, l, r) => {
            let bvars = bindings_comb(&c);
            let (new_subst, inv) = mk_subst(fresh, &bvars);
            let mut ann2 = ann;
            ann2.back_substitution = ann2.back_substitution.compose(&inv);
            let c1 = rename_comb(&new_subst, &c);
            let l1 = reference_rename(fresh, &new_subst, &l);
            let r1 = reference_rename(fresh, &new_subst, &r);
            Process::Comb(c1, ann2, Box::new(l1).into(), Box::new(r1).into())
        }
    }
}

#[test]
fn renaming_matches_suffix_substitution_with_shadowing_and_branches() {
    // Include annotation-only names that can collide with minted names,
    // repeated binders, typed variables, and independent sibling scopes.
    for seed in 0..24 {
        let ann = |i| {
            let mut a = ProcessParsedAnnotation::empty();
            a.location = Some(var_term(slv("x", i, Some("site"))));
            a
        };
        let mut p = Process::Null(ann(seed % 5));
        for i in 0..8 {
            p = if (seed + i) % 3 == 0 {
                Process::Comb(
                    ProcessCombinator::Lookup(var_term(slv("x", 0, None)), slv("x", i % 2, None)),
                    ann(i % 5),
                    Box::new(p).into(),
                    Box::new(Process::Action(
                        SapicAction::New(slv("x", 0, None)),
                        ann(1),
                        Box::new(Process::Null(ann(2))).into(),
                    ))
                    .into(),
                )
            } else {
                Process::Action(
                    SapicAction::New(slv("x", i % 2, Some("message"))),
                    ann(i % 5),
                    Box::new(p).into(),
                )
            };
        }
        let avoid = proc_lvars(&p)
            .into_iter()
            .map(|v| (v.name.to_string(), v.idx))
            .collect::<Vec<_>>();
        let expected = reference_rename(
            &mut PreciseFreshState::avoid_precise(avoid),
            &BTreeMap::new(),
            &p,
        );
        assert_eq!(rename_unique(&p), expected, "seed {seed}");
    }
}

#[test]
fn deep_typing_and_variable_collection_use_bounded_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let x = slv("x", 0, Some("message"));
        let mut process = Process::Action(
            SapicAction::New(x.clone()),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
        );
        for _ in 0..100_000 {
            process = Process::Action(
                SapicAction::Rep,
                ProcessParsedAnnotation::empty(),
                Box::new(process).into(),
            );
        }
        assert_eq!(vars_proc(&process), vec![x.clone()]);
        let env = || TypingEnvironment {
            vars: BTreeMap::new(),
            funs: BTreeMap::new(),
            events: BTreeMap::new(),
        };
        // Also release the renamed temporary owned by the complete pipeline.
        drop(type_and_rename_process_in(&mut env(), &process).unwrap());
        let typed = type_process(&mut env(), &process).unwrap();
        assert_eq!(vars_proc(&typed), vec![x.clone()]);
        typed.drop_iteratively();
        // The left branch is already rebuilt when the right branch's
        // duplicate binder fails; its cleanup must use the worklist too.
        let input = Process::Comb(
            ProcessCombinator::Parallel,
            ProcessParsedAnnotation::empty(),
            Box::new(process).into(),
            Box::new(Process::Action(
                SapicAction::New(x),
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
            ))
            .into(),
        );
        let error = type_process(&mut env(), &input).unwrap_err();
        assert!(error.contains("variable bound twice"));
        input.drop_iteratively();
    });
}

#[test]
fn typing_visits_children_before_parent_terms_and_left_before_right() {
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    let x = slv("x", 0, Some("learned"));
    let tag = FactTag::Proto(Multiplicity::Linear, "Learned", 1);
    // The parent event can only type x after visiting the child's binder.
    let input = Process::Action(
        SapicAction::Event(Fact::new(tag, vec![var_term(slv("x", 0, None))])),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Comb(
            ProcessCombinator::Parallel,
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Action(
                SapicAction::New(x),
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
            ))
            .into(),
            Box::new(Process::Action(
                SapicAction::Event(Fact::new(tag, vec![var_term(slv("x", 0, None))])),
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
            ))
            .into(),
        ))
        .into(),
    );
    let mut env = TypingEnvironment {
        vars: BTreeMap::new(),
        funs: BTreeMap::new(),
        events: BTreeMap::new(),
    };
    let typed = type_process(&mut env, &input).unwrap();
    assert_eq!(env.events[&tag], vec![Some("learned".into())]);
    let Process::Action(SapicAction::Event(event), _, _) = &typed else {
        panic!("typed event")
    };
    assert_eq!(event.terms[0], var_term(slv("x", 0, Some("learned"))));
}

fn slv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
    SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(|s| s.to_string()))
}

#[test]
fn rename_unique_mints_x1_for_new_x0() {
    // new x:lol; 0  with x at index 0 → x.1
    let new = Process::Action(
        SapicAction::New(slv("x", 0, Some("lol"))),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    let r = rename_unique(&new);
    if let Process::Action(SapicAction::New(v), _, _) = r {
        assert_eq!(v.var.idx, 1);
        assert_eq!(v.var.name, "x");
        assert_eq!(v.stype, Some("lol".to_string()));
    } else {
        panic!("expected New action");
    }
}

#[test]
fn rename_unique_renames_location_terms() {
    let mut body_ann = ProcessParsedAnnotation::empty();
    body_ann.location = Some(var_term(slv("x", 0, None)));
    let proc = Process::Action(
        SapicAction::New(slv("x", 0, None)),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(body_ann)).into(),
    );

    let Process::Action(_, _, body) = rename_unique(&proc) else {
        panic!("expected New action");
    };
    assert_eq!(
        body.annotation().location,
        Some(var_term(slv("x", 1, None)))
    );
}

/// An MSR's embedded `_restrict(...)` alpha-renames with the rest of the
/// rule body: HS maps the formula list with the SAME substitution as the
/// fact rows (`mapTermsAction f ff fv (MSR ..) = MSR .. (fmap ff rest) ..`).
/// A stale variable here leaks into the `process="..."` attribute AND into
/// the generated `Restr_*` action fact's arguments.
///
/// Oracle bytes (pinned build, Git revision ef3f0468) for
/// `in(k); [ ] --[ Ev(k), _restrict(k = 'b') ]-> [ ]; out('y')`:
///   `_restrict(k.1 = 'b')` — index 1, matching the renamed `Ev( k.1 )`.
#[test]
fn rename_unique_renames_msr_embedded_restriction() {
    use tamarin_theory::atom::ProtoAtom;
    use tamarin_theory::formula::ProtoFormula;

    // `k = 'b'`, with `k` the process variable the enclosing `new` binds.
    let restr = ProtoFormula::Atom(ProtoAtom::EqE(
        var_term(tamarin_term::lterm::BVar::Free(slv("k", 0, None))),
        VTerm::Lit(Lit::Con(Name::new(tamarin_term::lterm::NameTag::Pub, "b"))),
    ));
    let ev = tamarin_theory::fact::Fact::new(
        tamarin_theory::fact::FactTag::Proto(tamarin_theory::fact::Multiplicity::Linear, "Ev", 1),
        vec![var_term(slv("k", 0, None))],
    );
    let msr = Process::Action(
        SapicAction::Msr {
            prems: Vec::new(),
            acts: vec![ev],
            concs: Vec::new(),
            rest: vec![restr],
            match_vars: std::collections::BTreeSet::new(),
        },
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
    );
    // `new k; <msr>` — the binder renames `k` to `k.1` throughout the body.
    let proc = Process::Action(
        SapicAction::New(slv("k", 0, None)),
        ProcessParsedAnnotation::empty(),
        Box::new(msr).into(),
    );

    let Process::Action(_, _, body) = rename_unique(&proc) else {
        panic!("expected New action");
    };
    let Process::Action(SapicAction::Msr { acts, rest, .. }, _, _) = body.into_inner() else {
        panic!("expected MSR action");
    };
    // The action row renamed...
    assert_eq!(
        acts[0].terms[0],
        var_term(slv("k", 1, None)),
        "Ev's argument must be k.1"
    );
    // ...and so did the embedded restriction.
    assert_eq!(
        formula_frees(&rest[0]),
        vec![slv("k", 1, None)],
        "the restriction's only free variable must be k.1"
    );
}

/// The `gAct Event` case (Typing.hs:145-150) records the event's inferred
/// argument types in `env.events`, keyed by the fact tag.
#[test]
fn typing_records_event_arg_types_in_env() {
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    // new x:lol; event Run(x); 0
    let x = slv("x", 0, Some("lol"));
    let run = Fact::new(
        FactTag::Proto(Multiplicity::Linear, "Run", 1),
        vec![var_term(slv("x", 0, None))],
    );
    let proc = Process::Action(
        SapicAction::New(x),
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Action(
            SapicAction::Event(run),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
        ))
        .into(),
    );
    let mut env = TypingEnvironment {
        vars: BTreeMap::new(),
        funs: BTreeMap::new(),
        events: BTreeMap::new(),
    };
    type_process(&mut env, &proc).unwrap();
    assert_eq!(
        env.events
            .get(&FactTag::Proto(Multiplicity::Linear, "Run", 1)),
        Some(&vec![Some("lol".to_string())])
    );
}

/// `initTEFromSig`'s `foldM typeRule initTE sigRules` (Typing.hs:185,
/// 179-181): typing the signature's subterm rewrite rules propagates a
/// DECLARED function type through an equation onto another symbol.  Here
/// `g(f(x)) = x` with `f(bitstring):bitstring` teaches `g` the argument
/// type `bitstring` (from `f`'s output type).
#[test]
fn init_te_from_sig_types_signature_equations() {
    use tamarin_term::function_symbols::{Constructability, FunSym, Privacy};
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::f_app;

    let f = NoEqSym::new(
        b"f".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let g = NoEqSym::new(
        b"g".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let mut sig = tamarin_term::maude_sig::MaudeSig::default();
    sig.st_fun_syms.insert(f);
    sig.st_fun_syms.insert(g);
    let x = LVar::new("x", LSort::Msg, 0);
    let lhs: tamarin_term::lterm::LNTerm = f_app(
        FunSym::NoEq(g),
        vec![f_app(FunSym::NoEq(f), vec![var_term(x)])],
    );
    sig.st_rules.insert(CtxtStRule::new(
        lhs,
        StRhs {
            positions: vec![vec![0, 0]],
            term: var_term(x),
        },
    ));

    let env = init_te_from_sig(
        &sig,
        &[(
            "f".to_string(),
            vec![Some("bitstring".to_string())],
            Some("bitstring".to_string()),
        )],
    )
    .unwrap();
    assert_eq!(
        env.funs.get(&UserDefinedSym::NoEqUser(g)),
        Some(&(vec![Some("bitstring".to_string())], None)),
        "g must learn its argument type from f's declared output type"
    );
    // The equation's variable stays in `vars` (HS clears `vars` per
    // process, not in `initTEFromSig`), typed by `f`'s argument type.
    assert_eq!(env.vars.get(&x), Some(&Some("bitstring".to_string())));
}
#[test]
fn deep_polymorphic_type_inference_uses_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut t: SapicTerm = tamarin_term::lterm::pub_term("a");
        for _ in 0..20_000 {
            t = tamarin_term::term::f_app(tamarin_term::function_symbols::FunSym::List, vec![t]);
        }
        let mut env = TypingEnvironment {
            vars: BTreeMap::new(),
            funs: BTreeMap::new(),
            events: BTreeMap::new(),
        };
        let (typed, ty) = type_with(&mut env, &t, &None).unwrap();
        assert_eq!(typed, t);
        assert_eq!(ty, None);
        drop((typed, t));
    });
}
fn reference_type_with(
    env: &mut TypingEnvironment,
    t: &SapicTerm,
    tt: &SapicType,
) -> Result<(SapicTerm, SapicType), String> {
    match t {
        VTerm::Lit(Lit::Var(v)) => {
            let lvar = &v.var;
            // CASE: variable.
            let stype = if lvar.sort == LSort::Pub {
                None
            } else {
                match env.vars.get(lvar) {
                    None => return Err(format!("unbound variable {lvar:?}")),
                    Some(ty) => ty.clone(),
                }
            };
            let merged = sqcap(&stype, tt)?;
            env.vars.insert(*lvar, merged.clone());
            Ok((var_term(SapicLVar::new(*lvar, merged.clone())), merged))
        }
        VTerm::App(sym, args) => {
            use tamarin_term::function_symbols::FunSym;
            match sym {
                // HS `typeWith` dispatches on `viewTerm2 t`: a NoEq application
                // whose head is one of the SPECIAL symbols (`pair`, `exp`, `inv`,
                // `pmult`, `diff`, `one`, `natOne`, `dhNeutral`) does NOT view as
                // `FAppNoEq` (Term/Raw.hs:191-204) — it views as its own
                // constructor (`FPair`, `FExp`, …).  None of those match the
                // `FAppNoEq fs ts` case (Typing.hs:63-124, see line 83), so they fall through to
                // the polymorphic `FApp fs ts <- viewTerm t` branch (Typing.hs:63-124, see line 102)
                // which types arguments with `Nothing` and learns NO function
                // type.  Crucially this means pairs (`<a,b>`) do NOT back-propagate
                // an argument type onto `a`/`b` — matching HS, which keeps
                // tuple-component variables untyped.
                FunSym::NoEq(fs) if !is_special_viewterm2_sym(fs) => {
                    let n = fs.arity;
                    // HS keys the typing environment by `NoEqUser fs`
                    // (Typing.hs:63-124, see line 83).
                    let key = UserDefinedSym::NoEqUser(*fs);
                    // First pass: refine output type from target.
                    let (intypes1, outtype1) = get_fun(env, n, &key);
                    let mintype1 = sqcap(&outtype1, tt)?;
                    insert_fun(env, &key, (intypes1.clone(), mintype1))?;
                    // Type args (discard results, just to learn input types).
                    let ts: Vec<SapicTerm> = args.to_vec();
                    let mut ptypes: Vec<SapicType> = Vec::with_capacity(ts.len());
                    for (a, want) in ts.iter().zip(intypes1.iter()) {
                        let (_, ty) = reference_type_with(env, a, want)?;
                        ptypes.push(ty);
                    }
                    // Recompute output type, having learnt arg types.
                    let (intypes2, outtype2) = get_fun(env, n, &key);
                    let mintype2 = sqcap(&outtype2, tt)?;
                    insert_fun(env, &key, (ptypes, mintype2))?;
                    // Type args for real.
                    let mut ts_new: Vec<SapicTerm> = Vec::with_capacity(ts.len());
                    let mut ptypes2: Vec<SapicType> = Vec::with_capacity(ts.len());
                    for (a, want) in ts.iter().zip(intypes2.iter()) {
                        let (a_new, ty) = reference_type_with(env, a, want)?;
                        ts_new.push(a_new);
                        ptypes2.push(ty);
                    }
                    insert_fun(env, &key, (ptypes2, outtype2.clone()))?;
                    Ok((tamarin_term::term::f_app(*sym, ts_new), outtype2))
                }
                // list / AC / C symbol: polymorphic, type args with Nothing.
                _ => {
                    let mut ts_new = Vec::with_capacity(args.len());
                    for a in args.iter() {
                        let (a_new, _) = reference_type_with(env, a, &None)?;
                        ts_new.push(a_new);
                    }
                    Ok((tamarin_term::term::f_app(*sym, ts_new), None))
                }
            }
        }
        // Constant literal: never occurs as the variable/funapp cases; type Nothing.
        VTerm::Lit(Lit::Con(_)) => Ok((t.clone(), None)),
    }
}
#[test]
fn deep_ordinary_inference_reuses_unchanged_visits() {
    use tamarin_term::function_symbols::{Constructability, FunSym, NdcState, Privacy};
    tamarin_test_support::on_stack(256 * 1024, || {
        let symbol = NoEqSym {
            name: b"deep_inference",
            arity: 1,
            privacy: Privacy::Public,
            constructability: Constructability::Constructor,
            ndc: NdcState::NotNdc,
        };
        for declared in [false, true] {
            let x = LVar::new("x", LSort::Msg, 0);
            let ty = declared.then(|| "a".to_string());
            let mut term = var_term(SapicLVar::new(x, None));
            for _ in 0..20_000 {
                term = tamarin_term::term::f_app(FunSym::NoEq(symbol), vec![term]);
            }
            let mut env = TypingEnvironment {
                vars: [(x, None)].into(),
                funs: if declared {
                    [(
                        UserDefinedSym::NoEqUser(symbol),
                        (vec![ty.clone()], ty.clone()),
                    )]
                    .into()
                } else {
                    BTreeMap::new()
                },
                events: BTreeMap::new(),
            };
            let (typed, actual_ty) = type_with(&mut env, &term, &ty).unwrap();
            assert_eq!(actual_ty, ty);
            assert_eq!(env.vars[&x], ty);
            assert_eq!(tamarin_term::term::term_depth(&typed), 20_001);
        }
    });
}

#[test]
fn branching_inference_matches_two_pass_reference() {
    use tamarin_term::function_symbols::{Constructability, FunSym, NdcState, Privacy};
    use tamarin_term::term::{f_app, f_app_list};
    let symbol = |name, arity| NoEqSym {
        name,
        arity,
        privacy: Privacy::Public,
        constructability: Constructability::Constructor,
        ndc: NdcState::NotNdc,
    };
    let symbols = [
        symbol(b"cache_f", 1),
        symbol(b"cache_g", 1),
        symbol(b"cache_h", 2),
    ];
    let vars = [
        LVar::new("x", LSort::Msg, 0),
        LVar::new("y", LSort::Msg, 0),
        LVar::new("p", LSort::Pub, 0),
    ];
    fn term(seed: &mut u64, depth: usize, syms: &[NoEqSym; 3], vars: &[LVar; 3]) -> SapicTerm {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let choice = (*seed >> 32) as usize;
        if depth == 0 || choice % 7 < 3 {
            return var_term(SapicLVar::new(vars[choice % 3], None));
        }
        let left = term(seed, depth - 1, syms, vars);
        match choice % 7 {
            3 | 4 => f_app(FunSym::NoEq(syms[choice % 7 - 3]), vec![left]),
            5 => f_app(
                FunSym::NoEq(syms[2]),
                vec![left, term(seed, depth - 1, syms, vars)],
            ),
            _ => f_app_list(vec![left, term(seed, depth - 1, syms, vars)]),
        }
    }
    // Rebuilding from the FINAL environment would incorrectly type the
    // first x: list arguments are visited once, left to right, and f(x)
    // only teaches x's type after the earlier occurrence was constructed.
    let x = var_term(SapicLVar::new(vars[0], None));
    let typed_x = var_term(SapicLVar::new(vars[0], Some("a".into())));
    let mut snapshot_env = TypingEnvironment {
        vars: [(vars[0], None)].into(),
        funs: [(
            UserDefinedSym::NoEqUser(symbols[0]),
            (vec![Some("a".into())], None),
        )]
        .into(),
        events: BTreeMap::new(),
    };
    let input = f_app_list(vec![
        x.clone(),
        f_app(FunSym::NoEq(symbols[0]), vec![x.clone()]),
    ]);
    assert_eq!(
        type_with(&mut snapshot_env, &input, &None).unwrap().0,
        f_app_list(vec![x, f_app(FunSym::NoEq(symbols[0]), vec![typed_x])])
    );
    assert_eq!(snapshot_env.vars[&vars[0]], Some("a".into()));

    for case in 0..1000u64 {
        let t = term(&mut (case + 1), 4, &symbols, &vars);
        for target in [None, Some("a".to_string()), Some("b".to_string())] {
            let make_env = || {
                let mut env = TypingEnvironment {
                    vars: [(vars[0], None), (vars[1], Some("a".to_string()))].into(),
                    funs: BTreeMap::new(),
                    events: BTreeMap::new(),
                };
                if case % 2 == 0 {
                    env.funs.insert(
                        UserDefinedSym::NoEqUser(symbols[0]),
                        (vec![Some("a".to_string())], None),
                    );
                }
                if case % 3 == 0 {
                    env.funs.insert(
                        UserDefinedSym::NoEqUser(symbols[1]),
                        (vec![None], Some("b".to_string())),
                    );
                }
                if case % 5 == 0 {
                    env.vars.remove(&vars[1]);
                }
                env
            };
            let mut actual = make_env();
            let mut expected = make_env();
            assert_eq!(
                type_with(&mut actual, &t, &target),
                reference_type_with(&mut expected, &t, &target),
                "case {case}: {t:?}"
            );
            assert_eq!(actual.vars, expected.vars, "case {case}: variables");
            assert_eq!(actual.funs, expected.funs, "case {case}: functions");
        }
    }
}

#[test]
fn ordinary_function_inference_matches_two_pass_reference() {
    use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
    use tamarin_term::term::f_app;
    let symbol = NoEqSym {
        name: b"test_inference",
        arity: 1,
        privacy: Privacy::Public,
        constructability: Constructability::Constructor,
        ndc: tamarin_term::function_symbols::NdcState::NotNdc,
    };
    for depth in [0, 1, 4, 10] {
        for initial in [None, Some("a".to_string())] {
            for target in [None, Some("a".to_string()), Some("b".to_string())] {
                let v = LVar::new("x", LSort::Msg, 0);
                let mut t = var_term(SapicLVar::new(v, initial.clone()));
                for _ in 0..depth {
                    t = f_app(FunSym::NoEq(symbol), vec![t]);
                }
                let env = || TypingEnvironment {
                    vars: [(v, initial.clone())].into(),
                    funs: BTreeMap::new(),
                    events: BTreeMap::new(),
                };
                let mut actual = env();
                let mut expected = env();
                assert_eq!(
                    type_with(&mut actual, &t, &target),
                    reference_type_with(&mut expected, &t, &target)
                );
                assert_eq!(actual.vars, expected.vars);
                assert_eq!(actual.funs, expected.funs);
            }
        }
    }
}
