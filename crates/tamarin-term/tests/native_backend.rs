#![cfg(feature = "lean-unification")]

use std::sync::Arc;
use tamarin_term::algebra_backend::AlgebraBackend;
use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle, MaudePool, SharedMaudeCaches};
use tamarin_term::maude_sig::{mset_maude_sig, pair_maude_sig};
use tamarin_term::rewriting::Equal;
use tamarin_term::term::{f_app_ac, Term};
use tamarin_term::vterm::Lit;

const MISSING: &str = "/nonexistent/tamarin-native-only-must-not-start-maude";

fn native() -> MaudeHandle {
    MaudeHandle::start_with_backend(MISSING, mset_maude_sig(), AlgebraBackend::NativeOnly).unwrap()
}

fn sum(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_ac(AcSym::Union, vec![a, b])
}

fn variable(name: &str) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
}

#[test]
fn native_only_solves_supported_ac_without_any_binary() {
    let h = native();
    let x = LVar::new("x", LSort::Msg, 0);
    let rhs = sum(pub_term("a"), sum(pub_term("b"), pub_term("b")));
    let eq = Equal {
        lhs: sum(variable("x"), pub_term("a")),
        rhs,
    };
    let answers = h.unify(std::slice::from_ref(&eq)).unwrap();
    assert_eq!(answers, vec![vec![(x, sum(pub_term("b"), pub_term("b")))]]);
    assert_eq!(h.unify(&[eq]).unwrap(), answers); // cached, still native
    let unequal = Equal {
        lhs: sum(pub_term("a"), pub_term("a")),
        rhs: sum(pub_term("a"), pub_term("b")),
    };
    assert!(h.unify(&[unequal]).unwrap().is_empty());
    let stats = h.stats();
    assert_eq!(stats.unify_count, 0);
    assert_eq!(stats.norm_count, 0);
    assert_eq!(stats.match_count, 0);
    assert_eq!(stats.var_count, 0);
    assert_eq!(stats.lean_unify_count, 3);
    h.check_backend_status().unwrap();
    h.kill_subprocess(); // safe without a child
}

#[test]
fn unsupported_unification_is_an_error_and_latches_across_clones() {
    let h = native();
    let clone = h.with_fresh_counter_from(7);
    let eq = Equal {
        // This input exceeds the matrix column budget and has no ground side.
        lhs: f_app_ac(
            AcSym::Union,
            (0..33).map(|i| variable(&format!("v{i}"))).collect(),
        ),
        rhs: sum(variable("w"), variable("z")),
    };
    assert!(matches!(
        h.unify(&[eq]),
        Err(MaudeError::UnsupportedOperation("AC/C unification"))
    ));
    assert!(clone.check_backend_status().is_err());
    assert!(
        clone.unify(&[]).is_err(),
        "a recovered error must not become a later successful answer"
    );
}

#[test]
fn missing_operations_return_explicit_errors() {
    let h = native();
    assert!(matches!(
        h.variants(&tamarin_term::builtin::fst(variable("x"))),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
    let h = native();
    assert!(matches!(
        h.match_eqs(&[Equal {
            lhs: tamarin_term::builtin::fst(variable("subject")), // undeclared in this signature
            rhs: variable("x")
        }]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    let h = native();
    assert!(matches!(
        h.unify_via_maude(&[]),
        Err(MaudeError::UnsupportedOperation("Maude unification oracle"))
    ));
}

#[test]
fn native_unify_keeps_independent_and_shared_witnesses_at_max_index() {
    let handle =
        MaudeHandle::start_with_backend(MISSING, pair_maude_sig(), AlgebraBackend::NativeOnly)
            .unwrap();
    let x = LVar::new("w", LSort::Msg, 0);
    let y = LVar::new("w", LSort::Msg, 1);
    let result = LVar::new("w", LSort::Msg, u64::MAX);
    let v = |x| Term::Lit(Lit::Var(x));
    let rhs = tamarin_term::builtin::pair(v(x), tamarin_term::builtin::pair(v(y), v(x)));
    let answers = handle
        .unify(&[Equal {
            lhs: v(result),
            rhs,
        }])
        .unwrap();
    assert_eq!(answers.len(), 1);
    let arm =
        tamarin_term::subst_vfresh::LNSubstVFresh::from_list(answers.into_iter().next().unwrap());
    let Some(Term::Lit(Lit::Var(a))) = arm.image_of(&x) else {
        panic!("missing x witness")
    };
    let Some(Term::Lit(Lit::Var(b))) = arm.image_of(&y) else {
        panic!("missing y witness")
    };
    assert_ne!(a, b);
    for witness in [a, b] {
        assert!(![x, y, result].contains(witness));
    }
    assert_eq!(
        arm.image_of(&result),
        Some(&tamarin_term::builtin::pair(
            v(*a),
            tamarin_term::builtin::pair(v(*b), v(*a))
        ))
    );
    handle.check_backend_status().unwrap();
}

#[test]
fn native_handles_keep_existing_free_fast_paths() {
    let h = MaudeHandle::start_with_backend(MISSING, pair_maude_sig(), AlgebraBackend::NativeOnly)
        .unwrap();
    assert_eq!(h.reduce(&pub_term("a")).unwrap(), pub_term("a"));
    assert_eq!(h.unify(&[]).unwrap(), vec![vec![]]);
    assert_eq!(
        h.match_eqs(&[Equal {
            lhs: pub_term("a"),
            rhs: pub_term("a")
        }])
        .unwrap(),
        vec![vec![]]
    );
    h.check_backend_status().unwrap();
}

#[test]
fn pool_members_preserve_selection_and_share_failure_latch() {
    let caches = Arc::new(SharedMaudeCaches::default());
    let h = MaudeHandle::start_with_backend_and_caches(
        MISSING,
        mset_maude_sig(),
        AlgebraBackend::NativeOnly,
        caches.clone(),
    )
    .unwrap();
    let pool = MaudePool::new_with_backend(
        MISSING,
        mset_maude_sig(),
        2,
        caches,
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let first = pool.acquire();
    let second = pool.try_acquire().unwrap();
    assert_eq!(first.backend(), AlgebraBackend::NativeOnly);
    assert_eq!(second.backend(), AlgebraBackend::NativeOnly);
    assert!(second
        .variants(&tamarin_term::builtin::fst(variable("x")))
        .is_err());
    assert!(first.check_backend_status().is_err());
    assert!(h.check_backend_status().is_err());
}

#[test]
fn pairing_normalization_and_rigid_literal_binding_are_native() {
    let h = MaudeHandle::start_with_backend(MISSING, pair_maude_sig(), AlgebraBackend::NativeOnly)
        .unwrap();
    let term =
        tamarin_term::builtin::fst(tamarin_term::builtin::pair(pub_term("a"), pub_term("b")));
    assert_eq!(h.reduce(&term).unwrap(), pub_term("a"));
    assert_eq!(h.stats().norm_count, 0);
    let h = native();
    let patterns = std::collections::BTreeSet::from([("x", 0)]);
    assert_eq!(
        h.match_eqs_skolemize_both(
            &[Equal {
                lhs: variable("x"),
                rhs: pub_term("a")
            }],
            &patterns
        )
        .unwrap(),
        vec![vec![(LVar::new("x", LSort::Msg, 0), pub_term("a"))]]
    );
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn pairing_variants_preserve_correlations_and_freshness_without_maude() {
    use tamarin_term::builtin::{fst, pair, snd};
    use tamarin_term::term::f_app_list;
    let h = MaudeHandle::start_with_backend(MISSING, pair_maude_sig(), AlgebraBackend::NativeOnly)
        .unwrap();
    let x = LVar::new("original_name", LSort::Msg, 17);
    let vx = Term::Lit(Lit::Var(x));
    for project in [fst, snd] {
        let q = f_app_list(vec![vx.clone(), project(vx.clone()), project(vx.clone())]);
        let arms = h.variants(&q).unwrap();
        assert_eq!(arms.len(), 2);
        assert!(arms[0].is_empty());
        let [(key, Term::App(_, children))] = arms[1].as_slice() else {
            panic!("{arms:?}")
        };
        assert_eq!(*key, x);
        let [Term::Lit(Lit::Var(a)), Term::Lit(Lit::Var(b))] = children.as_ref() else {
            panic!()
        };
        assert_ne!(a, b);
        assert_ne!(*a, x);
        assert_ne!(*b, x);
        assert_eq!(a.sort, LSort::Msg);
        assert_eq!(b.sort, LSort::Msg);
        assert_eq!(
            h.reduce(&project(pair(children[0].clone(), children[1].clone())))
                .unwrap(),
            if project(vx.clone()) == fst(vx.clone()) {
                children[0].clone()
            } else {
                children[1].clone()
            }
        );
    }
    let query = f_app_list(vec![vx.clone(), pair(vx.clone(), vx)]);
    assert_eq!(h.variants(&query).unwrap(), vec![vec![]]);
    assert_eq!(h.stats().var_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn pairing_adapter_rejects_queries_outside_the_proven_fragment() {
    use tamarin_term::builtin::{fst, pair, snd};
    use tamarin_term::function_symbols::{pair_sym, FunSym};
    use tamarin_term::lean_unification::{pairing_variants, Error, Outcome};
    use tamarin_term::term::f_app_list;
    let sig = pair_maude_sig();
    let x = variable("x");
    let y = variable("y"); // same index, different full identity
    let rejected = [
        f_app_list(vec![x.clone(), fst(y)]),
        f_app_list(vec![fst(x.clone()), snd(x.clone())]),
        fst(fst(x.clone())),
        Term::Lit(Lit::Var(LVar::new("natural", LSort::Nat, 0))),
        Term::Lit(Lit::Con(tamarin_term::lterm::Name::new(
            tamarin_term::lterm::NameTag::Nat,
            "1",
        ))),
        fst(Term::Lit(Lit::Var(LVar::new("x", LSort::Pub, 0)))),
        pair(
            x.clone(),
            Term::Lit(Lit::Var(LVar::new("n", LSort::Node, 0))),
        ),
        Term::App(FunSym::NoEq(pair_sym()), vec![x].into()),
    ];
    for query in rejected {
        assert_eq!(
            pairing_variants(&sig, &query).unwrap(),
            Outcome::Unsupported,
            "{query:?}"
        );
    }
    let mut extended = sig.clone();
    extended.enable_diff = true;
    assert_eq!(
        pairing_variants(&extended, &pub_term("a")).unwrap(),
        Outcome::Unsupported
    );
    let last_representable = fst(Term::Lit(Lit::Var(LVar::new(
        "x",
        LSort::Msg,
        u64::MAX - 2,
    ))));
    assert!(matches!(
        pairing_variants(&sig, &last_representable).unwrap(),
        Outcome::Complete(_)
    ));
    let too_large = fst(Term::Lit(Lit::Var(LVar::new(
        "x",
        LSort::Msg,
        u64::MAX - 1,
    ))));
    assert_eq!(
        pairing_variants(&sig, &too_large),
        Err(Error::FreshVariableOverflow)
    );
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    assert!(matches!(
        h.variants(&too_large),
        Err(MaudeError::NativeFailure(_))
    ));
    assert!(h.check_backend_status().is_err());
}

#[test]
fn pairing_multiset_variants_cover_constructor_queries_without_maude() {
    use tamarin_term::builtin::{fst, pair};
    use tamarin_term::term::f_app_list;
    let sig = pair_maude_sig().merge(mset_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let x = variable("x");
    let nested = pair(sum(x.clone(), pub_term("a")), sum(pub_term("b"), x.clone()));
    let query = f_app_list(vec![
        x.clone(),
        nested.clone(),
        sum(nested.clone(), x.clone()),
    ]);
    assert_eq!(h.variants(&query).unwrap(), vec![vec![]]);
    let query = f_app_list(vec![x.clone(), fst(x.clone()), fst(x)]);
    assert_eq!(h.variants(&query).unwrap().len(), 2);
    assert_eq!(
        h.reduce(&fst(pair(nested.clone(), pub_term("a")))).unwrap(),
        nested
    );
    assert_eq!(h.stats().var_count, 0);
    assert_eq!(h.stats().norm_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn union_variant_gate_rejects_undeclared_or_malformed_operators() {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::lean_unification::{pairing_variants, Outcome};
    let sig = pair_maude_sig().merge(mset_maude_sig());
    let union = sum(variable("x"), pub_term("a"));
    assert_eq!(
        pairing_variants(&pair_maude_sig(), &union).unwrap(),
        Outcome::Unsupported
    );
    for invalid in [
        Term::App(FunSym::Ac(AcSym::Union), vec![].into()),
        Term::App(FunSym::Ac(AcSym::Union), vec![pub_term("a")].into()),
        f_app_ac(AcSym::Xor, vec![pub_term("a"), pub_term("b")]),
        sum(variable("x"), tamarin_term::builtin::fst(variable("y"))),
    ] {
        assert_eq!(
            pairing_variants(&sig, &invalid).unwrap(),
            Outcome::Unsupported
        );
    }
    let mut extra_equations = sig.clone();
    extra_equations.enable_xor = true;
    assert_eq!(
        pairing_variants(&extra_equations, &union).unwrap(),
        Outcome::Unsupported
    );
}

#[test]
fn hybrid_reflexive_recipe_admits_unsplittable_ac_operands() {
    use tamarin_term::lean_unification::{unify, Outcome};
    let h = native();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, 7)));
    let terms = [sum(x.clone(), pub_term("a")), sum(x.clone(), pub_term("b"))];
    let eqs: Vec<_> = terms
        .iter()
        .map(|t| Equal {
            lhs: t.clone(),
            rhs: t.clone(),
        })
        .collect();
    assert_eq!(h.unify(&eqs).unwrap(), vec![vec![]]);
    assert_eq!(h.unify(&eqs).unwrap(), vec![vec![]]); // cached identity remains scoped correctly
    assert_eq!(h.stats().unify_count, 0);
    assert_eq!(h.stats().lean_unify_count, 2);
    let split = sum(variable("msg"), pub_term("a"));
    assert_eq!(
        unify(&[Equal {
            lhs: split.clone(),
            rhs: split
        }])
        .unwrap(),
        Outcome::Unsupported
    );
    for term in [
        sum(x.clone(), x.clone()),
        sum(x.clone(), tamarin_term::lterm::fresh_term("a")),
        f_app_ac(AcSym::Mult, vec![x.clone(), pub_term("a")]),
    ] {
        assert_eq!(
            unify(&[Equal {
                lhs: term.clone(),
                rhs: term
            }])
            .unwrap(),
            Outcome::Complete(vec![vec![]])
        );
    }
    let same_index_different_name = Equal {
        lhs: sum(x.clone(), pub_term("a")),
        rhs: sum(
            Term::Lit(Lit::Var(LVar::new("y", LSort::Fresh, 7))),
            pub_term("a"),
        ),
    };
    assert_eq!(
        unify(&[same_index_different_name]).unwrap(),
        Outcome::Unsupported
    );
    let different = Equal {
        lhs: sum(x.clone(), pub_term("a")),
        rhs: sum(x, pub_term("b")),
    };
    assert_eq!(unify(&[different]).unwrap(), Outcome::Unsupported);
    h.check_backend_status().unwrap();
}

#[test]
fn declared_free_and_ac_extensions_use_the_generic_constructor_contract() {
    use tamarin_term::builtin::{fst, pair};
    use tamarin_term::function_symbols::{
        AcFctSym, Constructability, FunSym, NdcState, NoEqSym, Privacy,
    };
    use tamarin_term::lean_unification::{pairing_reduce, pairing_variants, Outcome};
    use tamarin_term::maude_sig::{hash_maude_sig, sym_enc_maude_sig};
    use tamarin_term::term::f_app_list;
    let wrap = NoEqSym::new(b"wrap", 1, Privacy::Private, Constructability::Constructor);
    let combine = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let mut sig = pair_maude_sig().merge(hash_maude_sig());
    sig.st_fun_syms.insert(wrap);
    sig.st_ac_fun_syms.insert(combine);
    // Deliberately leave derived caches stale: admission reads declarations.
    let child = f_app_ac(AcSym::AcFct(combine), vec![variable("x"), pub_term("a")]);
    let term = Term::App(FunSym::NoEq(wrap), vec![child.clone()].into());
    let query = f_app_list(vec![term.clone(), child.clone(), variable("x")]);
    assert_eq!(
        pairing_variants(&sig, &query).unwrap(),
        Outcome::Complete(vec![vec![]])
    );
    assert_eq!(
        pairing_reduce(&sig, &fst(pair(term.clone(), child))).unwrap(),
        Some(term.clone())
    );
    for bad in [
        Term::App(FunSym::NoEq(wrap), vec![].into()),
        Term::App(
            FunSym::NoEq(wrap.with_destructor()),
            vec![pub_term("a")].into(),
        ),
        Term::App(
            FunSym::Ac(AcSym::AcFct(combine)),
            vec![pub_term("a")].into(),
        ),
        Term::App(
            FunSym::Ac(AcSym::AcFct(combine.with_ndc(NdcState::IsNdc))),
            vec![pub_term("a"), pub_term("b")].into(),
        ),
    ] {
        assert_eq!(pairing_variants(&sig, &bad).unwrap(), Outcome::Unsupported);
    }
    assert_eq!(
        pairing_variants(&pair_maude_sig(), &term).unwrap(),
        Outcome::Unsupported
    );
    assert_eq!(
        pairing_variants(&sig.merge(sym_enc_maude_sig()), &term).unwrap(),
        Outcome::Unsupported
    );
}

#[test]
fn directional_ac_matching_preserves_subjects_and_shared_bindings_without_maude() {
    let h = native();
    let pattern = sum(variable("x"), pub_term("tail"));
    let subject = sum(pub_term("a"), pub_term("tail"));
    let eq = Equal {
        lhs: subject.clone(),
        rhs: pattern.clone(),
    };
    assert_eq!(
        h.match_eqs(&[eq.clone(), eq]).unwrap(),
        vec![vec![(LVar::new("x", LSort::Msg, 0), pub_term("a"))]]
    );
    assert!(h
        .match_eqs(&[Equal {
            lhs: sum(pub_term("a"), pub_term("a")),
            rhs: pattern.clone(),
        }])
        .unwrap()
        .is_empty());
    assert!(h
        .match_eqs(&[Equal {
            lhs: sum(pub_term("tail"), pub_term("tail")),
            rhs: f_app_ac(
                AcSym::Union,
                vec![variable("x"), pub_term("tail"), pub_term("tail")]
            ),
        }])
        .unwrap()
        .is_empty());
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
    // The variable in the subject stays rigid and retains its full identity.
    assert_eq!(
        h.match_eqs(&[Equal {
            lhs: sum(variable("y"), pub_term("tail")),
            rhs: pattern,
        }])
        .unwrap(),
        vec![vec![(LVar::new("x", LSort::Msg, 0), variable("y"))]]
    );
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn rigid_context_ac_matching_restores_full_subject_variable_identities() {
    let h = native();
    let x = LVar::new("x", LSort::Msg, 0);
    let rigid = LVar::new("rigid", LSort::Fresh, u64::MAX);
    let vr = Term::Lit(Lit::Var(rigid));
    let answer = h
        .match_eqs_skolemize_both(
            &[Equal {
                lhs: sum(variable("x"), vr.clone()),
                rhs: f_app_ac(AcSym::Union, vec![vr.clone(), vr.clone(), pub_term("a")]),
            }],
            &[(x.name, x.idx)].into_iter().collect(),
        )
        .unwrap();
    assert_eq!(answer, vec![vec![(x, sum(vr, pub_term("a")))]]);
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn rigid_matching_skolem_ids_cannot_alias_original_names() {
    let h = native();
    let x = LVar::new("x", LSort::Msg, 0);
    let rigid = Term::Lit(Lit::Var(LVar::new("rigid", LSort::Pub, 0)));
    let original = pub_term("__sk0_rigid_0_P");
    let answer = h
        .match_eqs_skolemize_both(
            &[Equal {
                lhs: sum(variable("x"), rigid.clone()),
                rhs: sum(rigid, original.clone()),
            }],
            &[(x.name, x.idx)].into_iter().collect(),
        )
        .unwrap();
    assert_eq!(answer, vec![vec![(x, original)]]);
}

#[test]
fn multi_variable_and_repeated_ac_patterns_enumerate_all_matches_without_maude() {
    let h = native();
    let a = pub_term("a");
    let b = pub_term("b");
    let x = LVar::new("x", LSort::Msg, 7);
    let y = LVar::new("y", LSort::Msg, 7);
    let z = LVar::new("z", LSort::Msg, 7);
    let var = |v| Term::Lit(Lit::Var(v));
    let run = |pattern: Vec<LNTerm>, subject: Vec<LNTerm>| {
        h.match_eqs(&[Equal {
            lhs: f_app_ac(AcSym::Union, subject),
            rhs: f_app_ac(AcSym::Union, pattern),
        }])
        .unwrap()
    };
    let mut expected = vec![
        vec![(x, a.clone()), (y, b.clone())],
        vec![(x, b.clone()), (y, a.clone())],
    ];
    expected.sort();
    assert_eq!(
        run(vec![var(x), var(y)], vec![a.clone(), b.clone()]),
        expected
    );
    assert_eq!(
        run(vec![var(x), var(x)], vec![a.clone(), a.clone()]),
        vec![vec![(x, a.clone())]]
    );
    assert!(run(vec![var(x), var(x)], vec![a.clone(), b.clone()]).is_empty());
    let repeated = run(
        vec![var(x), var(x), var(y)],
        vec![a.clone(), a.clone(), b.clone(), b.clone()],
    );
    assert_eq!(repeated.len(), 2);
    for answer in &repeated {
        assert_eq!(answer.len(), 2);
        assert!(answer.iter().all(|(v, _)| *v == x || *v == y));
    }
    assert_eq!(
        run(
            vec![var(x), var(y), var(z)],
            vec![a.clone(), b.clone(), pub_term("c")]
        )
        .len(),
        6
    );
    assert_eq!(
        run(
            vec![var(x), var(y)],
            vec![a, b, pub_term("c"), pub_term("d")]
        )
        .len(),
        14
    );
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn repeated_ac_collectors_refute_wide_rigid_remainders() {
    let handle = native();
    let pattern = f_app_ac(
        AcSym::Union,
        vec![variable("x"), variable("x"), variable("y")],
    );
    for width in [9, 65] {
        let subject = (0..width)
            .map(|idx| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, idx))))
            .collect();
        let equation = Equal {
            lhs: f_app_ac(AcSym::Union, subject),
            rhs: pattern.clone(),
        };
        assert!(!handle
            .has_match_eqs(std::slice::from_ref(&equation))
            .unwrap());
        assert!(handle.match_eqs(&[equation]).unwrap().is_empty());
    }
    assert_eq!(handle.stats().match_count, 0);
}

#[test]
fn a_live_repeated_collector_partition_still_obeys_the_selection_limit() {
    let pattern = (0u64..65)
        .map(|i| Term::Lit(Lit::Var(LVar::new("key", LSort::Msg, i.saturating_sub(1)))))
        .collect();
    // All 64 variables could bind the same rigid factor. The refutation must
    // let the original admission limit decide whether to enumerate that answer.
    let equation = Equal {
        lhs: f_app_ac(AcSym::Union, vec![variable("rigid"); 65]),
        rhs: f_app_ac(AcSym::Union, pattern),
    };
    assert!(matches!(
        native().match_eqs(&[equation]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
}

#[test]
fn repeated_ac_collectors_count_whole_factors_after_structural_selection() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let handle = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let pattern = f_app_ac(
        AcSym::Union,
        vec![
            hash(variable("z")),
            variable("x"),
            variable("x"),
            variable("y"),
        ],
    );
    let rigid = variable("r");
    let factor = hash(rigid.clone());
    // Picking either hash(r) for hash(z) removes the only duplicate.
    let mut subject = vec![factor.clone(), factor.clone()];
    subject.extend((0..8).map(|i| Term::Lit(Lit::Var(LVar::new("tail", LSort::Msg, i)))));
    let equation = |xs| Equal {
        lhs: f_app_ac(AcSym::Union, xs),
        rhs: pattern.clone(),
    };
    assert!(handle.match_eqs(&[equation(subject)]).unwrap().is_empty());

    // With a third copy, both remaining copies can form the shared image.
    let tail = variable("tail");
    let mut rows = handle
        .match_eqs(&[equation(vec![
            factor.clone(),
            factor.clone(),
            factor.clone(),
            tail.clone(),
        ])])
        .unwrap();
    assert_eq!(rows.len(), 1);
    let mut expected = vec![
        (LVar::new("x", LSort::Msg, 0), factor),
        (LVar::new("y", LSort::Msg, 0), tail),
        (LVar::new("z", LSort::Msg, 0), rigid),
    ];
    expected.sort();
    rows[0].sort();
    assert_eq!(rows[0], expected);
    assert_eq!(handle.stats().match_count, 0);
}

#[test]
fn repeated_narrow_variables_share_one_sorted_image_across_the_match() {
    use tamarin_term::lterm::fresh_term;
    let h = native();
    let x = LVar::new("v", LSort::Fresh, 7);
    let y = LVar::new("v", LSort::Msg, 7);
    let var = |v| Term::Lit(Lit::Var(v));
    let a = fresh_term("a");
    let b = pub_term("b");
    let c = pub_term("c");
    let pattern = f_app_ac(AcSym::Union, vec![var(x), var(x), var(y)]);
    let query = |factors| Equal {
        lhs: f_app_ac(AcSym::Union, factors),
        rhs: pattern.clone(),
    };
    let valid = query(vec![a.clone(), a.clone(), b.clone(), c.clone()]);
    let independent = Equal {
        lhs: sum(a.clone(), c.clone()),
        rhs: sum(var(x), c.clone()),
    };
    let mut answers = h.match_eqs(&[valid, independent]).unwrap();
    assert_eq!(answers.len(), 1);
    answers[0].sort();
    let mut expected = vec![(x, a.clone()), (y, sum(b.clone(), c))];
    expected.sort();
    assert_eq!(answers[0], expected);
    assert!(h
        .match_eqs(&[query(vec![a, b.clone(), b])])
        .unwrap()
        .is_empty());
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn mixed_sort_matching_restores_rigid_subject_variables() {
    let h = native();
    let p = LVar::new("p", LSort::Pub, 7);
    let x = LVar::new("x", LSort::Msg, 7);
    let rigid = LVar::new("rigid", LSort::Msg, 7);
    let var = |v| Term::Lit(Lit::Var(v));
    let a = pub_term("a");
    let bindable = [(p.name, p.idx), (x.name, x.idx)].into_iter().collect();
    let answer = h
        .match_eqs_skolemize_both(
            &[Equal {
                lhs: sum(var(p), var(x)),
                rhs: sum(var(rigid), a.clone()),
            }],
            &bindable,
        )
        .unwrap();
    let mut expected = vec![(p, a), (x, var(rigid))];
    expected.sort();
    assert_eq!(answer.len(), 1);
    let mut got = answer[0].clone();
    got.sort();
    assert_eq!(got, expected);
    let both = h
        .match_eqs(&[Equal {
            lhs: sum(pub_term("a"), pub_term("b")),
            rhs: sum(var(p), var(x)),
        }])
        .unwrap();
    assert_eq!(both.len(), 2);
    for (pub_image, msg_image) in [("a", "b"), ("b", "a")] {
        assert!(both
            .iter()
            .any(|arm| arm.contains(&(p, pub_term(pub_image)))
                && arm.contains(&(x, pub_term(msg_image)))));
    }
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn expensive_matching_is_explicitly_unsupported_not_unsatisfiable() {
    let h = native();
    let pattern = f_app_ac(
        AcSym::Union,
        vec![variable("x"), variable("y"), variable("z")],
    );
    let subject = f_app_ac(
        AcSym::Union,
        (0..8).map(|i| pub_term(format!("a{i}"))).collect(),
    );
    assert!(matches!(
        h.match_eqs(&[Equal {
            lhs: subject,
            rhs: pattern
        }]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    assert!(h.check_backend_status().is_err());
}

#[test]
fn multi_branch_matching_conjunctions_join_every_compatible_assignment() {
    let h = native();
    let x = variable("x");
    let y = variable("y");
    let z = variable("z");
    let first = Equal {
        lhs: sum(pub_term("a"), pub_term("b")),
        rhs: sum(x.clone(), y),
    };
    let second = Equal {
        lhs: sum(pub_term("a"), pub_term("c")),
        rhs: sum(x.clone(), z),
    };
    assert_eq!(
        h.match_eqs(&[first.clone(), second]).unwrap(),
        vec![vec![
            (LVar::new("x", LSort::Msg, 0), pub_term("a")),
            (LVar::new("y", LSort::Msg, 0), pub_term("b")),
            (LVar::new("z", LSort::Msg, 0), pub_term("c")),
        ]]
    );
    let impossible = Equal {
        lhs: sum(pub_term("c"), pub_term("d")),
        rhs: sum(x, variable("w")),
    };
    assert!(h.match_eqs(&[first, impossible]).unwrap().is_empty());
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn nested_free_matching_preserves_correlations_and_validates_declarations() {
    use tamarin_term::builtin::pair;
    let sig = pair_maude_sig().merge(mset_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let a = pub_term("a");
    let b = pub_term("b");
    let c = pub_term("c");
    let x = LVar::new("x", LSort::Msg, 7);
    let y = LVar::new("y", LSort::Msg, 7);
    let z = LVar::new("z", LSort::Msg, 7);
    let v = |var| Term::Lit(Lit::Var(var));
    let pattern = pair(pair(sum(v(x), v(y)), a.clone()), sum(v(x), v(z)));
    let subject = pair(
        pair(sum(a.clone(), b.clone()), a.clone()),
        sum(b.clone(), c.clone()),
    );
    let eqs = [Equal {
        lhs: subject,
        rhs: pattern,
    }];
    assert_eq!(
        h.match_eqs(&eqs).unwrap(),
        vec![vec![(x, b), (y, a), (z, c)]]
    );
    assert_eq!(h.stats().match_count, 0);
    assert!(native().match_eqs(&eqs).is_err());
}

#[test]
fn native_unification_joins_ground_sides_in_mixed_orientations() {
    let h = native();
    let a = pub_term("a");
    let b = pub_term("b");
    let x = variable("x");
    let y = variable("y");
    let first = Equal {
        lhs: sum(x.clone(), y.clone()),
        rhs: sum(a.clone(), b.clone()),
    };
    assert_eq!(h.unify(std::slice::from_ref(&first)).unwrap().len(), 2);
    let second = Equal {
        lhs: sum(a.clone(), a.clone()),
        rhs: sum(x.clone(), x),
    };
    assert_eq!(
        h.unify(&[first, second]).unwrap(),
        vec![vec![
            (LVar::new("x", LSort::Msg, 0), a),
            (LVar::new("y", LSort::Msg, 0), b)
        ]]
    );
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn exact_fit_matches_larger_than_the_submultiset_search_limit() {
    let h = native();
    let product = |left: LNTerm, right: LNTerm, nl, nr| {
        f_app_ac(AcSym::Union, [vec![left; nl], vec![right; nr]].concat())
    };
    let a = pub_term("a");
    let b = pub_term("b");
    let x = variable("x");
    let y = variable("y");
    let pattern = product(x.clone(), y.clone(), 20, 20);
    let subject = product(a.clone(), b.clone(), 20, 20);
    let eq = Equal {
        lhs: subject.clone(),
        rhs: pattern.clone(),
    };
    let xvar = LVar::new("x", LSort::Msg, 0);
    let yvar = LVar::new("y", LSort::Msg, 0);
    let mut expected = vec![
        vec![(xvar, a.clone()), (yvar, b.clone())],
        vec![(xvar, b.clone()), (yvar, a.clone())],
    ];
    expected.sort();
    assert_eq!(h.match_eqs(std::slice::from_ref(&eq)).unwrap(), expected);
    assert_eq!(h.unify(&[eq]).unwrap(), expected);
    for impossible in [
        Equal {
            lhs: subject,
            rhs: product(x, y, 21, 20),
        },
        Equal {
            lhs: product(a, b, 21, 19),
            rhs: pattern,
        },
    ] {
        assert!(h
            .match_eqs(std::slice::from_ref(&impossible))
            .unwrap()
            .is_empty());
        assert!(h.unify(&[impossible]).unwrap().is_empty());
    }
    assert_eq!(h.stats().match_count, 0);
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn sorted_residuals_keep_distinct_variable_identities_and_reject_wide_images() {
    use tamarin_term::lterm::fresh_term;

    let h = native();
    let p = LVar::new("v", LSort::Pub, 9);
    let f = LVar::new("v", LSort::Fresh, 9);
    let a = pub_term("name");
    let b = fresh_term("name");
    let tail = pub_term("tail");
    let equations = [
        Equal {
            lhs: sum(a.clone(), tail.clone()),
            rhs: sum(Term::Lit(Lit::Var(p)), tail.clone()),
        },
        Equal {
            lhs: sum(b.clone(), tail.clone()),
            rhs: sum(Term::Lit(Lit::Var(f)), tail.clone()),
        },
    ];
    let mut bindings = h.match_eqs(&equations).unwrap();
    assert_eq!(bindings.len(), 1);
    bindings[0].sort();
    assert_eq!(bindings, vec![vec![(p, a.clone()), (f, b.clone())]]);
    for subject in [
        sum(b, tail.clone()),
        f_app_ac(AcSym::Union, vec![a.clone(), a, tail]),
    ] {
        let impossible = Equal {
            lhs: subject,
            rhs: equations[0].rhs.clone(),
        };
        assert!(h
            .unify(std::slice::from_ref(&impossible))
            .unwrap()
            .is_empty());
        assert!(h.match_eqs(&[impossible]).unwrap().is_empty());
    }
    assert_eq!(h.stats().match_count, 0);
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn cancellation_preserves_free_variables_and_joins_remaining_constraints() {
    let h = native();
    let (x, y, z) = (variable("x"), variable("y"), variable("z"));
    let (a, b) = (pub_term("a"), pub_term("b"));
    let product = |v: Vec<LNTerm>| f_app_ac(AcSym::Union, v);
    // x+y+z = z+a+b leaves z free in both answers.
    let split = Equal {
        lhs: product(vec![x.clone(), y.clone(), z.clone()]),
        rhs: product(vec![z.clone(), a.clone(), b.clone()]),
    };
    let vx = LVar::new("x", LSort::Msg, 0);
    let vy = LVar::new("y", LSort::Msg, 0);
    let vz = LVar::new("z", LSort::Msg, 0);
    let mut expected = vec![
        vec![(vx, a.clone()), (vy, b.clone())],
        vec![(vx, b.clone()), (vy, a.clone())],
    ];
    expected.sort();
    assert_eq!(h.unify(std::slice::from_ref(&split)).unwrap(), expected);
    // x+x = x+a forces x=a even though one occurrence of x cancels.
    let force = Equal {
        lhs: sum(x.clone(), a.clone()),
        rhs: sum(x.clone(), x.clone()),
    };
    // The previous equation left z free. This one binds it.
    let bind_z = Equal {
        lhs: sum(z.clone(), y.clone()),
        rhs: sum(y.clone(), b.clone()),
    };
    let eqs = [split, force, bind_z];
    assert_eq!(
        h.unify(&eqs).unwrap(),
        vec![vec![(vx, a), (vy, b.clone()), (vz, b)]]
    );
    assert_eq!(h.stats().unify_count, 0);
    assert!(h.stats().lean_unify_count >= 2);
}

#[test]
fn cancelled_empty_inventories_have_no_implicit_unit() {
    let h = native();
    let x = variable("x");
    let shared = sum(x.clone(), x);
    assert_eq!(
        h.unify(&[Equal {
            lhs: shared.clone(),
            rhs: shared.clone()
        }])
        .unwrap(),
        vec![vec![]]
    );
    for extra in [variable("y"), pub_term("a")] {
        let bigger = sum(shared.clone(), extra);
        for (lhs, rhs) in [(bigger.clone(), shared.clone()), (shared.clone(), bigger)] {
            assert!(h.unify(&[Equal { lhs, rhs }]).unwrap().is_empty());
        }
    }
    let incompatible = Equal {
        lhs: sum(shared.clone(), pub_term("a")),
        rhs: sum(shared, pub_term("b")),
    };
    assert!(h.unify(&[incompatible]).unwrap().is_empty());
    h.check_backend_status().unwrap();
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn two_sided_constraints_test_every_ground_branch_in_either_order() {
    let h = native();
    let (x, y) = (variable("x"), variable("y"));
    let (a, b) = (pub_term("a"), pub_term("b"));
    let split = Equal {
        lhs: sum(x.clone(), y.clone()),
        rhs: sum(a.clone(), b.clone()),
    };
    let check = Equal {
        lhs: sum(x.clone(), a.clone()),
        rhs: sum(y.clone(), b.clone()),
    };
    let expected = vec![vec![
        (LVar::new("x", LSort::Msg, 0), b.clone()),
        (LVar::new("y", LSort::Msg, 0), a.clone()),
    ]];
    assert_eq!(h.unify(&[split.clone(), check.clone()]).unwrap(), expected);
    assert_eq!(h.unify(&[check, split.clone()]).unwrap(), expected);
    assert!(h
        .unify(&[
            split,
            Equal {
                lhs: sum(x, a.clone()),
                rhs: sum(y, a)
            }
        ])
        .unwrap()
        .is_empty());
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn partially_grounded_constraint_is_solved_by_propagating_each_ground_match() {
    let h = native();
    let split = Equal {
        lhs: sum(variable("x"), variable("y")),
        rhs: sum(pub_term("a"), pub_term("b")),
    };
    let check = Equal {
        lhs: sum(variable("x"), pub_term("a")),
        rhs: sum(variable("z"), pub_term("b")),
    };
    let nested = Equal {
        lhs: tamarin_term::builtin::pair(split.lhs.clone(), check.lhs.clone()),
        rhs: tamarin_term::builtin::pair(split.rhs.clone(), check.rhs.clone()),
    };
    let mut answer = h.unify(&[split, check]).unwrap();
    assert_eq!(answer.len(), 1);
    answer[0].sort();
    assert_eq!(
        answer[0],
        vec![
            (LVar::new("x", LSort::Msg, 0), pub_term("b")),
            (LVar::new("y", LSort::Msg, 0), pub_term("a")),
            (LVar::new("z", LSort::Msg, 0), pub_term("a")),
        ]
    );
    let with_pairs = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(pair_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let mut nested_answer = with_pairs.unify(&[nested]).unwrap();
    assert_eq!(nested_answer.len(), 1);
    nested_answer[0].sort();
    assert_eq!(nested_answer, answer);
    assert_eq!(with_pairs.stats().unify_count, 0);
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn offset_witness_is_shared_after_factoring_and_scoped_to_the_answer() {
    use tamarin_term::builtin::pair;
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    let h = native().with_fresh_counter_next(2000);
    // One name/index collision and one same-sort name different from x.
    let x = LVar::new("x", LSort::Msg, 17);
    let y = LVar::new("y", LSort::Msg, 17);
    let alias = LVar::new("alias", LSort::Msg, 80);
    let retained = LVar::new("x", LSort::Msg, 81);
    let v = |v| Term::Lit(Lit::Var(v));
    let eq = Equal {
        lhs: sum(v(x), pub_term("a")),
        rhs: sum(v(y), pub_term("b")),
    };
    let factored = Equal {
        lhs: v(alias),
        rhs: pair(v(x), v(retained)),
    };
    let call = |eqs: &[Equal<LNTerm>]| {
        h.unify(eqs)
            .unwrap()
            .into_iter()
            .map(LNSubstVFresh::from_list)
            .collect::<Vec<_>>()
    };
    let answers = call(&[eq.clone(), factored]);
    assert_eq!(answers.len(), 2);
    let mut shared = 0;
    for arm in answers {
        let xr = arm.image_of(&x).unwrap();
        let yr = arm.image_of(&y).unwrap();
        let independent = arm.image_of(&retained).unwrap();
        assert_eq!(
            arm.image_of(&alias),
            Some(&pair(xr.clone(), independent.clone()))
        );
        let Term::Lit(Lit::Var(w)) = independent else {
            panic!("missing retained variable")
        };
        assert!(w.idx > retained.idx);
        let range = tamarin_term::vterm::vars_vterm(xr);
        match range.as_slice() {
            [] => {
                assert_eq!(xr, &pub_term("b"));
                assert_eq!(yr, &pub_term("a"));
            }
            [z] => {
                shared += 1;
                assert!(z.idx > retained.idx && z != w);
                assert_eq!(xr, &sum(pub_term("b"), v(*z)));
                assert_eq!(yr, &sum(pub_term("a"), v(*z)));
            }
            _ => panic!("unexpected witnesses: {range:?}"),
        }
    }
    assert_eq!(shared, 1);
    // Same residual, different factoring context. No reified witness leaks across calls.
    let plain = call(&[eq]);
    assert_eq!(plain.len(), 2);
    for arm in plain {
        assert!(arm.dom().all(|v| *v == x || *v == y));
    }
    assert_eq!(h.fresh_counter_peek(), 2000);
    assert_eq!(h.stats().unify_count, 0);
    assert_eq!(h.stats().lean_unify_count, 2);
    h.check_backend_status().unwrap();
}

#[test]
fn offset_fresh_indices_are_checked_at_the_word_limit() {
    let query = |idx| Equal {
        lhs: sum(
            Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, idx))),
            pub_term("a"),
        ),
        rhs: sum(variable("y"), pub_term("b")),
    };
    let h = native();
    let arms = h.unify(&[query(u64::MAX - 1)]).unwrap();
    assert!(arms
        .iter()
        .flatten()
        .flat_map(|(_, t)| tamarin_term::vterm::vars_vterm(t))
        .any(|v| v.idx == u64::MAX));
    assert!(h.unify(&[query(u64::MAX)]).is_err());
    assert!(h.check_backend_status().is_err());
}

#[test]
fn narrower_variable_cannot_receive_a_shared_ac_product() {
    let h = native();
    let equation = Equal {
        lhs: sum(
            Term::Lit(Lit::Var(LVar::new("x", LSort::Pub, 7))),
            pub_term("a"),
        ),
        rhs: sum(variable("y"), pub_term("b")),
    };
    let arms = h.unify(&[equation]).unwrap();
    let [arm] = arms.as_slice() else {
        panic!("expected only x=b, y=a");
    };
    assert!(arm.contains(&(LVar::new("x", LSort::Pub, 7), pub_term("b"))));
    assert!(arm.contains(&(LVar::new("y", LSort::Msg, 0), pub_term("a"))));
}

#[test]
fn constructor_variants_check_declared_operators_and_all_rule_heads() {
    use tamarin_term::builtin::{aenc, hash, pk, sdec, senc};
    use tamarin_term::maude_sig::{asym_enc_maude_sig, hash_maude_sig, sym_enc_maude_sig};
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::f_app_list;
    let mut sig = mset_maude_sig()
        .merge(asym_enc_maude_sig())
        .merge(sym_enc_maude_sig())
        .merge(hash_maude_sig());
    let x = variable("x");
    let k = pub_term("key");
    let safe = f_app_list(vec![
        x.clone(),
        aenc(sum(x.clone(), k.clone()), pk(k.clone())),
        senc(x.clone(), k.clone()),
    ]);
    let open = f_app_list(vec![x.clone(), hash(sdec(x.clone(), k.clone()))]);
    let h =
        MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap();
    assert_eq!(h.variants(&safe).unwrap(), vec![vec![]]);
    let narrowed = h.variants(&sdec(x.clone(), variable("y"))).unwrap();
    let left = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 1)));
    let right = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 2)));
    assert_eq!(
        narrowed,
        vec![
            vec![],
            vec![
                (LVar::new("x", LSort::Msg, 0), senc(left, right.clone())),
                (LVar::new("y", LSort::Msg, 0), right),
            ]
        ]
    );
    assert_eq!(h.stats().var_count, 0);
    assert!(matches!(
        h.variants(&open),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
    // Turning a former constructor into a defined head must invalidate the
    // identity recipe even if the caller didn't refresh derived symbol sets.
    sig.st_rules.insert(CtxtStRule::new(
        hash(hash(x.clone())),
        StRhs {
            positions: vec![vec![0, 0]],
            term: x.clone(),
        },
    ));
    let h =
        MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap();
    assert!(matches!(
        h.variants(&f_app_list(vec![x.clone(), pk(hash(x.clone()))])),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
    // A variable-headed rule can fire after any substitution.
    sig.st_rules.insert(CtxtStRule::new(
        x.clone(),
        StRhs {
            positions: vec![],
            term: k.clone(),
        },
    ));
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    assert!(matches!(
        h.variants(&k),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
}

#[test]
fn constructor_variants_decline_aliases_for_a_defined_operator() {
    use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    let mut sig = mset_maude_sig();
    let defined = NoEqSym::new(
        "read_back",
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    let alias = NoEqSym::new(
        "read-back",
        1,
        Privacy::Public,
        Constructability::Constructor,
    );
    sig.st_fun_syms.extend([defined, alias]);
    let x = variable("x");
    let apply = |f| Term::App(FunSym::NoEq(f), vec![x.clone()].into());
    sig.st_rules.insert(CtxtStRule::new(
        apply(defined),
        StRhs {
            positions: vec![vec![0]],
            term: x.clone(),
        },
    ));
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    assert!(matches!(
        h.variants(&apply(alias)),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
}

#[test]
fn common_compound_children_keep_contextual_witnesses_and_check_declarations() {
    use tamarin_term::builtin::{hash, pair};
    use tamarin_term::maude_sig::hash_maude_sig;
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    let sig = mset_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let x = LVar::new("x", LSort::Msg, 1);
    let y = LVar::new("y", LSort::Msg, 1);
    let k = LVar::new("k", LSort::Msg, 0);
    let erased = LVar::new("erased", LSort::Msg, 991);
    let var = |v| Term::Lit(Lit::Var(v));
    let common = hash(var(erased));
    let eqs = [
        Equal {
            lhs: var(k),
            rhs: pair(var(x), var(erased)),
        },
        Equal {
            lhs: sum(common.clone(), var(x)),
            rhs: sum(common, hash(var(y))),
        },
    ];
    let before = h.fresh_counter_peek();
    let answers = h.unify(&eqs).unwrap();
    assert_eq!(answers.len(), 1);
    let arm = LNSubstVFresh::from_list(answers[0].clone());
    let wy = arm.image_of(&y).unwrap().clone();
    let we = arm.image_of(&erased).unwrap().clone();
    assert_ne!(wy, we);
    for t in [&wy, &we] {
        assert!(matches!(t,Term::Lit(Lit::Var(v)) if v.idx > erased.idx));
    }
    assert_eq!(arm.image_of(&x), Some(&hash(wy.clone())));
    assert_eq!(arm.image_of(&k), Some(&pair(hash(wy), we)));
    assert_eq!(h.unify(&eqs).unwrap(), answers);
    assert_eq!(h.fresh_counter_peek(), before);
    assert_eq!(h.stats().unify_count, 0);
    assert_eq!(h.stats().lean_unify_count, 2);
    let bad = hash(var(LVar::new("i", LSort::Node, 0)));
    assert!(matches!(
        h.unify(&[Equal {
            lhs: sum(bad.clone(), var(x)),
            rhs: sum(bad, var(y))
        }]),
        Err(MaudeError::UnsupportedOperation("AC/C unification"))
    ));
}

#[test]
fn compound_ac_matching_tracks_full_factors_and_restores_rigid_sorts() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;

    let sig = mset_maude_sig().merge(hash_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let a = pub_term("a");
    let b = pub_term("b");
    let rigid = LVar::new("rigid", LSort::Msg, 8);
    let vr = Term::Lit(Lit::Var(rigid));
    for sort in [LSort::Msg, LSort::Pub] {
        let x = LVar::new("x", sort, 0);
        let vx = Term::Lit(Lit::Var(x));
        let bindable = [(x.name, x.idx)].into_iter().collect();
        for tail in [a.clone(), hash(a.clone())] {
            let eq = Equal {
                lhs: sum(vx.clone(), tail.clone()),
                rhs: sum(vr.clone(), tail),
            };
            let answers = h.match_eqs_skolemize_both(&[eq], &bindable).unwrap();
            if sort == LSort::Msg {
                assert_eq!(answers, vec![vec![(x, vr.clone())]]);
            } else {
                assert!(answers.is_empty());
            }
        }
    }
    let x = LVar::new("x", LSort::Msg, 0);
    let pat = sum(variable("x"), hash(a.clone()));
    for (subject, expected) in [
        (sum(a.clone(), hash(b.clone())), vec![]),
        (
            sum(hash(a.clone()), hash(b.clone())),
            vec![vec![(x, hash(b.clone()))]],
        ),
        (
            f_app_ac(
                AcSym::Union,
                vec![hash(a.clone()), hash(a.clone()), b.clone()],
            ),
            vec![vec![(x, sum(hash(a.clone()), b.clone()))]],
        ),
    ] {
        assert_eq!(
            h.match_eqs(&[Equal {
                lhs: subject,
                rhs: pat.clone()
            }])
            .unwrap(),
            expected
        );
    }
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn open_constructor_ac_matching_shares_bindings_across_selected_and_remaining_factors() {
    use tamarin_term::builtin::{hash, pair};
    use tamarin_term::maude_sig::hash_maude_sig;
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let (x, y) = (LVar::new("x", LSort::Msg, 0), LVar::new("y", LSort::Msg, 0));
    let var = |v| Term::Lit(Lit::Var(v));
    let a = pub_term("a");
    let b = pub_term("b");
    let u = |fs| f_app_ac(AcSym::Union, fs);
    let pat = u(vec![hash(pair(var(x), var(x))), var(x), var(y)]);
    let good = hash(pair(a.clone(), a.clone()));
    let bad = hash(pair(a.clone(), b.clone()));
    let subject = u(vec![good.clone(), bad.clone(), a.clone(), b.clone()]);
    let query = |pattern, subject| Equal {
        lhs: subject,
        rhs: pattern,
    };
    let answers = h.match_eqs(&[query(pat.clone(), subject)]).unwrap();
    assert_eq!(answers.len(), 1);
    assert!(answers[0].contains(&(x, a.clone())));
    assert!(answers[0].contains(&(y, sum(b.clone(), bad))));
    assert!(h
        .match_eqs(&[query(pat, u(vec![good, b.clone(), b]))])
        .unwrap()
        .is_empty());
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn open_match_cancels_closed_siblings_and_restores_contextual_subjects() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let x = LVar::new("x", LSort::Pub, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let rigid = LVar::new("z", LSort::Pub, u64::MAX);
    let var = |v| Term::Lit(Lit::Var(v));
    let fixed = vec![hash(pub_term("fixed")); 20];
    let u = |mut xs: Vec<LNTerm>| {
        xs.extend(fixed.clone());
        f_app_ac(AcSym::Union, xs)
    };
    let eq = Equal {
        lhs: u(vec![hash(var(x)), var(y)]),
        rhs: u(vec![hash(var(rigid)), pub_term("a")]),
    };
    let mut answers = h
        .match_eqs_skolemize_both(
            &[eq],
            &[(x.name, x.idx), (y.name, y.idx)].into_iter().collect(),
        )
        .unwrap();
    assert_eq!(answers.len(), 1);
    answers[0].sort();
    let mut expected = vec![(x, var(rigid)), (y, pub_term("a"))];
    expected.sort();
    assert_eq!(answers[0], expected);
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn native_alternative_order_uses_bindings_in_the_callers_scope() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let (x, y) = (LVar::new("x", LSort::Msg, 0), LVar::new("y", LSort::Msg, 1));
    let var = |v| Term::Lit(Lit::Var(v));
    let rigid = variable("context");
    let a = pub_term("z");
    let pattern = sum(hash(var(x)), hash(var(y)));
    let eq = Equal {
        lhs: pattern.clone(),
        rhs: sum(hash(rigid.clone()), hash(a.clone())),
    };
    let arms = h
        .match_eqs_skolemize_both(
            &[eq],
            &[(x.name, x.idx), (y.name, y.idx)].into_iter().collect(),
        )
        .unwrap();
    assert_eq!(
        arms,
        vec![
            vec![(x, a.clone()), (y, rigid.clone())],
            vec![(x, rigid), (y, a.clone())],
        ]
    );
    let b = pub_term("p");
    let plain = Equal {
        lhs: sum(hash(a.clone()), hash(b.clone())),
        rhs: pattern,
    };
    assert_eq!(
        h.match_eqs(&[plain]).unwrap(),
        vec![vec![(x, b.clone()), (y, a.clone())], vec![(x, a), (y, b)],]
    );
}

#[test]
fn open_match_joins_whole_compound_images_across_equations() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let p = sum(hash(variable("x")), variable("y"));
    let query = |last| Equal {
        lhs: f_app_ac(
            AcSym::Union,
            vec![hash(pub_term("a")), hash(pub_term(last)), pub_term("c")],
        ),
        rhs: p.clone(),
    };
    assert_eq!(h.match_eqs(&[query("b"), query("b")]).unwrap().len(), 2);
    assert!(h.match_eqs(&[query("b"), query("d")]).unwrap().is_empty());
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn open_match_budget_exhaustion_discards_earlier_successes() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let u = |xs| f_app_ac(AcSym::Union, xs);
    // The first H(x) leaves eight factors for two variables (65,025 candidate
    // pairs), which fits and yields matches. The next H(x) exhausts the query budget.
    let eq = Equal {
        lhs: u((0..9).map(|i| hash(pub_term(format!("v{i}")))).collect()),
        rhs: u(vec![hash(variable("x")), variable("y"), variable("z")]),
    };
    assert!(matches!(
        h.match_eqs(&[eq]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    assert_eq!(h.stats().match_count, 0);
}
#[test]
fn rigid_allocation_preserves_fresh_variables_after_common_child_cancellation() {
    use tamarin_term::builtin::{hash, pair};
    use tamarin_term::maude_sig::hash_maude_sig;
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig()
            .merge(hash_maude_sig())
            .merge(pair_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let (x, y, z, erased, alias) = (
        LVar::new("x", LSort::Msg, 0),
        LVar::new("y", LSort::Msg, 0),
        LVar::new("z", LSort::Msg, 0),
        LVar::new("erased", LSort::Msg, 20),
        LVar::new("alias", LSort::Msg, 99),
    );
    let var = |v| Term::Lit(Lit::Var(v));
    let common = hash(var(erased));
    let eqs = [
        Equal {
            lhs: var(alias),
            rhs: pair(var(z), var(erased)),
        },
        Equal {
            lhs: sum(common.clone(), sum(var(x), var(y))),
            rhs: sum(common, sum(var(z), pub_term("a"))),
        },
    ];
    let arms = h.unify(&eqs).unwrap();
    assert_eq!(arms.len(), 4);
    for bindings in &arms {
        let arm = LNSubstVFresh::from_list(bindings.clone());
        let image = |v| arm.image_of(&v).unwrap().clone();
        assert_eq!(sum(image(x), image(y)), sum(image(z), pub_term("a")));
        assert_eq!(image(alias), pair(image(z), image(erased)));
        assert!(arm.vars_range().iter().all(|v| v.idx > alias.idx));
        let Term::Lit(Lit::Var(ambient)) = image(erased) else {
            panic!()
        };
        assert!(!tamarin_term::vterm::vars_vterm(&image(z)).contains(&ambient));
    }
    assert_eq!(h.unify(&eqs).unwrap(), arms);
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn narrow_allocation_and_space_for_both_rigid_allocation_witnesses() {
    let eq = |sort, idx| Equal {
        lhs: sum(
            Term::Lit(Lit::Var(LVar::new("x", sort, idx))),
            variable("y"),
        ),
        rhs: sum(variable("z"), pub_term("a")),
    };
    assert_eq!(native().unify(&[eq(LSort::Pub, 0)]).unwrap().len(), 3);
    let h = native();
    assert_eq!(h.unify(&[eq(LSort::Msg, u64::MAX - 2)]).unwrap().len(), 4);
    assert!(h.unify(&[eq(LSort::Msg, u64::MAX - 1)]).is_err());
    assert!(h.check_backend_status().is_err());
}

#[test]
fn compound_offsets_reconcile_equalizable_heads_and_check_declarations() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let query = |a, b| Equal {
        lhs: sum(variable("x"), a),
        rhs: sum(variable("y"), b),
    };
    let h = || {
        MaudeHandle::start_with_backend(
            MISSING,
            mset_maude_sig().merge(hash_maude_sig()),
            AlgebraBackend::NativeOnly,
        )
        .unwrap()
    };
    let one = pub_term("one");
    let x = variable("x");
    let z = variable("z");
    assert_eq!(
        h().unify(&[query(one.clone(), hash(z.clone()))])
            .unwrap()
            .len(),
        2
    );
    assert!(h()
        .unify(&[query(one.clone(), hash(x))])
        .unwrap()
        .is_empty());
    assert_eq!(
        h().unify(&[query(hash(z.clone()), hash(variable("w")))])
            .unwrap()
            .len(),
        3
    );
    let ill_sorted = query(
        one.clone(),
        hash(Term::Lit(Lit::Var(LVar::new("i", LSort::Node, 0)))),
    );
    assert!(matches!(
        h().unify(&[ill_sorted]),
        Err(MaudeError::UnsupportedOperation("AC/C unification"))
    ));
    assert!(matches!(
        native().unify(&[query(one, hash(z))]),
        Err(MaudeError::UnsupportedOperation("AC/C unification"))
    ));
}

#[test]
fn commutative_branch_witnesses_preserve_full_query_aliases_without_a_process() {
    use tamarin_term::builtin::{emap, pair};
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    let sig = bp_maude_sig().merge(dh_maude_sig()).merge(pair_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly)
        .unwrap()
        .with_fresh_counter_next(1000);
    let (x, y, z, u, alias, ambient) = (
        LVar::new("x", LSort::Msg, 0),
        LVar::new("x", LSort::Msg, 1),
        LVar::new("x", LSort::Msg, 2),
        LVar::new("x", LSort::Msg, 3),
        LVar::new("alias", LSort::Msg, 7),
        LVar::new("ambient", LSort::Msg, 121),
    );
    let v = |w| Term::Lit(Lit::Var(w));
    let eqs = [
        Equal {
            lhs: emap(v(x), v(y)),
            rhs: emap(v(z), v(u)),
        },
        Equal {
            lhs: v(alias),
            rhs: pair(v(x), v(ambient)),
        },
    ];
    let answers = h.unify(&eqs).unwrap();
    assert_eq!(answers.len(), 2);
    let mut straight = Vec::new();
    for arm in &answers {
        let arm = LNSubstVFresh::from_list(arm.clone());
        let image = |v| arm.image_of(&v).unwrap().clone();
        assert_eq!(emap(image(x), image(y)), emap(image(z), image(u)));
        assert_ne!(image(x), image(y));
        assert_ne!(image(x), image(ambient));
        assert_ne!(image(y), image(ambient));
        assert_eq!(image(alias), pair(image(x), image(ambient)));
        assert!(arm.vars_range().iter().all(|w| w.idx > ambient.idx));
        straight.push(image(x) == image(z));
    }
    straight.sort_unstable();
    assert_eq!(straight, [false, true]);
    assert_eq!(h.unify(&eqs).unwrap(), answers);
    assert_eq!(h.fresh_counter_peek(), 1000);
    assert_eq!(h.stats().lean_unify_count, 2);
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn commutative_search_defers_when_a_live_sibling_or_input_is_unsupported() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = bp_maude_sig().merge(dh_maude_sig()).merge(mset_maude_sig());
    let h = || {
        MaudeHandle::start_with_backend(MISSING, sig.clone(), AlgebraBackend::NativeOnly).unwrap()
    };
    let eq = |lhs, rhs| Equal { lhs, rhs };
    // One orientation binds p and q to ordinary terms. The other requires
    // solving an independent four-variable AC equation with shared witnesses.
    let covered = eq(
        emap(variable("p"), sum(variable("x"), variable("y"))),
        emap(variable("q"), sum(variable("z"), variable("u"))),
    );
    let supported = h();
    assert_eq!(supported.unify(&[covered]).unwrap().len(), 8);
    assert_eq!(supported.stats().unify_count, 0);
    // The crossed orientation still succeeds, but the straight one now
    // exceeds the matrix column limit. Its sibling must not be published.
    let wide = f_app_ac(
        AcSym::Union,
        (0..33).map(|i| variable(&format!("v{i}"))).collect(),
    );
    let unknown = eq(
        emap(variable("p"), wide),
        emap(variable("q"), sum(variable("z"), variable("u"))),
    );
    let bad = eq(
        emap(
            Term::Lit(Lit::Var(LVar::new("i", LSort::Node, 1))),
            variable("x"),
        ),
        emap(variable("y"), variable("z")),
    );
    for q in [unknown, bad] {
        let h = h();
        assert!(matches!(
            h.unify(&[q]),
            Err(MaudeError::UnsupportedOperation("AC/C unification"))
        ));
        assert_eq!(h.stats().lean_unify_count, 0);
        assert!(h.check_backend_status().is_err());
    }
    let undeclared = eq(
        emap(variable("p"), variable("q")),
        emap(variable("r"), variable("s")),
    );
    assert!(native().unify(&[undeclared]).is_err());
    let overflow = eq(
        emap(
            Term::Lit(Lit::Var(LVar::new("p", LSort::Msg, u64::MAX))),
            variable("q"),
        ),
        emap(variable("r"), variable("s")),
    );
    let h = h();
    assert!(h.unify(&[overflow]).is_err());
    assert!(h.check_backend_status().is_err());
}

#[test]
fn commutative_resource_limit_and_cancellation_discard_incomplete_searches() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let sig = bp_maude_sig().merge(dh_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let qs: Vec<_> = (0..13)
        .map(|i| {
            let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, i)));
            Equal {
                lhs: emap(v("a"), v("b")),
                rhs: emap(pub_term("left"), pub_term("right")),
            }
        })
        .collect();
    {
        let token = CancellationToken::default();
        token.request_cancel();
        let _guard = CancellationGuard::new(Some(token));
        assert!(matches!(h.unify(&qs), Err(MaudeError::Cancelled)));
    }
    h.check_backend_status().unwrap();
    assert_eq!(h.unify(&qs[..2]).unwrap().len(), 4);
    assert!(matches!(
        h.unify(&qs),
        Err(MaudeError::UnsupportedOperation("AC/C unification"))
    ));
    assert_eq!(h.stats().lean_unify_count, 1);
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn repeated_commutative_operand_keeps_independent_equations_in_one_branch() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    use tamarin_term::subst_vfresh::LNSubstVFresh;

    let sig = bp_maude_sig().merge(dh_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let var = |name, index| LVar::new(name, LSort::Msg, index);
    // Keeping both equivalent orientations visits 8,191 search nodes before
    // deduplication. With either single orientation the whole query needs 13.
    let equations: Vec<_> = (0..12)
        .map(|i| {
            let term = |name| Term::Lit(Lit::Var(var(name, i)));
            Equal {
                lhs: emap(term("x"), term("x")),
                rhs: emap(term("y"), term("z")),
            }
        })
        .collect();
    let answers = h.unify(&equations).unwrap();
    let [one] = answers.as_slice() else {
        panic!("expected one most-general answer, got {answers:?}");
    };
    let answer = LNSubstVFresh::from_list(one.clone());
    let mut witnesses = std::collections::BTreeSet::new();
    for i in 0..12 {
        let Some(Term::Lit(Lit::Var(witness))) = answer.image_of(&var("x", i)) else {
            panic!("group {i} lost its open witness");
        };
        assert!(
            witnesses.insert(*witness),
            "independent groups must stay independent"
        );
        for name in ["y", "z"] {
            assert_eq!(
                answer.image_of(&var(name, i)),
                Some(&Term::Lit(Lit::Var(*witness)))
            );
        }
    }
    h.check_backend_status().unwrap();
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn mixed_commutative_and_free_equations_use_skolem_message_sorts_in_every_order() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    use tamarin_term::maude_types::SKOLEM_MSG_PREFIX;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        bp_maude_sig().merge(dh_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let c = Equal {
        lhs: emap(variable("x"), variable("y")),
        rhs: emap(pub_term("a"), pub_term("b")),
    };
    let impossible = Equal {
        lhs: Term::Lit(Lit::Var(LVar::new("p", LSort::Pub, 0))),
        rhs: pub_term(format!("{SKOLEM_MSG_PREFIX}example")),
    };
    assert!(h
        .unify(std::slice::from_ref(&impossible))
        .unwrap()
        .is_empty());
    assert!(h
        .unify(&[impossible.clone(), c.clone()])
        .unwrap()
        .is_empty());
    assert!(h.unify(&[c, impossible]).unwrap().is_empty());
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn alternating_ac_cancellation_and_commutative_splits_share_one_search_budget() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = mset_maude_sig().merge(dh_maude_sig()).merge(bp_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    // Each level contributes one independent two-way C equation. The next
    // level is visible only after cancelling the AC factor under its parent.
    let query = |depth: u64| {
        let mut left = pub_term("end");
        let mut right = left.clone();
        for i in 0..depth {
            let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, i)));
            left = emap(emap(var("x"), var("y")), sum(pub_term("anchor"), left));
            right = emap(
                emap(pub_term("a"), pub_term("b")),
                sum(pub_term("anchor"), right),
            );
        }
        Equal {
            lhs: sum(pub_term("outer"), left),
            rhs: sum(pub_term("outer"), right),
        }
    };
    assert_eq!(h.unify(&[query(2)]).unwrap().len(), 4);
    // A 12-level result would fit in the answer buffer, but exploring its
    // 4,096 leaves requires more than 4,096 total worklist states.
    assert!(matches!(
        h.unify(&[query(12)]),
        Err(MaudeError::UnsupportedOperation("AC/C unification"))
    ));
    assert_eq!(h.stats().lean_unify_count, 1);
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn natural_kind_queries_preserve_variable_sorts_before_factoring() {
    use tamarin_term::builtin::{fst, nat_plus};
    use tamarin_term::function_symbols::nat_one_sym;
    use tamarin_term::maude_sig::nat_maude_sig;
    use tamarin_term::term::{f_app_list, f_app_no_eq};

    let handle = || {
        MaudeHandle::start_with_backend(
            MISSING,
            nat_maude_sig().merge(pair_maude_sig()),
            AlgebraBackend::NativeOnly,
        )
        .unwrap()
    };
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let one = f_app_no_eq(nat_one_sym(), vec![]);
    let natural = var("n", LSort::Nat);
    let known = nat_plus(natural.clone(), one.clone());
    let fresh = var("w", LSort::Fresh);
    let bad = nat_plus(fresh.clone(), one.clone());
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let h = handle();
    let packed = f_app_list(vec![fresh.clone(), bad.clone(), bad.clone()]);
    assert_eq!(h.variants(&packed).unwrap(), vec![vec![]]);
    assert_eq!(
        h.unify(&[eq(bad.clone(), bad.clone())]).unwrap(),
        vec![vec![]]
    );
    for factor in [
        fresh,
        var("p", LSort::Pub),
        pub_term("a"),
        fst(variable("v")),
    ] {
        let never = nat_plus(factor, one.clone());
        for other in [natural.clone(), known.clone(), variable("v")] {
            for query in [eq(never.clone(), other.clone()), eq(other, never.clone())] {
                assert!(h
                    .unify(&[query.clone(), eq(variable("alias"), one.clone())])
                    .unwrap()
                    .is_empty());
                assert!(!h.unifiable(&[query]).unwrap());
            }
        }
    }
    assert_eq!(h.stats().unify_count, 0);
    let maybe = nat_plus(variable("m"), one.clone());
    for query in [
        eq(maybe, known), // m can later become a Nat
        eq(
            bad.clone(),
            nat_plus(var("other", LSort::Fresh), one.clone()),
        ), // both can agree
    ] {
        assert!(matches!(
            handle().unify(&[query]),
            Err(MaudeError::UnsupportedOperation(_))
        ));
    }
    for query in [
        f_app_list(vec![fst(variable("x")), bad]), // narrowing requires sorted observers
        nat_plus(var("node", LSort::Node), one),   // outside the admitted message-kind fragment
    ] {
        assert!(matches!(
            handle().variants(&query),
            Err(MaudeError::UnsupportedOperation(_))
        ));
    }
}

#[test]
fn reduction_lifts_through_declared_free_constructors() {
    use tamarin_term::builtin::{fst, hash, pair, xor, zero_const};
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::maude_sig::{hash_maude_sig, xor_maude_sig};
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::f_app_no_eq;

    let wrap = NoEqSym::new(b"wrap", 3, Privacy::Public, Constructability::Constructor);
    let mut sig = xor_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    sig.st_fun_syms.insert(wrap);
    let a = pub_term("a");
    let x = variable("x");
    let duplicate = xor(a.clone(), a.clone());
    let projected = fst(pair(x.clone(), a.clone()));
    let test = |h: &MaudeHandle| {
        for (t, expected) in [
            (hash(duplicate.clone()), hash(zero_const())),
            (
                f_app_no_eq(
                    wrap,
                    vec![a.clone(), hash(duplicate.clone()), hash(projected.clone())],
                ),
                f_app_no_eq(wrap, vec![a.clone(), hash(zero_const()), hash(x.clone())]),
            ),
        ] {
            assert_eq!(h.reduce(&t).unwrap(), expected);
        }
    };
    let native =
        |s| MaudeHandle::start_with_backend(MISSING, s, AlgebraBackend::NativeOnly).unwrap();
    let h = native(sig.clone());
    test(&h);
    assert_eq!(h.stats().norm_count, 0);
    if let Some(path) = tamarin_test_support::configured_maude_path() {
        let oracle =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        test(&oracle);
        assert_eq!(oracle.stats().norm_count, 2);
    }

    // A formerly inert head can acquire a rule applicable after its child
    // reduces. Rebuilding hash(zero) would report a reducible answer.
    sig.st_rules.insert(CtxtStRule::new(
        hash(zero_const()),
        StRhs {
            term: zero_const(),
            positions: vec![vec![0]],
        },
    ));
    let active = native(sig.refresh());
    // The first sibling can complete. If the second defers, the whole
    // request must defer, even though a prefix has already been rebuilt.
    let packed = f_app_no_eq(wrap, vec![duplicate.clone(), hash(duplicate), a.clone()]);
    match active.reduce(&packed) {
        Ok(value) => assert_eq!(
            value,
            f_app_no_eq(wrap, vec![zero_const(), zero_const(), a])
        ),
        Err(MaudeError::UnsupportedOperation("normalization")) => {}
        other => panic!("unexpected reduction result: {other:?}"),
    }
}

#[test]
fn fresh_xor_variants_share_a_fresh_witness_and_require_the_exact_live_rules() {
    use tamarin_term::builtin::{xor, zero_const};
    use tamarin_term::maude_sig::xor_maude_sig;
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::f_app_list;
    let sig = xor_maude_sig();
    let new = |s| MaudeHandle::start_with_backend(MISSING, s, AlgebraBackend::NativeOnly).unwrap();
    let (x, y) = (
        LVar::new("x", LSort::Fresh, 6),
        LVar::new("y", LSort::Fresh, 9),
    );
    let var = |v| Term::Lit(Lit::Var(v));
    let term = xor(var(x), var(y));
    let h = new(sig.clone());
    let (identity, diagonal) = {
        let [first, second]: [_; 2] = h
            .variants(&f_app_list(vec![var(y), term.clone(), var(x)]))
            .unwrap()
            .try_into()
            .unwrap();
        (first, second)
    };
    assert!(identity.is_empty());
    assert_eq!(diagonal.len(), 2);
    let w = &diagonal[0].1;
    assert!(matches!(w,Term::Lit(Lit::Var(v)) if v.sort==LSort::Fresh && v.idx>y.idx));
    assert_eq!(diagonal, vec![(x, w.clone()), (y, w.clone())]);
    assert_eq!(h.reduce(&xor(var(x), var(x))).unwrap(), zero_const());
    assert_eq!(h.variants(&xor(var(y), var(y))).unwrap(), vec![vec![]]);
    assert_eq!(h.stats().var_count, 0);
    assert_eq!(h.stats().norm_count, 0);
    let extra = |lhs, rhs| {
        CtxtStRule::new(
            lhs,
            StRhs {
                positions: vec![],
                term: rhs,
            },
        )
    };
    for change in [
        extra(xor(variable("a"), variable("b")), pub_term("new")),
        extra(zero_const(), pub_term("new")),
    ] {
        let mut changed = sig.clone();
        changed.st_rules.insert(change);
        assert!(matches!(
            new(changed.clone()).variants(&term),
            Err(MaudeError::UnsupportedOperation("variant generation"))
        ));
        assert!(matches!(
            new(changed).reduce(&xor(var(x), var(x))),
            Err(MaudeError::UnsupportedOperation("normalization"))
        ));
    }
    for q in [
        f_app_list(vec![variable("ambient"), term.clone()]),
        f_app_list(vec![term.clone(), xor(var(x), var(x))]),
    ] {
        assert_eq!(new(sig.clone()).variants(&q).unwrap().len(), 2);
    }
    let open_msg = xor(var(x), variable("m"));
    for (q, count) in [
        (open_msg.clone(), 4),
        (f_app_list(vec![term.clone(), open_msg]), 8),
    ] {
        assert_eq!(new(sig.clone()).variants(&q).unwrap().len(), count);
    }
    let huge = var(LVar::new("huge", LSort::Fresh, u64::MAX));
    assert_eq!(
        new(sig.clone())
            .variants(&xor(huge.clone(), huge.clone()))
            .unwrap(),
        vec![vec![]]
    );
    let h = new(sig);
    let low = var(LVar::new("x", LSort::Fresh, 0));
    let application = xor(huge.clone(), low.clone());
    let [identity, diagonal]: [_; 2] = h.variants(&application).unwrap().try_into().unwrap();
    assert!(identity.is_empty());
    let [(left, first), (right, second)]: [_; 2] = diagonal.try_into().unwrap();
    assert_eq!(xor(var(left), var(right)), application);
    assert_eq!(first, second);
    assert!(
        matches!(first, Term::Lit(Lit::Var(v)) if v.sort == LSort::Fresh && v.idx != 0 && v.idx != u64::MAX)
    );
    assert_eq!(h.reduce(&xor(huge.clone(), huge)).unwrap(), zero_const());
    h.check_backend_status().unwrap();
}

#[test]
fn dh_stable_variants_respect_the_active_equations_and_variable_sorts() {
    use tamarin_term::builtin::{exp, inv, mult};
    use tamarin_term::maude_sig::dh_maude_sig;
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::f_app_list;

    let native =
        |sig| MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let sig = dh_maude_sig();
    let r = Term::Lit(Lit::Var(LVar::new("r", LSort::Fresh, 0)));
    let s = Term::Lit(Lit::Var(LVar::new("s", LSort::Fresh, 0)));
    let power = exp(pub_term("g"), mult(r.clone(), s.clone()));
    let query = f_app_list(vec![r.clone(), s.clone(), power.clone(), inv(r.clone())]);
    let h = native(sig.clone());
    assert_eq!(h.variants(&query).unwrap(), vec![vec![]]);
    assert_eq!(h.reduce(&power).unwrap(), power);
    h.check_backend_status().unwrap();

    let x = variable("x");
    let y = variable("y");
    // This overlap adds a competing result to the DH tower rule. It is a
    // live subterm equation, even if the caller has not refreshed the cache.
    let mut changed = sig.clone();
    changed.st_rules.insert(CtxtStRule::new(
        exp(exp(x.clone(), y.clone()), variable("z")),
        StRhs {
            positions: vec![vec![0, 0]],
            term: x.clone(),
        },
    ));
    let h = native(changed);
    let tower = exp(exp(pub_term("g"), r.clone()), s.clone());
    assert!(matches!(
        h.variants(&tower),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
    // A Msg exponent may become one. A Msg base may become DH-neutral or
    // itself be an exponentiation. Both are genuine narrowing queries.
    for open in [exp(pub_term("g"), y), exp(x, r)] {
        match native(sig.clone()).variants(&open) {
            Ok(arms) => assert!(arms.len() > 1),
            Err(MaudeError::UnsupportedOperation("variant generation")) => {}
            other => panic!("unexpected DH variant result: {other:?}"),
        }
    }
}

#[test]
fn received_dh_variants_share_the_exponent_and_defer_uncertified_tuples() {
    use tamarin_term::builtin::{exp, inv};
    use tamarin_term::lterm::frees;
    use tamarin_term::maude_sig::dh_maude_sig;
    use tamarin_term::subst::Subst;
    use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
    use tamarin_term::term::f_app_list;
    let sig = dh_maude_sig();
    let native =
        |sig| MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let peer = LVar::new("x", LSort::Msg, 7);
    let r = LVar::new("x", LSort::Fresh, 7);
    let var = |v| Term::Lit(Lit::Var(v));
    let power = exp(var(peer), var(r));
    let query = f_app_list(vec![
        power.clone(),
        var(r),
        power.clone(),
        var(peer),
        variable("ambient"),
    ]);
    let h = native(sig.clone());
    let answers = h.variants(&query).unwrap();
    assert_eq!(answers.len(), 7);
    let caller = frees(&query);
    let mut shared = 0;
    for answer in answers {
        let subst = Subst::from_list(answer);
        let base = subst.image_of(&peer).unwrap();
        let Term::Lit(Lit::Var(fresh)) = subst.image_of(&r).unwrap() else {
            panic!("fresh exponent lost its sort");
        };
        assert_eq!(fresh.sort, LSort::Fresh);
        shared += usize::from(frees(base).contains(fresh));
        assert!(frees(base).iter().all(|v| !caller.contains(v)));
        assert!(!caller.contains(fresh));
    }
    assert_eq!(shared, 4);
    assert_eq!(h.stats().var_count, 0);
    let high = LVar::new("x", LSort::Msg, u64::MAX);
    let low = LVar::new("x", LSort::Fresh, 0);
    let edge = exp(var(high), var(low));
    let at_limit = h.variants(&edge).unwrap();
    assert_eq!(at_limit.len(), 7);
    for (_, image) in at_limit.into_iter().flatten() {
        assert!(frees(&image)
            .iter()
            .all(|v| v.idx != high.idx && v.idx != low.idx));
    }
    // Both powers share one observed exponent across their independent peers.
    let second = exp(variable("other_peer"), var(r));
    let packed = f_app_list(vec![power.clone(), second]);
    assert_eq!(native(sig.clone()).variants(&packed).unwrap().len(), 49);
    // An extra live inversion rule changes the signed-product theory.
    let mut changed = sig;
    let x = variable("z");
    changed.st_rules.insert(CtxtStRule::new(
        inv(x.clone()),
        StRhs {
            positions: vec![vec![0]],
            term: x,
        },
    ));
    assert!(matches!(
        native(changed).variants(&power),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
}

#[test]
fn native_dh_powers_cancel_inside_products_and_nested_towers() {
    use tamarin_term::builtin::{dh_neutral, exp, inv, mult, one_const};
    use tamarin_term::maude_sig::dh_maude_sig;
    let h = MaudeHandle::start_with_backend(MISSING, dh_maude_sig(), AlgebraBackend::NativeOnly)
        .unwrap();
    let g = pub_term("g");
    let r = Term::Lit(Lit::Var(LVar::new("r", LSort::Fresh, 0)));
    let p = variable("p");
    let n = variable("n");
    let pow = |e| exp(g.clone(), e);
    for (input, expected) in [
        (exp(pow(inv(r.clone())), r.clone()), g.clone()),
        (
            exp(
                pow(mult(p.clone(), inv(mult(r.clone(), n.clone())))),
                r.clone(),
            ),
            pow(mult(p.clone(), inv(n.clone()))),
        ),
        (
            exp(
                exp(pow(inv(mult(r.clone(), r.clone()))), r.clone()),
                r.clone(),
            ),
            g.clone(),
        ),
        (exp(exp(dh_neutral(), n.clone()), r.clone()), dh_neutral()),
        (exp(exp(g.clone(), one_const()), one_const()), g),
    ] {
        assert_eq!(h.reduce(&input).unwrap(), expected, "{input:?}");
    }
    assert_eq!(h.stats().norm_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn dh_positive_product_matches_only_the_compatible_intruder_rule_heads() {
    use tamarin_term::builtin::{inv, mult};
    use tamarin_term::maude_sig::dh_maude_sig;
    let h = MaudeHandle::start_with_backend(MISSING, dh_maude_sig(), AlgebraBackend::NativeOnly)
        .unwrap();
    let fresh = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Fresh, 0)));
    let subject = mult(fresh("r"), fresh("s"));
    let (x, y, z, w) = (variable("x"), variable("y"), variable("z"), variable("w"));
    // These are the product unification queries during source precomputation
    // for the upstream DH_Message_Deduction example.
    for (rhs, count) in [
        (mult(x.clone(), y.clone()), 2),
        (mult(x.clone(), inv(y.clone())), 0),
        (mult(x.clone(), inv(mult(y.clone(), z.clone()))), 0),
        (mult(mult(x.clone(), y.clone()), inv(z.clone())), 0),
        (mult(mult(x, y), inv(mult(z, w))), 0),
    ] {
        let answers = h
            .unify(&[Equal {
                lhs: subject.clone(),
                rhs,
            }])
            .unwrap();
        assert_eq!(answers.len(), count);
    }
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn whole_unification_on_original_equations_can_complete_or_defer_without_maude() {
    use tamarin_term::builtin::{hash, pair};
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::maude_sig::hash_maude_sig;
    let sig = mset_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let (x, y) = (variable("x"), variable("y"));
    let free = Equal {
        lhs: hash(x.clone()),
        rhs: hash(x.clone()),
    };
    assert_eq!(h.unify(std::slice::from_ref(&free)).unwrap(), vec![vec![]]);
    // Previously the local free factorer completed this before any Lean call.
    assert_eq!(h.stats().lean_unify_count, 1);
    let ac = |terms: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::Union), terms.into());
    let mixed = Equal {
        lhs: pair(
            ac(vec![x.clone(), ac(vec![pub_term("a"), y.clone()])]),
            x.clone(),
        ),
        rhs: pair(ac(vec![y.clone(), x.clone(), pub_term("a")]), x.clone()),
    };
    assert_eq!(
        h.unify(&[free.clone(), mixed.clone()]).unwrap(),
        vec![vec![]]
    );
    // The same prefix remains compatible with non-identity solutions.
    let q = Equal {
        lhs: x.clone(),
        rhs: pub_term("fixed"),
    };
    let arms = h.unify(&[q.clone(), free, mixed]).unwrap();
    assert_eq!(arms.len(), 1);
    assert!(arms[0].contains(&(LVar::new("x", LSort::Msg, 0), q.rhs)));
    let before = h.stats().lean_unify_count;
    let open = Equal {
        lhs: sum(x.clone(), y.clone()),
        rhs: sum(variable("other"), variable("rest")),
    };
    let clash = Equal {
        lhs: hash(pub_term("a")),
        rhs: hash(pub_term("b")),
    };
    assert!(h.unify(&[open, clash]).unwrap().is_empty());
    assert_eq!(h.stats().lean_unify_count, before + 1);
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn native_homogeneous_system_preserves_shared_and_repeated_witnesses() {
    let h = native();
    let vars = ["x", "y", "z", "w"].map(|name| LVar::new(name, LSort::Msg, u64::MAX));
    let [x, y, z, w] = vars.map(|v| Term::Lit(Lit::Var(v)));
    let equations = [
        Equal {
            lhs: sum(x.clone(), x),
            rhs: y.clone(),
        },
        Equal {
            lhs: sum(y, z),
            rhs: w,
        },
    ];
    let arms = h.unify(&equations).unwrap();
    let [arm] = arms.as_slice() else {
        panic!("expected one general answer");
    };
    let image = |v| arm.iter().find(|(k, _)| *k == v).unwrap().1.clone();
    let a = image(vars[0]);
    let b = image(vars[2]);
    assert!(
        matches!((&a,&b), (Term::Lit(Lit::Var(u)),Term::Lit(Lit::Var(v))) if
        u != v && !vars.contains(u) && !vars.contains(v) && u.sort == LSort::Msg && v.sort == LSort::Msg)
    );
    assert_eq!(image(vars[1]), sum(a.clone(), a.clone()));
    assert_eq!(image(vars[3]), sum(sum(a.clone(), a), b));
    let cross = Equal {
        lhs: sum(variable("a"), variable("b")),
        rhs: sum(variable("c"), variable("d")),
    };
    assert_eq!(h.unify(&[cross]).unwrap().len(), 7);
    assert_eq!(h.stats().lean_unify_count, 2);
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn native_ac_operands_preserve_both_commutative_orientations() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = mset_maude_sig().merge(dh_maude_sig()).merge(bp_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let [x, y, a, b, c, d] =
        ["x", "y", "a", "b", "c", "d"].map(|s| LVar::new(s, LSort::Msg, u64::MAX));
    let v = |k| Term::Lit(Lit::Var(k));
    let eq = Equal {
        lhs: sum(v(x), emap(v(a), v(b))),
        rhs: sum(v(y), emap(v(c), v(d))),
    };
    let answers = h.unify(&[eq]).unwrap();
    assert_eq!(answers.len(), 4);
    let mut paired = Vec::new();
    for arm in &answers {
        let image = |k| &arm.iter().find(|(key, _)| *key == k).unwrap().1;
        if image(x) == image(y) {
            assert_ne!(image(a), image(b));
            paired.push((
                image(a) == image(c) && image(b) == image(d),
                image(a) == image(d) && image(b) == image(c),
            ));
        }
    }
    paired.sort_unstable();
    assert_eq!(paired, [(false, true), (true, false)]);
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn nested_ac_witnesses_keep_an_independent_outer_binding() {
    use tamarin_term::builtin::hash;
    use tamarin_term::lterm::HasFrees;
    use tamarin_term::maude_sig::hash_maude_sig;
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let x = LVar::new("x", LSort::Msg, u64::MAX);
    let z = LVar::new("z", LSort::Msg, 0);
    let v = |v| Term::Lit(Lit::Var(v));
    let outer = Equal {
        lhs: sum(v(x), hash(sum(variable("a"), variable("b")))),
        rhs: sum(v(z), hash(sum(variable("c"), variable("d")))),
    };
    assert_eq!(h.unify(std::slice::from_ref(&outer)).unwrap().len(), 9);
    let answers = h
        .unify(&[
            outer,
            Equal {
                lhs: v(x),
                rhs: v(z),
            },
        ])
        .unwrap();
    assert_eq!(answers.len(), 7);
    for arm in answers {
        let image = |key| &arm.iter().find(|(k, _)| *k == key).unwrap().1;
        assert_eq!(image(x), image(z));
        let Term::Lit(Lit::Var(witness)) = image(x) else {
            panic!("outer witness must be unconstrained")
        };
        assert_ne!(witness.idx, u64::MAX);
        assert_ne!(witness.idx, 0);
        for name in ["a", "b", "c", "d"] {
            image(LVar::new(name, LSort::Msg, 0)).for_each_free(&mut |w| assert_ne!(w, witness));
        }
    }
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn native_weighted_ac_preserves_a_single_shared_witness() {
    let h = native();
    let x = LVar::new("x", LSort::Msg, u64::MAX);
    let y = LVar::new("y", LSort::Msg, 0);
    let repeat = |term, k| f_app_ac(AcSym::Union, vec![term; k]);
    let equations = [Equal {
        lhs: repeat(Term::Lit(Lit::Var(x)), 11),
        rhs: repeat(Term::Lit(Lit::Var(y)), 13),
    }];
    let arms = h.unify(&equations).unwrap();
    let [arm] = arms.as_slice() else {
        panic!("expected one primitive ratio")
    };
    let image = |v| &arm.iter().find(|(key, _)| *key == v).unwrap().1;
    let Term::App(_, factors) = image(x) else {
        panic!("expected an AC product")
    };
    let w = &factors[0];
    assert!(matches!(w, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg && *v != x && *v != y));
    assert_eq!(image(x), &repeat(w.clone(), 13));
    assert_eq!(image(y), &repeat(w.clone(), 11));
    assert_eq!(h.stats().lean_unify_count, 1);
    assert_eq!(h.stats().unify_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn factored_ac_matrix_answers_solve_the_original_conjunction() {
    use tamarin_term::builtin::pair;
    use tamarin_term::subst::{apply_vterm, Subst};

    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(pair_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let [a, b, c, d, e, f] = ["a", "b", "c", "d", "e", "f"].map(variable);
    let first = Equal {
        lhs: sum(a.clone(), b.clone()),
        rhs: sum(c.clone(), d.clone()),
    };
    let second = Equal {
        lhs: f_app_ac(AcSym::Union, vec![a.clone(), b, c.clone(), e]),
        rhs: f_app_ac(AcSym::Union, vec![a.clone(), c, d, f.clone()]),
    };
    let equations = [
        Equal {
            lhs: variable("observed"),
            rhs: pair(a, f),
        },
        first.clone(),
        second.clone(),
        first,
        second,
    ];
    let arms = h.unify(&equations).unwrap();
    assert_eq!(arms.len(), 11);
    for arm in arms {
        let subst = Subst::from_list(arm);
        for eq in &equations {
            assert_eq!(
                apply_vterm(&subst, eq.lhs.clone()),
                apply_vterm(&subst, eq.rhs.clone())
            );
        }
    }
    h.check_backend_status().unwrap();
    assert_eq!(h.stats().unify_count, 0);
}

#[test]
fn open_ac_match_visits_both_nested_commutative_alignments() {
    use tamarin_term::builtin::{emap, hash};
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig};
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(bp_maude_sig())
        .merge(dh_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let a = pub_term("a");
    let b = pub_term("b");
    let pattern = hash(emap(variable("x"), variable("y")));
    let subject = hash(emap(a.clone(), b.clone()));
    let query = |p, t| Equal {
        lhs: sum(subject.clone(), t),
        rhs: sum(pattern.clone(), p),
    };
    let ambiguous = h.match_eqs(&[query(variable("z"), a.clone())]).unwrap();
    assert_eq!(ambiguous.len(), 2);
    for (left, right) in [(a.clone(), b.clone()), (b.clone(), a.clone())] {
        assert!(ambiguous
            .iter()
            .any(|arm| arm.contains(&(x, left.clone())) && arm.contains(&(y, right.clone()))));
        let forced = h.match_eqs(&[query(variable("x"), left.clone())]).unwrap();
        assert_eq!(forced.len(), 1);
        assert!(forced[0].contains(&(x, left)) && forced[0].contains(&(y, right)));
    }
    assert!(h
        .match_eqs(&[query(variable("x"), pub_term("c"))])
        .unwrap()
        .is_empty());
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn open_ac_match_counts_equivalent_ground_c_factors_in_both_orders() {
    use tamarin_term::builtin::emap;
    use tamarin_term::function_symbols::{CSym, FunSym};
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = mset_maude_sig().merge(bp_maude_sig()).merge(dh_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let canonical = emap(a.clone(), b.clone());
    let raw = Term::App(FunSym::C(CSym::EMap), vec![b, a].into());
    let x = LVar::new("x", LSort::Msg, 0);
    let q = |p, s| Equal { lhs: s, rhs: p };
    assert_eq!(
        h.match_eqs(&[q(
            sum(variable("x"), variable("x")),
            sum(raw.clone(), canonical.clone())
        )])
        .unwrap(),
        vec![vec![(x, canonical.clone())]]
    );
    assert_eq!(
        h.match_eqs(&[q(sum(variable("x"), raw), sum(pub_term("tail"), canonical))])
            .unwrap(),
        vec![vec![(x, pub_term("tail"))]]
    );
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn nested_c_match_discards_partial_answers_on_orientation_budget_exhaustion() {
    use tamarin_term::builtin::{emap, pair};
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = mset_maude_sig()
        .merge(bp_maude_sig())
        .merge(dh_maude_sig())
        .merge(pair_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let mut p = pub_term("end");
    let mut t = p.clone();
    // Twelve independent binary choices all succeed, but their combinations
    // exceed this query's budget. No prefix of their answers is complete.
    for i in 0..12 {
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)));
        let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, i)));
        p = pair(emap(x, y), p);
        t = pair(emap(pub_term("a"), pub_term("b")), t);
    }
    let query = Equal {
        lhs: sum(t, pub_term("tag")),
        rhs: sum(p, variable("tail")),
    };
    assert!(matches!(
        h.match_eqs(&[query]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn nested_ac_under_a_commutative_factor_returns_both_bindings() {
    use tamarin_term::builtin::emap;
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = mset_maude_sig().merge(bp_maude_sig()).merge(dh_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let nested = |a| emap(sum(a, pub_term("fixed")), pub_term("other"));
    let q = Equal {
        lhs: sum(nested(pub_term("a")), pub_term("tail")),
        rhs: sum(nested(variable("x")), variable("y")),
    };
    assert_eq!(
        h.match_eqs(&[q]).unwrap(),
        vec![vec![
            (LVar::new("x", LSort::Msg, 0), pub_term("a")),
            (LVar::new("y", LSort::Msg, 0), pub_term("tail")),
        ]]
    );
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn nested_ac_matches_share_a_product_across_levels_and_equations() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let (a, b, c) = (pub_term("a"), pub_term("b"), pub_term("c"));
    let (x, y) = (LVar::new("x", LSort::Msg, 0), LVar::new("y", LSort::Msg, 0));
    let ab = sum(a.clone(), b.clone());
    let inner = hash(sum(ab.clone(), c.clone()));
    let pattern = sum(hash(sum(variable("x"), variable("y"))), variable("x"));
    let matched = Equal {
        lhs: sum(inner.clone(), ab.clone()),
        rhs: pattern.clone(),
    };
    let second = |tail| Equal {
        lhs: sum(pub_term("tag"), hash(tail)),
        rhs: sum(pub_term("tag"), hash(variable("y"))),
    };
    assert_eq!(
        h.match_eqs(&[matched.clone(), second(c.clone())]).unwrap(),
        vec![vec![(x, ab), (y, c)]]
    );
    assert!(h
        .match_eqs(&[matched, second(b.clone())])
        .unwrap()
        .is_empty());
    // Raw associations at the enclosing AC root and below the hash represent
    // the same input. Each repeated occurrence still counts separately.
    let raw = |xs: Vec<LNTerm>| {
        Term::App(
            tamarin_term::function_symbols::FunSym::Ac(AcSym::Union),
            xs.into(),
        )
    };
    let pattern = raw(vec![
        hash(raw(vec![
            variable("x"),
            raw(vec![variable("x"), variable("y")]),
        ])),
        raw(vec![variable("x"), pub_term("tag")]),
    ]);
    let subject = raw(vec![
        hash(raw(vec![b.clone(), raw(vec![a.clone(), a.clone()])])),
        raw(vec![pub_term("tag"), a.clone()]),
    ]);
    assert_eq!(
        h.match_eqs(&[Equal {
            lhs: subject,
            rhs: pattern
        }])
        .unwrap(),
        vec![vec![(x, a), (y, b)]]
    );
    assert_eq!(h.stats().match_count, 0);
    h.check_backend_status().unwrap();
}

#[test]
fn nested_ac_cancels_closed_siblings_before_selecting() {
    use tamarin_term::builtin::hash;
    use tamarin_term::maude_sig::hash_maude_sig;
    let h = MaudeHandle::start_with_backend(
        MISSING,
        mset_maude_sig().merge(hash_maude_sig()),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let fixed = pub_term("repeated");
    let a = pub_term("a");
    let nested = |t, copies| {
        let mut factors = vec![fixed.clone(); copies];
        factors.push(t);
        hash(f_app_ac(AcSym::Union, factors))
    };
    let pattern = sum(nested(variable("x"), 70), variable("tail"));
    let q = |n| Equal {
        lhs: sum(nested(a.clone(), n), pub_term("end")),
        rhs: pattern.clone(),
    };
    assert_eq!(
        h.match_eqs(&[q(70)]).unwrap(),
        vec![vec![
            (LVar::new("tail", LSort::Msg, 0), pub_term("end")),
            (LVar::new("x", LSort::Msg, 0), a.clone())
        ]]
    );
    assert!(h.match_eqs(&[q(69)]).unwrap().is_empty());
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn nested_ac_search_budget_is_shared_by_independent_subtrees() {
    use tamarin_term::builtin::{hash, pair};
    use tamarin_term::maude_sig::hash_maude_sig;
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let mut pattern = pub_term("end");
    let mut subject = pattern.clone();
    for i in 0..18 {
        let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, i)));
        pattern = pair(hash(sum(v("x"), v("y"))), pattern);
        subject = pair(hash(sum(pub_term("a"), pub_term("b"))), subject);
    }
    // Each individual inner match is easy. Together they have 2^18 distinct
    // answers, so returning the first successful branches would lose matches.
    let eq = Equal {
        lhs: sum(subject, pub_term("tag")),
        rhs: sum(pattern, variable("tail")),
    };
    assert!(matches!(
        h.match_eqs(&[eq]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn rigid_ground_match_checks_raw_c_and_ac_forms_in_both_public_apis() {
    use tamarin_term::function_symbols::{CSym, FunSym};
    use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig};
    let sig = mset_maude_sig().merge(bp_maude_sig()).merge(dh_maude_sig());
    let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::NativeOnly).unwrap();
    let raw_c = |x, y| Term::App(FunSym::C(CSym::EMap), vec![x, y].into());
    let raw_ac = |xs: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::Union), xs.into());
    let (a, b, c) = (pub_term("a"), pub_term("b"), pub_term("c"));
    let raw = |x: LNTerm| {
        raw_ac(vec![
            c.clone(),
            raw_ac(vec![b.clone(), raw_c(x.clone(), a.clone())]),
        ])
    };
    let normal = |x| {
        sum(
            sum(c.clone(), b.clone()),
            tamarin_term::builtin::emap(a.clone(), x),
        )
    };
    let q = |lhs, rhs| Equal { lhs, rhs };
    for (other, expected) in [(b.clone(), true), (c.clone(), false)] {
        let eq = q(raw(b.clone()), normal(other));
        assert_eq!(
            h.has_match_eqs(std::slice::from_ref(&eq)).unwrap(),
            expected
        );
        assert_eq!(
            !h.match_eqs_skolemize_both(&[eq], &Default::default())
                .unwrap()
                .is_empty(),
            expected
        );
    }
    let x = variable("context");
    assert_eq!(
        h.match_eqs_skolemize_both(&[q(raw(x.clone()), normal(x))], &Default::default())
            .unwrap(),
        vec![vec![]]
    );
    assert_eq!(h.stats().match_count, 0);
}

#[test]
fn rigid_match_defers_undeclared_raw_operators_and_invalid_arities() {
    use tamarin_term::function_symbols::{CSym, FunSym};
    let (a, b) = (pub_term("a"), pub_term("b"));
    let nat = MaudeHandle::start_with_backend(
        MISSING,
        tamarin_term::maude_sig::nat_maude_sig(),
        AlgebraBackend::NativeOnly,
    )
    .unwrap();
    let raw_nat = |xs: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::NatPlus), xs.into());
    let ill_sorted = Equal {
        lhs: raw_nat(vec![b.clone(), a.clone()]),
        rhs: raw_nat(vec![a.clone(), b.clone()]),
    };
    assert!(matches!(
        nat.match_eqs(&[ill_sorted]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    let eq = Equal {
        lhs: Term::App(FunSym::C(CSym::EMap), vec![b.clone(), a.clone()].into()),
        rhs: Term::App(FunSym::C(CSym::EMap), vec![a.clone(), b].into()),
    };
    assert!(matches!(
        native().match_eqs(&[eq]),
        Err(MaudeError::UnsupportedOperation("matching"))
    ));
    let empty = Term::App(FunSym::Ac(AcSym::Union), vec![].into());
    let malformed = Equal { lhs: empty, rhs: a };
    assert!(matches!(
        native().match_eqs_skolemize_both(&[malformed], &Default::default()),
        Err(MaudeError::UnsupportedOperation("rigid-context matching"))
    ));
}
