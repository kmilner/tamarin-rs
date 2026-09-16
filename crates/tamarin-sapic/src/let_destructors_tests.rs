// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use std::collections::BTreeSet;
use tamarin_term::lterm::{LSort, NameTag};
use tamarin_term::vterm::var_term;
use tamarin_theory::sapic::{ProcessParsedAnnotation, SapicAction};

fn ann() -> ProcessAnnotation<LVar> {
    ProcessAnnotation {
        parsing_ann: ProcessParsedAnnotation::empty(),
        ..Default::default()
    }
}

fn svar(name: &str) -> SapicLVar {
    SapicLVar::untyped(LVar::new(name, LSort::Msg, 0))
}

fn pub_name(s: &str) -> SapicTerm {
    VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, s)))
}

#[test]
fn singleton_ac_destructor_still_takes_the_else_branch() {
    use tamarin_term::function_symbols::{AcSym, NoEqSym, Privacy};
    let dest = NoEqSym::new(
        b"missing".to_vec(),
        1,
        Privacy::Public,
        Constructability::Destructor,
    );
    let right = tamarin_term::term::unsafe_f_app(
        FunSym::Ac(AcSym::Mult),
        vec![tamarin_term::term::f_app_no_eq(
            dest,
            vec![tamarin_term::lterm::pub_term("a")],
        )],
    );
    let p = Process::Comb(
        ProcessCombinator::Let {
            left: tamarin_term::vterm::var_term(SapicLVar::untyped(LVar::new(
                "x",
                tamarin_term::lterm::LSort::Msg,
                0,
            ))),
            right,
            match_vars: Default::default(),
        },
        ProcessAnnotation::empty(),
        Box::new(Process::Action(
            tamarin_theory::sapic::SapicAction::Rep,
            ProcessAnnotation::empty(),
            Box::new(Process::Null(ProcessAnnotation::empty())).into(),
        ))
        .into(),
        Box::new(Process::Null(ProcessAnnotation::empty())).into(),
    );
    assert!(matches!(
        translate_let_destr(&Default::default(), p),
        Process::Null(_)
    ));
}

#[test]
fn case_b_eliminates_var_rhs_let() {
    // `let h = 't' in out(h)` (h not a match-var) → `out('t')`, Let gone.
    let h = svar("h");
    let body = Process::Action(
        SapicAction::ChOut {
            chan: None,
            msg: var_term(h.clone()),
        },
        ann(),
        Box::new(Process::Null(ann())).into(),
    );
    let lett = Process::Comb(
        ProcessCombinator::Let {
            left: var_term(h),
            right: pub_name("t"),
            match_vars: BTreeSet::new(),
        },
        ann(),
        Box::new(body).into(),
        Box::new(Process::Null(ann())).into(),
    );
    let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
    let out = translate_let_destr(&rules, lett);
    // The Let must be gone.  The top node is the substituted `out('t')`.
    // That is the RHS term itself, not just some constant.
    let Process::Action(SapicAction::ChOut { msg, .. }, _, body) = out else {
        panic!("expected Let to be eliminated to ChOut");
    };
    assert_eq!(msg, pub_name("t"), "h must be replaced by 't'");
    assert!(matches!(*body, Process::Null(_)));
}

#[test]
fn let_elimination_substitutes_compound_location() {
    // Upstream #922: annotations use ordinary term substitution, so an
    // eliminated let may replace its location variable with a pair.
    let h = svar("h");
    let location = tamarin_term::builtin::pair(pub_name("site"), pub_name("device"));
    let mut body_ann = ann();
    body_ann.parsing_ann.location = Some(var_term(h.clone()));
    let body = Process::Action(
        SapicAction::ChOut {
            chan: None,
            msg: pub_name("payload"),
        },
        body_ann,
        Box::new(Process::Null(ann())).into(),
    );
    let lett = Process::Comb(
        ProcessCombinator::Let {
            left: var_term(h),
            right: location.clone(),
            match_vars: BTreeSet::new(),
        },
        ann(),
        Box::new(body).into(),
        Box::new(Process::Null(ann())).into(),
    );

    let out = translate_let_destr(&BTreeSet::new(), lett);
    assert_eq!(out.annotation().parsing_ann.location, Some(location));
}

/// HS `mapTermsAction .. (fmap ff rest) ..` (Sapic/Process.hs:155) under
/// `apply subst` (Sapic/Process.hs:319-321): a Case-B `let`-elimination
/// rewrites the `let`-bound variable inside an embedded MSR's
/// `_restrict` formula, not only inside its fact rows.
#[test]
fn let_elimination_substitutes_into_an_msr_restriction() {
    use tamarin_theory::atom::ProtoAtom;
    use tamarin_theory::formula::ProtoFormula;

    let h = svar("h");
    // `[ ] --[ Ev(h) ]-> [ ]` restricted by `h = 'b'`.
    let ev = tamarin_theory::fact::Fact::new(
        tamarin_theory::fact::FactTag::Proto(tamarin_theory::fact::Multiplicity::Linear, "Ev", 1),
        vec![var_term(h.clone())],
    );
    let restr = ProtoFormula::Atom(ProtoAtom::EqE(
        var_term(tamarin_term::lterm::BVar::Free(h.clone())),
        VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "b"))),
    ));
    let msr = Process::Action(
        SapicAction::Msr {
            prems: Vec::new(),
            acts: vec![ev],
            concs: Vec::new(),
            rest: vec![restr],
            match_vars: BTreeSet::new(),
        },
        ann(),
        Box::new(Process::Null(ann())).into(),
    );
    // `let h = 't' in <msr>` — Case B drops the Let and substitutes `'t'`.
    let lett = Process::Comb(
        ProcessCombinator::Let {
            left: var_term(h),
            right: pub_name("t"),
            match_vars: BTreeSet::new(),
        },
        ann(),
        Box::new(msr).into(),
        Box::new(Process::Null(ann())).into(),
    );
    let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
    let out = translate_let_destr(&rules, lett);
    let Process::Action(SapicAction::Msr { acts, rest, .. }, _, _) = out else {
        panic!("expected Let to be eliminated to the MSR");
    };
    assert_eq!(
        acts[0].terms[0],
        pub_name("t"),
        "the action row is rewritten"
    );
    assert_eq!(
        rest[0],
        ProtoFormula::Atom(ProtoAtom::EqE(
            VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "t"))),
            VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "b"))),
        )),
        "and so is the embedded restriction"
    );
}

#[test]
fn let_substitution_rewrites_nested_let_and_msr_match_vars() {
    let x = svar("x");
    let a = svar("a");
    let image = tamarin_term::builtin::pair(var_term(a.clone()), pub_name("tag"));
    let subst = make_let_subst(&x, &image);

    let comb = ProcessCombinator::Let {
        left: var_term(x.clone()),
        right: pub_name("message"),
        match_vars: BTreeSet::from([x.clone()]),
    };
    let ProcessCombinator::Let { match_vars, .. } = subst_comb(&subst, &comb) else {
        panic!("expected Let")
    };
    assert_eq!(match_vars, BTreeSet::from([a.clone()]));

    let action = SapicAction::Msr {
        prems: Vec::new(),
        acts: Vec::new(),
        concs: Vec::new(),
        rest: Vec::new(),
        match_vars: BTreeSet::from([x]),
    };
    let SapicAction::Msr { match_vars, .. } = subst_action(&subst, &action) else {
        panic!("expected MSR")
    };
    assert_eq!(match_vars, BTreeSet::from([a]));
}

#[test]
fn case_c_keeps_nonvar_lhs_let_and_sets_else_branch() {
    // `let <a,b> = m in P else 0`: LHS is a pair (not a plain var), so the
    // Let is KEPT (Case C); else_branch is False (right child is Null).
    let a = svar("a");
    let b = svar("b");
    let pair = tamarin_term::builtin::pair(var_term(a), var_term(b));
    let lett = Process::Comb(
        ProcessCombinator::Let {
            left: pair,
            right: pub_name("m"),
            match_vars: BTreeSet::new(),
        },
        ann(),
        Box::new(Process::Null(ann())).into(),
        Box::new(Process::Null(ann())).into(),
    );
    let rules: BTreeSet<CtxtStRule> = BTreeSet::new();
    let out = translate_let_destr(&rules, lett);
    match out {
        Process::Comb(ProcessCombinator::Let { .. }, a2, _, _) => {
            assert!(
                !a2.else_branch,
                "else_branch must be False (Null right child)"
            );
        }
        other => panic!("expected kept Let, got {other:?}"),
    }
}
#[test]
fn deferred_lets_match_eager_substitution_with_branches_and_annotations() {
    fn build(seed: &mut u64, depth: usize) -> AnnotatedProcess<LVar> {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let n = (*seed >> 32) as usize;
        let v = SapicLVar::new(
            LVar::new("x", LSort::Msg, (n % 4) as u64),
            (n.is_multiple_of(9)).then(|| "Any".to_string()),
        );
        let w = SapicLVar::untyped(LVar::new("x", LSort::Msg, ((n / 5) % 4) as u64));
        let term = if n.is_multiple_of(3) {
            pub_name("a")
        } else if n % 3 == 1 {
            var_term(w.clone())
        } else {
            tamarin_term::builtin::hash(var_term(w.clone()))
        };
        let mut annotation = ann();
        annotation.parsing_ann.location = Some(var_term(v.clone()));
        if depth == 0 {
            return Process::Action(
                SapicAction::ChIn {
                    chan: None,
                    msg: term,
                    match_vars: BTreeSet::from([v]),
                },
                annotation,
                Box::new(Process::Null(ann())).into(),
            );
        }
        let left = build(seed, depth - 1);
        match n % 5 {
            0 => Process::Action(SapicAction::New(v), annotation, Box::new(left).into()),
            1 => Process::Comb(
                ProcessCombinator::Ndc,
                annotation,
                Box::new(left).into(),
                Box::new(build(seed, depth - 1)).into(),
            ),
            2 => Process::Comb(
                ProcessCombinator::Cond(tamarin_theory::formula::ProtoFormula::Atom(
                    tamarin_theory::atom::ProtoAtom::EqE(
                        var_term(tamarin_term::lterm::BVar::Free(v)),
                        tamarin_term::term::map_lits(&term, &mut |lit| match lit {
                            Lit::Con(c) => Lit::Con(*c),
                            Lit::Var(v) => Lit::Var(tamarin_term::lterm::BVar::Free(v.clone())),
                        }),
                    ),
                )),
                annotation,
                Box::new(left).into(),
                Box::new(build(seed, depth - 1)).into(),
            ),
            _ => Process::Comb(
                ProcessCombinator::Let {
                    left: var_term(v.clone()),
                    right: term,
                    match_vars: if n.is_multiple_of(7) {
                        BTreeSet::from([v])
                    } else {
                        BTreeSet::new()
                    },
                },
                annotation,
                Box::new(left).into(),
                Box::new(build(seed, depth - 1)).into(),
            ),
        }
    }
    for seed in 0..3000 {
        let process = build(&mut (seed + 1), 5);
        let expected = translate_let_destr_reference(&BTreeSet::new(), process.clone());
        assert_eq!(
            translate_let_destr(&BTreeSet::new(), process),
            expected,
            "seed {seed}"
        );
    }
}

#[test]
fn deep_unused_and_forward_alias_lets_use_one_process_walk() {
    tamarin_test_support::on_stack(256 * 1024, || {
        for aliases in [false, true] {
            let v = |i| SapicLVar::untyped(LVar::new("x", LSort::Msg, i));
            let mut p = Process::Action(
                SapicAction::ChOut {
                    chan: None,
                    msg: if aliases {
                        var_term(v(0))
                    } else {
                        pub_name("a")
                    },
                },
                ann(),
                Box::new(Process::Null(ann())).into(),
            );
            for i in (0..8192).rev() {
                p = Process::Comb(
                    ProcessCombinator::Let {
                        left: var_term(v(i)),
                        right: if aliases && i < 8191 {
                            var_term(v(i + 1))
                        } else {
                            pub_name("a")
                        },
                        match_vars: BTreeSet::new(),
                    },
                    ann(),
                    Box::new(p).into(),
                    Box::new(Process::Null(ann())).into(),
                );
            }
            let result = translate_let_destr(&BTreeSet::new(), p);
            let Process::Action(SapicAction::ChOut { msg, .. }, _, _) = result else {
                panic!("expected output");
            };
            assert_eq!(msg, pub_name("a"));
        }
    });
}
