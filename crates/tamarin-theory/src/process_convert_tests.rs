// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_term::lterm::LSort;
use tamarin_term::lterm::LVar;
use tamarin_term::maude_sig::pair_maude_sig;

/// The signature a def-less conversion runs against: `minimalMaudeSig`
/// (`pairFunSig`, Term/Maude/Signature.hs:224-226), which every theory
/// carries.
fn msig() -> MaudeSig {
    pair_maude_sig()
}

#[test]
fn convert_new_event_out_chain() {
    // new x:lol; event Test(x); out(f(f(x)))
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
    let inner = p::Process::Action {
        action: p::SapicAction::ChOut {
            chan: None,
            msg: ffx,
        },
        body: Box::new(p::Process::Null),
    };
    let evt = p::Process::Action {
        action: p::SapicAction::Event(p::Fact {
            persistent: false,
            name: "Test".into(),
            args: vec![xref],
            annotations: vec![],
        }),
        body: Box::new(inner),
    };
    let top = p::Process::Action {
        action: p::SapicAction::New(xspec),
        body: Box::new(evt),
    };
    let conv = convert_process(&top, &msig()).unwrap();
    // The complete spine converts. `New` carries the SAPIC type. The
    // event fact comes next. Then comes the out with the nested `f(f(x))`
    // payload.
    let Process::Action(SapicAction::New(v), _, body) = conv else {
        panic!("expected New at the top");
    };
    assert_eq!(v.var.name, "x");
    assert_eq!(v.stype.as_deref(), Some("lol"));
    let Process::Action(SapicAction::Event(fact), _, body) = body.into_inner() else {
        panic!("expected Event under the New");
    };
    assert_eq!(crate::fact::fact_tag_name(&fact.tag), "Test");
    assert_eq!(fact.terms.len(), 1);
    let Process::Action(SapicAction::ChOut { chan, msg }, _, body) = body.into_inner() else {
        panic!("expected ChOut under the Event");
    };
    assert!(chan.is_none(), "`out(t)` has no explicit channel");
    // `f(f(x))` has two nested applications over the bound variable.
    use tamarin_term::vterm::{Lit, VTerm};
    let VTerm::App(_, outer) = &msg else {
        panic!("expected f(f(x)), got {msg:?}");
    };
    let VTerm::App(_, inner) = &outer[0] else {
        panic!("expected the inner f(x)");
    };
    assert!(matches!(inner[0], VTerm::Lit(Lit::Var(_))));
    assert!(matches!(*body, Process::Null(_)));
}

fn event(name: &str) -> p::Process {
    p::Process::Action {
        action: p::SapicAction::Event(p::Fact {
            persistent: false,
            name: name.into(),
            args: vec![],
            annotations: vec![],
        }),
        body: Box::new(p::Process::Null),
    }
}

/// Returns the event name that a converted `event N` child carries. The
/// tests use it to assert that a combinator keeps its two children in the
/// source order.
fn child_event_name(p: &PlainProcess) -> String {
    let Process::Action(SapicAction::Event(f), _, _) = p else {
        panic!("expected an event child, got {p:?}");
    };
    crate::fact::fact_tag_name(&f.tag)
}

#[test]
fn convert_parallel_and_ndc() {
    for (comb, want) in [
        (p::ProcessComb::Parallel, ProcessCombinator::Parallel),
        (p::ProcessComb::Ndc, ProcessCombinator::Ndc),
    ] {
        let src = p::Process::Comb {
            comb,
            left: Box::new(event("A")),
            right: Box::new(event("B")),
        };
        let Process::Comb(got, _, l, r) = convert_process(&src, &msig()).unwrap() else {
            panic!("expected a combinator for {want:?}");
        };
        assert_eq!(got, want);
        // The children convert. The left and right order does not change.
        assert_eq!(child_event_name(&l), "A");
        assert_eq!(child_event_name(&r), "B");
    }
}

#[test]
fn convert_replication_becomes_rep_action() {
    let rep = p::Process::Replication(Box::new(event("A")));
    // `!P` becomes `Rep`. The replicated body is the only child of `Rep`.
    // The body must stay. The usual `0` must not replace it.
    let Process::Action(SapicAction::Rep, _, body) = convert_process(&rep, &msig()).unwrap() else {
        panic!("expected a Rep action");
    };
    let Process::Action(SapicAction::Event(f), _, _) = body.into_inner() else {
        panic!("expected the replicated event as Rep's child");
    };
    assert_eq!(crate::fact::fact_tag_name(&f.tag), "A");
}

#[test]
fn convert_at_annotation_sets_the_root_location() {
    let location = p::Term::Pair(vec![
        p::Term::PubLit("site".into()),
        p::Term::PubLit("device".into()),
    ]);
    let src = p::Process::AtAnnotation(Box::new(event("A")), location.clone());

    let converted = convert_process(&src, &msig()).unwrap();
    assert_eq!(
        converted.annotation().location,
        Some(term(&location, &msig()).unwrap())
    );
}

#[test]
fn convert_condeq() {
    let a = p::Term::Var(p::VarSpec {
        name: "a".into(),
        idx: 0,
        sort: LSort::Msg,
        typ: None,
    });
    let b = p::Term::PubLit("b".into());
    let cond = p::Process::Comb {
        comb: p::ProcessComb::Cond(p::Condition::Eq(a.clone(), b.clone())),
        left: Box::new(event("E")),
        right: Box::new(p::Process::Null),
    };
    let Process::Comb(ProcessCombinator::CondEq(l, r), _, then, els) =
        convert_process(&cond, &msig()).unwrap()
    else {
        panic!("expected a CondEq combinator");
    };
    // Both sides of `t1 = t2` convert, and they keep their order. The then
    // arm and the else arm stay on their own sides.
    assert_eq!(l, term(&a, &msig()).unwrap());
    assert_eq!(r, term(&b, &msig()).unwrap());
    assert_eq!(child_event_name(&then), "E");
    assert!(matches!(*els, Process::Null(_)));
}

#[test]
fn convert_cond_formula() {
    // `if <formula> then E else 0` converts to ProcessCombinator::Cond,
    // whose payload is the locally-nameless SAPIC formula the condition
    // parser builds.  A predicate atom stays `SyntacticSugar::Pred` until
    // the SAPIC rule injection (`tamarin_sapic::apply`) expands it.
    let frml = p::Formula::Atom(p::Atom::Pred(p::Fact {
        persistent: false,
        name: "P".into(),
        args: vec![p::Term::PubLit("c".into())],
        annotations: vec![],
    }));
    let cond = p::Process::Comb {
        comb: p::ProcessComb::Cond(p::Condition::Formula(frml.clone())),
        left: Box::new(event("E")),
        right: Box::new(p::Process::Null),
    };
    let Process::Comb(ProcessCombinator::Cond(got), _, then, _) =
        convert_process(&cond, &msig()).unwrap()
    else {
        panic!("expected a Cond combinator");
    };
    let want = crate::formula::ProtoFormula::Atom(crate::atom::ProtoAtom::Syntactic(
        crate::atom::SyntacticSugar::Pred(crate::fact::Fact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "P", 1),
            vec![tamarin_term::vterm::VTerm::Lit(
                tamarin_term::vterm::Lit::Con(tamarin_term::lterm::Name::new(
                    tamarin_term::lterm::NameTag::Pub,
                    "c",
                )),
            )],
        )),
    ));
    assert_eq!(got, want);
    assert_eq!(child_event_name(&then), "E");
}

#[test]
fn convert_lookup() {
    let cell = p::Term::PubLit("x".into());
    let lookup = p::Process::Comb {
        comb: p::ProcessComb::Lookup(
            cell.clone(),
            p::VarSpec {
                name: "v".into(),
                idx: 0,
                sort: LSort::Msg,
                typ: Some("cellty".into()),
            },
        ),
        left: Box::new(event("E")),
        right: Box::new(p::Process::Null),
    };
    let Process::Comb(ProcessCombinator::Lookup(t, v), _, found, notfound) =
        convert_process(&lookup, &msig()).unwrap()
    else {
        panic!("expected a Lookup combinator");
    };
    assert_eq!(t, term(&cell, &msig()).unwrap());
    // `lookup t as v` binds `v` and keeps its SAPIC type. A bare
    // variable is message-sorted.
    assert_eq!(v.var.name, "v");
    assert_eq!(v.var.sort, LSort::Msg);
    assert_eq!(v.stype.as_deref(), Some("cellty"));
    assert_eq!(child_event_name(&found), "E");
    assert!(matches!(*notfound, Process::Null(_)));
}

/// A bare token naming a declared 0-arity symbol is an APPLICATION in a
/// condition, not a free variable: HS's term parser resolves it against
/// the signature while parsing (`nullaryApp`,
/// Theory/Text/Parser/Term.hs:151,158-163), so `freesList` never reports
/// it and a substitution never rewrites it.
#[test]
fn a_declared_nullary_symbol_in_a_condition_is_an_application_not_a_free_variable() {
    let cond = |decl: &str| {
        let thy =
            tamarin_parser::parse_theory(&format!("theory T begin\n{decl}\nend"), &[]).unwrap();
        let msig = crate::elaborate::elaborate(&thy).unwrap().signature;
        let f = tamarin_parser::parser::parse_formula_str("Eq(c, k)", &msig).unwrap();
        sapic_from_parser(&f, &msig).unwrap()
    };
    let names = |f: &crate::sapic::SapicFormula| -> Vec<String> {
        crate::formula::formula_frees(f)
            .iter()
            .map(|v| v.var.name.to_string())
            .collect()
    };
    // Undeclared, `c` is an ordinary variable, so both are free — this is
    // what makes the assertion below discriminating.
    assert_eq!(names(&cond("")), vec!["c".to_string(), "k".to_string()]);
    assert_eq!(
        names(&cond("functions: c/0")),
        vec!["k".to_string()],
        "a declared nullary symbol is an application, not a variable"
    );
}

/// A quantifier binder in a condition is a `Bound` De Bruijn index, so it
/// is not a free variable and no substitution can reach it — HS's
/// `Foldable BVar` yields `Free` variables only
/// (Theory/Sapic/Term.hs:131-132#freesSapicTerm).
#[test]
fn a_bound_occurrence_in_a_condition_is_not_a_free_variable() {
    let msig = msig();
    let f = tamarin_parser::parser::parse_formula_str("Ex k. Eq(c, k)", &msig).unwrap();
    let got = sapic_from_parser(&f, &msig).unwrap();
    let frees: Vec<String> = crate::formula::formula_frees(&got)
        .iter()
        .map(|v| v.var.name.to_string())
        .collect();
    assert_eq!(frees, vec!["c".to_string()]);
}

#[test]
fn convert_insert_delete() {
    let ins = p::Process::Action {
        action: p::SapicAction::Insert(p::Term::PubLit("k".into()), p::Term::PubLit("v".into())),
        body: Box::new(p::Process::Action {
            action: p::SapicAction::Delete(p::Term::PubLit("k".into())),
            body: Box::new(p::Process::Null),
        }),
    };
    let key = term(&p::Term::PubLit("k".into()), &msig()).unwrap();
    let conv = convert_process(&ins, &msig()).unwrap();
    let Process::Action(SapicAction::Insert(k, v), _, body) = conv else {
        panic!("expected Insert at the top");
    };
    assert_eq!(k, key);
    assert_eq!(v, term(&p::Term::PubLit("v".into()), &msig()).unwrap());
    // The `delete` below it also converts. It keeps its key term.
    let Process::Action(SapicAction::Delete(dk), _, _) = body.into_inner() else {
        panic!("expected Delete under the Insert");
    };
    assert_eq!(dk, key);
}

// -- pattern (`=t`) splitting -------------------------------------------
//
// HS tags pattern variables at the leaf. The rule is `ltypedpatternlit =
// vlit sapicpatternvar` (Parser/Sapic.hs:52-53). A `sapicpatternvar` is an
// optional `=` in front of a single `sapicvar` (Token.hs:512-519). A
// pattern term is therefore a `SapicNTerm PatternSapicLVar`. Every
// variable in that term carries a `PatternBind` or `PatternMatch` tag.
// `unpattern = fmap (fmap unpatternVar)` drops the tags
// (Pattern.hs:54-60). `extractMatchingVariables pt = S.fromList $ foldMap
// (foldMap isPatternMatch) pt` (Pattern.hs:92-96) collects the matched
// ones. It is a foldMap over the complete term. The depth therefore does
// not matter, and the result is a set.

/// Builds `x` or `x:ty` as a parser-AST variable leaf. A bare variable is
/// message-sorted.
fn pvar(name: &str, typ: Option<&str>) -> p::Term {
    p::Term::Var(p::VarSpec {
        name: name.into(),
        idx: 0,
        sort: LSort::Msg,
        typ: typ.map(Into::into),
    })
}

/// Builds the `SapicLVar` that [`pvar`] elaborates to. A `sapicvar` keeps
/// the `:type` annotation (Token.hs:506-510). A `PatternSapicLVar` wraps a
/// complete `SapicLVar` (Pattern.hs:42-44). The type is therefore part of
/// the `extractMatchingVariables` set element.
fn svar(name: &str, typ: Option<&str>) -> SapicLVar {
    SapicLVar::new(LVar::new(name, LSort::Msg, 0), typ.map(Into::into))
}

fn pfact(name: &str, args: Vec<p::Term>) -> p::Fact {
    p::Fact {
        persistent: false,
        name: name.into(),
        args,
        annotations: vec![],
    }
}

/// The `=t` marker.
fn pat_match(t: p::Term) -> p::Term {
    p::Term::PatMatch(Box::new(t))
}

#[test]
fn msr_unpatterns_every_row_but_takes_match_vars_from_the_premises_only() {
    // HS (Parser/Sapic.hs:155-161):
    //   (l,a,r,phi) <- try $ genericRule sapicpatternvar (PatternBind <$> sapicnodevar)
    //   let matchVars =  foldMap (foldMap extractMatchingVariables) l
    //   let f = fmap (fmap unpattern)
    //   ... then return (MSR (f l) (f a) (f r) (g phi) matchVars, mempty)
    // The `matchVars` fold runs over `l` only. The code applies `f`
    // (unpattern) to all three rows.
    let deep =
        |leaf: p::Term| p::Term::App("h".into(), vec![p::Term::Pair(vec![leaf, pvar("y", None)])]);
    let prems = vec![pfact("In", vec![deep(pat_match(pvar("x", None)))])];
    // HS never gives this code a `=` in the action rows or the conclusion
    // rows. The `validMSR` guards `(_,[]) <- freesPatternFactList a` and
    // `(_,[]) <- freesPatternFactList r` (Pattern.hs:79-89) fail the parse
    // first. The pinned oracle also rejects such a source. The half that
    // this test pins is the HS half. Whatever those rows contain, they add
    // nothing to `matchVars`.
    let acts = vec![pfact("Ev", vec![pat_match(pvar("z", None))])];
    let concs = vec![pfact("Out", vec![pat_match(pvar("w", None))])];
    let msr = p::Process::Action {
        action: p::SapicAction::Msr {
            prems,
            acts,
            concs,
            restrictions: vec![],
        },
        body: Box::new(p::Process::Null),
    };
    let Process::Action(
        SapicAction::Msr {
            prems,
            acts,
            concs,
            rest,
            match_vars,
        },
        _,
        _,
    ) = convert_process(&msr, &msig()).unwrap()
    else {
        panic!("expected an Msr action");
    };
    // The set holds the premise variables only. `z` and `w` are absent,
    // although they carry `=`.
    assert_eq!(match_vars, BTreeSet::from([svar("x", None)]));
    // The conversion unpatterns every row. A `PatMatch` that survives
    // makes `term_to_sapic_term` answer `None`, and then the conversion
    // fails. The comparison against the marker-free terms therefore pins
    // two things. It pins the removal of the markers, and it pins the rows
    // that the removal reaches.
    assert_eq!(
        prems[0].terms.to_vec(),
        vec![term(&deep(pvar("x", None)), &msig()).unwrap()],
        "the premise keeps its shape with the `=` marker removed"
    );
    assert_eq!(
        acts[0].terms.to_vec(),
        vec![term(&pvar("z", None), &msig()).unwrap()]
    );
    assert_eq!(
        concs[0].terms.to_vec(),
        vec![term(&pvar("w", None), &msig()).unwrap()]
    );
    assert!(rest.is_empty());
}

#[test]
fn msr_restrict_formulas_lose_their_markers_and_add_no_match_vars() {
    // HS applies `g = fmap (fmap unpatternVar)` to the embedded
    // restriction formulas (Parser/Sapic.hs:158-160): every `=` marker
    // goes away, and `matchVars` still folds over the premises only.
    // The strip runs BEFORE the locally-nameless formula is built, and
    // the second assertion below is what pins that order — the end-to-end
    // pin is `scripts/divergence_fixtures/sapic_msr_pattern_restrict`.
    let ispec = p::VarSpec {
        name: "i".into(),
        idx: 0,
        sort: LSort::Node,
        typ: None,
    };
    // One template built twice — with the marker and without — so the
    // wrapped leaf is the only delta under test.  `=x = x` at the top and
    // a marker nested under a quantifier inside an action fact's
    // argument, so the strip provably recurses.
    let formulas = |wrap: fn(p::Term) -> p::Term| {
        vec![
            p::Formula::Atom(p::Atom::Eq(wrap(pvar("x", None)), pvar("x", None))),
            p::Formula::Forall(
                vec![ispec.clone()],
                Box::new(p::Formula::Atom(p::Atom::Action(
                    pfact("Ev", vec![wrap(pvar("x", None))]),
                    p::Term::Var(ispec.clone()),
                ))),
            ),
        ]
    };
    let marked = formulas(pat_match);
    let plain = formulas(|t| t);
    let msr = p::Process::Action {
        action: p::SapicAction::Msr {
            prems: vec![pfact("In", vec![pvar("x", None)])],
            acts: vec![],
            concs: vec![pfact("Out", vec![pvar("x", None)])],
            restrictions: marked.clone(),
        },
        body: Box::new(p::Process::Null),
    };
    let Process::Action(
        SapicAction::Msr {
            rest, match_vars, ..
        },
        _,
        _,
    ) = convert_process(&msr, &msig()).unwrap()
    else {
        panic!("expected an Msr action");
    };
    let want: Vec<_> = plain
        .iter()
        .map(|f| sapic_from_parser(f, &msig()).unwrap())
        .collect();
    assert_eq!(rest, want, "both formulas come out marker-free");
    assert!(
        match_vars.is_empty(),
        "a `=` inside `_restrict` contributes no match-var"
    );
    // A marker that survives to the formula builder has no SAPIC term to
    // read it as, so leaving out the strip fails the conversion.
    for f in &marked {
        assert!(
            sapic_from_parser(f, &msig()).is_err(),
            "a `=` marker must not reach the formula builder"
        );
    }
}

#[test]
fn let_and_chin_patterns_split_matched_leaves_out_of_the_bound_term() {
    // HS builds `let` as `ProcessComb (Let (unpattern t1) t2
    // (extractMatchingVariables t1)) mempty p' q` (Parser/Sapic.hs:268-269).
    // HS builds `in(c,pt)` as `ChIn maybeChannel (unpattern pt)
    // (extractMatchingVariables pt)` (Parser/Sapic.hs:113-114). Both sides
    // use the same pair of Pattern.hs functions.
    //
    // `extractMatchingVariables` returns an `S.Set SapicLVar`. The two
    // `=x:ty` leaves below therefore collapse to one element, and that
    // element carries the `:ty` annotation. `y` is bound, not matched, so
    // it stays out of the set.
    let marked = p::Term::Pair(vec![
        pat_match(pvar("x", Some("ty"))),
        p::Term::Pair(vec![pvar("y", None), pat_match(pvar("x", Some("ty")))]),
    ]);
    let plain = p::Term::Pair(vec![
        pvar("x", Some("ty")),
        p::Term::Pair(vec![pvar("y", None), pvar("x", Some("ty"))]),
    ]);
    let want_vars = BTreeSet::from([svar("x", Some("ty"))]);

    let lt = p::Process::Comb {
        comb: p::ProcessComb::Let {
            pat: marked.clone(),
            value: p::Term::PubLit("v".into()),
        },
        left: Box::new(event("E")),
        right: Box::new(p::Process::Null),
    };
    let Process::Comb(
        ProcessCombinator::Let {
            left,
            right,
            match_vars,
        },
        _,
        _,
        _,
    ) = convert_process(&lt, &msig()).unwrap()
    else {
        panic!("expected a Let combinator");
    };
    assert_eq!(left, term(&plain, &msig()).unwrap(), "`unpattern t1`");
    assert_eq!(match_vars, want_vars, "`extractMatchingVariables t1`");
    // The right-hand side is a `sapicterm`, not a pattern. The conversion
    // leaves it unchanged.
    assert_eq!(right, term(&p::Term::PubLit("v".into()), &msig()).unwrap());

    let chin = p::Process::Action {
        action: p::SapicAction::ChIn {
            chan: Some(p::Term::PubLit("c".into())),
            msg: marked,
        },
        body: Box::new(p::Process::Null),
    };
    let Process::Action(
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        },
        _,
        _,
    ) = convert_process(&chin, &msig()).unwrap()
    else {
        panic!("expected a ChIn action");
    };
    assert_eq!(
        chan,
        Some(term(&p::Term::PubLit("c".into()), &msig()).unwrap())
    );
    assert_eq!(msg, term(&plain, &msig()).unwrap(), "`unpattern pt`");
    assert_eq!(match_vars, want_vars, "`extractMatchingVariables pt`");
}
#[test]
fn deep_process_conversion_and_pattern_stripping_use_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut p = p::Process::Null;
        for _ in 0..20_000 {
            p = p::Process::Replication(Box::new(p));
        }
        let converted = convert_process(&p, &msig()).unwrap();
        drop((converted, p));
        let var = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        };
        let mut t = p::Term::PatMatch(Box::new(p::Term::Var(var.clone())));
        for _ in 0..20_000 {
            t = p::Term::App("f".into(), vec![t]);
        }
        let mut matched = BTreeSet::new();
        let stripped = strip_pat_match(&t, &mut matched);
        assert_eq!(matched, [varspec_to_sapic(&var)].into());
        drop((t, stripped));
    });
}
