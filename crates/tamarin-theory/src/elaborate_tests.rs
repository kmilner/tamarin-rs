// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_parser::parse_theory;

/// A bundle carrying one `<tag>_<set>` name in every set, so a test can
/// tell which bundle is installed and which set a name came from.
fn tagged_user_funs(tag: &str) -> CollectedUserFuns {
    let one = |kind: &str| BTreeSet::from([format!("{tag}_{kind}")]);
    let ac_name = format!("{tag}_ac");
    CollectedUserFuns {
        unary: one("unary"),
        nullary: one("nullary"),
        private: one("private"),
        destructor: one("destructor"),
        ac: BTreeMap::from([(
            ac_name.clone(),
            AcFctSym::new(
                ac_name.into_bytes(),
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            ),
        )]),
        noeq_names: one("noeq"),
        ndc: one("ndc"),
        ndc_diff: one("ndc_diff"),
        bp: false,
    }
}

#[test]
fn user_funs_guards_restore_the_displaced_bundle_on_drop() {
    let outer = tagged_user_funs("outer");
    let inner = tagged_user_funs("inner");
    assert!(
        !with_user_fun_sets(|f| f.is_user_ac_fun("outer_ac")),
        "thread starts with empty sets"
    );

    let outer_guard = set_user_funs_from_collected(&outer);
    assert!(with_user_fun_sets(|f| f.is_user_ac_fun("outer_ac")));
    assert!(is_user_nullary_fun("outer_nullary"));
    {
        let _inner_guard = set_user_funs_from_collected(&inner);
        assert!(with_user_fun_sets(|f| f.is_user_ac_fun("inner_ac")));
        assert!(!with_user_fun_sets(|f| f.is_user_ac_fun("outer_ac")));
    }
    // The nested guard's drop restores every set of the outer bundle.
    assert!(with_user_fun_sets(|f| f.is_user_ac_fun("outer_ac")));
    assert!(!with_user_fun_sets(|f| f.is_user_ac_fun("inner_ac")));
    assert!(with_user_fun_sets(|f| f.is_user_unary_fun("outer_unary")));
    assert_eq!(snapshot_user_funs().nullary, outer.nullary);

    drop(outer_guard);
    assert!(!with_user_fun_sets(|f| f.is_user_ac_fun("outer_ac")));
    assert!(!is_user_nullary_fun("outer_nullary"));
    assert!(with_user_fun_sets(|f| f.unary.is_empty()));
}

#[test]
fn maude_sig_nullary_guard_replaces_only_the_nullary_set() {
    let base = tagged_user_funs("base");
    let _base_guard = set_user_funs_from_collected(&base);
    {
        let _nullary_guard = MaudeSigNullaryGuard::set(&xor_maude_sig());
        // `xor` contributes the 0-arity constant `zero`, which displaces
        // the installed nullary set outright.
        assert!(is_user_nullary_fun("zero"));
        assert!(!is_user_nullary_fun("base_nullary"));
        // Every other set is carried over unchanged.
        assert!(with_user_fun_sets(|f| f.is_user_ac_fun("base_ac")));
        with_user_fun_sets(|f| {
            assert!(f.is_user_unary_fun("base_unary"));
            assert_eq!(f.user_fun_privacy("base_private"), Privacy::Private);
            assert_eq!(
                f.user_fun_constructability("base_destructor"),
                Constructability::Destructor
            );
            assert_eq!(f.user_fun_ndc("base_ndc"), NdcState::IsNdc);
            assert_eq!(f.user_fun_ndc("base_ndc_diff"), NdcState::IsNdcDiff);
        });
    }
    assert!(!is_user_nullary_fun("zero"));
    assert!(is_user_nullary_fun("base_nullary"));
    assert!(with_user_fun_sets(|f| f.is_user_ac_fun("base_ac")));
}

#[test]
fn installed_bundle_resolves_every_attribute_in_term_to_lnterm() {
    use tamarin_term::function_symbols::{AcSym, FunSym};

    let src = "theory T begin\n\
                   functions: add/2 [AC], sec/0 [private], dec/1 [destructor], nd/2 [NDC]\n\
                   end";
    let thy = parse_theory(src, &[]).unwrap();
    let _guard = set_user_funs_for_theory(&thy);

    let x = parser_var("x", 0, p::SortHint::Msg);
    let y = parser_var("y", 0, p::SortHint::Msg);

    // `ac` set: a prefix application of an `[AC]` symbol lowers to an AC
    // application carrying the declaration's flags.
    let ac_app = p::Term::App("add".into(), vec![x.clone(), y.clone()]);
    match term_to_lnterm(&ac_app).unwrap() {
        Term::App(FunSym::Ac(AcSym::AcFct(sym)), _) => {
            assert_eq!(String::from_utf8_lossy(sym.name), "add");
            assert_eq!(sym.privacy, Privacy::Public);
            assert_eq!(sym.constructability, Constructability::Constructor);
            assert_eq!(sym.ndc, NdcState::NotNdc);
        }
        other => panic!("expected an AC application, got {other:?}"),
    }

    // `private` set + `nullary` set: a bare untagged name declared `/0`
    // becomes a 0-arity private constant, not a free variable.
    match term_to_lnterm(&parser_var("sec", 0, p::SortHint::Untagged)).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert!(args.is_empty());
            assert_eq!(sym.arity, 0);
            assert_eq!(sym.privacy, Privacy::Private);
        }
        other => panic!("expected a nullary constant, got {other:?}"),
    }

    // `destructor` set + `unary` set: the surplus arguments fold into one
    // pair, and the symbol is a destructor.
    let folded = p::Term::App("dec".into(), vec![x.clone(), y.clone()]);
    match term_to_lnterm(&folded).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert_eq!(sym.arity, 1);
            assert_eq!(args.len(), 1, "arity-1 fold should pair the arguments");
            assert_eq!(sym.constructability, Constructability::Destructor);
        }
        other => panic!("expected a destructor application, got {other:?}"),
    }

    // `ndc` set.
    let ndc_app = p::Term::App("nd".into(), vec![x, y]);
    match term_to_lnterm(&ndc_app).unwrap() {
        Term::App(FunSym::NoEq(sym), _) => assert_eq!(sym.ndc, NdcState::IsNdc),
        other => panic!("expected an NDC application, got {other:?}"),
    }
}

/// `diff(a, b)` (reachable with the `diff` flag set) lowers to the
/// PRIVATE `diffSym`, not a public symbol that merely shares the name.
///
/// HS `diffSym = (diffSymString,(2,Private,Constructor,NotNDC))`
/// (Term/Term/FunctionSymbols.hs:249).  Privacy is observable three ways:
/// the Maude operator is `tamPCFUdiff` (`funSymEncodeAttr`,
/// Term/Maude/Parser.hs:76-88 — the port's `fun_sym_encode_attr`), the
/// `NoEqSym` equality that `viewTerm2`/`ppTerm` use to recognise a diff
/// term compares the whole tuple, and `contains_private` keys off it.
#[test]
fn diff_term_lowers_to_the_private_diff_symbol() {
    use tamarin_term::function_symbols::{diff_sym, AcState, FunSym};
    use tamarin_term::maude_print::fun_sym_encode_attr;

    let x = parser_var("x", 0, p::SortHint::Msg);
    let y = parser_var("y", 0, p::SortHint::Msg);
    let t = p::Term::Diff(Box::new(x), Box::new(y));

    match term_to_lnterm(&t).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert_eq!(args.len(), 2);
            assert_eq!(String::from_utf8_lossy(sym.name), "diff");
            assert_eq!(sym.arity, 2);
            assert_eq!(sym.privacy, Privacy::Private);
            assert_eq!(sym.constructability, Constructability::Constructor);
            assert_eq!(sym.ndc, NdcState::NotNdc);
            // Whole-tuple equality: what the `s == diffSym` guards test.
            assert_eq!(sym, diff_sym());
            assert_eq!(
                fun_sym_encode_attr(sym.privacy, sym.constructability, AcState::NotAc, sym.ndc),
                "PCFU",
                "Maude emission must be `tamPCFUdiff`"
            );
        }
        other => panic!("expected a diff application, got {other:?}"),
    }
}

#[test]
fn canonicalize_ac_in_pterm_flattens_and_sorts() {
    use tamarin_parser::ast as p;
    // Build: BinOp(Xor, BinOp(Xor, na, k), nb)
    let na = p::Term::Var(p::VarSpec {
        typ: None,
        name: "na".into(),
        sort: p::SortHint::Msg,
        idx: 0,
    });
    let k = p::Term::Var(p::VarSpec {
        typ: None,
        name: "k".into(),
        sort: p::SortHint::Fresh,
        idx: 0,
    });
    let nb = p::Term::Var(p::VarSpec {
        typ: None,
        name: "nb".into(),
        sort: p::SortHint::Fresh,
        idx: 0,
    });
    let inner = p::Term::BinOp(p::BinOp::Xor, Box::new(na.clone()), Box::new(k.clone()));
    let outer = p::Term::BinOp(p::BinOp::Xor, Box::new(inner), Box::new(nb.clone()));
    // Canonicalised right-fold should be `BinOp(Xor, k, BinOp(Xor, nb, na))`.
    let canon = canonicalize_ac_in_pterm(&outer);
    let expected = p::Term::BinOp(
        p::BinOp::Xor,
        Box::new(k),
        Box::new(p::Term::BinOp(p::BinOp::Xor, Box::new(nb), Box::new(na))),
    );
    assert_eq!(canon, expected);
    // And the LNTerm-side via `term_to_lnterm` should produce the
    // flat sorted form (already byte-identical to HS).
    let l = term_to_lnterm(&outer).unwrap();
    assert_eq!(
        tamarin_term::pretty::pretty_lnterm(&l),
        "(~k\u{2295}~nb\u{2295}na)"
    );
}

// The prefix-`[AC]` arm reads the bundle the entry point snapshotted, so
// the `[AC]` classification must reach NESTED `App` nodes as well as the
// root — through the plain term entry and through the fact wrapper, which
// takes the snapshot once for the whole fact.
#[test]
fn canonicalize_ac_in_pterm_sees_the_installed_ac_set_at_every_depth() {
    use tamarin_parser::ast as p;
    let v = |name: &str| {
        p::Term::Var(p::VarSpec {
            typ: None,
            name: name.into(),
            sort: p::SortHint::Msg,
            idx: 0,
        })
    };
    let op = p::BinOp::AcFct(tamarin_term::intern::intern_str("add"));
    // `h(add(add(b, a), c))`: the AC application sits one level below an
    // ordinary `App`.
    let nested = p::Term::App(
        "add".into(),
        vec![p::Term::App("add".into(), vec![v("b"), v("a")]), v("c")],
    );
    let wrapped = p::Term::App("h".into(), vec![nested.clone()]);
    // Flattened, sorted (LVar order: same idx and sort, so by name) and
    // re-folded right-leaning.
    let canon_ac = p::Term::BinOp(
        op,
        Box::new(v("a")),
        Box::new(p::Term::BinOp(op, Box::new(v("b")), Box::new(v("c")))),
    );

    // With no bundle installed `add` is an ordinary function symbol.
    assert_eq!(canonicalize_ac_in_pterm(&wrapped), wrapped);

    let funs = CollectedUserFuns {
        ac: BTreeMap::from([(
            "add".to_string(),
            AcFctSym::new(
                b"add".to_vec(),
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            ),
        )]),
        ..CollectedUserFuns::default()
    };
    let _guard = set_user_funs_from_collected(&funs);
    assert_eq!(
        canonicalize_ac_in_pterm(&wrapped),
        p::Term::App("h".into(), vec![canon_ac.clone()])
    );
    let fact = p::Fact {
        persistent: false,
        name: "F".into(),
        args: vec![wrapped],
        annotations: Vec::new(),
    };
    assert_eq!(
        canonicalize_ac_in_pfact(&fact).args,
        vec![p::Term::App("h".into(), vec![canon_ac])]
    );
}

#[test]
fn elaborate_empty_theory() {
    let p = parse_theory("theory T begin end", &[]).unwrap();
    let t = elaborate(&p).unwrap();
    assert_eq!(t.name, "T");
}

#[test]
fn elaborate_builtins() {
    let p = parse_theory("theory T begin builtins: hashing, signing end", &[]).unwrap();
    let t = elaborate(&p).unwrap();
    // hashing adds h/1, signing adds sign/2 etc.
    let funs: Vec<String> = t
        .signature
        .maude_sig
        .st_fun_syms
        .iter()
        .map(|s| String::from_utf8_lossy(s.name).to_string())
        .collect();
    assert!(funs.iter().any(|n| n == "h"), "expected h: {:?}", funs);
    assert!(
        funs.iter().any(|n| n == "sign"),
        "expected sign: {:?}",
        funs
    );
}

// Matching-tuple redeclarations stay legal in BOTH orders (corpus
// regression fixtures issue753-5 / issue753-6, oracle probe td).
#[test]
fn builtin_matching_redeclaration_accepted() {
    for src in [
        "theory T begin builtins: hashing functions: h/1 end",
        "theory T begin functions: h/1 builtins: hashing end",
    ] {
        let p = parse_theory(src, &[]).unwrap();
        let t = elaborate(&p).unwrap();
        let hs = t
            .signature
            .maude_sig
            .st_fun_syms
            .iter()
            .filter(|s| s.name == b"h")
            .count();
        assert_eq!(hs, 1, "exactly one h sym for {src:?}");
    }
}

// `dest-pairing` is exempt from the builtins-arm FUNCTION check
// (Theory/Text/Parser/Signature.hs:124) — oracle probes tb / tc — and a destructor
// fst re-declaration matches its merged tuple, so the pre-check
// passes too.
#[test]
fn dest_pairing_exempt_from_builtins_arm_check() {
    for src in [
        "theory T begin functions: fst/1 builtins: dest-pairing end",
        "theory T begin builtins: dest-pairing functions: fst/1 [destructor] end",
    ] {
        let p = parse_theory(src, &[]).unwrap();
        let t = elaborate(&p).unwrap();
        let fst = t
            .signature
            .maude_sig
            .st_fun_syms
            .iter()
            .find(|s| s.name == b"fst")
            .unwrap();
        assert_eq!(
            fst.constructability,
            Constructability::Destructor,
            "for {src:?}"
        );
    }
}

// Enable-flag-only builtins (dh/bp/mset/xor/nat) have empty
// `stFunSyms`, so they reserve nothing (oracle probe te: exp/3 is
// accepted alongside diffie-hellman's exp/2).
#[test]
fn enable_flag_builtins_reserve_no_names() {
    let src = "theory T begin builtins: diffie-hellman functions: exp/3 end";
    let p = parse_theory(src, &[]).unwrap();
    let t = elaborate(&p).unwrap();
    assert!(t
        .signature
        .maude_sig
        .st_fun_syms
        .iter()
        .any(|s| s.name == b"exp" && s.arity == 3));
}

// Without `dest-pairing`, `fst`/`snd` are not builtin-reserved, so the
// pre-check is silent and the name-only short-circuit
// (Theory/Text/Parser/Signature.hs:217)
// returns the existing symbol: the signature keeps the CONSTRUCTOR
// variant — oracle probe t1.
#[test]
fn fst_destructor_redeclaration_leaves_signature_untouched() {
    let src = "theory T begin functions: fst/1 [destructor] end";
    let p = parse_theory(src, &[]).unwrap();
    let t = elaborate(&p).unwrap();
    let fst = t
        .signature
        .maude_sig
        .st_fun_syms
        .iter()
        .find(|s| s.name == b"fst")
        .unwrap();
    assert_eq!(fst.constructability, Constructability::Constructor);
}

#[test]
fn elaborate_simple_rule() {
    let src = r#"theory T begin
            rule R: [Fr(~k)] --[Foo(~k)]-> [Out(~k)]
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let t = elaborate(&p).unwrap();
    let rules: Vec<_> = t.rules().collect();
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].name(), "R");
}

#[test]
fn elaborate_lemma_passthrough() {
    let src = r#"theory T begin
            rule R: [Fr(~k)] --[Foo(~k)]-> [Out(~k)]
            lemma secret: "All k #i. Foo(k) @ i ==> F"
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let t = elaborate(&p).unwrap();
    assert_eq!(t.lemmas().count(), 1);
    let l = t.lemmas().next().unwrap();
    assert_eq!(l.name, "secret");
    assert_eq!(l.trace_quantifier, TraceQuantifier::AllTraces);
}

// =========================================================================
// lnterm_to_term round-tripping correctness
// =========================================================================

fn parser_var(name: &str, idx: u64, sort: p::SortHint) -> p::Term {
    p::Term::Var(p::VarSpec {
        name: name.into(),
        idx,
        sort,
        typ: None,
    })
}

#[test]
fn lnterm_to_term_round_trip_var_msg() {
    let v = parser_var("x", 7, p::SortHint::Msg);
    let lt = term_to_lnterm(&v).unwrap();
    let back = lnterm_to_term(&lt);
    assert_eq!(back, v);
}

#[test]
fn lnterm_to_term_round_trip_var_fresh() {
    let v = parser_var("k", 3, p::SortHint::Fresh);
    let lt = term_to_lnterm(&v).unwrap();
    assert_eq!(lnterm_to_term(&lt), v);
}

#[test]
fn lnterm_to_term_round_trip_var_node() {
    let v = parser_var("i", 0, p::SortHint::Node);
    let lt = term_to_lnterm(&v).unwrap();
    assert_eq!(lnterm_to_term(&lt), v);
}

#[test]
fn lnterm_to_term_round_trip_pub_lit() {
    let pl = p::Term::PubLit("Alice".into());
    let lt = term_to_lnterm(&pl).unwrap();
    assert_eq!(lnterm_to_term(&lt), pl);
}

#[test]
fn lnterm_to_term_round_trip_fresh_lit() {
    let fl = p::Term::FreshLit("n42".into());
    let lt = term_to_lnterm(&fl).unwrap();
    assert_eq!(lnterm_to_term(&lt), fl);
}

#[test]
fn lnterm_to_term_round_trip_pair() {
    // <a, b> → pair(a, b) → back to Pair([a, b]).
    let pair = p::Term::Pair(vec![
        parser_var("a", 0, p::SortHint::Msg),
        parser_var("b", 0, p::SortHint::Msg),
    ]);
    let lt = term_to_lnterm(&pair).unwrap();
    let back = lnterm_to_term(&lt);
    assert_eq!(back, pair);
}

#[test]
fn lnterm_to_term_round_trip_triple() {
    // <a, b, c> → pair(a, pair(b, c)) → back to Pair([a, b, c]).
    let triple = p::Term::Pair(vec![
        parser_var("a", 0, p::SortHint::Msg),
        parser_var("b", 0, p::SortHint::Msg),
        parser_var("c", 0, p::SortHint::Msg),
    ]);
    let lt = term_to_lnterm(&triple).unwrap();
    let back = lnterm_to_term(&lt);
    assert_eq!(back, triple);
}

#[test]
fn lnterm_to_term_round_trip_nested_app() {
    // f(g(x), y) → ... → f(g(x), y).
    let inner = p::Term::App("g".into(), vec![parser_var("x", 0, p::SortHint::Msg)]);
    let outer = p::Term::App(
        "f".into(),
        vec![inner.clone(), parser_var("y", 0, p::SortHint::Msg)],
    );
    let lt = term_to_lnterm(&outer).unwrap();
    let back = lnterm_to_term(&lt);
    assert_eq!(back, outer);
}

// =========================================================================
// Rule let-block desugaring
// =========================================================================
//
// Haskell tamarin desugars `rule R: let x = t in body` by substituting
// `t` for occurrences of `x` in the body before any further analysis.
// These tests pin our `apply_let_block` to the same semantics.

#[test]
fn let_block_substitutes_in_premises() {
    // rule R: let r = ~k in [In(r)] --[]-> []
    // After desugaring: [In(~k)] --[]-> []
    let src = r#"theory T begin
            rule R: let r = ~k in [In(r), Fr(~k)] --[]-> []
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let r = match &p.items[0] {
        p::TheoryItem::Rule(r) => r,
        _ => unreachable!(),
    };
    let desugared = apply_let_block(r);
    assert!(desugared.let_block.is_empty());
    // Premise In should now hold ~k (Var with sort Fresh), not local `r`.
    let in_fact = &desugared.premises[0];
    assert_eq!(in_fact.name, "In");
    match &in_fact.args[0] {
        p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
        other => panic!("expected ~k after subst, got {:?}", other),
    }
}

#[test]
fn let_block_sequential_bindings() {
    // let a = ~k; b = h(a) in [In(b)] --[]-> []
    // After desugaring: [In(h(~k))]
    // `builtins: hashing` declares `h/1` — the parser resolves prefix
    // applications through `lookupArity` and an undeclared head would
    // reparse as a variable and fail (oracle probes p05/p25).
    let src = r#"theory T begin
            builtins: hashing
            rule R: let a = ~k b = h(a) in [In(b), Fr(~k)] --[]-> []
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let r = p
        .items
        .iter()
        .find_map(|it| match it {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap();
    let desugared = apply_let_block(r);
    let in_fact = &desugared.premises[0];
    match &in_fact.args[0] {
        p::Term::App(name, args) if name == "h" => match &args[0] {
            p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
            other => panic!("expected h(~k), got h({:?})", other),
        },
        other => panic!("expected h(~k), got {:?}", other),
    }
}

#[test]
fn let_block_forward_reference_stays_free() {
    // HS bottom-up semantics (`letBlock`'s `toSubst = foldr1 compose .
    // map (substFromList . return)`, Theory/Text/Parser/Let.hs:22-35): a binding whose
    // RHS references a LATER binding keeps that name as a free var —
    // by the time `a`'s application introduces `b` into the body,
    // `b`'s singleton substitution has already been applied.
    //   let a = h(b) b = ~k in [In(a), Fr(~k)]
    // After desugaring: In(h(b)) with `b` a free Msg-var, NOT h(~k).
    // `builtins: hashing` declares `h/1` — see
    // `let_block_sequential_bindings`.
    let src = r#"theory T begin
            builtins: hashing
            rule R: let a = h(b) b = ~k in [In(a), Fr(~k)] --[]-> []
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let r = p
        .items
        .iter()
        .find_map(|it| match it {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap();
    let desugared = apply_let_block(r);
    let in_fact = &desugared.premises[0];
    match &in_fact.args[0] {
        p::Term::App(name, args) if name == "h" => match &args[0] {
            p::Term::Var(vs) if vs.name == "b" && vs.sort != p::SortHint::Fresh => {}
            other => panic!("expected h(b) with free b, got h({:?})", other),
        },
        other => panic!("expected h(b), got {:?}", other),
    }
}

#[test]
fn let_block_substitutes_in_actions_and_conclusions() {
    let src = r#"theory T begin
            rule R: let r = ~k in [Fr(~k)] --[Use(r)]-> [Out(r)]
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let r = match &p.items[0] {
        p::TheoryItem::Rule(r) => r,
        _ => unreachable!(),
    };
    let desugared = apply_let_block(r);
    let use_act = &desugared.actions[0];
    match &use_act.args[0] {
        p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
        other => panic!("expected Use(~k), got Use({:?})", other),
    }
    let out_conc = &desugared.conclusions[0];
    match &out_conc.args[0] {
        p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
        other => panic!("expected Out(~k), got Out({:?})", other),
    }
}

#[test]
fn let_block_end_to_end_elaborates() {
    // The desugared rule should elaborate cleanly through `elaborate`.
    let src = r#"theory T begin
            rule R: let r = ~k in [Fr(~k)] --[Use(r)]-> [Out(r)]
            lemma trivial: "All k #i. Use(k) @ i ==> Use(k) @ i"
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let t = elaborate(&p).unwrap();
    let rules: Vec<_> = t.rules().collect();
    assert_eq!(rules.len(), 1);
}
