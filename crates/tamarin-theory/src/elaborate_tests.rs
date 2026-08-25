// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_parser::parse_theory;
use tamarin_term::maude_sig::pair_maude_sig;

/// The signature every production caller of [`term_to_lnterm`] holds: the
/// elaborated theory's own `MaudeSig`.
fn theory_msig(src: &str) -> tamarin_term::maude_sig::MaudeSig {
    elaborate(&parse_theory(src, &[]).unwrap())
        .unwrap()
        .signature
        .maude_sig
}

/// The spellings are read from a parsed rule, because the resolution they
/// exercise is split between the two stages: the parser lowers the prefix
/// `[AC]` head and the bare 0-arity name (`lookupArity`/`nullaryApp`,
/// Theory/Text/Parser/Term.hs:62-72,158-163), and `term_to_lnterm` reads the
/// declaration's attributes off the signature.
#[test]
fn term_to_lnterm_reads_every_attribute_from_the_signature() {
    use tamarin_term::function_symbols::{AcSym, FunSym};

    let src = "theory T begin\n\
                   functions: add/2 [AC], sec/0 [private], dec/1 [destructor], nd/2 [NDC]\n\
                   rule R:\n\
                     [ ] --> [ Out(add(x, y)), Out(sec), Out(dec(x, y)), Out(nd(x, y)) ]\n\
                   end";
    let thy = parse_theory(src, &[]).unwrap();
    let msig = theory_msig(src);
    let concs = &thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap()
        .conclusions;
    let arg = |i: usize| concs[i].args[0].clone();

    // `ac` set: a prefix application of an `[AC]` symbol lowers to an AC
    // application carrying the declaration's flags.
    match term_to_lnterm(&arg(0), &msig).unwrap() {
        Term::App(FunSym::Ac(AcSym::AcFct(sym)), _) => {
            assert_eq!(String::from_utf8_lossy(sym.name), "add");
            assert_eq!(sym.privacy, Privacy::Public);
            assert_eq!(sym.constructability, Constructability::Constructor);
            assert_eq!(sym.ndc, NdcState::NotNdc);
        }
        other => panic!("expected an AC application, got {other:?}"),
    }

    // `private` set: a bare name declared `/0` is a 0-arity private
    // constant, not a free variable.
    match term_to_lnterm(&arg(1), &msig).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert!(args.is_empty());
            assert_eq!(sym.arity, 0);
            assert_eq!(sym.privacy, Privacy::Private);
        }
        other => panic!("expected a nullary constant, got {other:?}"),
    }

    // `destructor` set + `unary` set: the surplus arguments fold into one
    // pair, and the symbol is a destructor.
    match term_to_lnterm(&arg(2), &msig).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert_eq!(sym.arity, 1);
            assert_eq!(args.len(), 1, "arity-1 fold should pair the arguments");
            assert_eq!(sym.constructability, Constructability::Destructor);
        }
        other => panic!("expected a destructor application, got {other:?}"),
    }

    // `[NDC]`.
    match term_to_lnterm(&arg(3), &msig).unwrap() {
        Term::App(FunSym::NoEq(sym), _) => assert_eq!(sym.ndc, NdcState::IsNdc),
        other => panic!("expected an NDC application, got {other:?}"),
    }
}

/// A name declared both `[AC]` and free carries TWO symbols with their own
/// attributes (`stACFunSyms` and `stFunSyms`, Term/Maude/Signature.hs:97-98).
/// `lookupArity`'s list search reaches the free one first, so the prefix
/// spelling `f(a, b)` is the free symbol, while `acterm` builds the infix
/// spelling `(a f b)` straight from `stACFunSyms`
/// (Theory/Text/Parser/Term.hs:60-71,165-172).
#[test]
fn a_name_declared_twice_resolves_prefix_free_and_infix_ac() {
    use tamarin_term::function_symbols::{AcSym, FunSym};

    let src = "theory T begin\n\
                   functions: f/2 [AC, destructor], f/2\n\
                   rule R: [ ] --> [ Out(f(x, y)), Out((x f y)) ]\n\
                   end";
    let thy = parse_theory(src, &[]).unwrap();
    let msig = theory_msig(src);
    let concs = &thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap()
        .conclusions;

    match term_to_lnterm(&concs[0].args[0], &msig).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert_eq!(String::from_utf8_lossy(sym.name), "f");
            assert_eq!(args.len(), 2);
            assert_eq!(sym.constructability, Constructability::Constructor);
        }
        other => panic!("expected the free application, got {other:?}"),
    }
    match term_to_lnterm(&concs[1].args[0], &msig).unwrap() {
        Term::App(FunSym::Ac(AcSym::AcFct(sym)), _) => {
            assert_eq!(String::from_utf8_lossy(sym.name), "f");
            assert_eq!(sym.constructability, Constructability::Destructor);
        }
        other => panic!("expected the AC application, got {other:?}"),
    }
}

/// `em(a, b)` is the bilinear-pairing C symbol (HS `naryOpApp`'s
/// `o == emapSymString` arm, Theory/Text/Parser/Term.hs:102-103).  HS applies
/// that arm with no builtin gate; the port gates it on the builtin, because
/// the Maude operator `tamem` is declared only under `enableBP` and a term
/// carrying it without the builtin crashes the first `get variants` query.
/// Without the builtin, `em` is an ordinary free symbol.
#[test]
fn em_is_the_emap_symbol_only_under_bilinear_pairing() {
    use tamarin_term::function_symbols::{CSym, FunSym};

    let rule = "rule R: [ ] --> [ Out(em(x, y)) ]\n";
    let term = |src: &str| {
        parse_theory(src, &[])
            .unwrap()
            .items
            .iter()
            .find_map(|i| match i {
                p::TheoryItem::Rule(r) => Some(r.conclusions[0].args[0].clone()),
                _ => None,
            })
            .unwrap()
    };

    let bp_src = format!("theory T begin\nbuiltins: bilinear-pairing\n{rule}end");
    match term_to_lnterm(&term(&bp_src), &theory_msig(&bp_src)).unwrap() {
        Term::App(FunSym::C(CSym::EMap), args) => assert_eq!(args.len(), 2),
        other => panic!("expected an EMap application, got {other:?}"),
    }

    let plain_src = format!("theory T begin\n{rule}end");
    match term_to_lnterm(&term(&plain_src), &theory_msig(&plain_src)).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert_eq!(String::from_utf8_lossy(sym.name), "em");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected a free application, got {other:?}"),
    }
}

/// The arity-1 fold in `term_to_vterm` names the builtin unary symbols in a
/// written-out list, because widening it to the whole signature regresses the
/// corpus.  The fold is therefore only as good as the membership of that
/// list.  Every name on it must fold surplus comma-separated arguments into
/// one right-associative pair, mirroring the `k == 1` branch of HS
/// `naryOpApp` (Theory/Text/Parser/Term.hs:94-96).  A builtin that genuinely
/// takes several arguments must not fold.  The corpus exercises `h` alone.
/// The other names (`inv`/`pk` and the revealing-signing and
/// locations-report symbols) are reachable only from theories that the fast
/// corpus does not carry.
#[test]
fn hardcoded_unary_builtins_fold_surplus_arguments() {
    use tamarin_term::function_symbols::FunSym;

    let a = parser_var("a", 0, LSort::Msg);
    let b = parser_var("b", 0, LSort::Msg);
    let msig = pair_maude_sig();
    let a_b_pair = tamarin_term::builtin::pair(
        term_to_lnterm(&a, &msig).unwrap(),
        term_to_lnterm(&b, &msig).unwrap(),
    );
    for name in [
        "h",
        "fst",
        "snd",
        "inv",
        "pk",
        "getMessage",
        "get_rep",
        "report",
    ] {
        let t = p::Term::App(name.into(), vec![a.clone(), b.clone()]);
        match term_to_lnterm(&t, &msig).unwrap() {
            Term::App(FunSym::NoEq(sym), args) => {
                assert_eq!(String::from_utf8_lossy(sym.name), name);
                assert_eq!(sym.arity, 1, "{name}: the symbol stays arity-1");
                assert_eq!(
                    args.to_vec(),
                    vec![a_b_pair.clone()],
                    "{name}: surplus args fold"
                );
            }
            other => panic!("{name}: expected a NoEq application, got {other:?}"),
        }
    }
    // `senc` genuinely takes 2 arguments, so the fold must not change it.
    let senc = p::Term::App("senc".into(), vec![a, b]);
    match term_to_lnterm(&senc, &msig).unwrap() {
        Term::App(FunSym::NoEq(sym), args) => {
            assert_eq!(sym.arity, 2, "senc is not a unary builtin");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected a NoEq application, got {other:?}"),
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

    let x = parser_var("x", 0, LSort::Msg);
    let y = parser_var("y", 0, LSort::Msg);
    let t = p::Term::Diff(Box::new(x), Box::new(y));

    match term_to_lnterm(&t, &pair_maude_sig()).unwrap() {
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
        sort: LSort::Msg,
        idx: 0,
    });
    let k = p::Term::Var(p::VarSpec {
        typ: None,
        name: "k".into(),
        sort: LSort::Fresh,
        idx: 0,
    });
    let nb = p::Term::Var(p::VarSpec {
        typ: None,
        name: "nb".into(),
        sort: LSort::Fresh,
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
    let l = term_to_lnterm(&outer, &pair_maude_sig()).unwrap();
    assert_eq!(
        tamarin_term::pretty::pretty_lnterm(&l),
        "(~k\u{2295}~nb\u{2295}na)"
    );
}

/// The AC canonicalisation must reach NESTED nodes as well as the root —
/// through the plain term entry and through the fact wrapper.  The terms
/// come from a parse, because the `[AC]` classification is the parser's
/// (`lookupArity`'s `IsAC` case, Theory/Text/Parser/Term.hs:62-72,98-105).
#[test]
fn canonicalize_ac_flattens_a_nested_node() {
    use tamarin_parser::ast as p;
    let src = |decl: &str| {
        format!(
            "theory T begin\n\
             builtins: hashing\n\
             {decl}\n\
             rule R: [ ] --> [ Out(h(add(add(b, a), c))) ]\n\
             end"
        )
    };
    let conclusion = |decl: &str| {
        let thy = parse_theory(&src(decl), &[]).unwrap();
        thy.items
            .iter()
            .find_map(|i| match i {
                p::TheoryItem::Rule(r) => Some(r.conclusions[0].clone()),
                _ => None,
            })
            .unwrap()
    };

    // Declared `[AC]`: flattened, sorted (LVar order: same idx and sort, so
    // by name) and re-folded right-leaning, one level below an ordinary
    // `App`.
    let v = |name: &str| {
        p::Term::Var(p::VarSpec {
            typ: None,
            name: name.into(),
            sort: LSort::Msg,
            idx: 0,
        })
    };
    let op = p::BinOp::AcFct(tamarin_term::intern::intern_str("add"));
    let canon_ac = p::Term::BinOp(
        op,
        Box::new(v("a")),
        Box::new(p::Term::BinOp(op, Box::new(v("b")), Box::new(v("c")))),
    );
    let want = p::Term::App("h".into(), vec![canon_ac]);
    let ac_fact = conclusion("functions: add/2 [AC]");
    assert_eq!(canonicalize_ac_in_pterm(&ac_fact.args[0]), want);
    assert_eq!(canonicalize_ac_in_pfact(&ac_fact).args, vec![want]);

    // Declared plain: `add` is an ordinary function symbol and the term is
    // left as written.
    let plain_fact = conclusion("functions: add/2");
    assert_eq!(
        canonicalize_ac_in_pterm(&plain_fact.args[0]),
        plain_fact.args[0]
    );
}

// A theory with no declarations still carries HS's `minimalMaudeSig`
// (`emptySignaturePure`, Theory/Model/Signature.hs).  `pair`, `fst` and
// `snd` are always in scope.  That is why `<a, b>` parses, and why the pair
// intruder rules exist in every theory.
#[test]
fn elaborate_empty_theory() {
    let p = parse_theory("theory T begin end", &[]).unwrap();
    let t = elaborate(&p).unwrap();
    assert_eq!(t.name, "T");
    assert!(t.items.is_empty());
    let mut funs: Vec<String> = t
        .signature
        .maude_sig
        .st_fun_syms
        .iter()
        .map(|s| String::from_utf8_lossy(s.name).to_string())
        .collect();
    funs.sort();
    assert_eq!(funs, vec!["fst", "pair", "snd"]);
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

fn parser_var(name: &str, idx: u64, sort: LSort) -> p::Term {
    p::Term::Var(p::VarSpec {
        name: name.into(),
        idx,
        sort,
        typ: None,
    })
}

// `lnterm_to_term` inverts `term_to_lnterm` on every surface shape that the
// solver round-trips through the parser AST.  A round trip on its own still
// succeeds with two matching bugs: one that mangles a sort, and one that
// unmangles it again.
// So each case also pins the LNTerm that the forward direction produces.
#[test]
fn lnterm_to_term_inverts_term_to_lnterm() {
    use tamarin_term::function_symbols::NoEqSym;
    use tamarin_term::lterm::{LNTerm, Name, NameTag};
    use tamarin_term::term::f_app_no_eq;
    use tamarin_term::vterm::{var_term, Lit};

    let msg = |n: &str| var_term(LVar::new(n, LSort::Msg, 0));
    let noeq = |n: &str, arity: usize| {
        NoEqSym::new(
            n.as_bytes().to_vec(),
            arity,
            Privacy::Public,
            Constructability::Constructor,
        )
    };
    let con = |tag, s: &str| LNTerm::Lit(Lit::Con(Name::new(tag, s.to_string())));
    let pair2 = |a: LNTerm, b: LNTerm| tamarin_term::builtin::pair(a, b);

    let cases: Vec<(&str, p::Term, LNTerm)> = vec![
        (
            "msg var carries LSortMsg and its index",
            parser_var("x", 7, LSort::Msg),
            var_term(LVar::new("x", LSort::Msg, 7)),
        ),
        (
            "`~k.3` is LSortFresh, not Msg",
            parser_var("k", 3, LSort::Fresh),
            var_term(LVar::new("k", LSort::Fresh, 3)),
        ),
        (
            "`#i` is LSortNode",
            parser_var("i", 0, LSort::Node),
            var_term(LVar::new("i", LSort::Node, 0)),
        ),
        (
            "`'Alice'` is a Pub-tagged Name constant, not a variable",
            p::Term::PubLit("Alice".into()),
            con(NameTag::Pub, "Alice"),
        ),
        (
            "`~'n42'` is a Fresh-tagged Name constant",
            p::Term::FreshLit("n42".into()),
            con(NameTag::Fresh, "n42"),
        ),
        (
            "<a, b> is one `pair` application",
            p::Term::Pair(vec![
                parser_var("a", 0, LSort::Msg),
                parser_var("b", 0, LSort::Msg),
            ]),
            pair2(msg("a"), msg("b")),
        ),
        (
            "<a, b, c> nests RIGHT: pair(a, pair(b, c)), and unnests flat",
            p::Term::Pair(vec![
                parser_var("a", 0, LSort::Msg),
                parser_var("b", 0, LSort::Msg),
                parser_var("c", 0, LSort::Msg),
            ]),
            pair2(msg("a"), pair2(msg("b"), msg("c"))),
        ),
        (
            "f(g(x), y): the nested application survives both directions",
            p::Term::App(
                "f".into(),
                vec![
                    p::Term::App("g".into(), vec![parser_var("x", 0, LSort::Msg)]),
                    parser_var("y", 0, LSort::Msg),
                ],
            ),
            f_app_no_eq(
                noeq("f", 2),
                vec![
                    f_app_no_eq(noeq("g", 1), vec![msg("x")]),
                    var_term(LVar::new("y", LSort::Msg, 0)),
                ],
            ),
        ),
    ];
    for (label, surface, lnterm) in cases {
        assert_eq!(
            term_to_lnterm(&surface, &pair_maude_sig()).unwrap(),
            lnterm,
            "{label}: term_to_lnterm"
        );
        assert_eq!(lnterm_to_term(&lnterm), surface, "{label}: lnterm_to_term");
    }
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
        p::Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
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
            p::Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
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
            p::Term::Var(vs) if vs.name == "b" && vs.sort != LSort::Fresh => {}
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
        p::Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
        other => panic!("expected Use(~k), got Use({:?})", other),
    }
    let out_conc = &desugared.conclusions[0];
    match &out_conc.args[0] {
        p::Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
        other => panic!("expected Out(~k), got Out({:?})", other),
    }
}

// `elaborate` must run the desugaring itself (`rule_to_proto_rule_e`).  It
// must not merely leave `apply_let_block` available to other callers.  The
// action and the conclusion of the elaborated rule carry `~k`.  The local
// name `r` is gone.  Without the desugaring, `r` elaborates without any
// complaint as a free Msg-variable.
#[test]
fn let_block_end_to_end_elaborates() {
    let src = r#"theory T begin
            rule R: let r = ~k in [Fr(~k)] --[Use(r)]-> [Out(r)]
            lemma trivial: "All k #i. Use(k) @ i ==> Use(k) @ i"
        end"#;
    let p = parse_theory(src, &[]).unwrap();
    let t = elaborate(&p).unwrap();
    let rules: Vec<_> = t.rules().collect();
    assert_eq!(rules.len(), 1);
    let k = tamarin_term::vterm::var_term(LVar::new("k", LSort::Fresh, 0));
    assert_eq!(rules[0].rule.actions[0].terms.to_vec(), vec![k.clone()]);
    assert_eq!(rules[0].rule.conclusions[0].terms.to_vec(), vec![k]);
}

/// The public names of a `Cond` condition come from the formula's own `Name`
/// literals, the same constants `universeBi` collects from a rule's facts
/// (`publicNamesReport'`, Wellformedness.hs:463-483).  A declared nullary
/// symbol is an application and contributes nothing.
#[test]
fn condition_public_names_are_harvested_from_the_internal_terms() {
    use crate::sapic::{Process, ProcessCombinator, ProcessParsedAnnotation};

    let names = |decl: &str, src: &str| -> Vec<String> {
        let msig = theory_msig(&format!("theory T begin\n{decl}\nend"));
        let f = tamarin_parser::parser::parse_formula_str(src, &msig).unwrap();
        let proc = Process::Comb(
            ProcessCombinator::Cond(crate::formula::sapic_from_parser(&f, &msig).unwrap()),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        let mut out = Vec::new();
        collect_process_pub_names(&proc, &mut out);
        out
    };

    assert_eq!(
        names("", "Eq(h('Foo'), 'bar')"),
        vec!["Foo".to_string(), "bar".to_string()]
    );
    // A fresh literal is not public-sorted, and a declared 0-arity name is an
    // application — neither joins the capitalization check.
    assert_eq!(
        names("functions: nil/0", "Eq(nil, ~k)"),
        Vec::<String>::new()
    );
}

/// HS's `universeBi ru` (Wellformedness.hs:463-483#publicNamesReport') is a
/// whole-value traversal of the generated rule, so it reaches the embedded
/// MSR's restriction formulas as well as its fact rows — the end-to-end pin
/// is `scripts/divergence_fixtures/sapic_pubname_in_restrict`.
#[test]
fn process_pub_names_reach_an_msr_embedded_restriction() {
    use crate::sapic::{Process, ProcessParsedAnnotation, SapicAction};

    let msig = theory_msig("theory T begin\nend");
    let f = tamarin_parser::parser::parse_formula_str("Eq(h('Foo'), 'bar')", &msig).unwrap();
    let out_fact = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Out", 1),
        vec![VTerm::Lit(Lit::Con(tamarin_term::lterm::Name::new(
            tamarin_term::lterm::NameTag::Pub,
            "baz",
        )))],
    );
    let proc = Process::Action(
        SapicAction::Msr {
            prems: Vec::new(),
            acts: Vec::new(),
            concs: vec![out_fact],
            rest: vec![crate::formula::sapic_from_parser(&f, &msig).unwrap()],
            match_vars: std::collections::BTreeSet::new(),
        },
        ProcessParsedAnnotation::empty(),
        Box::new(Process::Null(ProcessParsedAnnotation::empty())),
    );
    let mut got = Vec::new();
    collect_process_pub_names(&proc, &mut got);
    assert_eq!(
        got,
        vec!["baz".to_string(), "Foo".to_string(), "bar".to_string()]
    );
}

/// A case test's formula is a `SyntacticLNFormula` (Items/CaseTestItem.hs:27)
/// added verbatim by `liftedAddCaseTest` (Theory/Text/Parser.hs:159-163), so
/// a predicate atom reaches the elaborated item unexpanded;
/// `caseTestToPredicate` strips the sugar at accountability-translation time
/// (Items/CaseTestItem.hs:33-37).
#[test]
fn a_case_test_keeps_its_predicate_sugar() {
    use crate::atom::{ProtoAtom, SyntacticSugar};
    use crate::formula::ProtoFormula;

    let src = "theory T begin\n\
               predicates: Blamed(a) <=> Ex #i. Blame(a) @ #i\n\
               rule R: [ In(x) ] --[ Blame(x) ]-> [ Out(x) ]\n\
               test blamed: \"Blamed(a)\"\n\
               end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let ct = thy
        .items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Translation(TranslationElement::CaseTest(ct)) => Some(ct),
            _ => None,
        })
        .expect("case test");
    match &ct.formula {
        ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(fa))) => {
            assert_eq!(crate::fact::fact_tag_name(&fa.tag), "Blamed");
        }
        other => panic!("expected an unexpanded predicate atom, got {other:?}"),
    }
}

/// An accountability lemma's formula is a `SyntacticLNFormula`
/// (Items/AccLemmaItem.hs:32) built by the formula parser, so elaboration
/// closes each binder into a De Bruijn index carrying the binder's name and
/// sort and lowers the terms to the internal representation.
#[test]
fn an_acc_lemma_stores_the_internal_formula() {
    use crate::atom::ProtoAtom;
    use crate::formula::{Connective, ProtoFormula, Quantifier};
    use tamarin_term::lterm::BVar;

    let src = "theory T begin\n\
               rule R: [ In(x) ] --[ Blame(x), Fin() ]-> [ Out(x) ]\n\
               test blamed: \"Ex #i. Blame('a') @ #i\"\n\
               lemma acc: blamed accounts for \"All #i. Fin() @ #i ==> Ex #j. Blame('a') @ #j\"\n\
               end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let al = thy
        .items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Translation(TranslationElement::AccLemma(al)) => Some(al),
            _ => None,
        })
        .expect("acc lemma");
    let body = match &al.formula {
        ProtoFormula::Qua(Quantifier::All, hint, body) => {
            assert_eq!(hint, &("i".to_string(), LSort::Node));
            body
        }
        other => panic!("expected a universal quantifier, got {other:?}"),
    };
    let (lhs, rhs) = match &**body {
        ProtoFormula::Conn(Connective::Imp, l, r) => (l, r),
        other => panic!("expected an implication, got {other:?}"),
    };
    match &**lhs {
        ProtoFormula::Atom(ProtoAtom::Action(t, fa)) => {
            assert_eq!(t, &VTerm::Lit(Lit::Var(BVar::Bound(0))));
            assert_eq!(crate::fact::fact_tag_name(&fa.tag), "Fin");
        }
        other => panic!("expected an action atom, got {other:?}"),
    }
    // The existential binder is the innermost one inside its own body, so
    // its timepoint is index 0 again; `'a'` is a public-name constant.
    match &**rhs {
        ProtoFormula::Qua(Quantifier::Ex, hint, inner) => {
            assert_eq!(hint, &("j".to_string(), LSort::Node));
            match &**inner {
                ProtoFormula::Atom(ProtoAtom::Action(t, fa)) => {
                    assert_eq!(t, &VTerm::Lit(Lit::Var(BVar::Bound(0))));
                    assert_eq!(
                        fa.terms.to_vec(),
                        vec![VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "a")))]
                    );
                }
                other => panic!("expected an action atom, got {other:?}"),
            }
        }
        other => panic!("expected an existential quantifier, got {other:?}"),
    }
}

/// A lemma stores two formulas: `_lFormula`, the macro-expanded one the solver
/// and the guarded block read, and `_lOriginalFormula`, the pre-macro one HS's
/// `applyMacroInLemma` records (lib/theory/src/Lemma.hs:83-88, applied to every
/// lemma by `closeTheoryItem`, CloseRule.hs:85).  `liftedAddLemma`
/// predicate-expands the lemma before it is stored
/// (Theory/Text/Parser.hs:141-152), so the predicate atom is inlined in both
/// while the macro call survives only in the original.  A lemma that calls no
/// macro stores the same formula twice.
#[test]
fn lemma_stores_the_pre_macro_formula_as_its_original() {
    let src = "theory T\n\
begin\n\
predicates:\n  IsPairOf(m, a, b) <=> m = <a, b>\n\
macros:\n  tag(x) = <'t', x>, wrap(x, y) = tag(<x, y>)\n\
rule A:\n  [ In( <x, y> ) ] --[ A( wrap(x, y) ) ]-> [ Out( tag(x) ) ]\n\
lemma PlainLemma:\n  all-traces\n  \"All m #i. A( m ) @ #i ==> not( m = 'no' )\"\n\
lemma MacroLemma:\n  exists-trace\n  \"Ex x y m #i. A( m ) @ #i & IsPairOf(m, x, y) & m = wrap(x, y)\"\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let shown = |f: &crate::formula::LNFormula| crate::pretty_formula::pretty_lnformula(f);
    let ls: Vec<(&str, String, String)> = thy
        .lemmas()
        .map(|l| {
            (
                l.name.as_str(),
                shown(l.original_formula.as_ref().expect("original formula")),
                shown(&l.formula),
            )
        })
        .collect();
    assert_eq!(
        ls,
        vec![
            (
                "PlainLemma",
                "∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))".to_string(),
                "∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))".to_string(),
            ),
            (
                "MacroLemma",
                "∃ x y m #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ∧ (m = wrap(x, y))".to_string(),
                "∃ x y m #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ∧ (m = <'t', x, y>)".to_string(),
            ),
        ]
    );
}

/// A restriction stores two formulas: `_rstrFormula`, the macro-expanded one
/// the solver and the `expanded formula:` block read, and
/// `_rstrOriginalFormula`, the pre-macro one HS's `applyMacroInRestriction`
/// records (Theory/Model/Restriction.hs:164-166).  `liftedAddRestriction`
/// predicate-expands the restriction before it is stored
/// (Theory/Text/Parser.hs:129-139), so the predicate atom is inlined in both
/// while the macro call survives only in the original.  A restriction that
/// calls no macro stores the same formula twice.
#[test]
fn restriction_stores_the_pre_macro_formula_as_its_original() {
    let src = "theory T\n\
begin\n\
predicates:\n  IsPairOf(m, a, b) <=> m = <a, b>\n\
macros:\n  tag(x) = <'t', x>, wrap(x, y) = tag(<x, y>)\n\
rule A:\n  [ In( <x, y> ) ] --[ A( wrap(x, y) ) ]-> [ Out( tag(x) ) ]\n\
restriction PlainRestriction:\n  \"All m #i. A( m ) @ #i ==> not( m = 'no' )\"\n\
restriction MacroRestriction:\n  \"All m x y #i. A( m ) @ #i & IsPairOf(m, x, y) ==> m = wrap(x, y)\"\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let shown = |f: &crate::formula::LNFormula| crate::pretty_formula::pretty_lnformula(f);
    let rs: Vec<(&str, String, String)> = thy
        .restrictions()
        .map(|r| {
            (
                r.name.as_str(),
                shown(r.original_formula.as_ref().expect("original formula")),
                shown(&r.formula),
            )
        })
        .collect();
    assert_eq!(
        rs,
        vec![
            (
                "PlainRestriction",
                "∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))".to_string(),
                "∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))".to_string(),
            ),
            (
                "MacroRestriction",
                "∀ m x y #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ⇒ (m = wrap(x, y))".to_string(),
                "∀ m x y #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ⇒ (m = <'t', x, y>)".to_string(),
            ),
        ]
    );
}

/// The stored proof of a lemma reaches the solver as internal
/// [`ProofMethod`](crate::constraint::solver::proof_method::ProofMethod)
/// values: HS's `proofMethod` (Theory/Text/Parser/Proof.hs:75-85) builds them
/// in the parser, and `proof_tree_from_parsed` builds them here, through the
/// same converters the rest of the theory goes through.
#[test]
fn stored_proof_steps_convert_to_internal_goals() {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::proof_method::ProofMethod;
    use crate::rule::{ConcIdx, PremIdx};
    use tamarin_term::function_symbols::{AcSym, FunSym};

    let src = "theory T begin\n\
                   functions: add/2 [AC], zero/0, h/1\n\
                   rule R: [ ] --[ A( ) ]-> [ ]\n\
                   lemma l:\n\
                     exists-trace\n\
                     \"\u{2203} #i. A( ) @ #i\"\n\
                     solve( !KU( zero ) @ #vk.3 )\n\
                     solve( F( (z add h(y)) ) @ #i )\n\
                     solve( (#i.2, 0) ~~> (#j, 1) )\n\
                     by sorry\n\
                   end";
    let parsed = parse_theory(src, &[]).unwrap();
    let thy = elaborate(&parsed).expect("elaborate");
    let lemma = thy.lemmas().next().expect("one lemma");
    let step0 = lemma.proof.as_ref().expect("a stored proof");

    // A nullary user function inside a stored goal is an application, not a
    // variable, and the timepoint keeps its index.
    match &step0.method {
        ProofMethod::SolveGoal(Goal::Action(i, fa)) => {
            assert_eq!(i, &LVar::new("vk", LSort::Node, 3));
            assert!(matches!(
                fa.terms[0],
                Term::App(FunSym::NoEq(ref s), _) if s.name == b"zero"
            ));
        }
        other => panic!("expected an action goal, got {other:?}"),
    }

    // The theory's `[AC]` symbols reach the goal sub-parser, so the infix
    // spelling of `add` is that AC application.
    let step1 = &step0.cases[0].1;
    match &step1.method {
        ProofMethod::SolveGoal(Goal::Action(_, fa)) => match &fa.terms[0] {
            Term::App(FunSym::Ac(AcSym::AcFct(sym)), args) => {
                assert_eq!(String::from_utf8_lossy(sym.name), "add");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected an AC application, got {other:?}"),
        },
        other => panic!("expected an action goal, got {other:?}"),
    }

    // Both endpoints of a chain goal keep their node index.
    let step2 = &step1.cases[0].1;
    assert_eq!(
        step2.method,
        ProofMethod::SolveGoal(Goal::Chain(
            (LVar::new("i", LSort::Node, 2), ConcIdx(0)),
            (LVar::new("j", LSort::Node, 0), PremIdx(1)),
        ))
    );
    assert_eq!(step2.cases[0].1.method, ProofMethod::Sorry(None));
}

/// HS `guardedFormula` (Theory/Text/Parser/Formula.hs:122-127) `fail`s the
/// parse when a disjunct of a stored goal is not guardable; here the
/// conversion fails elaboration, and the message names the lemma.
#[test]
fn a_non_guardable_stored_disjunct_fails_elaboration() {
    let src = "theory T begin\n\
                   rule R: [ ] --[ A( ) ]-> [ ]\n\
                   lemma unguarded:\n\
                     exists-trace\n\
                     \"\u{2203} #i. A( ) @ #i\"\n\
                     solve( (\u{2200} x. \u{22A5}) \u{2225} (last(#t1)) )\n\
                     by sorry\n\
                   end";
    let parsed = parse_theory(src, &[]).unwrap();
    let err = elaborate(&parsed).expect_err("a non-guardable disjunct must fail");
    assert!(
        err.message.contains("lemma `unguarded`"),
        "the message must name the lemma, got {:?}",
        err.message
    );
}

// =========================================================================
// Projection: internal values → parser AST
// =========================================================================

/// HS writes an action atom as `Action t (Fact t)` (Atom.hs:78) and the
/// parser AST as `Action(Fact, Term)`, so the two operands swap places.
#[test]
fn lnatom_to_parser_keeps_the_action_timepoint_and_fact() {
    use crate::atom::{Atom, ProtoAtom};
    use crate::fact::{Fact, FactTag, Multiplicity};
    use tamarin_term::intern::intern_str;
    use tamarin_term::lterm::LNTerm;
    use tamarin_term::vterm::var_term;

    let x: LNTerm = var_term(LVar::new("x", LSort::Msg, 0));
    let i: LNTerm = var_term(LVar::new("i", LSort::Node, 0));
    let fa = Fact::new(
        FactTag::Proto(Multiplicity::Linear, intern_str("Ev"), 1),
        vec![x],
    );
    let a: Atom<LNTerm> = ProtoAtom::Action(i, fa);
    assert_eq!(
        lnatom_to_parser(&a),
        p::Atom::Action(
            p::Fact {
                persistent: false,
                name: "Ev".to_string(),
                args: vec![parser_var("x", 0, LSort::Msg)],
                annotations: Vec::new(),
            },
            parser_var("i", 0, LSort::Node),
        )
    );
}

/// The binary atoms keep their left and right operand where they are.
#[test]
fn lnatom_to_parser_keeps_the_binary_operand_order() {
    use crate::atom::{Atom, ProtoAtom};
    use tamarin_term::lterm::LNTerm;
    use tamarin_term::vterm::var_term;

    let i: LNTerm = var_term(LVar::new("i", LSort::Node, 0));
    let j: LNTerm = var_term(LVar::new("j", LSort::Node, 0));
    let a: Atom<LNTerm> = ProtoAtom::Less(i, j);
    assert_eq!(
        lnatom_to_parser(&a),
        p::Atom::Less(
            parser_var("i", 0, LSort::Node),
            parser_var("j", 0, LSort::Node)
        )
    );
}

/// A `diffSym` application projects to `p::Term::Diff`, the shape whose
/// renderer is the chain of `<>` HS `prettyTerm` uses (Term/Term.hs:311).
/// A wide one therefore wraps inside its second operand and never at the
/// comma, which is what the oracle prints for the rules of
/// `examples/csf18-alethea/alethea_selectionphase_anonymity.spthy`.
#[test]
fn lnterm_to_parser_keeps_the_unbreakable_diff_shape() {
    use tamarin_term::lterm::LNTerm;

    let wide = |c: char| -> LNTerm { tamarin_term::lterm::pub_term(c.to_string().repeat(60)) };
    let d: LNTerm = tamarin_term::term::f_app_no_eq(
        tamarin_term::function_symbols::diff_sym(),
        vec![wide('a'), wide('b')],
    );
    let projected = lnterm_to_parser(&d);
    assert!(matches!(projected, p::Term::Diff(..)));
    let rendered = crate::pretty_formula::term_doc(&projected).render_with(110, 73);
    assert!(!rendered.contains('\n'), "{rendered}");
    assert_eq!(
        rendered,
        tamarin_term::pretty::pretty_nterm(&d).render_with(110, 73)
    );
}

/// The two `LNTerm` → parser-AST projections are not interchangeable.
///
/// `lnterm_to_parser` materialises the surface HS `prettyTerm` prints, so a
/// `List` application is `LIST(…)` (Term/Term.hs:317) and a degenerate
/// one-argument AC application — a shape `fAppAC` collapses away
/// (Term/Term/Raw.hs:121) — is its operand alone, because an infix chain
/// needs two operands.  `lnterm_to_term` materialises the surface
/// `term_to_lnterm` reads back, where neither head has a spelling of its own
/// and both fall through to a placeholder name.
#[test]
fn converters_disagree_on_list_and_degenerate_ac() {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::lterm::LNTerm;
    use tamarin_term::term::{f_app_list, unsafe_f_app};
    use tamarin_term::vterm::var_term;

    let x: LNTerm = var_term(LVar::new("x", LSort::Msg, 0));
    let px = parser_var("x", 0, LSort::Msg);

    let list = f_app_list(vec![x.clone()]);
    assert_eq!(
        lnterm_to_parser(&list),
        p::Term::App("LIST".to_string(), vec![px.clone()])
    );
    assert_eq!(
        lnterm_to_term(&list),
        p::Term::App("?".to_string(), vec![px.clone()])
    );

    let degenerate = unsafe_f_app(FunSym::Ac(AcSym::Mult), vec![x]);
    assert_eq!(lnterm_to_parser(&degenerate), px);
    assert_eq!(
        lnterm_to_term(&degenerate),
        p::Term::App("?Mult".to_string(), vec![parser_var("x", 0, LSort::Msg)])
    );
}

// =========================================================================
// The parser-AST term order `canonicalize_ac_in_pterm` sorts by
// =========================================================================

/// HS's pair is a nested arity-2 FAPP (`fAppPair`, Term/Term.hs:163), so
/// `<a, z>` and `<a, b, c>` first differ at argument 2 — `z` against
/// `pair(b, c)` — where `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74) puts
/// `<a, z>` first.  Comparing the parser's FLAT operand vectors element-wise
/// would weigh `b` against `z` and reverse the two.
#[test]
fn cmp_pterm_orders_pairs_by_their_nested_spine() {
    use std::cmp::Ordering::{Equal, Greater, Less};
    let v = |n: &str| parser_var(n, 0, LSort::Msg);
    let short = p::Term::Pair(vec![v("a"), v("z")]);
    let long = p::Term::Pair(vec![v("a"), v("b"), v("c")]);
    assert_eq!(cmp_pterm(&short, &long), Less);
    assert_eq!(cmp_pterm(&long, &short), Greater);
    // The right-nested spelling of the SAME term compares equal, so the
    // flat `Pair` and the tail it stands for are interchangeable.
    let nested = p::Term::Pair(vec![v("a"), p::Term::Pair(vec![v("b"), v("c")])]);
    assert_eq!(cmp_pterm(&long, &nested), Equal);
}

/// The source spelling `pair(a, b)` is HS's `pairSym` FAPP just like
/// `<a, b>` (`naryOpApp`, Theory/Text/Parser/Term.hs:88-105, see line
/// 104), so the two parser-AST shapes tie — and both order against a longer
/// pair through the same nested spine.
#[test]
fn cmp_pterm_ties_the_prefix_pair_spelling_with_the_bracket_spelling() {
    use std::cmp::Ordering::{Equal, Less};
    let v = |n: &str| parser_var(n, 0, LSort::Msg);
    let prefix = p::Term::App("pair".into(), vec![v("a"), v("z")]);
    let bracket = p::Term::Pair(vec![v("a"), v("z")]);
    assert_eq!(cmp_pterm(&prefix, &bracket), Equal);
    let long = p::Term::Pair(vec![v("a"), v("b"), v("c")]);
    assert_eq!(cmp_pterm(&prefix, &long), Less);
}

/// `em/2` occupies the `C` tier of HS's derived `Ord FunSym`
/// (`NoEq < AC < C < List`, FunctionSymbols.hs:150-154), so it outranks
/// every `NoEq` and every `AC` head whatever the names involved.  The
/// classification is by name alone — `naryOpApp` builds `fAppC EMap` for
/// any `em(…)` application, builtin-declared or user-declared
/// (Theory/Text/Parser/Term.hs:103) — while the `op{t1}t2` spelling goes
/// through `binaryAlgApp`, which has no `em` case and yields `fAppNoEq`
/// (Theory/Text/Parser/Term.hs:109-121).
///
/// Oracle bytes (pinned build, Git revision ef3f0468), each from a theory
/// whose source order is `em` first:
///   * `builtins: bilinear-pairing` + `functions: f/2`,
///     `Test(em('g','h') * f('g','h'))`
///     renders `Test( (f('g', 'h')*em('g', 'h')) )` — `f` FIRST, though
///     `"em" < "f"` as names.
///   * same theory with `Test(em{'g'}'h' * f('g','h'))`
///     renders `Test( (em('g', 'h')*f('g', 'h')) )` — `em` FIRST, the
///     `NoEq` name order.
///   * `builtins: bilinear-pairing, multiset`,
///     `Test(em(~a,~b) + (~a * ~b))`
///     renders `Test( ((~a*~b)++em(~a, ~b)) )` — the `AC` product first.
///   * `builtins: diffie-hellman` + `functions: em/2, f/2` (no pairing
///     builtin), `Test(em('g','h') * f('g','h'))`
///     still renders `Test( (f('g', 'h')*em('g', 'h')) )`.
#[test]
fn cmp_pterm_ranks_em_in_the_c_tier() {
    use std::cmp::Ordering::{Greater, Less};
    let gl = p::Term::PubLit("g".into());
    let hl = p::Term::PubLit("h".into());
    let gh = vec![gl.clone(), hl.clone()];
    let em = p::Term::App("em".into(), gh.clone());
    let f = p::Term::App("f".into(), gh.clone());

    // C(2) beats NoEq(0) in BOTH directions, name order notwithstanding.
    assert_eq!(
        cmp_pterm(&f, &em),
        Less,
        "NoEq `f/2` must sort before C `em/2` despite \"em\" < \"f\""
    );
    assert_eq!(
        cmp_pterm(&em, &f),
        Greater,
        "cmp_pterm must be antisymmetric"
    );
    // A NoEq name that already precedes "em" stays first — the tier, not
    // the name, decides.
    let aaa = p::Term::App("aaa".into(), gh.clone());
    assert_eq!(cmp_pterm(&aaa, &em), Less);

    // AC(1) < C(2): the multiset operand `~a*~b` precedes the pairing.
    let prod = p::Term::BinOp(p::BinOp::Mult, Box::new(gl.clone()), Box::new(hl.clone()));
    assert_eq!(
        cmp_pterm(&prod, &em),
        Less,
        "an AC head must sort before the C `em/2`"
    );

    // `em{'g'}'h'` is `fAppNoEq`, so it sorts by name and precedes `f/2`.
    let em_alg = p::Term::AlgApp("em".into(), Box::new(gl.clone()), Box::new(hl.clone()));
    assert_eq!(
        cmp_pterm(&em_alg, &f),
        Less,
        "the `op{{t1}}t2` spelling of em is a NoEq symbol, ordered by name"
    );
    assert_eq!(
        cmp_pterm(&em_alg, &em),
        Less,
        "NoEq `em/2` and C `em/2` are distinct FunSyms, NoEq first"
    );

    // Two C terms tie on the whole FunSym key (`CSym` is a single nullary
    // constructor) and fall through to the argument list.
    let em_gg = p::Term::App("em".into(), vec![gl.clone(), gl.clone()]);
    assert_eq!(
        cmp_pterm(&em_gg, &em),
        Less,
        "same-FunSym C terms compare by their arguments"
    );

    // Only the binary form is a C symbol: `viewTerm2` rejects a `C` node
    // of any other arity (Term/Term/Raw.hs:190), so a 3-ary `em` keeps the
    // NoEq key and its name order.
    let em3 = p::Term::App("em".into(), vec![gl.clone(), hl.clone(), gl.clone()]);
    assert_eq!(cmp_pterm(&em3, &f), Less);
}

/// `t` and every one of its sub-terms, outermost first.
fn pterm_subterms<'a>(t: &'a p::Term, out: &mut Vec<&'a p::Term>) {
    out.push(t);
    match t {
        p::Term::App(_, args) | p::Term::Pair(args) => {
            for a in args {
                pterm_subterms(a, out);
            }
        }
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            pterm_subterms(a, out);
            pterm_subterms(b, out);
        }
        p::Term::PatMatch(a) => pterm_subterms(a, out),
        _ => {}
    }
}

fn pfact_subterms<'a>(f: &'a p::Fact, out: &mut Vec<&'a p::Term>) {
    for a in &f.args {
        pterm_subterms(a, out);
    }
}

fn patom_subterms<'a>(a: &'a p::Atom, out: &mut Vec<&'a p::Term>) {
    match a {
        p::Atom::Eq(x, y)
        | p::Atom::Less(x, y)
        | p::Atom::LessMset(x, y)
        | p::Atom::Subterm(x, y) => {
            pterm_subterms(x, out);
            pterm_subterms(y, out);
        }
        p::Atom::Action(fa, t) => {
            pfact_subterms(fa, out);
            pterm_subterms(t, out);
        }
        p::Atom::Last(t) => pterm_subterms(t, out),
        p::Atom::Pred(fa) => pfact_subterms(fa, out),
    }
}

fn pformula_subterms<'a>(f: &'a p::Formula, out: &mut Vec<&'a p::Term>) {
    match f {
        p::Formula::False | p::Formula::True => {}
        p::Formula::Atom(a) => patom_subterms(a, out),
        p::Formula::Not(x) => pformula_subterms(x, out),
        p::Formula::And(x, y)
        | p::Formula::Or(x, y)
        | p::Formula::Implies(x, y)
        | p::Formula::Iff(x, y) => {
            pformula_subterms(x, out);
            pformula_subterms(y, out);
        }
        p::Formula::Forall(_, x) | p::Formula::Exists(_, x) => pformula_subterms(x, out),
    }
}

fn prule_subterms<'a>(r: &'a p::Rule, out: &mut Vec<&'a p::Term>) {
    for fa in r.premises.iter().chain(&r.actions).chain(&r.conclusions) {
        pfact_subterms(fa, out);
    }
    for f in &r.embedded_restrictions {
        pformula_subterms(f, out);
    }
    for v in &r.variants {
        prule_subterms(v, out);
    }
    if let Some((l, r2)) = &r.left_right {
        prule_subterms(l, out);
        prule_subterms(r2, out);
    }
}

/// Every parser-AST term one theory's lemmas, restrictions and rule bodies
/// hold, outermost first.
fn theory_pterms(thy: &p::Theory) -> Vec<&p::Term> {
    let mut out = Vec::new();
    for item in &thy.items {
        match item {
            p::TheoryItem::Lemma(l) => pformula_subterms(&l.formula, &mut out),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                pformula_subterms(&r.formula, &mut out)
            }
            p::TheoryItem::Rule(r) | p::TheoryItem::IntrRule(r) => prule_subterms(r, &mut out),
            _ => {}
        }
    }
    out
}

/// How many terms of one file the comparison samples.  The sample is
/// compared pairwise, so the per-file cost is quadratic in this number.
const CORPUS_PTERM_SAMPLE: usize = 120;

/// [`cmp_pterm`] is the parser-AST reading of the order
/// `crate::guarded::cmp_term` gives the same term lifted to `GTerm`
/// (`term_to_gterm_free` is the lift).  Both comparators exist while the
/// solver's guarded formulas are still `GTerm`-shaped, and the theory echo's
/// AC operand order rides on [`canonicalize_ac_in_pterm`] sorting by the
/// first — so the two must agree on every term the examples tree holds.
#[test]
fn cmp_pterm_agrees_with_the_guarded_comparator_over_the_corpus() {
    use crate::guarded::cmp_term;
    use crate::guarded_types::{term_to_gterm_free, GTerm};
    use crate::test_corpus::{beyond_budget, corpus_root, parse_file, rel, spthy_files};
    use rayon::prelude::*;

    let root = corpus_root();
    if !root.is_dir() {
        assert_eq!(
            std::env::var("TAM_ALLOW_NO_CORPUS").as_deref(),
            Ok("1"),
            "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
            root.display()
        );
        eprintln!("corpus: root {} missing, skipped", root.display());
        return;
    }
    let files = spthy_files(&root);
    // The parser recurses along the input; the web server parses on 64 MiB
    // tokio threads (run.rs), so the workers get the same stacks.
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool");
    let probe = |path: &std::path::Path| -> (usize, usize, Vec<String>) {
        if beyond_budget(path, &root) {
            return (0, 0, Vec::new());
        }
        let Some(thy) = parse_file(path) else {
            return (0, 0, Vec::new());
        };
        let all = theory_pterms(&thy);
        let step = all.len().div_ceil(CORPUS_PTERM_SAMPLE).max(1);
        let sample: Vec<&p::Term> = all
            .into_iter()
            .step_by(step)
            .take(CORPUS_PTERM_SAMPLE)
            .collect();
        let lifted: Vec<GTerm> = sample.iter().map(|t| term_to_gterm_free(t)).collect();
        let mut findings = Vec::new();
        let mut pairs = 0usize;
        for i in 0..sample.len() {
            for j in (i + 1)..sample.len() {
                pairs += 1;
                let here = cmp_pterm(sample[i], sample[j]);
                let there = cmp_term(&lifted[i], &lifted[j]);
                if here != there && findings.is_empty() {
                    findings.push(format!(
                        "{}: {:?} vs {:?} — cmp_pterm {here:?}, cmp_term {there:?}",
                        rel(path, &root).display(),
                        sample[i],
                        sample[j]
                    ));
                }
            }
        }
        (1, pairs, findings)
    };
    let probes: Vec<(usize, usize, Vec<String>)> =
        pool.install(|| files.par_iter().map(|p| probe(p)).collect());

    let parsed: usize = probes.iter().map(|p| p.0).sum();
    let pairs: usize = probes.iter().map(|p| p.1).sum();
    let findings: Vec<&String> = probes.iter().flat_map(|p| &p.2).collect();
    eprintln!(
        "cmp_pterm vs cmp_term: files={} parsed={parsed} pairs={pairs}",
        files.len()
    );
    // A comparison over the corpus is a net only while it covers the tree.
    // The tree has 19 parser rejects in 1037 files, the same floor the other
    // corpus nets hold.
    assert!(
        parsed * 20 >= files.len() * 19,
        "only {parsed} of {} files reached the comparison",
        files.len()
    );
    assert!(pairs > 0, "no pairs compared");
    assert!(
        findings.is_empty(),
        "{} disagreements; first: {}",
        findings.len(),
        findings[0]
    );
}
