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
// display path round-trips.  (`pretty_theory` reads a parser AST back out of
// elaborated terms.)  A round trip on its own still succeeds with two
// matching bugs: one that mangles a sort, and one that unmangles it again.
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
