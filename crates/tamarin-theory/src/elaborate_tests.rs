// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::theory::TraceQuantifier;
use tamarin_parser::parse_theory;
use tamarin_term::lterm::{sort_of_name, LSort};
use tamarin_term::maude_sig::pair_maude_sig;

/// The signature every production caller of [`term_to_lnterm`] holds: the
/// elaborated theory's own `MaudeSig`.
fn theory_msig(src: &str) -> tamarin_term::maude_sig::MaudeSig {
    elaborate(&parse_theory(src, &[]).unwrap())
        .unwrap()
        .signature
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
// term_to_lnterm surface-shape coverage
// =========================================================================

fn parser_var(name: &str, idx: u64, sort: LSort) -> p::Term {
    p::Term::Var(p::VarSpec {
        name: name.into(),
        idx,
        sort,
        typ: None,
    })
}

// The internal term `term_to_lnterm` builds for every surface shape the
// parser writes: the sort each variable spelling carries, the `NameTag` each
// literal spelling carries, and the right-nested `pair` chain a tuple becomes.
#[test]
fn term_to_lnterm_reads_every_surface_shape() {
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
    }
}

// =========================================================================
// Rule `let` inlining
// =========================================================================

// The parser inlines a rule's `let` bindings (its own tests pin the
// substitution); elaboration therefore sees the substituted body.  The
// action and the conclusion of the elaborated rule carry `~k`, and the local
// name `r` is gone.
#[test]
fn let_inlining_end_to_end_elaborates() {
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
        let mut names = Vec::new();
        collect_process_names(&proc, &mut names);
        names
            .into_iter()
            .filter(|n| sort_of_name(n) == LSort::Pub)
            .map(|n| n.id.0.to_string())
            .collect()
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
    let mut names = Vec::new();
    collect_process_names(&proc, &mut names);
    let got: Vec<String> = names
        .into_iter()
        .filter(|n| sort_of_name(n) == LSort::Pub)
        .map(|n| n.id.0.to_string())
        .collect();
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

/// HS applies the theory's macros to the internal rule at close time
/// (`closeTheoryItem`, CloseRule.hs:84, `applyMacroInRule`,
/// Theory/Model/Rule.hs:1115-1121) and keeps the parsed rule unexpanded, which
/// is what the `rule (modulo E)` block prints — the split
/// `examples/features/macros/MacroExample.spthy` shows.  The parser has
/// already inlined the rule's `let` bindings by then
/// (Theory/Text/Parser/Rule.hs:119), so a macro call written on the right of
/// a binding reaches the internal rule expanded.
#[test]
fn macro_in_a_let_bound_term_reaches_the_internal_rule() {
    use crate::pretty_hpj::FLAT_WIDTH;

    let src = "theory T\n\
begin\n\
functions: h/1\n\
macros:\n  m(x) = h(x)\n\
rule A:\n  let y = m(~k) in\n  [ Fr(~k) ] --[ A( y ) ]-> [ Out( y ) ]\n\
end\n";
    let parsed = parse_theory(src, &[]).unwrap();
    let parsed_rule = parsed
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("parsed rule");
    assert!(
        matches!(&parsed_rule.actions[0].args[0],
            p::Term::App(n, args) if n == "m" && args.len() == 1),
        "the parsed rule keeps the macro call: {:?}",
        parsed_rule.actions[0].args[0]
    );

    let thy = elaborate(&parsed).unwrap();
    let rule = thy.rules().next().expect("elaborated rule");
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    assert_eq!(shown(&rule.rule.actions[0]), "A( h(~k) )");
    assert_eq!(shown(&rule.rule.conclusions[0]), "Out( h(~k) )");
}

/// `closeProtoRule` narrows `applyMacroInRule macros ruE` into the AC half and
/// keeps `ruE` itself as `cprRuleE` (lib/theory/src/Rule.hs:82-86), the half
/// `prettyClosedProtoRule` quotes as the `rule (modulo E)` block
/// (ClosedTheory.hs:331-366).  That is the `encrypt`/`aenc` split
/// `examples/features/macros/MacroExample.spthy` prints.  A rule whose body
/// calls no macro is its own E half, so it stores none.
#[test]
fn macro_rule_keeps_its_pre_macro_e_half() {
    use crate::pretty_hpj::FLAT_WIDTH;

    let src = "theory T\n\
begin\n\
builtins: asymmetric-encryption\n\
macros:\n  encrypt(x, y) = aenc(x, y)\n\
rule Client:\n  [ Fr(~k), !Pk($S, pkS) ] --> [ Out( encrypt(~k, pkS) ) ]\n\
rule Plain:\n  [ Fr(~k) ] --> [ Out( ~k ) ]\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    let rules: Vec<_> = thy.rules().collect();

    assert!(rules[0].rule_e.is_some());
    assert_eq!(
        shown(&rules[0].rule_e().conclusions[0]),
        "Out( encrypt(~k, pkS) )"
    );
    assert_eq!(shown(&rules[0].rule.conclusions[0]), "Out( aenc(~k, pkS) )");

    assert!(rules[1].rule_e.is_none());
    assert_eq!(shown(&rules[1].rule_e().conclusions[0]), "Out( ~k )");
}

/// HS `nullaryApp` (Theory/Text/Parser/Term.hs:151,158-163) parses a bare
/// arity-0 macro name as a 0-ary application, so `konst` and `konst()` are
/// the same call and reach the internal rule expanded.  `nullaryApp` claims
/// the bare name outright, which makes `konst.1` and `konst:pub` a parse
/// error upstream; the port reads them as variables, and no macro matches a
/// variable.
#[test]
fn a_bare_nullary_macro_name_reaches_the_internal_rule_expanded() {
    use crate::pretty_hpj::FLAT_WIDTH;

    let src = "theory T\n\
begin\n\
builtins: hashing\n\
macros:\n  konst() = h('seed')\n\
rule R:\n  [ In( konst ) ] --[ M( konst.1, konst:pub ) ]-> [ ]\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let rule = thy.rules().next().expect("elaborated rule");
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    assert_eq!(shown(&rule.rule.premises[0]), "In( h('seed') )");
    assert_eq!(shown(&rule.rule.actions[0]), "M( konst.1, $konst )");
    assert_eq!(shown(&rule.rule_e().premises[0]), "In( konst )");
}

/// The parser splices a live `#ifdef` branch into the top-level item stream,
/// as HS's `ifdef` adds the branch's items to the theory it is parsing
/// (Theory/Text/Parser.hs:350-361), so the macro call-sites of a rule written
/// inside one are expanded like any other rule's.
#[test]
fn a_macro_call_inside_a_live_ifdef_branch_is_expanded() {
    use crate::pretty_hpj::FLAT_WIDTH;

    let src = "theory T\n\
begin\n\
functions: id/1\n\
macros:\n  idm(x) = id(x)\n\
#ifdef FLAG\n\
rule R:\n  [ In( idm(a) ) ] --> [ Out( a ) ]\n\
#endif\n\
end\n";
    let thy = elaborate(&parse_theory(src, &["FLAG"]).unwrap()).unwrap();
    let rule = thy.rules().next().expect("rule from the live ifdef branch");
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    assert_eq!(shown(&rule.rule.premises[0]), "In( id(a) )");
    assert_eq!(shown(&rule.rule_e().premises[0]), "In( idm(a) )");
}

/// A `variants` block is parsed into `_oprRuleAC` (`protoRule`,
/// Theory/Text/Parser/Rule.hs:126-135, see line 134) and reaches the close
/// untouched: `closeProtoRule`'s third equation maps `ClosedProtoRule ruE`
/// over the list instead of computing variants or applying the macros
/// (lib/theory/src/Rule.hs:82-86, see line 86).
#[test]
fn manual_variants_reach_the_internal_rule() {
    use crate::pretty_hpj::FLAT_WIDTH;

    let src = "theory T\n\
begin\n\
functions: f/1\n\
macros:\n  m(x) = f(x)\n\
rule R:\n  [ In( x ) ] --[ A( m(x) ) ]-> [ Out( m(x) ) ]\n\
  variants\n\
    rule (modulo AC) R:\n      [ In( y ) ] --[ A( m(y) ) ]-> [ Out( f(y) ) ],\n\
    rule (modulo AC) R:\n      [ In( z ) ] --[ A( f(z) ) ]-> [ Out( f(z) ) ]\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    let rule = thy.rules().next().expect("elaborated rule");

    assert_eq!(rule.rule_ac.len(), 2);
    assert_eq!(rule.rule_ac[0].info.name, ProtoRuleName::Stand("R"));
    assert_eq!(shown(&rule.rule_ac[0].actions[0]), "A( m(y) )");
    assert_eq!(shown(&rule.rule_ac[0].conclusions[0]), "Out( f(y) )");
    assert_eq!(shown(&rule.rule_ac[1].actions[0]), "A( f(z) )");
}

/// A case test and an accountability lemma are `TranslationItem`s, which
/// `closeTheoryItem` passes through with no macro application
/// (CloseRule.hs:82-90, see line 90) and `liftedAddCaseTest` /
/// `liftedAddAccLemma` add verbatim (Theory/Text/Parser.hs:153-163, see lines
/// 157 and 163).  Their formulas keep the macro call the source wrote.
#[test]
fn a_case_test_and_an_acc_lemma_keep_their_macro_calls() {
    use crate::pretty_hpj::FLAT_WIDTH;
    use crate::theory::TranslationElement;

    let src = "theory T\n\
begin\n\
functions: id/1\n\
macros:\n  idm(x) = id(x)\n\
rule R:\n  [ In( x ) ] --[ Blame( x ), Fin( ) ]-> [ Out( x ) ]\n\
test blamed:\n  \"Ex #i. Blame(idm('a')) @ #i\"\n\
lemma acc:\n  blamed accounts for \"All #i. Fin() @ #i ==> Ex #j. Blame(idm('a')) @ #j\"\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let shown = |f: &crate::formula::SyntacticLNFormula| {
        crate::pretty_formula::syntactic_lnformula_doc(f).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    let mut seen: Vec<String> = Vec::new();
    for item in &thy.items {
        match item {
            TheoryItem::Translation(TranslationElement::CaseTest(c)) => {
                seen.push(shown(&c.formula))
            }
            TheoryItem::Translation(TranslationElement::AccLemma(a)) => {
                seen.push(shown(&a.formula))
            }
            _ => {}
        }
    }
    assert_eq!(
        seen,
        vec![
            "∃ #i. Blame( idm('a') ) @ #i".to_string(),
            "∀ #i. (Fin( ) @ #i) ⇒ (∃ #j. Blame( idm('a') ) @ #j)".to_string(),
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

/// HS folds `addFunctionTypingInfo` over every declaration of a `functions:`
/// block (Theory/Text/Parser.hs:259-262), so a block of three declarations
/// leaves three `FunctionTypingInfo` items in source order, each carrying the
/// `UserDefinedSym` the declaration's attributes select and the declared SAPIC
/// types (HS `function`, Theory/Text/Parser/Signature.hs:183-225).
#[test]
fn each_function_declaration_becomes_a_typing_info() {
    use tamarin_term::function_symbols::{Constructability, NdcState, Privacy, UserDefinedSym};

    let src = "theory T begin\n\
               functions: h/2, unpack(cipher, key):plain [private, destructor],\n\
                          mix/2 [AC, NDC]\n\
               end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let infos: Vec<&crate::theory::SapicFunSym> = thy.function_typing_infos().collect();
    assert_eq!(
        infos
            .iter()
            .map(|f| String::from_utf8_lossy(f.sym.name()).into_owned())
            .collect::<Vec<_>>(),
        vec!["h", "unpack", "mix"]
    );

    let unpack = match infos[1].sym {
        UserDefinedSym::NoEqUser(s) => s,
        other => panic!("expected a free symbol, got {other:?}"),
    };
    assert_eq!(unpack.arity, 2);
    assert_eq!(unpack.privacy, Privacy::Private);
    assert_eq!(unpack.constructability, Constructability::Destructor);
    assert_eq!(unpack.ndc, NdcState::NotNdc);
    assert_eq!(
        infos[1].arg_types,
        vec![Some("cipher".to_string()), Some("key".to_string())]
    );
    assert_eq!(infos[1].out_type, Some("plain".to_string()));

    // `/2` is the untyped form: every argument and the result take
    // `defaultSapicType` (HS `functionType`,
    // Theory/Text/Parser/Signature.hs:152-156), and `[AC]` selects the
    // arity-free `ACfctUser` symbol.
    let mix = match infos[2].sym {
        UserDefinedSym::AcFctUser(s) => s,
        other => panic!("expected a user-defined AC symbol, got {other:?}"),
    };
    assert_eq!(mix.privacy, Privacy::Public);
    assert_eq!(mix.constructability, Constructability::Constructor);
    assert_eq!(mix.ndc, NdcState::IsNdc);
    assert_eq!(infos[2].arg_types, vec![None, None]);
    assert_eq!(infos[2].out_type, None);
}

/// HS's parser stores each process-bearing declaration as its own theory item
/// as it reads it (`addProcess`, Theory/Text/Parser.hs:290-291; the
/// `ProcessDef` / `EquivLemma` neighbours at :292-296), so the elaborated item
/// list holds them interleaved with the rules in source order.  A `P(args)`
/// call arrives inlined behind its `ProcessCall` marker action, which is what
/// `checkProcess` + `applyM` build (Theory/Text/Parser/Sapic.hs:295-312).
#[test]
fn process_items_keep_their_source_position() {
    use crate::sapic::{Process, SapicAction};

    let src = "theory T begin\n\
               rule R: [ ] --> [ ]\n\
               let P(x) = out(x)\n\
               process: P('a')\n\
               equivLemma: out('b') out('c')\n\
               end\n";
    let thy = elaborate(&parse_theory(src, &["diff"]).unwrap()).unwrap();
    let kinds: Vec<&str> = thy
        .items
        .iter()
        .map(|i| match i {
            TheoryItem::Rule(_) => "rule",
            TheoryItem::Translation(TranslationElement::ProcessDef(_)) => "processdef",
            TheoryItem::Translation(TranslationElement::Process(_)) => "process",
            TheoryItem::Translation(TranslationElement::EquivLemma(_, _)) => "equivlemma",
            other => panic!("unexpected item {other:?}"),
        })
        .collect();
    assert_eq!(kinds, ["rule", "processdef", "process", "equivlemma"]);

    // `_pVars` carries the declared formals as `SapicLVar`s, whose `show` is
    // the parameter list the open print writes back.
    let def = thy.process_defs().next().unwrap();
    assert_eq!(def.name, "P");
    assert_eq!(
        def.vars
            .as_ref()
            .unwrap()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["x"]
    );

    // `out('a')` behind the marker, with the definition's name recorded on
    // the substituted body (`processAddAnnotation`,
    // Theory/Text/Parser/Sapic.hs:308-311).
    let top = thy.processes().next().unwrap();
    let Process::Action(SapicAction::ProcessCall(name, args), _, body) = top else {
        panic!("expected a ProcessCall marker, got {top:?}");
    };
    assert_eq!(name, "P");
    assert_eq!(args.len(), 1);
    assert_eq!(body.annotation().process_names, ["P".to_string()]);
    let Process::Action(SapicAction::ChOut { chan: None, msg }, _, _) = body.as_ref() else {
        panic!("expected the substituted `out(x)` body, got {body:?}");
    };
    assert_eq!(*msg, args[0]);
}

#[test]
fn process_calls_only_see_preceding_definitions() {
    let prior = "theory T begin\n\
                 let P = out('ok')\n\
                 process: P\n\
                 end\n";
    elaborate(&parse_theory(prior, &[]).unwrap()).expect("a prior definition is visible");

    let forward = "theory T begin\n\
                   process: P\n\
                   let P = out('too-late')\n\
                   end\n";
    let err = elaborate(&parse_theory(forward, &[]).unwrap()).unwrap_err();
    assert!(err.message.contains("process not defined: P"), "{err}");
}

#[test]
fn recursive_process_definitions_fail_cleanly() {
    let self_recursive = "theory T begin\n\
                          let P = P\n\
                          end\n";
    let err = elaborate(&parse_theory(self_recursive, &[]).unwrap()).unwrap_err();
    assert!(err.message.contains("process not defined: P"), "{err}");

    let mutually_recursive = "theory T begin\n\
                              let P = Q\n\
                              let Q = P\n\
                              end\n";
    let err = elaborate(&parse_theory(mutually_recursive, &[]).unwrap()).unwrap_err();
    assert!(err.message.contains("process not defined: Q"), "{err}");
}

#[test]
fn duplicate_process_definitions_are_rejected() {
    let src = "theory T begin\n\
               let P = 0\n\
               let P = 0\n\
               end\n";
    let err = elaborate(&parse_theory(src, &[]).unwrap()).unwrap_err();
    assert!(
        err.message.contains("duplicate process definition: P"),
        "{err}"
    );
}

#[test]
fn duplicate_heuristic_headers_are_rejected() {
    let src = "theory T begin\n\
               heuristic: s\n\
               heuristic: c\n\
               end\n";
    let err = elaborate(&parse_theory(src, &[]).unwrap()).unwrap_err();
    assert_eq!(err.message, "default heuristic already defined");
}

/// One process-bearing item as the comparison below reads it.
#[derive(Debug, PartialEq)]
enum ProcessProbe {
    Process(crate::sapic::PlainProcess),
    Def(
        String,
        Option<Vec<crate::sapic::SapicLVar>>,
        crate::sapic::PlainProcess,
    ),
    Equiv(crate::sapic::PlainProcess, crate::sapic::PlainProcess),
    DiffEquiv(crate::sapic::PlainProcess),
}

/// The process-bearing parsed items converted in source order against the
/// FINISHED signature. This independently mirrors the elaborator's definition
/// visibility while keeping the corpus test's signature comparison.
fn parsed_process_probes(
    thy: &p::Theory,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Result<Vec<ProcessProbe>, String> {
    let mut defs = crate::process_inline::ProcessDefMap::new();
    let mut out = Vec::new();
    for item in &thy.items {
        match item {
            p::TheoryItem::TopLevelProcess(pr) => {
                let p = crate::process_inline::convert_process_with_defs(pr, &defs, sig)
                    .map_err(|e| e.message)?;
                out.push(ProcessProbe::Process(p));
            }
            p::TheoryItem::ProcessDef(d) => {
                if defs.contains_key(&d.name) {
                    return Err(format!("duplicate process definition: {}", d.name));
                }
                let vars = d
                    .vars
                    .as_ref()
                    .map(|vs| vs.iter().map(varspec_to_sapic).collect());
                let body = crate::process_inline::convert_process_with_defs(&d.body, &defs, sig)
                    .map_err(|e| e.message)?;
                let def = crate::theory::ProcessDef {
                    name: d.name.clone(),
                    vars: vars.clone(),
                    body: body.clone(),
                };
                defs.insert(d.name.clone(), def);
                out.push(ProcessProbe::Def(d.name.clone(), vars, body));
            }
            p::TheoryItem::EquivLemma(p1, p2) => {
                let p1 = crate::process_inline::convert_process_with_defs(p1, &defs, sig)
                    .map_err(|e| e.message)?;
                let p2 = crate::process_inline::convert_process_with_defs(p2, &defs, sig)
                    .map_err(|e| e.message)?;
                out.push(ProcessProbe::Equiv(p1, p2))
            }
            p::TheoryItem::DiffEquivLemma(pr) => {
                let p = crate::process_inline::convert_process_with_defs(pr, &defs, sig)
                    .map_err(|e| e.message)?;
                out.push(ProcessProbe::DiffEquiv(p));
            }
            _ => {}
        }
    }
    Ok(out)
}

/// The same items off the elaborated theory, in item order.
fn internal_process_probes(thy: &Theory) -> Vec<ProcessProbe> {
    thy.items
        .iter()
        .filter_map(|i| match i {
            TheoryItem::Translation(TranslationElement::Process(pr)) => {
                Some(ProcessProbe::Process(pr.clone()))
            }
            TheoryItem::Translation(TranslationElement::ProcessDef(d)) => Some(ProcessProbe::Def(
                d.name.clone(),
                d.vars.clone(),
                d.body.clone(),
            )),
            TheoryItem::Translation(TranslationElement::EquivLemma(p1, p2)) => {
                Some(ProcessProbe::Equiv(p1.clone(), p2.clone()))
            }
            TheoryItem::Translation(TranslationElement::DiffEquivLemma(pr)) => {
                Some(ProcessProbe::DiffEquiv(pr.clone()))
            }
            _ => None,
        })
        .collect()
}

/// `elaborate` converts each process against the signature the declarations
/// BEFORE it have built, the way it converts each rule; every other caller
/// converts against the finished signature.  Over the examples tree the two
/// readings agree item for item, so the internal items carry exactly the
/// processes the open print renders.
///
/// The floor keeps it a net: a regression that stops producing the items, or
/// that makes elaboration reject process theories, fails here instead of
/// passing on fewer files.
#[test]
fn corpus_process_items_match_the_converted_parsed_items() {
    use crate::test_corpus::{
        beyond_budget, corpus_root, elaborate_file, parse_file, rel, spthy_files,
    };
    use rayon::prelude::*;

    let root = corpus_root();
    if !root.is_dir() {
        if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
            eprintln!("corpus: root {} missing, skipped", root.display());
            return;
        }
        panic!(
            "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
            root.display()
        );
    }
    let files = spthy_files(&root);
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool");
    let per_file: Vec<(usize, Vec<String>)> = pool.install(|| {
        files
            .par_iter()
            .map(|path| {
                let mut findings = Vec::new();
                if beyond_budget(path, &root) {
                    return (0, findings);
                }
                let Some(thy) = parse_file(path) else {
                    return (0, findings);
                };
                let at = rel(path, &root).display().to_string();
                let carries_process = thy.items.iter().any(|i| {
                    matches!(
                        i,
                        p::TheoryItem::TopLevelProcess(_)
                            | p::TheoryItem::ProcessDef(_)
                            | p::TheoryItem::EquivLemma(_, _)
                            | p::TheoryItem::DiffEquivLemma(_)
                    )
                });
                let elab = match elaborate_file(path) {
                    Ok(e) => e,
                    Err(e) if carries_process => {
                        findings.push(format!("{at}: elaboration rejects it: {e}"));
                        return (0, findings);
                    }
                    Err(_) => return (0, findings),
                };
                let internal = internal_process_probes(&elab);
                match parsed_process_probes(&thy, &elab.signature) {
                    Ok(parsed) if parsed == internal => (parsed.len(), findings),
                    Ok(parsed) => {
                        for (i, (a, b)) in parsed.iter().zip(&internal).enumerate() {
                            if a != b {
                                findings.push(format!("{at}: item {i} differs"));
                            }
                        }
                        if parsed.len() != internal.len() {
                            findings.push(format!(
                                "{at}: {} parsed items against {} internal",
                                parsed.len(),
                                internal.len()
                            ));
                        }
                        (0, findings)
                    }
                    Err(e) => {
                        findings.push(format!("{at}: the finished signature rejects it: {e}"));
                        (0, findings)
                    }
                }
            })
            .collect()
    });

    let compared: usize = per_file.iter().map(|(n, _)| n).sum();
    let with_items = per_file.iter().filter(|(n, _)| *n > 0).count();
    let findings: Vec<&String> = per_file.iter().flat_map(|(_, f)| f).collect();
    eprintln!(
        "process items: files={} with_process_items={with_items} items={compared} findings={}",
        files.len(),
        findings.len()
    );
    // The tree holds 1037 files, of which 122 carry 316 process-bearing
    // items.
    assert!(
        with_items >= 120,
        "only {with_items} files contributed a process item"
    );
    assert!(compared >= 310, "only {compared} process items compared");
    assert!(
        findings.is_empty(),
        "{} disagreements; first: {:#?}",
        findings.len(),
        findings.iter().take(5).collect::<Vec<_>>()
    );
}
