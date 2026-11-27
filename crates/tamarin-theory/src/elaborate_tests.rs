// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
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
/// Theory/Text/Parser/Term.hs), and `term_to_lnterm` reads the
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

// `dest-pairing` is exempt from the builtins-arm FUNCTION check
// (Theory/Text/Parser/Signature.hs) — oracle probes tb / tc — and a destructor
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
// (Theory/Text/Parser/Signature.hs)
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

/// The internal term `term_to_lnterm` builds for every surface shape the
/// parser writes, under the signature `decls` declares: the sort each
/// variable spelling carries, the `NameTag` each literal spelling carries,
/// the right-nested `pair` chain a tuple becomes, and the applications
/// whose symbol depends on the signature.
#[test]
fn term_to_lnterm_reads_every_surface_shape() {
    use tamarin_term::function_symbols::{diff_sym, AcState, NoEqSym};
    use tamarin_term::lterm::{LNTerm, Name, NameTag};
    use tamarin_term::maude_print::fun_sym_encode_attr;
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
    let pv = |n: &str| parser_var(n, 0, LSort::Msg);
    let app = |f: &str, args: Vec<p::Term>| p::Term::App(f.into(), args);
    // HS `naryOpApp` (Theory/Text/Parser/Term.hs) folds surplus arguments
    // into one right-associative pair exactly when `lookupArity` gives the
    // symbol arity 1, as these builtins have.
    const ARITY1: &str = "builtins: hashing, asymmetric-encryption, revealing-signing, \
                          diffie-hellman, locations-report";

    enum Want {
        Term(LNTerm),
        /// The same internal term as this other surface term.
        Same(p::Term),
    }
    let mut cases: Vec<(&str, &str, p::Term, Want)> = vec![
        (
            "msg var carries LSortMsg and its index",
            "",
            parser_var("x", 7, LSort::Msg),
            Want::Term(var_term(LVar::new("x", LSort::Msg, 7))),
        ),
        (
            "`~k.3` is LSortFresh, not Msg",
            "",
            parser_var("k", 3, LSort::Fresh),
            Want::Term(var_term(LVar::new("k", LSort::Fresh, 3))),
        ),
        (
            "`#i` is LSortNode",
            "",
            parser_var("i", 0, LSort::Node),
            Want::Term(var_term(LVar::new("i", LSort::Node, 0))),
        ),
        (
            "`'Alice'` is a Pub-tagged Name constant, not a variable",
            "",
            p::Term::PubLit("Alice".into()),
            Want::Term(con(NameTag::Pub, "Alice")),
        ),
        (
            "`~'n42'` is a Fresh-tagged Name constant",
            "",
            p::Term::FreshLit("n42".into()),
            Want::Term(con(NameTag::Fresh, "n42")),
        ),
        (
            "<a, b> is one `pair` application",
            "",
            p::Term::Pair(vec![
                parser_var("a", 0, LSort::Msg),
                parser_var("b", 0, LSort::Msg),
            ]),
            Want::Term(pair2(msg("a"), msg("b"))),
        ),
        (
            "<a, b, c> nests RIGHT: pair(a, pair(b, c)), and unnests flat",
            "",
            p::Term::Pair(vec![
                parser_var("a", 0, LSort::Msg),
                parser_var("b", 0, LSort::Msg),
                parser_var("c", 0, LSort::Msg),
            ]),
            Want::Term(pair2(msg("a"), pair2(msg("b"), msg("c")))),
        ),
        (
            "f(g(x), y): the nested application survives both directions",
            "",
            p::Term::App(
                "f".into(),
                vec![
                    p::Term::App("g".into(), vec![parser_var("x", 0, LSort::Msg)]),
                    parser_var("y", 0, LSort::Msg),
                ],
            ),
            Want::Term(f_app_no_eq(
                noeq("f", 2),
                vec![
                    f_app_no_eq(noeq("g", 1), vec![msg("x")]),
                    var_term(LVar::new("y", LSort::Msg, 0)),
                ],
            )),
        ),
        (
            "`em` is the bilinear-pairing C symbol (`naryOpApp`)",
            "builtins: bilinear-pairing",
            app("em", vec![pv("x"), pv("y")]),
            Want::Term(tamarin_term::builtin::emap(msg("x"), msg("y"))),
        ),
        (
            "without the builtin a declared `em` is a free symbol",
            "functions: em/2",
            app("em", vec![pv("x"), pv("y")]),
            Want::Term(f_app_no_eq(noeq("em", 2), vec![msg("x"), msg("y")])),
        ),
        (
            "a declared `h/2` takes its arguments as written",
            "functions: h/2",
            app("h", vec![pv("a"), pv("b")]),
            Want::Term(f_app_no_eq(noeq("h", 2), vec![msg("a"), msg("b")])),
        ),
        (
            "`senc` is not a unary builtin, so nothing folds",
            ARITY1,
            app("senc", vec![pv("a"), pv("b")]),
            Want::Term(f_app_no_eq(noeq("senc", 2), vec![msg("a"), msg("b")])),
        ),
        // HS `diffSym` is PRIVATE (Term/Term/FunctionSymbols.hs), and the
        // `s == diffSym` guards compare the whole tuple.
        (
            "`diff(x, y)` lowers to the private diff symbol",
            "",
            p::Term::Diff(Box::new(pv("x")), Box::new(pv("y"))),
            Want::Term(f_app_no_eq(diff_sym(), vec![msg("x"), msg("y")])),
        ),
    ];
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
        cases.push((
            "an arity-1 builtin folds surplus arguments into a pair",
            ARITY1,
            app(name, vec![pv("a"), pv("b")]),
            Want::Same(app(name, vec![p::Term::Pair(vec![pv("a"), pv("b")])])),
        ));
    }
    for (label, decls, surface, want) in cases {
        let msig = if decls.is_empty() {
            pair_maude_sig()
        } else {
            theory_msig(&format!("theory T begin\n{decls}\nend"))
        };
        let want = match want {
            Want::Term(t) => t,
            Want::Same(other) => term_to_lnterm(&other, &msig).unwrap(),
        };
        assert_eq!(
            term_to_lnterm(&surface, &msig).unwrap(),
            want,
            "{label}: {surface:?}"
        );
    }
    // The diff symbol's Maude operator is `tamPCFUdiff`.
    let diff = diff_sym();
    assert_eq!(
        fun_sym_encode_attr(
            diff.privacy,
            diff.constructability,
            AcState::NotAc,
            diff.ndc
        ),
        "PCFU"
    );
}

/// The public names of a `Cond` condition come from the formula's own `Name`
/// literals, the same constants `universeBi` collects from a rule's facts
/// (`publicNamesReport'`, Wellformedness.hs).  A declared nullary
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

/// HS applies the theory's macros to the internal rule at close time
/// (`closeTheoryItem`, CloseRule.hs, `applyMacroInRule`,
/// Theory/Model/Rule.hs) and keeps the parsed rule unexpanded, which
/// is what the `rule (modulo E)` block prints — the split
/// `examples/features/macros/MacroExample.spthy` shows.  The rule's `let`
/// bindings are applied before that (Theory/Text/Parser/Rule.hs), so a
/// macro call written on the right of a binding reaches the internal rule
/// expanded.
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
        matches!(&parsed_rule.lets[0].1,
            p::Term::App(n, args) if n == "m" && args.len() == 1),
        "the parsed binding keeps the macro call: {:?}",
        parsed_rule.lets[0].1
    );

    let thy = elaborate(&parsed).unwrap();
    let rule = thy.rules().next().expect("elaborated rule");
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    assert_eq!(shown(&rule.rule.actions[0]), "A( h(~k) )");
    assert_eq!(shown(&rule.rule.conclusions[0]), "Out( h(~k) )");
}

/// HS `nullaryApp` (Theory/Text/Parser/Term.hs) parses a bare
/// arity-0 macro name as a 0-ary application, so `konst` and `konst()` are
/// the same call and reach the internal rule expanded. `nullaryApp` claims
/// the bare identifier before an index or sort suffix can be read, making
/// `konst.1` and `konst:pub` parse errors.
#[test]
fn a_bare_nullary_macro_name_reaches_the_internal_rule_expanded() {
    use crate::pretty_hpj::FLAT_WIDTH;

    let src = "theory T\n\
begin\n\
builtins: hashing\n\
macros:\n  konst() = h('seed')\n\
rule R:\n  [ In( konst ) ] --[ M( konst() ) ]-> [ ]\n\
end\n";
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    let rule = thy.rules().next().expect("elaborated rule");
    let shown = |fa: &crate::fact::LNFact| {
        crate::fact::pretty_lnfact(fa).render_with(FLAT_WIDTH, FLAT_WIDTH)
    };
    assert_eq!(shown(&rule.rule.premises[0]), "In( h('seed') )");
    assert_eq!(shown(&rule.rule.actions[0]), "M( h('seed') )");
    assert_eq!(shown(&rule.rule_e().premises[0]), "In( konst )");
    assert_eq!(shown(&rule.rule_e().actions[0]), "M( konst )");
}

/// A case test and an accountability lemma are `TranslationItem`s, which
/// `closeTheoryItem` passes through with no macro application
/// (CloseRule.hs) and `liftedAddCaseTest` /
/// `liftedAddAccLemma` add verbatim (Theory/Text/Parser.hs).  Their formulas keep the macro call the source wrote.
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
/// values: HS's `proofMethod` (Theory/Text/Parser/Proof.hs) builds them
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
    let step1 = &step0.cases[""];
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
    let step2 = &step1.cases[""];
    assert_eq!(
        step2.method,
        ProofMethod::SolveGoal(Goal::Chain(
            (LVar::new("i", LSort::Node, 2), ConcIdx(0)),
            (LVar::new("j", LSort::Node, 0), PremIdx(1)),
        ))
    );
    assert_eq!(step2.cases[""].method, ProofMethod::Sorry(None));
}

/// HS `guardedFormula` (Theory/Text/Parser/Formula.hs) `fail`s the
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
    assert!(err.message.contains("duplicate process: P"), "{err}");
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
                    return Err(format!("duplicate process: {}", d.name));
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
        beyond_budget, corpus_root_or_skip, elaborate_file, parse_file, rel, spthy_files,
    };
    use rayon::prelude::*;

    let Some(root) = corpus_root_or_skip("corpus") else {
        return;
    };
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

// =========================================================================
// Rule `let` blocks and `addOpenProtoRule`'s duplicate guard
// =========================================================================

/// The elaborated `ProtoRuleE` of the theory's first rule.
fn first_rule_e(src: &str) -> ProtoRuleE {
    let thy = elaborate(&parse_theory(src, &[]).unwrap()).unwrap();
    thy.rules().next().expect("one rule").rule_e().clone()
}

/// HS applies the `let` substitution to `(ps, as, cs, rs)` (Theory/Text/
/// Parser/Rule.hs), so a `let`-written rule elaborates to its expanded form.
/// `letBlock` folds the singletons with `foldr1 compose`
/// (Theory/Text/Parser/Let.hs): a binding sees the bindings before it, a
/// reference to a later one stays free, and the locally nameless
/// `_restrict` formulas neither capture an image nor rewrite a bound name.
#[test]
fn a_let_rule_elaborates_to_its_expanded_form() {
    for (lets, body, expanded) in [
        (
            "let r = ~k",
            "[In(r), Fr(~k)] --[Use(r)]-> [Out(r)]",
            "[In(~k), Fr(~k)] --[Use(~k)]-> [Out(~k)]",
        ),
        (
            "let a = ~k b = h(a)",
            "[In(b), Fr(~k)] --[]-> []",
            "[In(h(~k)), Fr(~k)] --[]-> []",
        ),
        (
            "let a = h(b) b = ~k",
            "[In(a), Fr(~k)] --[]-> []",
            "[In(h(b)), Fr(~k)] --[]-> []",
        ),
        (
            "let 5G_AV = <'a', ~k>",
            "[Fr(~k)] --[]-> [Out(5G_AV)]",
            "[Fr(~k)] --[]-> [Out(<'a', ~k>)]",
        ),
        (
            "let m = h(~k)",
            "[Fr(~k)] --[ _restrict(m = ~k) ]-> []",
            "[Fr(~k)] --[ _restrict(h(~k) = ~k) ]-> []",
        ),
        (
            "let x = 'value'",
            "[] --[ _restrict(Ex x #i. A(x) @ i) ]-> []",
            "[] --[ _restrict(Ex x #i. A(x) @ i) ]-> []",
        ),
        (
            "let x = y",
            "[] --[ _restrict(Ex y #i. A(x,y) @ i) ]-> []",
            "[] --[ _restrict(Ex y.1 #i. A(y,y.1) @ i) ]-> []",
        ),
        (
            "let x = y.18446744073709551615",
            "[] --[ _restrict(Ex y.18446744073709551615 #i. \
             A(x,y.18446744073709551615,y.0,y.1) @ i) ]-> []",
            "[] --[ _restrict(Ex y.5 #i. \
             A(y.18446744073709551615,y.5,y.0,y.1) @ i) ]-> []",
        ),
    ] {
        let thy = |rule: &str| format!("theory T begin builtins: hashing rule R: {rule} end");
        assert_eq!(
            first_rule_e(&thy(&format!("{lets} in {body}"))),
            first_rule_e(&thy(expanded)),
            "{lets} in {body}"
        );
    }
}

/// HS `intrRule` reads no `letBlock` (Theory/Text/Parser/Rule.hs).
#[test]
fn an_intruder_rule_rejects_a_let_block() {
    let src = "theory T begin\n\
               rule (modulo AC) d_0_fst: let p = <x, y> in [ !KD(p) ] --> [ !KD(x) ]\n\
               end";
    let err = elaborate(&parse_theory(src, &[]).unwrap()).unwrap_err();
    assert!(err.message.contains("let block"), "{}", err.message);
}

fn duplicate_rule_error(src: &str) -> Option<String> {
    elaborate(&parse_theory(src, &[]).unwrap())
        .err()
        .map(|e| e.message)
}

/// `addOpenProtoRule` (OpenTheory.hs) rejects a name bound to a different
/// open rule and appends an equal one again.  Equality is on the elaborated
/// rules, so two spellings of one term, or a `let` and its expansion, are
/// equal.  [`parse_theory_checked`] raises the conflict while parsing, at the
/// second rule's name; a theory parsed without the check meets the same
/// guard at elaboration, as HS's `duplicate rule: <name>`.
#[test]
fn a_rule_name_bound_to_a_different_rule_is_a_duplicate() {
    for (first, second) in [
        (
            "rule R1[color=ff0000]: [ ] --> [ ]",
            "rule R1[color=00ff00]: [ ] --> [ ]",
        ),
        (
            "rule R1: [ ] --> [ Out('a') ]",
            "rule R1: [ ] --> [ Out('b') ]",
        ),
        (
            "rule R1: [ ] --> [ Out('a') ]",
            "rule R1: [ ] --[ _restrict( All x #i #j. A(x) @ #i & A(x) @ #j \
             ==> #i = #j ) ]-> [ Out('a') ]",
        ),
    ] {
        let src = format!("theory T begin\n{first}\n{second}\nend");
        assert_eq!(
            duplicate_rule_error(&src).as_deref(),
            Some("duplicate rule: R1"),
            "{second}"
        );
        let err = parse_theory_checked(&src, &[], None).unwrap_err();
        assert!(
            matches!(err.kind(), tamarin_parser::ParseErrorKind::ConflictingDeclaration {
                name, context: tamarin_parser::ParseContext::Rule } if name == "R1"),
            "{second}: {err:?}"
        );
        let label = &err.diagnostic_labels_with_source(&src)[0];
        assert_eq!(label.span.start, src.rfind("R1").unwrap(), "{second}");
    }
    for (first, second) in [
        ("rule R1: [ ] --> [ ]", "rule R1: [ ] --> [ ]"),
        (
            "rule R1: [ Fr(~k) ] --> [ Out(<~k, ~k>) ]",
            "rule R1: let x = ~k in [ Fr(~k) ] --> [ Out(pair(x, ~k)) ]",
        ),
    ] {
        let src = format!("theory T begin\n{first}\n{second}\nend");
        assert_eq!(duplicate_rule_error(&src), None, "{second}");
        parse_theory_checked(&src, &[], None).expect(second);
        let thy = elaborate(&parse_theory(&src, &[]).unwrap()).unwrap();
        assert_eq!(thy.rules().count(), 2, "{second}");
    }
}

#[test]
fn a_duplicate_rule_across_an_include_is_rejected() {
    let dir = std::env::temp_dir().join(format!(
        "tamarin_theory_dup_rule_include_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("mkdir");
    std::fs::write(
        dir.join("frag.spthy"),
        "rule R1[color=ff0000]: [ ] --> [ ]\n",
    )
    .expect("write fragment");
    let src = "theory T begin\n#include \"frag.spthy\"\nrule R1[color=00ff00]: [ ] --> [ ]\nend\n";
    let parsed = tamarin_parser::parse_theory_with_base(src, &[], Some(dir.clone())).unwrap();
    let checked = parse_theory_checked(src, &[], Some(dir.clone()));
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        elaborate(&parsed).unwrap_err().message,
        "duplicate rule: R1"
    );
    assert!(matches!(
        checked.unwrap_err().kind(),
        tamarin_parser::ParseErrorKind::ConflictingDeclaration { .. }
    ));
}

/// The parse-time check builds each rule under the signature declared before
/// it, as HS's parser state has it; a declaration between two rules that does
/// not touch their symbols leaves them equal.
#[test]
fn a_declaration_between_equal_rules_leaves_them_equal() {
    let src = "theory T begin\n\
               functions: f/1\n\
               rule R1: [ In(x) ] --> [ Out(f(x)) ]\n\
               functions: g/1 [private]\n\
               rule R1: [ In(x) ] --> [ Out(f(x)) ]\n\
               end";
    let thy = elaborate(&parse_theory_checked(src, &[], None).unwrap()).unwrap();
    assert_eq!(thy.rules().count(), 2);
}
