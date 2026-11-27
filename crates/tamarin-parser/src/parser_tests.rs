// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::parse_error::{ErrorDetails, MAX_DIAGNOSTIC_MESSAGE_CHARS};

#[test]
fn diff_theory_validates_but_does_not_lower_diff_proofs() {
    let src = "theory D begin
        diffLemma observational_equivalence:
        rule-equivalence
        case Rule
        by sorry
        qed
        end";
    let parsed = parse_diff_theory(src, &[]).expect("parse diff theory");
    assert!(parsed.is_diff);
    let TheoryItem::DiffLemma(lemma) = &parsed.items[0] else {
        panic!("expected diff lemma");
    };
    let proof = lemma.proof.as_ref().expect("stored diff proof");
    assert!(proof.tree.is_none());

    assert!(parse_diff_theory("theory D begin diffLemma E: rule-equivalence end", &[]).is_err());
}
use tamarin_term::maude_sig::pair_maude_sig;

/// [`parse_formula_str`] against the signature HS `parseString` installs
/// (`pairMaudeSig`, Theory/Text/Parser/Token.hs).
fn parse_formula_str_sig(s: &str) -> Result<Formula, ParseError> {
    parse_formula_str(s, &pair_maude_sig())
}

/// A parser carrying `msig`'s symbols, standing in for the theory parser
/// [`parse_parens_goal`] reads a stored proof's goals inside.
fn sig_parser(msig: &tamarin_term::maude_sig::MaudeSig) -> Parser<'static> {
    let mut p = Parser::new("", &[], false);
    p.seed_signature(msig);
    p
}

/// The small side of the subterm goal `<src> ⊏ y`, which is where the goal
/// grammar reads a term.
fn goal_term(src: &str, msig: &tamarin_term::maude_sig::MaudeSig) -> Result<Term, ParseError> {
    parse_parens_goal(&format!("({src} \u{228F} y)"), &sig_parser(msig)).map(|(g, _)| match g {
        GoalSpec::Subterm(small, _) => small,
        other => panic!("expected a subterm goal for {src}, got {other:?}"),
    })
}

#[test]
fn alternative_selection_preserves_the_complete_furthest_error() {
    let progress = Pos {
        offset: 20,
        line: 2,
        col: 10,
    };
    let cause = Pos {
        offset: 3,
        line: 1,
        col: 4,
    };
    for semantic_first in [false, true] {
        let generic = ParseError::expected(Pos::ZERO, "term", Some(')'));
        let mut semantic = ParseError::at(progress)
            .with_kind(ParseErrorKind::PersistentFreshFact)
            .with_location(cause, 2);
        semantic.source = "included.spthy".into();
        let selected = if semantic_first {
            Parser::select_alt_error(semantic, generic)
        } else {
            Parser::select_alt_error(generic, semantic)
        };
        assert!(matches!(
            selected.kind(),
            ParseErrorKind::PersistentFreshFact
        ));
        assert_eq!(selected.span(), 3..5);
        assert_eq!(selected.line_column(), (1, 4));
        assert_eq!(selected.source, "included.spthy");
        assert_eq!(selected.pos.offset, 20);
        assert_eq!(
            selected.diagnostic_notes(),
            ["the builtin `Fr` fact cannot be persistent"]
        );
    }
}

#[test]
fn alternative_selection_prioritizes_progress_and_keeps_stable_ties() {
    let later = Pos {
        offset: 9,
        line: 1,
        col: 10,
    };
    let semantic = ParseError::at(Pos::ZERO).with_kind(ParseErrorKind::PersistentFreshFact);
    let generic = ParseError::expected(later, "term", Some(')'));
    let selected = Parser::select_alt_error(semantic, generic);
    assert_eq!(selected.pos.offset, 9);
    assert!(matches!(selected.kind(), ParseErrorKind::Expected { .. }));
    let first = ParseError::expected(later, "term", Some(')'));
    let second = ParseError::expected(later, "fact", Some(')'));
    assert_eq!(
        Parser::select_alt_error(first, second).diagnostic_notes(),
        ["expected term; found ')'"]
    );
    let first = ParseError::expected(later, "term", Some(')'));
    let second = ParseError::at(later).with_kind(ParseErrorKind::PersistentFreshFact);
    assert!(matches!(
        Parser::select_alt_error(first, second).kind(),
        ParseErrorKind::Expected { .. }
    ));
    let first = ParseError::custom(later, "first cause".into());
    let second = ParseError::custom(later, "second cause".into());
    assert_eq!(
        Parser::select_alt_error(first, second).diagnostic_message(),
        "first cause"
    );
}

#[test]
fn fact_goal_heads_backtrack_but_node_failures_commit() {
    for source in ["G(x) ▶ #i", "G(x) ▶x #i", "G(x) ∥ H(x))"] {
        let mut parser = Parser::new(source, &[], false);
        let mut head_error = None;
        assert!(parser.fact_goal(&mut head_error).unwrap().is_none());
        assert_eq!(parser.save().offset, 0);
        assert!(head_error.is_some());
        if source.contains('∥') {
            assert!(matches!(parser.goal().unwrap(), GoalSpec::Disj(parts) if parts.len() == 2));
        }
    }
    for separator in ["@", "▶₀"] {
        for node in ["~i", "i:msg"] {
            let source = format!("G(x) {separator} {node} ∥ H(x))");
            let mut parser = Parser::new(&source, &[], false);
            let mut head_error = None;
            let error = parser.fact_goal(&mut head_error).unwrap_err();
            assert!(head_error.is_none());
            assert_eq!(error.span().start, source.find(node).unwrap());
            assert!(error.diagnostic_message().contains("timepoint variable"));
        }
    }
}

#[test]
fn diagnostic_details_bound_owned_text() {
    let long = "é".repeat(100_000);
    let error = ParseError::custom(Pos::ZERO, long.clone());
    assert!(error.diagnostic_message().chars().count() <= MAX_DIAGNOSTIC_MESSAGE_CHARS + 1);
    let error = ParseError::expected(Pos::ZERO, long, None);
    let Some(ErrorDetails::Expected { expected, .. }) = error.details else {
        panic!()
    };
    assert!(expected.chars().count() <= MAX_DIAGNOSTIC_MESSAGE_CHARS + 1);
    assert!(expected.capacity() < 4096);
}

#[test]
fn theory_options_are_limited_to_the_shared_declarable_set() {
    let all = DeclarableOption::ALL
        .map(DeclarableOption::as_str)
        .join(", ");
    assert!(parse_theory(&format!("theory P begin\noptions: {all}\nend"), &[]).is_ok());

    let err = parse_theory("theory P begin\noptions: unknown-option\nend", &[])
        .expect_err("unknown option must fail");
    assert_eq!(err.line_column(), (2, 10));
    assert!(err
        .diagnostic_notes()
        .iter()
        .any(|note| note.contains("theory option")));

    let err = parse_theory("theory P begin\noptions: translation-progressx\nend", &[])
        .expect_err("a valid option prefix must leave its suffix to the outer parser");
    assert_eq!(err.line_column(), (2, 30));
    assert!(matches!(err.kind(), ParseErrorKind::UnknownItem { item, .. } if item == "x"));
}

#[test]
fn empty_theory() {
    let s = "theory Foo begin end";
    let t = parse_theory(s, &[]).unwrap();
    assert_eq!(t.name, "Foo");
    assert!(t.items.is_empty());
}

#[test]
fn theory_with_builtins() {
    let s = "theory T begin builtins: hashing, signing end";
    let t = parse_theory(s, &[]).unwrap();
    match &t.items[0] {
        TheoryItem::Builtins(v) => {
            assert_eq!(v, &vec!["hashing".to_string(), "signing".into()])
        }
        x => panic!("expected builtins, got {:?}", x),
    }
}

#[test]
fn simple_rule() {
    let s = r#"
            theory T begin
              rule R: [Fr(~k)] --[ Foo(~k) ]-> [ Out(~k) ]
            end
        "#;
    let t = parse_theory(s, &[]).unwrap();
    match &t.items[0] {
        TheoryItem::Rule(r) => {
            assert_eq!(r.name, "R");
            // Each of the three lists holds exactly one fact.  So only the
            // names separate the premise, action and conclusion slots.  The
            // test compares the names, not the lengths.
            fn names(fs: &[Fact]) -> Vec<&str> {
                fs.iter().map(|f| f.name.as_str()).collect()
            }
            assert_eq!(names(&r.premises), ["Fr"]);
            assert_eq!(names(&r.actions), ["Foo"]);
            assert_eq!(names(&r.conclusions), ["Out"]);
        }
        x => panic!("expected rule, got {:?}", x),
    }
}

#[test]
fn lemma_with_quantifier() {
    let s = r#"
            theory T begin
              lemma secret: "All x #i. K(x) @ i ==> F"
            end
        "#;
    let t = parse_theory(s, &[]).unwrap();
    match &t.items[0] {
        TheoryItem::Lemma(l) => {
            assert_eq!(l.name, "secret");
            // The parser gives the quoted body to the formula parser.  It
            // does not keep the body as text.  The two binders `x` and `#i`
            // and the `All` head must reach the AST.
            match &l.formula {
                Formula::Forall(vs, _) => assert_eq!(vs.len(), 2),
                other => panic!("expected Forall, got {:?}", other),
            }
        }
        x => panic!("expected lemma, got {:?}", x),
    }
}

#[test]
fn comment_handling() {
    let s = "/* outer */ theory T // line\n begin /* x /* y */ z */ diffLemma{*body*} end";
    let t = parse_theory(s, &[]).unwrap();
    assert_eq!(t.name, "T");
    assert!(
        matches!(t.items.as_slice(), [TheoryItem::FormalComment { header, body }] if header == "diffLemma" && body == "body")
    );
}

/// The one argument of a subterm goal.  The goal grammar reads it with the
/// theory's symbols, so an arity-2 head takes a nested tuple as ONE of its
/// two arguments.
#[test]
fn term_application() {
    match goal_term("pair(<a, b>, ~k)", &pair_maude_sig()).unwrap() {
        Term::App(name, args) => {
            assert_eq!(name, "pair");
            // The nested tuple is one argument, not two.
            assert!(
                matches!(args.as_slice(), [Term::Pair(p), Term::Var(_)] if p.len() == 2),
                "unexpected argument shape: {:?}",
                args
            );
        }
        other => panic!("expected App, got {:?}", other),
    }
}

// HS `blatom` (Theory/Text/Parser/Formula.hs) tries the term-relational
// atoms
// (Subterm/Less/EqE) BEFORE the bare-fact `Pred` alternative, so an
// uppercase function applied with a relational operator is an equality/
// subterm atom, not a predicate. Verified against tamarin-prover 1.13.0:
// `A(Foo(x))@i ==> Foo(x) = Foo(y)` renders `(Foo(x) = Foo(y))`.
#[test]
fn fatom_fact_lhs_of_relop_is_term_atom() {
    // Equality: `Foo(x) = Foo(y)` must be Atom::Eq(App,App), not Pred.
    let f = parse_formula_str_sig("Foo(x) = Foo(y)").unwrap();
    match f {
        Formula::Atom(Atom::Eq(Term::App(l, _), Term::App(r, _))) => {
            assert_eq!(l, "Foo");
            assert_eq!(r, "Foo");
        }
        other => panic!("expected Eq(App,App), got {:?}", other),
    }
    // Subterm: `A(x) << B(y)` must be Atom::Subterm, not Pred.
    let f = parse_formula_str_sig("A(x) << B(y)").unwrap();
    match f {
        Formula::Atom(Atom::Subterm(Term::App(l, _), Term::App(r, _))) => {
            assert_eq!(l, "A");
            assert_eq!(r, "B");
        }
        other => panic!("expected Subterm(App,App), got {:?}", other),
    }
    // A genuine predicate atom (no following relational op) stays Pred.
    let f = parse_formula_str_sig("P(x) & Q(y)").unwrap();
    match f {
        Formula::And(a, _) => match *a {
            Formula::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
            ref other => panic!("expected Pred, got {:?}", other),
        },
        other => panic!("expected And, got {:?}", other),
    }
    // Implication after a predicate must NOT be misread as `=` (==> guard).
    let f = parse_formula_str_sig("P(x) ==> Q(y)").unwrap();
    match f {
        Formula::Implies(a, _) => match *a {
            Formula::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
            ref other => panic!("expected Pred LHS of ==>, got {:?}", other),
        },
        other => panic!("expected Implies, got {:?}", other),
    }
}

// HS `typep` (Token.hs) maps only the literal `Any` to the default
// (Nothing); lowercase `any` is `Just "any"`. Verified against
// tamarin-prover 1.13.0: `new x:any` renders with `:any` preserved.
#[test]
fn type_p_only_capital_any_is_default() {
    // `functions: f(any):bitstring` — arg type must be Some("any").
    let t = parse_theory("theory T begin functions: f(any):bitstring end", &[]).unwrap();
    let decl = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Functions(ds) => ds.iter().find(|d| d.name == "f"),
            _ => None,
        })
        .expect("function f");
    assert_eq!(decl.arg_types, vec![Some("any".to_string())]);
    assert_eq!(decl.out_type, Some("bitstring".to_string()));

    // `functions: g(Any):bitstring` — capital Any is the default (None).
    let t = parse_theory("theory T begin functions: g(Any):bitstring end", &[]).unwrap();
    let decl = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Functions(ds) => ds.iter().find(|d| d.name == "g"),
            _ => None,
        })
        .expect("function g");
    assert_eq!(decl.arg_types, vec![None]);
}

// HS `tupleterm` uses `chainr1`, which requires >=1 operand, so `<>` fails
// to parse and `<x>` collapses to `x`. Verified against tamarin-prover
// 1.13.0: `A(<>)` is a parse error; `A(<x>)` renders `A( x )`.
#[test]
fn empty_tuple_is_error_singleton_collapses() {
    let term = |src: &str| goal_term(src, &pair_maude_sig());
    assert!(term("<>").is_err(), "<> must be a parse error");
    // Singleton tuple collapses to the inner term.
    match term("<x>").unwrap() {
        Term::Var(v) => assert_eq!(v.name, "x"),
        other => panic!("expected singleton to collapse to Var, got {:?}", other),
    }
    // Two-element tuple is a Pair.
    match term("<x, y>").unwrap() {
        Term::Pair(items) => assert_eq!(items.len(), 2),
        other => panic!("expected Pair, got {:?}", other),
    }
}

// HS `factAnnotation` (Theory/Text/Parser/Fact.hs) maps
// `opUnion` to SolveFirst, `opMinus` to SolveLast and `no_precomp` to
// NoSources.  HS also defines `opUnion = symbol_ "++" <|> symbol_ "+"`
// (Token.hs).  So the parser accepts `[++]` like `[+]`.
// Verified against tamarin-prover 1.13.0: `Foo(~k)[++]` parses and renders
// as `[+]`.
#[test]
fn fact_annotation_accepts_double_plus() {
    use FactAnnotation::*;
    for (written, expected) in [
        ("[++]", vec![SolveFirst]),
        ("[+]", vec![SolveFirst]),
        ("[-]", vec![SolveLast]),
        ("[no_precomp]", vec![NoSources]),
        // `list` is comma-separated.  The annotations keep the source order.
        ("[-,++,no_precomp]", vec![SolveLast, SolveFirst, NoSources]),
        ("[]", vec![]),
        ("", vec![]),
    ] {
        let s =
            format!("theory T begin rule R: [ Fr(~k) ] --[ Foo(~k){written} ]-> [ Out(~k) ] end");
        let t = parse_theory(&s, &[]).unwrap_or_else(|e| panic!("{written}: {e}"));
        let rule = t
            .items
            .iter()
            .find_map(|it| match it {
                TheoryItem::Rule(r) => Some(r),
                _ => None,
            })
            .expect("rule R");
        assert_eq!(
            rule.actions[0].annotations, expected,
            "annotation {written}"
        );
    }
}

// ---- Stored proof boundaries and source preservation ---------------------

/// The source text consumed by the theory's single lemma proof. Checking the
/// lemma count also catches proof tokens accidentally parsed as theory items.
fn lemma_proof_raw(thy: &Theory) -> &str {
    let mut lemmas = thy.items.iter().filter_map(|it| match it {
        TheoryItem::Lemma(l) => Some(l),
        _ => None,
    });
    let l = lemmas.next().expect("a lemma");
    assert!(lemmas.next().is_none(), "expected exactly one lemma");
    &l.proof.as_ref().expect("lemma has a proof skeleton").raw
}

#[test]
fn stored_proof_preserves_raw_and_lemma_text_whitespace() {
    let lemma_text = "lemma L:\t\"T\"\n  by\t sorry \n \t";
    let source = format!("theory T begin\n{lemma_text}rule R: [] --> []\nend");
    let theory = parse_theory(&source, &[]).expect("proof followed by a rule");
    let TheoryItem::Lemma(lemma) = &theory.items[0] else {
        panic!("expected lemma");
    };
    assert_eq!(lemma.proof.as_ref().unwrap().raw, "by\t sorry \n \t");
    assert_eq!(lemma.plaintext, lemma_text);
    assert!(matches!(&theory.items[1], TheoryItem::Rule(rule) if rule.name == "R"));
}

#[test]
fn completed_proofs_keep_following_theory_items_separate() {
    for (is_diff, declaration, proof) in [
        (
            false,
            "lemma L: \"T\"\n",
            "induction\n  case lemma\n  by sorry\nqed \t/* proof tail */\n  ",
        ),
        (
            true,
            "diffLemma L:\n",
            "rule-equivalence\n  case lemma\n  MIRRORED\nqed \t/* proof tail */\n  ",
        ),
    ] {
        for (following, item_kind) in [
            ("text{* proof documentation *}\n", "comment"),
            ("lemma Next: \"T\" by sorry\n", "lemma"),
            ("rule Next: [] --> []\n", "rule"),
            ("#ifdef LIVE\nrule Next: [] --> []\n#endif\n", "rule"),
        ] {
            let source = format!("theory T begin\n{declaration}{proof}{following}end");
            let theory = if is_diff {
                parse_diff_theory(&source, &["LIVE"])
            } else {
                parse_theory(&source, &["LIVE"])
            }
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert_eq!(theory.items.len(), 2, "{source}");
            let stored = match &theory.items[0] {
                TheoryItem::Lemma(lemma) => lemma.proof.as_ref().unwrap(),
                TheoryItem::DiffLemma(lemma) => lemma.proof.as_ref().unwrap(),
                other => panic!("expected proof-bearing lemma, got {other:?}"),
            };
            assert_eq!(stored.raw, proof, "{source}");
            assert_eq!(stored.tree.is_none(), is_diff);
            match (&theory.items[1], item_kind) {
                (TheoryItem::FormalComment { header, body }, "comment") => {
                    assert_eq!(header, "text");
                    assert_eq!(body, " proof documentation ");
                }
                (TheoryItem::Lemma(lemma), "lemma") => assert_eq!(lemma.name, "Next"),
                (TheoryItem::Rule(rule), "rule") => assert_eq!(rule.name, "Next"),
                (other, _) => panic!("expected {item_kind}, got {other:?}"),
            }
        }
    }
}

/// Text inside a public literal of a stored proof is data: a closing
/// parenthesis, a keyword, a comment opener or a backslash there neither ends
/// the proof nor escapes anything, and the raw proof keeps it.
#[test]
fn stored_proof_ignores_structure_inside_public_literals() {
    for proof in [
        "by solve( Foo('a)) rule') @ #i )\n",
        "by solve( Foo('a\\') @ #i )\n",
        "by solve( G(' /* ' )) rule */ x') @ #i)\n",
        "by solve( G(' // ' )) rule\n x') @ #i)\n",
    ] {
        let source = format!("theory T\nbegin\nlemma L: \"T\"\n{proof}end\n");
        let theory = parse_theory(&source, &[]).unwrap_or_else(|e| panic!("{proof}: {e}"));
        assert_eq!(lemma_proof_raw(&theory), proof);
    }
}

/// A diagnostic's expectation set holds what the failing position could
/// have read, once each: 200 declared `[AC]` operators do not join an item
/// or declaration error, and 40 nested parentheses that all fail at one
/// token leave one expectation.
#[test]
fn expectation_sets_stay_bounded() {
    let operators = (0..200)
        .map(|index| format!("f{index}/2 [AC]"))
        .collect::<Vec<_>>()
        .join(", ");
    let error = parse_theory(
        &format!("theory T begin\nfunctions: {operators}\nmacros: m(x) = x, m(y) = y\nend"),
        &[],
    )
    .expect_err("the second macro conflicts");
    let rendered = error.to_string();
    assert!(
        rendered.contains("Conflicting macro")
            && rendered.contains("`m` was already declared incompatibly"),
        "{rendered}"
    );

    let error = parse_theory(
        &format!("theory T begin\nfunctions: {operators}\nequations: x = y\n@\nend"),
        &[],
    )
    .expect_err("junk at item position must fail");
    assert_eq!(
        error.diagnostic_notes(),
        ["expected theory item, \"end\"; found '@'"]
    );

    let formula = format!("{}☃{}", "(".repeat(40), ")".repeat(40));
    let error =
        parse_theory(&format!("theory T begin lemma L: \"{formula}\" end"), &[]).unwrap_err();
    assert_eq!(error.diagnostic_notes(), ["expected term; found '☃'"]);
}

// ---- user-defined AC function symbols (upstream #883) ----

fn fun_decl(t: &Theory, name: &str) -> FunctionDecl {
    for it in &t.items {
        if let TheoryItem::Functions(ds) = it {
            for d in ds {
                if d.name == name {
                    return d.clone();
                }
            }
        }
    }
    panic!("function {name} must be declared");
}

fn equation_lhs(src: &str) -> Term {
    let t = parse_theory(src, &[]).expect("theory must parse");
    for it in &t.items {
        if let TheoryItem::Equations { eqs, .. } = it {
            return eqs[0].lhs.clone();
        }
    }
    panic!("theory must contain an equation");
}

// HS `functionAttribute` (Theory/Text/Parser/Signature.hs) accepts
// `AC`, `NDC-diff` and `NDC`; `function`
// (Theory/Text/Parser/Signature.hs) folds them into the symbol's AC
// and NDC state.
#[test]
fn function_attributes_ac_ndc() {
    let t = parse_theory("theory T begin functions: a/2 [AC] end", &[]).unwrap();
    let a = fun_decl(&t, "a");
    assert!(a.ac && !a.ndc && !a.ndc_diff);

    let t = parse_theory("theory T begin functions: b/2 [AC,NDC] end", &[]).unwrap();
    let b = fun_decl(&t, "b");
    assert!(b.ac && b.ndc && !b.ndc_diff);

    // `NDC-diff` is tried before `NDC`, so it is never read as `NDC`
    // followed by a stray `-diff`.
    let t = parse_theory("theory T begin functions: c/2 [NDC-diff] end", &[]).unwrap();
    let c = fun_decl(&t, "c");
    assert!(!c.ac && !c.ndc && c.ndc_diff);

    let src = "theory T begin functions: d/2 [AC, NDC-diff, NDC] end";
    let t = parse_theory(src, &[]).unwrap();
    let d = fun_decl(&t, "d");
    assert!(d.ac && d.ndc && d.ndc_diff);

    let src = "theory T begin functions: e/1 [private,destructor] end";
    let t = parse_theory(src, &[]).unwrap();
    let e = fun_decl(&t, "e");
    assert!(e.private && e.destructor && !e.ac && !e.ndc && !e.ndc_diff);
}

/// `f/n` declares the same symbol as `f(Any, ...):Any` with n arguments.
#[test]
fn numeric_arities_materialize_the_same_types_as_explicit_any_arguments() {
    for (numeric, typed) in [
        ("f/0", "f():Any"),
        ("f/1", "f(Any):Any"),
        ("f/3", "f(Any,Any,Any):Any"),
        ("f/2 [AC]", "f(Any,Any):Any [AC]"),
        ("fst/1 [AC]", "fst(Any):Any [AC]"),
    ] {
        let declarations = |decl: &str| {
            parse_theory(
                &format!("theory T begin\n\nfunctions: {decl}\n\nend\n"),
                &[],
            )
            .unwrap()
            .items
        };
        assert_eq!(declarations(numeric), declarations(typed), "{numeric}");
    }
}

// HS `acterm` (Theory/Text/Parser/Term.hs): a binary `[AC]` symbol is
// also an infix,
// left-associative operator — the notation `prettyTerm` emits for such
// terms.  The AST records the infix spelling as `BinOp::AcFct`, distinct
// from the prefix `App`, because a name that is also a `NoEq` symbol of
// the signature resolves NoEq when written prefix (`lookupArity`,
// Theory/Text/Parser/Term.hs) but stays the AC symbol when written
// infix.
#[test]
fn ac_symbol_parses_infix_left_associative() {
    let src = "theory T begin functions: add/2 [AC] equations: x add y = z end";
    match equation_lhs(src) {
        Term::BinOp(BinOp::AcFct(f), _, _) => assert_eq!(f, "add"),
        other => panic!("expected an infix `add`, got {other:?}"),
    }
    // `chainl1` associates to the LEFT.
    let src = "theory T begin functions: add/2 [AC] equations: x add y add z = w end";
    match equation_lhs(src) {
        Term::BinOp(BinOp::AcFct("add"), l, _) => match *l {
            Term::BinOp(BinOp::AcFct("add"), _, _) => {}
            other => panic!("expected a nested `add` on the LEFT, got {other:?}"),
        },
        other => panic!("expected an infix `add`, got {other:?}"),
    }
}

// HS `acterm`'s `parseACSym` recursion nests one `chainl1` level per AC symbol
// in `S.toList (stACFunSyms sig)` (i.e. name) order, so the LAST symbol in
// that order binds tightest: `x f y g z` is `f(x, g(y,z))` however the two
// symbols were declared.
#[test]
fn ac_symbols_nest_in_name_order() {
    let src = "theory T begin functions: g/2 [AC], f/2 [AC] equations: x f y g z = w end";
    match equation_lhs(src) {
        Term::BinOp(BinOp::AcFct("f"), _, r) => match *r {
            Term::BinOp(BinOp::AcFct("g"), _, _) => {}
            other => panic!("expected `g` to bind tighter than `f`, got {other:?}"),
        },
        other => panic!("expected `f` at the root, got {other:?}"),
    }
}

// A symbol is an infix operator only once DECLARED `[AC]` (HS reads the AC
// symbols out of the parse-time signature state).
// A `:` after a variable means different things inside and outside a SAPIC
// process.  Rules/formulas use `msgvar`/`lvar` = `sortedLVar`, whose
// `mkSuffixParser` reads `x:nat` as the NAT-SORTED `x` (Token.hs);
// processes use `sapicvar` = `lvarNoSuffix` (prefix sorts only) plus
// an optional type, so the same text is the msg-sorted `x` carrying the SAPIC
// TYPE `"nat"` (Token.hs). Node-sorted variables default to type `node`, while
// an explicit `Any` remains the untyped placeholder.
#[test]
fn colon_suffix_is_a_sapic_type_in_a_process_and_a_sort_in_a_rule() {
    fn process_let_binder(src: &str) -> VarSpec {
        let thy = parse_theory(src, &[]).expect("parses");
        for item in &thy.items {
            if let TheoryItem::TopLevelProcess(Process::Comb {
                comb: ProcessComb::Let {
                    pat: Term::Var(v), ..
                },
                ..
            }) = item
            {
                return v.clone();
            }
        }
        panic!("no let binder in {src}");
    }

    let v = process_let_binder(
        "theory T begin builtins: natural-numbers process: let x:nat = %c %+ %1 in 0 end",
    );
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Msg, Some("nat")));
    let v = process_let_binder("theory T begin process: let x:msg = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Msg, Some("msg")));
    let v = process_let_binder("theory T begin process: let x:Any = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Msg, None));
    // The `%` PREFIX still sorts a process variable (`lvarNoSuffix` keeps every
    // prefix parser), and a type may follow it.
    let v = process_let_binder(
        "theory T begin builtins: natural-numbers process: let %x:nat = %c in 0 end",
    );
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Nat, Some("nat")));
    let v = process_let_binder("theory T begin process: let #x = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Node, Some("node")));
    let v = process_let_binder("theory T begin process: let #x:Any = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Node, None));

    // Same text in a rule: a sort suffix, no type.
    let thy = parse_theory(
        "theory T begin builtins: natural-numbers rule R: [ In(x:nat) ] --[ ]-> [ ] end",
        &[],
    )
    .expect("parses");
    let mut seen = None;
    for item in &thy.items {
        if let TheoryItem::Rule(r) = item
            && let Term::Var(v) = &r.premises[0].args[0]
        {
            seen = Some(v.clone());
        }
    }
    let v = seen.expect("rule premise variable");
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Nat, None));

    // A pattern variable takes a type too: `sapicpatternvar` (Token.hs).
    let thy = parse_theory(
        "theory T begin process: in('c', <=x:nat, y>); out('c', y) end",
        &[],
    )
    .expect("parses");
    let pattern = thy.items.iter().find_map(|item| match item {
        TheoryItem::TopLevelProcess(Process::Action {
            action:
                SapicAction::ChIn {
                    msg: Term::Pair(items),
                    ..
                },
            ..
        }) => Some(items[0].clone()),
        _ => None,
    });
    let Some(Term::PatMatch(inner)) = pattern else {
        panic!("`=x:nat` is a pattern: {pattern:?}");
    };
    let Term::Var(v) = *inner else {
        panic!("the pattern wraps a variable");
    };
    assert_eq!((v.sort, v.typ.as_deref()), (LSort::Msg, Some("nat")));
}

/// A digit-initial name after `%` is a nat variable, not `%1` followed by a
/// suffix (`natVar`, Token.hs).
#[test]
fn digit_initial_nat_variable_is_not_split_as_nat_one() {
    let thy = parse_theory(
        "theory T begin\nbuiltins: natural-numbers\nrule R: [ In(%12) ] --> [ Out(%1) ]\nend",
        &[],
    )
    .expect("digit-initial nat variable");
    let rule = thy
        .items
        .iter()
        .find_map(|item| match item {
            TheoryItem::Rule(rule) => Some(rule),
            _ => None,
        })
        .expect("rule");
    assert!(matches!(
        &rule.premises[0].args[0],
        Term::Var(var) if var.name == "12" && var.sort == LSort::Nat
    ));
    assert_eq!(rule.conclusions[0].args[0], Term::NatOne);
}

// =============================================================================
// The sort the parser stamps on every variable
// =============================================================================

/// The argument of the predicate `P(<args>)`, read as a lemma formula, where
/// a variable of every sort may appear (`fact (vlit (try varp <|> nodep))`,
/// Theory/Text/Parser/Formula.hs).
fn predicate_term(args: &str) -> Term {
    let src = format!("theory T begin builtins: natural-numbers lemma L: \"P(<{args}>)\" end");
    let thy = parse_theory(&src, &[]).expect("parses");
    match thy.items.last() {
        Some(TheoryItem::Lemma(Lemma {
            formula: Formula::Atom(Atom::Pred(fact)),
            ..
        })) => fact.args[0].clone(),
        other => panic!("expected a predicate lemma, got {other:?}"),
    }
}

/// `(name, idx, sort)` of every element of a tuple of variables.
fn tuple_var_specs(t: &Term) -> Vec<(&str, u64, LSort)> {
    let Term::Pair(items) = t else {
        panic!("expected a tuple, got {t:?}");
    };
    items
        .iter()
        .map(|i| match i {
            Term::Var(v) => (v.name.as_str(), v.idx, v.sort),
            other => panic!("expected a variable, got {other:?}"),
        })
        .collect()
}

/// The variable a term is, or a panic naming what it is instead.
fn var_of(t: &Term) -> &VarSpec {
    match t {
        Term::Var(v) => v,
        other => panic!("expected a variable, got {other:?}"),
    }
}

#[test]
fn explicit_variable_indices_fit_in_u32() {
    let model = |idx| format!("theory T begin rule R: [In(x.{idx})] --> [Out(x.{idx})] end");
    let facts = rule_conclusions(&model(u64::from(u32::MAX)));
    assert_eq!(var_of(&facts[0].args[0]).idx, u64::from(u32::MAX));
    let error = parse_theory(&model(u64::from(u32::MAX) + 1), &[]).unwrap_err();
    assert!(error
        .to_string()
        .contains("variable index exceeds 4294967295"));
}

/// A sigil names the sort and a bare identifier is message-sorted, as HS
/// `sortedLVar`'s prefix arms do — the bare `LSortMsg -> pure ()` case
/// (Token.hs).
#[test]
fn bare_variable_is_msg_sorted() {
    let t = predicate_term("x, x.1, ~f, $p, #i, %n");
    assert_eq!(
        tuple_var_specs(&t),
        vec![
            ("x", 0, LSort::Msg),
            ("x", 1, LSort::Msg),
            ("f", 0, LSort::Fresh),
            ("p", 0, LSort::Pub),
            ("i", 0, LSort::Node),
            ("n", 0, LSort::Nat),
        ]
    );
}

/// `blatom`'s timepoint operands are read with `nodevar`, which stamps
/// `LSortNode` on a bare identifier (Theory/Text/Parser/Formula.hs,
/// Token.hs): the argument of `last`, the operand after `@`, both
/// operands of `<`, and both operands of an equality whose left operand is a
/// node variable — that last one being the "node equality" alternative, which
/// is reached only because "term equality" reads its operands with `msgvar`
/// and `msgvar` rejects a node variable.
#[test]
fn timepoint_positions_are_node_sorted() {
    let sort_of = |src: &str| -> Vec<LSort> {
        match parse_formula_str_sig(src).expect("parses") {
            Formula::Atom(Atom::Action(_, t)) | Formula::Atom(Atom::Last(t)) => {
                vec![var_of(&t).sort]
            }
            Formula::Atom(Atom::Less(l, r)) | Formula::Atom(Atom::Eq(l, r)) => {
                vec![var_of(&l).sort, var_of(&r).sort]
            }
            other => panic!("expected one atom, got {other:?}"),
        }
    };
    assert_eq!(sort_of("A(x) @ i"), vec![LSort::Node]);
    assert_eq!(sort_of("last(i)"), vec![LSort::Node]);
    assert_eq!(sort_of("i < j"), vec![LSort::Node, LSort::Node]);
    assert_eq!(sort_of("#k = l"), vec![LSort::Node, LSort::Node]);
    assert_eq!(sort_of("k:node = l"), vec![LSort::Node, LSort::Node]);
    // The "term equality" alternative reads both operands with `msgvar`, so
    // two bare names are message variables.
    assert_eq!(sort_of("k = l"), vec![LSort::Msg, LSort::Msg]);
}

/// `nodevar` reads a bare name with `indexedIdentifier` (Token.hs),
/// which does not consult the signature, so a name declared as an arity-0
/// symbol is still a timepoint variable in a timepoint position — unlike the
/// term parser, where `nullaryApp` claims it
/// (Theory/Text/Parser/Term.hs).
#[test]
fn nullary_symbol_name_in_a_timepoint_position_is_a_variable() {
    // `c` is an application everywhere the term parser reads it.
    let concs =
        rule_conclusions("theory T begin\nfunctions: c/0\nrule R:\n  [ ] --> [ Out(c) ]\nend");
    assert!(matches!(&concs[0].args[0], Term::App(n, a) if n == "c" && a.is_empty()));

    let thy = parse_theory(
        "theory T begin\n\
         functions: c/0\n\
         lemma l1: \"All #i. A( ) @ c\"\n\
         lemma l2: \"last(c)\"\n\
         lemma l3: \"All #i. #i < c\"\n\
         lemma l4: \"All #i. #i = c\"\n\
         end",
        &[],
    )
    .expect("parses");
    let mut seen = 0;
    for it in &thy.items {
        let TheoryItem::Lemma(l) = it else { continue };
        let f = match &l.formula {
            Formula::Forall(_, body) => body.as_ref().clone(),
            other => other.clone(),
        };
        let t = match f {
            Formula::Atom(Atom::Action(_, t)) | Formula::Atom(Atom::Last(t)) => t,
            Formula::Atom(Atom::Less(_, r)) | Formula::Atom(Atom::Eq(_, r)) => r,
            other => panic!("expected one atom in {}, got {other:?}", l.name),
        };
        let v = var_of(&t);
        assert_eq!(
            (v.name.as_str(), v.idx, v.sort),
            ("c", 0, LSort::Node),
            "{} reads `c` as a constant",
            l.name
        );
        seen += 1;
    }
    assert_eq!(seen, 4);
}

/// A quantifier binder is `try varp <|> nodep` with `varp = msgvar`
/// (Theory/Text/Parser/Formula.hs), and an operand of an AC operator is
/// a message term, so the `dif` binder and the `seq1` operand of
/// examples/sapic/fast/SCADA/opc_ua_secure_conversation.spthy's
/// `A_Counter_Increases` restriction are both message-sorted.  Both feed
/// `Ord LVar`, which compares the sort second (LTerm.hs), so the
/// printed operand order of `seq1 + dif` follows from them.
#[test]
fn bare_binder_and_bare_message_operand_are_msg_sorted() {
    // That theory declares `builtins: multiset`, which is what opens the `+`
    // level of `msetterm` (Theory/Text/Parser/Term.hs).
    let f = parse_formula_str(
        "All A B seq1 seq2 #i #j.(Seq_Sent(A, B, seq1) @ #i \
         & Seq_Sent(A, B, seq2) @ #j & #i < #j ==> Ex dif. seq2 = seq1 + dif )",
        &pair_maude_sig().merge(tamarin_term::maude_sig::mset_maude_sig()),
    )
    .expect("parses");
    let Formula::Forall(_, body) = &f else {
        panic!("expected a universal quantifier, got {f:?}");
    };
    let Formula::Implies(_, concl) = body.as_ref() else {
        panic!("expected an implication, got {body:?}");
    };
    let Formula::Exists(vs, eq) = concl.as_ref() else {
        panic!("expected an existential quantifier, got {concl:?}");
    };
    assert_eq!(
        (vs[0].name.as_str(), vs[0].idx, vs[0].sort),
        ("dif", 0, LSort::Msg)
    );
    let Formula::Atom(Atom::Eq(_, sum)) = eq.as_ref() else {
        panic!("expected an equality, got {eq:?}");
    };
    let Term::BinOp(BinOp::Union, l, r) = sum else {
        panic!("expected a multiset union, got {sum:?}");
    };
    assert_eq!(var_of(l).sort, LSort::Msg);
    assert_eq!(var_of(r).sort, LSort::Msg);
}

// ---- 0-arity symbols and the DH `exp` head ----

/// The conclusion facts of the first rule of `src`.
fn rule_conclusions(src: &str) -> Vec<Fact> {
    parse_theory(src, &[])
        .expect("parses")
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Rule(r) => Some(r.conclusions.clone()),
            _ => None,
        })
        .expect("the theory declares a rule")
}

/// HS `nullaryApp` (Theory/Text/Parser/Term.hs) claims a bare
/// identifier that is an arity-0 symbol of `funSyms maudeSig ∪ macroNames
/// maudeSig`, so it is an application, not a variable.  A sigil and a use
/// ahead of the declaration leave a variable in HS too. A `.idx`, a `:sort`
/// suffix and a SAPIC `:type` are not part of the identifier, so the nullary
/// parser claims the name and leaves the suffix to be rejected.  Only a whole
/// identifier is claimed.
#[test]
fn bare_nullary_symbol_parses_as_application() {
    let concs = rule_conclusions(
        "theory T begin\n\
         builtins: signing, xor, diffie-hellman, natural-numbers\n\
         functions: c/0\n\
         macros: m() = 'x'\n\
         rule R:\n\
           [ ] --> [ Out(c), Out(true), Out(zero), Out(one), Out(tone), Out(m) ]\n\
         end",
    );
    for (i, name) in ["c", "true", "zero", "one", "tone", "m"].iter().enumerate() {
        assert!(
            matches!(&concs[i].args[0], Term::App(n, a) if n == name && a.is_empty()),
            "{name} is not a 0-arity application: {:?}",
            concs[i].args[0]
        );
    }

    for term in ["c.1", "c:msg"] {
        let src =
            format!("theory T begin\nfunctions: c/0\nrule R:\n  [ ] --> [ Out({term}) ]\nend");
        assert!(parse_theory(&src, &[]).is_err(), "{term} must be rejected");
    }

    assert!(parse_theory(
        "theory T begin\nfunctions: c/0\nprocess: out(c:ty)\nend",
        &[],
    )
    .is_err());

    // A sigil starts a variable parser before `nullaryApp`, so it remains a
    // variable even when the unsigilled name is declared nullary.
    let concs =
        rule_conclusions("theory T begin\nfunctions: c/0\nrule R:\n  [ ] --> [ Out(~c) ]\nend");
    let v = var_of(&concs[0].args[0]);
    assert_eq!((v.name.as_str(), v.sort), ("c", LSort::Fresh));

    // `lookupArity`/`nullaryApp` read the signature declared SO FAR, so a use
    // ahead of the declaration is a variable.
    let concs = rule_conclusions(
        "theory T begin\n\
         rule R:\n\
           [ ] --> [ Out(c) ]\n\
         functions: c/0\n\
         end",
    );
    assert_eq!(var_of(&concs[0].args[0]).name, "c");

    // A nullary symbol or a fixed literal claims a whole identifier only, so
    // one it merely begins stays a variable.
    for (decl, name) in [
        ("functions: c/0\n", "cx"),
        ("", "1abc"),
        ("", "DH_neutralx"),
    ] {
        let concs = rule_conclusions(&format!(
            "theory T begin\n{decl}rule R:\n  [ ] --> [ Out({name}) ]\nend"
        ));
        assert_eq!(var_of(&concs[0].args[0]).name, name);
    }
}

/// A prefix (or `op{a}b`) application whose head resolves to HS `expSym`
/// builds the same node the `^` operator does, which is what makes
/// `prettyTerm` render it infix (Term/Term.hs).  A redeclaration that is
/// a different symbol keeps the application.
#[test]
fn prefix_exp_resolving_to_the_dh_symbol_is_binop_exp() {
    let concs = rule_conclusions(
        "theory T begin\n\
         builtins: diffie-hellman\n\
         rule R:\n\
           [ ] --> [ Out(exp('a', 'b')), Out(exp{'a'}'b'), Out('a' ^ 'b') ]\n\
         end",
    );
    for c in &concs {
        assert!(
            matches!(&c.args[0], Term::BinOp(BinOp::Exp, _, _)),
            "expected an exponentiation node, got {:?}",
            c.args[0]
        );
    }

    // `functions: exp/2 [private]` is a different symbol.
    let concs = rule_conclusions(
        "theory T begin\n\
         functions: exp/2 [private]\n\
         rule R:\n\
           [ ] --> [ Out(exp('a', 'b')) ]\n\
         end",
    );
    assert!(
        matches!(&concs[0].args[0], Term::App(n, a) if n == "exp" && a.len() == 2),
        "expected an application, got {:?}",
        concs[0].args[0]
    );

    // A lone `[AC]` declaration resolves to the AC symbol.
    let concs = rule_conclusions(
        "theory T begin\n\
         functions: exp/2 [AC]\n\
         rule R:\n\
           [ ] --> [ Out(exp('a', 'b')) ]\n\
         end",
    );
    assert!(
        matches!(&concs[0].args[0], Term::BinOp(BinOp::AcFct(_), _, _)),
        "expected an AC node, got {:?}",
        concs[0].args[0]
    );
}

/// The goal grammar reads a stored proof's terms in the state of the parser
/// the text came out of, so it resolves the same 0-arity constants and `[AC]`
/// infix operators the theory parse did.
#[test]
fn structural_mode_resolves_nullary_names_from_the_signature() {
    let mut msig = pair_maude_sig();
    msig.st_fun_syms
        .insert(tamarin_term::function_symbols::NoEqSym::new(
            b"c".to_vec(),
            0,
            tamarin_term::function_symbols::Privacy::Public,
            tamarin_term::function_symbols::Constructability::Constructor,
        ));
    msig.st_ac_fun_syms
        .insert(tamarin_term::function_symbols::AcFctSym::new(
            b"add".to_vec(),
            tamarin_term::function_symbols::Privacy::Public,
            tamarin_term::function_symbols::Constructability::Constructor,
            tamarin_term::function_symbols::NdcState::NotNdc,
        ));

    assert!(matches!(goal_term("c", &msig).unwrap(), Term::App(n, a) if n == "c" && a.is_empty()));
    assert!(matches!(
        goal_term("(x add c)", &msig).unwrap(),
        Term::BinOp(BinOp::AcFct(_), _, _)
    ));
    // Without the declarations both spellings stay what the bare grammar
    // gives them.
    assert!(matches!(
        goal_term("c", &pair_maude_sig()).unwrap(),
        Term::Var(_)
    ));
    assert!(goal_term("(x add c)", &pair_maude_sig()).is_err());
}

// =========================================================================
// Rule `let` blocks
// =========================================================================
//
// HS applies the `let` substitution inside the rule parsers
// (Theory/Text/Parser/Rule.hs); the port keeps the bindings on the rule and
// elaboration applies them (see `elaborate_tests`).

/// The parser records the bindings in source order and leaves the body as
/// written.  HS identifiers start with any alphanumeric character, so
/// upstream's ccs18-5G models bind `let 5G_AV = ...`.
#[test]
fn rule_let_bindings_are_kept_unapplied() {
    let thy = parse_theory(
        r#"theory T begin
            rule R: let 5G_AV = <'a', ~k> b = 5G_AV in [Fr(~k)] --[]-> [Out(b)]
        end"#,
        &[],
    )
    .expect("parses");
    let Some(TheoryItem::Rule(r)) = thy.items.first() else {
        panic!("expected one rule");
    };
    let names: Vec<&str> = r.lets.iter().map(|(v, _)| v.name.as_str()).collect();
    assert_eq!(names, ["5G_AV", "b"]);
    assert!(matches!(&r.lets[0].1, Term::Pair(items) if items.len() == 2));
    assert!(matches!(&r.conclusions[0].args[0], Term::Var(v) if v.name == "b"));
}

/// HS's rule `let` binds a variable — `sortedLVar [LSortMsg, LSortNat]` under
/// `genericletBlock` (Theory/Text/Parser/Let.hs) — while the rule body
/// reads a declared arity-0 symbol as `nullaryApp`'s constant
/// (Theory/Text/Parser/Term.hs).  A binding whose name is such a
/// symbol therefore binds a variable the body never mentions, and the oracle
/// prints `--[ E( c ) ]->` for the theory below.
#[test]
fn a_let_binder_is_a_variable_not_a_nullary_constant() {
    let thy = parse_theory(
        "theory L\nbegin\n\nfunctions: c/0\n\nrule R:\n  let c = 'lit'\n  in\n  \
         [ ] --[ E(c) ]-> [ ]\n\nend\n",
        &[],
    )
    .expect("parses");
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("one rule");
    assert_eq!(
        rule.actions[0].args,
        vec![Term::App("c".to_string(), vec![])]
    );
}

#[test]
fn display_uses_structured_causes_and_primary_locations() {
    for (source, cause, location) in [
        ("theory T begin /*", "Unclosed block comment", (1, 18)),
        (
            "theory T begin functions: f/1, f/3 end",
            "Conflicting function declaration",
            (1, 32),
        ),
    ] {
        let error = parse_theory(source, &[])
            .unwrap_err()
            .with_source("test.spthy");
        assert_eq!(error.to_string(), error.render_plain());
        assert!(error.to_string().contains(cause), "{error}");
        assert_eq!(error.line_column(), location);
    }
}

#[test]
fn reserved_names_have_their_own_kind_and_keyword_span() {
    for word in RESERVED_NAMES {
        for template in [
            "theory T begin functions: NAME/2 end",
            "theory T begin #define NAME end",
            "theory NAME begin end",
            "theory T begin rule NAME: [] --> [] end",
            "theory T begin lemma NAME: \"T\" end",
            "theory T begin predicates: NAME(x) <=> T end",
        ] {
            let start = template.find("NAME").unwrap();
            let source = template.replace("NAME", word);
            let error = parse_theory(&source, &[]).unwrap_err();
            assert!(
                matches!(error.kind(), ParseErrorKind::ReservedKeyword { keyword } if keyword == word),
                "{source}: {error:?}"
            );
            assert_eq!(error.span(), start..start + word.len());
        }
        for suffix in ["x", "_", "0", "é"] {
            parse_theory(
                &format!("theory T begin functions: {word}{suffix}/2 end"),
                &[],
            )
            .unwrap();
        }
    }
}

#[test]
fn show_lit_string_escapes_like_haskell() {
    assert_eq!(show_lit_string("ab"), "\"ab\"");
    assert_eq!(
        show_lit_string("\u{0B}\u{0C}\u{07}\u{08}"),
        "\"\\v\\f\\a\\b\""
    );
    assert_eq!(show_lit_string("a\"b\\c"), "\"a\\\"b\\\\c\"");
    assert_eq!(show_lit_string("\u{100}"), "\"\\256\"");
    assert_eq!(show_lit_string("\u{100}7"), "\"\\256\\&7\"");
}

#[test]
fn expected_diagnostics_distinguish_eof_and_escape_controls() {
    let eof = parse_theory("theory T", &[]).unwrap_err();
    assert!(
        eof.diagnostic_notes()
            .iter()
            .any(|n| n.contains("found end of input")),
        "{eof}"
    );
    let error = parse_theory("theory T begin tactic: t presort: 1 end", &[]).unwrap_err();
    assert_eq!(error.diagnostic_notes(), ["expected letter; found '1'"]);
    for (input, found) in [("\0", "'\\0'"), ("☃", "'☃'"), ("'", "'\\''")] {
        let mut parser = Parser::new(input, &[], false);
        assert_eq!(
            parser.err_expect("term").diagnostic_notes(),
            [format!("expected term; found {found}")]
        );
    }
}

#[test]
fn lemma_comment_stripping_preserves_textarea_newline_rules() {
    for (source, expected) in [
        ("α/β*γ", "α/β*γ"),
        ("a\n// comment\nb", "a\nb"),
        ("a\n/* comment */\nb", "ab"),
        ("a\n\n/* comment */\n\nb", "a\n\nb"),
        ("a// tail", "a"),
        ("a\n/* tail", "a"),
        ("a/* outer /* inner */b */c", "ab */c"),
        ("a// one\n// two\nb", "a\nb"),
        ("a\n/* one *//* two */\nb", "ab"),
        ("a\r\n/* comment */\r\nb", "a\r\r\nb"),
        ("\"a//quoted\"\nb", "\"a\nb"),
        ("a/**/é/**/雪", "aé雪"),
    ] {
        assert_eq!(remove_comments(source), expected, "{source:?}");
    }
}

// =========================================================================
// `#include` graphs
// =========================================================================

enum IncludeExpect {
    /// Parses, with these rules in this order.
    Rules(&'static [&'static str]),
    /// A cycle error whose message names every string here; with a closing
    /// file, the error carries that file's source.
    Cycle {
        names: &'static [&'static str],
        closing: Option<&'static str>,
    },
}

/// `#include` graphs, rooted at `main.spthy`.  A re-entry of an open
/// (file, directory, flags) frame is a cycle the parser reports with its
/// chain; HS hangs on one, so this table is the port's own.  Any other
/// re-visit, a diamond or a guarded re-entry whose `#define` changed the
/// flags, parses.  `{dir}` in a body is the scratch directory's name.
#[test]
fn include_graphs_parse_or_report_their_cycle() {
    use IncludeExpect::*;
    let guarded_common = "#ifdef not COMMON_INCLUDED\n#define COMMON_INCLUDED\n\
        builtins: symmetric-encryption\n\
        rule EstablishKey: [ Fr(~k) ] --> [ !SharedKey($A, $B, ~k) ]\n\
        #include \"channels.spthyi\"\n#endif\n";
    let guarded_channels = "#ifdef not CHANNELS_INCLUDED\n#define CHANNELS_INCLUDED\n\
        #include \"common.spthyi\"\n\
        rule SendEncrypted: [ !SharedKey(A, B, k), In(m) ] --> [ Out(senc(m, k)) ]\n\
        #endif\n";
    #[allow(clippy::type_complexity)]
    let rows: &[(&str, &[(&str, &str)], &[(&str, &str)], IncludeExpect)] = &[
        (
            "acyclic",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"core.spthyi\"\nend\n"),
                ("core.spthyi", "rule Core: [ Fr(~n) ] --[ Core(~n) ]-> [ ]\n"),
            ],
            &[],
            Rules(&["Core"]),
        ),
        (
            "mutual",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"x.spthyi\"\nend\n"),
                ("x.spthyi", "#include \"y.spthyi\"\n"),
                ("y.spthyi", "#include \"x.spthyi\"\n"),
            ],
            &[],
            Cycle {
                names: &["x.spthyi", "y.spthyi"],
                closing: Some("y.spthyi"),
            },
        ),
        (
            "self",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"loop.spthyi\"\nend\n"),
                ("loop.spthyi", "#include \"loop.spthyi\"\n"),
            ],
            &[],
            Cycle {
                names: &["loop.spthyi"],
                closing: None,
            },
        ),
        (
            "self_via_parent_dir",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"loop.spthyi\"\nend\n"),
                ("loop.spthyi", "#include \"../{dir}/loop.spthyi\"\n"),
            ],
            &[],
            Cycle {
                names: &["loop.spthyi"],
                closing: None,
            },
        ),
        (
            "deep",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"one.spthyi\"\nend\n"),
                ("one.spthyi", "#include \"two.spthyi\"\n"),
                ("two.spthyi", "#include \"three.spthyi\"\n"),
                ("three.spthyi", "#include \"one.spthyi\"\n"),
            ],
            &[],
            Cycle {
                names: &["one.spthyi", "three.spthyi"],
                closing: None,
            },
        ),
        // A `#define` on the way round changes the flags once; the next lap
        // re-enters with them unchanged.
        (
            "define_without_guard",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"x.spthyi\"\nend\n"),
                ("x.spthyi", "#define SEEN\n#include \"y.spthyi\"\n"),
                ("y.spthyi", "#include \"x.spthyi\"\n"),
            ],
            &[],
            Cycle {
                names: &["SEEN"],
                closing: None,
            },
        ),
        (
            "diamond",
            &[
                (
                    "main.spthy",
                    "theory T\nbegin\n#include \"a.spthyi\"\n#include \"b.spthyi\"\nend\n",
                ),
                ("core.spthyi", "rule Core: [ ] --> [ ]\n"),
                ("a.spthyi", "#include \"core.spthyi\"\n"),
                ("b.spthyi", "#include \"core.spthyi\"\n"),
            ],
            &[],
            Rules(&["Core", "Core"]),
        ),
        (
            "guarded_mutual",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"common.spthyi\"\nend\n"),
                ("common.spthyi", guarded_common),
                ("channels.spthyi", guarded_channels),
            ],
            &[],
            Rules(&["EstablishKey", "SendEncrypted"]),
        ),
        (
            "guarded_twice_from_main",
            &[
                (
                    "main.spthy",
                    "theory T\nbegin\n#include \"common.spthyi\"\n#include \"channels.spthyi\"\nend\n",
                ),
                ("common.spthyi", guarded_common),
                ("channels.spthyi", guarded_channels),
            ],
            &[],
            Rules(&["EstablishKey", "SendEncrypted"]),
        ),
        // A link's includes resolve from the link's directory (HS
        // `takeDirectory` of the path as written), so the same bytes reached
        // through it include another file.
        (
            "through_a_symlink",
            &[
                ("main.spthy", "theory T\nbegin\n#include \"fragment.spthyi\"\nend\n"),
                ("fragment.spthyi", "#include \"child/fragment.spthyi\"\n"),
                ("child/child/fragment.spthyi", "rule R: [ Fr(~n) ] --[ R(~n) ]-> [ ]\n"),
            ],
            &[("child/fragment.spthyi", "../fragment.spthyi")],
            Rules(&["R"]),
        ),
    ];
    for (name, files, links, expect) in rows {
        if !links.is_empty() && !cfg!(unix) {
            continue;
        }
        let dir =
            std::env::temp_dir().join(format!("tamarin_rs_include_{}_{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let dir_name = dir.file_name().unwrap().to_str().unwrap().to_string();
        for (path, body) in *files {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, body.replace("{dir}", &dir_name)).unwrap();
        }
        #[cfg(unix)]
        for (link, target) in *links {
            std::os::unix::fs::symlink(target, dir.join(link)).unwrap();
        }
        let result = parse_theory_with_base(files[0].1, &[], Some(dir.clone()));
        match (expect, result) {
            (Rules(want), Ok(thy)) => {
                let got: Vec<&str> = thy
                    .items
                    .iter()
                    .filter_map(|i| match i {
                        TheoryItem::Rule(r) => Some(r.name.as_str()),
                        _ => None,
                    })
                    .collect();
                assert_eq!(got, *want, "{name}");
            }
            (Cycle { names, closing }, Err(err)) => {
                let msg = err.to_string();
                assert!(msg.contains("`#include` cycle"), "{name}: {msg}");
                for n in *names {
                    assert!(msg.contains(n), "{name}: {msg} names {n}");
                }
                if let Some(file) = closing {
                    let closing_file = dir.join(file);
                    assert_eq!(err.source_name(), closing_file.to_str(), "{name}");
                    let text = files.iter().find(|(p, _)| p == file).unwrap().1;
                    assert_eq!(err.source_text(), Some(text), "{name}");
                }
            }
            (_, other) => panic!("{name}: {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}
