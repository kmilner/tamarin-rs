// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

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

#[test]
fn diff_theory_checks_each_lemma_namespace() {
    let formula = "\"All #i. A() @ i ==> A() @ i\"";
    for body in [
        format!("lemma L [left]: {formula} lemma L [left]: {formula}"),
        format!("lemma L [right]: {formula} lemma L: {formula}"),
        "diffLemma D: by sorry diffLemma D: by sorry".to_string(),
    ] {
        let src = format!("theory D begin {body} end");
        assert!(
            parse_diff_theory(&src, &[]).is_err(),
            "accepted duplicate namespace: {body}"
        );
    }
    let src = format!("theory D begin lemma L [left]: {formula} lemma L [right]: {formula} end");
    parse_diff_theory(&src, &[]).expect("the two side-specific stores are independent");
}
use tamarin_term::maude_sig::pair_maude_sig;

/// [`parse_formula_str`] against the signature HS `parseString` installs
/// (`pairMaudeSig`, Theory/Text/Parser/Token.hs:250-258).
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
fn structured_expected_notes_include_the_token_and_deduplicate() {
    let error = ParseError::at(
        crate::lexer::Pos {
            offset: 0,
            line: 1,
            col: 1,
        },
        vec![
            Message::SysUnExpect("\"{\"".into()),
            Message::Expect("term".into()),
            Message::Expect("term".into()),
        ],
    )
    .with_context(ParseContext::Term);

    assert_eq!(
        error.diagnostic_notes(),
        ["expected term; found \"{\"".to_string()]
    );
}

#[test]
fn custom_context_does_not_allocate_structured_storage() {
    let error = ParseError::at(
        crate::lexer::Pos {
            offset: 0,
            line: 1,
            col: 1,
        },
        vec![Message::Message("custom".into())],
    )
    .with_context(ParseContext::Term);

    assert!(error.diagnostic.is_none());
}

#[test]
fn non_binary_ac_declaration_is_a_parse_error() {
    for tail in ["rule R: [] --> []", ", g/1", ""] {
        let source = format!("theory T begin functions: f/3 [AC]{tail} end");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::NonBinaryAcFunction { name, arity: 3 } if name == "f")
        );
        assert_eq!(&source[error.span()], "f");
    }
    parse_theory("theory T begin functions: f/2 [AC] end", &[]).unwrap();
}

#[test]
fn builtin_reserved_name_check_precedes_the_arity_and_ac_checks() {
    for (body, name, details) in [
        (
            "builtins: hashing functions: h/3 [AC]",
            "h",
            "arity 3 requested, previously 1",
        ),
        (
            "builtins: hashing functions: h/1, h/3 [AC]",
            "h",
            "arity 3 requested, previously 1",
        ),
        (
            "builtins: dest-pairing functions: fst/1 [AC]",
            "fst",
            "destructor removed",
        ),
        (
            "builtins: asymmetric-encryption functions: pk/2",
            "pk",
            "arity 2 requested, previously 1",
        ),
        (
            "builtins: dest-symmetric-encryption functions: sdec/2",
            "sdec",
            "destructor removed",
        ),
        (
            "builtins: locations-report functions: rep/2",
            "rep",
            "private removed",
        ),
    ] {
        let error = function_conflict(body, name);
        assert!(
            error
                .diagnostic_notes()
                .iter()
                .any(|note| note.contains(details)),
            "{body}: {error:?}"
        );
    }
    for attribute in ["private", "destructor", "NDC", "NDC-diff"] {
        let error = function_conflict(
            &format!("builtins: hashing functions: h/1 [{attribute}]"),
            "h",
        );
        assert!(error
            .diagnostic_notes()
            .iter()
            .any(|note| note.contains(&format!("{attribute} added"))));
    }
}

#[test]
fn conflicting_declarations_fail_with_or_without_attributes() {
    for decl in ["h/1, h/2", "h/3 []"] {
        function_conflict(&format!("builtins: hashing functions: {decl}"), "h");
    }
}

fn function_conflict(body: &str, name: &str) -> ParseError {
    let source = format!("theory T begin {body} end");
    let error = parse_theory(&source, &[]).unwrap_err();
    assert!(
        matches!(error.kind(), ParseErrorKind::ConflictingDeclaration { name: n, context: ParseContext::FunctionDeclaration } if n == name),
        "{source}: {error:?}"
    );
    let start = source.rfind(&format!("{name}/")).unwrap();
    assert_eq!(error.span(), start..start + name.len());
    error
}

#[test]
fn conflicting_arities_is_a_parse_error() {
    for (body, name, reason) in [
        (
            "functions: f/1, f/3",
            "f",
            "arity 3 requested, previously 1",
        ),
        (
            "builtins: reliable-channel functions: h/1, h/2",
            "h",
            "arity 2 requested, previously 1",
        ),
        (
            "macros: mh(x, y) = x functions: mh/2",
            "mh",
            "private removed, destructor removed",
        ),
    ] {
        let error = function_conflict(body, name);
        assert!(
            error
                .diagnostic_notes()
                .iter()
                .any(|note| note.contains(reason)),
            "{error}"
        );
    }
}

/// HS `extendSig`'s own two checks
/// (Theory/Text/Parser/Signature.hs:107-119), raised at the
/// position the builtin's `symbol` lexeme reached.
#[test]
fn builtins_item_rejects_conflicting_functions_and_macros() {
    for (body, builtin, cause) in [
        (
            "functions: h/2 builtins: hashing",
            "hashing",
            "function `h`",
        ),
        ("macros: h(x) = x builtins: hashing", "hashing", "macro `h`"),
        (
            "builtins: symmetric-encryption, dest-symmetric-encryption functions: sdec/2",
            "dest-symmetric-encryption",
            "function `sdec`",
        ),
        (
            "builtins: symmetric-encryption, dest-symmetric-encryption",
            "dest-symmetric-encryption",
            "function `sdec`",
        ),
        (
            "builtins: signing, dest-signing",
            "dest-signing",
            "function `verify`",
        ),
    ] {
        let error = parse_theory(&format!("theory T begin {body} end"), &[]).unwrap_err();
        let message = error.diagnostic_message();
        let notes = error.diagnostic_notes().join("; ");
        let details = format!("{message}; {notes}");
        assert!(
            details.contains(builtin) && details.contains(cause),
            "{body}: {details}"
        );
    }
    parse_theory("theory T begin builtins: dest-pairing end", &[]).unwrap();
}

/// The declarations HS accepts around the same two checks — a
/// re-declaration at the builtin's own shape, the `fst`/`snd` exemption of
/// check (2), a duplicate, and the builtins whose `MaudeSig` only flips an
/// enable flag and so reserve no names at all.
#[test]
fn matching_and_exempt_function_declarations_are_accepted() {
    for body in [
        "builtins: hashing\nfunctions: h/1",
        "builtins: hashing\nfunctions: h/1, h/1",
        "functions: fst/1 [destructor]",
        "builtins: dest-pairing\nfunctions: fst/1 [destructor]",
        "builtins: diffie-hellman\nfunctions: exp/3",
        "builtins: multiset\nfunctions: union/3",
        "builtins: natural-numbers\nfunctions: tplus/3",
        // Two builtins sharing `pk`/`true` at the same shape merge cleanly.
        "builtins: signing, revealing-signing\nfunctions: pk/1",
    ] {
        assert!(
            parse_theory(&format!("theory P begin\n\n{body}\n\nend\n"), &[]).is_ok(),
            "should parse: {body}"
        );
    }
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
fn misspelled_theory_keyword_reports_the_expected_construct() {
    let error = parse_theory("theary Foo\nbegin\nend\n", &[]).unwrap_err();
    assert_eq!(error.span().start, 0);
    assert!(error
        .diagnostic_notes()
        .iter()
        .any(|note| note.contains("theory")));
}

#[test]
fn unknown_item_points_at_its_name() {
    let source = "theory T begin rul R: [] --> [] end";
    let error = parse_theory(source, &[]).unwrap_err();
    assert!(matches!(error.kind(), ParseErrorKind::UnknownItem { item, .. } if item == "rul"));
    assert_eq!(&source[error.span()], "rul");
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
    let s = "/* outer */ theory T // line\n begin /* x /* y */ z */ end";
    let t = parse_theory(s, &[]).unwrap();
    assert_eq!(t.name, "T");
    // `/* */` and `//` are whitespace, not theory items.  Only the
    // `name{* … *}` formal comment becomes a theory item.
    assert!(t.items.is_empty(), "unexpected items: {:?}", t.items);
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

#[test]
fn formula_string() {
    let f = parse_formula_str_sig("All x. P(x) ==> Q(x)").unwrap();
    match f {
        Formula::Forall(_, _) => {}
        _ => panic!("expected Forall"),
    }
}

// HS `blatom` (Theory/Text/Parser/Formula.hs:45-57) tries the term-relational
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

#[test]
fn relational_application_errors_outweigh_predicate_prefixes() {
    let source = "theory T begin\nlemma L: \"Foo(x) = y\"\nend\n";
    let error = parse_theory(source, &[]).expect_err("a relation requires a declared function");
    assert!(
        matches!(
            error.kind(),
            ParseErrorKind::UndeclaredFunction { name } if name == "Foo"
        ),
        "{error:?}"
    );
    assert_eq!(&source[error.span()], "Foo");
}

// HS `typep` (Token.hs:471-473) maps only the literal `Any` to the default
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

// HS `factAnnotation` (Theory/Text/Parser/Fact.hs:31-36, see line 33) maps
// `opUnion` to SolveFirst, `opMinus` to SolveLast and `no_precomp` to
// NoSources.  HS also defines `opUnion = symbol_ "++" <|> symbol_ "+"`
// (Token.hs:551-552).  So the parser accepts `[++]` like `[+]`.
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

// ---- `read_until_next_top_level`: where a raw capture ends ----------------

/// The raw text that `read_until_next_top_level` captured for the proof
/// skeleton of the theory.  This function also asserts that the theory holds
/// exactly one lemma.  A capture that stops early leaves the rest of the
/// text, and the parser then reads that rest as more theory items.  So the
/// lemma count is part of every check below.
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
fn malformed_stored_proof_fails_theory_parse() {
    let src = "theory T begin\nlemma L: \"T\"\nsimplify\nend";
    let err = parse_theory(src, &[]).expect_err("a bare intermediate method needs a child");
    assert_eq!((err.pos.line, err.pos.col), (4, 1));

    let src = "theory T begin\nlemma L: \"T\"\nby sorry trailing\nend";
    let err = parse_theory(src, &[]).expect_err("trailing proof text must not be discarded");
    assert!(err.to_string().contains("unexpected trailing proof text"));
}

#[test]
fn stored_proof_stops_before_top_level_process_definition() {
    let source = r#"theory T begin
lemma L: "T"
by sorry
let P = 0
process: P
end"#;
    parse_theory(source, &[]).expect("top-level let after a proof must remain a theory item");
}

#[test]
fn stored_proof_ignores_structure_inside_public_literals() {
    let source = r#"theory T begin
lemma L: "T"
by solve( Foo('a)) rule') @ #i )
end"#;
    let theory = parse_theory(source, &[]).expect("literal punctuation cannot truncate a proof");
    assert!(lemma_proof_raw(&theory).contains("'a)) rule'"));
}

#[test]
fn stored_proof_treats_backslashes_as_public_literal_data() {
    let source = r#"theory T begin
lemma L: "T"
by solve( Foo('a\') @ #i )
end"#;
    let theory = parse_theory(source, &[]).expect("backslash does not escape a public quote");
    assert!(lemma_proof_raw(&theory).contains("'a\\'"));
}

#[test]
fn parser_messages_are_bounded_after_construction() {
    let declarations = (0..200)
        .map(|index| format!("f{index}/2 [AC]"))
        .collect::<Vec<_>>()
        .join(", ");
    let source =
        format!("theory T begin\nfunctions: {declarations}\nmacros: m(x) = x, m(y) = y\nend");
    let error = parse_theory(&source, &[]).expect_err("the second macro conflicts");
    assert!(error.messages.len() <= MAX_DIAGNOSTIC_MESSAGES);
    assert!(!error.messages_truncated);
    assert!(!error
        .diagnostic_notes()
        .iter()
        .any(|note| note == "additional parser messages omitted"));
    let rendered = error.to_string();
    assert!(
        !rendered.contains("additional parser messages omitted"),
        "{rendered}"
    );
    assert!(
        rendered.contains("Conflicting macro")
            && rendered.contains("`m` was already declared incompatibly"),
        "{rendered}"
    );
}

#[test]
fn short_parser_messages_reuse_their_allocations() {
    let text = String::from("short expectation");
    let text_allocation = text.as_ptr();
    let messages = vec![Message::Expect(text)];
    let messages_allocation = messages.as_ptr();

    let error = ParseError::at(Pos::ZERO, messages);

    assert_eq!(error.messages.as_ptr(), messages_allocation);
    let Message::Expect(text) = &error.messages[0] else {
        panic!("expected the original expectation");
    };
    assert_eq!(text.as_ptr(), text_allocation);
}

#[test]
fn item_errors_do_not_collect_unrelated_operator_names() {
    let declarations = (0..200)
        .map(|index| format!("f{index}/2 [AC]"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!("theory T begin\nfunctions: {declarations}\nequations: x = y\n@\nend");

    let error = parse_theory(&source, &[]).expect_err("junk at item position must fail");

    assert!(error.messages.len() <= MAX_DIAGNOSTIC_MESSAGES);
    assert!(!error.messages_truncated);
    assert!(
        !error
            .to_string()
            .contains("additional parser messages omitted"),
        "{error}"
    );
}

#[test]
fn message_overflow_keeps_a_late_cause_and_records_the_omission() {
    let mut messages = (0..MAX_DIAGNOSTIC_MESSAGES)
        .map(|index| Message::Expect(format!("alternative {index}")))
        .collect::<Vec<_>>();
    let mut truncated = false;

    push_bounded_message(
        &mut messages,
        &mut truncated,
        Message::Message("specific cause".to_string()),
    );

    assert_eq!(messages.len(), MAX_DIAGNOSTIC_MESSAGES);
    assert!(truncated);
    assert!(messages
        .iter()
        .any(|message| matches!(message, Message::Message(text) if text == "specific cause")));
}

#[test]
fn message_overflow_is_recorded_without_expectations_to_displace() {
    let mut messages = (0..MAX_DIAGNOSTIC_MESSAGES)
        .map(|index| Message::Message(format!("cause {index}")))
        .collect::<Vec<_>>();
    let mut truncated = false;

    push_bounded_message(
        &mut messages,
        &mut truncated,
        Message::Message("latest cause".to_string()),
    );

    assert_eq!(messages.len(), MAX_DIAGNOSTIC_MESSAGES);
    assert!(truncated);
    assert!(messages
        .iter()
        .any(|message| matches!(message, Message::Message(text) if text == "latest cause")));
}

/// Reports whether the parser split a top-level `test` CaseTest item out of
/// the theory.  That is the symptom of a capture that stopped at a `test`
/// token inside a proof body.
fn has_casetest(thy: &Theory) -> bool {
    thy.items
        .iter()
        .any(|it| matches!(it, TheoryItem::CaseTest(_)))
}

// Regression: `test` is a genuine top-level theory-item keyword (HS
// `caseTest = CaseTest <$> (symbol "test" *> identifier)`,
// Theory/Text/Parser/Accountability.hs:25-27, see line 26, dispatched in `addItems`,
// Theory/Text/Parser.hs:230-393, see line 268) but is ALSO an ordinary message variable
// name inside proof goals — e.g. `solve( Match( test, sid ) @ #i4 )` in
// examples/ake/bilinear/Scott.spthy.  HS parses the proof skeleton
// STRUCTURALLY (`solve <$> parens goal`, Theory/Text/Parser/Proof.hs:76-85,
// see line 80), so a `test` inside
// `solve( ... )` is a `parens`-nested term and can never begin a new
// top-level item.  `read_until_next_top_level` reproduces that boundary
// rule by only testing the top-level-keyword set at paren-depth 0; without
// it the capture truncates at `test` and the following parse blows up with
// `expected identifier`.
#[test]
fn proof_skeleton_not_truncated_by_keyword_fact_arg() {
    let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Match( test, sid ) @ #i4 )
    case c
    by sorry
  qed
end"#;
    let t = parse_theory(s, &[]).expect("keyword-named goal arg must parse");
    assert!(
        !has_casetest(&t),
        "no CaseTest may be split out of the body"
    );
    let raw = lemma_proof_raw(&t);
    assert!(
        raw.contains("Match( test, sid )"),
        "proof raw truncated at/before `test`: {raw:?}"
    );
    assert!(raw.contains("qed"), "proof raw missing `qed`: {raw:?}");
}

// The paren-depth guard must cover fresh `~k`, public `$A`, and indexed
// message arguments alongside a bare identifier that collides with a
// top-level keyword. None may truncate the capture while inside the goal.
#[test]
fn proof_skeleton_captures_mixed_sorted_indexed_and_keyword_args() {
    let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Foo( ~k, $A, k.1, test, sid ) @ #i1 )
    case c
    by sorry
  qed
end"#;
    let t = parse_theory(s, &[]).expect("mixed-arg goal must parse");
    assert!(!has_casetest(&t));
    let raw = lemma_proof_raw(&t);
    assert!(
        raw.contains("Foo( ~k, $A, k.1, test, sid )"),
        "mixed-arg goal truncated: {raw:?}"
    );
    assert!(raw.contains("qed"), "missing qed: {raw:?}");
}

// Dual check: the depth-0 boundary must still fire.  A genuine top-level
// `test` CaseTest item following a proof (whose body also contains a `test`
// goal argument) must be recognized as a CaseTest, and the proof must not
// absorb it.
#[test]
fn real_casetest_after_proof_still_recognized() {
    let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Foo( test, sid ) @ #i1 )
    case c
    by sorry
  qed
  test Reachable:
    "Ex #i. Bar() @ #i"
end"#;
    let t = parse_theory(s, &[]).expect("proof followed by CaseTest must parse");
    let raw = lemma_proof_raw(&t);
    assert!(
        raw.contains("Foo( test, sid )") && raw.contains("qed"),
        "proof body truncated: {raw:?}"
    );
    let ct = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::CaseTest(c) => Some(c),
            _ => None,
        })
        .expect("top-level `test` CaseTest must be recognized after the proof");
    assert_eq!(ct.name, "Reachable");
}

// Regression (companion to the depth guard): tactic filter regexes carry
// ESCAPED, UNBALANCED parens inside a double-quoted string literal —
// e.g. `regex "cp\("` and `regex "In_A\( 'S', <'codes'"` in
// examples/csf18-alethea/....  Those `(`s are opaque regex text (HS lexes
// the whole thing as `stringLiteral`, Token.hs:366-367); counting them as
// grouping would keep `depth` permanently positive so the tactic capture
// swallows every following item.  The scanner must treat double-quoted
// string interiors as opaque.
#[test]
fn tactic_regex_with_unbalanced_paren_does_not_swallow_next_item() {
    let s = r#"theory T begin
  tactic: myTac
  presort: C
  prio:
    regex "In_A\( 'S', <'codes'"
  prio:
    regex "cp\("
  rule R: [ Fr(~k) ] --[ Created(~k) ]-> [ Out(~k) ]
end"#;
    let t = parse_theory(s, &[]).expect("tactic with unbalanced regex parens must parse");
    let tac = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Tactic(t) => Some(t),
            _ => None,
        })
        .expect("tactic present");
    assert_eq!(tac.prios.len(), 2);
    let SelectorExpr::Leaf(second) = &tac.prios[1].selectors[0] else {
        panic!("expected regex selector")
    };
    assert_eq!(second.name, "regex");
    assert_eq!(second.params, [r#"cp\("#]);
    // The `(` inside the regex string must not consume the following rule.
    let rule = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("rule R must remain a separate top-level item");
    assert_eq!(rule.name, "R");
}

#[test]
fn tactic_blocks_require_a_selector_without_consuming_the_next_token() {
    for (block, tail) in [
        ("prio:", "rule R: [] --> [] end"),
        ("deprio: {id}", "rule R: [] --> [] end"),
        ("prio:", "foo"),
        ("prio:", "deprio:"),
        ("prio:", ""),
    ] {
        let prefix = format!("theory T begin\ntactic: rank\n{block}\n");
        let source = format!("{prefix}{tail}");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert_eq!(error.span().start, prefix.len(), "{source}: {error:?}");
        assert!(
            error
                .diagnostic_notes()
                .iter()
                .any(|note| note.contains("tactic selector with a quoted argument")),
            "{error:?}"
        );
    }
}

#[test]
fn tactic_presort_requires_one_known_non_oracle_ranking() {
    for presort in ["sx", "z", "o"] {
        let src = format!("theory T begin\ntactic: rank\npresort: {presort}\nend");
        let err = parse_theory(&src, &[]).expect_err("invalid presort must fail");
        assert!(err.to_string().contains("unknown proof method ranking"));
    }
    for presort in ["s", "S", "p", "P", "c", "C", "i", "I"] {
        let src = format!("theory T begin\ntactic: rank\npresort: {presort}\nend");
        parse_theory(&src, &[]).unwrap_or_else(|e| panic!("valid presort {presort}: {e}"));
    }
}

// Regression: a proof CASE LABEL that collides with a top-level keyword must
// not truncate the capture.  HS parses `oneCase = symbol "case" *> identifier`
// (Theory/Text/Parser/Proof.hs:98-115, see line 115) structurally, so the identifier after
// `case` is the case NAME and can be any top-level keyword — case names come
// from rule / source-case names, and `test` is the CaseTest keyword
// (Theory/Text/Parser/Accountability.hs:25-27, see line 26).  A rule named
// `test` prints its solved case as
// `case test` at paren-depth 0 (unlike Scott's `test` which was inside
// `solve( ... )`), so the paren-depth guard alone does not suppress it —
// the case-label suppression below is also needed.
#[test]
fn proof_case_label_named_after_keyword_does_not_truncate() {
    let s = r#"theory T begin
  lemma l:
    exists-trace "Ex x #i. Done(x) @ #i"
  simplify
  solve( A( x ) ▶₀ #i )
    case test
    SOLVED // trace found
  qed
end"#;
    let t = parse_theory(s, &[]).expect("`case test` must not truncate the proof");
    // The bare `test` case label must NOT be split off as a CaseTest item.
    assert!(
        !has_casetest(&t),
        "case label `test` must not become a top-level CaseTest"
    );
    let raw = lemma_proof_raw(&t);
    assert!(
        raw.contains("case test"),
        "proof raw truncated at/before `case test`: {raw:?}"
    );
    assert!(
        raw.contains("SOLVED") && raw.contains("qed"),
        "proof raw missing SOLVED/qed: {raw:?}"
    );
}

// The suppression must fire per `case` keyword — several cases in a row, each
// labelled after a different top-level keyword (`rule`, `lemma`, `function`),
// separated by `next`.  None may truncate the capture, and none may be split
// off as its own top-level item.
#[test]
fn multiple_case_labels_named_after_keywords_do_not_truncate() {
    let s = r#"theory T begin
  lemma l:
    all-traces "All x #i. Done(x) @ #i ==> F"
  simplify
  solve( A( x ) ▶₀ #i )
    case rule
      by sorry
    next
    case lemma
      by sorry
    next
    case function
      by sorry
  qed
end"#;
    let t = parse_theory(s, &[]).expect("keyword-named case labels must not truncate");
    // The parser splits no Rule or Functions items out of the body.
    // `lemma_proof_raw` checks the lemma count.
    assert!(
        !t.items.iter().any(|it| matches!(it, TheoryItem::Rule(_))),
        "a `case rule` label must not be split into a top-level rule"
    );
    assert!(
        !t.items
            .iter()
            .any(|it| matches!(it, TheoryItem::Functions(_))),
        "a `case function` label must not be split into a top-level functions decl"
    );
    let raw = lemma_proof_raw(&t);
    for label in ["case rule", "case lemma", "case function"] {
        assert!(raw.contains(label), "proof raw missing {label:?}: {raw:?}");
    }
    assert!(raw.contains("qed"), "proof raw missing qed: {raw:?}");
}

// Dual check: the depth-0 boundary must still fire for a REAL top-level
// keyword that is NOT a case label.  A genuine `test` CaseTest item following
// a proof whose body contains a `case test` label must still be recognized:
// the case-label suppression is armed only by the preceding `case` keyword and
// is cleared after one token, so the later bare `test` still terminates the
// capture.
#[test]
fn keyword_after_proof_still_terminates_capture() {
    let s = r#"theory T begin
  lemma l:
    exists-trace "Ex x #i. Done(x) @ #i"
  simplify
  solve( A( x ) ▶₀ #i )
    case test
    SOLVED
  qed
  rule two:
    [ A(x) ] --[ Done(x) ]-> [ ]
end"#;
    let t = parse_theory(s, &[]).expect("proof followed by a real rule must parse");
    let raw = lemma_proof_raw(&t);
    assert!(
        raw.contains("case test") && raw.contains("qed"),
        "proof body truncated: {raw:?}"
    );
    assert!(
        !raw.contains("rule two"),
        "the following rule leaked into the proof capture: {raw:?}"
    );
    let rule = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("the top-level `rule two` must remain a separate item");
    assert_eq!(rule.name, "two");
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

// HS `functionAttribute` (Theory/Text/Parser/Signature.hs:164-171) accepts
// `AC`, `NDC-diff` and `NDC`; `function`
// (Theory/Text/Parser/Signature.hs:183-225) folds them into the symbol's AC
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

// HS `acterm` (Theory/Text/Parser/Term.hs:165-172): a binary `[AC]` symbol is
// also an infix,
// left-associative operator — the notation `prettyTerm` emits for such
// terms.  The AST records the infix spelling as `BinOp::AcFct`, distinct
// from the prefix `App`, because a name that is also a `NoEq` symbol of
// the signature resolves NoEq when written prefix (`lookupArity`,
// Theory/Text/Parser/Term.hs:62-72) but stays the AC symbol when written
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
#[test]
fn ac_infix_requires_a_preceding_declaration() {
    let src = "theory T begin equations: x add y = z end";
    assert!(parse_theory(src, &[]).is_err(), "`add` is not infix here");
}

// A `:` after a variable means different things inside and outside a SAPIC
// process.  Rules/formulas use `msgvar`/`lvar` = `sortedLVar`, whose
// `mkSuffixParser` reads `x:nat` as the NAT-SORTED `x` (Token.hs:407-432);
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
}

// =============================================================================
// The sort the parser stamps on every variable
// =============================================================================

/// The first argument of the first premise of the theory's single rule.
fn rule_premise_term(src: &str) -> Term {
    let thy = parse_theory(src, &[]).expect("parses");
    for item in &thy.items {
        if let TheoryItem::Rule(r) = item {
            return r.premises[0].args[0].clone();
        }
    }
    panic!("no rule in {src}");
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

/// A sigil names the sort and a bare identifier is message-sorted, as HS
/// `sortedLVar`'s prefix arms do — the bare `LSortMsg -> pure ()` case
/// (Token.hs:409-433, see lines 424-426).
#[test]
fn bare_variable_is_msg_sorted() {
    let t = rule_premise_term(
        "theory T begin builtins: natural-numbers \
         rule R: [ In(<x, x.1, ~f, $p, #i, %n>) ] --[ ]-> [ ] end",
    );
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

/// HS `sortedLVar`'s suffix arm returns `LVar n s i` with `s` the suffix's
/// sort, the same plain `LVar` the sigil arms build (Token.hs:409-421), so
/// `x:fresh` and `~x` are one variable.
#[test]
fn sort_suffix_parses_to_the_plain_sort() {
    let t = rule_premise_term(
        "theory T begin builtins: natural-numbers \
         rule R: [ In(<x:msg, x:fresh, x:pub, x:node, x:nat>) ] --[ ]-> [ ] end",
    );
    assert_eq!(
        tuple_var_specs(&t),
        vec![
            ("x", 0, LSort::Msg),
            ("x", 0, LSort::Fresh),
            ("x", 0, LSort::Pub),
            ("x", 0, LSort::Node),
            ("x", 0, LSort::Nat),
        ]
    );
}

/// `blatom`'s timepoint operands are read with `nodevar`, which stamps
/// `LSortNode` on a bare identifier (Theory/Text/Parser/Formula.hs:44-59,
/// Token.hs:443-448): the argument of `last`, the operand after `@`, both
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

    for invalid in [
        "$i < $j",
        "x:msg < j",
        "f(i) < j",
        "$i = #j",
        "f(i) = #j",
        "k = #l",
    ] {
        assert!(
            parse_formula_str_sig(invalid).is_err(),
            "accepted non-node operands in {invalid}"
        );
    }
}

/// `nodevar` reads a bare name with `indexedIdentifier` (Token.hs:445-447),
/// which does not consult the signature, so a name declared as an arity-0
/// symbol is still a timepoint variable in a timepoint position — unlike the
/// term parser, where `nullaryApp` claims it
/// (Theory/Text/Parser/Term.hs:158-163).
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
/// (Theory/Text/Parser/Formula.hs:73-76), and an operand of an AC operator is
/// a message term, so the `dif` binder and the `seq1` operand of
/// examples/sapic/fast/SCADA/opc_ua_secure_conversation.spthy's
/// `A_Counter_Increases` restriction are both message-sorted.  Both feed
/// `Ord LVar`, which compares the sort second (LTerm.hs:546-548), so the
/// printed operand order of `seq1 + dif` follows from them.
#[test]
fn bare_binder_and_bare_message_operand_are_msg_sorted() {
    // That theory declares `builtins: multiset`, which is what opens the `+`
    // level of `msetterm` (Theory/Text/Parser/Term.hs:195-200).
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

/// HS `nullaryApp` (Theory/Text/Parser/Term.hs:158-163) claims a bare
/// identifier that is an arity-0 symbol of `funSyms maudeSig ∪ macroNames
/// maudeSig`, so it is an application, not a variable.  A sigil and a use
/// ahead of the declaration leave a variable in HS too. A `.idx`, a `:sort`
/// suffix and a SAPIC `:type` are not part of the identifier, so the nullary
/// parser claims the name and leaves the suffix to be rejected.
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
}

/// `nullaryApp` resolves a complete identifier, so a declared `c/0` cannot
/// claim the prefix of the distinct identifier `cx`.
#[test]
fn nullary_symbol_matches_the_whole_identifier() {
    let concs = rule_conclusions(
        "theory T begin\n\
         functions: c/0\n\
         rule R:\n\
           [ ] --> [ Out(cx) ]\n\
         end",
    );
    assert_eq!(var_of(&concs[0].args[0]).name, "cx");
}

/// Fixed literals also stop at an identifier boundary. Identifiers beginning
/// with `1` or `DH_neutral` therefore remain intact.
#[test]
fn fixed_literals_do_not_claim_identifier_prefixes() {
    for name in ["1abc", "DH_neutralx"] {
        let src = format!("theory T begin\nrule R:\n  [ ] --> [ Out({name}) ]\nend");
        let concs = rule_conclusions(&src);
        assert_eq!(var_of(&concs[0].args[0]).name, name);
    }
}

/// A prefix (or `op{a}b`) application whose head resolves to HS `expSym`
/// builds the same node the `^` operator does, which is what makes
/// `prettyTerm` render it infix (Term/Term.hs:310).  A redeclaration that is
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
// Rule `let` inlining
// =========================================================================
//
// HS applies the `let` substitution to `(ps, as, cs, rs)` inside the rule
// parsers themselves (Theory/Text/Parser/Rule.hs:119, 133, 153), so a parsed
// rule carries no `let`-bound names.  `letBlock` folds the bindings with
// `foldr1 compose` over singletons (Theory/Text/Parser/Let.hs:35) and
// `compose s1 s2` means `s1(s2(t))` (Term/Substitution/SubstVFree.hs:186-191),
// so the bindings apply in reverse source order.

/// The single rule of a one-rule theory.
fn only_rule(src: &str) -> Rule {
    let thy = parse_theory(src, &[]).expect("parses");
    thy.items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .expect("one rule")
}

#[test]
fn let_inlining_substitutes_in_premises() {
    // rule R: let r = ~k in [In(r), Fr(~k)] --[]-> []
    // The In premise holds ~k, not the local `r`.
    let r = only_rule(
        r#"theory T begin
            rule R: let r = ~k in [In(r), Fr(~k)] --[]-> []
        end"#,
    );
    let in_fact = &r.premises[0];
    assert_eq!(in_fact.name, "In");
    match &in_fact.args[0] {
        Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
        other => panic!("expected ~k after subst, got {other:?}"),
    }
}

#[test]
fn let_inlining_is_sequential() {
    // let a = ~k; b = h(a) in [In(b)] --[]-> [] gives In(h(~k)): `b`'s
    // singleton applies first, then `a`'s rewrites the `a` it introduced.
    // `builtins: hashing` declares `h/1` — the parser resolves prefix
    // applications through `lookupArity` and an undeclared head would
    // reparse as a variable and fail (oracle probes p05/p25).
    let r = only_rule(
        r#"theory T begin
            builtins: hashing
            rule R: let a = ~k b = h(a) in [In(b), Fr(~k)] --[]-> []
        end"#,
    );
    match &r.premises[0].args[0] {
        Term::App(name, args) if name == "h" => match &args[0] {
            Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
            other => panic!("expected h(~k), got h({other:?})"),
        },
        other => panic!("expected h(~k), got {other:?}"),
    }
}

#[test]
fn let_inlining_leaves_a_forward_reference_free() {
    // A binding whose right-hand side names a LATER binding keeps that name as
    // a free variable: by the time `a`'s singleton introduces `b` into the
    // body, `b`'s singleton has already been applied.
    //   let a = h(b) b = ~k in [In(a), Fr(~k)]
    // gives In(h(b)) with `b` a free Msg-var, NOT h(~k).
    // `builtins: hashing` declares `h/1` — see `let_inlining_is_sequential`.
    let r = only_rule(
        r#"theory T begin
            builtins: hashing
            rule R: let a = h(b) b = ~k in [In(a), Fr(~k)] --[]-> []
        end"#,
    );
    match &r.premises[0].args[0] {
        Term::App(name, args) if name == "h" => match &args[0] {
            Term::Var(vs) if vs.name == "b" && vs.sort != LSort::Fresh => {}
            other => panic!("expected h(b) with free b, got h({other:?})"),
        },
        other => panic!("expected h(b), got {other:?}"),
    }
}

#[test]
fn let_inlining_substitutes_in_actions_and_conclusions() {
    let r = only_rule(
        r#"theory T begin
            rule R: let r = ~k in [Fr(~k)] --[Use(r)]-> [Out(r)]
        end"#,
    );
    match &r.actions[0].args[0] {
        Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
        other => panic!("expected Use(~k), got Use({other:?})"),
    }
    match &r.conclusions[0].args[0] {
        Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
        other => panic!("expected Out(~k), got Out({other:?})"),
    }
}

/// HS substitutes into `rs0`, the rule's `_restrict` formulas, alongside the
/// three fact rows (Theory/Text/Parser/Rule.hs:119).
#[test]
fn let_inlining_reaches_an_embedded_restriction() {
    let r = only_rule(
        r#"theory T begin
            builtins: hashing
            rule R: let m = h(~k) in [Fr(~k)] --[ _restrict(m = ~k) ]-> []
        end"#,
    );
    match &r.embedded_restrictions[0] {
        Formula::Atom(Atom::Eq(lhs, _)) => match lhs {
            Term::App(name, args) if name == "h" => match &args[0] {
                Term::Var(vs) if vs.name == "k" && vs.sort == LSort::Fresh => {}
                other => panic!("expected h(~k), got h({other:?})"),
            },
            other => panic!("expected h(~k), got {other:?}"),
        },
        other => panic!("expected an equality atom, got {other:?}"),
    }
}

#[test]
fn let_inlining_respects_quantifier_shadowing() {
    let r = only_rule(
        r#"theory T begin
            rule R: let x = 'value' in []
              --[ _restrict(Ex x #i. A(x) @ i) ]-> []
        end"#,
    );
    match &r.embedded_restrictions[0] {
        Formula::Exists(vars, body) => {
            let x = vars.iter().find(|v| v.name == "x").expect("bound x");
            match body.as_ref() {
                Formula::Atom(Atom::Action(fact, _)) => {
                    assert_eq!(fact.args, vec![Term::Var(x.clone())]);
                }
                other => panic!("expected an action atom, got {other:?}"),
            }
        }
        other => panic!("expected an existential, got {other:?}"),
    }
}

#[test]
fn let_inlining_avoids_capture_by_quantifiers() {
    let r = only_rule(
        r#"theory T begin
            rule R: let x = y in []
              --[ _restrict(Ex y #i. A(x,y) @ i) ]-> []
        end"#,
    );
    match &r.embedded_restrictions[0] {
        Formula::Exists(vars, body) => {
            let bound_y = vars.iter().find(|v| v.name == "y").expect("bound y");
            match body.as_ref() {
                Formula::Atom(Atom::Action(fact, _)) => {
                    let [Term::Var(inserted_y), Term::Var(original_y)] = fact.args.as_slice()
                    else {
                        panic!("expected two variable arguments, got {:?}", fact.args);
                    };
                    assert_ne!(inserted_y, bound_y, "replacement y was captured");
                    assert_eq!(original_y, bound_y, "bound occurrence was not renamed");
                }
                other => panic!("expected an action atom, got {other:?}"),
            }
        }
        other => panic!("expected an existential, got {other:?}"),
    }
}

#[test]
fn rule_let_requires_a_binding_and_in_terminator() {
    for src in [
        "theory T begin rule R: let in [] --[]-> [] end",
        "theory T begin rule R: let x = y [] --[]-> [] end",
    ] {
        assert!(parse_theory(src, &[]).is_err(), "unexpectedly parsed {src}");
    }
}

#[test]
fn rule_let_rejects_sorts_outside_msg_and_nat() {
    for binder in ["$x", "~x", "#x"] {
        let src = format!("theory T begin rule R: let {binder} = y in [] --[]-> [] end");
        assert!(
            parse_theory(&src, &[]).is_err(),
            "unexpectedly parsed {src}"
        );
    }
}

/// HS's rule `let` binds a variable — `sortedLVar [LSortMsg, LSortNat]` under
/// `genericletBlock` (Theory/Text/Parser/Let.hs:24-31) — while the rule body
/// reads a declared arity-0 symbol as `nullaryApp`'s constant
/// (Theory/Text/Parser/Term.hs:158-163).  A binding whose name is such a
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
fn invalid_term_reports_its_expectation_and_token() {
    let source = "theory T begin rule R: [A(☃)] --> [] end";
    let error = parse_theory(source, &[]).unwrap_err();
    assert_eq!(
        &source[error.diagnostic_labels_with_source(source)[0].span.clone()],
        "☃"
    );
    assert!(
        error
            .diagnostic_notes()
            .iter()
            .any(|note| note.contains("expected term") && note.contains("found")),
        "{error}"
    );
}

#[test]
fn oversized_diagnostics_release_large_allocations() {
    let huge = "a".repeat(100_000);
    let mut owned = huge.clone();
    crate::parse_error::bound_owned_text(&mut owned, 80);
    assert_eq!(owned.chars().count(), 81);
    assert!(owned.capacity() < 1024);

    let source = format!("theory T begin rule R[color={huge}]: [] --> [] end");
    let error = parse_theory(&source, &[]).unwrap_err();
    assert!(matches!(
        error.kind(),
        ParseErrorKind::MalformedHexColor { .. }
    ));
    assert_eq!(error.span().len(), huge.len());
    assert!(error.messages.is_empty());
    assert!(error.diagnostic_notes()[0].contains("100000"));

    let source = format!("theory T begin rule R: [{huge}()] --> [] end");
    let error = parse_theory(&source, &[]).unwrap_err();
    let ParseErrorKind::InvalidFactName { name } = error.kind() else {
        panic!("{error}");
    };
    assert!(name.capacity() < 1024);
    assert_eq!(error.span().len(), huge.len());
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
fn missing_theory_end_is_independent_of_previous_item() {
    for body in [
        "rule R: [] --> []",
        "builtins: hashing",
        "functions: f/2,g/1",
        "functions: f/2,g/2 [AC]",
    ] {
        let source = format!("theory T begin {body}");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert_eq!(error.span().start, source.len());
        assert!(
            error.diagnostic_notes().iter().any(|n| n.contains("end")),
            "{error:?}"
        );
    }
}

#[test]
fn diff_validation_preserves_priority_and_source_spans() {
    for args in ["(~a*~b), ~a", "diff(~a, ~b), ~b"] {
        let source = diff_probe(args);
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(matches!(
            error.kind(),
            ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::DiffModeDisabled)
        ));
        let start = if args.starts_with("diff") {
            source.rfind("diff(").unwrap()
        } else {
            source.find("diff(").unwrap()
        };
        assert_eq!(error.span(), start..start + 4);
    }
    for args in ["~a", "~a, ~b, ~a", "", "~a,"] {
        for flags in [&[][..], &["diff"][..]] {
            let error = parse_theory(&diff_probe(args), flags).unwrap_err();
            assert!(
                matches!(
                    error.kind(),
                    ParseErrorKind::WrongFunctionArity { declared: 2, .. }
                ),
                "{args}: {error:?}"
            );
        }
    }
    for flags in [&[][..], &["diff"][..]] {
        for (args, wrong_arity) in [("x, x", false), ("x", true)] {
            let source = format!("theory D begin equations: diff({args}) = x end");
            let error = parse_theory(&source, flags).unwrap_err();
            if wrong_arity {
                assert!(matches!(
                    error.kind(),
                    ParseErrorKind::WrongFunctionArity { .. }
                ));
            } else {
                assert!(matches!(
                    error.kind(),
                    ParseErrorKind::IllegalDiffOperator(IllegalDiffReason::InEquation)
                ));
            }
            let start = source.find("diff").unwrap();
            assert_eq!(error.span(), start..start + 4);
        }
    }
    parse_theory(&diff_probe("~a, ~b,"), &["diff"]).unwrap();
}

#[test]
fn bare_diff_token_requires_an_argument_list() {
    for (term, unexpected) in [
        ("diff", ")"),
        ("diff{~a}~b", "{"),
        ("diff /* comment */", ")"),
    ] {
        let source = format!("theory D begin rule R: [] --> [Out({term})] end");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(source[error.span().start..].starts_with(unexpected));
        assert!(
            error
                .diagnostic_notes()
                .iter()
                .any(|note| note.contains('(')),
            "{error:?}"
        );
    }
}

#[test]
fn diff_operator_is_accepted_with_the_diff_flag() {
    let thy = parse_theory(&diff_probe("(~a*~b), ~a"), &["diff"]).expect("diff flag enables it");
    let mut seen = false;
    for item in &thy.items {
        if let TheoryItem::Rule(r) = item {
            for f in &r.conclusions {
                for t in &f.args {
                    if matches!(t, Term::Diff(_, _)) {
                        seen = true;
                    }
                }
            }
        }
    }
    assert!(seen, "expected a Term::Diff in the rule conclusion");

    // The word boundary keeps `diffuse(...)` an ordinary function application
    // even without the flag (HS routes it through `naryOpApp`).
    assert!(parse_theory(
        "theory D\nbegin\n\nfunctions: diffuse/2\n\nrule RA:\n  \
             [ Fr(~a), Fr(~b) ] --> [ Out( diffuse(~a, ~b) ) ]\n\nend\n",
        &[]
    )
    .is_ok());
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
fn repeated_failures_do_not_exhaust_the_message_budget() {
    let formula = format!("{}☃{}", "(".repeat(40), ")".repeat(40));
    let source = format!("theory T begin lemma L: \"{formula}\" end");
    let error = parse_theory(&source, &[]).unwrap_err();
    assert!(!error.messages_truncated, "{error}");
    assert_eq!(error.diagnostic_notes(), ["expected term; found '☃'"]);
}

#[test]
fn diagnostic_messages_are_deduplicated_after_bounding() {
    for count in [3, MAX_DIAGNOSTIC_MESSAGES + 10] {
        let messages = (0..count)
            .map(|i| Message::Expect(format!("{}{i}", "x".repeat(MAX_DIAGNOSTIC_MESSAGE_CHARS))))
            .collect();
        let mut error = ParseError::at(Pos::ZERO, messages);
        error.extend_messages(error.messages.clone());
        assert_eq!(error.messages.len(), 1);
        assert!(!error.messages_truncated);
    }
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
    let parser = Parser::new("\0", &[], false);
    assert_eq!(parser.unexpected_token(), "'\\0'");
}

#[test]
fn conflict_progress_includes_trailing_comments() {
    for body in [
        "functions: f/1, f/2",
        "functions: f/1, f/1 [private]",
        "functions: h/2 builtins: hashing",
        "macros: h(x) = x builtins: hashing",
        "macros: m(x) = x, m(y) = y",
        "rule R: [] --> [] rule R: [] --> [A()]",
    ] {
        let source = format!("theory T begin {body} /* trailing */ end");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert_eq!(
            error.pos.offset,
            source.rfind("end").unwrap(),
            "{body}: {error:?}"
        );
        let source = format!("theory T begin {body} /* unclosed");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::UnclosedBlockComment { .. }),
            "{body}: {error:?}"
        );
    }
}

fn diff_probe(args: &str) -> String {
    format!(
        "theory D\nbegin\n\nbuiltins: diffie-hellman\n\nrule RA:\n  \
             [ Fr(~a), Fr(~b) ] --[ Go( 'a' ) ]-> [ Out( diff({args}) ) ]\n\nend\n"
    )
}
