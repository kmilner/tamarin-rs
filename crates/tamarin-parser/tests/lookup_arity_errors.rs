// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, BTom-GH, charlie-j, jdreier, meiersi, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Text/Parser/Formula.hs,
//   lib/theory/src/Theory/Text/Parser/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Parse errors of `lookupArity`-driven prefix-application resolution
//! (Theory/Text/Parser/Term.hs:62-105) and the term-path expectations its
//! backtrack leaves behind.
//!
//! HS resolves every prefix application through `lookupArity` over the
//! signature built SO FAR and parses the arity the lookup returns; on any
//! failure — unknown operator, arity mismatch, malformed argument list — the
//! try-wrapped application backtracks and the name reparses as a variable,
//! so the NEXT token breaks the enclosing grammar.  The reported error is
//! that consumed failure, merged with the variable's `letter or digit`/`"."`
//! identifier hangovers and the enabled operator labels.
//!
//! Each case pins the error's position and its `expected` set; both are the
//! ones the pinned Haskell oracle (Git revision ef3f0468) reports for the
//! same bytes (probe files p02–p48 of the lookup-arity probe matrix; sources
//! here are byte-identical to the probes).

use tamarin_parser::{parse_theory, ParseError};

/// Asserts `src` fails with the [`ParseError::Expected`] bridge variant at
/// `line`:`col`, on a token starting with `found`, carrying exactly the
/// `expected` labels.
#[track_caller]
fn assert_expected(src: &str, line: u32, col: u32, found: &str, expected: &[&str]) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    assert!(
        matches!(&e, ParseError::Expected { .. }),
        "expected the `Expected` variant, got {e:?}"
    );
    let at = e.location();
    assert_eq!((at.line, at.col), (line, col), "position of {e:?}");
    let got = e.found().unwrap_or("");
    assert!(
        got.starts_with(found),
        "offending token {got:?} should start with {found:?}"
    );
    let labels = e.expected().unwrap_or_default();
    assert_eq!(
        labels.iter().map(String::as_str).collect::<Vec<_>>(),
        expected
    );
}

/// Arity mismatch in a rule's fact argument: `g/3` applied to two arguments.
/// The application backtracks, `g` reparses as a variable, and `commaSep`'s
/// comma plus `parens`' close are expected at the `(` together with the
/// variable's identifier hangovers.
#[test]
fn arity_mismatch_backtracks_to_variable_frame() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g('a','b')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

/// An UNDECLARED name applied prefix is `lookupArity`'s `fail "unknown
/// operator …"` — same backtrack, same expectations.
#[test]
fn undeclared_application_is_a_parse_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ Out(g('a')) ]\n\nend\n";
    assert_expected(
        src,
        5,
        18,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

/// Use BEFORE declaration: `lookupArity` reads the signature built so far,
/// so a later `functions:` item does not rescue an earlier use.
#[test]
fn use_before_declaration_is_a_parse_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ Out(g('a')) ]\n\nfunctions: g/1\n\nend\n";
    assert_expected(
        src,
        5,
        18,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

/// A nullary symbol applied to arguments fails the arity check; the name is
/// then claimed by `nullaryApp`'s `symbol` (Term.hs:158-163), which leaves NO
/// identifier hangovers — only the fact-argument labels remain.
#[test]
fn nullary_applied_with_args_has_no_identifier_hangover() {
    let src =
        "theory T\nbegin\n\nfunctions: f/0\n\nrule r:\n  [ ] --> [ Out(f('a','b')) ]\n\nend\n";
    assert_expected(src, 7, 18, "(", &["\",\"", "\")\""]);
}

/// `h()` for the unary hashing builtin: the `k == 1` branch parses ONE
/// `tupleterm`, which requires an operand — the empty argument list
/// backtracks the application.
#[test]
fn unary_empty_parens_backtracks() {
    let src = "theory T\nbegin\n\nbuiltins: hashing\n\nrule r:\n  [ ] --> [ Out(h()) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

/// `h('a',)` — the `k == 1` branch's `tupleterm` is `chainr1`, which does
/// NOT admit a trailing comma (unlike `commaSep` for other arities).
#[test]
fn unary_trailing_comma_backtracks() {
    let src =
        "theory T\nbegin\n\nbuiltins: hashing\n\nrule r:\n  [ ] --> [ Out(h('a',)) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

/// A malformed NESTED application (undeclared `k` inside a well-arity `g`)
/// fails the whole outer application: the error sits at the OUTER `(` and
/// the inner failure is discarded, exactly like parsec's `try`.
#[test]
fn nested_failure_reports_at_the_outer_application() {
    let src =
        "theory T\nbegin\n\nfunctions: g/2\n\nrule r:\n  [ ] --> [ Out(g(k('x'),'b')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

/// Whitespace between the name and `(`: the `letter or digit` hangover sits
/// at the name's end and the error position (post-whitespace) has moved past
/// it, so only `"."` survives of the identifier's labels.
#[test]
fn whitespace_before_paren_drops_letter_or_digit() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g ('a','b')) ]\n\nend\n";
    assert_expected(src, 7, 19, "(", &["\".\"", "\",\"", "\")\""]);
}

/// `em` is ALWAYS in `lookupArity`'s list at arity 2 (appended after the
/// macro names, Term.hs:65); under bilinear-pairing a 3-argument use fails
/// the arity check and the DH operator labels (`^`, `*` — BP forces
/// `enableDH`) join the expectations.
#[test]
fn em_wrong_arity_under_bp_shows_dh_operator_labels() {
    let src = "theory T\nbegin\n\nbuiltins: bilinear-pairing\n\nrule r:\n  [ ] --> [ Out(em('a','b','c')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        19,
        "(",
        &[
            "letter or digit",
            "\".\"",
            "\"^\"",
            "\"*\"",
            "\",\"",
            "\")\"",
        ],
    );
}

/// A declared `[AC]` symbol adds its own infix-operator label between the
/// variable hangovers and the fact-argument labels (`acterm`'s per-symbol
/// `chainl1` level, Term.hs:165-172).
#[test]
fn user_ac_symbol_label_joins_the_frame() {
    let src =
        "theory T\nbegin\n\nfunctions: f/2 [AC]\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &["letter or digit", "\".\"", "\"f\"", "\",\"", "\")\""],
    );
}

/// `builtins: xor` opens the `XOR`/`⊕` chain level; both spellings' labels
/// appear (Term.hs:187-192, Token.hs:554-556).
#[test]
fn xor_operator_labels_join_the_frame() {
    let src = "theory T\nbegin\n\nbuiltins: xor\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &[
            "letter or digit",
            "\".\"",
            "\"XOR\"",
            "\"⊕\"",
            "\",\"",
            "\")\"",
        ],
    );
}

/// `builtins: multiset` opens the `++`/`+` union level (Term.hs:195-200,
/// Token.hs:550-552).
#[test]
fn multiset_operator_labels_join_the_frame() {
    let src =
        "theory T\nbegin\n\nbuiltins: multiset\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &[
            "letter or digit",
            "\".\"",
            "\"++\"",
            "\"+\"",
            "\",\"",
            "\")\"",
        ],
    );
}

/// `builtins: natural-numbers` opens the `%+` level (Term.hs:203-208).
#[test]
fn nat_operator_label_joins_the_frame() {
    let src = "theory T\nbegin\n\nbuiltins: natural-numbers\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "(",
        &["letter or digit", "\".\"", "\"%+\"", "\",\"", "\")\""],
    );
}

/// Inside a tuple, the failed application carries the tuple's own close
/// label (`chainr1` comma + `angled`'s `>`).
#[test]
fn tuple_close_labels_join_the_frame() {
    let src = "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(<g('a','b'), 'c'>) ]\n\nend\n";
    assert_expected(
        src,
        7,
        19,
        "(",
        &["letter or digit", "\".\"", "\",\"", "\">\""],
    );
}

/// Inside grouping parens there is no comma alternative — only the close.
#[test]
fn grouping_parens_frame_has_no_comma() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out((g('a','b'))) ]\n\nend\n";
    assert_expected(src, 7, 19, "(", &["letter or digit", "\".\"", "\")\""]);
}

/// `op{t1}t2` (`binaryAlgApp`, Term.hs:109-121) requires arity 2; a `g/3`
/// head backtracks the same way and the error sits at the `{`.
#[test]
fn algapp_arity_mismatch_backtracks() {
    let src = "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g{'a'}'b') ]\n\nend\n";
    assert_expected(
        src,
        7,
        18,
        "{",
        &["letter or digit", "\".\"", "\",\"", "\")\""],
    );
}

// ---------------------------------------------------------------------------
// Formula contexts: `blatom`'s un-try'd node-equality alternative
// (Formula.hs:57) consumes the atom's leading identifier as a `nodevar` and
// its `opEqual` failure right after it is THE reported error.
// ---------------------------------------------------------------------------

/// A lowercase applied name in a lemma: `fact` refuses it (lowercase), the
/// term path backtracks to a variable, and the node-equality reparse puts the
/// error at the char after the name.
#[test]
fn formula_lowercase_application_frame() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3(x) @ #i ==> F\"\n\nend\n";
    assert_expected(src, 8, 16, "(", &["letter or digit", "\".\"", "\"=\""]);
}

/// Whitespace variant: the `letter or digit` hangover is dropped, `"."`
/// survives at the post-whitespace position.
#[test]
fn formula_lowercase_application_frame_with_whitespace() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3 (x) @ #i ==> F\"\n\nend\n";
    assert_expected(src, 8, 17, "(", &["\".\"", "\"=\""]);
}

/// Even a DECLARED, well-arity application errors when used where a fact is
/// needed: the node-equality reparse stops after the bare name, so the error
/// sits at the `(` — not at the `@`.
#[test]
fn formula_declared_application_errors_after_the_name() {
    let src = "theory T\nbegin\n\nfunctions: g/1\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. g(x) @ #i ==> F\"\n\nend\n";
    assert_expected(src, 10, 15, "(", &["letter or digit", "\".\"", "\"=\""]);
}

/// A bare variable with no relational operator: same reparse, error at the
/// `@` (whitespace dropped the `letter or digit`).
#[test]
fn formula_bare_variable_frame() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. x @ #i ==> F\"\n\nend\n";
    assert_expected(src, 8, 16, "@", &["\".\"", "\"=\""]);
}

/// A non-identifier-headed atom (`'a' @ …`): `nodevar` consumes nothing, so
/// the empty failures merge instead — the `<?>` relabels of the try-wrapped
/// relational alternatives that consumed the term.
#[test]
fn formula_nonidentifier_atom_unions_relational_labels() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. 'a' @ #i ==> F\"\n\nend\n";
    assert_expected(src, 8, 18, "@", &["subterm predicate", "term equality"]);
}

/// An undeclared UPPERCASE application before a relational operator: the
/// term-relational alternatives die at the `(`, the `Pred` fact alternative
/// then wins, and the leftover `= y` breaks the formula at its closing
/// quote.  The port reports that as the unterminated formula string, whose
/// primary position is the same one the parsec frame carried.
#[test]
fn formula_undeclared_uppercase_relop_becomes_pred_then_close_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x y #i. P3(x) = y ==> F\"\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::UnterminatedDelimiter {
        opening,
        opening_at,
        found,
        found_at,
        expected,
    } = &e
    else {
        panic!("expected an unterminated-delimiter error, got {e:?}");
    };
    assert_eq!(opening, "\"");
    assert_eq!((opening_at.line, opening_at.col), (8, 3));
    assert_eq!(found.as_deref(), Some("="));
    assert_eq!((found_at.line, found_at.col), (8, 22));
    assert_eq!(expected, &["\""]);
}

// ---------------------------------------------------------------------------
// `equations:` context (eqn = True)
// ---------------------------------------------------------------------------

/// Arity mismatch inside an equation: the backtracked variable is followed by
/// `equalSign`'s failing `=`.
#[test]
fn equation_arity_mismatch_frame() {
    let src = "theory T\nbegin\n\nfunctions: g/2\n\nequations: g(x) = x\n\nend\n";
    assert_expected(src, 6, 13, "(", &["letter or digit", "\".\"", "\"=\""]);
}

/// A reserved builtin name in an equation is a GHC `error`, not a parsec
/// failure (Term.hs:90-92): the exception escapes every `try`, which the port
/// models with the non-backtrackable [`ParseError::Abort`].
#[test]
fn equation_reserved_builtin_is_an_abort() {
    let src = "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::Abort { message, .. } = &e else {
        panic!("expected an abort, got {e:?}");
    };
    assert_eq!(
        message,
        "`\"exp\"` is a reserved function name for builtins."
    );
}

/// The check fires on the identifier alone — even a BARE reserved name in an
/// equation operand aborts (naryOpApp runs before `nullaryApp`/`plit` for
/// every identifier-headed atom).
#[test]
fn equation_bare_reserved_builtin_is_an_abort() {
    let src = "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::Abort { message, .. } = &e else {
        panic!("expected an abort, got {e:?}");
    };
    assert_eq!(
        message,
        "`\"mun\"` is a reserved function name for builtins."
    );
}

// ---------------------------------------------------------------------------
// `macros:` body — the term ends the ITEM, so the error is the top-level
// item alternation's.
// ---------------------------------------------------------------------------

/// The failed application leaves the macro list at a position where only a
/// theory item can follow, so the item alternation reports.  Its `expected`
/// set is the three item keywords closest to the offending token, not the
/// full keyword list parsec used to print.
#[test]
fn macro_body_application_frame_is_the_item_position_error() {
    let src =
        "theory T\nbegin\n\nmacros: m(x) = k(x,'a')\n\nrule r:\n  [ ] --> [ Out(m('b')) ]\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    assert!(
        matches!(&e, ParseError::ExpectedTheoryItem { .. }),
        "expected a theory-item error, got {e:?}"
    );
    let at = e.location();
    assert_eq!((at.line, at.col), (4, 17));
    assert!(e.found().is_some_and(|f| f.starts_with('(')));
    assert_eq!(
        e.expected().unwrap_or_default(),
        ["\"axiom\"", "\"test\"", "\"lemma\""]
    );
}
