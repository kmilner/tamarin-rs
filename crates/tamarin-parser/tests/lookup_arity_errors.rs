// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parse errors of `lookupArity`-driven prefix-application resolution
//! (Theory/Text/Parser/Term.hs:62-105).
//!
//! HS resolves every prefix application through `lookupArity` over the
//! signature built SO FAR and parses the arity the lookup returns; on any
//! failure — unknown operator, arity mismatch, malformed argument list — the
//! try-wrapped application backtracks and the name reparses as a variable, so
//! the NEXT token breaks the enclosing grammar and the user sees that
//! consumed failure's merged frame.  This port instead reports the failure
//! directly at the application: [`ParseError::UndeclaredFunction`] for an
//! unknown operator, [`ParseError::FunctionUsedWithWrongArity`] (carrying the
//! declaration site) for an arity mismatch.  Which sources are rejected
//! matches the pinned Haskell oracle (Git revision ef3f0468, probe files
//! p02–p48 of the lookup-arity probe matrix; sources here are byte-identical
//! to the probes); the variants and positions are the port's own.

use tamarin_parser::{parse_theory, ParseError};

/// Asserts `src` fails with [`ParseError::UndeclaredFunction`] naming `name`,
/// whose span starts at `line`:`col`.
#[track_caller]
fn assert_undeclared(src: &str, name: &str, line: u32, col: u32) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::UndeclaredFunction { name: got, at } = &e else {
        panic!("expected the undeclared-function variant, got {e:?}");
    };
    assert_eq!(got, name);
    assert_eq!((at.line, at.col), (line, col), "position of {e:?}");
}

/// Asserts `src` fails with [`ParseError::FunctionUsedWithWrongArity`]:
/// `name` declared at arity `declared` (`declared_at` starting at
/// `declared_pos` when the declaration is the user's own, `None` for a
/// builtin's), used at arity `used`, the use's span starting at `used_pos`.
#[track_caller]
fn assert_wrong_arity(
    src: &str,
    name: &str,
    declared: usize,
    used: usize,
    declared_pos: Option<(u32, u32)>,
    used_pos: (u32, u32),
) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::FunctionUsedWithWrongArity {
        name: got,
        declared_arity,
        used_arity,
        declared_at,
        used_at,
    } = &e
    else {
        panic!("expected the wrong-arity variant, got {e:?}");
    };
    assert_eq!(got, name);
    assert_eq!((*declared_arity, *used_arity), (declared, used));
    assert_eq!(
        declared_at.map(|at| (at.line, at.col)),
        declared_pos,
        "declared_at of {e:?}"
    );
    assert_eq!((used_at.line, used_at.col), used_pos, "used_at of {e:?}");
}

/// Arity mismatch in a rule's fact argument: `g/3` applied to two arguments
/// reports both the declaration and the use.
#[test]
fn arity_mismatch_reports_declaration_and_use() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g('a','b')) ]\n\nend\n";
    assert_wrong_arity(src, "g", 3, 2, Some((4, 12)), (7, 17));
}

/// An UNDECLARED name applied prefix is HS `lookupArity`'s `fail "unknown
/// operator …"`; the port names the operator.
#[test]
fn undeclared_application_is_a_parse_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ Out(g('a')) ]\n\nend\n";
    assert_undeclared(src, "g", 5, 17);
}

/// Use BEFORE declaration: `lookupArity` reads the signature built so far,
/// so a later `functions:` item does not rescue an earlier use.
#[test]
fn use_before_declaration_is_a_parse_error() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ Out(g('a')) ]\n\nfunctions: g/1\n\nend\n";
    assert_undeclared(src, "g", 5, 17);
}

/// A nullary symbol applied to arguments fails the arity check like any
/// other declared symbol.
#[test]
fn nullary_applied_with_args_is_an_arity_error() {
    let src =
        "theory T\nbegin\n\nfunctions: f/0\n\nrule r:\n  [ ] --> [ Out(f('a','b')) ]\n\nend\n";
    assert_wrong_arity(src, "f", 0, 2, Some((4, 12)), (7, 17));
}

/// `h()` for the unary hashing builtin: the `k == 1` branch parses ONE
/// `tupleterm`, which requires an operand — the empty argument list fails
/// where the term was expected.
#[test]
fn unary_empty_parens_is_a_term_error() {
    let src = "theory T\nbegin\n\nbuiltins: hashing\n\nrule r:\n  [ ] --> [ Out(h()) ]\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::ExpectedTerm { found, at, .. } = &e else {
        panic!("expected a term error, got {e:?}");
    };
    assert!(
        found.as_deref().unwrap_or("").starts_with(')'),
        "offending token {found:?} should start with `)`"
    );
    assert_eq!((at.line, at.col), (7, 19));
}

/// `h('a',)` — the `k == 1` branch's `tupleterm` is `chainr1`, which does
/// NOT admit a trailing comma (unlike `commaSep` for other arities).
#[test]
fn unary_trailing_comma_is_a_term_error() {
    let src =
        "theory T\nbegin\n\nbuiltins: hashing\n\nrule r:\n  [ ] --> [ Out(h('a',)) ]\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::ExpectedTerm { found, at, .. } = &e else {
        panic!("expected a term error, got {e:?}");
    };
    assert!(
        found.as_deref().unwrap_or("").starts_with(')'),
        "offending token {found:?} should start with `)`"
    );
    assert_eq!((at.line, at.col), (7, 23));
}

/// A malformed NESTED application (undeclared `k` inside a well-arity `g`):
/// the INNER failure is the reported error.  Parsec's `try` discards it and
/// re-reports at the outer `(`; the port keeps the precise cause.
#[test]
fn nested_failure_reports_the_inner_application() {
    let src =
        "theory T\nbegin\n\nfunctions: g/2\n\nrule r:\n  [ ] --> [ Out(g(k('x'),'b')) ]\n\nend\n";
    assert_undeclared(src, "k", 7, 19);
}

/// Whitespace between the name and `(` does not move the report off the
/// application.
#[test]
fn whitespace_before_paren_keeps_the_report() {
    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g ('a','b')) ]\n\nend\n";
    assert_wrong_arity(src, "g", 3, 2, Some((4, 12)), (7, 17));
}

/// `em` is ALWAYS in `lookupArity`'s list at arity 2 (appended after the
/// macro names, Parser/Term.hs:65); a 3-argument use under bilinear-pairing
/// fails the arity check.  The builtin has no declaration site, so
/// `declared_at` is absent.
#[test]
fn em_wrong_arity_under_bp_has_no_declaration_site() {
    let src = "theory T\nbegin\n\nbuiltins: bilinear-pairing\n\nrule r:\n  [ ] --> [ Out(em('a','b','c')) ]\n\nend\n";
    assert_wrong_arity(src, "em", 2, 3, None, (7, 17));
}

/// An undeclared application reports the same variant whatever operator
/// levels the theory's builtins (or a user `[AC]` symbol) opened — HS's
/// frame varies here, collecting one label per enabled `chainl1` level.
#[test]
fn undeclared_application_reports_the_same_under_every_operator_level() {
    for (case, src) in [
        (
            "user [AC] symbol",
            "theory T\nbegin\n\nfunctions: f/2 [AC]\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n",
        ),
        (
            "xor",
            "theory T\nbegin\n\nbuiltins: xor\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n",
        ),
        (
            "multiset",
            "theory T\nbegin\n\nbuiltins: multiset\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n",
        ),
        (
            "natural-numbers",
            "theory T\nbegin\n\nbuiltins: natural-numbers\n\nrule r:\n  [ ] --> [ Out(k('a')) ]\n\nend\n",
        ),
    ] {
        let e = parse_theory(src, &[]).expect_err("must fail to parse");
        let ParseError::UndeclaredFunction { name, at } = &e else {
            panic!("case {case}: expected the undeclared-function variant, got {e:?}");
        };
        assert_eq!(name, "k", "case {case}");
        assert_eq!((at.line, at.col), (7, 17), "case {case}");
    }
}

/// The surrounding context — a tuple, grouping parens — does not change the
/// report either (HS's frame carries the context's own close labels).
#[test]
fn surrounding_context_does_not_change_the_report() {
    let src = "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(<g('a','b'), 'c'>) ]\n\nend\n";
    assert_wrong_arity(src, "g", 3, 2, Some((4, 12)), (7, 18));

    let src =
        "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out((g('a','b'))) ]\n\nend\n";
    assert_wrong_arity(src, "g", 3, 2, Some((4, 12)), (7, 18));
}

/// `op{t1}t2` (`binaryAlgApp`, Theory/Text/Parser/Term.hs:109-121) requires
/// arity 2; a `g/3` head reports the same arity mismatch.
#[test]
fn algapp_arity_mismatch_is_an_arity_error() {
    let src = "theory T\nbegin\n\nfunctions: g/3\n\nrule r:\n  [ ] --> [ Out(g{'a'}'b') ]\n\nend\n";
    assert_wrong_arity(src, "g", 3, 2, Some((4, 12)), (7, 17));
}

// ---------------------------------------------------------------------------
// Formula contexts: an atom's leading term parses through the same
// application resolution, and a missing relational operator after a complete
// term reports the relational expected set.
// ---------------------------------------------------------------------------

/// A lowercase applied name in a lemma: `fact` refuses it (lowercase), and
/// the term path reports the application as undeclared.
#[test]
fn formula_lowercase_application_is_undeclared() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3(x) @ #i ==> F\"\n\nend\n";
    assert_undeclared(src, "p3", 8, 14);
}

/// Whitespace after the name does not move the report.
#[test]
fn formula_lowercase_application_with_whitespace_is_undeclared() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3 (x) @ #i ==> F\"\n\nend\n";
    assert_undeclared(src, "p3", 8, 14);
}

/// Asserts `src` fails with the relational expected set at `line`:`col` on a
/// token starting with `found` — the error after a complete formula-atom
/// term that no relational operator follows.
#[track_caller]
fn assert_relational_expected(src: &str, line: u32, col: u32, found: &str) {
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
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
    assert_eq!(e.expected().unwrap_or_default(), ["=", "<<", "<", "(<)"]);
}

/// A DECLARED, well-arity application where a fact is needed parses as a
/// term; the missing relational operator then errors at the `@` — a fact
/// name must be uppercase, so the application can never become an action.
#[test]
fn formula_declared_application_errors_at_the_relop_position() {
    let src = "theory T\nbegin\n\nfunctions: g/1\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. g(x) @ #i ==> F\"\n\nend\n";
    assert_relational_expected(src, 10, 19, "@");
}

/// The same with the lowercase name DECLARED at the used arity: the
/// application parses, and the `@` is the error.
#[test]
fn formula_lowercase_fact_declared_as_function_fails_at_the_relop() {
    let src = "theory T\nbegin\n\nfunctions: p3/1\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. p3(x) @ #i ==> F\"\n\nend\n";
    assert_relational_expected(src, 10, 20, "@");
}

/// A bare variable with no relational operator: error at the `@`.
#[test]
fn formula_bare_variable_errors_at_the_relop_position() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. x @ #i ==> F\"\n\nend\n";
    assert_relational_expected(src, 8, 16, "@");
}

/// A non-identifier-headed atom (`'a' @ …`) reports the same set.
#[test]
fn formula_nonidentifier_atom_errors_at_the_relop_position() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x #i. 'a' @ #i ==> F\"\n\nend\n";
    assert_relational_expected(src, 8, 18, "@");
}

/// An undeclared UPPERCASE application before a relational operator: the
/// term path resolves the head and reports it undeclared.  (HS's `Pred` fact
/// alternative claims `P3(x)` instead, and the leftover `= y` breaks the
/// formula at its closing quote.)
#[test]
fn formula_undeclared_uppercase_relop_is_undeclared() {
    let src = "theory T\nbegin\n\nrule r:\n  [ ] --> [ ]\n\nlemma L:\n  \"All x y #i. P3(x) = y ==> F\"\n\nend\n";
    assert_undeclared(src, "P3", 8, 16);
}

// ---------------------------------------------------------------------------
// `equations:` context (eqn = True)
// ---------------------------------------------------------------------------

/// Arity mismatch inside an equation reports the same variant.
#[test]
fn equation_arity_mismatch_is_an_arity_error() {
    let src = "theory T\nbegin\n\nfunctions: g/2\n\nequations: g(x) = x\n\nend\n";
    assert_wrong_arity(src, "g", 2, 1, Some((4, 12)), (6, 12));
}

/// A reserved builtin name in an equation is a GHC `error` in HS
/// (Theory/Text/Parser/Term.hs:90-92): the exception escapes every `try`.
/// The port reports [`ParseError::UsedReservedBuiltin`] in the equation
/// context.
#[test]
fn equation_reserved_builtin_is_rejected() {
    let src = "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::UsedReservedBuiltin { f, at, .. } = &e else {
        panic!("expected the reserved-builtin variant, got {e:?}");
    };
    assert_eq!(f, "exp");
    assert_eq!((at.line, at.col), (4, 12));
}

/// The check fires on the identifier alone — even a BARE reserved name in an
/// equation operand is rejected (naryOpApp runs before `nullaryApp`/`plit`
/// for every identifier-headed atom).
#[test]
fn equation_bare_reserved_builtin_is_rejected() {
    let src = "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n";
    let e = parse_theory(src, &[]).expect_err("must fail to parse");
    let ParseError::UsedReservedBuiltin { f, at, .. } = &e else {
        panic!("expected the reserved-builtin variant, got {e:?}");
    };
    assert_eq!(f, "mun");
    assert_eq!((at.line, at.col), (6, 19));
}

// ---------------------------------------------------------------------------
// `macros:` body
// ---------------------------------------------------------------------------

/// An undeclared application in a macro body reports the application itself
/// (HS's backtrack ends the item instead, and the top-level item alternation
/// reports at the leftover `(`).
#[test]
fn macro_body_application_is_undeclared() {
    let src =
        "theory T\nbegin\n\nmacros: m(x) = k(x,'a')\n\nrule r:\n  [ ] --> [ Out(m('b')) ]\n\nend\n";
    assert_undeclared(src, "k", 4, 16);
}
