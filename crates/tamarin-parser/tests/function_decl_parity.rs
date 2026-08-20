// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parse-error parity for `functions:` declarations and for the theory's
//! closing `end`.
//!
//! WHICH theories are rejected is pinned to the Haskell oracle (Git revision
//! ef3f0468), as are the expectation sets and their positions, except where a
//! comment marks a deliberate divergence.  The conflict and AC-arity
//! positions are the port's own: the AC-arity error points at the offending
//! declaration, the conflict at both declarations of the name.

use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError, TheoryItem};

/// Asserts `src` is rejected by a conflicting-declaration guard
/// (Theory/Text/Parser/Signature.hs:200-217): the parse fails with
/// [`ParseError::ConflictingDeclarations`] naming `name`, its `first_at` at
/// `first` — `None` when the existing symbol is seeded and so has no
/// declaration site — and its offending declaration at `second`.
#[track_caller]
fn assert_conflict(src: &str, name: &str, first: Option<(u32, u32)>, second: (u32, u32)) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::ConflictingDeclarations {
        name: got,
        context: ParseContext::Function,
        first_at,
        second_at,
    } = &e
    else {
        panic!("expected the conflict variant, got {e:?}");
    };
    assert_eq!(got, name);
    assert_eq!(
        first_at.map(|at| (at.line, at.col)),
        first,
        "first_at of {e:?}"
    );
    assert_eq!(
        (second_at.line, second_at.col),
        second,
        "second_at of {e:?}"
    );
}

/// `theory T begin\n\nfunctions: <decl>\n\nend\n`, the shape of the one-line
/// declaration probes below.
fn decl_theory(decl: &str) -> String {
    format!("theory T begin\n\nfunctions: {decl}\n\nend\n")
}

/// Asserts `functions: <decl>` fails with the [`ParseError::Expected`] bridge
/// variant at `line`:`col`, on a token starting with `found`, carrying
/// exactly the `expected` labels.
#[track_caller]
fn assert_decl_expected(decl: &str, line: u32, col: u32, found: &str, expected: &[&str]) {
    let e = parse_theory(&decl_theory(decl), &[]).expect_err("must fail to parse");
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

/// HS `function` reaches the `IsAC` arity `fail` (Theory/Text/Parser/Signature.hs:220) only
/// through the `_` case of the conflict check at Theory/Text/Parser/Signature.hs:212-217, so a
/// name already in the signature reports THAT diagnostic instead.
#[test]
fn redeclaration_conflict_outranks_the_ac_arity_check() {
    assert_conflict(
        "theory AC4 begin\n\nfunctions: f/1, f/3 [AC]\n\nend\n",
        "f",
        Some((3, 12)),
        (3, 17),
    );

    // The compared tuple carries every attribute — privacy, constructability
    // and the NDC state — so an earlier declaration that differs in any of
    // them conflicts too.
    assert_conflict(
        "theory C3 begin\n\nfunctions: f/1 [private], f/3 [AC]\n\nend\n",
        "f",
        Some((3, 12)),
        (3, 27),
    );
    assert_conflict(
        "theory C4 begin\n\nfunctions: f/1 [destructor], f/3 [AC]\n\nend\n",
        "f",
        Some((3, 12)),
        (3, 30),
    );
    assert_conflict(
        "theory C5 begin\n\nfunctions: f/1 [NDC], f/3 [AC]\n\nend\n",
        "f",
        Some((3, 12)),
        (3, 23),
    );

    // The lookup spans the whole parse, not just the current `functions:`
    // block; `second_at` is the later block's declaration.
    assert_conflict(
        "theory C9 begin\n\nfunctions: f/1\n\nfunctions: f/3 [AC]\n\nend\n",
        "f",
        Some((3, 12)),
        (5, 12),
    );

    // `pairMaudeSig` is the starting signature (Token.hs:260-261), so `pair`
    // and the two projections are already declared.  They are seeded, not
    // declared in the source, so there is no `first_at` to point at.
    assert_conflict(
        "theory C2 begin\n\nfunctions: pair/3 [AC]\n\nend\n",
        "pair",
        None,
        (3, 12),
    );
    assert_conflict(
        "theory D5 begin\n\nfunctions: fst/3 [AC], f/2 [AC]\n\nend\n",
        "fst",
        None,
        (3, 12),
    );

    // Macros register as `(k, Private, Destructor, NotNDC)` (Parser/Macro.hs:46) and
    // are searched after the free symbols, so the macro's own site is
    // `first_at`.
    assert_conflict(
        "theory C8 begin\n\nbuiltins: hashing\nmacros: m(x) = h(x)\nfunctions: m/3 [AC]\n\nend\n",
        "m",
        Some((4, 9)),
        (5, 12),
    );

    // A name NOT yet in the signature still gets the arity diagnostic, and the
    // trailing `f/1` never runs — the oracle stops at the first `[AC]`.
    let e = parse_theory("theory C7 begin\n\nfunctions: f/3 [AC], f/1\n\nend\n", &[])
        .expect_err("must fail to parse");
    let ParseError::WrongArityforACFunctionDeclaration {
        name,
        found_arity,
        at,
    } = &e
    else {
        panic!("expected the AC-arity variant, got {e:?}");
    };
    assert_eq!(name, "f");
    assert_eq!(*found_arity, 3);
    assert_eq!((at.line, at.col), (3, 12));

    // An `[AC]` symbol goes to `stACFunSyms`, not `stFunSyms`, so it leaves the
    // name free for a later declaration.  `tests/dual_declared_names.rs`
    // checks both orders, and the two symbols that each order keeps.
}

/// Parser/Signature.hs:213 exempts a `fst`/`snd` re-declaration at the pair
/// projections' own shape, and :217 then returns the EXISTING symbol
/// `NoEqUser (f, kp')` — so the arity check never runs, `[AC]` is dropped, and
/// the whole requested option tuple gives way to the builtin pair projection's
/// `(1, Public, Constructor, NotNDC)`.  The oracle accepts `fst/1 [AC]` and
/// `snd/1 [AC]` at exit 0 and prints the full theory.
#[test]
fn pair_projection_redeclaration_short_circuits_the_ac_check() {
    for src in [
        "theory D1 begin\n\nfunctions: fst/1 [AC]\n\nend\n",
        "theory D2 begin\n\nfunctions: snd/1 [AC]\n\nend\n",
        // Every other attribute is discarded the same way; the open theory's
        // `function:` typing line therefore shows none of them.
        "theory D1 begin\n\nfunctions: fst/1 [destructor, NDC, NDC-diff]\n\nend\n",
        "theory D2 begin\n\nfunctions: snd/1 [destructor, NDC, NDC-diff]\n\nend\n",
    ] {
        let thy = parse_theory(src, &[]).expect("pair projection re-declaration is accepted");
        let Some(TheoryItem::Functions(decls)) = thy
            .items
            .iter()
            .find(|i| matches!(i, TheoryItem::Functions(_)))
        else {
            panic!("no functions item in {src}");
        };
        assert!(!decls[0].ac, "the `[AC]` attribute is dropped: {src}");
        assert!(!decls[0].private, "privacy comes from `kp'`: {src}");
        assert!(
            !decls[0].destructor,
            "constructability comes from `kp'`: {src}"
        );
        assert!(!decls[0].ndc, "the NDC state comes from `kp'`: {src}");
        assert!(!decls[0].ndc_diff, "the NDC state comes from `kp'`: {src}");
    }

    // The exemption tests name, arity AND privacy, so these still conflict —
    // against the seeded projection, which has no declaration site.
    assert_conflict(
        "theory D4 begin\n\nfunctions: fst/1 [private, AC]\n\nend\n",
        "fst",
        None,
        (3, 12),
    );
    assert_conflict(
        "theory D3 begin\n\nfunctions: fst/2 [AC]\n\nend\n",
        "fst",
        None,
        (3, 12),
    );
}

/// `conflictingBuiltins` (Parser/Signature.hs:200-210) rejects a declaration
/// of a name a `builtins:` entry reserved, at any option tuple but the
/// builtin's own.  The symbol carries the `builtins:` entry that merged it, so
/// `first_at` is that entry's name — not the seeded-symbol `None` of the
/// probes above.
///
/// The oracle rejects `hashing`+`h/3` with ``` `h` conflicts with builtin(s)
/// ["hashing"] ``` and `dest-pairing`+`fst/2` with the same shape for `fst`,
/// whose destructor entry REPLACED the seeded constructor.
#[test]
fn a_builtins_entry_is_the_first_declaration_of_the_symbols_it_merges() {
    assert_conflict(
        "theory CF begin\nbuiltins: hashing\nfunctions: h/3\nend\n",
        "h",
        Some((2, 11)),
        (3, 12),
    );
    assert_conflict(
        "theory CS begin\nbuiltins: signing\nfunctions: sign/3\nend\n",
        "sign",
        Some((2, 11)),
        (3, 12),
    );
    assert_conflict(
        "theory CP begin\nbuiltins: dest-pairing\nfunctions: fst/2\nend\n",
        "fst",
        Some((2, 11)),
        (3, 12),
    );

    // Same tuple: no conflict, and the theory loads (oracle exit 0).
    parse_theory(
        "theory CH begin\nbuiltins: hashing\nfunctions: h/1\nend\n",
        &[],
    )
    .expect("a re-declaration at the builtin's own tuple is accepted");

    // The `NoEq` symbols an equational theory opens are NOT in `stFunSyms`, so
    // `functions:` may name them (oracle exit 0) even though `macros:` may not
    // — `tests/macro_conflicts.rs` pins the macro side.
    parse_theory(
        "theory CD begin\nbuiltins: diffie-hellman\nfunctions: DH_neutral/2\nend\n",
        &[],
    )
    .expect("a theory-level NoEq symbol leaves the name free for `functions:`");
}

/// The expectation sets HS `functionType` (Parser/Signature.hs:151-162) merges at the
/// position where its sub-parsers stop.
#[test]
fn function_type_expectation_sets() {
    // `identifier`'s trailing `many identLetter` leaves `letter or digit` on
    // the carried error, merged with `commaSep`'s `,` and `parens`' `)`.
    assert_decl_expected(
        "f(a:Any, b:Any, c:Any):Any [AC]",
        3,
        15,
        ":",
        &["letter or digit", "\",\"", "\")\""],
    );
    assert_decl_expected(
        "f(a_1:Any",
        3,
        17,
        ":",
        &["letter or digit", "\",\"", "\")\""],
    );

    // Trailing whitespace consumes past the hangover, which parsec then drops.
    assert_decl_expected("f(a :Any):Any", 3, 16, ":", &["\",\"", "\")\""]);
    assert_decl_expected("f(a b):Any", 3, 16, "b", &["\",\"", "\")\""]);

    // `Any` matches through `symbol`, i.e. `string`, so it has no hangover.
    assert_decl_expected("f(Any:Any):Any", 3, 17, ":", &["\",\"", "\")\""]);
    assert_decl_expected("f(Any, Any:Any", 3, 22, ":", &["\",\"", "\")\""]);

    // An element that fails without consuming is recovered by `sepEndBy`'s
    // empty alternative, which merges `typep`'s own two labels.
    assert_decl_expected("f(*):Any", 3, 14, "*", &["\"Any\"", "identifier", "\")\""]);
    assert_decl_expected(
        "f(Any,*):Any",
        3,
        18,
        "*",
        &["\"Any\"", "identifier", "\")\""],
    );

    // Neither `functionType` alternative consumed: `/` and `(` union, with the
    // function NAME's hangover in front when nothing moved past it.
    assert_decl_expected("f:Any", 3, 13, ":", &["letter or digit", "\"/\"", "\"(\""]);
    assert_decl_expected("f", 5, 1, "end", &["\"/\"", "\"(\""]);

    // `T.natural`'s `<?> "natural"` is the only label after `symbol "/"`.
    assert_decl_expected("f/x", 3, 14, "x", &["natural"]);

    // Legal shapes on either side of those errors (oracle exit 0).
    for decl in ["f():Any", "f(Any,):Any", "f(Any, b):Any", "f(Any) :Any"] {
        assert!(parse_theory(&decl_theory(decl), &[]).is_ok(), "{decl}");
    }
}

/// Trailing content after the closing `end` is ignored: HS runs the theory
/// parser WITHOUT `eof` (`runParser (whiteSpace *> parser) …`, Token.hs:247-248),
/// so whatever follows is left unconsumed and discarded.
///
/// DELIBERATE DIVERGENCE on `endd`/`endx`/`endrule …`.  HS's `symbol_ "end"`
/// (Text/Parser.hs:243,245) is `try (T.symbol spthy "end")` (Token.hs:272-273), a
/// plain `string` with no word boundary, so it PREFIX-matches the identifier
/// and the remainder becomes ignored trailing input: the pinned oracle accepts
/// `… endrule R2: [ ] --[ ]-> [ ]` at exit 0 and silently drops the rule.  This
/// port requires the word boundary (`Lexer::symbol`) and rejects the whole
/// word as an unknown theory item, so a typo cannot truncate a theory.
#[test]
fn theory_end_ignores_trailing_content_but_needs_a_word_boundary() {
    let body = "theory PE begin\n\nfunctions: f/2, g/1\n\nrule R: [ ] --[ ]-> [ ]\n\n";

    // Parity: everything after a well-delimited `end` is ignored.
    for tail in [
        "end\nthis is trailing prose that is not spthy at all !!! ###\n",
        "end\ntheory OTHER begin end\n",
        "end /* trailing comment */\n",
        "end!\n",
    ] {
        assert!(
            parse_theory(&format!("{body}{tail}"), &[]).is_ok(),
            "{tail}"
        );
    }

    // Divergence: the oracle accepts the first two (exit 0, full theory
    // printed).  The port reports the whole word as the offending token, at
    // the item position, and offers the item keywords nearest to it.
    for (tail, word, expected) in [
        ("endd\n", "endd", ["\"end\"", "\"test\"", "letter"]),
        (
            "endrule R2: [ ] --[ ]-> [ ]\n",
            "endrule",
            ["\"rule\"", "\"end\"", "\"macros\""],
        ),
        // A shorter prefix is not the keyword on either side.
        ("en\n", "en", ["\"end\"", "\"let\"", "\"test\""]),
    ] {
        let e = parse_theory(&format!("{body}{tail}"), &[]).expect_err("must fail to parse");
        assert!(
            matches!(&e, ParseError::ExpectedTheoryItem { .. }),
            "expected a theory-item error for {tail:?}, got {e:?}"
        );
        let at = e.location();
        assert_eq!((at.line, at.col), (7, 1), "position for {tail:?}");
        assert_eq!(e.found(), Some(word));
        assert_eq!(e.expected().unwrap_or_default(), expected, "for {tail:?}");
    }
}
