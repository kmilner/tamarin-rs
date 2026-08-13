// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, BTom-GH, charlie-j, jdreier, ValentinYuri, racoucho1u,
//   Mathias-AURAND, meiersi, and other minor contributors (see upstream
//   git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser.hs,
//   lib/theory/src/Theory/Text/Parser/Macro.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

//! Parse-error parity for `functions:` declarations and for the theory's
//! closing `end`.
//!
//! Every message, position and expectation set here is the pinned Haskell
//! oracle's (Git revision ef3f0468) for the same theory, except where a
//! comment marks a deliberate divergence.

use tamarin_parser::{parse_theory, ParseError, TheoryItem};

/// Asserts `src` is rejected by a `functions:` guard with HS's `fail`ed
/// `message`, at `line`:`col`.
#[track_caller]
fn assert_custom(src: &str, message: &str, line: u32, col: u32) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let at = *e.location().location().expect("expected a location");
    let ParseError::Custom { message: got, .. } = &e else {
        panic!("expected a `fail`-style error, got {e:?}");
    };
    assert_eq!(got, message);
    assert_eq!((at.line, at.col), (line, col));
}

/// [`assert_custom`] for the conflicting-arities/options diagnostic
/// (Signature.hs:212-217), whose message is the two `show`n option tuples.
#[track_caller]
fn assert_conflict(src: &str, existing: &str, requested: &str, name: &str, line: u32, col: u32) {
    assert_custom(
        src,
        &format!(
            "conflicting arities/options ({existing}) and ({requested}) for `{name}`. \
             Please choose a different name for this function."
        ),
        line,
        col,
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
    let at = *e.location().location().expect("expected a location");
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

/// HS `function` reaches the `IsAC` arity `fail` (Signature.hs:220) only
/// through the `_` case of the conflict check at Signature.hs:212-217, so a
/// name already in the signature reports THAT diagnostic instead.
#[test]
fn redeclaration_conflict_outranks_the_ac_arity_check() {
    assert_conflict(
        "theory AC4 begin\n\nfunctions: f/1, f/3 [AC]\n\nend\n",
        "1,Public,Constructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "f",
        5,
        1,
    );

    // Each component of the options tuple is the Haskell `show` of its
    // constructor; the NDC slot is `joinNDC` of the two requested flags.
    assert_conflict(
        "theory C3 begin\n\nfunctions: f/1 [private], f/3 [AC]\n\nend\n",
        "1,Private,Constructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "f",
        5,
        1,
    );
    assert_conflict(
        "theory C4 begin\n\nfunctions: f/1 [destructor], f/3 [AC]\n\nend\n",
        "1,Public,Destructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "f",
        5,
        1,
    );
    assert_conflict(
        "theory C5 begin\n\nfunctions: f/1 [NDC], f/3 [AC]\n\nend\n",
        "1,Public,Constructor,IsNDC",
        "3,Public,Constructor,NotNDC",
        "f",
        5,
        1,
    );

    // The lookup spans the whole parse, not just the current `functions:`
    // block, and the position is wherever the attribute list left off.
    assert_conflict(
        "theory C9 begin\n\nfunctions: f/1\n\nfunctions: f/3 [AC]\n\nend\n",
        "1,Public,Constructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "f",
        7,
        1,
    );

    // `pairMaudeSig` is the starting signature (Token.hs:260-261), so `pair`
    // and the two projections are already declared.
    assert_conflict(
        "theory C2 begin\n\nfunctions: pair/3 [AC]\n\nend\n",
        "2,Public,Constructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "pair",
        5,
        1,
    );
    assert_conflict(
        "theory D5 begin\n\nfunctions: fst/3 [AC], f/2 [AC]\n\nend\n",
        "1,Public,Constructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "fst",
        3,
        22,
    );

    // Macros register as `(k, Private, Destructor, NotNDC)` (Macro.hs:46) and
    // are searched after the free symbols.
    assert_conflict(
        "theory C8 begin\n\nbuiltins: hashing\nmacros: m(x) = h(x)\nfunctions: m/3 [AC]\n\nend\n",
        "1,Private,Destructor,NotNDC",
        "3,Public,Constructor,NotNDC",
        "m",
        7,
        1,
    );

    // A name NOT yet in the signature still gets the arity diagnostic, and the
    // trailing `f/1` never runs — the oracle stops at the first `[AC]`.
    assert_custom(
        "theory C7 begin\n\nfunctions: f/3 [AC], f/1\n\nend\n",
        "conflicting arity : AC function must be binary",
        3,
        20,
    );

    // An `[AC]` symbol goes to `stACFunSyms`, not `stFunSyms`, so it leaves the
    // name free for a later declaration (oracle exit 0 for both).
    assert!(parse_theory("theory C begin\n\nfunctions: f/2 [AC], f/3\n\nend\n", &[]).is_ok());
    assert!(parse_theory("theory C begin\n\nfunctions: f/2 [AC], f/2\n\nend\n", &[]).is_ok());
}

/// Signature.hs:213 exempts a `fst`/`snd` re-declaration at the pair
/// projections' own shape, and :217 then returns the EXISTING symbol — so the
/// arity check never runs and `[AC]` is dropped.  The oracle accepts
/// `fst/1 [AC]` and `snd/1 [AC]` at exit 0 and prints the full theory.
#[test]
fn pair_projection_redeclaration_short_circuits_the_ac_check() {
    for src in [
        "theory D1 begin\n\nfunctions: fst/1 [AC]\n\nend\n",
        "theory D2 begin\n\nfunctions: snd/1 [AC]\n\nend\n",
    ] {
        let thy = parse_theory(src, &[]).expect("pair projection re-declaration is accepted");
        let Some(TheoryItem::Functions(decls)) = thy
            .items
            .iter()
            .find(|i| matches!(i, TheoryItem::Functions(_)))
        else {
            panic!("no functions item in {src}");
        };
        assert!(!decls[0].ac, "the `[AC]` attribute is dropped");
    }

    // The exemption tests name, arity AND privacy, so these still conflict.
    assert_conflict(
        "theory D4 begin\n\nfunctions: fst/1 [private, AC]\n\nend\n",
        "1,Public,Constructor,NotNDC",
        "1,Private,Constructor,NotNDC",
        "fst",
        5,
        1,
    );
    assert_conflict(
        "theory D3 begin\n\nfunctions: fst/2 [AC]\n\nend\n",
        "1,Public,Constructor,NotNDC",
        "2,Public,Constructor,NotNDC",
        "fst",
        5,
        1,
    );
}

/// The expectation sets HS `functionType` (Signature.hs:150-161) merges at the
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
/// (Parser.hs:246-248) is `try (T.symbol spthy "end")` (Token.hs:272-273), a
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
        let at = *e.location().location().expect("expected a location");
        assert_eq!((at.line, at.col), (7, 1), "position for {tail:?}");
        assert_eq!(e.found(), Some(word));
        assert_eq!(e.expected().unwrap_or_default(), expected, "for {tail:?}");
    }
}
