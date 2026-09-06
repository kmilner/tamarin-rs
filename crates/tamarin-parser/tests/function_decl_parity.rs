// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Function declaration validation and theory closing boundaries.

use tamarin_parser::{parse_theory, ParseErrorKind, TheoryItem};

/// `theory T begin\n\nfunctions: <decl>\n\nend\n`, the shape of the one-line
/// declaration probes below.
fn decl_theory(decl: &str) -> String {
    format!("theory T begin\n\nfunctions: {decl}\n\nend\n")
}

/// HS `function` reaches the `IsAC` arity `fail` (Parser/Signature.hs:220) only
/// through the `_` case of the conflict check at Parser/Signature.hs:212-217, so a
/// name already in the signature reports THAT diagnostic instead.
#[test]
fn redeclaration_conflict_outranks_the_ac_arity_check() {
    for (body, name) in [
        ("functions: f/1, f/3 [AC]", "f"),
        ("functions: f/1 [private], f/3 [AC]", "f"),
        ("functions: f/1 [destructor], f/3 [AC]", "f"),
        ("functions: f/1 [NDC], f/3 [AC]", "f"),
        ("functions: f/1 functions: f/3 [AC]", "f"),
        ("functions: pair/3 [AC]", "pair"),
        ("functions: fst/3 [AC], f/2 [AC]", "fst"),
        (
            "builtins: hashing macros: m(x) = h(x) functions: m/3 [AC]",
            "m",
        ),
    ] {
        let source = format!("theory T begin {body} end");
        let error = parse_theory(&source, &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::ConflictingDeclaration { name: n, .. } if n == name),
            "{source}: {error}"
        );
        let start = source.rfind(&format!("{name}/")).unwrap();
        assert_eq!(error.span(), start..start + name.len());
    }
    let error = parse_theory(&decl_theory("f/3 [AC], f/1"), &[]).unwrap_err();
    assert!(matches!(
        error.kind(),
        ParseErrorKind::NonBinaryAcFunction { arity: 3, .. }
    ));
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

    // The exemption tests name, arity and privacy.
    for decl in ["fst/1 [private, AC]", "fst/2 [AC]"] {
        let error = parse_theory(&decl_theory(decl), &[]).unwrap_err();
        assert!(
            matches!(error.kind(), ParseErrorKind::ConflictingDeclaration { name, .. } if name == "fst")
        );
    }
}

#[test]
fn malformed_function_types_point_at_the_invalid_token() {
    for (decl, token) in [
        ("f(a:Any, b:Any, c:Any):Any [AC]", ":"),
        ("f(a_1:Any", ":"),
        ("f(a :Any):Any", ":"),
        ("f(a b):Any", "b"),
        ("f(Any:Any):Any", ":"),
        ("f(Any, Any:Any", ":"),
        ("f(*):Any", "*"),
        ("f(Any,*):Any", "*"),
        ("f:Any", ":"),
        ("f/x", "x"),
    ] {
        let src = decl_theory(decl);
        let error = parse_theory(&src, &[]).unwrap_err();
        assert!(
            src[error.span().start..].starts_with(token),
            "{decl}: {error}"
        );
    }
    assert!(parse_theory(&decl_theory("f"), &[]).is_err());
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
/// port requires the word boundary (`Lexer::symbol`) and rejects, so a typo
/// cannot truncate a theory.
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

    for tail in ["endd\n", "endrule R2: [ ] --[ ]-> [ ]\n", "en\n"] {
        let error = parse_theory(&format!("{body}{tail}"), &[]).unwrap_err();
        assert_eq!(error.span().start, body.len());
    }
}
