// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parse-error parity for `functions:` declarations and for the
//! theory's closing `end`.
//!
//! Every expected string here is the stderr the pinned Haskell oracle
//! (Git revision ef3f0468) prints for the same theory, minus the three
//! `maude tool:` banner lines.

use tamarin_parser::{parse_theory, TheoryItem};

/// The parse error for `src`, rendered with `file` as parsec's `SourcePos`
/// name — the same string HS's `show err` produces.
fn err(src: &str, file: &str) -> String {
    parse_theory(src, &[])
        .unwrap_err()
        .with_source(file)
        .to_string()
}

/// `theory T begin\n\nfunctions: <decl>\n\nend\n`, the shape of the one-line
/// declaration probes below.
fn decl_theory(decl: &str) -> String {
    format!("theory T begin\n\nfunctions: {decl}\n\nend\n")
}

/// HS `function` reaches the `IsAC` arity `fail` (Signature.hs:220) only
/// through the `_` case of the conflict check at Signature.hs:212-217, so a
/// name already in the signature reports THAT diagnostic instead.
#[test]
fn redeclaration_conflict_outranks_the_ac_arity_check() {
    assert_eq!(
        err(
            "theory AC4 begin\n\nfunctions: f/1, f/3 [AC]\n\nend\n",
            "ac4.spthy"
        ),
        "\"ac4.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Public,Constructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
         for this function."
    );

    // Each component of the options tuple is the Haskell `show` of its
    // constructor; the NDC slot is `joinNDC` of the two requested flags.
    assert_eq!(
        err(
            "theory C3 begin\n\nfunctions: f/1 [private], f/3 [AC]\n\nend\n",
            "c3.spthy"
        ),
        "\"c3.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Private,Constructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
         for this function."
    );
    assert_eq!(
        err(
            "theory C4 begin\n\nfunctions: f/1 [destructor], f/3 [AC]\n\nend\n",
            "c4.spthy"
        ),
        "\"c4.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Public,Destructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
         for this function."
    );
    assert_eq!(
        err(
            "theory C5 begin\n\nfunctions: f/1 [NDC], f/3 [AC]\n\nend\n",
            "c5.spthy"
        ),
        "\"c5.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Public,Constructor,IsNDC) and \
         (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
         for this function."
    );

    // The lookup spans the whole parse, not just the current `functions:`
    // block, and the position is wherever the attribute list left off.
    assert_eq!(
        err(
            "theory C9 begin\n\nfunctions: f/1\n\nfunctions: f/3 [AC]\n\nend\n",
            "c9.spthy"
        ),
        "\"c9.spthy\" (line 7, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Public,Constructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
         for this function."
    );

    // `pairMaudeSig` is the starting signature (Token.hs:260-261), so `pair`
    // and the two projections are already declared.
    assert_eq!(
        err(
            "theory C2 begin\n\nfunctions: pair/3 [AC]\n\nend\n",
            "c2.spthy"
        ),
        "\"c2.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (2,Public,Constructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `pair`. Please choose a different name \
         for this function."
    );
    assert_eq!(
        err(
            "theory D5 begin\n\nfunctions: fst/3 [AC], f/2 [AC]\n\nend\n",
            "d5.spthy"
        ),
        "\"d5.spthy\" (line 3, column 22):\nunexpected \",\"\n\
         conflicting arities/options (1,Public,Constructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `fst`. Please choose a different name \
         for this function."
    );

    // Macros register as `(k, Private, Destructor, NotNDC)` (Macro.hs:46) and
    // are searched after the free symbols.
    assert_eq!(
        err(
            "theory C8 begin\n\nbuiltins: hashing\nmacros: m(x) = h(x)\nfunctions: m/3 [AC]\n\nend\n",
            "c8.spthy"
        ),
        "\"c8.spthy\" (line 7, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Private,Destructor,NotNDC) and \
         (3,Public,Constructor,NotNDC) for `m`. Please choose a different name \
         for this function."
    );

    // A name NOT yet in the signature still gets the arity diagnostic, and the
    // trailing `f/1` never runs — the oracle stops at the first `[AC]`.
    assert_eq!(
        err(
            "theory C7 begin\n\nfunctions: f/3 [AC], f/1\n\nend\n",
            "c7.spthy"
        ),
        "\"c7.spthy\" (line 3, column 20):\nunexpected \",\"\n\
         conflicting arity : AC function must be binary"
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
    assert_eq!(
        err(
            "theory D4 begin\n\nfunctions: fst/1 [private, AC]\n\nend\n",
            "d4.spthy"
        ),
        "\"d4.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Public,Constructor,NotNDC) and \
         (1,Private,Constructor,NotNDC) for `fst`. Please choose a different name \
         for this function."
    );
    assert_eq!(
        err(
            "theory D3 begin\n\nfunctions: fst/2 [AC]\n\nend\n",
            "d3.spthy"
        ),
        "\"d3.spthy\" (line 5, column 1):\nunexpected \"e\"\n\
         conflicting arities/options (1,Public,Constructor,NotNDC) and \
         (2,Public,Constructor,NotNDC) for `fst`. Please choose a different name \
         for this function."
    );
}

/// The expectation sets HS `functionType` (Signature.hs:150-161) merges at the
/// position where its sub-parsers stop.
#[test]
fn function_type_expectation_sets() {
    // `identifier`'s trailing `many identLetter` leaves `letter or digit` on
    // the carried error, merged with `commaSep`'s `,` and `parens`' `)`.
    assert_eq!(
        err(&decl_theory("f(a:Any, b:Any, c:Any):Any [AC]"), "ac7.spthy"),
        "\"ac7.spthy\" (line 3, column 15):\nunexpected \":\"\n\
         expecting letter or digit, \",\" or \")\""
    );
    assert_eq!(
        err(&decl_theory("f(a_1:Any"), "t9.spthy"),
        "\"t9.spthy\" (line 3, column 17):\nunexpected \":\"\n\
         expecting letter or digit, \",\" or \")\""
    );

    // Trailing whitespace consumes past the hangover, which parsec then drops.
    assert_eq!(
        err(&decl_theory("f(a :Any):Any"), "t2.spthy"),
        "\"t2.spthy\" (line 3, column 16):\nunexpected \":\"\nexpecting \",\" or \")\""
    );
    assert_eq!(
        err(&decl_theory("f(a b):Any"), "t4.spthy"),
        "\"t4.spthy\" (line 3, column 16):\nunexpected \"b\"\nexpecting \",\" or \")\""
    );

    // `Any` matches through `symbol`, i.e. `string`, so it has no hangover.
    assert_eq!(
        err(&decl_theory("f(Any:Any):Any"), "t3.spthy"),
        "\"t3.spthy\" (line 3, column 17):\nunexpected \":\"\nexpecting \",\" or \")\""
    );
    assert_eq!(
        err(&decl_theory("f(Any, Any:Any"), "t8.spthy"),
        "\"t8.spthy\" (line 3, column 22):\nunexpected \":\"\nexpecting \",\" or \")\""
    );

    // An element that fails without consuming is recovered by `sepEndBy`'s
    // empty alternative, which merges `typep`'s own two labels.
    assert_eq!(
        err(&decl_theory("f(*):Any"), "t5.spthy"),
        "\"t5.spthy\" (line 3, column 14):\nunexpected \"*\"\n\
         expecting \"Any\", identifier or \")\""
    );
    assert_eq!(
        err(&decl_theory("f(Any,*):Any"), "t12.spthy"),
        "\"t12.spthy\" (line 3, column 18):\nunexpected \"*\"\n\
         expecting \"Any\", identifier or \")\""
    );

    // Neither `functionType` alternative consumed: `/` and `(` union, with the
    // function NAME's hangover in front when nothing moved past it.
    assert_eq!(
        err(&decl_theory("f:Any"), "t10.spthy"),
        "\"t10.spthy\" (line 3, column 13):\nunexpected \":\"\n\
         expecting letter or digit, \"/\" or \"(\""
    );
    assert_eq!(
        err(&decl_theory("f"), "t11.spthy"),
        "\"t11.spthy\" (line 5, column 1):\nunexpected \"e\"\nexpecting \"/\" or \"(\""
    );

    // `T.natural`'s `<?> "natural"` is the only label after `symbol "/"`.
    assert_eq!(
        err(&decl_theory("f/x"), "t14.spthy"),
        "\"t14.spthy\" (line 3, column 14):\nunexpected \"x\"\nexpecting natural"
    );

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

    // Divergence: the oracle accepts these two (exit 0, full theory printed).
    assert_eq!(
        err(&format!("{body}endd\n"), "pe.spthy"),
        "\"pe.spthy\" (line 7, column 5):\nunexpected \"\\n\"\nexpecting letter or \"{*\""
    );
    assert_eq!(
        err(
            &format!("{body}endrule R2: [ ] --[ ]-> [ ]\n"),
            "pe10.spthy"
        ),
        "\"pe10.spthy\" (line 7, column 8):\nunexpected \" \"\nexpecting letter or \"{*\""
    );

    // A shorter prefix is not the keyword on either side.
    assert_eq!(
        err(&format!("{body}en\n"), "pe6.spthy"),
        "\"pe6.spthy\" (line 7, column 3):\nunexpected \"\\n\"\nexpecting letter or \"{*\""
    );
}
