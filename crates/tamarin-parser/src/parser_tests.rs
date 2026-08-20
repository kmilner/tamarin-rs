use super::*;

// ---- error-model helpers ----

/// The `(line, column, message)` of the [`ParseError::Custom`] a `fail` site
/// raises.  `Custom` is the bridge variant for the HS `fail`s this port
/// reproduces verbatim, so the message text is the HS one and the position is
/// the one `lexeme` left behind.
fn custom_err(src: &str, flags: &[&str]) -> (u32, u32, String) {
    match parse_theory(src, flags).unwrap_err() {
        ParseError::Custom { message, at } => (at.line, at.col, message),
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// A non-binary `[AC]` declaration is HS `function`'s `fail "conflicting
/// arity : AC function must be binary"` (Signature.hs:220), raised at the
/// position `lexeme` left after the attribute list.  Positions pinned to the
/// pinned oracle (ef3f0468).
#[test]
fn non_binary_ac_declaration_is_a_parse_error() {
    assert_eq!(
        custom_err(
            "theory AC3 begin\n\nfunctions: f/3 [AC]\n\nrule R: [ ] --[ ]-> [ ]\n\nend\n",
            &[],
        ),
        (
            5,
            1,
            "conflicting arity : AC function must be binary".to_string()
        )
    );

    assert_eq!(
        custom_err("theory AC5 begin\n\nfunctions: f/3 [AC], g/1\n\nend\n", &[]),
        (
            3,
            20,
            "conflicting arity : AC function must be binary".to_string()
        )
    );

    // Arity 2 is accepted (and only then does the symbol become infix).
    assert!(parse_theory("theory AC begin\n\nfunctions: f/2 [AC]\n\nend\n", &[]).is_ok());
}

/// A `theory <NAME> begin … end` around a two-line body, the shape of the
/// pinned `builtins:`/`functions:` probes: the body occupies lines 3 and 4, so
/// every diagnostic below lands on `end` at line 6, column 1.
fn decl_probe_err(name: &str, body: &str) -> (u32, u32, String) {
    custom_err(&format!("theory {name} begin\n\n{body}\n\nend\n"), &[])
}

/// HS `function`'s check (1) (Theory/Text/Parser/Signature.hs:200-209): a
/// name an enabled `builtins:` item reserved must be re-declared at exactly
/// the builtin's `(arity, Privacy, Constructability, NDCstate)` tuple.  It
/// runs BEFORE the conflicting-arities check (Signature.hs:212) and before
/// the `[AC]` arity check (Signature.hs:220), so its message wins over both.
/// Message text and position pinned to the pinned oracle (ef3f0468).
#[test]
fn builtin_reserved_name_check_precedes_the_arity_and_ac_checks() {
    // `[AC]` + arity 3 would otherwise be "AC function must be binary".
    assert_eq!(
        decl_probe_err("B1", "builtins: hashing\nfunctions: h/3 [AC]"),
        (
            6,
            1,
            "`h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
    // Same name declared twice would otherwise be "conflicting arities".
    assert_eq!(
        decl_probe_err("B7", "builtins: hashing\nfunctions: h/1, h/3 [AC]"),
        (
            6,
            1,
            "`h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
    // `fst` has no exemption in check (1): `dest-pairing` reserves it at
    // the DESTRUCTOR shape, so re-declaring the constructor is an error
    // even though check (2) would wave it through (Signature.hs:213).
    assert_eq!(
        decl_probe_err("E1", "builtins: dest-pairing\nfunctions: fst/1 [AC]"),
        (
            6,
            1,
            "`fst` conflicts with builtin(s) [\"dest-pairing\"] \
             (builtin: (1,Public,Destructor,NotNDC), requested: (1,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
    // Every attribute reaches `requested`, including the two NDC flags.
    for (attr, shown) in [
        ("private", "(1,Private,Constructor,NotNDC)"),
        ("destructor", "(1,Public,Destructor,NotNDC)"),
        ("NDC", "(1,Public,Constructor,IsNDC)"),
        ("NDC-diff", "(1,Public,Constructor,IsNDCDiff)"),
    ] {
        assert_eq!(
            decl_probe_err("P", &format!("builtins: hashing\nfunctions: h/1 [{attr}]")),
            (
                6,
                1,
                format!(
                    "`h` conflicts with builtin(s) [\"hashing\"] \
                     (builtin: (1,Public,Constructor,NotNDC), requested: {shown})"
                )
            ),
            "attribute {attr}"
        );
    }
    // `conflictingBuiltins` (Signature.hs:203) scans the WHOLE table in
    // `builtinsNames` order, not just the builtins this theory enabled.
    assert_eq!(
        decl_probe_err("P6", "builtins: asymmetric-encryption\nfunctions: pk/2"),
        (
            6,
            1,
            "`pk` conflicts with builtin(s) [\"asymmetric-encryption\",\"signing\",\
             \"dest-asymmetric-encryption\",\"dest-signing\",\"revealing-signing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (2,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
    // The builtin tuple comes from the ENABLED signature, so the two
    // `dest-*` rows report their destructor variants.
    assert_eq!(
        decl_probe_err(
            "P12",
            "builtins: dest-symmetric-encryption\nfunctions: sdec/2"
        ),
        (
            6,
            1,
            "`sdec` conflicts with builtin(s) [\"symmetric-encryption\",\
             \"dest-symmetric-encryption\"] (builtin: (2,Public,Destructor,NotNDC), \
             requested: (2,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
    // `locations-report` is the only row with a private symbol and the only
    // one HS lists first.
    assert_eq!(
        decl_probe_err("P9", "builtins: locations-report\nfunctions: rep/2"),
        (
            6,
            1,
            "`rep` conflicts with builtin(s) [\"locations-report\"] \
             (builtin: (2,Private,Constructor,NotNDC), requested: (2,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
}

/// The attribute list is not part of the diagnostic: a declaration written
/// with an explicit `[…]` and one written without land on the same variant at
/// the same position, carrying only the `fail` message.
#[test]
fn bracketed_and_unbracketed_declarations_report_the_same_conflict() {
    assert_eq!(
        decl_probe_err("B2", "builtins: hashing\nfunctions: h/1, h/2"),
        (
            6,
            1,
            "`h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (2,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
    assert_eq!(
        decl_probe_err("P24", "builtins: hashing\nfunctions: h/3 []"),
        (
            6,
            1,
            "`h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))"
                .to_string()
        )
    );
}

/// HS `function`'s check (2) (Signature.hs:212-216) is a parse error too,
/// not something a later stage reports.  The macro row it can also match
/// registers as `(k, Private, Destructor, NotNDC)` (Macro.hs:46).
/// Message text and position pinned to the pinned oracle.
#[test]
fn conflicting_arities_is_a_parse_error() {
    assert_eq!(
        custom_err("theory CONF1 begin\n\nfunctions: f/1, f/3\n\nend\n", &[]),
        (
            5,
            1,
            "conflicting arities/options (1,Public,Constructor,NotNDC) and \
             (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
             for this function."
                .to_string()
        )
    );
    // `reliable-channel` has no MaudeSig, so it reserves nothing and the
    // clash between the two user declarations is check (2)'s to report.
    assert_eq!(
        decl_probe_err("P22", "builtins: reliable-channel\nfunctions: h/1, h/2"),
        (
            6,
            1,
            "conflicting arities/options (1,Public,Constructor,NotNDC) and \
             (2,Public,Constructor,NotNDC) for `h`. Please choose a different name \
             for this function."
                .to_string()
        )
    );
    assert_eq!(
        decl_probe_err("P29", "macros: mh(x, y) = x\nfunctions: mh/2"),
        (
            6,
            1,
            "conflicting arities/options (2,Private,Destructor,NotNDC) and \
             (2,Public,Constructor,NotNDC) for `mh`. Please choose a different name \
             for this function."
                .to_string()
        )
    );
}

/// HS `extendSig`'s own two checks (Signature.hs:107-119), raised at the
/// position the builtin's `symbol` lexeme reached.  Message text and position
/// pinned to the pinned oracle.
#[test]
fn builtins_item_rejects_conflicting_functions_and_macros() {
    assert_eq!(
        decl_probe_err("P17", "functions: h/2\nbuiltins: hashing"),
        (
            6,
            1,
            "Builtin 'hashing' conflicts with existing function(s) (same name, different \
             arity or function options): [\"h\"]. Please remove these function definitions \
             or use different names."
                .to_string()
        )
    );
    assert_eq!(
        decl_probe_err("P28", "macros: h(x) = x\nbuiltins: hashing"),
        (
            6,
            1,
            "Builtin 'hashing' conflicts with existing macro '[\"h\"]'".to_string()
        )
    );
    // Per-name, in list order: the SECOND builtin sees what the first
    // merged, and the error sits at the end of that name's lexeme.
    assert_eq!(
        custom_err(
            "theory P26 begin\n\nbuiltins: symmetric-encryption, dest-symmetric-encryption\n\
             functions: sdec/2\n\nend\n",
            &[],
        ),
        (
            4,
            1,
            "Builtin 'dest-symmetric-encryption' conflicts with existing function(s) \
             (same name, different arity or function options): [\"sdec\"]. Please remove \
             these function definitions or use different names."
                .to_string()
        )
    );
    // A `dest-*` builtin therefore cannot follow its constructor twin.
    assert_eq!(
        decl_probe_err(
            "P30",
            "builtins: symmetric-encryption, dest-symmetric-encryption\n"
        ),
        (
            6,
            1,
            "Builtin 'dest-symmetric-encryption' conflicts with existing function(s) \
             (same name, different arity or function options): [\"sdec\"]. Please remove \
             these function definitions or use different names."
                .to_string()
        )
    );
    assert_eq!(
        decl_probe_err("P31", "builtins: signing, dest-signing\n"),
        (
            6,
            1,
            "Builtin 'dest-signing' conflicts with existing function(s) (same name, \
             different arity or function options): [\"verify\"]. Please remove these \
             function definitions or use different names."
                .to_string()
        )
    );
    // `dest-pairing` is exempt (Signature.hs:121): replacing the seeded
    // `fst`/`snd` constructors with the destructor variants is its job.
    assert!(parse_theory("theory OK begin\n\nbuiltins: dest-pairing\n\nend\n", &[]).is_ok());
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

/// HS `T.identifier` (Token.hs:393-394) rejects the reserved names
/// `["in","let","rule","diff"]` (Token.hs:214-230, see line 225).  The
/// rejection is reported at the word's END — the lexeme's trailing whitespace
/// never runs — on every declaration position below; positions pinned to the
/// pinned oracle.
#[test]
fn reserved_word_at_a_declaration_position() {
    for (src, line, col, word) in [
        (
            "theory D5\nbegin\n\nfunctions: diff/2\n\nend\n",
            4,
            16,
            "diff",
        ),
        ("theory D9\nbegin\n\n#define diff\n\nend\n", 4, 13, "diff"),
        (
            "theory R1\nbegin\n\nfunctions: let/2\n\nend\n",
            4,
            15,
            "let",
        ),
        ("theory R2\nbegin\n\nfunctions: in/2\n\nend\n", 4, 14, "in"),
        (
            "theory R3\nbegin\n\nfunctions: rule/2\n\nend\n",
            4,
            16,
            "rule",
        ),
        ("theory diff\nbegin\n\nend\n", 1, 12, "diff"),
        (
            "theory R6\nbegin\n\nrule diff:\n  [ ] --> [ ]\n\nend\n",
            4,
            10,
            "diff",
        ),
        (
            "theory R7\nbegin\n\nlemma diff:\n  exists-trace \"Ex #i. F() @ #i\"\n\nend\n",
            4,
            11,
            "diff",
        ),
    ] {
        assert_eq!(
            custom_err(src, &[]),
            (
                line,
                col,
                format!("`{word}` is a reserved word and cannot be used as an identifier")
            ),
            "source: {src:?}"
        );
    }
    // A word that merely STARTS with a reserved name is an identifier.
    assert!(parse_theory("theory D\nbegin\n\nfunctions: diffuse/2\n\nend\n", &[]).is_ok());

    // A labelled grammar site reports its own label instead — HS `predicate …
    // <?> "predicate declaration"` (Signature.hs:270-275) — pointing at the
    // start of the offending token rather than at the reserved word's end.
    let e = parse_theory(
        "theory R8 begin\n\npredicates: diff(x) <=> x = x\n\nend\n",
        &[],
    )
    .unwrap_err();
    match e {
        ParseError::Expected {
            found,
            expected,
            at,
        } => {
            assert_eq!(found.as_deref(), Some("diff(x)"));
            assert_eq!(expected, vec!["predicate declaration".to_string()]);
            assert_eq!(at.line, 3);
            assert_eq!(at.col, 13);
        }
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// A theory whose `end` never arrives fails at the item position the input
/// ran out at, asking for the one keyword that could still close it.  The
/// trailing optional parsers of the item just parsed contribute nothing to
/// the report.
#[test]
fn unterminated_theory_reports_the_missing_end_keyword() {
    for (body, line) in [
        // `protoRule`'s `option [] $ symbol "variants" *> …` (Rule.hs:134).
        ("rule R: [ ] --[ ]-> [ ]", 5),
        // `commaSep1`'s trailing `comma` after a `builtins:` list.
        ("builtins: hashing", 5),
        // `option [] $ list functionAttribute` plus the trailing `comma`
        // after a `functions:` list, with and without brackets.
        ("functions: f/2, g/1", 5),
        ("functions: f/2, g/2 [AC]", 5),
        // Two items: the position follows the LAST one.
        ("rule R: [ ] --[ ]-> [ ]\nbuiltins: hashing", 6),
    ] {
        let e = parse_theory(&format!("theory PE begin\n\n{body}\n\n"), &[]).unwrap_err();
        match e {
            ParseError::UnexpectedKeyword {
                found,
                expected,
                at,
            } => {
                assert_eq!(found, None, "body: {body:?}");
                assert_eq!(expected, vec!["end".to_string()], "body: {body:?}");
                assert_eq!(at.line, line, "body: {body:?}");
                assert_eq!(at.col, 1, "body: {body:?}");
            }
            other => panic!("unexpected variant: {other:?}"),
        }
    }
}

/// The theory of the pinned `diff` probes: a `diff(a, b)` in a rule's
/// conclusion.  `$ARGS` is substituted with the argument list under test.
fn diff_probe(args: &str) -> String {
    format!(
        "theory D\nbegin\n\nbuiltins: diffie-hellman\n\nrule RA:\n  \
             [ Fr(~a), Fr(~b) ] --[ Go( 'a' ) ]-> [ Out( diff({args}) ) ]\n\nend\n"
    )
}

fn diff_probe_err(args: &str, flags: &[&str]) -> (u32, u32, String) {
    custom_err(&diff_probe(args), flags)
}

/// HS `diffOp` (Term.hs:123-135) parses `diff(...)` unconditionally and then
/// `fail`s unless the signature's diff bit is on, so a `diff` term in a
/// theory parsed without the flag is a parse error — not an ordinary user
/// function.  The three `fail`s fire in HS's order (arity, then equations,
/// then flag); message text and position pinned to the pinned oracle
/// (ef3f0468).
#[test]
fn diff_operator_without_the_diff_flag_is_a_parse_error() {
    assert_eq!(
        diff_probe_err("(~a*~b), ~a", &[]),
        (
            7,
            65,
            "diff operator found, but flag diff not set".to_string()
        )
    );

    // The arity check runs FIRST and hides the flag diagnostic, with or
    // without the flag.  `commaSep = flip sepEndBy comma` (Token.hs:353-355)
    // parses the empty and the over-long list happily, so all three counts
    // reach the same `fail`.
    for args in ["~a", "~a, ~b, ~a", ""] {
        let expected_col = (47 + args.len() + 7) as u32;
        for flags in [&[][..], &["diff"][..]] {
            assert_eq!(
                diff_probe_err(args, flags),
                (
                    7,
                    expected_col,
                    "the diff operator requires exactly 2 arguments".to_string()
                ),
                "args = {args:?}, flags = {flags:?}"
            );
        }
    }

    // Nested: the INNER `diff` fails first, and its position (after the inner
    // closing paren, at the outer comma) is the one reported.
    assert_eq!(
        diff_probe_err("diff(~a, ~b), ~b", &[]),
        (
            7,
            64,
            "diff operator found, but flag diff not set".to_string()
        )
    );
}

/// `equations:` parses with HS's `eqn` flag set, where `diffOp`'s second
/// `fail` fires ahead of the flag check — again with or without the flag.
#[test]
fn diff_operator_is_rejected_in_equations() {
    for flags in [&[][..], &["diff"][..]] {
        assert_eq!(
            custom_err(
                "theory D\nbegin\n\nfunctions: f/1, g/1\nequations: diff(x, x) = x\n\n\
                 rule RA:\n  [ Fr(~a) ] --> [ Out( ~a ) ]\n\nend\n",
                flags,
            ),
            (5, 23, "diff operator not allowed in equations".to_string()),
            "flags = {flags:?}"
        );
    }
}

/// `diff` not followed by `(`: `diffOp`'s `parens` fails and no other `term`
/// alternative accepts a reserved word, so the site reports its own `term`
/// label at the token that stopped it.
#[test]
fn bare_diff_token_is_a_parse_error() {
    let e = parse_theory(
        "theory D\nbegin\n\nrule RA:\n  [ Fr(~a) ] --> [ Out( diff ) ]\n\nend\n",
        &[],
    )
    .unwrap_err();
    match e {
        ParseError::Expected {
            found,
            expected,
            at,
        } => {
            assert_eq!(found.as_deref(), Some(")"));
            assert_eq!(expected, vec!["term".to_string()]);
            assert_eq!(at.line, 5);
            assert_eq!(at.col, 30);
        }
        other => panic!("unexpected variant: {other:?}"),
    }

    let e = parse_theory(
        "theory D\nbegin\n\nrule RA:\n  [ Fr(~a), Fr(~b) ] --> [ Out( diff{~a}~b ) ]\n\nend\n",
        &[],
    )
    .unwrap_err();
    match e {
        ParseError::Expected {
            found,
            expected,
            at,
        } => {
            assert_eq!(found.as_deref(), Some("{~a}~b"));
            assert_eq!(expected, vec!["term".to_string()]);
            assert_eq!(at.line, 5);
            assert_eq!(at.col, 37);
        }
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// The guard is flag-gated, not an unconditional reject: HS `theory` turns
/// the signature bit on when the CLI-defined flags contain `diff`
/// (Theory/Text/Parser.hs:232-237, see line 234), and the pinned oracle then
/// parses the same probe.  `Term::Diff` stays constructible on that path.
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
fn theory_keyword_error() {
    let e = parse_theory("theary Foo\nbegin\nend\n", &[]).unwrap_err();
    match e {
        ParseError::UnexpectedKeyword {
            found,
            expected,
            at,
        } => {
            assert_eq!(found.as_deref(), Some("theary"));
            assert_eq!(expected, vec!["theory".to_string()]);
            assert_eq!(at.line, 1);
            assert_eq!(at.col, 1);
            assert_eq!(at.start, 0);
            assert_eq!(at.end, 6);
        }
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// Garbage at an item position reports the whole top-level keyword set,
/// ranked by edit distance to what was actually written, at the start of the
/// offending token.
#[test]
fn garbage_at_item_position_suggests_the_nearest_theory_items() {
    let e = parse_theory("theory Foo\nbegin\nrul R:\n[]-->[]\nend\n", &[]).unwrap_err();
    match &e {
        ParseError::ExpectedTheoryItem { found, at, .. } => {
            assert_eq!(found.as_deref(), Some("rul"));
            assert_eq!(at.line, 3);
            assert_eq!(at.col, 1);
        }
        other => panic!("unexpected variant: {other:?}"),
    }
    // `expected()` narrows the full item set to the three nearest matches.
    assert_eq!(
        e.expected().unwrap(),
        vec!["\"rule\"", "\"let\"", "\"end\""]
    );
}

#[test]
fn formula_trailing_garbage_uses_structured_variant() {
    let e = parse_formula_str("T & F junk").unwrap_err();
    match e {
        ParseError::TrailingGarbageInFormulaString {
            found,
            expected,
            at,
        } => {
            assert_eq!(found.as_deref(), Some("junk"));
            assert_eq!(expected, vec!["end of input".to_string()]);
            assert_eq!(at.line, 1);
            assert_eq!(at.col, 7);
        }
        other => panic!("unexpected variant: {other:?}"),
    }
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
            let kinds = v.iter().map(|b| b.kind).collect::<Vec<_>>();
            assert_eq!(kinds, vec![BuiltinKind::Hashing, BuiltinKind::Signing]);
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
            assert_eq!(r.premises.len(), 1);
            assert_eq!(r.actions.len(), 1);
            assert_eq!(r.conclusions.len(), 1);
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
        TheoryItem::Lemma(_) => {}
        x => panic!("expected lemma, got {:?}", x),
    }
}

#[test]
fn comment_handling() {
    let s = "/* outer */ theory T // line\n begin /* x /* y */ z */ end";
    let t = parse_theory(s, &[]).unwrap();
    assert_eq!(t.name, "T");
}

#[test]
fn term_application() {
    // Structural mode ([`parse_term_str`]'s): a theory parse resolves the
    // head through `lookup_arity` and an undeclared `h` would backtrack
    // to a variable (oracle probes p05/p25 — unknown operators are parse
    // errors upstream).
    let mut p = Parser::new("h(<a, b>, ~k)", &[], false);
    p.resolve_prefix_apps = false;
    let t = p.term(false).unwrap();
    match t {
        Term::App(name, args) => {
            assert_eq!(name, "h");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected App"),
    }
}

#[test]
fn formula_string() {
    let f = parse_formula_str("All x. P(x) ==> Q(x)").unwrap();
    match &f.kind {
        FormulaKind::Forall(_, _) => {}
        _ => panic!("expected Forall"),
    }
}

// HS `blatom` (Formula.hs:45-57) tries the term-relational atoms
// (Subterm/Less/EqE) BEFORE the bare-fact `Pred` alternative, so an
// uppercase function applied with a relational operator is an equality/
// subterm atom, not a predicate. Verified against tamarin-prover 1.13.0:
// `A(Foo(x))@i ==> Foo(x) = Foo(y)` renders `(Foo(x) = Foo(y))`.
#[test]
fn fatom_fact_lhs_of_relop_is_term_atom() {
    // Equality: `Foo(x) = Foo(y)` must be Atom::Eq(App,App), not Pred.
    let f = parse_formula_str("Foo(x) = Foo(y)").unwrap();
    match f.kind {
        FormulaKind::Atom(Atom::Eq(Term::App(l, _), Term::App(r, _))) => {
            assert_eq!(l, "Foo");
            assert_eq!(r, "Foo");
        }
        other => panic!("expected Eq(App,App), got {:?}", other),
    }
    // Subterm: `A(x) << B(y)` must be Atom::Subterm, not Pred.
    let f = parse_formula_str("A(x) << B(y)").unwrap();
    match f.kind {
        FormulaKind::Atom(Atom::Subterm(Term::App(l, _), Term::App(r, _))) => {
            assert_eq!(l, "A");
            assert_eq!(r, "B");
        }
        other => panic!("expected Subterm(App,App), got {:?}", other),
    }
    // A genuine predicate atom (no following relational op) stays Pred.
    let f = parse_formula_str("P(x) & Q(y)").unwrap();
    match f.kind {
        FormulaKind::And(a, _) => match a.kind {
            FormulaKind::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
            ref other => panic!("expected Pred, got {:?}", other),
        },
        other => panic!("expected And, got {:?}", other),
    }
    // Implication after a predicate must NOT be misread as `=` (==> guard).
    let f = parse_formula_str("P(x) ==> Q(y)").unwrap();
    match f.kind {
        FormulaKind::Implies(a, _) => match a.kind {
            FormulaKind::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
            ref other => panic!("expected Pred LHS of ==>, got {:?}", other),
        },
        other => panic!("expected Implies, got {:?}", other),
    }
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
    assert!(parse_term_str("<>").is_err(), "<> must be a parse error");
    // Singleton tuple collapses to the inner term.
    match parse_term_str("<x>").unwrap() {
        Term::Var(v) => assert_eq!(v.name, "x"),
        other => panic!("expected singleton to collapse to Var, got {:?}", other),
    }
    // Two-element tuple is a Pair.
    match parse_term_str("<x, y>").unwrap() {
        Term::Pair(items) => assert_eq!(items.len(), 2),
        other => panic!("expected Pair, got {:?}", other),
    }
}

// HS `factAnnotation` SolveFirst is `opUnion = symbol_ "++" <|> symbol_ "+"`
// (Fact.hs:31-36, see line 32, Token.hs:551-552), so `[++]` is accepted like `[+]`.
// Verified against tamarin-prover 1.13.0: `Foo(~k)[++]` parses and renders
// as `[+]`.
#[test]
fn fact_annotation_accepts_double_plus() {
    let s = "theory T begin rule R: [ Fr(~k) ] --[ Foo(~k)[++] ]-> [ Out(~k) ] end";
    let t = parse_theory(s, &[]).unwrap();
    let rule = t
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("rule R");
    let act = &rule.actions[0];
    assert_eq!(act.annotations, vec![FactAnnotation::SolveFirst]);
}

// Regression: `test` is a genuine top-level theory-item keyword (HS
// `caseTest = CaseTest <$> (symbol "test" *> identifier)`,
// Theory/Text/Parser/Accountability.hs:25-27, see line 26, dispatched in `addItems`,
// Theory/Text/Parser.hs:230-393, see line 268) but is ALSO an ordinary message variable
// name inside proof goals — e.g. `solve( Match( test, sid ) @ #i4 )` in
// examples/ake/bilinear/Scott.spthy.  HS parses the proof skeleton
// STRUCTURALLY (`solve <$> parens goal`, Proof.hs:76-85, see line 80), so a `test` inside
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
    let lemmas: Vec<_> = t
        .items
        .iter()
        .filter(|it| matches!(it, TheoryItem::Lemma(_)))
        .collect();
    assert_eq!(lemmas.len(), 1, "expected exactly one lemma");
    assert!(
        !t.items
            .iter()
            .any(|it| matches!(it, TheoryItem::CaseTest(_))),
        "no CaseTest may be split out of the proof body"
    );
    let proof = match &lemmas[0] {
        TheoryItem::Lemma(l) => l.proof.as_ref().expect("lemma has a proof skeleton"),
        _ => unreachable!(),
    };
    assert!(
        proof.raw.contains("Match( test, sid )"),
        "proof raw truncated at/before `test`: {:?}",
        proof.raw
    );
    assert!(
        proof.raw.contains("qed"),
        "proof raw missing `qed`: {:?}",
        proof.raw
    );
}

// The paren-depth guard must cover the full spread of message-argument
// sorts a printed goal can carry — fresh `~k`, public `$A`, nat `%n`,
// indexed `k.1` — mixed with several bare identifiers that collide with
// top-level keywords (`test`, `rule`, `function`).  None may truncate the
// capture.
#[test]
fn proof_skeleton_captures_mixed_sorted_indexed_and_keyword_args() {
    let s = r#"theory T begin
  lemma L:
    "All x #i. Start(x) @ #i ==> F"
  simplify
  solve( Foo( ~k, $A, %n, k.1, test, rule, function ) @ #i1 )
    case c
    by sorry
  qed
end"#;
    let t = parse_theory(s, &[]).expect("mixed-arg goal must parse");
    let proof = match t
        .items
        .iter()
        .find(|it| matches!(it, TheoryItem::Lemma(_)))
        .expect("lemma")
    {
        TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
        _ => unreachable!(),
    };
    assert!(
        proof
            .raw
            .contains("Foo( ~k, $A, %n, k.1, test, rule, function )"),
        "mixed-arg goal truncated: {:?}",
        proof.raw
    );
    assert!(proof.raw.contains("qed"), "missing qed: {:?}", proof.raw);
    assert!(!t
        .items
        .iter()
        .any(|it| matches!(it, TheoryItem::CaseTest(_))));
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
    let proof = match t
        .items
        .iter()
        .find(|it| matches!(it, TheoryItem::Lemma(_)))
        .expect("lemma")
    {
        TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
        _ => unreachable!(),
    };
    assert!(
        proof.raw.contains("Foo( test, sid )") && proof.raw.contains("qed"),
        "proof body truncated: {:?}",
        proof.raw
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
    assert!(
        tac.raw.contains(r#"regex "cp\(""#),
        "tactic body truncated: {:?}",
        tac.raw
    );
    // The `(` inside the regex string must not leak the following rule into
    // the tactic capture.
    assert!(
        !tac.raw.contains("rule R"),
        "next item leaked into tactic capture: {:?}",
        tac.raw
    );
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

// Regression: a proof CASE LABEL that collides with a top-level keyword must
// not truncate the capture.  HS parses `oneCase = symbol "case" *> identifier`
// (Theory/Text/Parser/Proof.hs:98-115, see line 115) structurally, so the identifier after
// `case` is the case NAME and can be any top-level keyword — case names come
// from rule / source-case names, and `test` is the CaseTest keyword
// (Accountability.hs:25-27, see line 26).  A rule named `test` prints its solved case as
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
        !t.items
            .iter()
            .any(|it| matches!(it, TheoryItem::CaseTest(_))),
        "case label `test` must not become a top-level CaseTest"
    );
    let proof = match t
        .items
        .iter()
        .find(|it| matches!(it, TheoryItem::Lemma(_)))
        .expect("lemma")
    {
        TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
        _ => unreachable!(),
    };
    assert!(
        proof.raw.contains("case test"),
        "proof raw truncated at/before `case test`: {:?}",
        proof.raw
    );
    assert!(
        proof.raw.contains("SOLVED") && proof.raw.contains("qed"),
        "proof raw missing SOLVED/qed: {:?}",
        proof.raw
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
    // Exactly one lemma, no stray Rule/Functions items split out of the body.
    assert_eq!(
        t.items
            .iter()
            .filter(|it| matches!(it, TheoryItem::Lemma(_)))
            .count(),
        1
    );
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
    let proof = match t
        .items
        .iter()
        .find(|it| matches!(it, TheoryItem::Lemma(_)))
        .expect("lemma")
    {
        TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
        _ => unreachable!(),
    };
    for label in ["case rule", "case lemma", "case function"] {
        assert!(
            proof.raw.contains(label),
            "proof raw missing {label:?}: {:?}",
            proof.raw
        );
    }
    assert!(
        proof.raw.contains("qed"),
        "proof raw missing qed: {:?}",
        proof.raw
    );
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
    let proof = match t
        .items
        .iter()
        .find(|it| matches!(it, TheoryItem::Lemma(_)))
        .expect("lemma")
    {
        TheoryItem::Lemma(l) => l.proof.as_ref().expect("proof skeleton"),
        _ => unreachable!(),
    };
    assert!(
        proof.raw.contains("case test") && proof.raw.contains("qed"),
        "proof body truncated: {:?}",
        proof.raw
    );
    assert!(
        !proof.raw.contains("rule two"),
        "the following rule leaked into the proof capture: {:?}",
        proof.raw
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

// HS `functionAttribute` (Signature.hs:164-171) accepts `AC`, `NDC-diff` and
// `NDC`; `function` (Signature.hs:183-225) folds them into the symbol's AC and
// NDC state.
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

// HS `acterm` (Term.hs:165-174): a binary `[AC]` symbol is also an infix,
// left-associative operator — the notation `prettyTerm` emits for such
// terms.  The AST records the infix spelling as `BinOp::AcFct`, distinct
// from the prefix `App`, because a name that is also a `NoEq` symbol of
// the signature resolves NoEq when written prefix (`lookupArity`,
// Term.hs:62-72) but stays the AC symbol when written infix.
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
