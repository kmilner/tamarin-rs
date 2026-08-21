// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

// ---- error-model helpers ----

fn reserved_keyword_err(src: &str) -> (u32, u32, String) {
    match parse_theory(src, &[]).unwrap_err() {
        ParseError::UsedReservedKeyword { found, at, .. } => (
            at.line,
            at.col,
            format!("`{found}` is a reserved word and cannot be used as an identifier"),
        ),
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// The `(name, first_at, second_at)` of the
/// [`ParseError::ConflictingDeclarations`] a conflicting declaration
/// raises, positions flattened to `(line, col)`.  `first_at` is the earlier
/// declaration's site — a `functions:`/`macros:` entry, or the `builtins:`
/// entry that reserved the name — and `None` for a symbol the theory carries
/// implicitly, which has no site to point at.
fn conflict_err(
    src: &str,
    expected_first_context: ParseContext,
    expected_second_context: ParseContext,
) -> (String, Option<(u32, u32)>, (u32, u32)) {
    match parse_theory(src, &[]).unwrap_err() {
        ParseError::ConflictingDeclarations {
            name,
            first_context,
            second_context,
            first_at,
            second_at,
        } => {
            assert_eq!(first_context, expected_first_context);
            assert_eq!(second_context, expected_second_context);
            (
                name,
                first_at.map(|at| (at.line, at.col)),
                (second_at.line, second_at.col),
            )
        }
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// A non-binary `[AC]` declaration is HS `function`'s `fail "conflicting
/// arity : AC function must be binary"` (Theory/Text/Parser/Signature.hs:220);
/// the port reports it as [`ParseError::WrongArityforACFunctionDeclaration`]
/// spanning the declaration itself.
#[test]
fn non_binary_ac_declaration_is_a_parse_error() {
    let ac_arity_err = |src: &str| match parse_theory(src, &[]).unwrap_err() {
        ParseError::WrongArityforACFunctionDeclaration {
            name,
            found_arity,
            at,
        } => (name, found_arity, (at.line, at.col)),
        other => panic!("unexpected variant: {other:?}"),
    };
    assert_eq!(
        ac_arity_err("theory AC3 begin\n\nfunctions: f/3 [AC]\n\nrule R: [ ] --[ ]-> [ ]\n\nend\n"),
        ("f".to_string(), 3, (3, 12))
    );

    assert_eq!(
        ac_arity_err("theory AC5 begin\n\nfunctions: f/3 [AC], g/1\n\nend\n"),
        ("f".to_string(), 3, (3, 12))
    );

    // Arity 2 is accepted (and only then does the symbol become infix).
    assert!(parse_theory("theory AC begin\n\nfunctions: f/2 [AC]\n\nend\n", &[]).is_ok());
}

/// HS `function`'s check (1) (Theory/Text/Parser/Signature.hs:200-209): a
/// name an enabled `builtins:` item reserved must be re-declared at exactly
/// the builtin's `(arity, Privacy, Constructability, NDCstate)` tuple.  It
/// runs BEFORE the conflicting-arities check
/// (Theory/Text/Parser/Signature.hs:212) and before the `[AC]` arity check
/// (Theory/Text/Parser/Signature.hs:220), so its diagnostic wins over both.
/// The port reports it as [`ParseError::ConflictingDeclarations`] with
/// `first_at` pointing at the `builtins:` entry that reserved the name.
#[test]
fn builtin_reserved_name_check_precedes_the_arity_and_ac_checks() {
    let probe = |name: &str, body: &str, first_context, second_context| {
        conflict_err(
            &format!("theory {name} begin\n\n{body}\n\nend\n"),
            first_context,
            second_context,
        )
    };
    // `[AC]` + arity 3 would otherwise be the AC-arity variant.
    assert_eq!(
        probe(
            "B1",
            "builtins: hashing\nfunctions: h/3 [AC]",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("h".to_string(), Some((3, 11)), (4, 12))
    );
    // Same name declared twice would otherwise be check (2)'s conflict,
    // whose `first_at` points at the earlier declaration.
    assert_eq!(
        probe(
            "B7",
            "builtins: hashing\nfunctions: h/1, h/3 [AC]",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("h".to_string(), Some((3, 11)), (4, 17))
    );
    // `fst` has no exemption in check (1): `dest-pairing` reserves it at
    // the DESTRUCTOR shape, so re-declaring the constructor is an error
    // even though check (2) would wave it through
    // (Theory/Text/Parser/Signature.hs:213).
    assert_eq!(
        probe(
            "E1",
            "builtins: dest-pairing\nfunctions: fst/1 [AC]",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("fst".to_string(), Some((3, 11)), (4, 12))
    );
    // Every attribute reaches `requested`, including the two NDC flags:
    // each one moves the declaration off the builtin's tuple, so each one
    // conflicts even at the builtin's own arity.
    for attr in ["private", "destructor", "NDC", "NDC-diff"] {
        assert_eq!(
            probe(
                "P",
                &format!("builtins: hashing\nfunctions: h/1 [{attr}]"),
                ParseContext::FunctionDeclaration,
                ParseContext::FunctionDeclaration
            ),
            ("h".to_string(), Some((3, 11)), (4, 12)),
            "attribute {attr}"
        );
    }
    // A re-declaration at EXACTLY the builtin's tuple is accepted.
    assert!(parse_theory(
        "theory OK begin\n\nbuiltins: hashing\nfunctions: h/1\n\nend\n",
        &[]
    )
    .is_ok());
    // The check consults the ENABLED signature's tuple: `dest-symmetric-
    // encryption` reserves `sdec` at the destructor shape, so the plain
    // constructor re-declaration conflicts.
    assert_eq!(
        probe(
            "P12",
            "builtins: dest-symmetric-encryption\nfunctions: sdec/2",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration,
        ),
        ("sdec".to_string(), Some((3, 11)), (4, 12))
    );
    // `locations-report` reserves `rep` privately, so the public
    // re-declaration conflicts.
    assert_eq!(
        probe(
            "P9",
            "builtins: locations-report\nfunctions: rep/2",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("rep".to_string(), Some((3, 11)), (4, 12))
    );
    // `first_at` is the entry that reserved THIS name, not the head of the
    // `builtins:` list: `sign` comes from `signing`, the second entry, at
    // column 20 rather than the column 11 every single-entry probe above
    // reports.
    assert_eq!(
        probe(
            "P32",
            "builtins: hashing, signing\nfunctions: sign/1",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("sign".to_string(), Some((3, 20)), (4, 12))
    );
}

/// The attribute list is not part of the diagnostic: a declaration written
/// with an explicit `[…]` and one written without both report the conflict at
/// the offending declaration.  An EMPTY `[]` counts as present.
#[test]
fn bracketed_and_unbracketed_declarations_report_the_same_conflict() {
    assert_eq!(
        conflict_err(
            "theory B2 begin\n\nbuiltins: hashing\nfunctions: h/1, h/2\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("h".to_string(), Some((3, 11)), (4, 17))
    );
    assert_eq!(
        conflict_err(
            "theory P24 begin\n\nbuiltins: hashing\nfunctions: h/3 []\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("h".to_string(), Some((3, 11)), (4, 12))
    );
}

/// HS `function`'s check (2) (Theory/Text/Parser/Signature.hs:212-216) is a
/// parse error too,
/// not something a later stage reports.  The macro row it can also match
/// registers as `(k, Private, Destructor, NotNDC)` (Theory/Text/Parser/Macro.hs:46).
/// The port reports [`ParseError::ConflictingDeclarations`] with
/// `first_at` pointing at the earlier declaration.
#[test]
fn conflicting_arities_is_a_parse_error() {
    assert_eq!(
        conflict_err(
            "theory CONF1 begin\n\nfunctions: f/1, f/3\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration
        ),
        ("f".to_string(), Some((3, 12)), (3, 17))
    );
    // `reliable-channel` has no MaudeSig, so it reserves nothing and the
    // clash between the two user declarations is check (2)'s to report.
    assert_eq!(
        conflict_err(
            "theory P22 begin\n\nbuiltins: reliable-channel\nfunctions: h/1, h/2\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration,
        ),
        ("h".to_string(), Some((4, 12)), (4, 17))
    );
    assert_eq!(
        conflict_err(
            "theory P29 begin\n\nmacros: mh(x, y) = x\nfunctions: mh/2\n\nend\n",
            ParseContext::Macro,
            ParseContext::FunctionDeclaration
        ),
        ("mh".to_string(), Some((3, 9)), (4, 12))
    );
}

/// HS `extendSig`'s own two checks (Theory/Text/Parser/Signature.hs:107-119), raised at the
/// position the builtin's `symbol` lexeme reached.  Message text and position
/// pinned to the pinned oracle.
#[test]
fn builtins_item_rejects_conflicting_functions_and_macros() {
    assert_eq!(
        conflict_err(
            "theory P17 begin\n\nfunctions: h/2\nbuiltins: hashing\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration,
        ),
        ("h".to_string(), Some((3, 12)), (4, 11))
    );
    assert_eq!(
        conflict_err(
            "theory P28 begin\n\nmacros: h(x) = x\nbuiltins: hashing\n\nend\n",
            ParseContext::Macro,
            ParseContext::FunctionDeclaration,
        ),
        ("h".to_string(), Some((3, 9)), (4, 11))
    );
    // Per-name, in list order: the SECOND builtin sees what the first
    // merged, and the error sits at the end of that name's lexeme.
    assert_eq!(
        conflict_err(
            "theory P26 begin\n\nbuiltins: symmetric-encryption, dest-symmetric-encryption\n\
             functions: sdec/2\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration,
        ),
        ("sdec".to_string(), Some((3, 11)), (3, 33))
    );
    // A `dest-*` builtin therefore cannot follow its constructor twin.
    assert_eq!(
        conflict_err(
            "theory P30 begin\n\nbuiltins: symmetric-encryption, dest-symmetric-encryption\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration,
        ),
        ("sdec".to_string(), Some((3, 11)), (3, 33))
    );
    assert_eq!(
        conflict_err(
            "theory P31 begin\n\nbuiltins: signing, dest-signing\n\nend\n",
            ParseContext::FunctionDeclaration,
            ParseContext::FunctionDeclaration,
        ),
        ("verify".to_string(), Some((3, 11)), (3, 20))
    );
    // `dest-pairing` is exempt (Theory/Text/Parser/Signature.hs:121):
    // replacing the seeded
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
            12,
            "diff",
        ),
        ("theory D9\nbegin\n\n#define diff\n\nend\n", 4, 9, "diff"),
        (
            "theory R1\nbegin\n\nfunctions: let/2\n\nend\n",
            4,
            12,
            "let",
        ),
        ("theory R2\nbegin\n\nfunctions: in/2\n\nend\n", 4, 12, "in"),
        (
            "theory R3\nbegin\n\nfunctions: rule/2\n\nend\n",
            4,
            12,
            "rule",
        ),
        ("theory diff\nbegin\n\nend\n", 1, 8, "diff"),
        (
            "theory R6\nbegin\n\nrule diff:\n  [ ] --> [ ]\n\nend\n",
            4,
            6,
            "diff",
        ),
        (
            "theory R7\nbegin\n\nlemma diff:\n  exists-trace \"Ex #i. F() @ #i\"\n\nend\n",
            4,
            7,
            "diff",
        ),
    ] {
        assert_eq!(
            reserved_keyword_err(src),
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
    // <?> "predicate declaration"` (Theory/Text/Parser/Signature.hs:270-275) — pointing at the
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
            when_parsing,
        } => {
            assert_eq!(found.as_deref(), Some("diff(x)"));
            assert_eq!(expected, vec!["predicate declaration".to_string()]);
            assert_eq!(at.line, 3);
            assert_eq!(at.col, 13);
            assert_eq!(when_parsing, ParseContext::PredicateDeclaration);
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
        // `protoRule`'s `option [] $ symbol "variants" *> …` (Theory/Text/Parser/Rule.hs:134).
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
            ParseError::Expected {
                found,
                expected,
                at,
                when_parsing,
            } => {
                assert_eq!(found, None, "body: {body:?}");
                assert_eq!(expected, vec!["end".to_string()], "body: {body:?}");
                assert_eq!(at.line, line, "body: {body:?}");
                assert_eq!(at.col, 1, "body: {body:?}");
                assert_eq!(when_parsing, ParseContext::Theory);
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

fn diff_illegal_probe_err(args: &str, flags: &[&str]) -> (bool, Option<ParseContext>, (u32, u32)) {
    match parse_theory(&diff_probe(args), flags).unwrap_err() {
        ParseError::IllegalDiffOperator {
            diff_set,
            context,
            at,
        } => (diff_set, context, (at.line, at.col)),
        other => panic!("unexpected variant: {other:?}"),
    }
}

fn diff_arity_probe_err(args: &str, flags: &[&str]) -> (String, usize, usize, (u32, u32)) {
    match parse_theory(&diff_probe(args), flags).unwrap_err() {
        ParseError::FunctionUsedWithWrongArity {
            name,
            declared_arity,
            used_arity,
            used_at,
            ..
        } => (
            name,
            declared_arity,
            used_arity,
            (used_at.line, used_at.col),
        ),
        other => panic!("unexpected variant: {other:?}"),
    }
}

/// HS `diffOp` (Theory/Text/Parser/Term.hs:123-135) parses `diff(...)`
/// unconditionally and then
/// `fail`s unless the signature's diff bit is on, so a `diff` term in a
/// theory parsed without the flag is a parse error — not an ordinary user
/// function.  The three `fail`s fire in HS's order (arity, then equations,
/// then flag); message text and position pinned to the pinned oracle
/// (ef3f0468).
#[test]
fn diff_operator_without_the_diff_flag_is_a_parse_error() {
    assert_eq!(
        diff_illegal_probe_err("(~a*~b), ~a", &[]),
        (false, None, (7, 47))
    );

    // The arity check runs FIRST and hides the flag diagnostic, with or
    // without the flag.  `commaSep = flip sepEndBy comma` (Token.hs:353-355)
    // parses the empty and the over-long list happily, so all three counts
    // reach the same `fail`.
    for args in ["~a", "~a, ~b, ~a", ""] {
        for flags in [&[][..], &["diff"][..]] {
            assert_eq!(
                diff_arity_probe_err(args, flags),
                (
                    "diff".to_string(),
                    2,
                    args.split(',').filter(|arg| !arg.is_empty()).count(),
                    (7, 47),
                ),
                "args = {args:?}, flags = {flags:?}"
            );
        }
    }

    // Nested: the INNER `diff` fails first, and its position (after the inner
    // closing paren, at the outer comma) is the one reported.
    assert_eq!(
        diff_illegal_probe_err("diff(~a, ~b), ~b", &[]),
        (false, None, (7, 52))
    );
}

/// `equations:` parses with HS's `eqn` flag set, where `diffOp`'s second
/// `fail` fires ahead of the flag check — again with or without the flag.
#[test]
fn diff_operator_is_rejected_in_equations() {
    for flags in [&[][..], &["diff"][..]] {
        assert_eq!(
            match parse_theory(
                "theory D\nbegin\n\nfunctions: f/1, g/1\nequations: diff(x, x) = x\n\n\
                 rule RA:\n  [ Fr(~a) ] --> [ Out( ~a ) ]\n\nend\n",
                flags,
            )
            .unwrap_err()
            {
                ParseError::IllegalDiffOperator {
                    diff_set,
                    context,
                    at,
                } => {
                    (diff_set, context, (at.line, at.col))
                }
                other => panic!("unexpected variant: {other:?}"),
            },
            (
                flags.contains(&"diff"),
                Some(ParseContext::Equation),
                (5, 12)
            ),
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
            when_parsing,
        } => {
            assert_eq!(found.as_deref(), Some(")"));
            assert_eq!(expected, vec!["term".to_string()]);
            assert_eq!(at.line, 5);
            assert_eq!(at.col, 30);
            assert_eq!(when_parsing, ParseContext::TermAtom);
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
            when_parsing,
        } => {
            assert_eq!(found.as_deref(), Some("{~a}~b"));
            assert_eq!(expected, vec!["term".to_string()]);
            assert_eq!(at.line, 5);
            assert_eq!(at.col, 37);
            assert_eq!(when_parsing, ParseContext::TermAtom);
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
        ParseError::Expected {
            found,
            expected,
            at,
            when_parsing,
        } => {
            assert_eq!(found.as_deref(), Some("theary"));
            assert_eq!(expected, vec!["theory".to_string()]);
            assert_eq!(at.line, 1);
            assert_eq!(at.col, 1);
            assert_eq!(at.start, 0);
            assert_eq!(at.end, 6);
            assert_eq!(when_parsing, ParseContext::Theory);
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
        ParseError::Expected {
            found,
            at,
            when_parsing,
            ..
        } => {
            assert_eq!(found.as_deref(), Some("rul"));
            assert_eq!(at.line, 3);
            assert_eq!(at.col, 1);
            assert_eq!(*when_parsing, ParseContext::TheoryItem);
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
        ParseError::Expected {
            found,
            expected,
            at,
            when_parsing,
        } => {
            assert_eq!(found.as_deref(), Some("junk"));
            assert_eq!(expected, vec!["end of input".to_string()]);
            assert_eq!(at.line, 1);
            assert_eq!(at.col, 7);
            assert_eq!(when_parsing, ParseContext::Formula);
        }
        other => panic!("unexpected variant: {other:?}"),
    }
}

#[test]
fn term_trailing_garbage_uses_expected_end_of_input() {
    let e = parse_term_str("x junk", &[]).unwrap_err();
    match e {
        ParseError::Expected {
            found,
            expected,
            at,
            when_parsing,
        } => {
            assert_eq!(found.as_deref(), Some("junk"));
            assert_eq!(expected, vec!["end of input".to_string()]);
            assert_eq!(at.line, 1);
            assert_eq!(at.col, 3);
            assert_eq!(when_parsing, ParseContext::Term);
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
            // Each entry spans its own name and stops at the last character of
            // the lexeme: `hyphen_identifier` replays the word to undo the
            // trailing-whitespace skip `ident` already did, so `signing`'s
            // span ends at 41 (before the space) and not at 42 (`end`).
            let spans = v
                .iter()
                .map(|b| (b.location.col, b.location.start, b.location.end))
                .collect::<Vec<_>>();
            assert_eq!(spans, vec![(26, 25, 32), (35, 34, 41)]);
            assert_eq!(&s[25..32], "hashing");
            assert_eq!(&s[34..41], "signing");
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
            match &l.formula.kind {
                FormulaKind::Forall(vs, _) => assert_eq!(vs.len(), 2),
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

#[test]
fn empty_unterminated_delimiter_reports_the_missing_closer() {
    let error = parse_theory("theory T begin\nmacros: m(\n", &[]).unwrap_err();
    assert!(
        matches!(error, ParseError::UnclosedDelimiter { .. }),
        "expected the missing macro-argument delimiter, got {error:?}"
    );
}

#[test]
fn empty_rule_premise_list_reports_the_unclosed_delimiter() {
    let error = parse_theory("theory T begin rule x: [ --> [] end", &[]).unwrap_err();
    assert!(
        matches!(error, ParseError::UnclosedDelimiter { .. }),
        "expected the missing rule premise-list delimiter, got {error:?}"
    );
}

#[test]
fn term_application() {
    // Structural mode ([`parse_term_str`]'s): a theory parse resolves the
    // head through `lookup_arity` and an undeclared `h` would backtrack
    // to a variable (oracle probes p05/p25 — unknown operators are parse
    // errors upstream).
    match parse_term_str("h(<a, b>, ~k)", &[]).unwrap() {
        Term::App(name, args) => {
            assert_eq!(name, "h");
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
    let f = parse_formula_str("All x. P(x) ==> Q(x)").unwrap();
    match &f.kind {
        FormulaKind::Forall(_, _) => {}
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
    assert!(
        parse_term_str("<>", &[]).is_err(),
        "<> must be a parse error"
    );
    // Singleton tuple collapses to the inner term.
    match parse_term_str("<x>", &[]).unwrap() {
        Term::Var(v) => assert_eq!(v.name, "x"),
        other => panic!("expected singleton to collapse to Var, got {:?}", other),
    }
    // Two-element tuple is a Pair.
    match parse_term_str("<x, y>", &[]).unwrap() {
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
    assert!(!has_casetest(&t));
    let raw = lemma_proof_raw(&t);
    assert!(
        raw.contains("Foo( ~k, $A, %n, k.1, test, rule, function )"),
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
// `option Nothing (colon *> typep)`, so the same text is the msg-sorted `x`
// carrying the SAPIC TYPE `"nat"` (Token.hs:487-510).  `typep`'s `Any` is the
// untyped placeholder.
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
    assert_eq!(
        (v.sort, v.typ.as_deref()),
        (SortHint::Untagged, Some("nat"))
    );
    let v = process_let_binder("theory T begin process: let x:msg = y in 0 end");
    assert_eq!(
        (v.sort, v.typ.as_deref()),
        (SortHint::Untagged, Some("msg"))
    );
    let v = process_let_binder("theory T begin process: let x:Any = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (SortHint::Untagged, None));
    // The `%` PREFIX still sorts a process variable (`lvarNoSuffix` keeps every
    // prefix parser), and a type may follow it.
    let v = process_let_binder(
        "theory T begin builtins: natural-numbers process: let %x:nat = %c in 0 end",
    );
    assert_eq!((v.sort, v.typ.as_deref()), (SortHint::Nat, Some("nat")));

    // Same text in a rule: a sort suffix, no type.
    let thy = parse_theory(
        "theory T begin builtins: natural-numbers rule R: [ In(x:nat) ] --[ ]-> [ ] end",
        &[],
    )
    .expect("parses");
    let mut seen = None;
    for item in &thy.items {
        if let TheoryItem::Rule(r) = item {
            if let Term::Var(v) = &r.premises[0].args[0] {
                seen = Some(v.clone());
            }
        }
    }
    let v = seen.expect("rule premise variable");
    assert_eq!(
        (v.sort, v.typ.as_deref()),
        (SortHint::Suffix(SuffixSort::Nat), None)
    );
}
