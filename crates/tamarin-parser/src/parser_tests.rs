// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

#[test]
fn predicate_diagnostics_space_multiple_annotations() {
    let fact = Fact {
        persistent: false,
        name: "P".into(),
        args: Vec::new(),
        annotations: vec![FactAnnotation::SolveLast, FactAnnotation::SolveFirst],
    };
    assert_eq!(pred_fact_text(&fact), "P( )[+, -]");
}

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

// ---- GHC call-site coordinates, read back out of the pinned source --------
//
// The three `*_SITE` constants below are pasted verbatim into `HasCallStack`
// frames the port must emit byte-for-byte.  Every other test of those frames
// compares the port against bytes captured FROM the port, so all of them agree
// with a stale coordinate; only reading the pinned Haskell notices when a bump
// moves an `error`.

const MACRO_HS: &str =
    include_str!("../../../tamarin-prover/lib/theory/src/Theory/Text/Parser/Macro.hs");
const TERM_HS: &str =
    include_str!("../../../tamarin-prover/lib/theory/src/Theory/Text/Parser/Term.hs");

/// `LINE:COLUMN` of the `error` token on the first line of `hs` holding
/// `needle`, as GHC's `HasCallStack` prints it: both 1-based, the column that
/// of the token itself.
fn error_site(hs: &str, needle: &str) -> String {
    let (idx, line) = hs
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains(needle))
        .unwrap_or_else(|| panic!("no line of the pinned source holds {needle:?}"));
    let col = line
        .match_indices("error")
        .find(|(i, _)| {
            !line[..*i]
                .chars()
                .next_back()
                .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        })
        .map(|(i, _)| line[..i].chars().count() + 1)
        .expect("no `error` token on that line");
    format!("{}:{}", idx + 1, col)
}

#[test]
fn ghc_call_sites_name_the_pinned_error_tokens() {
    assert_eq!(
        Parser::MACRO_RESERVED_NAME_SITE,
        error_site(MACRO_HS, "is a reserved function name for builtins.")
    );
    assert_eq!(
        Parser::MACRO_DUPLICATE_ARG_SITE,
        error_site(MACRO_HS, "have two arguments with the same name.")
    );
    assert_eq!(
        Parser::TERM_RESERVED_NAME_SITE,
        error_site(TERM_HS, "is a reserved function name for builtins.")
    );
}

// ---- parsec frame-rendering port (Text.Parsec.Error) ----

fn pe(source: &str, line: u32, col: u32, messages: Vec<Message>) -> String {
    ParseError::at(
        crate::lexer::Pos {
            offset: 0,
            line,
            col,
        },
        messages,
    )
    .with_source(source)
    .to_string()
}

#[test]
fn structured_expected_notes_prefer_user_tokens_and_deduplicate() {
    let error = ParseError::at(
        crate::lexer::Pos {
            offset: 0,
            line: 1,
            col: 1,
        },
        vec![
            Message::SysUnExpect("\"{\"".into()),
            Message::UnExpect("reserved word \"diff\"".into()),
            Message::Expect("term".into()),
            Message::Expect("term".into()),
        ],
    )
    .with_context(ParseContext::Term);

    assert_eq!(
        error.diagnostic_notes(),
        ["expected term; found reserved word \"diff\"".to_string()]
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
fn frame_sysunexpect_and_expect() {
    // parsec: `unexpected "t"` / `expecting "theory"`.
    let s = pe(
        "f.spthy",
        1,
        1,
        vec![
            Message::SysUnExpect("\"t\"".into()),
            Message::Expect("\"theory\"".into()),
        ],
    );
    assert_eq!(
        s,
        "\"f.spthy\" (line 1, column 1):\nunexpected \"t\"\nexpecting \"theory\""
    );
}

#[test]
fn frame_eof_is_end_of_input() {
    // Empty SysUnExpect string renders as "unexpected end of input".
    let s = pe(
        "f",
        5,
        1,
        vec![
            Message::SysUnExpect(String::new()),
            Message::Expect("\"end\"".into()),
        ],
    );
    assert_eq!(
        s,
        "\"f\" (line 5, column 1):\nunexpected end of input\nexpecting \"end\""
    );
}

#[test]
fn frame_expecting_commas_or() {
    // showMany: `a, b or c` (comma-separated, "or" before the last).
    let s = pe(
        "f",
        4,
        7,
        vec![
            Message::SysUnExpect("\"]\"".into()),
            Message::Expect("\".\"".into()),
            Message::Expect("\",\"".into()),
            Message::Expect("\")\"".into()),
        ],
    );
    assert_eq!(
        s,
        "\"f\" (line 4, column 7):\nunexpected \"]\"\nexpecting \".\", \",\" or \")\""
    );
}

/// A non-binary `[AC]` declaration is HS `function`'s `fail "conflicting
/// arity : AC function must be binary"`
/// (Theory/Text/Parser/Signature.hs:220), raised at the
/// position `lexeme` left after the attribute list.  Byte-pinned to the
/// pinned oracle (ef3f0468), which prints for the two theories below:
///
/// ```text
/// "ac3.spthy" (line 5, column 1):
/// unexpected "r"
/// conflicting arity : AC function must be binary
/// ```
/// ```text
/// "ac5.spthy" (line 3, column 20):
/// unexpected ","
/// conflicting arity : AC function must be binary
/// ```
#[test]
fn non_binary_ac_declaration_is_a_parse_error() {
    let err = parse_theory(
        "theory AC3 begin\n\nfunctions: f/3 [AC]\n\nrule R: [ ] --[ ]-> [ ]\n\nend\n",
        &[],
    )
    .unwrap_err()
    .with_source("ac3.spthy");
    assert_eq!(
        err.to_string(),
        "\"ac3.spthy\" (line 5, column 1):\nunexpected \"r\"\n\
             conflicting arity : AC function must be binary"
    );

    let err = parse_theory("theory AC5 begin\n\nfunctions: f/3 [AC], g/1\n\nend\n", &[])
        .unwrap_err()
        .with_source("ac5.spthy");
    assert_eq!(
        err.to_string(),
        "\"ac5.spthy\" (line 3, column 20):\nunexpected \",\"\n\
             conflicting arity : AC function must be binary"
    );

    // Arity 2 is accepted (and only then does the symbol become infix).
    assert!(parse_theory("theory AC begin\n\nfunctions: f/2 [AC]\n\nend\n", &[]).is_ok());
}

/// A `theory <NAME> begin … end` around a two-line body, the shape of the
/// byte-pinned `builtins:`/`functions:` probes: the body occupies lines 3
/// and 4, so every diagnostic below lands on `end` at line 6, column 1.
fn decl_probe_err(name: &str, body: &str) -> String {
    parse_theory(&format!("theory {name} begin\n\n{body}\n\nend\n"), &[])
        .unwrap_err()
        .with_source("p.spthy")
        .to_string()
}

/// HS `function`'s check (1) (Theory/Text/Parser/Signature.hs:200-209): a
/// name an enabled `builtins:` item reserved must be re-declared at exactly
/// the builtin's `(arity, Privacy, Constructability, NDCstate)` tuple.  It
/// runs BEFORE the conflicting-arities check
/// (Theory/Text/Parser/Signature.hs:212) and before the `[AC]` arity check
/// (Theory/Text/Parser/Signature.hs:220), so its message wins over both.
/// Byte-pinned to the pinned oracle (ef3f0468).
#[test]
fn builtin_reserved_name_check_precedes_the_arity_and_ac_checks() {
    // ```text
    // "b1.spthy" (line 6, column 1):
    // unexpected "e"
    // `h` conflicts with builtin(s) ["hashing"] (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))
    // ```
    // `[AC]` + arity 3 would otherwise be "AC function must be binary".
    assert_eq!(
        decl_probe_err("B1", "builtins: hashing\nfunctions: h/3 [AC]"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             `h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))"
    );
    // Same name declared twice would otherwise be "conflicting arities".
    assert_eq!(
        decl_probe_err("B7", "builtins: hashing\nfunctions: h/1, h/3 [AC]"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             `h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))"
    );
    // `fst` has no exemption in check (1): `dest-pairing` reserves it at
    // the DESTRUCTOR shape, so re-declaring the constructor is an error
    // even though check (2) would wave it through
    // (Theory/Text/Parser/Signature.hs:213).
    assert_eq!(
        decl_probe_err("E1", "builtins: dest-pairing\nfunctions: fst/1 [AC]"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             `fst` conflicts with builtin(s) [\"dest-pairing\"] \
             (builtin: (1,Public,Destructor,NotNDC), requested: (1,Public,Constructor,NotNDC))"
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
            format!(
                "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
                     `h` conflicts with builtin(s) [\"hashing\"] \
                     (builtin: (1,Public,Constructor,NotNDC), requested: {shown})"
            ),
            "attribute {attr}"
        );
    }
    // `conflictingBuiltins` (Theory/Text/Parser/Signature.hs:203) scans the
    // WHOLE table in
    // `builtinsNames` order, not just the builtins this theory enabled.
    assert_eq!(
        decl_probe_err("P6", "builtins: asymmetric-encryption\nfunctions: pk/2"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             `pk` conflicts with builtin(s) [\"asymmetric-encryption\",\"signing\",\
             \"dest-asymmetric-encryption\",\"dest-signing\",\"revealing-signing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (2,Public,Constructor,NotNDC))"
    );
    // The builtin tuple comes from the ENABLED signature, so the two
    // `dest-*` rows report their destructor variants.
    assert_eq!(
        decl_probe_err(
            "P12",
            "builtins: dest-symmetric-encryption\nfunctions: sdec/2"
        ),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             `sdec` conflicts with builtin(s) [\"symmetric-encryption\",\
             \"dest-symmetric-encryption\"] (builtin: (2,Public,Destructor,NotNDC), \
             requested: (2,Public,Constructor,NotNDC))"
    );
    // `locations-report` is the only row with a private symbol and the only
    // one HS lists first.
    assert_eq!(
        decl_probe_err("P9", "builtins: locations-report\nfunctions: rep/2"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             `rep` conflicts with builtin(s) [\"locations-report\"] \
             (builtin: (2,Private,Constructor,NotNDC), requested: (2,Public,Constructor,NotNDC))"
    );
}

/// `option [] $ list functionAttribute`
/// (Theory/Text/Parser/Signature.hs:187) leaves an
/// `Expect "\"[\""` behind when the declaration carries no attribute list,
/// and parsec merges it into the `fail` that follows — so the same
/// diagnostic gains or loses an `expecting "["` line with the brackets.
/// An EMPTY `[]` counts as present.  Byte-pinned to the pinned oracle.
#[test]
fn declaration_diagnostics_carry_the_attribute_bracket_expectation() {
    assert_eq!(
        decl_probe_err("B2", "builtins: hashing\nfunctions: h/1, h/2"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             `h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (2,Public,Constructor,NotNDC))"
    );
    assert_eq!(
        decl_probe_err("P24", "builtins: hashing\nfunctions: h/3 []"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             `h` conflicts with builtin(s) [\"hashing\"] \
             (builtin: (1,Public,Constructor,NotNDC), requested: (3,Public,Constructor,NotNDC))"
    );
}

/// HS `function`'s check (2) (Theory/Text/Parser/Signature.hs:212-216) is a
/// parse error too,
/// not something a later stage reports.  The macro row it can also match
/// registers as `(k, Private, Destructor, NotNDC)`
/// (Theory/Text/Parser/Macro.hs:46).
/// Byte-pinned to the pinned oracle.
#[test]
fn conflicting_arities_is_a_parse_error() {
    // ```text
    // "conf1.spthy" (line 5, column 1):
    // unexpected "e"
    // expecting "["
    // conflicting arities/options (1,Public,Constructor,NotNDC) and (3,Public,Constructor,NotNDC) for `f`. Please choose a different name for this function.
    // ```
    let err = parse_theory("theory CONF1 begin\n\nfunctions: f/1, f/3\n\nend\n", &[])
        .unwrap_err()
        .with_source("conf1.spthy");
    assert_eq!(
        err.to_string(),
        "\"conf1.spthy\" (line 5, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             conflicting arities/options (1,Public,Constructor,NotNDC) and \
             (3,Public,Constructor,NotNDC) for `f`. Please choose a different name \
             for this function."
    );
    // `reliable-channel` has no MaudeSig, so it reserves nothing and the
    // clash between the two user declarations is check (2)'s to report.
    assert_eq!(
        decl_probe_err("P22", "builtins: reliable-channel\nfunctions: h/1, h/2"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             conflicting arities/options (1,Public,Constructor,NotNDC) and \
             (2,Public,Constructor,NotNDC) for `h`. Please choose a different name \
             for this function."
    );
    assert_eq!(
        decl_probe_err("P29", "macros: mh(x, y) = x\nfunctions: mh/2"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\nexpecting \"[\"\n\
             conflicting arities/options (2,Private,Destructor,NotNDC) and \
             (2,Public,Constructor,NotNDC) for `mh`. Please choose a different name \
             for this function."
    );
}

/// HS `extendSig`'s own two checks
/// (Theory/Text/Parser/Signature.hs:107-119), raised at the
/// position the builtin's `symbol` lexeme reached.  Byte-pinned to the
/// pinned oracle.
#[test]
fn builtins_item_rejects_conflicting_functions_and_macros() {
    assert_eq!(
        decl_probe_err("P17", "functions: h/2\nbuiltins: hashing"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             Builtin 'hashing' conflicts with existing function(s) (same name, different \
             arity or function options): [\"h\"]. Please remove these function definitions \
             or use different names."
    );
    assert_eq!(
        decl_probe_err("P28", "macros: h(x) = x\nbuiltins: hashing"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             Builtin 'hashing' conflicts with existing macro '[\"h\"]'"
    );
    // Per-name, in list order: the SECOND builtin sees what the first
    // merged, and the frame sits at the end of that name's lexeme.
    let err = parse_theory(
        "theory P26 begin\n\nbuiltins: symmetric-encryption, dest-symmetric-encryption\n\
             functions: sdec/2\n\nend\n",
        &[],
    )
    .unwrap_err()
    .with_source("p26.spthy");
    assert_eq!(
        err.to_string(),
        "\"p26.spthy\" (line 4, column 1):\nunexpected \"f\"\n\
             Builtin 'dest-symmetric-encryption' conflicts with existing function(s) \
             (same name, different arity or function options): [\"sdec\"]. Please remove \
             these function definitions or use different names."
    );
    // A `dest-*` builtin therefore cannot follow its constructor twin.
    assert_eq!(
        decl_probe_err(
            "P30",
            "builtins: symmetric-encryption, dest-symmetric-encryption\n"
        ),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             Builtin 'dest-symmetric-encryption' conflicts with existing function(s) \
             (same name, different arity or function options): [\"sdec\"]. Please remove \
             these function definitions or use different names."
    );
    assert_eq!(
        decl_probe_err("P31", "builtins: signing, dest-signing\n"),
        "\"p.spthy\" (line 6, column 1):\nunexpected \"e\"\n\
             Builtin 'dest-signing' conflicts with existing function(s) (same name, \
             different arity or function options): [\"verify\"]. Please remove these \
             function definitions or use different names."
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

#[test]
fn theory_options_are_limited_to_the_shared_declarable_set() {
    let all = DeclarableOption::ALL
        .map(DeclarableOption::as_str)
        .join(", ");
    assert!(parse_theory(&format!("theory P begin\noptions: {all}\nend"), &[]).is_ok());

    let err = parse_theory("theory P begin\noptions: unknown-option\nend", &[])
        .expect_err("unknown option must fail");
    assert_eq!(
        err.to_string(),
        "(line 2, column 10):\nunexpected \"u\"\nexpecting \
         \"translation-progress\", \"translation-allow-pattern-lookups\", \
         \"translation-state-optimisation\", \"translation-asynchronous-channels\" or \
         \"translation-compress-events\""
    );

    let err = parse_theory("theory P begin\noptions: translation-progressx\nend", &[])
        .expect_err("a valid option prefix must leave its suffix to the outer parser");
    assert_eq!(
        err.to_string(),
        "(line 2, column 31):\nunexpected \"\\n\"\nexpecting letter or \"{*\""
    );
}

/// HS `T.identifier` (Token.hs:393-394) rejects the reserved names
/// `["in","let","rule","diff"]` (Token.hs:214-230, see line 225) with an
/// `unexpected reserved word "…"` whose position is the word's end — the
/// lexeme's trailing whitespace never runs — merged with the
/// `Expect "letter or digit"` `ident`'s `many identLetter` left there.
/// Byte-pinned to the pinned oracle on each declaration position below.
#[test]
fn reserved_word_at_a_declaration_position() {
    // ```text
    // "d5.spthy" (line 4, column 16):
    // unexpected reserved word "diff"
    // expecting letter or digit
    // ```
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
        let err = parse_theory(src, &[]).unwrap_err().with_source("r.spthy");
        assert_eq!(
            err.to_string(),
            format!(
                "\"r.spthy\" (line {line}, column {col}):\n\
                     unexpected reserved word \"{word}\"\nexpecting letter or digit"
            ),
            "source: {src:?}"
        );
    }
    // A word that merely STARTS with a reserved name is an identifier.
    assert!(parse_theory("theory D\nbegin\n\nfunctions: diffuse/2\n\nend\n", &[]).is_ok());

    // An enclosing `<?>` on a non-consuming failure keeps the `UnExpect`
    // and swaps the `Expect`s for its own label — HS `predicate … <?>
    // "predicate declaration"` (Theory/Text/Parser/Signature.hs:270-275):
    // ```text
    // "r8.spthy" (line 3, column 17):
    // unexpected reserved word "diff"
    // expecting predicate declaration
    // ```
    let err = parse_theory(
        "theory R8 begin\n\npredicates: diff(x) <=> x = x\n\nend\n",
        &[],
    )
    .unwrap_err()
    .with_source("r8.spthy");
    assert_eq!(
        err.to_string(),
        "\"r8.spthy\" (line 3, column 17):\nunexpected reserved word \"diff\"\n\
             expecting predicate declaration"
    );
}

/// Parsec carries a consumed-ok parse's error forward and merges it
/// into whatever the continuation reports at the same position, so the
/// trailing optional parsers of the item just parsed PREPEND their labels
/// to the item-position error.  Byte-pinned to the pinned oracle on the
/// three items this port tracks.
#[test]
fn item_position_error_carries_the_previous_items_trailing_labels() {
    let base = "\"pe.spthy\" (line 5, column 1):\nunexpected end of input\nexpecting ";
    let items = "\"heuristic\", \"tactic\", \"builtins\", \"options\", \"functions\", \
                     \"function\", \"equations\", \"macros\", \"restriction\", \"axiom\", \
                     \"test\", \"lemma\", \"rule\", letter, top-level process, \"let\", \
                     \"equivLemma\", \"diffEquivLemma\", predicate block, export block, \
                     \"#ifdef\", \"#define\", \"#include\" or \"end\"";
    let err = |body: &str| {
        parse_theory(&format!("theory PE begin\n\n{body}\n\n"), &[])
            .unwrap_err()
            .with_source("pe.spthy")
            .to_string()
    };
    // `protoRule`'s `option [] $ symbol "variants" *> …`
    // (Theory/Text/Parser/Rule.hs:134).
    assert_eq!(
        err("rule R: [ ] --[ ]-> [ ]"),
        format!("{base}\"variants\", {items}")
    );
    // `commaSep1`'s trailing `comma` after a `builtins:` list.
    assert_eq!(err("builtins: hashing"), format!("{base}\",\", {items}"));
    // Both `option [] $ list functionAttribute` and the trailing `comma`
    // after a `functions:` list — unless the last declaration bracketed
    // its attributes, which consumes the `[`.
    assert_eq!(
        err("functions: f/2, g/1"),
        format!("{base}\"[\", \",\", {items}")
    );
    assert_eq!(
        err("functions: f/2, g/2 [AC]"),
        format!("{base}\",\", {items}")
    );
    // The labels are pinned to the offset the item stopped at: a following
    // item resets them, and `formalComment`'s `many1 letter` moves the
    // error past them.
    assert_eq!(
        parse_theory(
            "theory PE begin\n\nrule R: [ ] --[ ]-> [ ]\nbuiltins: hashing\n\n",
            &[]
        )
        .unwrap_err()
        .with_source("pe.spthy")
        .to_string(),
        "\"pe.spthy\" (line 6, column 1):\nunexpected end of input\nexpecting \",\", ".to_string()
            + items
    );
}

/// The theory of the byte-pinned `diff` probes: a `diff(a, b)` in a rule's
/// conclusion.  `$ARGS` is substituted with the argument list under test.
fn diff_probe(args: &str) -> String {
    format!(
        "theory D\nbegin\n\nbuiltins: diffie-hellman\n\nrule RA:\n  \
             [ Fr(~a), Fr(~b) ] --[ Go( 'a' ) ]-> [ Out( diff({args}) ) ]\n\nend\n"
    )
}

fn diff_probe_err(args: &str, flags: &[&str]) -> String {
    parse_theory(&diff_probe(args), flags)
        .unwrap_err()
        .with_source("d.spthy")
        .to_string()
}

/// HS `diffOp` (Theory/Text/Parser/Term.hs:123-135) parses `diff(...)`
/// unconditionally and then
/// `fail`s unless the signature's diff bit is on, so a `diff` term in a
/// theory parsed without the flag is a parse error — not an ordinary user
/// function.  Byte-pinned to the pinned oracle (ef3f0468) on the probes in
/// this test; the three `fail`s fire in HS's order (arity, then equations,
/// then flag), and `term`'s `<?> "term"`
/// (Theory/Text/Parser/Term.hs:138-163, see line 154)
/// supplies the `expecting term` line.
#[test]
fn diff_operator_without_the_diff_flag_is_a_parse_error() {
    // ```text
    // "d.spthy" (line 7, column 65):
    // unexpected ")"
    // expecting term
    // diff operator found, but flag diff not set
    // ```
    assert_eq!(
        diff_probe_err("(~a*~b), ~a", &[]),
        "\"d.spthy\" (line 7, column 65):\nunexpected \")\"\nexpecting term\n\
             diff operator found, but flag diff not set"
    );

    // The arity check runs FIRST and hides the flag diagnostic, with or
    // without the flag.  `commaSep = flip sepEndBy comma` (Token.hs:353-355)
    // parses the empty and the over-long list happily, so all three counts
    // reach the same `fail`.
    for args in ["~a", "~a, ~b, ~a", ""] {
        let expected_col = 47 + args.len() + 7;
        for flags in [&[][..], &["diff"][..]] {
            assert_eq!(
                diff_probe_err(args, flags),
                format!(
                    "\"d.spthy\" (line 7, column {expected_col}):\nunexpected \")\"\n\
                         expecting term\nthe diff operator requires exactly 2 arguments"
                ),
                "args = {args:?}, flags = {flags:?}"
            );
        }
    }

    // Nested: the INNER `diff` fails first, and its position (after the inner
    // closing paren, at the outer comma) is the one parsec reports.
    assert_eq!(
        diff_probe_err("diff(~a, ~b), ~b", &[]),
        "\"d.spthy\" (line 7, column 64):\nunexpected \",\"\nexpecting term\n\
             diff operator found, but flag diff not set"
    );
}

/// `equations:` parses with HS's `eqn` flag set, where `diffOp`'s second
/// `fail` fires ahead of the flag check — again with or without the flag.
#[test]
fn diff_operator_is_rejected_in_equations() {
    for flags in [&[][..], &["diff"][..]] {
        let err = parse_theory(
            "theory D\nbegin\n\nfunctions: f/1, g/1\nequations: diff(x, x) = x\n\n\
                 rule RA:\n  [ Fr(~a) ] --> [ Out( ~a ) ]\n\nend\n",
            flags,
        )
        .unwrap_err()
        .with_source("d.spthy");
        assert_eq!(
            err.to_string(),
            "\"d.spthy\" (line 5, column 23):\nunexpected \"=\"\nexpecting term\n\
                 diff operator not allowed in equations",
            "flags = {flags:?}"
        );
    }
}

/// `diff` not followed by `(`: `diffOp`'s `parens` fails and no other `term`
/// alternative accepts a reserved word.  The reserved-word `UnExpect` of
/// `identifier` (Token.hs:393-394) sits before the lexeme's trailing
/// whitespace and the `parens` `SysUnExpect` after it, so parsec reports
/// only the latter when they are separated and both when they coincide.
#[test]
fn bare_diff_token_is_a_parse_error() {
    let err = parse_theory(
        "theory D\nbegin\n\nrule RA:\n  [ Fr(~a) ] --> [ Out( diff ) ]\n\nend\n",
        &[],
    )
    .unwrap_err()
    .with_source("d.spthy");
    assert_eq!(
        err.to_string(),
        "\"d.spthy\" (line 5, column 30):\nunexpected \")\"\nexpecting term"
    );

    let err = parse_theory(
        "theory D\nbegin\n\nrule RA:\n  [ Fr(~a), Fr(~b) ] --> [ Out( diff{~a}~b ) ]\n\nend\n",
        &[],
    )
    .unwrap_err()
    .with_source("d.spthy");
    assert_eq!(
        err.to_string(),
        "\"d.spthy\" (line 5, column 37):\nunexpected reserved word \"diff\"\nexpecting term"
    );
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
fn frame_dedup_and_message_ordering() {
    // clean = nub . filter (not . null): duplicate/empty Expects collapse,
    // and sort orders SysUnExpect < Expect < Message regardless of input.
    let s = pe(
        "f",
        2,
        3,
        vec![
            Message::Message("raw note".into()),
            Message::Expect("\"a\"".into()),
            Message::Expect("\"a\"".into()),
            Message::Expect(String::new()),
            Message::SysUnExpect("\"x\"".into()),
        ],
    );
    assert_eq!(
        s,
        "\"f\" (line 2, column 3):\nunexpected \"x\"\nexpecting \"a\"\nraw note"
    );
}

#[test]
fn frame_sysunexpect_suppressed_by_unexpect() {
    // showSysUnExpect = "" when a user UnExpect is present.
    let s = pe(
        "f",
        1,
        1,
        vec![
            Message::SysUnExpect("\"z\"".into()),
            Message::UnExpect("something".into()),
            Message::Expect("\"a\"".into()),
        ],
    );
    assert_eq!(
        s,
        "\"f\" (line 1, column 1):\nunexpected something\nexpecting \"a\""
    );
}

#[test]
fn frame_empty_messages_is_unknown() {
    // parsec: `| null msgs = msgUnknown` — no leading newline.
    let s = pe("f", 1, 1, vec![]);
    assert_eq!(s, "\"f\" (line 1, column 1):unknown parse error");
}

#[test]
fn frame_null_source_omits_quoted_name() {
    // `instance Show SourcePos`: null name → no `"name" ` prefix.
    let s = pe("", 3, 2, vec![Message::Message("m".into())]);
    assert_eq!(s, "(line 3, column 2):\nm");
}

#[test]
fn show_char_token_escapes_like_haskell() {
    assert_eq!(show_char_token('t'), "\"t\"");
    assert_eq!(show_char_token(' '), "\" \"");
    assert_eq!(show_char_token('"'), "\"\\\"\"");
    assert_eq!(show_char_token('\n'), "\"\\n\"");
    assert_eq!(show_char_token('\t'), "\"\\t\"");
}

/// GHC `show :: String -> String` over a whole string: the named control
/// escapes, a decimal escape for a character above `\DEL`, and the `\&`
/// separator before a digit that would otherwise extend that escape.
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
fn theory_keyword_error_matches_parsec() {
    // End-to-end: the top-level `theory` keyword mismatch renders exactly
    // like HS's `symbol_ "theory"` failure.
    let e = parse_theory("theary Foo\nbegin\nend\n", &[]).unwrap_err();
    assert_eq!(
        e.with_source("f.spthy").to_string(),
        "\"f.spthy\" (line 1, column 1):\nunexpected \"t\"\nexpecting \"theory\""
    );
}

#[test]
fn item_position_letters_expect_letter_or_comment() {
    // Garbage identifier at item position → `letter or "{*"` after the
    // consumed letters (formalComment `many1 letter <* string "{*"`).
    let e = parse_theory("theory Foo\nbegin\nrul R:\n[]-->[]\nend\n", &[]).unwrap_err();
    assert_eq!(
        e.with_source("f").to_string(),
        "\"f\" (line 3, column 4):\nunexpected \" \"\nexpecting letter or \"{*\""
    );
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
fn fatom_keeps_a_valid_fact_when_term_reinterpretation_fails() {
    let source = "theory T begin\nlemma L: \"Foo(x) = y\"\nend\n";
    let error = parse_theory(source, &[]).expect_err("a predicate cannot precede equality");
    assert!(
        !matches!(error.kind(), ParseErrorKind::UndeclaredFunction { .. }),
        "the successful Foo(x) fact parse must outrank term reinterpretation: {error:?}"
    );
    assert!(source[error.span().start..].starts_with('='));
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
    assert!(error.messages_truncated);
    assert!(error
        .diagnostic_notes()
        .iter()
        .any(|note| note == OMITTED_MESSAGES));
    assert!(!error
        .diagnostic_notes()
        .iter()
        .any(|note| note.starts_with("expected ") && note.contains(OMITTED_MESSAGES)));
    let rendered = error.to_string();
    assert!(rendered.contains(OMITTED_MESSAGES), "{rendered}");
    assert!(
        rendered.contains("Conflicting name for macro m"),
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
fn item_position_hangovers_respect_the_message_limit() {
    let declarations = (0..200)
        .map(|index| format!("f{index}/2 [AC]"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!("theory T begin\nfunctions: {declarations}\nequations: x = y\n@\nend");

    let error = parse_theory(&source, &[]).expect_err("junk at item position must fail");

    assert!(error.messages.len() <= MAX_DIAGNOSTIC_MESSAGES);
    assert!(error.messages_truncated);
    assert!(error.to_string().contains(OMITTED_MESSAGES), "{error}");
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
        .map(|index| Message::UnExpect(format!("cause {index}")))
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
fn tactic_blocks_require_a_selector() {
    for block in ["prio:", "deprio: {id}"] {
        let src = format!("theory T begin\ntactic: rank\n{block}\nrule R: [ ] --> [ ]\nend");
        let err = parse_theory(&src, &[]).expect_err("empty tactic block must fail");
        assert_eq!(
            err.to_string(),
            "(line 4, column 5):\nunexpected reserved word \"rule\"\nexpecting letter or digit"
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
