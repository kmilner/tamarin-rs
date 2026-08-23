// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

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
    ParseError {
        line,
        col,
        offset: 0,
        source: source.to_string(),
        messages,
        ghc_error: None,
    }
    .to_string()
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
    let f = parse_formula_str("Foo(x) = Foo(y)").unwrap();
    match f {
        Formula::Atom(Atom::Eq(Term::App(l, _), Term::App(r, _))) => {
            assert_eq!(l, "Foo");
            assert_eq!(r, "Foo");
        }
        other => panic!("expected Eq(App,App), got {:?}", other),
    }
    // Subterm: `A(x) << B(y)` must be Atom::Subterm, not Pred.
    let f = parse_formula_str("A(x) << B(y)").unwrap();
    match f {
        Formula::Atom(Atom::Subterm(Term::App(l, _), Term::App(r, _))) => {
            assert_eq!(l, "A");
            assert_eq!(r, "B");
        }
        other => panic!("expected Subterm(App,App), got {:?}", other),
    }
    // A genuine predicate atom (no following relational op) stays Pred.
    let f = parse_formula_str("P(x) & Q(y)").unwrap();
    match f {
        Formula::And(a, _) => match *a {
            Formula::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
            ref other => panic!("expected Pred, got {:?}", other),
        },
        other => panic!("expected And, got {:?}", other),
    }
    // Implication after a predicate must NOT be misread as `=` (==> guard).
    let f = parse_formula_str("P(x) ==> Q(y)").unwrap();
    match f {
        Formula::Implies(a, _) => match *a {
            Formula::Atom(Atom::Pred(ref fa)) => assert_eq!(fa.name, "P"),
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
    assert_eq!((v.sort, v.typ.as_deref()), (SortHint::Msg, Some("nat")));
    let v = process_let_binder("theory T begin process: let x:msg = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (SortHint::Msg, Some("msg")));
    let v = process_let_binder("theory T begin process: let x:Any = y in 0 end");
    assert_eq!((v.sort, v.typ.as_deref()), (SortHint::Msg, None));
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
    assert_eq!((v.sort, v.typ.as_deref()), (SortHint::Nat, None));
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
fn tuple_var_specs(t: &Term) -> Vec<(&str, u64, SortHint)> {
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
            ("x", 0, SortHint::Msg),
            ("x", 1, SortHint::Msg),
            ("f", 0, SortHint::Fresh),
            ("p", 0, SortHint::Pub),
            ("i", 0, SortHint::Node),
            ("n", 0, SortHint::Nat),
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
            ("x", 0, SortHint::Msg),
            ("x", 0, SortHint::Fresh),
            ("x", 0, SortHint::Pub),
            ("x", 0, SortHint::Node),
            ("x", 0, SortHint::Nat),
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
    let sort_of = |src: &str| -> Vec<SortHint> {
        match parse_formula_str(src).expect("parses") {
            Formula::Atom(Atom::Action(_, t)) | Formula::Atom(Atom::Last(t)) => {
                vec![var_of(&t).sort]
            }
            Formula::Atom(Atom::Less(l, r)) | Formula::Atom(Atom::Eq(l, r)) => {
                vec![var_of(&l).sort, var_of(&r).sort]
            }
            other => panic!("expected one atom, got {other:?}"),
        }
    };
    assert_eq!(sort_of("A(x) @ i"), vec![SortHint::Node]);
    assert_eq!(sort_of("last(i)"), vec![SortHint::Node]);
    assert_eq!(sort_of("i < j"), vec![SortHint::Node, SortHint::Node]);
    assert_eq!(sort_of("#k = l"), vec![SortHint::Node, SortHint::Node]);
    assert_eq!(sort_of("k:node = l"), vec![SortHint::Node, SortHint::Node]);
    // The "term equality" alternative reads both operands with `msgvar`, so
    // two bare names are message variables.
    assert_eq!(sort_of("k = l"), vec![SortHint::Msg, SortHint::Msg]);
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
    let f = parse_formula_str(
        "All A B seq1 seq2 #i #j.(Seq_Sent(A, B, seq1) @ #i \
         & Seq_Sent(A, B, seq2) @ #j & #i < #j ==> Ex dif. seq2 = seq1 + dif )",
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
        ("dif", 0, SortHint::Msg)
    );
    let Formula::Atom(Atom::Eq(_, sum)) = eq.as_ref() else {
        panic!("expected an equality, got {eq:?}");
    };
    let Term::BinOp(BinOp::Union, l, r) = sum else {
        panic!("expected a multiset union, got {sum:?}");
    };
    assert_eq!(var_of(l).sort, SortHint::Msg);
    assert_eq!(var_of(r).sort, SortHint::Msg);
}
