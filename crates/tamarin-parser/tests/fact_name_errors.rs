// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for the lowercase-fact-name rejection.
//!
//! HS `fact'` (Parser/Fact.hs:39-50, see line 46) raises `fail "facts must start
//! with upper-case letters"` right after `identifier` consumed the name.  The
//! identifier lexeme's pending empty error — `SysUnExpect` of the next char
//! plus `alphaNum`'s `Expect "letter or digit"` — merges into the fail when
//! the lexeme's trailing whiteSpace consumed nothing; whitespace after the
//! name discards the label.  Every expected string below is the stderr the
//! pinned Haskell oracle (Git revision ef3f0468) prints for the same theory,
//! minus the three `maude tool:` banner lines.
//!
//! In FORMULA context the whole `fact'` sits under `try … <?> "fact"` and the
//! atom alternation falls through to the term-relational atoms, so the fact
//! message never surfaces there (the oracle reports the term path's merged
//! labels instead: `unexpected "(" / expecting letter or digit, "." or "="`).
//! That residual formula-path shape is not pinned here — RS's formula-atom
//! error machinery reports its own `expected formula atom` frame.

use tamarin_parser::parse_theory;

/// The parse error for `src`, rendered as HS's `show err` with `fact.spthy`
/// as the `SourcePos` name.
fn err(src: &str) -> String {
    parse_theory(src, &[])
        .unwrap_err()
        .with_source("fact.spthy")
        .to_string()
}

/// Every rule position routes through the one `fact'`.  The error therefore
/// reports at the character right after the name, that is the `(`.  The
/// pending label of the identifier merges into that error.  This holds
/// wherever the fact stands, and whether or not the fact is persistent,
/// because the `!` parses before the name.
#[test]
fn a_lowercase_fact_fails_at_the_paren_in_every_rule_position() {
    for (case, src, col) in [
        ("premise", "rule R: [ foo(x) ] --> [ ]", 14),
        ("conclusion", "rule R: [ ] --> [ foo('a') ]", 22),
        ("action", "rule R: [ ] --[ foo('a') ]-> [ ]", 20),
        ("persistent premise", "rule R: [ !foo(x) ] --> [ ]", 15),
    ] {
        assert_eq!(
            err(&format!("theory T begin\n\n{src}\n\nend\n")),
            format!(
                "\"fact.spthy\" (line 3, column {col}):\n\
                 unexpected \"(\"\n\
                 expecting letter or digit\n\
                 facts must start with upper-case letters"
            ),
            "case {case}"
        );
    }
}

/// Whitespace between the name and the next token discards the pending
/// `letter or digit` label.  The error then reports at the token after the
/// space, whatever that token is.
#[test]
fn whitespace_after_the_name_drops_the_letter_label() {
    for (case, src, unexpected) in [
        ("argument list", "rule R: [ foo (x) ] --> [ ]", "\"(\""),
        ("bare name", "rule R: [ foo ] --> [ ]", "\"]\""),
    ] {
        assert_eq!(
            err(&format!("theory T begin\n\n{src}\n\nend\n")),
            format!(
                "\"fact.spthy\" (line 3, column 15):\n\
                 unexpected {unexpected}\n\
                 facts must start with upper-case letters"
            ),
            "case {case}"
        );
    }
}

/// The ordering case that exposed the divergence: a rule whose conclusion
/// bracket is left open swallows the following `macros:` keyword as a fact
/// name — the fail sits at the `:` right after `macros`, label intact.
#[test]
fn macros_keyword_after_open_bracket_is_a_fact_name() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ ] --> [\nmacros:\nm() = 'a'\n\nend\n"),
        "\"fact.spthy\" (line 4, column 7):\n\
         unexpected \":\"\n\
         expecting letter or digit\n\
         facts must start with upper-case letters"
    );
}
