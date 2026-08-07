// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pinned parity for the lowercase-fact-name rejection.
//!
//! HS `fact'` (Fact.hs:39-50, see line 46) raises `fail "facts must start
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

/// A lowercase fact in a rule premise: the fail sits at the char right after
/// the name (the `(`), with the identifier's pending label merged in.
#[test]
fn lowercase_fact_in_premise() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ foo(x) ] --> [ ]\n\nend\n"),
        "\"fact.spthy\" (line 3, column 14):\n\
         unexpected \"(\"\n\
         expecting letter or digit\n\
         facts must start with upper-case letters"
    );
}

/// The same in a conclusion.
#[test]
fn lowercase_fact_in_conclusion() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ ] --> [ foo('a') ]\n\nend\n"),
        "\"fact.spthy\" (line 3, column 22):\n\
         unexpected \"(\"\n\
         expecting letter or digit\n\
         facts must start with upper-case letters"
    );
}

/// The same in an action.
#[test]
fn lowercase_fact_in_action() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ ] --[ foo('a') ]-> [ ]\n\nend\n"),
        "\"fact.spthy\" (line 3, column 20):\n\
         unexpected \"(\"\n\
         expecting letter or digit\n\
         facts must start with upper-case letters"
    );
}

/// A persistent lowercase fact behaves the same (the `!` parses first).
#[test]
fn lowercase_persistent_fact() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ !foo(x) ] --> [ ]\n\nend\n"),
        "\"fact.spthy\" (line 3, column 15):\n\
         unexpected \"(\"\n\
         expecting letter or digit\n\
         facts must start with upper-case letters"
    );
}

/// Whitespace between the name and the next token discards the pending
/// `letter or digit` label — the fail reports at the token after the space.
#[test]
fn whitespace_after_name_drops_the_letter_label() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ foo (x) ] --> [ ]\n\nend\n"),
        "\"fact.spthy\" (line 3, column 15):\n\
         unexpected \"(\"\n\
         facts must start with upper-case letters"
    );
}

/// A bare lowercase name before `]` likewise.
#[test]
fn bare_lowercase_name_before_bracket() {
    assert_eq!(
        err("theory T begin\n\nrule R: [ foo ] --> [ ]\n\nend\n"),
        "\"fact.spthy\" (line 3, column 15):\n\
         unexpected \"]\"\n\
         facts must start with upper-case letters"
    );
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
