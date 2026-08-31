// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Structured tactics and their pretty-printing.
//!
//! Mirrors the Haskell reference:
//!   - data type:  `Theory.Constraint.System.Tactic / Prio / Deprio`
//!     (lib/theory/src/Theory/Constraint/System.hs:439-504)
//!   - parser:     `Theory.Text.Parser.Tactics`
//!     (lib/theory/src/Theory/Text/Parser/Tactics.hs:60-115)
//!   - pretty:     `prettyTactic` (lib/theory/src/TheoryObject.hs:924-942)
//!
//! Tactics are parsed directly into [`Tactic`] by `tamarin-parser`; this
//! module evaluates and renders that shared representation.

pub use tamarin_parser::{PrioBlock, SelectorExpr, SelectorLeaf, Tactic};

/// Render via the ported HS `prettyTactic` (TheoryObject.hs:924-942).
pub fn render(tactic: &Tactic) -> String {
    let mut out = String::new();
    out.push_str("tactic: ");
    out.push_str(&tactic.name);
    out.push('\n');
    out.push_str("presort: ");
    out.push(tactic.presort);
    for block in &tactic.prios {
        out.push('\n');
        out.push_str(&render_block("prio", block));
    }
    for block in &tactic.deprios {
        out.push('\n');
        out.push_str(&render_block("deprio", block));
    }
    out
}

/// `ppTab` for one block: `<kw>: {ranking}` $-$ nest-2 prettified lines.
fn render_block(kw: &str, b: &PrioBlock) -> String {
    let mut out = String::new();
    out.push_str(kw);
    out.push_str(": {");
    out.push_str(&b.ranking);
    out.push('}');
    for selector in &b.selectors {
        out.push('\n');
        out.push_str("  ");
        render_selector(&mut out, selector);
    }
    out
}

/// Render a parsed selector in the canonical form produced by HS
/// `prettify` (TheoryObject.hs:947-952).
fn render_selector(out: &mut String, selector: &SelectorExpr) {
    let mut raw = String::new();
    render_selector_raw(&mut raw, selector);
    for word in raw.split_whitespace() {
        match word {
            "|" => out.push_str(" | "),
            "&" => out.push_str(" & "),
            "not" => out.push_str("not "),
            _ => out.push_str(word),
        }
    }
}

/// Rebuild the selector text stored by HS's tactic parser before `prettify`.
fn render_selector_raw(out: &mut String, selector: &SelectorExpr) {
    match selector {
        SelectorExpr::Leaf(leaf) => {
            out.push_str(&leaf.name);
            for param in &leaf.params {
                out.push_str(" \"");
                out.push_str(param);
                out.push('"');
            }
        }
        SelectorExpr::Not(expr) => {
            out.push_str("not ");
            render_selector_raw(out, expr);
        }
        SelectorExpr::And(left, right) => {
            render_selector_raw(out, left);
            out.push_str(" & ");
            render_selector_raw(out, right);
        }
        SelectorExpr::Or(left, right) => {
            render_selector_raw(out, left);
            out.push_str(" | ");
            render_selector_raw(out, right);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(name: &str, body: &str) -> Tactic {
        let source = format!("theory T begin\ntactic: {name}\n{body}\nend");
        tamarin_parser::parse_theory(&source, &[])
            .expect("tactic parses")
            .items
            .into_iter()
            .find_map(|item| match item {
                tamarin_parser::TheoryItem::Tactic(tactic) => Some(tactic),
                _ => None,
            })
            .expect("tactic item")
    }

    #[test]
    fn parses_and_renders_noise_unless() {
        let raw = "presort: s\n\
prio: {id}\n\
  regex\"^My\"\n\
  regex\"^I_\"\n\
prio: {id}\n\
  regex\"!KU\\(*~.*\\)\" & reasonableNoncesNoise\"resN\"\n\
prio: {smallest}\n\
  dhreNoise\"dh\"\n";
        let t = parse("unless", raw);
        assert_eq!(t.presort, 's');
        assert_eq!(t.prios.len(), 3);
        let r = render(&t);
        let expected = concat!(
            "tactic: unless\n",
            "presort: s\n",
            "prio: {id}\n",
            "  regex\"^My\"\n",
            "  regex\"^I_\"\n",
            "prio: {id}\n",
            "  regex\"!KU\\(*~.*\\)\" & reasonableNoncesNoise\"resN\"\n",
            "prio: {smallest}\n",
            "  dhreNoise\"dh\"",
        );
        assert_eq!(r, expected);
    }

    #[test]
    fn collapses_internal_regex_spaces_and_or_chain() {
        // LAK06-style: `|regex` with no trailing space, internal regex spaces.
        let raw = "presort: s\n\
prio:\n\
  regex \".*!K.\\( \\(.*~r0\\.1.*\" |regex \".*!K.\\( \\(.*~r0.*\" | regex \".*!K.\\( ~r.*\"\n";
        let t = parse("helping", raw);
        assert_eq!(t.prios.len(), 1);
        assert_eq!(t.prios[0].ranking, "id");
        let r = render(&t);
        assert_eq!(
            r,
            "tactic: helping\npresort: s\nprio: {id}\n  \
             regex\".*!K.\\(\\(.*~r0\\.1.*\" | \
             regex\".*!K.\\(\\(.*~r0.*\" | \
             regex\".*!K.\\(~r.*\""
        );
    }

    #[test]
    fn selector_rendering_preserves_prettify_boundaries() {
        let raw = "prio:\n  regex \"not a | b not c & d\"\n";
        assert_eq!(
            render(&parse("x", raw)),
            "tactic: x\npresort: s\nprio: {id}\n  regex\"nota | bnot c & d\""
        );
    }

    #[test]
    fn selector_rendering_preserves_quoted_boundary_whitespace() {
        let raw = "prio:\n  regex \" | \" \" & \" \" not \"\n";
        assert_eq!(
            render(&parse("x", raw)),
            "tactic: x\npresort: s\nprio: {id}\n  regex\" | \"\" & \"\"not \""
        );
    }

    #[test]
    fn prio_and_deprio() {
        let raw = "presort: s\n\
prio:\n\
  regex \".*!Tag\\(.*\"\n\
deprio:\n\
  regex \".*TagK\\(.*\"\n";
        let t = parse("x", raw);
        assert_eq!(t.prios.len(), 1);
        assert_eq!(t.deprios.len(), 1);
        let r = render(&t);
        assert_eq!(
            r,
            "tactic: x\npresort: s\nprio: {id}\n  regex\".*!Tag\\(.*\"\ndeprio: {id}\n  regex\".*TagK\\(.*\""
        );
    }

    /// Locks the corpus-relevant presort chars (`C`, `c`, `s`) which
    /// round-trip identically through `goalRankingToChar` (System.hs:649-651).
    #[test]
    fn presort_char_round_trips() {
        let t = parse("x", "presort: C\nprio:\n  regex \"a\"\n");
        assert_eq!(t.presort, 'C');
        let t = parse("x", "presort: c\nprio:\n  regex \"a\"\n");
        assert_eq!(t.presort, 'c');
        // Default (no presort) is SmartRanking False -> 's' (Tactics.hs:109-115, see line 112).
        let t = parse("x", "prio:\n  regex \"a\"\n");
        assert_eq!(t.presort, 's');
    }

    /// HS opLAnd/opLOr/opLNot accept the Unicode spellings ∧/∨/¬ in a tactic
    /// body (Token.hs:596-604) and render them as canonical ASCII ` & `/` | `/
    /// `not ` (Tactics.hs:73-79). Verified against the HS prover v1.13.0: a
    /// `regex "a" ∧ regex "b"` block prints `regex"a" & regex"b"`, etc.
    #[test]
    fn accepts_unicode_operators() {
        let raw = "presort: C\n\
prio:\n\
  regex \"a\" \u{2227} regex \"b\"\n\
prio:\n\
  regex \"c\" \u{2228} regex \"d\"\n\
prio:\n\
  \u{00AC} regex \"e\"\n";
        let t = parse("mytac", raw);
        assert_eq!(t.prios.len(), 3);
        // Structure mirrors the ASCII spellings.
        assert!(matches!(t.prios[0].selectors[0], SelectorExpr::And(_, _)));
        assert!(matches!(t.prios[1].selectors[0], SelectorExpr::Or(_, _)));
        assert!(matches!(t.prios[2].selectors[0], SelectorExpr::Not(_)));
        // Rendered with canonical ASCII operators, byte-identical to HS.
        let r = render(&t);
        assert_eq!(
            r,
            "tactic: mytac\npresort: C\n\
prio: {id}\n  regex\"a\" & regex\"b\"\n\
prio: {id}\n  regex\"c\" | regex\"d\"\n\
prio: {id}\n  not regex\"e\""
        );
    }

    /// HS spthy `identLetter` excludes `.` (Token.hs:214-230, see line 224), so a function name
    /// containing `.` is not tokenized as one identifier: HS parses `foo` then
    /// requires a `"` and rejects the `.` (confirmed against the HS prover:
    /// `unexpected "." expecting letter or digit or """`). The Rust parser
    /// likewise stops the function name at `.`, leaving invalid input for the
    /// enclosing theory parser to reject.
    #[test]
    fn dot_is_not_an_ident_letter() {
        let source = "theory T begin\ntactic: x\nprio:\n  foo.bar \"a\"\nend";
        assert!(tamarin_parser::parse_theory(source, &[]).is_err());
        // A dot-free name parses normally.
        let t = parse("x", "prio:\n  regex \"a\"\n");
        assert_eq!(t.prios[0].selectors.len(), 1);
        assert!(matches!(
            t.prios[0].selectors[0],
            SelectorExpr::Leaf(ref l) if l.name == "regex"
        ));
    }
}
