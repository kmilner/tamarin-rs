// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Structured tactics and their pretty-printing.
//!
//! Mirrors the Haskell reference:
//!   - data type:  `Theory.Constraint.System.Tactic / Prio / Deprio`
//!     (lib/theory/src/Theory/Constraint/System.hs)
//!   - parser:     `Theory.Text.Parser.Tactics`
//!     (lib/theory/src/Theory/Text/Parser/Tactics.hs)
//!   - pretty:     `prettyTactic` (lib/theory/src/TheoryObject.hs)
//!
//! Tactics are parsed directly into [`Tactic`] by `tamarin-parser`; this
//! module renders that shared representation.

pub use tamarin_parser::{PrioBlock, SelectorExpr, SelectorLeaf, Tactic};

/// Render via the ported HS `prettyTactic` (TheoryObject.hs).
pub fn render(tactic: &Tactic) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    hpj::vcat(vec![
        hpj::keyword_("tactic").beside(Doc::text(format!(": {}", tactic.name))),
        hpj::keyword_("presort").beside(Doc::text(format!(": {}", tactic.presort))),
        hpj::sep(vec![
            hpj::vcat(
                tactic
                    .prios
                    .iter()
                    .map(|b| render_block("prio", b))
                    .collect(),
            ),
            hpj::vcat(
                tactic
                    .deprios
                    .iter()
                    .map(|b| render_block("deprio", b))
                    .collect(),
            ),
        ]),
    ])
    .render()
}

/// `ppTab` for one block: `<kw>: {ranking}` $-$ nest-2 prettified lines.
fn render_block(kw: &str, b: &PrioBlock) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    hpj::vcat(vec![
        hpj::keyword_(kw).beside(Doc::text(format!(": {{{}}}", b.ranking))),
        hpj::vcat(b.selectors.iter().map(render_selector).collect()).nest(2),
    ])
}

/// HS `prettify`: highlight operators and escape selector text through Doc.
fn render_selector(selector: &SelectorExpr) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let mut raw = String::new();
    render_selector_raw(&mut raw, selector);
    raw.split_whitespace().fold(Doc::empty(), |doc, word| {
        doc.beside(match word {
            "|" => hpj::operator_(" | "),
            "&" => hpj::operator_(" & "),
            "not" => hpj::operator_("not "),
            _ => Doc::text(word),
        })
    })
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
    fn html_tactics_highlight_keywords_and_operators_and_escape_text() {
        let tactic = parse(
            "example",
            "prio: {id}\n regex \"<tag>\" & not regex \"other\"\n",
        );
        let _html = crate::pretty_hpj::HtmlDocGuard::enable();
        let html = render(&tactic);
        assert!(
            html.contains("class=\"hl_keyword\">tactic</span>"),
            "{html}"
        );
        assert!(html.contains("class=\"hl_keyword\">prio</span>"), "{html}");
        assert!(
            html.contains("class=\"hl_operator\"> &amp; </span>"),
            "{html}"
        );
        assert!(html.contains("&lt;tag&gt;"), "{html}");
        assert!(!html.contains("<tag>"));
    }

    /// HS spthy `identLetter` excludes `.` (Token.hs), so a function name
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
