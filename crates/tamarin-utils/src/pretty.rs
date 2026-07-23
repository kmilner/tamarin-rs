// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Text/PrettyPrint/Class.hs,
//   lib/utils/src/Text/PrettyPrint/Html.hs

//! Port of `Text.PrettyPrint.Class` (and `Highlight`) from
//! `lib/utils/src/Text/PrettyPrint/Class.hs`.
//!
//! The Haskell version is a thin wrapper around `Text.PrettyPrint.HughesPJ`
//! plus a `Document` typeclass that lets the prover render to plain text or
//! to HTML via a different instance.
//!
//! This module provides a line-based pretty-printer (no Hughes width-aware
//! reflowing) supporting the combinators the consumers here actually use:
//! `text`, `<>` (`cat_with`), `<+>` (`beside`), `$-$` (`above`), and
//! `hcat`/`hsep`/`vcat`, `nest`. (The Haskell `$$` and `caseEmptyDoc` class
//! methods are not ported here.)
//!
//! This module is NOT used on the `--prove`/web-UI render path. The faithful,
//! width-accurate HughesPJ port that the prover and web UI actually call lives
//! in `tamarin-theory::pretty_hpj` (full HughesPJ with `render_with`). The only
//! in-crate consumer of this module is `pretty_html`, which uses just `Doc`,
//! `keyword`, `cat_with` and `render_with`. Since `pretty_html` itself has no
//! live consumer, this module currently has no live caller; it is retained as
//! the `Class.hs` port for the future HTML rendering path.
//!
//! Highlight styling (`Comment`/`Keyword`/`Operator`) is carried as an enum
//! tag on a `Doc` node; the plain-text renderer ignores it. The HTML renderer
//! lives in `pretty_html`.

use std::fmt::Write as _;

use crate::prelude_ext::flush_right;

/// Highlight style tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HighlightStyle {
    Keyword,
    Comment,
    Operator,
}

#[derive(Debug, Clone)]
enum Node {
    Empty,
    Text(String),
    /// Width-zero text. Renders normally but `width` reports 0 for it.
    ZeroWidth(String),
    Cat(Box<Node>, Box<Node>),
    /// Vertical concatenation: insert a newline between the two.
    Above(Box<Node>, Box<Node>),
    Nest(usize, Box<Node>),
    Highlight(HighlightStyle, Box<Node>),
}

/// A pretty-printable document.
///
/// The `empty` flag is an O(1) cache of the recursive emptiness predicate,
/// computed once at construction. Without it, `is_empty` would re-walk the
/// whole `Node` tree, making folds like `hcat`/`vcat` (which call combinators
/// that test emptiness on a growing accumulator) O(N^2).
#[derive(Debug, Clone)]
pub struct Doc {
    node: Node,
    empty: bool,
}

impl Default for Doc {
    fn default() -> Self {
        Doc::empty()
    }
}

impl Doc {
    pub fn empty() -> Self {
        Doc {
            node: Node::Empty,
            empty: true,
        }
    }
    pub fn text<S: Into<String>>(s: S) -> Self {
        Doc {
            node: Node::Text(s.into()),
            empty: false,
        }
    }
    pub fn char(c: char) -> Self {
        Doc {
            node: Node::Text(c.to_string()),
            empty: false,
        }
    }
    pub fn zero_width_text<S: Into<String>>(s: S) -> Self {
        Doc {
            node: Node::ZeroWidth(s.into()),
            empty: false,
        }
    }

    pub fn is_empty(&self) -> bool {
        // Mirrors HughesPJ `P.isEmpty`, which is true ONLY for `mempty`/`empty`,
        // never for `text ""` / `zeroWidthText ""`. Combinators (`<>`, `$$`,
        // `nest`, ...) collapse `empty` operands away, so a tree built only from
        // `empty` (via `Cat`/`Above`/`Nest`/`Highlight`) is itself empty. The
        // flag below equals that recursive predicate exactly: it is computed at
        // construction (Empty => true; Text/ZeroWidth => false; Cat/Above =>
        // both children empty; Nest/Highlight => child empty).
        self.empty
    }

    /// Render to a `String` ignoring highlight tags.
    pub fn render(&self) -> String {
        let lines = layout(&self.node, 0);
        let mut out = String::new();
        for (i, line) in lines.iter().enumerate() {
            if i > 0 {
                out.push('\n');
            }
            for _ in 0..line.indent {
                out.push(' ');
            }
            out.push_str(&line.content);
        }
        out
    }

    /// Render to a `String`, bracketing each highlighted span with the
    /// `(open, close)` pair returned by `tags(style)`.
    ///
    /// Mirrors Haskell `withTag` (Html.hs:60-64), which glues ONE `open`
    /// zero-width tag before the entire inner doc and ONE `close` after it
    /// (`open <> inner <> close`). For a multi-line span this places `open` at
    /// the start of the first line's content and `close` at the end of the last
    /// line's content, leaving intermediate lines bare — so a two-line keyword
    /// renders `<span ...>line1\nline2</span>`, not `<span>line1</span>\n<span>line2</span>`.
    pub fn render_with<F: Fn(HighlightStyle) -> (String, String)>(&self, tags: &F) -> String {
        let lines = layout_with(&self.node, 0, tags);
        let mut out = String::new();
        for (i, line) in lines.iter().enumerate() {
            if i > 0 {
                out.push('\n');
            }
            for _ in 0..line.indent {
                out.push(' ');
            }
            out.push_str(&line.content);
        }
        out
    }

    /// `<>`: horizontal concatenation.
    pub fn cat_with(self, other: Doc) -> Doc {
        match (self.is_empty(), other.is_empty()) {
            (true, _) => other,
            (_, true) => self,
            // Both non-empty here, so the result is non-empty.
            _ => Doc {
                node: Node::Cat(Box::new(self.node), Box::new(other.node)),
                empty: false,
            },
        }
    }

    /// `<+>`: horizontal concatenation with a single space between.
    pub fn beside(self, other: Doc) -> Doc {
        if self.is_empty() {
            return other;
        }
        if other.is_empty() {
            return self;
        }
        self.cat_with(Doc::text(" ")).cat_with(other)
    }

    /// `$-$`: vertical concatenation, always inserting a newline.
    pub fn above(self, other: Doc) -> Doc {
        match (self.is_empty(), other.is_empty()) {
            (true, _) => other,
            (_, true) => self,
            // Both non-empty here, so the result is non-empty.
            _ => Doc {
                node: Node::Above(Box::new(self.node), Box::new(other.node)),
                empty: false,
            },
        }
    }

    /// `nest n d`: indent every line of `d` after the first by `n` spaces.
    pub fn nest(self, n: usize) -> Doc {
        // Reached only when `self` is non-empty, so the result is non-empty.
        if self.is_empty() || n == 0 {
            self
        } else {
            Doc {
                node: Node::Nest(n, Box::new(self.node)),
                empty: false,
            }
        }
    }

    /// Tag this document with a highlight style.
    pub fn highlight(self, style: HighlightStyle) -> Doc {
        // Highlight is empty iff its child is empty.
        let empty = self.empty;
        Doc {
            node: Node::Highlight(style, Box::new(self.node)),
            empty,
        }
    }
}

/// `hcat`: horizontal concatenation without separator.
pub fn hcat(ds: impl IntoIterator<Item = Doc>) -> Doc {
    ds.into_iter().fold(Doc::empty(), Doc::cat_with)
}

/// `hsep`: horizontal concatenation separated by single spaces.
pub fn hsep(ds: impl IntoIterator<Item = Doc>) -> Doc {
    let mut iter = ds.into_iter().filter(|d| !d.is_empty());
    let first = match iter.next() {
        Some(d) => d,
        None => return Doc::empty(),
    };
    iter.fold(first, |acc, d| acc.beside(d))
}

/// `vcat`: vertical concatenation, one document per line.
pub fn vcat(ds: impl IntoIterator<Item = Doc>) -> Doc {
    let mut iter = ds.into_iter().filter(|d| !d.is_empty());
    let first = match iter.next() {
        Some(d) => d,
        None => return Doc::empty(),
    };
    iter.fold(first, |acc, d| acc.above(d))
}

// -- Atomic punctuation -------------------------------------------------------

pub fn semi() -> Doc {
    Doc::char(';')
}
pub fn colon() -> Doc {
    Doc::char(':')
}
pub fn comma() -> Doc {
    Doc::char(',')
}
pub fn space() -> Doc {
    Doc::char(' ')
}
pub fn equals() -> Doc {
    Doc::char('=')
}
pub fn lparen() -> Doc {
    Doc::char('(')
}
pub fn rparen() -> Doc {
    Doc::char(')')
}
pub fn lbrack() -> Doc {
    Doc::char('[')
}
pub fn rbrack() -> Doc {
    Doc::char(']')
}
pub fn lbrace() -> Doc {
    Doc::char('{')
}
pub fn rbrace() -> Doc {
    Doc::char('}')
}

pub fn quotes(d: Doc) -> Doc {
    Doc::char('\'').cat_with(d).cat_with(Doc::char('\''))
}
pub fn double_quotes(d: Doc) -> Doc {
    Doc::char('"').cat_with(d).cat_with(Doc::char('"'))
}
pub fn parens(d: Doc) -> Doc {
    Doc::char('(').cat_with(d).cat_with(Doc::char(')'))
}
pub fn brackets(d: Doc) -> Doc {
    Doc::char('[').cat_with(d).cat_with(Doc::char(']'))
}
pub fn braces(d: Doc) -> Doc {
    Doc::char('{').cat_with(d).cat_with(Doc::char('}'))
}

pub fn hang(d1: Doc, n: usize, d2: Doc) -> Doc {
    vcat([d1, d2.nest(n)])
}

/// `punctuate sep ds`: insert `sep` between successive `ds`.
pub fn punctuate(sep: Doc, ds: Vec<Doc>) -> Vec<Doc> {
    let n = ds.len();
    if n == 0 {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(n);
    for (i, d) in ds.into_iter().enumerate() {
        if i == n - 1 {
            out.push(d);
        } else {
            out.push(d.cat_with(sep.clone()));
        }
    }
    out
}

/// Output text with a fixed advertised width.
pub fn fixed_width_text(n: usize, s: &str) -> Doc {
    if s.chars().count() <= n {
        Doc::text(s)
    } else {
        let head: String = s.chars().take(n).collect();
        let tail: String = s.chars().skip(n).collect();
        Doc::text(head).cat_with(Doc::zero_width_text(tail))
    }
}

/// Treat a string as a single-column "symbol" (zero-width past column 1).
pub fn symbol(s: &str) -> Doc {
    fixed_width_text(1, s)
}

/// `numbered vsep ds`: prefix each `d` with a right-flushed index, then join the
/// items with `vsep` interspersed between them (Class.hs:252-259):
///   `foldr1 ($-$) $ intersperse vsep $ map pp $ zip [1..] ds`.
/// `vsep` is a standalone document placed on its own "line" via `$-$`, not glued
/// horizontally onto the items — so `numbered (text "")` yields blank separator
/// lines (because `text ""` is not empty).
pub fn numbered(vsep: Doc, ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::empty();
    }
    let n = ds.len();
    let n_width = n.to_string().chars().count();
    let mut buf = String::new();
    let lined: Vec<Doc> = ds
        .into_iter()
        .enumerate()
        .map(|(i, d)| {
            buf.clear();
            write!(&mut buf, "{}", i + 1).unwrap();
            let prefix = flush_right(n_width, &buf);
            Doc::text(prefix).cat_with(d)
        })
        .collect();
    // intersperse `vsep` between items, then foldr1 ($-$).
    let mut iter = lined.into_iter();
    let mut acc = iter.next().unwrap();
    for d in iter {
        acc = acc.above(vsep.clone()).above(d);
    }
    acc
}

// -- Highlight helpers --------------------------------------------------------

pub fn comment(d: Doc) -> Doc {
    d.highlight(HighlightStyle::Comment)
}
pub fn keyword(d: Doc) -> Doc {
    d.highlight(HighlightStyle::Keyword)
}
pub fn operator(d: Doc) -> Doc {
    d.highlight(HighlightStyle::Operator)
}

pub fn comment_text(s: &str) -> Doc {
    comment(Doc::text(s))
}
pub fn keyword_text(s: &str) -> Doc {
    keyword(Doc::text(s))
}
pub fn operator_text(s: &str) -> Doc {
    operator(Doc::text(s))
}

pub fn op_parens(d: Doc) -> Doc {
    operator_text("(").cat_with(d).cat_with(operator_text(")"))
}

// =============================================================================
// Layout: convert a Node tree to a flat list of (indent, content) lines.
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
struct Line {
    indent: usize,
    content: String,
}

fn layout(n: &Node, base_indent: usize) -> Vec<Line> {
    layout_with(n, base_indent, &|_| (String::new(), String::new()))
}

fn layout_with<F: Fn(HighlightStyle) -> (String, String)>(
    n: &Node,
    base_indent: usize,
    tags: &F,
) -> Vec<Line> {
    match n {
        Node::Empty => vec![Line {
            indent: base_indent,
            content: String::new(),
        }],
        Node::Text(s) | Node::ZeroWidth(s) => {
            vec![Line {
                indent: base_indent,
                content: s.clone(),
            }]
        }
        Node::Cat(a, b) => {
            let mut la = layout_with(a, base_indent, tags);
            let lb = layout_with(b, base_indent, tags);
            // Glue first line of b onto last line of a.
            let last = la.pop().unwrap_or(Line {
                indent: base_indent,
                content: String::new(),
            });
            let mut lb_iter = lb.into_iter();
            let first_b = lb_iter.next().unwrap_or(Line {
                indent: 0,
                content: String::new(),
            });
            let merged = Line {
                indent: last.indent,
                content: last.content + &first_b.content,
            };
            la.push(merged);
            la.extend(lb_iter);
            la
        }
        Node::Above(a, b) => {
            let mut la = layout_with(a, base_indent, tags);
            let lb = layout_with(b, base_indent, tags);
            la.extend(lb);
            la
        }
        Node::Nest(k, inner) => layout_with(inner, base_indent + k, tags),
        Node::Highlight(style, inner) => {
            // Haskell `withTag` (Html.hs:60-64) is `open <> inner <> close`:
            // one `open` tag glued before the whole inner doc and one `close`
            // after it. We mirror that exactly — prepend `open` to the first
            // laid-out line's content and append `close` to the last line's
            // content, leaving intermediate lines bare. So a multi-line span
            // renders `<span ...>line1\nline2</span>`. The open tag goes onto
            // the line *content* (after any indentation), matching HS where the
            // zero-width tag follows the line's leading spaces.
            let mut ls = layout_with(inner, base_indent, tags);
            let (open, close) = tags(*style);
            if let Some(first) = ls.first_mut() {
                first.content.insert_str(0, &open);
            }
            if let Some(last) = ls.last_mut() {
                last.content.push_str(&close);
            }
            ls
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_and_render() {
        assert_eq!(Doc::text("hello").render(), "hello");
        assert_eq!(Doc::empty().render(), "");
    }

    #[test]
    fn cat_horizontal() {
        let d = Doc::text("ab").cat_with(Doc::text("cd"));
        assert_eq!(d.render(), "abcd");
    }

    #[test]
    fn beside_inserts_space() {
        assert_eq!(Doc::text("a").beside(Doc::text("b")).render(), "a b");
    }

    #[test]
    fn above_inserts_newline() {
        let d = Doc::text("a").above(Doc::text("b"));
        assert_eq!(d.render(), "a\nb");
    }

    #[test]
    fn nest_indents_subsequent_lines() {
        let inner = Doc::text("a").above(Doc::text("b"));
        let d = Doc::text("hdr").cat_with(inner.nest(2));
        // Cat glues first line of nested onto "hdr" (no indent on first).
        // Subsequent line (b) gets nested by 2.
        assert_eq!(d.render(), "hdra\n  b");
    }

    #[test]
    fn vcat_lines_in_order() {
        let d = vcat(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]);
        assert_eq!(d.render(), "a\nb\nc");
    }

    #[test]
    fn hcat_concatenates() {
        assert_eq!(
            hcat(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]).render(),
            "abc"
        );
    }

    #[test]
    fn hsep_inserts_spaces() {
        assert_eq!(
            hsep(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]).render(),
            "a b c"
        );
    }

    #[test]
    fn brackets_wrap() {
        assert_eq!(parens(Doc::text("x")).render(), "(x)");
        assert_eq!(brackets(Doc::text("y")).render(), "[y]");
        assert_eq!(braces(Doc::text("z")).render(), "{z}");
    }

    #[test]
    fn punctuate_inserts_separators() {
        let ds = punctuate(
            Doc::char(','),
            vec![Doc::text("a"), Doc::text("b"), Doc::text("c")],
        );
        assert_eq!(hcat(ds).render(), "a,b,c");
    }

    #[test]
    fn numbered_intersperses_blank_separator() {
        // Haskell `numbered (text "")` intersperses a (non-empty) `text ""`
        // separator joined via `$-$`, producing a BLANK line between entries:
        // "1 alpha\n\n2 beta\n\n3 gamma".
        let d = numbered(
            Doc::text(""),
            vec![Doc::text(" alpha"), Doc::text(" beta"), Doc::text(" gamma")],
        );
        assert_eq!(d.render(), "1 alpha\n\n2 beta\n\n3 gamma");
    }

    #[test]
    fn fixed_width_text_pads_advertised_width() {
        // 3 chars rendered, width-3 advertised: text only.
        assert_eq!(fixed_width_text(3, "abc").render(), "abc");
        // 5 chars rendered but width-3 advertised: split into width-3 head plus zero-width tail.
        assert_eq!(fixed_width_text(3, "abcde").render(), "abcde");
    }

    #[test]
    fn highlight_passes_through_render() {
        let d = keyword(Doc::text("rule"));
        assert_eq!(d.render(), "rule");
        let html = d.render_with(&|s| match s {
            HighlightStyle::Keyword => ("<kw>".to_string(), "</kw>".to_string()),
            _ => (String::new(), String::new()),
        });
        assert_eq!(html, "<kw>rule</kw>");
    }

    #[test]
    fn is_empty_recurses() {
        assert!(Doc::empty().is_empty());
        // HughesPJ `P.isEmpty (text "") == False`: an explicit empty string is
        // NOT the empty document.
        assert!(!Doc::text("").is_empty());
        assert!(Doc::empty().nest(2).is_empty());
        assert!(!Doc::text("x").is_empty());
        assert!(!Doc::text("a").above(Doc::empty()).is_empty());
    }
}
