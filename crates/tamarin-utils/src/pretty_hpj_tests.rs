// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;

/// The hpj-layout table: `name, width, ribbon, doc, expected`.  `doc` is a
/// `Text.PrettyPrint.HughesPJ` expression in Haskell syntax and `expected`
/// the bytes pretty-1.1.3.6 renders it to at that line length and ribbon
/// (`\n` and `\\` escaped).
const HPJ_CASES: &str = include_str!("hpj_cases.tsv");

/// A value of the HughesPJ expression subset the table uses.
enum Val {
    Doc(Doc),
    List(Vec<Doc>),
    Int(isize),
    Str(String),
}

impl Val {
    fn doc(self) -> Doc {
        match self {
            Val::Doc(d) => d,
            _ => panic!("expected a Doc"),
        }
    }
    fn list(self) -> Vec<Doc> {
        match self {
            Val::List(ds) => ds,
            _ => panic!("expected a [Doc]"),
        }
    }
}

/// A recursive-descent reader of HughesPJ expressions: string and char
/// literals, integers, lists, parentheses, the combinators `text`, `char`,
/// `empty`, `nest`, `sep`, `fsep`, `fcat`, `hcat`, `hsep`, `vcat` and
/// `punctuate`, and the operators `<>`/`<+>` (infixl 6) and `$$`/`$+$`
/// (infixl 5).  `text ""` is HS's zero-width text, not `empty`.
struct Expr<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Expr<'a> {
    fn parse(src: &'a str) -> Doc {
        let mut e = Expr { src, pos: 0 };
        let d = e.above().doc();
        e.skip_ws();
        assert_eq!(e.pos, src.len(), "trailing input in {src:?}");
        d
    }

    fn rest(&self) -> &'a str {
        &self.src[self.pos..]
    }

    fn skip_ws(&mut self) {
        self.pos = self.src.len() - self.rest().trim_start().len();
    }

    fn eat(&mut self, tok: &str) -> bool {
        self.skip_ws();
        if self.rest().starts_with(tok) {
            self.pos += tok.len();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, tok: &str) {
        assert!(self.eat(tok), "expected {tok:?} at {:?}", self.rest());
    }

    fn above(&mut self) -> Val {
        let mut d = self.beside();
        loop {
            if self.eat("$+$") {
                d = Val::Doc(d.doc().above_g(self.beside().doc()));
            } else if self.eat("$$") {
                d = Val::Doc(d.doc().above(self.beside().doc()));
            } else {
                return d;
            }
        }
    }

    fn beside(&mut self) -> Val {
        let mut d = self.atom();
        loop {
            if self.eat("<+>") {
                d = Val::Doc(d.doc().beside_sp(self.atom().doc()));
            } else if self.eat("<>") {
                d = Val::Doc(d.doc().beside(self.atom().doc()));
            } else {
                return d;
            }
        }
    }

    /// A combinator applied to its arguments.
    fn app(&mut self, ident: &str) -> Val {
        match ident {
            "empty" => Val::Doc(Doc::empty()),
            "text" => match self.atom() {
                Val::Str(s) => Val::Doc(Doc::text_hs(s)),
                _ => panic!("text takes a string"),
            },
            "char" => match self.atom() {
                Val::Str(s) => Val::Doc(Doc::char(s.chars().next().unwrap())),
                _ => panic!("char takes a char"),
            },
            "nest" => match self.atom() {
                Val::Int(k) => Val::Doc(self.atom().doc().nest(k)),
                _ => panic!("nest takes an Int"),
            },
            "punctuate" => {
                let p = self.atom().doc();
                Val::List(punctuate(p, self.atom().list()))
            }
            "sep" => Val::Doc(sep(self.atom().list())),
            "fsep" => Val::Doc(fsep(self.atom().list())),
            "fcat" => Val::Doc(fcat(self.atom().list())),
            "hcat" => Val::Doc(hcat(self.atom().list())),
            "hsep" => Val::Doc(hsep(self.atom().list())),
            "vcat" => Val::Doc(vcat(self.atom().list())),
            other => panic!("unknown combinator {other:?}"),
        }
    }

    fn atom(&mut self) -> Val {
        self.skip_ws();
        let rest = self.rest();
        let ident_len = rest
            .find(|c: char| !c.is_ascii_alphabetic())
            .unwrap_or(rest.len());
        if ident_len > 0 {
            self.pos += ident_len;
            self.app(&rest[..ident_len])
        } else if self.eat("(") {
            let v = if self.rest().starts_with('-') {
                Val::Int(self.int())
            } else {
                self.above()
            };
            self.expect(")");
            v
        } else if self.eat("[") {
            let mut ds = Vec::new();
            if !self.eat("]") {
                loop {
                    ds.push(self.above().doc());
                    if self.eat("]") {
                        break;
                    }
                    self.expect(",");
                }
            }
            Val::List(ds)
        } else if rest.starts_with('"') || rest.starts_with('\'') {
            let quote = rest.chars().next().unwrap();
            let end = rest[1..].find(quote).expect("unterminated literal");
            self.pos += end + 2;
            Val::Str(rest[1..=end].to_string())
        } else {
            Val::Int(self.int())
        }
    }

    fn int(&mut self) -> isize {
        let rest = self.rest();
        let len = rest
            .char_indices()
            .find(|&(i, c)| !(c.is_ascii_digit() || (i == 0 && c == '-')))
            .map_or(rest.len(), |(i, _)| i);
        self.pos += len;
        rest[..len]
            .parse()
            .unwrap_or_else(|_| panic!("expected an expression at {rest:?}"))
    }
}

fn unescape(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('\\') => out.push('\\'),
                other => panic!("bad escape \\{other:?}"),
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[test]
fn every_hpj_layout_row_renders_as_hughes_pj() {
    let mut rows = 0;
    for line in HPJ_CASES.lines().skip(1) {
        let cols: Vec<&str> = line.split('\t').collect();
        let [name, width, ribbon, doc, expected] = cols[..] else {
            panic!("malformed row: {line:?}");
        };
        let out = Expr::parse(doc).render_with(width.parse().unwrap(), ribbon.parse().unwrap());
        assert_eq!(out, unescape(expected), "{name}:\n{out}");
        rows += 1;
    }
    assert!(rows > 0);
}

#[test]
fn html_mode_is_one_engine_flag() {
    // One flag drives the whole engine: `html_mode()` reports what
    // `HtmlDocGuard` set, and `Doc::text` escapes and measures against the
    // same flag.
    assert!(!html_mode());
    {
        let _g = HtmlDocGuard::enable();
        assert!(html_mode());
        assert_eq!(Doc::text("<a>").render(), "&lt;a&gt;");
    }
    assert!(!html_mode());
    assert_eq!(Doc::text("<a>").render(), "<a>");
}

#[test]
fn escape_html_entities_basics() {
    assert_eq!(
        escape_html_entities("<a href=\"x\">&'</a>"),
        "&lt;a href=&quot;x&quot;&gt;&amp;&#39;&lt;/a&gt;"
    );
}
