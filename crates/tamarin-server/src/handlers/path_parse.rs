// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, arcz, Kanakanajm, rsasse, beschmi, felixlinker,
//   addap, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   src/Web/Types.hs

//! Parse the wildcard path segment after `/thy/trace/<idx>/<section>/`
//! into a [`TheoryPath`], mirroring Haskell's `parseTheoryPath` in
//! `src/Web/Types.hs`.
//!
//! The frontend URL-encodes spaces and special characters, so we
//! percent-decode each segment first.

use percent_encoding::percent_decode_str;

/// A theory-internal path, mirroring Haskell `TheoryPath`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryPath {
    Help,
    Rules,
    Message,
    Tactic,
    Lemma(String),
    Source {
        kind: SourceKind,
        src_idx: i64,
        case_idx: i64,
    },
    Proof {
        lemma: String,
        sub: Vec<String>,
    },
    Method {
        lemma: String,
        idx: i64,
        sub: Vec<String>,
    },
    Edit(String),
    Add(String),
    Delete(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceKind {
    Refined,
    Raw,
}

impl TheoryPath {
    /// Render to the same shape Haskell does (for emitting URLs back
    /// to the frontend).  See `renderTheoryPath` / the
    /// `prefixWithUnderscore` quirk in Haskell.
    pub fn render(&self) -> Vec<String> {
        let segs: Vec<String> = match self {
            TheoryPath::Help => vec!["help".into()],
            TheoryPath::Rules => vec!["rules".into()],
            TheoryPath::Message => vec!["message".into()],
            TheoryPath::Tactic => vec!["tactic".into()],
            TheoryPath::Lemma(n) => vec!["lemma".into(), n.clone()],
            TheoryPath::Source {
                kind,
                src_idx,
                case_idx,
            } => {
                let k = match kind {
                    SourceKind::Refined => "refined",
                    SourceKind::Raw => "raw",
                };
                vec![
                    "cases".into(),
                    k.into(),
                    src_idx.to_string(),
                    case_idx.to_string(),
                ]
            }
            TheoryPath::Proof { lemma, sub } => {
                let mut v = vec!["proof".into(), lemma.clone()];
                v.extend(sub.iter().cloned());
                v
            }
            TheoryPath::Method { lemma, idx, sub } => {
                let mut v = vec!["method".into(), lemma.clone(), idx.to_string()];
                v.extend(sub.iter().cloned());
                v
            }
            TheoryPath::Edit(n) => vec!["edit".into(), n.clone()],
            TheoryPath::Add(n) => vec!["add".into(), n.clone()],
            TheoryPath::Delete(n) => vec!["delete".into(), n.clone()],
        };
        segs.iter().map(|s| prefix_with_underscore(s)).collect()
    }
}

/// Canonical URL path-segment escaping shared by the theory/graph/proof
/// handlers: keep `[A-Za-z0-9_.-]`, percent-encode everything else.
pub fn url_path_escape(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            c if c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '.' => c.to_string(),
            c => format!("%{:02X}", c as u32),
        })
        .collect()
}

/// Match Haskell's `prefixWithUnderscore`.  Empty + `_*` strings get
/// an extra leading `_` to avoid the empty-segment trap in Yesod.
pub fn prefix_with_underscore(s: &str) -> String {
    if s.is_empty() {
        "_".into()
    } else if s.starts_with('_') {
        format!("_{}", s)
    } else {
        s.to_string()
    }
}

/// Encode a proof/method sub-path as leading-slash-joined URL segments,
/// applying [`prefix_with_underscore`] then [`url_path_escape`] to each
/// (mirrors Yesod `getUrlRender`'s per-segment encoding).  Empty input
/// yields the empty string, so callers can append the result directly
/// after `.../proof/<lemma>` or `.../method/<lemma>/<idx>`.
pub fn encode_sub_path(sub: &[String]) -> String {
    let mut s = String::new();
    for seg in sub {
        s.push('/');
        s.push_str(&url_path_escape(&prefix_with_underscore(seg)));
    }
    s
}

/// Inverse of [`prefix_with_underscore`].
pub fn unprefix_underscore(s: &str) -> String {
    if s == "_" {
        String::new()
    } else if s.starts_with("__") {
        s[1..].to_string()
    } else {
        s.to_string()
    }
}

/// Decode a wildcard-captured URL path into its logical segments: strip
/// leading slashes, split on `/`, drop empty segments, percent-decode,
/// then reverse [`prefix_with_underscore`] per segment.
///
/// Mirrors Haskell's `prefixWithUnderscore` invariant: empty case names
/// are encoded as `_` on the URL so adjacent slashes don't collapse, and
/// segments starting with `_` get a leading extra `_`;
/// [`unprefix_underscore`] reverses that here.  Trailing empty segments
/// are dropped by the empty-segment filter, so a leading-only vs both-end
/// trim of `/` is immaterial.
pub fn decode_segments(raw: &str) -> Vec<String> {
    raw.trim_start_matches('/')
        .split('/')
        .filter(|s| !s.is_empty())
        .map(|s| percent_decode_str(s).decode_utf8_lossy().to_string())
        .map(|s| unprefix_underscore(&s))
        .collect()
}

/// Parse a wildcard-captured path (e.g. `proof/Alice/case_1/0`) into a
/// `TheoryPath`.  Returns `None` on malformed input.
pub fn parse(raw: &str) -> Option<TheoryPath> {
    parse_segs(&decode_segments(raw))
}

fn parse_segs(segs: &[String]) -> Option<TheoryPath> {
    let (head, rest) = segs.split_first()?;
    match head.as_str() {
        "help" => Some(TheoryPath::Help),
        "rules" => Some(TheoryPath::Rules),
        "message" => Some(TheoryPath::Message),
        "tactic" => Some(TheoryPath::Tactic),
        "lemma" => rest.first().map(|n| TheoryPath::Lemma(n.clone())),
        "edit" => rest.first().map(|n| TheoryPath::Edit(n.clone())),
        "add" => rest.first().map(|n| TheoryPath::Add(n.clone())),
        "delete" => rest.first().map(|n| TheoryPath::Delete(n.clone())),
        "proof" => {
            // Mirror Haskell `parseProof` (`src/Web/Types.hs:417-456, see line 443`):
            //   parseProof (y:ys) = Just (TheoryProof y ys)
            // i.e. the sub-path is taken AS-IS (after `unprefixUnderscore`
            // each segment).  We do NOT pop trailing empty segments:
            // `proof/<lemma>` is the lemma root (sub = []), while
            // `proof/<lemma>/_` is the sub-path with a single empty
            // case name (sub = [""]) — these are distinct paths in
            // the proof tree (Simplify produces a child with case
            // name "" so this distinction matters at every step).
            let lemma = rest.first()?.clone();
            let sub: Vec<String> = rest.get(1..).unwrap_or(&[]).to_vec();
            Some(TheoryPath::Proof { lemma, sub })
        }
        "method" => {
            // Mirror Haskell `parseMethod` (`src/Web/Types.hs:417-456, see line 446`):
            //   parseMethod (y:z:zs) = safeRead z >>= Just . TheoryMethod y zs
            // i.e. the sub-path is taken AS-IS (after `unprefixUnderscore`
            // each segment) — including a single empty trailing
            // segment, which encodes the inner proof case named "".
            //
            // We intentionally do NOT pop trailing empty segments here
            // (same as the `proof` branch above): the method URL is constructed
            // from the proof-tree path, and each `/_` denotes a real
            // path segment.  Popping would conflate the lemma-root
            // application with applying-at-inner-empty-case (which
            // simplify produces a lot of), routing the click to the
            // wrong node.
            let lemma = rest.first()?.clone();
            // `parseMethod`'s `safeRead z` is the same `ReadS Int` the case
            // indices go through, so `method/<lemma>/1x` and `method/<lemma>/(1)`
            // select method 1 just as `…/1` does.
            let idx = safe_read_int(rest.get(1)?)?;
            let sub: Vec<String> = rest.get(2..).unwrap_or(&[]).to_vec();
            Some(TheoryPath::Method { lemma, idx, sub })
        }
        "cases" => {
            let kind = match rest.first()?.as_str() {
                "refined" => SourceKind::Refined,
                "raw" => SourceKind::Raw,
                _ => return None,
            };
            let src_idx = safe_read_int(rest.get(1)?)?;
            let case_idx = safe_read_int(rest.get(2)?)?;
            Some(TheoryPath::Source {
                kind,
                src_idx,
                case_idx,
            })
        }
        _ => None,
    }
}

/// Haskell `parseCases`'s `safeRead = listToMaybe . map fst . reads`
/// (`src/Web/Types.hs:443`) at `ReadS Int`: the two case indices are SIGNED, so
/// a negative one parses and reaches the handler, which indexes the case list
/// with it exactly as index 0 does (see `handlers::theory::bang_bang_error`).
///
/// `reads` runs `Text.Read.Lex` over the segment and keeps whatever it did not
/// consume, so the accepted forms are wider than a decimal parse:
///
///   - leading whitespace is skipped and trailing input ignored — `1x` and
///     `1,2` both read as 1;
///   - the number may sit in nested parentheses, whitespace inside allowed:
///     `(-1)`, `( -1 )`, `((1))`.  An unbalanced `(1` is no parse, while a
///     stray `-1)` reads as -1 (the `)` is leftovers);
///   - `-` negates the following NUMBER TOKEN, so `- 1` reads while `-(1)`
///     does not; `+` is no Haskell token at all;
///   - `0x`/`0o` prefix a hexadecimal / octal literal (`0x10` is 16), and
///     there is no binary literal, so `0b101` reads as 0 with `b101` left
///     over — as does a bare `0x`;
///   - a decimal point or exponent followed by a digit makes the token
///     fractional, which is no `Int` (`1.5` and `1e2` are no parse, `1.` reads
///     as 1);
///   - the literal is `fromInteger`'d into a 64-bit `Int`, so an over-long one
///     wraps (`99999999999999999999` reads as 7766279631452241919).
fn safe_read_int(s: &str) -> Option<i64> {
    read_int_token(s).map(|(value, _leftovers)| value)
}

/// One `reads`-style `Int` with the input it did not consume.
fn read_int_token(s: &str) -> Option<(i64, &str)> {
    let s = s.trim_start();
    if let Some(inner) = s.strip_prefix('(') {
        let (value, rest) = read_int_token(inner)?;
        return Some((value, rest.trim_start().strip_prefix(')')?));
    }
    if let Some(after_sign) = s.strip_prefix('-') {
        let (value, rest) = read_number_token(after_sign.trim_start())?;
        return Some((value.wrapping_neg(), rest));
    }
    read_number_token(s)
}

/// One `Text.Read.Lex` number token, converted as `Read Int`'s `convertInt`
/// does.
fn read_number_token(s: &str) -> Option<(i64, &str)> {
    let bytes = s.as_bytes();
    if bytes.first() == Some(&b'0') {
        let radix = match bytes.get(1) {
            Some(b'x' | b'X') => Some(16),
            Some(b'o' | b'O') => Some(8),
            _ => None,
        };
        // Without digits behind it the prefix is not a literal: the `0` is the
        // whole token and the rest is leftovers.
        if let Some(digits) = radix.and_then(|r| read_digits(&s[2..], r)) {
            return Some(digits);
        }
    }
    let (value, rest) = read_digits(s, 10)?;
    if is_fractional_suffix(rest) {
        return None;
    }
    Some((value, rest))
}

/// Digits in `radix`, accumulated the way `fromInteger` truncates to `Int`.
fn read_digits(s: &str, radix: u32) -> Option<(i64, &str)> {
    let mut value: i64 = 0;
    let mut end = 0;
    for (i, c) in s.char_indices() {
        let Some(digit) = c.to_digit(radix) else {
            break;
        };
        value = value
            .wrapping_mul(i64::from(radix))
            .wrapping_add(i64::from(digit));
        end = i + c.len_utf8();
    }
    if end == 0 {
        return None;
    }
    Some((value, &s[end..]))
}

/// Whether what follows the digits turns them into a fractional literal — a
/// `.` or an exponent, each with at least one digit behind it.
fn is_fractional_suffix(rest: &str) -> bool {
    let bytes = rest.as_bytes();
    match bytes.first() {
        Some(b'.') => bytes.get(1).is_some_and(u8::is_ascii_digit),
        Some(b'e' | b'E') => match bytes.get(1) {
            Some(b'+' | b'-') => bytes.get(2).is_some_and(u8::is_ascii_digit),
            other => other.is_some_and(u8::is_ascii_digit),
        },
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn help_and_rules() {
        assert_eq!(parse("help"), Some(TheoryPath::Help));
        assert_eq!(parse("/help/"), Some(TheoryPath::Help));
        assert_eq!(parse("rules"), Some(TheoryPath::Rules));
    }
    #[test]
    fn lemma_basic() {
        assert_eq!(
            parse("lemma/Alice"),
            Some(TheoryPath::Lemma("Alice".into()))
        );
    }
    #[test]
    fn proof_path() {
        let p = parse("proof/Alice/case_1/0").unwrap();
        assert!(
            matches!(p, TheoryPath::Proof { lemma, sub } if lemma == "Alice" && sub == vec!["case_1", "0"])
        );
    }
    #[test]
    fn method_path() {
        let p = parse("method/Alice/3/0").unwrap();
        assert!(
            matches!(p, TheoryPath::Method { lemma, idx, sub } if lemma == "Alice" && idx == 3 && sub == vec!["0"])
        );
    }
    #[test]
    fn render_roundtrip() {
        let p = TheoryPath::Proof {
            lemma: "X".into(),
            sub: vec![],
        };
        let segs = p.render();
        assert_eq!(segs, vec!["proof", "X"]);
    }
    /// `parseCases`'s `safeRead` reads `Int`, so the case indices are signed:
    /// `cases/raw/-1/1` parses (and then raises in the handler, exactly as
    /// `cases/raw/0/1` does).
    #[test]
    fn case_indices_are_signed() {
        assert_eq!(
            parse("cases/raw/-1/1"),
            Some(TheoryPath::Source {
                kind: SourceKind::Raw,
                src_idx: -1,
                case_idx: 1,
            })
        );
        assert_eq!(
            parse("cases/refined/007/-0"),
            Some(TheoryPath::Source {
                kind: SourceKind::Refined,
                src_idx: 7,
                case_idx: 0,
            })
        );
        assert_eq!(parse("cases/raw/-/1"), None);
        assert_eq!(parse("cases/raw/1"), None);
    }

    /// Every form of [`safe_read_int`]'s doc comment, each pinned against the
    /// oracle through the `/thy/trace/1/json/cases/refined/<i>/1` route.
    #[test]
    fn case_indices_read_haskell_int_tokens() {
        let read = |s: &str| safe_read_int(s);
        // Trailing input is leftovers, leading whitespace is skipped.
        assert_eq!(read("1x"), Some(1));
        assert_eq!(read("1,2"), Some(1));
        assert_eq!(read("1 "), Some(1));
        assert_eq!(read("  1"), Some(1));
        assert_eq!(read("\t-1"), Some(-1));
        assert_eq!(read("-1x"), Some(-1));
        assert_eq!(read("-1)"), Some(-1));
        // Parentheses, nested, whitespace inside — but balanced, and the
        // number token must be complete before the `)`.
        assert_eq!(read("(-1)"), Some(-1));
        assert_eq!(read("((-1))"), Some(-1));
        assert_eq!(read("( -1 )"), Some(-1));
        assert_eq!(read("(1)x"), Some(1));
        assert_eq!(read("(1"), None);
        assert_eq!(read("(1x)"), None);
        // `-` negates a number token, not an expression; `+` is no token.
        assert_eq!(read("- 1"), Some(-1));
        assert_eq!(read("-(1)"), None);
        assert_eq!(read("+1"), None);
        // Hexadecimal and octal literals; no binary ones, and a prefix with no
        // digits behind it is just the `0`.
        assert_eq!(read("0x10"), Some(16));
        assert_eq!(read("0o10"), Some(8));
        assert_eq!(read("0b101"), Some(0));
        assert_eq!(read("0x"), Some(0));
        assert_eq!(read("0xg"), Some(0));
        assert_eq!(read("007"), Some(7));
        // A fractional literal is no `Int`; a `.` with no digit behind it is
        // leftovers.
        assert_eq!(read("1.5"), None);
        assert_eq!(read("1e2"), None);
        assert_eq!(read("1E+2"), None);
        assert_eq!(read("1."), Some(1));
        assert_eq!(read("1e"), Some(1));
        // Not numbers at all.
        assert_eq!(read("'1'"), None);
        assert_eq!(read(""), None);
        assert_eq!(read("-"), None);
        // `fromInteger` truncates to a 64-bit `Int`.
        assert_eq!(read("99999999999999999999"), Some(7766279631452241919));
        assert_eq!(read("-99999999999999999999"), Some(-7766279631452241919));
    }
    // Haskell `parseProof (y:ys) = Just (TheoryProof y ys)`: no trailing
    // strip — `proof/<lemma>` is the root (sub=[]), `proof/<lemma>/_`
    // is the inner sub-path with single empty case (sub=[""]).
    #[test]
    fn proof_root_vs_inner_empty_case() {
        let root = parse("proof/Alice").unwrap();
        assert!(
            matches!(&root, TheoryPath::Proof { lemma, sub } if lemma == "Alice" && sub.is_empty()),
            "got {:?}",
            root
        );
        let inner = parse("proof/Alice/_").unwrap();
        assert!(
            matches!(&inner, TheoryPath::Proof { lemma, sub } if lemma == "Alice" && sub == &[""]),
            "got {:?}",
            inner
        );
    }
    // Method path: `method/<lemma>/<N>` applies method N at lemma root
    // (sub=[]); `method/<lemma>/<N>/_` applies at the inner empty-case
    // sub-path (sub=[""]).  Without this distinction the click on a
    // post-simplify sub-case's method list would resolve to the
    // wrong proof node.
    #[test]
    fn method_root_vs_inner_empty_case() {
        let root = parse("method/Alice/1").unwrap();
        assert!(
            matches!(&root, TheoryPath::Method { lemma, idx, sub }
            if lemma == "Alice" && *idx == 1 && sub.is_empty()),
            "got {:?}",
            root
        );
        let inner = parse("method/Alice/1/_").unwrap();
        assert!(
            matches!(&inner, TheoryPath::Method { lemma, idx, sub }
            if lemma == "Alice" && *idx == 1 && sub == &[""]),
            "got {:?}",
            inner
        );
    }
}
