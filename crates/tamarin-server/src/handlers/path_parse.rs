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
        src_idx: usize,
        case_idx: usize,
    },
    Proof {
        lemma: String,
        sub: Vec<String>,
    },
    Method {
        lemma: String,
        idx: usize,
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
            let idx_s = rest.get(1)?;
            let idx: usize = idx_s.parse().ok()?;
            let sub: Vec<String> = rest.get(2..).unwrap_or(&[]).to_vec();
            Some(TheoryPath::Method { lemma, idx, sub })
        }
        "cases" => {
            let kind = match rest.first()?.as_str() {
                "refined" => SourceKind::Refined,
                "raw" => SourceKind::Raw,
                _ => return None,
            };
            let src_idx: usize = rest.get(1)?.parse().ok()?;
            let case_idx: usize = rest.get(2)?.parse().ok()?;
            Some(TheoryPath::Source {
                kind,
                src_idx,
                case_idx,
            })
        }
        _ => None,
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
