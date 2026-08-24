// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Structured parser for the proof skeleton attached to a lemma.
//!
//! Port of HS `Theory.Text.Parser.Proof.proofSkeleton`
//! (lib/theory/src/Theory/Text/Parser/Proof.hs:98-115).  The HS grammar
//! is:
//!
//! ```text
//! proofSkeleton =
//!     solvedProof <|> finalProof <|> interProof
//!   where
//!     solvedProof = "SOLVED"
//!     finalProof  = "by" proofMethod
//!     interProof  = proofMethod ( ("case" ident proofSkeleton)*
//!                                 "next" ... "qed"  | proofSkeleton )
//!
//! proofMethod = "sorry"        | "simplify"
//!             | "solve" "(" goal ")"
//!             | "contradiction"| "induction"
//!             | "INVALIDATED"  | "UNFINISHABLE"
//! ```
//!
//! See [`crate::ast::ParsedProofTree`] / [`crate::ast::ParsedMethod`]
//! for the shape of the structured output; the `goal` inside a
//! `solve( ... )` step is read by [`crate::parser::parse_goal_str`].
//! Anything we can't recognise structurally (rare proof-method tokens,
//! unusual goal formulas) is captured in `Other(text)` /
//! `GoalSpec::Raw(text)` so the replay walker can fall back to the
//! auto-prover.

use crate::ast::{DisjAlt, GoalSpec, ParsedMethod, ParsedProofTree};
use crate::lexer::{is_ident_char, Lexer};
use crate::parser::Parser;

#[derive(Debug, Clone)]
pub struct ProofTreeParseError {
    pub line: u32,
    pub col: u32,
    pub msg: String,
}

impl std::fmt::Display for ProofTreeParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "proof-tree parse error at line {} col {}: {}",
            self.line, self.col, self.msg
        )
    }
}
impl std::error::Error for ProofTreeParseError {}

/// Parse the raw skeleton text into a [`ParsedProofTree`].  Returns
/// `Err` if the token stream doesn't conform to the HS grammar — the
/// caller (parser.rs `try_proof_skeleton`) downgrades the failure to
/// `tree: None` so the lemma is at least readable, and replay falls
/// back to auto-prover at the top.
///
/// `parent` is the theory parser the skeleton text came out of, whose symbol
/// state [`crate::parser::parse_goal_str`] needs to read the goal inside a
/// `solve( ... )` step; HS's proof parser runs inside the theory parser and
/// reads the same state (Theory/Text/Parser/Proof.hs:38-72).
pub fn parse_proof_tree<'a>(
    raw: &'a str,
    parent: &'a Parser<'a>,
) -> Result<ParsedProofTree, ProofTreeParseError> {
    let mut p = TreeParser {
        lx: Lexer::new(raw),
        parent,
    };
    let tree = p.proof_skeleton()?;
    // Any trailing junk is tolerated — likely the outer `qed` from a
    // higher-level case block.  HS proofSkeleton consumes proper `qed`
    // inside interProof; anything left is fine for our purposes (caller's
    // `read_until_next_top_level` already framed the input).
    Ok(tree)
}

struct TreeParser<'a> {
    lx: Lexer<'a>,
    parent: &'a Parser<'a>,
}

impl<'a> TreeParser<'a> {
    fn err(&self, msg: impl Into<String>) -> ProofTreeParseError {
        let (line, col) = self.lx.line_col();
        ProofTreeParseError {
            line,
            col,
            msg: msg.into(),
        }
    }

    /// HS `proofSkeleton` (Theory/Text/Parser/Proof.hs:98-115).
    fn proof_skeleton(&mut self) -> Result<ParsedProofTree, ProofTreeParseError> {
        self.lx.skip_ws();
        // solvedProof: `SOLVED`
        if self.try_kw("SOLVED") {
            return Ok(ParsedProofTree {
                method: ParsedMethod::SolvedLeaf,
                cases: Vec::new(),
            });
        }
        // finalProof: `by <proofMethod>`
        if self.try_kw("by") {
            let m = self.proof_method()?;
            return Ok(ParsedProofTree {
                method: m,
                cases: Vec::new(),
            });
        }
        // interProof: <method> ( case-block | proofSkeleton )
        let m = self.proof_method()?;
        // HS: `cases <- (sepBy oneCase "next" <* "qed") <|>
        //               ((return . (,) "") <$> proofSkeleton)`
        // (Theory/Text/Parser/Proof.hs:111-112).  `oneCase` starts with
        // `case <ident>`, so a `case` token here means the case-block
        // branch.  Otherwise HS
        // *requires* a recursive `proofSkeleton` (the inline single-child
        // subproof, named ""); there is NO childless-leaf branch — an
        // interProof method must be followed by a child.
        self.lx.skip_ws();
        if self.peek_kw("case") {
            let mut cases: Vec<(String, ParsedProofTree)> = Vec::new();
            // HS: sepBy oneCase "next" <* "qed"
            // First case (mandatory at least one):
            cases.push(self.one_case()?);
            while self.try_kw("next") {
                cases.push(self.one_case()?);
            }
            self.require_kw("qed")?;
            return Ok(ParsedProofTree { method: m, cases });
        }
        // Inline (single-child) subproof.  HS: `(return . (,) "") <$>
        // proofSkeleton` — this alternative ALWAYS requires a successful
        // recursive `proofSkeleton`.  If neither a case-block nor a
        // following proofSkeleton parses, HS `interProof` fails (verified
        // against the v1.13.0 prover: a bare `simplify` with no child is a
        // parse error, "expecting case/qed/by/...").  We mirror that by
        // failing here; the caller (parser.rs `try_proof_skeleton`)
        // downgrades the `Err` to `tree: None` and replays via the
        // auto-prover — matching HS, where a failed skeleton parse yields
        // no usable tree.
        let sub = self.proof_skeleton()?;
        Ok(ParsedProofTree {
            method: m,
            cases: vec![("".to_string(), sub)],
        })
    }

    /// HS `oneCase` (Theory/Text/Parser/Proof.hs:98-115, see line 115):
    ///   `(,) <$> ("case" *> identifier) <*> proofSkeleton`
    fn one_case(&mut self) -> Result<(String, ParsedProofTree), ProofTreeParseError> {
        self.require_kw("case")?;
        let name = self.identifier_extended()?;
        let sub = self.proof_skeleton()?;
        Ok((name, sub))
    }

    /// HS `proofMethod` (Theory/Text/Parser/Proof.hs:76-85).
    fn proof_method(&mut self) -> Result<ParsedMethod, ProofTreeParseError> {
        self.lx.skip_ws();
        if self.try_kw("sorry") {
            return Ok(ParsedMethod::Sorry);
        }
        if self.try_kw("simplify") {
            return Ok(ParsedMethod::Simplify);
        }
        if self.try_kw("contradiction") {
            return Ok(ParsedMethod::Contradiction);
        }
        if self.try_kw("induction") {
            return Ok(ParsedMethod::Induction);
        }
        if self.try_kw("INVALIDATED") {
            return Ok(ParsedMethod::Invalidated);
        }
        if self.try_kw("UNFINISHABLE") {
            return Ok(ParsedMethod::Unfinishable);
        }
        // SOLVED is intentionally NOT a proofMethod: HS `proofMethod`
        // (Theory/Text/Parser/Proof.hs:76-85) never lists it; it is handled
        // only at the skeleton level (`solvedProof`,
        // Theory/Text/Parser/Proof.hs:102-103) — see the
        // `SOLVED` branch of `proof_skeleton`.
        if self.try_kw("solve") {
            // `solve( <goal-text> )`.  HS parses an inner `goal`
            // (Theory/Text/Parser/Proof.hs:80); we frame the parenthesised
            // text and hand it to the same grammar, keeping the text for the
            // forms [`parse_goal_spec`] still recognises.
            self.require_punct("(")?;
            let inner = self.read_balanced_paren()?;
            // `read_balanced_paren` consumed the matching `)`.
            let spec = crate::parser::parse_goal_str(&inner, self.parent)
                .unwrap_or_else(|_| parse_goal_spec(&inner));
            return Ok(ParsedMethod::SolveGoal(spec, inner));
        }
        // Unrecognised token — capture the next identifier-like word
        // so we can carry it through to `Other(...)`.
        let save = self.lx.pos();
        let mut word = String::new();
        while let Some(c) = self.lx.peek() {
            if c.is_whitespace() || c == '(' || c == ')' {
                break;
            }
            word.push(c);
            self.lx.bump();
        }
        if word.is_empty() {
            self.lx.set_pos(save);
            return Err(self.err("expected proof method"));
        }
        Ok(ParsedMethod::Other(word))
    }

    // -------- helpers --------

    /// Match a keyword with a word boundary.
    fn try_kw(&mut self, kw: &str) -> bool {
        self.lx.skip_ws();
        self.lx.try_symbol(kw)
    }

    fn peek_kw(&mut self, kw: &str) -> bool {
        self.lx.skip_ws();
        self.lx.peek_symbol(kw)
    }

    fn require_kw(&mut self, kw: &str) -> Result<(), ProofTreeParseError> {
        if self.try_kw(kw) {
            Ok(())
        } else {
            Err(self.err(format!("expected `{}`", kw)))
        }
    }

    fn require_punct(&mut self, p: &str) -> Result<(), ProofTreeParseError> {
        self.lx.skip_ws();
        if self.lx.eat_str(p) {
            Ok(())
        } else {
            Err(self.err(format!("expected `{}`", p)))
        }
    }

    /// Identifier with extended chars: HS's `identifier` accepts
    /// alphanum + `_` (Token.hs:214-230, see line 224 `identLetter = alphaNum <|> oneOf "_"`)
    /// and emits names like `Server_ReceiveOTP_NewSession_case_1`.
    fn identifier_extended(&mut self) -> Result<String, ProofTreeParseError> {
        self.lx.skip_ws();
        let mut s = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphanumeric() || c == '_' => {
                s.push(c);
                self.lx.bump();
            }
            _ => return Err(self.err("expected identifier")),
        }
        while let Some(c) = self.lx.peek() {
            if is_ident_char(c) {
                s.push(c);
                self.lx.bump();
            } else {
                break;
            }
        }
        self.lx.skip_ws();
        Ok(s)
    }

    /// Read raw text between an already-consumed `(` and its matching
    /// `)`, accounting for nested parens.  Returns the inner text
    /// (excluding the final `)` which is consumed).
    fn read_balanced_paren(&mut self) -> Result<String, ProofTreeParseError> {
        let mut s = String::new();
        let mut depth: i32 = 1;
        while depth > 0 {
            match self.lx.peek() {
                None => return Err(self.err("unterminated `(` in solve(...)")),
                Some('(') => {
                    s.push('(');
                    self.lx.bump();
                    depth += 1;
                }
                Some(')') => {
                    depth -= 1;
                    if depth == 0 {
                        self.lx.bump();
                        break;
                    }
                    s.push(')');
                    self.lx.bump();
                }
                Some(c) => {
                    s.push(c);
                    self.lx.bump();
                }
            }
        }
        Ok(s)
    }
}

// =============================================================================
// Goal-spec parser
// =============================================================================

/// Classify a `solve( ... )` goal text that [`crate::parser::parse_goal_str`]
/// does not accept.
///
/// HS `disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula (symbol "∥")`
/// (Theory/Text/Parser/Proof.hs:61) parses each disjunct into a `Guarded`
/// value; here each disjunct contributes its top-level shape and its
/// normalised text, which the replay matcher uses in place of those values.
/// Text that carries no top-level `∥` is kept verbatim in
/// [`GoalSpec::Raw`] and the replay walker falls back to the auto-prover.
pub fn parse_goal_spec(raw: &str) -> GoalSpec {
    let trimmed = raw.trim();
    let parts = split_top_level_disj(trimmed);
    if parts.len() < 2 {
        // `sepBy1` would read a lone `guardedFormula` as a one-disjunct
        // `DisjG (Disj [gf])`.  The solver mints a `DisjG` goal only from a
        // case split with two or more disjuncts, so that degenerate goal is
        // never printed; requiring `∥` also keeps every other unrecognised
        // goal text out of the `Disj` classification.
        return GoalSpec::Raw(trimmed.to_string());
    }
    let alts: Vec<DisjAlt> = parts.iter().map(|p| classify_disj_alt(p)).collect();
    // The shape signature alone does not separate two `DisjG` goals that the
    // insertImpliedFormulas pass minted at one induction hypothesis: they
    // share their alt count and every per-alt shape.  HS separates them by
    // the concrete LVar identities inside each parsed `Guarded`; the
    // normalised alt text carries the same distinction across the
    // skeleton-vs-runtime boundary.  Yubikey::slightly_weaker_invariant at
    // /non_empty_trace/case_1 is the case: alt[0] is `last(#t2)` in one and
    // `last(#t1)` in the other.
    let alt_texts: Vec<String> = parts
        .iter()
        .map(|p| {
            let s = strip_outer_parens(p.trim()).trim().to_string();
            normalize_disj_alt_text(&s)
        })
        .collect();
    GoalSpec::Disj { alts, alt_texts }
}

/// Normalize a disj-alt's text for cross-renderer comparison.  Both
/// sides are tamarin-style text: the HS skeleton renders alts via
/// `prettyGuarded` (Guarded.hs:822-864) and the runtime side is rendered
/// by `pretty_disj_alt`/`pretty_guarded` (the same HS `prettyGuarded`),
/// producing text such as `last(#t2)` — NOT a Rust Debug
/// `Var(Free(VarSpec{...}))` string.  The comparison only works because
/// BOTH sides run through this identical whitespace + leading-`#`
/// stripping, which reveals divergent var bindings via a simple
/// substring/equality check.
fn normalize_disj_alt_text(s: &str) -> String {
    s.chars()
        .filter(|c| !c.is_whitespace() && *c != '#')
        .collect()
}

/// Split `s` at top-level `∥` characters (U+2225).  Ignores any `∥`
/// that lives inside a `()/[]/<>/{}` bracket pair.
fn split_top_level_disj(s: &str) -> Vec<String> {
    const SEP: char = '\u{2225}';
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => {
                depth += 1;
                cur.push(c);
            }
            ')' | ']' | '}' => {
                depth -= 1;
                cur.push(c);
            }
            // `<` / `>` are used for tuple syntax inside facts; we don't
            // need to bracket-track them here because the `∥` separator
            // never appears inside `<…>`.  Tracking them would break on
            // `#t1 < #t2` which is a TIMEPOINT-LESS atom, not a tuple.
            _ if c == SEP && depth == 0 => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Classify the shape of one disj-alt — its top-level quantifier, if
/// any, plus the number of bound variables.  Strips any surrounding
/// `(...)` so `(∀ x y. …)` and `∀ x y. …` classify identically.
fn classify_disj_alt(raw: &str) -> DisjAlt {
    let trimmed = strip_outer_parens(raw.trim());
    // Look for a leading `∀` (U+2200) or `∃` (U+2203) after stripping
    // any further whitespace.
    let t = trimmed.trim_start();
    if let Some(rest) = t.strip_prefix('\u{2200}') {
        return DisjAlt::All {
            n_vars: count_quant_vars(rest),
        };
    }
    if let Some(rest) = t.strip_prefix('\u{2203}') {
        return DisjAlt::Ex {
            n_vars: count_quant_vars(rest),
        };
    }
    DisjAlt::NonQuant
}

/// Strip ONE balanced layer of outer parens.  `"(x ∨ y)"` → `"x ∨ y"`;
/// `"x ∨ y"` returns unchanged.  Only strips if the opening `(` at
/// position 0 matches a closing `)` at the very end of the string with
/// no intermediate depth-0 break.
fn strip_outer_parens(s: &str) -> &str {
    let bytes = s.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'(' || bytes[bytes.len() - 1] != b')' {
        return s;
    }
    // Verify the opening `(` matches the FINAL `)` (no depth-drop in between).
    let mut depth: i32 = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    if i + c.len_utf8() == s.len() {
                        // The first `(` closes at the last char — safe to strip.
                        return &s[1..s.len() - 1];
                    }
                    return s; // Closes early — not a wrapping pair.
                }
            }
            _ => {}
        }
    }
    s
}

/// Count the number of identifier-like variable names appearing after
/// a `∀` / `∃` and before the next `.`.  HS's quantifier list is
/// `\\forall x1 x2 … xN.` — we count whitespace-separated tokens that
/// look like identifiers (possibly with a leading `#` for nodevars or
/// `~` for fresh-name vars).  Stops at the quantifier-body separator
/// `.`.
///
/// Note: a bound var with a non-zero LVar index renders as
/// `name.idx` (HS `LVar` Show, LTerm.hs:550-557, via
/// `ppVars = fsep . map (text . show)`, Guarded.hs:824-866, see line 862), e.g.
/// `∀ x #i.1 #j.`.  So a `.` that is immediately followed by an ASCII
/// digit is a var-index suffix, NOT the body terminator — we must
/// keep counting through it.  The real body terminator `.` is always
/// followed by whitespace / `(` / EOF, never a digit.
fn count_quant_vars(after_qua: &str) -> usize {
    let mut n = 0usize;
    let mut in_token = false;
    let mut chars = after_qua.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '.' {
            // `.idx` suffix on the current var token — consume the dot
            // as part of the token and keep going.
            if chars.peek().is_some_and(|d| d.is_ascii_digit()) {
                in_token = true;
                continue;
            }
            // Genuine quantifier-body terminator.
            break;
        }
        if c == '#' || c == '~' || c == '$' || c == '%' || is_ident_char(c) {
            if !in_token {
                n += 1;
                in_token = true;
            }
        } else {
            in_token = false;
        }
    }
    n
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "proof_tree_tests.rs"]
mod tests;
