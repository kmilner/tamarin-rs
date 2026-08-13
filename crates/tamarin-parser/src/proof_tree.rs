// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rkunnema, jdreier, PhilipLukertWork, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/theory/src/Theory/Constraint/System/Constraints.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Text/Parser/Proof.hs,
//   lib/theory/src/Theory/Text/Parser/Token.hs

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
//! for the shape of the structured output.  Anything we can't
//! recognise structurally (rare proof-method tokens, unusual goal
//! formulas) is captured in `Other(text)` / `GoalSpec::Raw(text)` so
//! the replay walker can fall back to the auto-prover.

use crate::ast::{DisjAlt, Fact, GoalSpec, ParsedMethod, ParsedProofTree};
use crate::lexer::{is_ident_char, Lexer, Pos};
use crate::parser::{Location, Source};
use crate::SpannedStr;

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
pub fn parse_proof_tree(raw: &str) -> Result<ParsedProofTree, ProofTreeParseError> {
    let mut p = TreeParser {
        lx: Lexer::new(raw),
    };
    p.lx.skip_ws();
    let tree = p.proof_skeleton()?;
    p.lx.skip_ws();
    // Any trailing junk is tolerated — likely the outer `qed` from a
    // higher-level case block.  HS proofSkeleton consumes proper `qed`
    // inside interProof; anything left is fine for our purposes (caller's
    // `read_until_next_top_level` already framed the input).
    Ok(tree)
}

/// Read raw text between an already-consumed `(` and its matching `)`,
/// accounting for nested parens. Returns the inner text (excluding the final
/// `)`, which is consumed), or `None` on EOF before the closing paren.
fn read_balanced_paren(lx: &mut Lexer<'_>) -> Option<crate::SpannedStr> {
    let start = lx.pos();
    let mut s = String::new();
    let mut depth: i32 = 1;
    while depth > 0 {
        match lx.peek() {
            None => return None,
            Some('(') => {
                s.push('(');
                lx.bump();
                depth += 1;
            }
            Some(')') => {
                depth -= 1;
                if depth == 0 {
                    lx.bump();
                    break;
                }
                s.push(')');
                lx.bump();
            }
            Some(c) => {
                s.push(c);
                lx.bump();
            }
        }
    }
    let end = lx.pos();
    Some(crate::SpannedStr {
        content: s,
        source: crate::parser::Source::Location(Location::from_positions(start, end)),
    })
}

struct TreeParser<'a> {
    lx: Lexer<'a>,
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

    /// HS `proofSkeleton` (Proof.hs:98-115).
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
        // (Proof.hs:111-112).  `oneCase` starts with `case <ident>`, so
        // a `case` token here means the case-block branch.  Otherwise HS
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

    /// HS `oneCase` (Proof.hs:98-115, see line 115):
    ///   `(,) <$> ("case" *> identifier) <*> proofSkeleton`
    fn one_case(&mut self) -> Result<(String, ParsedProofTree), ProofTreeParseError> {
        self.require_kw("case")?;
        let name = self.identifier_extended()?;
        let sub = self.proof_skeleton()?;
        Ok((name, sub))
    }

    /// HS `proofMethod` (Proof.hs:76-85).
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
        // (Proof.hs:76-85) never lists it; it is handled only at the
        // skeleton level (`solvedProof`, Proof.hs:102-103) — see the
        // `SOLVED` branch of `proof_skeleton`.
        if self.try_kw("solve") {
            // `solve( <goal-text> )`.  HS parses an inner `goal`; we
            // capture the parenthesised text verbatim and best-effort
            // structural parse it.
            self.require_punct("(")?;
            let inner = self.read_balanced_paren()?;
            // `read_balanced_paren` consumed the matching `)`.
            let base_pos = match &inner.source {
                Source::Location(loc) => Pos {
                    offset: loc.start,
                    line: loc.line,
                    col: loc.col,
                },
                _ => Pos::ZERO,
            };
            let spec = parse_goal_spec_at(&inner, base_pos);
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
        let end = self.lx.pos();
        let loc = Location::from_positions(save, end);
        if word.is_empty() {
            self.lx.set_pos(save);
            return Err(self.err("expected proof method"));
        }
        Ok(ParsedMethod::Other(SpannedStr::with_location(word, loc)))
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
    fn read_balanced_paren(&mut self) -> Result<SpannedStr, ProofTreeParseError> {
        read_balanced_paren(&mut self.lx).ok_or_else(|| self.err("unterminated `(` in solve(...)"))
    }
}

// =============================================================================
// Goal-spec parser
// =============================================================================

/// Best-effort parse of the text inside `solve( ... )`.  Mirrors HS
/// `goal` (Theory/Text/Parser/Proof.hs:38-72):
///
/// ```haskell
/// goal = asum
///   [ stSplitGoal, premiseGoal, actionGoal,
///     chainGoal, disjSplitGoal, eqSplitGoal ]
/// ```
///
/// We structurally recognise (in the order the code tries them) Action
/// (`Fact(...) @ #t`), Premise (`Fact(...) ▶<n> #t`), Disj
/// (`gf1 ∥ gf2 ∥ ...` — HS `disjSplitGoal`, Proof.hs:39-72, see line 61), Chain
/// (`(#i,n) ~~> (#j,m)` — HS `chainGoal`, Proof.hs:39-72, see line 59), Split
/// (`splitEqs(N)` — HS `eqSplitGoal`, Proof.hs:70-72), then Subterm
/// (`<a> ⊏ <b>` — HS `stSplitGoal`, Proof.hs:63-66).  Anything else
/// lands in `GoalSpec::Raw` and the walker falls back to the
/// auto-prover.
pub fn parse_goal_spec(raw: &str) -> GoalSpec {
    parse_goal_spec_at(raw, Pos::ZERO)
}

/// Same as [`parse_goal_spec`], but `base_pos` is the source position of
/// `raw`'s (untrimmed) first char, used to give `GoalSpec::Raw` a real
/// `Source::Location` that accounts for the whitespace `trim()` strips.
pub fn parse_goal_spec_at(raw: &str, base_pos: Pos) -> GoalSpec {
    let trimmed = raw.trim();
    let leading_ws = raw.len() - raw.trim_start().len();
    let trimmed_start = advance_pos(base_pos, &raw[..leading_ws]);
    let mut p = GoalParser {
        lx: Lexer::new(trimmed),
    };
    if let Some(spec) = p.try_action_or_premise() {
        return spec;
    }
    if let Some(spec) = try_disj_split(trimmed, trimmed_start) {
        return spec;
    }
    if let Some(spec) = try_chain_split(trimmed, trimmed_start) {
        return spec;
    }
    if let Some(spec) = try_eq_split(trimmed) {
        return spec;
    }
    if let Some(spec) = try_subterm_split(trimmed, trimmed_start) {
        return spec;
    }
    let trimmed_end = advance_pos(trimmed_start, trimmed);
    GoalSpec::Raw(SpannedStr {
        content: trimmed.to_string(),
        source: Source::Location(Location::from_positions(trimmed_start, trimmed_end)),
    })
}

/// Try to split the goal-spec text on top-level `∥` (HS U+2225, the
/// disjunction-split separator).  Returns `GoalSpec::Disj { alts }` if
/// at least one `∥` appears at top-level (depth-0 of `()/[]/<>/{}`),
/// classifying each disjunct by its shape (`∀ / ∃ / NonQuant`).
///
/// Mirrors HS `disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula
/// (symbol "∥")` (Theory/Text/Parser/Proof.hs:39-72, see line 61).  HS parses each
/// disjunct as a full `Guarded` value — we capture only the shape so
/// we can match against an existing `Goal::Disj` in `sys.goals` at
/// replay time without rebuilding LVar identities.
fn try_disj_split(text: &str, base_pos: Pos) -> Option<GoalSpec> {
    let parts = split_top_level_disj(text, base_pos);
    if parts.len() < 2 {
        // HS `disjSplitGoal` uses `sepBy1`, so a lone `guardedFormula`
        // (no `∥`) would parse as a single-disjunct `DisjG (Disj [gf])`.
        // That degenerate goal is never emitted as an actionable goal by
        // the solver (DisjG goals arise from case-splits with >=2
        // disjuncts), so it is unreachable in printed proofs.  The `>= 2`
        // guard is also needed to avoid mis-classifying every non-disj
        // goal text as a 1-alt Disj — single-part text intentionally
        // falls through to chain/eq/subterm and finally `GoalSpec::Raw`,
        // which replays via the auto-prover.
        return None;
    }
    let alts: Vec<DisjAlt> = parts
        .iter()
        .map(|p| classify_disj_alt(&p.content))
        .collect();
    // HS-faithful disambiguation: when multiple Disj goals in
    // sys.goals share the same alt shape signature (e.g. binding-A
    // and binding-B instantiations of the same IH-body 5-alt disj),
    // the shape-only `disj_alts_match` can't distinguish them.  HS
    // parses each alt as a full `Guarded` with concrete LVar
    // identities (Proof.hs:39-72, see line 61), enabling structural match in
    // sys.goals.  We can't easily reconstruct those identities, but
    // we CAN capture each alt's normalized text and use it as a
    // tie-breaker when shape matching is ambiguous.  See
    // Yubikey::slightly_weaker_invariant at
    // /non_empty_trace/case_1: both binding-A's disj (alt[0] =
    // `last(#t2)`) and binding-B's (alt[0] = `last(#t1)`) match the
    // 5-alt NonQuant shape; without alt-text matching, match_goal
    // picks the wrong one and the proof diverges.
    let alt_texts: Vec<SpannedStr> = parts
        .iter()
        .map(|p| {
            let trimmed = trim_spanned(&strip_outer_parens_spanned(p));
            SpannedStr {
                content: normalize_disj_alt_text(&trimmed.content),
                source: trimmed.source,
            }
        })
        .collect();
    Some(GoalSpec::Disj { alts, alt_texts })
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
/// that lives inside a `()/[]/<>/{}` bracket pair.  Each returned
/// segment is trimmed of whitespace and spanned relative to `base_pos`
/// (the source position of `s`'s first char).
fn split_top_level_disj(s: &str, base_pos: Pos) -> Vec<SpannedStr> {
    const SEP: char = '\u{2225}';
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut seg_start = base_pos;
    let mut pos = base_pos;
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
                out.push(make_segment(&cur, seg_start));
                cur.clear();
                pos = bump_pos(pos, c);
                seg_start = pos;
                continue;
            }
            _ => cur.push(c),
        }
        pos = bump_pos(pos, c);
    }
    out.push(make_segment(&cur, seg_start));
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

/// Same as [`strip_outer_parens`], but adjusts `seg`'s `Location` to match
/// the stripped content (both delimiters are single ASCII bytes, so the
/// span shrinks by exactly one char on each side).
fn strip_outer_parens_spanned(seg: &SpannedStr) -> SpannedStr {
    let loc = match &seg.source {
        Source::Location(l) => *l,
        _ => return seg.clone(),
    };
    let stripped = strip_outer_parens(&seg.content);
    if stripped.len() == seg.content.len() {
        return seg.clone();
    }
    let start = advance_pos(
        Pos {
            offset: loc.start,
            line: loc.line,
            col: loc.col,
        },
        "(",
    );
    SpannedStr {
        content: stripped.to_string(),
        source: Source::Location(Location {
            line: start.line,
            col: start.col,
            start: start.offset,
            end: loc.end - 1,
        }),
    }
}

/// Trim whitespace from `seg`'s content, adjusting its `Location` to match.
fn trim_spanned(seg: &SpannedStr) -> SpannedStr {
    let loc = match &seg.source {
        Source::Location(l) => *l,
        _ => {
            return SpannedStr {
                content: seg.content.trim().to_string(),
                source: seg.source.clone(),
            }
        }
    };
    let leading_ws = seg.content.len() - seg.content.trim_start().len();
    let start = advance_pos(
        Pos {
            offset: loc.start,
            line: loc.line,
            col: loc.col,
        },
        &seg.content[..leading_ws],
    );
    let trimmed = seg.content.trim();
    let end = advance_pos(start, trimmed);
    SpannedStr {
        content: trimmed.to_string(),
        source: Source::Location(Location::from_positions(start, end)),
    }
}

/// Count the number of identifier-like variable names appearing after
/// a `∀` / `∃` and before the next `.`.  HS's quantifier list is
/// `\\forall x1 x2 … xN.` — we count whitespace-separated tokens that
/// look like identifiers (possibly with a leading `#` for nodevars or
/// `~` for fresh-name vars).  Stops at the quantifier-body separator
/// `.`.
///
/// Note: a bound var with a non-zero LVar index renders as
/// `name.idx` (HS `LVar` Show, LTerm.hs:529-532, via
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

/// Try to parse a chain-split goal-text: `(#i, N) ~~> (#j, M)`.
///
/// HS reference: `chainGoal = ChainG <$> (try (nodeConc <* opChain))
/// <*> nodePrem` (Theory/Text/Parser/Proof.hs:39-72, see line 59) where
/// `nodeConc/nodePrem = parens ((,) <$> nodevar <*> (comma *> natural))`
/// (Proof.hs:33-36).  The operator `~~>` is the HS pretty rendering
/// (Constraints.hs:269-270).
///
/// We extract the time-var ROOT name (stripping any trailing `.N`
/// freshen-suffix that HS's pretty-printer can emit) and the natural
/// idx for each side.  The matcher disambiguates by these.
fn try_chain_split(text: &str, base_pos: Pos) -> Option<GoalSpec> {
    // Find the top-level `~~>` separator.  HS prints exactly `~~>`
    // (operator_ "~~>" inside fsep) so a plain substring search suffices
    // — we only need to ensure we're at depth 0 of `()/[]/{}` to skip
    // any `~~>` that hypothetically appeared inside a tuple (none do in
    // practice but we are defensive).
    let arrow_pos = find_top_level_substr(text, "~~>")?;
    let lhs_raw = &text[..arrow_pos];
    let rhs_raw = &text[arrow_pos + 3..];
    let rhs_pos = advance_pos(base_pos, &text[..arrow_pos + 3]);
    let (src_var, conc_idx) = parse_node_idx_pair(lhs_raw, base_pos)?;
    let (tgt_var, prem_idx) = parse_node_idx_pair(rhs_raw, rhs_pos)?;
    Some(GoalSpec::Chain {
        src_var,
        conc_idx,
        tgt_var,
        prem_idx,
    })
}

/// Try to parse a subterm-split goal-text: `<small> ⊏ <big>` (U+228F).
///
/// HS reference: `stSplitGoal` (Theory/Text/Parser/Proof.hs:63-66)
/// parses `try (termp <* opSubterm) >>= ...`, where `opSubterm` is the
/// `⊏` operator (renderer at Constraints.hs:281-282).
///
/// We split on the FIRST top-level `⊏` and trim both sides.  The text
/// is kept raw — the matcher canonicalises against the runtime
/// `Goal::Subterm((l, r))` pretty-print at match time.
fn try_subterm_split(text: &str, base_pos: Pos) -> Option<GoalSpec> {
    const SUBTERM_OP: char = '\u{228F}';
    let pos = find_top_level_char(text, SUBTERM_OP)?;
    let small_raw = make_segment(&text[..pos], base_pos);
    let big_start = advance_pos(base_pos, &text[..pos + SUBTERM_OP.len_utf8()]);
    let big_raw = make_segment(&text[pos + SUBTERM_OP.len_utf8()..], big_start);
    if small_raw.content.is_empty() || big_raw.content.is_empty() {
        return None;
    }
    Some(GoalSpec::Subterm { small_raw, big_raw })
}

/// Try to parse an equation-split goal-text: `splitEqs(N)`.
///
/// HS reference: `eqSplitGoal = try $ do { symbol_ "splitEqs"; parens
/// $ (SplitG . SplitId . fromIntegral) <$> natural }`
/// (Theory/Text/Parser/Proof.hs:70-72).  Pretty-printer:
/// `text "splitEqs" <> parens (text $ show (unSplitId x))`
/// (Constraints.hs:279-280).
fn try_eq_split(text: &str) -> Option<GoalSpec> {
    let s = text.trim_start();
    let rest = s.strip_prefix("splitEqs")?.trim_start();
    let rest = rest.strip_prefix('(')?.trim_start();
    // Read decimal digits.
    let mut end = 0usize;
    let bs = rest.as_bytes();
    while end < bs.len() && bs[end].is_ascii_digit() {
        end += 1;
    }
    if end == 0 {
        return None;
    }
    let n: i64 = rest[..end].parse().ok()?;
    let tail = rest[end..].trim_start();
    if !tail.starts_with(')') {
        return None;
    }
    Some(GoalSpec::Split { split_id: n })
}

/// Locate the byte-offset of the first occurrence of `needle` at
/// top-level depth (depth 0 of `()/[]/{}`).  Returns `None` if absent.
fn find_top_level_substr(s: &str, needle: &str) -> Option<usize> {
    let bs = s.as_bytes();
    let nb = needle.as_bytes();
    if nb.is_empty() || bs.len() < nb.len() {
        return None;
    }
    let mut depth: i32 = 0;
    let mut i = 0;
    while i + nb.len() <= bs.len() {
        let c = bs[i];
        if c == b'(' || c == b'[' || c == b'{' {
            depth += 1;
        } else if c == b')' || c == b']' || c == b'}' {
            depth -= 1;
        } else if depth == 0 && &bs[i..i + nb.len()] == nb {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Same as [`find_top_level_substr`] but for a single (possibly
/// multi-byte) `char`.
fn find_top_level_char(s: &str, needle: char) -> Option<usize> {
    let mut depth: i32 = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ if c == needle && depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// Parse a `(#name[.idx], N)` (or `(name[.idx], N)`) pair as used by
/// HS `nodeConc / nodePrem` (Proof.hs:33-36).  Returns the time-var
/// ROOT name (stripping any `.idx` freshen suffix) plus the natural N,
/// with the name spanned relative to `base_pos` (the source position of
/// `s`'s, i.e. the untrimmed slice's, first char).
fn parse_node_idx_pair(s: &str, base_pos: Pos) -> Option<(SpannedStr, u32)> {
    let leading_ws = s.len() - s.trim_start().len();
    let paren_pos = advance_pos(base_pos, &s[..leading_ws]);
    let trimmed = s.trim();
    let inside_raw = trimmed.strip_prefix('(')?.strip_suffix(')')?;
    let after_open_pos = advance_pos(paren_pos, "(");
    let inside_leading_ws = inside_raw.len() - inside_raw.trim_start().len();
    let inside_start = advance_pos(after_open_pos, &inside_raw[..inside_leading_ws]);
    let inside = inside_raw.trim();
    // Split into name-side / number-side on the first top-level `,`.
    let comma = inside.find(',')?;
    let name_part_raw = &inside[..comma];
    let num_part = inside[comma + 1..].trim();
    let name_part = name_part_raw.trim();
    let name_leading_ws = name_part_raw.len() - name_part_raw.trim_start().len();
    let name_part_pos = advance_pos(inside_start, &name_part_raw[..name_leading_ws]);
    // Strip optional `#` prefix; capture identifier-like characters up
    // to (but not including) any `.` (freshen suffix) or whitespace.
    let (name_no_hash_raw, name_no_hash_pos) = match name_part.strip_prefix('#') {
        Some(rest) => (rest, advance_pos(name_part_pos, "#")),
        None => (name_part, name_part_pos),
    };
    let hash_ws_len = name_no_hash_raw.len() - name_no_hash_raw.trim_start().len();
    let name_no_hash_start = advance_pos(name_no_hash_pos, &name_no_hash_raw[..hash_ws_len]);
    let name_no_hash = name_no_hash_raw.trim();
    let mut end = name_no_hash.len();
    for (i, c) in name_no_hash.char_indices() {
        if c == '.' || c.is_whitespace() {
            end = i;
            break;
        }
        if !is_ident_char(c) {
            return None;
        }
    }
    let var_name = &name_no_hash[..end];
    if var_name.is_empty() {
        return None;
    }
    let var_name_end = advance_pos(name_no_hash_start, var_name);
    let idx: u32 = num_part.parse().ok()?;
    Some((
        SpannedStr {
            content: var_name.to_string(),
            source: Source::Location(Location::from_positions(name_no_hash_start, var_name_end)),
        },
        idx,
    ))
}

struct GoalParser<'a> {
    lx: Lexer<'a>,
}

impl<'a> GoalParser<'a> {
    /// Try to match `[!]Name( <args> ) @ #t`  or
    /// `[!]Name( <args> ) ▶<idx> #t`.
    fn try_action_or_premise(&mut self) -> Option<GoalSpec> {
        let save = self.lx.pos();
        // Optional `!` prefix for persistent facts.
        self.lx.skip_ws();
        let persistent = self.lx.eat_str("!");
        self.lx.skip_ws();
        // Fact name: starts with uppercase.
        let name = self.lx.identifier()?;
        if !name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            self.lx.set_pos(save);
            return None;
        }
        self.lx.skip_ws();
        if !self.lx.eat_str("(") {
            self.lx.set_pos(save);
            return None;
        }
        // Read the args as raw balanced-paren text here (we don't deeply
        // parse the terms). `build_fact` later splits on top-level commas
        // and wraps each arg as `crate::ast::Term::Var` so the Fact struct
        // is well-formed.
        let args_text = self.read_balanced_paren()?;
        // After the `)`, expect `@` (action) or `▶<digit>` (premise).
        self.lx.skip_ws();
        if self.lx.eat_str("@") {
            self.lx.skip_ws();
            // Time variable: `#name[.idx]`.
            let _hash = self.lx.eat_str("#");
            let tvar = match self.lx.identifier() {
                Some(s) => s,
                None => {
                    self.lx.set_pos(save);
                    return None;
                }
            };
            // Capture `.idx` if present (HS's `ActionG i fa` keeps the
            // full timepoint LVar incl. idx — needed to re-render the head
            // as `#vk.6` not `#vk`, and for exact goal matching).
            let tidx = if self.lx.eat_str(".") {
                self.lx.natural().unwrap_or(0) as u32
            } else {
                0
            };
            return Some(GoalSpec::Action {
                fact: build_fact(persistent, name, &args_text),
                time_var: tvar,
                time_idx: tidx,
            });
        }
        // Premise marker: `▶<digit>` — UTF-8 ▶ is `\u{25B6}`, the
        // subscript digit follows.
        if self.lx.rest().starts_with('\u{25B6}') {
            // consume the ▶ (a single Unicode scalar)
            self.lx.bump();
            // HS always emits a Unicode subscript here: the pretty-printer
            // prints `▶ ++ subscript (show v)` (Constraints.hs:273-288) and the
            // parser `opRequires = symbol "▶" *> naturalSubscript`
            // (Token.hs:618-619, see line 619) accepts ONLY subscript digits.
            let idx_val = self.lx.natural_subscript()?;
            self.lx.skip_ws();
            let _hash = self.lx.eat_str("#");
            let tvar = match self.lx.identifier() {
                Some(s) => s,
                None => {
                    self.lx.set_pos(save);
                    return None;
                }
            };
            let tidx = if self.lx.eat_str(".") {
                self.lx.natural().unwrap_or(0) as u32
            } else {
                0
            };
            return Some(GoalSpec::Premise {
                fact: build_fact(persistent, name, &args_text),
                prem_idx: idx_val as usize,
                time_var: tvar,
                time_idx: tidx,
            });
        }
        self.lx.set_pos(save);
        None
    }

    fn read_balanced_paren(&mut self) -> Option<SpannedStr> {
        read_balanced_paren(&mut self.lx)
    }
}

/// Build a `Fact` from name + raw args text.  We don't fully parse the
/// argument terms — that's used only for diagnostics today.  The
/// arity (number of commas at top level) is the load-bearing field for
/// goal matching (matches the count of terms in the runtime LNFact).
fn build_fact(persistent: bool, name: crate::SpannedStr, args_text: &SpannedStr) -> Fact {
    use crate::ast::Term;
    let trimmed = args_text.trim();
    let args: Vec<Term> = if trimmed.is_empty() {
        Vec::new()
    } else {
        // `args_text.content` is the raw (untrimmed) `solve(...)` arg
        // text; walk the location past whatever leading whitespace
        // `trim()` stripped so each argument's span lines up with source.
        let base_pos = match &args_text.source {
            Source::Location(loc) => {
                let leading_ws = args_text.content.len() - args_text.content.trim_start().len();
                advance_pos(
                    Pos {
                        offset: loc.start,
                        line: loc.line,
                        col: loc.col,
                    },
                    &args_text.content[..leading_ws],
                )
            }
            _ => Pos::ZERO,
        };
        split_top_level_commas(trimmed, base_pos)
            .into_iter()
            .map(|name| {
                Term::Var(crate::ast::VarSpec {
                    name,
                    idx: 0,
                    sort: crate::ast::SortHint::Untagged,
                    typ: None,
                })
            })
            .collect()
    };
    Fact {
        persistent,
        name,
        args,
        annotations: Vec::new(),
    }
}

/// Advance `pos` by one char, replicating `Lexer::bump`'s line/col
/// accounting (tabs advance to the next 8-column stop, `\n` resets to
/// column 1) so spans built here agree with lexer-derived spans.
fn bump_pos(mut pos: Pos, c: char) -> Pos {
    pos.offset += c.len_utf8();
    match c {
        '\n' => {
            pos.line += 1;
            pos.col = 1;
        }
        '\t' => pos.col += 8 - ((pos.col - 1) % 8),
        _ => pos.col += 1,
    }
    pos
}

/// Advance `pos` past every char of `s` (see [`bump_pos`]).
fn advance_pos(pos: Pos, s: &str) -> Pos {
    s.chars().fold(pos, bump_pos)
}

/// Build the trimmed, spanned segment for one raw (untrimmed) comma
/// slice, given the source position of the slice's first char.
fn make_segment(raw: &str, start_pos: Pos) -> SpannedStr {
    let leading_ws = raw.len() - raw.trim_start().len();
    let trimmed_start = advance_pos(start_pos, &raw[..leading_ws]);
    let trimmed = raw.trim();
    let trimmed_end = advance_pos(trimmed_start, trimmed);
    SpannedStr {
        content: trimmed.to_string(),
        source: Source::Location(Location::from_positions(trimmed_start, trimmed_end)),
    }
}

/// Split `s` at top-level commas — ignores commas inside any kind of
/// bracket (`()`, `<>`, `[]`, `{}`) — returning each segment trimmed of
/// surrounding whitespace, spanned relative to `base_pos` (the source
/// position of `s`'s first char).
fn split_top_level_commas(s: &str, base_pos: Pos) -> Vec<SpannedStr> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut seg_start = base_pos;
    let mut pos = base_pos;
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '<' | '[' | '{' => {
                depth += 1;
                cur.push(c);
            }
            ')' | '>' | ']' | '}' => {
                depth -= 1;
                cur.push(c);
            }
            ',' if depth == 0 => {
                out.push(make_segment(&cur, seg_start));
                cur.clear();
                pos = bump_pos(pos, c);
                seg_start = pos;
                continue;
            }
            _ => cur.push(c),
        }
        pos = bump_pos(pos, c);
    }
    if !cur.is_empty() {
        out.push(make_segment(&cur, seg_start));
    }
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "proof_tree_tests.rs"]
mod tests;
