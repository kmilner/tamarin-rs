// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Jannik Dreier, Benedikt Schmidt, Robert Künnemann, Philip
//   Lukert, Charlie Jacomme, Felix Linker, Kevin Morio, Ralf Sasse, "Tom"
//   (github BTom-GH), "sans-sucre" (github), Johannes Wocker, and other
//   minor contributors (see upstream git history)
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
use crate::lexer::{is_ident_char, Lexer};

#[derive(Debug, Clone)]
pub struct ProofTreeParseError {
    pub line: u32,
    pub col: u32,
    pub msg: String,
}

impl std::fmt::Display for ProofTreeParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "proof-tree parse error at line {} col {}: {}",
            self.line, self.col, self.msg)
    }
}
impl std::error::Error for ProofTreeParseError {}

/// Parse the raw skeleton text into a [`ParsedProofTree`].  Returns
/// `Err` if the token stream doesn't conform to the HS grammar — the
/// caller (parser.rs `try_proof_skeleton`) downgrades the failure to
/// `tree: None` so the lemma is at least readable, and replay falls
/// back to auto-prover at the top.
pub fn parse_proof_tree(raw: &str) -> Result<ParsedProofTree, ProofTreeParseError> {
    let mut p = TreeParser { lx: Lexer::new(raw) };
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
/// accounting for nested parens.  Returns the inner text (excluding the final
/// `)`, which is consumed), or `None` on EOF before the closing paren.
fn read_balanced_paren(lx: &mut Lexer<'_>) -> Option<String> {
    let mut s = String::new();
    let mut depth: i32 = 1;
    while depth > 0 {
        match lx.peek() {
            None => return None,
            Some('(') => { s.push('('); lx.bump(); depth += 1; }
            Some(')') => {
                depth -= 1;
                if depth == 0 { lx.bump(); break; }
                s.push(')'); lx.bump();
            }
            Some(c) => { s.push(c); lx.bump(); }
        }
    }
    Some(s)
}

struct TreeParser<'a> {
    lx: Lexer<'a>,
}

impl<'a> TreeParser<'a> {
    fn err(&self, msg: impl Into<String>) -> ProofTreeParseError {
        let (line, col) = self.lx.line_col();
        ProofTreeParseError { line, col, msg: msg.into() }
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
            return Ok(ParsedProofTree { method: m, cases: Vec::new() });
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

    /// HS `oneCase` (Proof.hs:115):
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
        if self.try_kw("sorry") { return Ok(ParsedMethod::Sorry); }
        if self.try_kw("simplify") { return Ok(ParsedMethod::Simplify); }
        if self.try_kw("contradiction") { return Ok(ParsedMethod::Contradiction); }
        if self.try_kw("induction") { return Ok(ParsedMethod::Induction); }
        if self.try_kw("INVALIDATED") { return Ok(ParsedMethod::Invalidated); }
        if self.try_kw("UNFINISHABLE") { return Ok(ParsedMethod::Unfinishable); }
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
            let spec = parse_goal_spec(&inner);
            return Ok(ParsedMethod::SolveGoal(spec, inner));
        }
        // Unrecognised token — capture the next identifier-like word
        // so we can carry it through to `Other(...)`.
        let save = self.lx.pos();
        let mut word = String::new();
        while let Some(c) = self.lx.peek() {
            if c.is_whitespace() || c == '(' || c == ')' { break; }
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
        if self.try_kw(kw) { Ok(()) } else {
            Err(self.err(format!("expected `{}`", kw)))
        }
    }

    fn require_punct(&mut self, p: &str) -> Result<(), ProofTreeParseError> {
        self.lx.skip_ws();
        if self.lx.eat_str(p) { Ok(()) }
        else { Err(self.err(format!("expected `{}`", p))) }
    }

    /// Identifier with extended chars: HS's `identifier` accepts
    /// alphanum + `_` (Token.hs:224 `identLetter = alphaNum <|> oneOf "_"`)
    /// and emits names like `Server_ReceiveOTP_NewSession_case_1`.
    fn identifier_extended(&mut self) -> Result<String, ProofTreeParseError> {
        self.lx.skip_ws();
        let mut s = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphanumeric() || c == '_' => {
                s.push(c); self.lx.bump();
            }
            _ => return Err(self.err("expected identifier")),
        }
        while let Some(c) = self.lx.peek() {
            if is_ident_char(c) { s.push(c); self.lx.bump(); }
            else { break; }
        }
        self.lx.skip_ws();
        Ok(s)
    }

    /// Read raw text between an already-consumed `(` and its matching
    /// `)`, accounting for nested parens.  Returns the inner text
    /// (excluding the final `)` which is consumed).
    fn read_balanced_paren(&mut self) -> Result<String, ProofTreeParseError> {
        read_balanced_paren(&mut self.lx)
            .ok_or_else(|| self.err("unterminated `(` in solve(...)"))
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
/// (`gf1 ∥ gf2 ∥ ...` — HS `disjSplitGoal`, Proof.hs:61), Chain
/// (`(#i,n) ~~> (#j,m)` — HS `chainGoal`, Proof.hs:59), Split
/// (`splitEqs(N)` — HS `eqSplitGoal`, Proof.hs:70-72), then Subterm
/// (`<a> ⊏ <b>` — HS `stSplitGoal`, Proof.hs:63-66).  Anything else
/// lands in `GoalSpec::Raw` and the walker falls back to the
/// auto-prover.
pub fn parse_goal_spec(raw: &str) -> GoalSpec {
    let trimmed = raw.trim();
    let mut p = GoalParser { lx: Lexer::new(trimmed) };
    if let Some(spec) = p.try_action_or_premise() {
        return spec;
    }
    if let Some(spec) = try_disj_split(trimmed) {
        return spec;
    }
    if let Some(spec) = try_chain_split(trimmed) {
        return spec;
    }
    if let Some(spec) = try_eq_split(trimmed) {
        return spec;
    }
    if let Some(spec) = try_subterm_split(trimmed) {
        return spec;
    }
    GoalSpec::Raw(trimmed.to_string())
}

/// Try to split the goal-spec text on top-level `∥` (HS U+2225, the
/// disjunction-split separator).  Returns `GoalSpec::Disj { alts }` if
/// at least one `∥` appears at top-level (depth-0 of `()/[]/<>/{}`),
/// classifying each disjunct by its shape (`∀ / ∃ / NonQuant`).
///
/// Mirrors HS `disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula
/// (symbol "∥")` (Theory/Text/Parser/Proof.hs:61).  HS parses each
/// disjunct as a full `Guarded` value — we capture only the shape so
/// we can match against an existing `Goal::Disj` in `sys.goals` at
/// replay time without rebuilding LVar identities.
fn try_disj_split(text: &str) -> Option<GoalSpec> {
    let parts = split_top_level_disj(text);
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
    let alts: Vec<DisjAlt> = parts.iter().map(|p| classify_disj_alt(p)).collect();
    // HS-faithful disambiguation: when multiple Disj goals in
    // sys.goals share the same alt shape signature (e.g. binding-A
    // and binding-B instantiations of the same IH-body 5-alt disj),
    // the shape-only `disj_alts_match` can't distinguish them.  HS
    // parses each alt as a full `Guarded` with concrete LVar
    // identities (Proof.hs:61), enabling structural match in
    // sys.goals.  We can't easily reconstruct those identities, but
    // we CAN capture each alt's normalized text and use it as a
    // tie-breaker when shape matching is ambiguous.  See
    // Yubikey::slightly_weaker_invariant at
    // /non_empty_trace/case_1: both binding-A's disj (alt[0] =
    // `last(#t2)`) and binding-B's (alt[0] = `last(#t1)`) match the
    // 5-alt NonQuant shape; without alt-text matching, match_goal
    // picks the wrong one and the proof diverges.
    let alt_texts: Vec<String> = parts.iter().map(|p| {
        let s = strip_outer_parens(p.trim()).trim().to_string();
        normalize_disj_alt_text(&s)
    }).collect();
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
    s.chars().filter(|c| !c.is_whitespace() && *c != '#').collect()
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
            '(' | '[' | '{' => { depth += 1; cur.push(c); }
            ')' | ']' | '}' => { depth -= 1; cur.push(c); }
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
        return DisjAlt::All { n_vars: count_quant_vars(rest) };
    }
    if let Some(rest) = t.strip_prefix('\u{2203}') {
        return DisjAlt::Ex { n_vars: count_quant_vars(rest) };
    }
    DisjAlt::NonQuant
}

/// Strip ONE balanced layer of outer parens.  `"(x ∨ y)"` → `"x ∨ y"`;
/// `"x ∨ y"` returns unchanged.  Only strips if the opening `(` at
/// position 0 matches a closing `)` at the very end of the string with
/// no intermediate depth-0 break.
fn strip_outer_parens(s: &str) -> &str {
    let bytes = s.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'(' || bytes[bytes.len()-1] != b')' {
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
                        return &s[1..s.len()-1];
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
/// `name.idx` (HS `LVar` Show, LTerm.hs:529-532, via
/// `ppVars = fsep . map (text . show)`, Guarded.hs:862), e.g.
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
            if !in_token { n += 1; in_token = true; }
        } else {
            in_token = false;
        }
    }
    n
}

/// Try to parse a chain-split goal-text: `(#i, N) ~~> (#j, M)`.
///
/// HS reference: `chainGoal = ChainG <$> (try (nodeConc <* opChain))
/// <*> nodePrem` (Theory/Text/Parser/Proof.hs:59) where
/// `nodeConc/nodePrem = parens ((,) <$> nodevar <*> (comma *> natural))`
/// (Proof.hs:33-36).  The operator `~~>` is the HS pretty rendering
/// (Constraints.hs:269-270).
///
/// We extract the time-var ROOT name (stripping any trailing `.N`
/// freshen-suffix that HS's pretty-printer can emit) and the natural
/// idx for each side.  The matcher disambiguates by these.
fn try_chain_split(text: &str) -> Option<GoalSpec> {
    // Find the top-level `~~>` separator.  HS prints exactly `~~>`
    // (operator_ "~~>" inside fsep) so a plain substring search suffices
    // — we only need to ensure we're at depth 0 of `()/[]/{}` to skip
    // any `~~>` that hypothetically appeared inside a tuple (none do in
    // practice but we are defensive).
    let arrow_pos = find_top_level_substr(text, "~~>")?;
    let lhs = text[..arrow_pos].trim();
    let rhs = text[arrow_pos + 3..].trim();
    let (src_var, conc_idx) = parse_node_idx_pair(lhs)?;
    let (tgt_var, prem_idx) = parse_node_idx_pair(rhs)?;
    Some(GoalSpec::Chain { src_var, conc_idx, tgt_var, prem_idx })
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
fn try_subterm_split(text: &str) -> Option<GoalSpec> {
    const SUBTERM_OP: char = '\u{228F}';
    let pos = find_top_level_char(text, SUBTERM_OP)?;
    let small_raw = text[..pos].trim().to_string();
    let big_raw = text[pos + SUBTERM_OP.len_utf8()..].trim().to_string();
    if small_raw.is_empty() || big_raw.is_empty() {
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
    if end == 0 { return None; }
    let n: i64 = rest[..end].parse().ok()?;
    let tail = rest[end..].trim_start();
    if !tail.starts_with(')') { return None; }
    Some(GoalSpec::Split { split_id: n })
}

/// Locate the byte-offset of the first occurrence of `needle` at
/// top-level depth (depth 0 of `()/[]/{}`).  Returns `None` if absent.
fn find_top_level_substr(s: &str, needle: &str) -> Option<usize> {
    let bs = s.as_bytes();
    let nb = needle.as_bytes();
    if nb.is_empty() || bs.len() < nb.len() { return None; }
    let mut depth: i32 = 0;
    let mut i = 0;
    while i + nb.len() <= bs.len() {
        let c = bs[i];
        if c == b'(' || c == b'[' || c == b'{' { depth += 1; }
        else if c == b')' || c == b']' || c == b'}' { depth -= 1; }
        else if depth == 0 && &bs[i..i + nb.len()] == nb {
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
/// ROOT name (stripping any `.idx` freshen suffix) plus the natural N.
fn parse_node_idx_pair(s: &str) -> Option<(String, u32)> {
    let trimmed = s.trim();
    let inside = trimmed.strip_prefix('(')?.strip_suffix(')')?.trim();
    // Split into name-side / number-side on the first top-level `,`.
    let comma = inside.find(',')?;
    let name_part = inside[..comma].trim();
    let num_part = inside[comma + 1..].trim();
    // Strip optional `#` prefix; capture identifier-like characters up
    // to (but not including) any `.` (freshen suffix) or whitespace.
    let name_no_hash = name_part.strip_prefix('#').unwrap_or(name_part).trim();
    let mut end = name_no_hash.len();
    for (i, c) in name_no_hash.char_indices() {
        if c == '.' || c.is_whitespace() { end = i; break; }
        if !is_ident_char(c) { return None; }
    }
    let var_name = name_no_hash[..end].to_string();
    if var_name.is_empty() { return None; }
    let idx: u32 = num_part.parse().ok()?;
    Some((var_name, idx))
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
                None => { self.lx.set_pos(save); return None; }
            };
            // Capture `.idx` if present (HS's `ActionG i fa` keeps the
            // full timepoint LVar incl. idx — needed to re-render the head
            // as `#vk.6` not `#vk`, and for exact goal matching).
            let tidx = if self.lx.eat_str(".") {
                self.lx.natural().unwrap_or(0) as u32
            } else { 0 };
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
            // prints `▶ ++ subscript (show v)` (Constraints.hs:273) and the
            // parser `opRequires = symbol "▶" *> naturalSubscript`
            // (Token.hs:619) accepts ONLY subscript digits.
            let idx_val = self.lx.natural_subscript()?;
            self.lx.skip_ws();
            let _hash = self.lx.eat_str("#");
            let tvar = match self.lx.identifier() {
                Some(s) => s,
                None => { self.lx.set_pos(save); return None; }
            };
            let tidx = if self.lx.eat_str(".") {
                self.lx.natural().unwrap_or(0) as u32
            } else { 0 };
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

    fn read_balanced_paren(&mut self) -> Option<String> {
        read_balanced_paren(&mut self.lx)
    }
}

/// Build a `Fact` from name + raw args text.  We don't fully parse the
/// argument terms — that's used only for diagnostics today.  The
/// arity (number of commas at top level) is the load-bearing field for
/// goal matching (matches the count of terms in the runtime LNFact).
fn build_fact(persistent: bool, name: String, args_text: &str) -> Fact {
    use crate::ast::Term;
    let trimmed = args_text.trim();
    let args: Vec<Term> = if trimmed.is_empty() {
        Vec::new()
    } else {
        split_top_level_commas(trimmed)
            .into_iter()
            .map(|s| Term::Var(crate::ast::VarSpec {
                name: s.trim().to_string(),
                idx: 0,
                sort: crate::ast::SortHint::Untagged,
                typ: None,
            }))
            .collect()
    };
    Fact { persistent, name, args, annotations: Vec::new() }
}

/// Split a string at top-level commas — ignores commas inside any kind
/// of bracket (`()`, `<>`, `[]`, `{}`).
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '<' | '[' | '{' => { depth += 1; cur.push(c); }
            ')' | '>' | ']' | '}' => { depth -= 1; cur.push(c); }
            ',' if depth == 0 => { out.push(std::mem::take(&mut cur)); }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() { out.push(cur); }
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaf_by_sorry() {
        let t = parse_proof_tree("by sorry").expect("parse");
        assert_eq!(t.method, ParsedMethod::Sorry);
        assert!(t.cases.is_empty());
    }

    #[test]
    fn leaf_by_contradiction() {
        let t = parse_proof_tree("by contradiction").expect("parse");
        assert_eq!(t.method, ParsedMethod::Contradiction);
    }

    #[test]
    fn solved_leaf() {
        let t = parse_proof_tree("SOLVED").expect("parse");
        assert_eq!(t.method, ParsedMethod::SolvedLeaf);
    }

    #[test]
    fn count_quant_vars_with_dotted_idx() {
        // Bound vars with idx>0 render as `name.idx` (HS LVar Show).
        // The `.idx` suffix must NOT terminate the count; only the
        // body-terminator `.` (followed by ws/EOF) ends the var list.
        assert_eq!(count_quant_vars("x y #i.1 #j."), 4);
        assert_eq!(count_quant_vars("t.5 x."), 2);
        // Trailing dotted var before the body terminator.
        assert_eq!(count_quant_vars("#t #t.1."), 2);
        // No dotted suffixes.
        assert_eq!(count_quant_vars("a b c."), 3);
    }

    #[test]
    fn induction_with_case_block() {
        let src = "
            induction
            case empty_trace
            by contradiction
            next
            case non_empty_trace
            by sorry
            qed
        ";
        let t = parse_proof_tree(src).expect("parse");
        assert_eq!(t.method, ParsedMethod::Induction);
        assert_eq!(t.cases.len(), 2);
        assert_eq!(t.cases[0].0, "empty_trace");
        assert_eq!(t.cases[0].1.method, ParsedMethod::Contradiction);
        assert_eq!(t.cases[1].0, "non_empty_trace");
        assert_eq!(t.cases[1].1.method, ParsedMethod::Sorry);
    }

    #[test]
    fn identifier_stops_at_hyphen() {
        // HS `identifier` (Token.hs:224 `identLetter = alphaNum <|> oneOf
        // "_"`) does NOT accept `-`, so a case name like `foo-bar` is
        // tokenised as the identifier `foo`; the `-bar` is not part of the
        // case name.  This locks in HS-faithful identifier termination.
        let t = parse_proof_tree("induction case foo-bar by sorry qed").expect("parse");
        assert_eq!(t.method, ParsedMethod::Induction);
        assert_eq!(t.cases.len(), 1);
        assert_eq!(t.cases[0].0, "foo");
    }

    #[test]
    fn bare_inter_method_without_child_is_err() {
        // HS `interProof` (Proof.hs:109-113) has no childless-leaf branch:
        // a method must be followed by either a `case`-block (`next`/`qed`)
        // or a recursive `proofSkeleton`.  A bare `simplify` with nothing
        // after it is a parse error in the v1.13.0 prover ("unexpected ...,
        // expecting case/qed/SOLVED/by/sorry/simplify/solve/...").  We must
        // mirror that failure (the caller downgrades `Err` to `tree: None`
        // and replays via the auto-prover), so it must NOT parse to a leaf.
        assert!(parse_proof_tree("simplify").is_err());
        assert!(parse_proof_tree("induction").is_err());
        // A method followed by an inline sub-proof DOES parse (the inline
        // single-child `""` subproof branch), and the leaf form is `by`.
        assert!(parse_proof_tree("simplify by sorry").is_ok());
        assert!(parse_proof_tree("by simplify").is_ok());
    }

    #[test]
    fn solve_action_goal() {
        let src = "solve( Foo( x ) @ #i )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Action { fact, time_var, time_idx }, _) => {
                assert_eq!(fact.name, "Foo");
                assert_eq!(fact.args.len(), 1);
                assert_eq!(time_var, "i");
                assert_eq!(*time_idx, 0);
            }
            other => panic!("expected Action solve goal, got {:?}", other),
        }
        assert_eq!(t.cases.len(), 1);
        assert_eq!(t.cases[0].0, "");
        assert_eq!(t.cases[0].1.method, ParsedMethod::Sorry);
    }

    #[test]
    fn solve_action_goal_captures_timepoint_idx() {
        // HS's `ActionG i fa` carries the full timepoint LVar incl. idx;
        // dropping `.6` would re-render the head as `#vk` (regression) and
        // break exact goal matching.
        let src = "solve( !KU( ~AK ) @ #vk.6 )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Action { time_var, time_idx, .. }, _) => {
                assert_eq!(time_var, "vk");
                assert_eq!(*time_idx, 6);
            }
            other => panic!("expected Action solve goal, got {:?}", other),
        }
    }

    #[test]
    fn solve_premise_goal_subscript() {
        // ▶₀ (subscript 0)
        let src = "solve( Server( pid, sid, otc ) \u{25B6}\u{2080} #t1 )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Premise { fact, prem_idx, time_var, time_idx }, _) => {
                assert_eq!(fact.name, "Server");
                assert_eq!(*prem_idx, 0);
                assert_eq!(time_var, "t1");
                assert_eq!(*time_idx, 0);
            }
            other => panic!("expected Premise solve goal, got {:?}", other),
        }
    }

    #[test]
    fn solve_persistent_premise() {
        // !F_Fact(...) ▶₂ #i
        let src = "solve( !F_OutSessKeys( a, b ) \u{25B6}\u{2082} #i )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Premise { fact, prem_idx, .. }, _) => {
                assert!(fact.persistent);
                assert_eq!(fact.name, "F_OutSessKeys");
                assert_eq!(*prem_idx, 2);
            }
            other => panic!("expected persistent premise, got {:?}", other),
        }
    }

    #[test]
    fn nested_case_block() {
        let src = "
            solve( Foo( a ) @ #i )
              case case_1
              solve( Bar( b ) @ #j )
                case case_a
                by sorry
              next
                case case_b
                by contradiction
              qed
            next
              case case_2
              by sorry
            qed
        ";
        let t = parse_proof_tree(src).expect("parse");
        assert!(matches!(t.method, ParsedMethod::SolveGoal(_, _)));
        assert_eq!(t.cases.len(), 2);
        assert_eq!(t.cases[0].0, "case_1");
        assert_eq!(t.cases[0].1.cases.len(), 2);
        assert_eq!(t.cases[0].1.cases[0].0, "case_a");
        assert_eq!(t.cases[0].1.cases[1].0, "case_b");
        assert_eq!(t.cases[1].0, "case_2");
    }

    #[test]
    fn raw_goalspec_fallback() {
        // Unknown gibberish goal-text — should fall back to
        // GoalSpec::Raw.  All recognised forms (Action, Premise, Disj,
        // Chain, Subterm, Split) need specific structural markers.
        let src = "solve( garbage_no_marker ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Raw(_), _) => {}
            other => panic!("expected Raw goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_chain_goal() {
        // HS `chainGoal` (Proof.hs:59) pretty-print:
        // `(#i, 0) ~~> (#j, 2)`  (NodeConc ~~> NodePrem).
        let src = "solve( (#i, 0) ~~> (#j, 2) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Chain { src_var, conc_idx, tgt_var, prem_idx }, _) => {
                assert_eq!(src_var, "i");
                assert_eq!(*conc_idx, 0);
                assert_eq!(tgt_var, "j");
                assert_eq!(*prem_idx, 2);
            }
            other => panic!("expected Chain goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_chain_goal_with_freshen_suffix() {
        // HS sometimes emits a freshen suffix like `#i.2` on the
        // pretty-printed nodevar; the parser must strip it.
        let src = "solve( (#i.5, 1) ~~> (#j.7, 0) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Chain { src_var, conc_idx, tgt_var, prem_idx }, _) => {
                // Freshen suffix stripped from the var ROOT.
                assert_eq!(src_var, "i");
                assert_eq!(*conc_idx, 1);
                assert_eq!(tgt_var, "j");
                assert_eq!(*prem_idx, 0);
            }
            other => panic!("expected Chain goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_subterm_goal() {
        // HS `stSplitGoal` (Proof.hs:63-66) pretty-print:
        // `<term> ⊏ <term>` (U+228F).
        let src = "solve( foo(a, b) \u{228F} bar(c) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Subterm { small_raw, big_raw }, _) => {
                assert_eq!(small_raw, "foo(a, b)");
                assert_eq!(big_raw, "bar(c)");
            }
            other => panic!("expected Subterm goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_split_goal() {
        // HS `eqSplitGoal` (Proof.hs:70-72) pretty-print: `splitEqs(N)`.
        let src = "solve( splitEqs(42) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Split { split_id }, _) => {
                assert_eq!(*split_id, 42);
            }
            other => panic!("expected Split goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_split_goal_zero() {
        // Boundary: split id 0 (the first id minted by EquationStore).
        let src = "solve( splitEqs(0) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Split { split_id }, _) => {
                assert_eq!(*split_id, 0);
            }
            other => panic!("expected Split goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_disj_two_alts() {
        // `solve( (last(#t1))  ∥ (#t1 < #t2) )` — two non-quant alts.
        let src = "solve( (last(#t1)) \u{2225} (#t1 < #t2) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Disj { alts, alt_texts: _ }, _) => {
                assert_eq!(alts.len(), 2);
                assert!(matches!(alts[0], DisjAlt::NonQuant));
                assert!(matches!(alts[1], DisjAlt::NonQuant));
            }
            other => panic!("expected Disj goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_disj_quantified_alts() {
        // Yubikey slightly_weaker_invariant first solve(...) — 2 alts:
        // ∀-quantified with 7 vars, ∃-quantified with 5 vars.
        let src = "solve( (\u{2200} pid otc1 tc1 otc2 tc2 #t1 #t2. \
                          (last(#t1)) \u{2228} (last(#t2))) \u{2225} \
                          (\u{2203} #t1 #t2 a b c. (last(#t1))) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Disj { alts, alt_texts: _ }, _) => {
                assert_eq!(alts.len(), 2);
                assert_eq!(alts[0], DisjAlt::All { n_vars: 7 });
                assert_eq!(alts[1], DisjAlt::Ex { n_vars: 5 });
            }
            other => panic!("expected Disj goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_disj_five_alts() {
        // Yubikey slightly_weaker_invariant inner solve — 5 non-quant alts.
        let src = "solve( (last(#t2)) \u{2225} (last(#t1)) \u{2225} \
                          ((#t1 < #t2) \u{2227} (last(#t3))) \u{2225} \
                          (#t2 < #t1) \u{2225} (#t1 = #t2) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Disj { alts, alt_texts: _ }, _) => {
                assert_eq!(alts.len(), 5);
                for a in alts.iter() { assert!(matches!(a, DisjAlt::NonQuant)); }
            }
            other => panic!("expected Disj goal-spec, got {:?}", other),
        }
    }
}
