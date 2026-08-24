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
//! A token this grammar does not accept fails the parse, as it does in HS;
//! the caller (parser.rs `try_proof_skeleton`) downgrades the failure to
//! `tree: None`.

use crate::ast::{ParsedMethod, ParsedProofTree};
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
            // `solve( <goal> )`.  HS reads `parens goal`
            // (Theory/Text/Parser/Proof.hs:80); the parenthesised text is
            // framed here and handed to the same grammar.
            self.require_punct("(")?;
            let inner = self.read_balanced_paren()?;
            // `read_balanced_paren` consumed the matching `)`.
            let spec = crate::parser::parse_goal_str(&inner, self.parent)
                .map_err(|e| self.err(format!("in solve( ... ): {}", e)))?;
            return Ok(ParsedMethod::SolveGoal(spec));
        }
        // HS `proofMethod` (Theory/Text/Parser/Proof.hs:75-85) has no
        // catch-all alternative, so any other token fails the skeleton parse.
        Err(self.err("expected proof method"))
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
// Tests
// =============================================================================

#[cfg(test)]
#[path = "proof_tree_tests.rs"]
mod tests;
