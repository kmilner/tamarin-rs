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
//! `solve( ... )` step is read by [`crate::parser::parse_parens_goal`].
//! A token this grammar does not accept fails the containing theory parse, as
//! it does in HS.

use crate::ast::{ParsedMethod, ParsedProofTree};
use crate::lexer::{is_ident_char, Lexer, Pos};
use crate::parser::{Message, ParseError, Parser};

#[derive(Debug, Clone)]
pub struct ProofTreeParseError {
    pub offset: usize,
    pub line: u32,
    pub col: u32,
    pub msg: String,
    inner: Option<ParseError>,
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
impl std::error::Error for ProofTreeParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.inner
            .as_ref()
            .map(|error| error as &(dyn std::error::Error + 'static))
    }
}

/// Parse the raw skeleton text into a [`ParsedProofTree`]. Returns `Err` if
/// the complete token stream does not conform to the HS grammar.
///
/// `parent` is the theory parser the skeleton text came out of, whose symbol
/// state [`crate::parser::parse_parens_goal`] needs to read the goal inside a
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
    p.lx.skip_ws();
    if !p.lx.is_eof() {
        return Err(p.err("unexpected trailing proof text"));
    }
    Ok(tree)
}

/// Validate a stored diff-proof skeleton against HS `diffProofSkeleton`
/// (`Theory/Text/Parser/Proof.hs:128-144`). Diff proofs have their own method
/// type and are not executable by the regular Rust replay engine, so callers
/// retain their raw text rather than manufacturing a [`ParsedProofTree`].
pub(crate) fn validate_diff_proof_tree<'a>(
    raw: &'a str,
    parent: &'a Parser<'a>,
) -> Result<(), ProofTreeParseError> {
    let mut p = TreeParser {
        lx: Lexer::new(raw),
        parent,
    };
    p.diff_proof_skeleton()?;
    p.lx.skip_ws();
    if !p.lx.is_eof() {
        return Err(p.err("unexpected trailing proof text"));
    }
    Ok(())
}

struct TreeParser<'a> {
    lx: Lexer<'a>,
    parent: &'a Parser<'a>,
}

impl<'a> TreeParser<'a> {
    fn err(&self, msg: impl Into<String>) -> ProofTreeParseError {
        let pos = self.lx.pos();
        ProofTreeParseError {
            offset: pos.offset,
            line: pos.line,
            col: pos.col,
            msg: msg.into(),
            inner: None,
        }
    }

    fn nested_error(&self, error: ParseError, base: Pos) -> ProofTreeParseError {
        let error = error.shifted(base.offset, self.lx.src());
        let (line, col) = error.line_column();
        ProofTreeParseError {
            offset: error.span().start as usize,
            line,
            col,
            msg: format!("in solve( ... ): {}", error.diagnostic_message()),
            inner: Some(error),
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
        // (Theory/Text/Parser/Proof.hs:111-112). `oneCase` starts with
        // `case <ident>`, while `sepBy` also accepts zero cases followed
        // immediately by `qed`. Otherwise HS
        // *requires* a recursive `proofSkeleton` (the inline single-child
        // subproof, named ""); there is NO childless-leaf branch — an
        // interProof method must be followed by a child.
        self.lx.skip_ws();
        if self.peek_kw("case") || self.peek_kw("qed") {
            let mut cases: Vec<(String, ParsedProofTree)> = Vec::new();
            // HS: sepBy oneCase "next" <* "qed"
            if self.peek_kw("case") {
                cases.push(self.one_case()?);
                while self.try_kw("next") {
                    cases.push(self.one_case()?);
                }
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
        // failing here; the containing theory parse fails as HS's does.
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
            // (Theory/Text/Parser/Proof.hs:80): the parentheses belong to the
            // goal grammar, so the term parser decides where the closing `)`
            // is and this lexer walks to the offset it stopped at, character
            // by character to keep its line and column right.
            self.lx.skip_ws();
            let start = self.lx.pos();
            let (spec, len) = crate::parser::parse_parens_goal(self.lx.rest(), self.parent)
                .map_err(|error| self.nested_error(error, start))?;
            let end = start.offset + len;
            while self.lx.pos().offset < end {
                self.lx.bump();
            }
            return Ok(ParsedMethod::SolveGoal(spec));
        }
        // HS `proofMethod` (Theory/Text/Parser/Proof.hs:75-85) has no
        // catch-all alternative, so any other token fails the skeleton parse.
        Err(self.err("expected proof method"))
    }

    /// HS `diffProofSkeleton` (Theory/Text/Parser/Proof.hs:128-144).
    fn diff_proof_skeleton(&mut self) -> Result<(), ProofTreeParseError> {
        self.lx.skip_ws();
        if self.try_kw("MIRRORED") {
            return Ok(());
        }
        if self.try_kw("by") {
            return self.diff_proof_method();
        }
        self.diff_proof_method()?;
        self.lx.skip_ws();
        if self.peek_kw("case") || self.peek_kw("qed") {
            if self.peek_kw("case") {
                self.diff_one_case()?;
                while self.try_kw("next") {
                    self.diff_one_case()?;
                }
            }
            return self.require_kw("qed");
        }
        self.diff_proof_skeleton()
    }

    fn diff_one_case(&mut self) -> Result<(), ProofTreeParseError> {
        self.require_kw("case")?;
        self.identifier_extended()?;
        self.diff_proof_skeleton()
    }

    /// HS `diffProofMethod` (Theory/Text/Parser/Proof.hs:118-126). A `step`
    /// wraps one ordinary proof method, not an ordinary proof skeleton.
    fn diff_proof_method(&mut self) -> Result<(), ProofTreeParseError> {
        self.lx.skip_ws();
        if self.try_kw("sorry")
            || self.try_kw("rule-equivalence")
            || self.try_kw("backward-search")
            || self.try_kw("ATTACK")
            || self.try_kw("UNFINISHABLEdiff")
        {
            return Ok(());
        }
        if self.try_kw("step") {
            if !self.lx.try_symbol("(") {
                return Err(self.err("expected `(`"));
            }
            self.proof_method()?;
            if !self.lx.try_symbol(")") {
                return Err(self.err("expected `)`"));
            }
            return Ok(());
        }
        Err(self.err("expected diff proof method"))
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
}

impl ProofTreeParseError {
    pub(crate) fn into_parse_error(self, base_offset: usize, source: &str) -> ParseError {
        if let Some(error) = self.inner {
            return error.shifted(base_offset, source);
        }
        let offset = base_offset.saturating_add(self.offset);
        let (line, col) = crate::parse_error::line_column(source, offset);
        ParseError::at(Pos { offset, line, col }, vec![Message::Message(self.msg)])
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "proof_tree_tests.rs"]
mod tests;
