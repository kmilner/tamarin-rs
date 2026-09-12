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
use crate::lexer::{is_ident_char, Lexer};
use crate::parse_error::ParseContext;
use crate::parser::{ParseError, Parser};

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
) -> Result<ParsedProofTree, ParseError> {
    let mut p = TreeParser {
        lx: Lexer::new(raw),
        parent,
    };
    let result = (|| {
        let tree = p.proof_skeleton()?;
        p.lx.skip_ws();
        if !p.lx.is_eof() {
            return Err(p.err_expect("end of proof"));
        }
        Ok(tree)
    })();
    p.lx.finish(result)
        .map_err(|error| error.with_context(ParseContext::Proof))
}

/// Validate a stored diff-proof skeleton against HS `diffProofSkeleton`
/// (`Theory/Text/Parser/Proof.hs:128-144`). Diff proofs have their own method
/// type and are not executable by the regular Rust replay engine, so callers
/// retain their raw text rather than manufacturing a [`ParsedProofTree`].
pub(crate) fn validate_diff_proof_tree<'a>(
    raw: &'a str,
    parent: &'a Parser<'a>,
) -> Result<(), ParseError> {
    let mut p = TreeParser {
        lx: Lexer::new(raw),
        parent,
    };
    let result = (|| {
        p.diff_proof_skeleton()?;
        p.lx.skip_ws();
        if !p.lx.is_eof() {
            return Err(p.err_expect("end of proof"));
        }
        Ok(())
    })();
    p.lx.finish(result)
        .map_err(|error| error.with_context(ParseContext::Proof))
}

struct TreeParser<'a> {
    lx: Lexer<'a>,
    parent: &'a Parser<'a>,
}

impl<'a> TreeParser<'a> {
    fn err_expect(&self, expected: impl Into<String>) -> ParseError {
        ParseError::expected(self.lx.pos(), expected, self.lx.peek())
    }

    /// HS `proofSkeleton` (Theory/Text/Parser/Proof.hs:98-115).
    fn proof_skeleton(&mut self) -> Result<ParsedProofTree, ParseError> {
        struct Pending {
            tree: ParsedProofTree,
            name: String,
            block: bool,
        }
        let mut pending: Vec<Pending> = Vec::new();
        'parse: loop {
            self.lx.skip_ws();
            let solved = self.try_kw("SOLVED");
            let terminal = solved || self.try_kw("by");
            let method = if solved {
                ParsedMethod::SolvedLeaf
            } else {
                self.proof_method()?
            };
            let mut tree = ParsedProofTree {
                method,
                cases: Vec::new(),
            };
            if !terminal {
                self.lx.skip_ws();
                let block = self.peek_kw("case") || self.peek_kw("qed");
                if block && self.try_kw("qed") {
                    // A case block may be empty.
                } else {
                    // Without a case block, an intermediate method requires
                    // one inline child; a bare method is not a complete proof.
                    let name = if block {
                        self.case_name()?
                    } else {
                        String::new()
                    };
                    pending.push(Pending { tree, name, block });
                    continue;
                }
            }
            // Complete inline parents until a case block needs another child.
            while let Some(mut parent) = pending.pop() {
                if parent.block {
                    parent.tree.cases.push((parent.name, tree));
                    if self.try_kw("next") {
                        parent.name = self.case_name()?;
                        pending.push(parent);
                        continue 'parse;
                    }
                    self.require_kw("qed")?;
                } else {
                    parent.tree.cases = vec![(parent.name, tree)];
                }
                tree = parent.tree;
            }
            return Ok(tree);
        }
    }

    /// HS `oneCase` begins with `case` and an extended identifier.
    fn case_name(&mut self) -> Result<String, ParseError> {
        self.require_kw("case")?;
        self.identifier_extended()
    }

    /// HS `proofMethod` (Theory/Text/Parser/Proof.hs:76-85).
    fn proof_method(&mut self) -> Result<ParsedMethod, ParseError> {
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
                .map_err(|error| error.shifted(start, self.lx.src()))?;
            let end = start.offset + len;
            while self.lx.pos().offset < end {
                self.lx.bump();
            }
            return Ok(ParsedMethod::SolveGoal(spec));
        }
        // HS `proofMethod` (Theory/Text/Parser/Proof.hs:75-85) has no
        // catch-all alternative, so any other token fails the skeleton parse.
        Err(self.err_expect("proof method"))
    }

    /// HS `diffProofSkeleton` (Theory/Text/Parser/Proof.hs:128-144).
    fn diff_proof_skeleton(&mut self) -> Result<(), ParseError> {
        // Inline continuations need no retained output. Only case blocks must
        // remember their depth and resume after a completed child.
        let mut blocks = 0usize;
        'parse: loop {
            self.lx.skip_ws();
            if !self.try_kw("MIRRORED") {
                if self.try_kw("by") {
                    self.diff_proof_method()?;
                } else {
                    self.diff_proof_method()?;
                    self.lx.skip_ws();
                    if self.peek_kw("case") {
                        self.case_name()?;
                        blocks += 1;
                        continue;
                    }
                    if !self.try_kw("qed") {
                        continue;
                    }
                }
            }
            while blocks > 0 {
                blocks -= 1;
                if self.try_kw("next") {
                    self.case_name()?;
                    blocks += 1;
                    continue 'parse;
                }
                self.require_kw("qed")?;
            }
            return Ok(());
        }
    }

    /// HS `diffProofMethod` (Theory/Text/Parser/Proof.hs:118-126). A `step`
    /// wraps one ordinary proof method, not an ordinary proof skeleton.
    fn diff_proof_method(&mut self) -> Result<(), ParseError> {
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
                return Err(self.err_expect("`(`"));
            }
            self.proof_method()?;
            if !self.lx.try_symbol(")") {
                return Err(self.err_expect("`)`"));
            }
            return Ok(());
        }
        Err(self.err_expect("diff proof method"))
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

    fn require_kw(&mut self, kw: &str) -> Result<(), ParseError> {
        if self.try_kw(kw) {
            Ok(())
        } else {
            Err(self.err_expect(format!("`{}`", kw)))
        }
    }

    /// Identifier with extended chars: HS's `identifier` accepts
    /// alphanum + `_` (Token.hs:214-230, see line 224 `identLetter = alphaNum <|> oneOf "_"`)
    /// and emits names like `Server_ReceiveOTP_NewSession_case_1`.
    fn identifier_extended(&mut self) -> Result<String, ParseError> {
        self.lx.skip_ws();
        let mut s = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphanumeric() || c == '_' => {
                s.push(c);
                self.lx.bump();
            }
            _ => return Err(self.err_expect("identifier")),
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

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "proof_tree_tests.rs"]
mod tests;
