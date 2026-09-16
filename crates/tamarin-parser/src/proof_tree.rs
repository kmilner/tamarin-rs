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
//! `solve( ... )` step shares the theory parser's cursor and symbol state.
//! A token this grammar does not accept fails the containing theory parse, as
//! it does in HS.

use crate::ast::{ParsedMethod, ParsedProofTree};
use crate::lexer::is_ident_char;
use crate::parse_error::ParseContext;
use crate::parser::{ParseError, Parser};

/// Parse a complete standalone proof using `parent`'s symbol signature.
/// Proofs attached to theory lemmas use the same grammar directly on the
/// enclosing parser (Theory/Text/Parser/Proof.hs:38-72).
pub fn parse_proof_tree(raw: &str, parent: &Parser<'_>) -> Result<ParsedProofTree, ParseError> {
    let mut parser = Parser::new(raw, &[], parent.is_diff);
    parser.seed_from(parent);
    let tree = parser.proof_tree()?;
    parser.require_end_of_proof()?;
    Ok(tree)
}

/// Validate HS `diffProofSkeleton` (Theory/Text/Parser/Proof.hs:128-144).
/// Diff proofs retain their raw text rather than an executable regular tree.
#[cfg(test)]
pub(crate) fn validate_diff_proof_tree(raw: &str, parent: &Parser<'_>) -> Result<(), ParseError> {
    let mut parser = Parser::new(raw, &[], parent.is_diff);
    parser.seed_from(parent);
    parser.diff_proof_tree()?;
    parser.require_end_of_proof()
}

impl Parser<'_> {
    fn require_end_of_proof(&self) -> Result<(), ParseError> {
        if self.lx.is_eof() {
            Ok(())
        } else {
            Err(self
                .err_expect_here("end of proof")
                .with_context(ParseContext::Proof))
        }
    }

    /// Read one proof and its trailing whitespace/comments in the theory's
    /// cursor. Goal parsing shares the signature and diagnostic declaration sites.
    pub(super) fn proof_tree(&mut self) -> Result<ParsedProofTree, ParseError> {
        self.proof_prefix(Self::proof_skeleton)
    }

    pub(super) fn diff_proof_tree(&mut self) -> Result<(), ParseError> {
        self.proof_prefix(Self::diff_proof_skeleton)
    }

    fn proof_prefix<T>(
        &mut self,
        parse: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        let result = parse(self);
        self.skip_ws();
        self.lx
            .finish(result)
            .map_err(|error| error.with_context(ParseContext::Proof))
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
            self.skip_ws();
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
                self.skip_ws();
                let block = self.at_keyword("case") || self.at_keyword("qed");
                if block && self.try_kw("qed") {
                    // A case block may be empty.
                } else {
                    // Without a case block, an intermediate method requires
                    // one inline child; a bare method is not a complete proof.
                    let name = if block {
                        self.proof_case_name()?
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
                        parent.name = self.proof_case_name()?;
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
    fn proof_case_name(&mut self) -> Result<String, ParseError> {
        self.require_kw("case")?;
        self.identifier_extended()
    }

    /// HS `proofMethod` (Theory/Text/Parser/Proof.hs:76-85).
    fn proof_method(&mut self) -> Result<ParsedMethod, ParseError> {
        self.skip_ws();
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
            // HS `symbol "solve" *> parens goal` (Theory/Text/Parser/Proof.hs:80).
            // Read directly from the shared cursor: spans are already absolute.
            self.require_punct("(")?;
            let spec = self.goal()?;
            self.skip_ws();
            if !self.try_punct(")") {
                return Err(self.err_expect_here("`)` after the goal"));
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
            self.skip_ws();
            if !self.try_kw("MIRRORED") {
                if self.try_kw("by") {
                    self.diff_proof_method()?;
                } else {
                    self.diff_proof_method()?;
                    self.skip_ws();
                    if self.at_keyword("case") {
                        self.proof_case_name()?;
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
                    self.proof_case_name()?;
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
        self.skip_ws();
        if self.try_kw("sorry")
            || self.try_kw("rule-equivalence")
            || self.try_kw("backward-search")
            || self.try_kw("ATTACK")
            || self.try_kw("UNFINISHABLEdiff")
        {
            return Ok(());
        }
        if self.try_kw("step") {
            self.require_punct("(")?;
            self.proof_method()?;
            self.require_punct(")")?;
            return Ok(());
        }
        Err(self.err_expect("diff proof method"))
    }

    /// Proof labels preserve generated names and reserved words (e.g. `rule`).
    /// Identifier with extended chars: HS's `identifier` accepts
    /// alphanum + `_` (Token.hs:214-230, see line 224 `identLetter = alphaNum <|> oneOf "_"`)
    /// and emits names like `Server_ReceiveOTP_NewSession_case_1`.
    fn identifier_extended(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
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
        self.skip_ws();
        Ok(s)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "proof_tree_tests.rs"]
mod tests;
