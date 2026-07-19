// Currently GPL 3.0 until granted permission by the following authors:
//   charlie-j, rkunnema, meiersi, jdreier, yavivanov, kevinmorio,
//   BTom-GH, rsasse, ValentinYuri, racoucho1u, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser.hs

//! Surface parser for Tamarin's `.spthy` security-protocol theory files.
//!
//! Port of `Theory.Text.Parser.*` from `lib/theory/src/Theory/Text/Parser/`.
//!
//! This is a *syntax-level* parser: it produces a loose AST that mirrors
//! the surface syntax. Semantic enrichment that the Haskell parser does
//! inline (arity validation, sort assignment, `_restrict` expansion,
//! macro expansion, scope analysis) is deferred to a later elaboration
//! pass. The goal is to recognise every well-formed `.spthy` file that
//! Tamarin's Haskell parser accepts.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod proof_tree;
pub mod wf;

pub use ast::*;
pub use parser::{
    parse_intruder_rules, parse_theory, parse_theory_or_diff, parse_theory_with_base, Message,
    ParseError,
};
pub use proof_tree::parse_proof_tree;
