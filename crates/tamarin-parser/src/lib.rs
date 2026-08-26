// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Surface parser for Tamarin's `.spthy` security-protocol theory files.
//!
//! Port of `Theory.Text.Parser.*` from `lib/theory/src/Theory/Text/Parser/`.
//!
//! This is a *syntax-level* parser: it produces a loose AST that mirrors
//! the surface syntax. Variables carry the `tamarin_term::lterm::LSort`
//! the Haskell parser assigns them, but the rest of the semantic
//! enrichment the Haskell parser does inline (arity validation,
//! `_restrict` expansion, macro expansion, scope analysis) is deferred to
//! a later elaboration pass. The goal is to recognise every well-formed
//! `.spthy` file that Tamarin's Haskell parser accepts.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod proof_tree;

pub use ast::*;
pub use parser::{
    parse_intruder_rules, parse_theory, parse_theory_with_base, GhcError, Message, ParseError,
};
pub use proof_tree::parse_proof_tree;
