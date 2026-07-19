// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/Solver.hs

//! Solver layer (port of `Theory.Constraint.Solver.*`).
//!
//! Submodules:
//! - [`annotated_goals`] — goal ranking / annotation helpers.
//! - [`context`] — port of the `ProofContext` data type used by every
//!   solver entry point.
//! - [`contradictions`] — port of `Solver.Contradictions`. Identifies
//!   all reasons a `System` is contradictory.
//! - [`goals`] — port of `Solver.Goals`. Goal solving and case
//!   distinction generation.
//! - [`proof_method`] — port of `Solver.ProofMethod`. The
//!   external small-step interface to the constraint solver
//!   (`ProofMethod`, `Result`, `is_finished`, `exec_proof_method`).
//! - [`reduction`] — port of `Solver.Reduction`. Constraint-reduction
//!   rules over a `System`.
//! - [`rename_precise`] — precise variable renaming helpers.
//! - [`search`] — proof-search driver over the small-step interface.
//! - [`simplify`] — port of `Solver.Simplify`. Simplification of a
//!   `System`.
//! - [`sources`] — port of `Solver.Sources`. Source/case-distinction
//!   precomputation.
//! - [`tactic_show`] — pretty-printing for tactic diagnostics.
//! - [`trace`] — RS-only diagnostic execution-trace scaffolding.
//!
//! The full Haskell source is ~4 k LOC across `ProofMethod`,
//! `Reduction`, `Goals`, `Sources`, `Simplify`, `Contradictions`, all
//! of which are ported here.

pub mod annotated_goals;
pub mod context;
pub mod contradictions;
pub mod goals;
pub mod proof_method;
pub mod reduction;
pub mod rename_precise;
pub mod search;
pub mod simplify;
pub mod sources;
pub mod tactic_show;
pub mod trace;

pub use context::ProofContext;
pub use contradictions::{contradictions, Contradiction};
pub use proof_method::{
    exec_proof_method, is_finished, ProofMethod, Result as ProofResult,
};
pub use search::{run_proof_search, NodeStatus, ProofNode};
