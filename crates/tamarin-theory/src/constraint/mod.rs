// Currently GPL 3.0 until granted permission by the following authors:
//   jdreier, meiersi, racoucho1u, rsasse, felixlinker,
//   PhilipLukertWork, kevinmorio, yavivanov, beschmi, arcz, Nick Moore,
//   katrielalex, rkunnema, addap, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/System.hs

//! Constraint solver data layer (port of `Theory.Constraint.System.*`).
//!
//! The Haskell tree splits the constraint system into:
//! - `Theory.Constraint.System.Guarded`     — guarded formulas (already
//!   ported in [`crate::guarded`])
//! - `Theory.Constraint.System.Constraints` — graph constraints, lessAtoms,
//!   goals (this module: [`mod@constraints`])
//! - `Theory.Constraint.System`             — the `System` sequent (the
//!   solver's working state)
//! - `Theory.Constraint.Solver.*`           — the actual proof-search loop

pub mod constraints;
pub mod solver;
pub mod system;

pub use constraints::*;
pub use solver::*;
pub use system::System;
