// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Solver-support tools — port of `Theory.Tools.*`.

pub mod abstract_interpretation;
pub mod equation_store;
pub mod injective_fact_instances;
pub mod rule_variants;
pub mod subterm_store;

pub use abstract_interpretation::{apply_partial_evaluation, EvaluationStyle};
pub use equation_store::EquationStore;
pub use rule_variants::variants_proto_rule;
pub use subterm_store::SubtermStore;
