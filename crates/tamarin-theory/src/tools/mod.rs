// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Solver-support tools — port of `Theory.Tools.*`.

pub mod abstract_interpretation;
pub mod equation_store;
pub mod injective_fact_instances;
pub mod rule_variants;
pub mod subterm_store;

pub use abstract_interpretation::{apply_partial_evaluation, partial_evaluation, EvaluationStyle};
pub use equation_store::EquationStore;
pub use rule_variants::variants_proto_rule;
pub use subterm_store::SubtermStore;
