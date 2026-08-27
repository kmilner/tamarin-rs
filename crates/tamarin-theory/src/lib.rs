// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Theory representation for the Tamarin prover (Rust port).
//!
//! Modules ported (mapping to Haskell):
//! - [`signature`] ← `Theory.Model.Signature`
//! - [`fact`] ← `Theory.Model.Fact`
//! - [`atom`] ← `Theory.Model.Atom`
//! - [`formula`] ← `Theory.Model.Formula` (data type + builders)
//! - [`guarded`] ← `Theory.Model.Formula` (guarded
//!   formulas)
//! - [`restriction`] ← `Theory.Model.Restriction`;
//!   [`rule_restriction`] ← `Theory.Model.Restriction` `liftedAddProtoRule`
//!   (surface-formula → `LNFormula` rewrite-then-quantify)
//! - [`rule`] ← `Theory.Model.Rule` (data layer + indices + info types);
//!   instantiation (`someRuleACInst*`) lives in
//!   [`constraint::solver::reduction`]
//! - [`sapic`] ← `Theory.Sapic.{Position, Term, Annotation, Process, Pattern}`;
//!   [`process_convert`] / [`process_inline`] build a `PlainProcess` from the
//!   parser's surface process AST, which HS's parser builds directly
//!   (`Theory/Text/Parser/Sapic.hs`)
//! - [`intruder_rules`] / [`intruder_variants`] ←
//!   `Theory.Tools.IntruderRules`; [`close_rule`] ← `CloseRule.hs`'s
//!   no-deconstruction-chain check
//! - [`predicate`] ← `Theory.Syntactic.Predicate`
//!   (data + lookup + `expandFormula`)
//! - [`constraint`] ← `Theory.Constraint.*` (the constraint solver,
//!   ~32k LOC: system, reduction, goals, sources, simplify,
//!   contradictions, search, …)
//! - [`tools`] ← `Theory.Tools.*` (equation store, subterm store,
//!   abstract interpretation, loop breakers, rule-variants,
//!   injective-fact instances)
//! - [`wellformedness`] ← `Theory.Tools.Wellformedness`;
//!   [`deriv_check`] ← message-derivation checks
//! - [`theory`] ← top-level `Theory` (open/closed theories);
//!   [`elaborate`] ← theory elaboration/closing
//! - [`tactic`] ← heuristic tactics; [`proof_skeleton`] / [`replay`] /
//!   [`prove`] ← proof skeletons, replay, and the per-lemma prover driver
//! - [`pretty_theory`] / [`pretty_system`] / [`pretty_formula`] /
//!   [`pretty_hpj`] ← theory / system / formula pretty-printing;
//!   [`pretty_sapic`] ← `Theory.Sapic.{Term,Process}` pretty-printing
//! - [`auto_sources`] ← `OpenTheory` `addAutoSourcesLemma` (`--auto-sources`)
//! - [`module`] ← `Theory.Module` (the `--output-module` selector)
//! - [`state_trace`] ← solver state tracing
//!
//! The `.spthy` parser lives in the sibling `tamarin-parser` crate.
//!
//! Not yet ported:
//! - Remaining `Theory.Sapic.*` (Substitution, Print)

pub mod apply;
pub mod atom;
pub mod auto_sources;
pub mod close_rule;
pub mod constraint;
pub mod deriv_check;
pub mod elaborate;
pub mod fact;
pub mod formula;
pub mod guarded;
pub mod intruder_rules;
pub mod intruder_variants;
pub mod module;
pub mod predicate;
pub mod pretty_formula;
pub mod pretty_hpj;
pub mod pretty_sapic;
pub mod pretty_system;
#[cfg(test)]
#[path = "pretty_term_corpus_tests.rs"]
mod pretty_term_corpus_tests;
pub mod pretty_theory;
pub mod process_convert;
pub mod process_inline;
pub mod proof_skeleton;
pub mod prove;
pub mod replay;
pub mod restriction;
pub mod rule;
pub mod rule_restriction;
pub mod sapic;
pub mod signature;
pub mod state_trace;
pub mod tactic;
#[cfg(test)]
pub(crate) mod test_corpus;
#[cfg(test)]
pub(crate) mod test_maude;
pub mod theory;
pub mod tools;
pub mod wellformedness;
