//! Term language for the Tamarin prover (Rust port).
//!
//! Modules ported (mapping to Haskell):
//! - [`function_symbols`] ← `Term.Term.FunctionSymbols`
//! - [`term`] ← `Term.Term.Raw` (raw term type + AC-normalising smart constructors)
//! - [`vterm`] ← `Term.VTerm` (`Lit<C, V>` and helpers)
//! - [`lterm`] ← `Term.LTerm` (sorts, names, LVar, BVar, HasFrees, rename)
//! - [`pretty`] ← pretty-printing helpers (`prettyLNTerm`/`prettyTerm`)
//! - [`subst`] ← `Term.Substitution.SubstVFree` (generic free substitution)
//! - [`subst_vfresh`] ← `Term.Substitution.SubstVFresh` (fresh-range substitution)
//! - [`rewriting`] ← `Term.Rewriting.Definitions` (Equal, Match, RRule)
//! - [`builtin`] ← `Term.Builtin.{Signature, Convenience, Rules}`
//! - [`subterm_rule`] ← `Term.SubtermRule`
//! - [`positions`] ← `Term.Positions` (AC-aware position math)
//! - [`maude_sig`] ← `Term.Maude.Signature`
//! - [`maude_proc`] ← `Term.Maude.Process` (spawns/drives the Maude
//!   subprocess; backs AC unification / matching / variants via
//!   `unify` / `unifiable` / `match_eqs` /
//!   `variant_unify_eqs`)
//! - [`maude_parse`] / [`maude_print`] / [`maude_types`] ←
//!   `Term.Maude.{Parser, ...}` (Maude reply parsing, term printing,
//!   and the LNTerm↔Maude conversion context)
//! - [`unification`] ← `Term.Unification` — **non-AC fragment only**
//!   (AC unification is delegated to Maude via [`maude_proc`])
//! - [`macro_expand`] ← `Term.Macro`
//! - [`subsumption`] ← `Term.Subsumption`
//! - [`norm`] ← `Term.Rewriting.Norm` (calls into Maude)
//! - [`intern`] ← (no HS analog) global write-once intern pools for
//!   symbol/variable names
//!
//! Not yet ported:
//! - `Term.Narrowing.{Variants, Variants.Check, Variants.Compute, Narrow}`
//!   (variant computation as a standalone module; the variant-unification
//!   entry point Tamarin needs lives in [`maude_proc`])

pub mod builtin;
pub mod function_symbols;
pub mod intern;
pub mod lterm;
pub mod macro_expand;
pub mod maude_parse;
pub mod maude_print;
pub mod maude_proc;
pub mod maude_sig;
pub mod maude_types;
pub mod norm;
pub mod pretty;
pub mod subsumption;
pub mod positions;
pub mod rewriting;
pub mod subst;
pub mod subst_vfresh;
pub mod subterm_rule;
pub mod term;
pub mod unification;
pub mod vterm;
