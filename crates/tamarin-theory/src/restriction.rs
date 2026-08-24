// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Restriction` from
//! `lib/theory/src/Theory/Model/Restriction.hs` — the
//! `ProtoRestriction`/`Restriction` data type.
//!
//! The surface-formula → `LNFormula` rewrite-then-quantify machinery
//! (`fromRuleRestriction` / `rewrite`, Theory/Model/Restriction.hs:90-162) is
//! ported in
//! [`crate::rule_restriction`]; this module models only the data type.

use crate::formula::LNFormula;

// Not yet ported: the `--diff` lhs/rhs restriction attributes
// (HS `RestrictionAttribute`); no caller yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RestrictionAttribute {
    LhsRestriction,
    RhsRestriction,
    BothRestriction,
}

/// `ProtoRestriction f` from the Haskell version. We keep it generic to
/// match the SyntacticRestriction / Restriction split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtoRestriction<F> {
    pub name: String,
    /// `_rstrFormula` — the macro- and predicate-expanded formula, which the
    /// solver converts to a guarded formula and the printer shows in the
    /// `expanded formula:` block.
    pub formula: F,
    /// `_rstrOriginalFormula` — the same formula before macro application,
    /// which the printer shows above that block.  HS's
    /// `applyMacroInRestriction` fills it for every restriction of a closed
    /// theory, macros or none (Theory/Model/Restriction.hs:164-166).
    pub original_formula: Option<F>,
}

pub type Restriction = ProtoRestriction<LNFormula>;
