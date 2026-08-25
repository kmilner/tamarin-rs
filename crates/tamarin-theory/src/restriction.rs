// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Restriction` from
//! `lib/theory/src/Theory/Model/Restriction.hs` — the
//! `ProtoRestriction`/`Restriction` data type and
//! [`apply_macro_in_restriction`].
//!
//! The surface-formula → `LNFormula` rewrite-then-quantify machinery
//! (`fromRuleRestriction` / `rewrite`, Theory/Model/Restriction.hs:90-162) is
//! ported in [`crate::rule_restriction`].

use tamarin_term::macro_expand::LNMacro;

use crate::formula::{apply_macro_in_formula, LNFormula};

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

/// HS `applyMacroInRestriction` (Theory/Model/Restriction.hs:164-166): the
/// theory's macros applied to the formula, with the formula as it stood
/// recorded as the original one unless the restriction already carries one.
/// HS runs it over every restriction of a closed theory (`closeTheoryItem`,
/// CloseRule.hs:84), macros or none, so `original_formula` ends up filled
/// either way.
pub fn apply_macro_in_restriction(macros: &[LNMacro], r: Restriction) -> Restriction {
    let original = r.original_formula.unwrap_or_else(|| r.formula.clone());
    Restriction {
        name: r.name,
        formula: apply_macro_in_formula(macros, r.formula),
        original_formula: Some(original),
    }
}
