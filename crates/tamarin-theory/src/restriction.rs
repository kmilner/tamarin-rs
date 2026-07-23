// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Model/Restriction.hs

//! Port of `Theory.Model.Restriction` from
//! `lib/theory/src/Theory/Model/Restriction.hs` — the
//! `ProtoRestriction`/`Restriction` data type.
//!
//! The surface-formula → `LNFormula` rewrite-then-quantify machinery
//! (`fromRuleRestriction` / `rewrite`, Restriction.hs:89-161) is ported in
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
    pub formula: F,
    pub original_formula: Option<F>,
}

impl<F> ProtoRestriction<F> {
    pub fn new(name: impl Into<String>, formula: F) -> Self {
        ProtoRestriction {
            name: name.into(),
            formula,
            original_formula: None,
        }
    }
}

pub type Restriction = ProtoRestriction<LNFormula>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::ProtoFormula;

    #[test]
    fn build_restriction() {
        let f: LNFormula = ProtoFormula::ltrue();
        let r = Restriction::new("MyR", f);
        assert_eq!(r.name, "MyR");
    }
}
