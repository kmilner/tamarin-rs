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

    /// `ProtoRestriction::new` — the sole constructor, used by elaboration
    /// (`elaborate.rs`) — stores name and formula verbatim and records NO
    /// original surface formula.  `original_formula` gates the arity-1
    /// rewrite in `elaborate.rs`, so a constructor that pre-filled it would
    /// silently double-rewrite the body.
    #[test]
    fn build_restriction() {
        let f: LNFormula = ProtoFormula::ltrue();
        let r = Restriction::new("MyR", f.clone());
        assert_eq!(r.name, "MyR");
        assert_eq!(r.formula, f);
        assert_eq!(r.original_formula, None);
    }
}
