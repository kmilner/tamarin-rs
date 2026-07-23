// Currently GPL 3.0 until granted permission by the following authors:
//   kevinmorio, meiersi, rkunnema, arcz, beschmi, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/accountability/src/Accountability/Generation.hs,
//   lib/theory/src/Theory/Model/Formula.hs

//! Port of `Theory.Model.Formula` from
//! `lib/theory/src/Theory/Model/Formula.hs` — data type + basic builders.
//!
//! The Haskell version uses a locally-nameless representation: bound
//! variables are `BVar::Bound(de_bruijn_idx)`, free variables are `Free(v)`.
//!
//! The pure transforms (`nnf`, `pullquants`, `prenex`, `pnf`,
//! `simplifyFormula`) are not ported on THIS type. Formula.hs's
//! `quantify`/`shiftFreeIndices`/`simplifyFormula` (plus Generation.hs's
//! `pullQuantifiers`/`mergeQuantifiers`) ARE ported in
//! `tamarin-accountability/src/formula.rs`, over a parallel locally-nameless
//! type (`Fm`) whose leaves are `guarded_types` parser-AST atoms rather than
//! this module's real-term `ProtoAtom`s — check there before porting a
//! transform here. (The guarded-formula simplifier `simplifyGuarded` is a
//! DIFFERENT HS function, ported as `simplify_guarded_with` in guarded.rs.)
//! (Pretty-printing of the parser-AST formula representation lives in
//! `pretty_formula.rs`; this `ProtoFormula` has no pretty-printer.)

use crate::atom::{ProtoAtom, Unit2};
use tamarin_term::lterm::{BVar, LVar, Name};
use tamarin_term::vterm::VTerm;

/// Logical connectives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Connective {
    And,
    Or,
    Imp,
    Iff,
}

/// Quantifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    All,
    Ex,
}

/// First-order formula in locally-nameless representation.
///
/// - `S`: syntactic-sugar type (use `()` for the post-parsing form)
/// - `H`: name/sort hint stored at each binder
/// - `C`: constant type for terms
/// - `V`: free-variable type for terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtoFormula<S, H, C, V> {
    Atom(ProtoAtom<S, VTerm<C, BVar<V>>>),
    /// `true`/`false`.
    Tf(bool),
    Not(Box<ProtoFormula<S, H, C, V>>),
    Conn(
        Connective,
        Box<ProtoFormula<S, H, C, V>>,
        Box<ProtoFormula<S, H, C, V>>,
    ),
    Qua(Quantifier, H, Box<ProtoFormula<S, H, C, V>>),
}

/// `Formula` after parsing: no syntactic sugar.
pub type Formula<H, C, V> = ProtoFormula<Unit2, H, C, V>;
pub type LFormula<C> = Formula<(String, tamarin_term::lterm::LSort), C, LVar>;
pub type LNFormula = LFormula<Name>;

impl<S, H, C, V> ProtoFormula<S, H, C, V> {
    pub fn ltrue() -> Self {
        ProtoFormula::Tf(true)
    }
    pub fn lfalse() -> Self {
        ProtoFormula::Tf(false)
    }

    pub fn not(self) -> Self {
        ProtoFormula::Not(Box::new(self))
    }

    pub fn and(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::And, Box::new(self), Box::new(other))
    }
    pub fn or(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Or, Box::new(self), Box::new(other))
    }
    pub fn implies(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Imp, Box::new(self), Box::new(other))
    }
    pub fn iff(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Iff, Box::new(self), Box::new(other))
    }

    pub fn for_all(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::All, hint, Box::new(body))
    }
    pub fn exists(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::Ex, hint, Box::new(body))
    }
}

// NOTE: Haskell `mapAtoms` (Formula.hs:264-267) is
// `foldFormulaScope (\i a -> Ato $ f i a) ...`, i.e. its callback receives
// the De Bruijn binder-depth `i` (threaded via `go (succ i)` at each `Qua`,
// Formula.hs:163-170). The scope-aware machinery in the Rust port lives
// elsewhere (depth-threaded rewrites in `guarded_types.rs`, macro
// application in `macro_expand.rs::apply_macros_formula`), so no
// depth-blind `mapAtoms` mirror is provided here.

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    fn lftrue() -> LNFormula {
        ProtoFormula::ltrue()
    }
    fn lffalse() -> LNFormula {
        ProtoFormula::lfalse()
    }

    #[test]
    fn build_a_simple_formula() {
        // ∀ x:msg. true ∧ ¬false
        let body: LNFormula = lftrue().and(lffalse().not());
        let f: LNFormula = ProtoFormula::for_all(("x".into(), LSort::Msg), body);
        if let ProtoFormula::Qua(q, _, _) = f {
            assert_eq!(q, Quantifier::All);
        } else {
            panic!();
        }
    }

    #[test]
    fn implies_constructs_imp() {
        let f: LNFormula = lftrue().implies(lffalse());
        assert!(matches!(f, ProtoFormula::Conn(Connective::Imp, _, _)));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for Connective and Quantifier order.
    //
    // Formula.hs:104-108: `data Connective = And | Or | Imp | Iff`
    //                     `data Quantifier = All | Ex`
    //
    // These orders matter for any BTreeMap<Connective,_> iteration and for
    // Haskell-faithful structural comparison / round-tripping of formulas.
    // =========================================================================

    /// `Connective` Ord — `And < Or < Imp < Iff` from Formula.hs:104-105.
    #[test]
    fn connective_ord_matches_haskell_declaration() {
        assert!(Connective::And < Connective::Or);
        assert!(Connective::Or < Connective::Imp);
        assert!(Connective::Imp < Connective::Iff);
    }

    /// `Quantifier` Ord — `All < Ex` from Formula.hs:108-109.
    ///
    /// The All<Ex order is required for Haskell-faithful structural /
    /// BTreeMap comparisons and round-tripping of formulas, matching the
    /// `data Quantifier = All | Ex` declaration order. (The guarded-formula
    /// simplifier does not iterate quantifiers in this order; it
    /// pattern-matches structurally — see `simplify_guarded_with`.)
    #[test]
    fn quantifier_ord_matches_haskell_declaration() {
        assert!(
            Quantifier::All < Quantifier::Ex,
            "All MUST sort before Ex (Formula.hs:108)"
        );
    }
}
