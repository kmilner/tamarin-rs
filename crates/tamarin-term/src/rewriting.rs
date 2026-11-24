// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Rewriting.Definitions` from
//! `lib/term/src/Term/Rewriting/Definitions.hs`.
//!
//! Equalities, matching problems, and rewriting rules.

// -- Equality -----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equal<A> {
    pub lhs: A,
    pub rhs: A,
}

impl<A> Equal<A> {
    pub fn new(lhs: A, rhs: A) -> Self {
        Equal { lhs, rhs }
    }
}

// -- Matching problem ---------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Match<A> {
    /// No matcher exists.
    NoMatch,
    /// `(term, pattern)` pairs that still need to be solved.
    DelayedMatches(Vec<(A, A)>),
}

impl<A> Match<A> {
    /// `matchWith t p`: a single-pair match problem.
    pub fn match_with(term: A, pattern: A) -> Self {
        Match::DelayedMatches(vec![(term, pattern)])
    }

    /// `flattenMatch`: list of pairs, or `None` if `NoMatch`.
    pub fn flatten(self) -> Option<Vec<(A, A)>> {
        match self {
            Match::NoMatch => None,
            Match::DelayedMatches(v) => Some(v),
        }
    }
}

// -- Rewrite rule -------------------------------------------------------------

/// HS `data RRule a = RRule a a` derives `Ord` over the left-hand side then
/// the right-hand side (Definitions.hs).  `MaudeSig::rrules` hands a
/// `BTreeSet<RRule<LNTerm>>` to the Maude module writer, so this order reaches
/// the emitted module.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RRule<A> {
    pub lhs: A,
    pub rhs: A,
}

impl<A> RRule<A> {
    pub fn new(lhs: A, rhs: A) -> Self {
        RRule { lhs, rhs }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The derived `Ord` compares `lhs` before `rhs`, the field order of HS's
    /// `RRule a a`.
    #[test]
    fn rrule_ord_compares_the_lhs_first() {
        assert!(RRule::new(1, 9) < RRule::new(2, 0));
        assert!(RRule::new(1, 0) < RRule::new(1, 1));
    }
}
