// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Rewriting.Definitions` from
//! `lib/term/src/Term/Rewriting/Definitions.hs`.
//!
//! Equalities, matching problems, and rewriting rules.
//!
//! Some methods here mirror the Haskell API one-to-one for parity even where
//! the port does not yet exercise them: `Match::only_if`/`no_match`/`empty`,
//! the `Match` `append` (the Haskell `Monoid` instance) and `Default`, and
//! `Equal::eval` have no current production caller. They are intentionally
//! retained as a faithful port surface.

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

impl<A: PartialEq> Equal<A> {
    pub fn eval(&self) -> bool {
        self.lhs == self.rhs
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

/// HS `instance Monoid (Match a)` sets `mempty = DelayedMatches []`
/// (Definitions.hs:117-118).  `#[derive(Default)]` would need a `#[default]`
/// variant and would pick `NoMatch`, the absorbing element.
impl<A> Default for Match<A> {
    fn default() -> Self {
        Match::DelayedMatches(Vec::new())
    }
}

impl<A> Match<A> {
    pub fn empty() -> Self {
        Match::DelayedMatches(Vec::new())
    }
    pub fn no_match() -> Self {
        Match::NoMatch
    }

    /// `matchOnlyIf b`: an empty match if `b`, otherwise `NoMatch`.
    pub fn only_if(b: bool) -> Self {
        if b {
            Match::empty()
        } else {
            Match::NoMatch
        }
    }

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

    /// Append: short-circuits on `NoMatch`, mirroring the Haskell `Monoid`
    /// instance.
    pub fn append(self, other: Self) -> Self {
        match (self, other) {
            (Match::NoMatch, _) | (_, Match::NoMatch) => Match::NoMatch,
            (Match::DelayedMatches(mut a), Match::DelayedMatches(b)) => {
                a.extend(b);
                Match::DelayedMatches(a)
            }
        }
    }
}

// -- Rewrite rule -------------------------------------------------------------

/// HS `data RRule a = RRule a a` derives `Ord` over the left-hand side then
/// the right-hand side (Definitions.hs:138-139).  `MaudeSig::rrules` hands a
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

    /// `Match::default` is HS's `mempty`, the EMPTY delayed match — not the
    /// `NoMatch` a derive would select.
    #[test]
    fn match_default_is_the_empty_delayed_match() {
        assert_eq!(Match::<i32>::default().flatten(), Some(Vec::new()));
    }

    /// The derived `Ord` compares `lhs` before `rhs`, the field order of HS's
    /// `RRule a a`.
    #[test]
    fn rrule_ord_compares_the_lhs_first() {
        assert!(RRule::new(1, 9) < RRule::new(2, 0));
        assert!(RRule::new(1, 0) < RRule::new(1, 1));
    }

    #[test]
    fn equal_eval() {
        assert!(Equal::new(1, 1).eval());
        assert!(!Equal::new(1, 2).eval());
    }

    #[test]
    fn match_short_circuits_on_no_match() {
        // The Haskell `Monoid` instance short-circuits on either side.  A
        // guard that checks only one side therefore fails this test.
        let a: Match<i32> = Match::match_with(1, 2);
        assert!(matches!(
            a.clone().append(Match::no_match()),
            Match::NoMatch
        ));
        assert!(matches!(Match::no_match().append(a), Match::NoMatch));
        // `matchOnlyIf False` is the other producer of the absorbing element.
        assert!(matches!(Match::<i32>::only_if(false), Match::NoMatch));
        assert_eq!(Match::<i32>::only_if(true).flatten(), Some(Vec::new()));
    }

    #[test]
    fn match_appends_pairs() {
        let a = Match::match_with(1, 2);
        let b = Match::match_with(3, 4);
        let r = a.append(b).flatten().unwrap();
        assert_eq!(r, vec![(1, 2), (3, 4)]);
    }
}
