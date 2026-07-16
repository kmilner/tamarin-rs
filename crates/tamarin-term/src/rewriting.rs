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
    pub fn new(lhs: A, rhs: A) -> Self { Equal { lhs, rhs } }
}

impl<A: PartialEq> Equal<A> {
    pub fn eval(&self) -> bool { self.lhs == self.rhs }
}

// -- Matching problem ---------------------------------------------------------

#[derive(Debug, Clone)]
pub enum Match<A> {
    /// No matcher exists.
    NoMatch,
    /// `(term, pattern)` pairs that still need to be solved.
    DelayedMatches(Vec<(A, A)>),
}

impl<A> Default for Match<A> {
    fn default() -> Self { Match::DelayedMatches(Vec::new()) }
}

impl<A> Match<A> {
    pub fn empty() -> Self { Match::DelayedMatches(Vec::new()) }
    pub fn no_match() -> Self { Match::NoMatch }

    /// `matchOnlyIf b`: an empty match if `b`, otherwise `NoMatch`.
    pub fn only_if(b: bool) -> Self {
        if b { Match::empty() } else { Match::NoMatch }
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RRule<A> {
    pub lhs: A,
    pub rhs: A,
}

impl<A> RRule<A> {
    pub fn new(lhs: A, rhs: A) -> Self { RRule { lhs, rhs } }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_eval() {
        assert!(Equal::new(1, 1).eval());
        assert!(!Equal::new(1, 2).eval());
    }

    #[test]
    fn match_short_circuits_on_no_match() {
        let a: Match<i32> = Match::match_with(1, 2);
        let b: Match<i32> = Match::no_match();
        assert!(matches!(a.append(b), Match::NoMatch));
    }

    #[test]
    fn match_appends_pairs() {
        let a = Match::match_with(1, 2);
        let b = Match::match_with(3, 4);
        let r = a.append(b).flatten().unwrap();
        assert_eq!(r, vec![(1, 2), (3, 4)]);
    }
}
