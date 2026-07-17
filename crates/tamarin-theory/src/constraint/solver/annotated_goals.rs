// Currently GPL 3.0 until granted permission by the following authors:
//   "Pops" (github racoucho1u)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/Solver/AnnotatedGoals.hs

//! Port of `Theory.Constraint.Solver.AnnotatedGoals`.
//!
//! `AnnotatedGoal` is `(Goal, (sequence-number, usefulness))` — used
//! by the heuristic to rank open goals during proof search.

use crate::constraint::constraints::Goal;

/// How useful solving a particular goal is likely to be.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Usefulness {
    /// Likely to result in progress.
    Useful,
    /// Delayed to avoid immediate termination (loop-breaker).
    LoopBreaker,
    /// Likely constructible by the adversary.
    ProbablyConstructible,
    /// Deducible from the current solution.
    CurrentlyDeducible,
}

/// A goal paired with its sequence number and a usefulness tag.
#[derive(Debug, Clone, PartialEq)]
pub struct AnnotatedGoal {
    pub goal: Goal,
    pub seq: u64,
    pub usefulness: Usefulness,
}

impl AnnotatedGoal {
    pub fn new(goal: Goal, seq: u64, usefulness: Usefulness) -> Self {
        AnnotatedGoal { goal, seq, usefulness }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn usefulness_total_order() {
        assert!(Usefulness::Useful < Usefulness::LoopBreaker);
        assert!(Usefulness::LoopBreaker < Usefulness::ProbablyConstructible);
        assert!(Usefulness::ProbablyConstructible < Usefulness::CurrentlyDeducible);
    }
}
