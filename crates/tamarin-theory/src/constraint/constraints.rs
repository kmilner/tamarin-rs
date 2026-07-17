// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Felix Linker, "sans-sucre" (github), Philip Lukert, and
//   other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/System/Constraints.hs

//! Port of `Theory.Constraint.System.Constraints` —
//! graph-constraint primitives (`Edge`, `LessAtom`), goal types
//! (`Goal`), and small helpers.
//!
//! These types do not carry generic `Apply LNSubst` / `HasFrees`
//! instances. The substitution layer is ported (`apply_vterm` in
//! `tamarin_term::subst`, the `HasFrees` trait in
//! `tamarin_term::lterm`); the solver applies substitutions to these
//! constraints directly in `constraint::solver::reduction`
//! (`subst_system` / `subst_system_once`, mirroring Haskell's
//! `substSystem`).

use tamarin_term::lterm::{LNTerm, LVar};

use crate::fact::LNFact;
use crate::guarded::Guarded;
use crate::rule::{ConcIdx, PremIdx};

// =============================================================================
// Graph constraints
// =============================================================================

/// `NodeId` is just an `LVar` of node sort. Tamarin's nodes are
/// identified by node-sort variables (`#i`, `#j`, etc.).
pub type NodeId = LVar;

/// A premise of a node: `(NodeId, PremIdx)`.
pub type NodePrem = (NodeId, PremIdx);

/// A conclusion of a node: `(NodeId, ConcIdx)`.
pub type NodeConc = (NodeId, ConcIdx);

/// An edge in the derivation graph — a conclusion of one rule
/// instance feeding a premise of another.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Edge {
    pub src: NodeConc,
    pub tgt: NodePrem,
}

/// Why two nodes are ordered. Used to attribute `LessAtom`s to their
/// source justification — the order from most-important to
/// least-important matches the Haskell enumeration so any tie-breaks
/// during pretty-printing produce the same output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Reason {
    Formula,
    InjectiveFacts,
    Fresh,
    Adversary,
    NormalForm,
}

impl std::fmt::Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Reason::Fresh => "fresh value",
            Reason::Formula => "formula",
            Reason::InjectiveFacts => "injective facts",
            Reason::NormalForm => "normal form condition",
            Reason::Adversary => "adversary",
        };
        write!(f, "{}", s)
    }
}

/// `i < j` ordering atom on node ids, with a reason tag.
///
/// Equality and ordering ignore the reason tag — two atoms are "the
/// same" iff they constrain the same pair, mirroring Haskell.
#[derive(Debug, Clone)]
pub struct LessAtom {
    pub smaller: NodeId,
    pub larger: NodeId,
    pub reason: Reason,
}

impl LessAtom {
    pub fn new(smaller: NodeId, larger: NodeId, reason: Reason) -> Self {
        LessAtom { smaller, larger, reason }
    }

    pub fn to_edge(&self) -> (NodeId, NodeId) {
        (self.smaller.clone(), self.larger.clone())
    }
}

impl PartialEq for LessAtom {
    fn eq(&self, other: &Self) -> bool {
        self.smaller == other.smaller && self.larger == other.larger
    }
}
impl Eq for LessAtom {}
impl Ord for LessAtom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self.smaller, &self.larger).cmp(&(&other.smaller, &other.larger))
    }
}
impl PartialOrd for LessAtom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Project the relation: just the `(smaller, larger)` pairs.
/// Reachable only from its own unit test in production; kept as a mirror
/// of the HS `getLessRel`-style projection (`to_edge` likewise).
pub fn get_less_rel(atoms: &[LessAtom]) -> Vec<(NodeId, NodeId)> {
    atoms.iter().map(|a| a.to_edge()).collect()
}

// =============================================================================
// Equation-store split identifiers
// =============================================================================

/// Re-export the equation-store split id so `Goal::Split` carries
/// the same type the eq-store actually allocates.
pub use crate::tools::equation_store::SplitId;

// =============================================================================
// Disjunction wrapper used by DisjG
// =============================================================================

/// A finite disjunction. Mirrors Haskell's `Logic.Connectives.Disj`.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Disj<T>(pub Vec<T>);

impl<T> Disj<T> {
    pub fn new(items: Vec<T>) -> Self { Disj(items) }
}

// =============================================================================
// Goals
// =============================================================================

/// A `Goal` denotes that a constraint reduction rule is applicable.
#[derive(Debug, Clone, PartialEq)]
pub enum Goal {
    /// An action that must exist in the trace.
    Action(LVar, LNFact),
    /// A destruction chain.
    Chain(NodeConc, NodePrem),
    /// A premise that must have an incoming direct edge.
    Premise(NodePrem, LNFact),
    /// A case split over equalities (referenced by id).
    Split(SplitId),
    /// A case split over a disjunction of guarded formulas.
    Disj(Disj<Guarded>),
    /// A split of a Subterm constraint (which lives in the SubtermStore).
    Subterm((LNTerm, LNTerm)),
}

impl Goal {
    // `is_split`/`is_disj`/`is_subterm`/`is_premise` mirror the HS `Goal`
    // predicate set (`isSplitGoal`/`isDisjGoal`/`isSubtermGoal`); no caller
    // yet, kept for parity with the sibling live predicates.
    pub fn is_action(&self) -> bool { matches!(self, Goal::Action(_, _)) }
    pub fn is_premise(&self) -> bool { matches!(self, Goal::Premise(_, _)) }
    pub fn is_chain(&self) -> bool { matches!(self, Goal::Chain(_, _)) }
    pub fn is_split(&self) -> bool { matches!(self, Goal::Split(_)) }
    pub fn is_disj(&self) -> bool { matches!(self, Goal::Disj(_)) }
    // HS's `isSubtermGoal` (Constraints.hs) erroneously matches `DisjG _`
    // (a copy-paste of `isDisjGoal`); we match the semantically-correct
    // `Goal::Subterm`. The divergence is inert (no caller yet).
    pub fn is_subterm(&self) -> bool { matches!(self, Goal::Subterm(_)) }

    /// "Standard" action goals are non-`KU` actions — `KU(_)` is
    /// special-cased by the solver (intruder-knowledge goals).
    pub fn is_standard_action(&self) -> bool {
        if let Goal::Action(_, fa) = self {
            !matches!(fa.tag, crate::fact::FactTag::Ku)
        } else { false }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    fn node(name: &str) -> NodeId { LVar::new(name, LSort::Node, 0) }

    #[test]
    fn less_atom_equality_ignores_reason() {
        let a = LessAtom::new(node("i"), node("j"), Reason::Fresh);
        let b = LessAtom::new(node("i"), node("j"), Reason::Formula);
        assert_eq!(a, b);
    }

    #[test]
    fn less_rel_projection() {
        let atoms = vec![
            LessAtom::new(node("i"), node("j"), Reason::Fresh),
            LessAtom::new(node("j"), node("k"), Reason::Formula),
        ];
        let rel = get_less_rel(&atoms);
        assert_eq!(rel.len(), 2);
        assert_eq!(rel[0].0, node("i"));
        assert_eq!(rel[1].1, node("k"));
    }

    #[test]
    fn goal_kind_predicates() {
        let v = LVar::new("k", LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        let g = Goal::Action(v, f);
        assert!(g.is_action());
        assert!(!g.is_premise());
    }
}
