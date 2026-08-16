// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
        LessAtom {
            smaller,
            larger,
            reason,
        }
    }

    pub fn to_edge(&self) -> (NodeId, NodeId) {
        (self.smaller, self.larger)
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
    pub fn new(items: Vec<T>) -> Self {
        Disj(items)
    }
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
    pub fn is_action(&self) -> bool {
        matches!(self, Goal::Action(_, _))
    }
    pub fn is_premise(&self) -> bool {
        matches!(self, Goal::Premise(_, _))
    }
    pub fn is_chain(&self) -> bool {
        matches!(self, Goal::Chain(_, _))
    }
    pub fn is_split(&self) -> bool {
        matches!(self, Goal::Split(_))
    }
    pub fn is_disj(&self) -> bool {
        matches!(self, Goal::Disj(_))
    }
    // HS's `isSubtermGoal` (Constraints.hs) erroneously matches `DisjG _`
    // (a copy-paste of `isDisjGoal`); we match the semantically-correct
    // `Goal::Subterm`. The divergence is inert (no caller yet).
    pub fn is_subterm(&self) -> bool {
        matches!(self, Goal::Subterm(_))
    }

    /// "Standard" action goals are non-`KU` actions — `KU(_)` is
    /// special-cased by the solver (intruder-knowledge goals).
    pub fn is_standard_action(&self) -> bool {
        if let Goal::Action(_, fa) = self {
            !matches!(fa.tag, crate::fact::FactTag::Ku)
        } else {
            false
        }
    }
}

/// HS-faithful structural comparison for [`Goal`], mirroring the derived
/// `Ord Goal` (Constraints.hs:159-172).
///
/// Constructor rank is `ActionG < ChainG < PremiseG < SplitG < DisjG <
/// SubtermG`, which is this enum's declaration order; within a constructor
/// the payloads compare left to right.  Every payload comparison below
/// delegates to an `Ord` that already mirrors its HS counterpart:
///
/// - `LVar` — manual `Ord` = `(idx, sort, name)` (LTerm.hs:546-548).
/// - `LNFact` — manual `Ord` = tag then terms, annotations IGNORED, which is
///   HS's manual `instance Ord (Fact t)` (Model/Fact.hs:173-174), not a derived
///   one; `FactTag`'s derived `Ord` matches HS's constructor and payload
///   order (Model/Fact.hs:137-148), as does `Multiplicity`'s
///   (Model/Fact.hs:133-134).
/// - `NodeConc` / `NodePrem` — `(LVar, ConcIdx/PremIdx)` tuples; the index
///   newtypes derive `Ord` over their integer, as HS's do
///   (Model/Rule.hs:233-238).
/// - `SplitId` — newtype over an integer, derived both sides
///   (EquationStore.hs:88-89).
/// - `LNTerm` — `Lit < App`, then symbol then arguments, mirroring the
///   derived `Ord (Term a)` / `Ord (Lit c v)` (Raw.hs:73-75, VTerm.hs:56-58).
///
/// `Disj` bottoms out in `Guarded`, whose HS-faithful comparison is
/// [`crate::guarded::cmp_guarded`]; HS's `Disj` is a newtype over a list, so
/// the wrapper compares lexicographically.
///
/// This is a free function rather than an `Ord` impl because `Ord` requires
/// `Eq`, and `Guarded` carries no `Eq` — the same reason `cmp_guarded` is a
/// free function.
///
/// HS holds `sGoals` in a `Map Goal GoalStatus`, so any `M.toList` walk of it
/// is in ascending `Goal` order; this crate's goal store is a `Vec` in
/// insertion order, so a caller mirroring such a walk sorts with this first.
pub fn cmp_goal(a: &Goal, b: &Goal) -> std::cmp::Ordering {
    let (ta, tb) = (goal_tag(a), goal_tag(b));
    if ta != tb {
        return ta.cmp(&tb);
    }
    // Tag equality above guarantees the same variant, so each `let … else`
    // binding of `b` is infallible.  Match `a` exhaustively (no wildcard) so a
    // new `Goal` variant forces a comparison here.
    match a {
        Goal::Action(i1, f1) => {
            let Goal::Action(i2, f2) = b else {
                unreachable!("goal tag matched Action")
            };
            i1.cmp(i2).then_with(|| f1.cmp(f2))
        }
        Goal::Chain(c1, p1) => {
            let Goal::Chain(c2, p2) = b else {
                unreachable!("goal tag matched Chain")
            };
            c1.cmp(c2).then_with(|| p1.cmp(p2))
        }
        Goal::Premise(p1, f1) => {
            let Goal::Premise(p2, f2) = b else {
                unreachable!("goal tag matched Premise")
            };
            p1.cmp(p2).then_with(|| f1.cmp(f2))
        }
        Goal::Split(s1) => {
            let Goal::Split(s2) = b else {
                unreachable!("goal tag matched Split")
            };
            s1.cmp(s2)
        }
        Goal::Disj(d1) => {
            let Goal::Disj(d2) = b else {
                unreachable!("goal tag matched Disj")
            };
            crate::guarded::cmp_slice(&d1.0, &d2.0, crate::guarded::cmp_guarded)
        }
        Goal::Subterm((s1, t1)) => {
            let Goal::Subterm((s2, t2)) = b else {
                unreachable!("goal tag matched Subterm")
            };
            s1.cmp(s2).then_with(|| t1.cmp(t2))
        }
    }
}

fn goal_tag(g: &Goal) -> u8 {
    match g {
        Goal::Action(_, _) => 0,
        Goal::Chain(_, _) => 1,
        Goal::Premise(_, _) => 2,
        Goal::Split(_) => 3,
        Goal::Disj(_) => 4,
        Goal::Subterm(_) => 5,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    fn node(name: &str) -> NodeId {
        LVar::new(name, LSort::Node, 0)
    }

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

    // HS's derived `Ord Goal` ranks by constructor first, in declaration
    // order `ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG`
    // (Constraints.hs:159-172), and only then by payload.
    #[test]
    fn cmp_goal_ranks_constructors_in_haskell_order() {
        use crate::fact::{FactTag, LNFact};
        use crate::guarded::gtrue;
        use crate::rule::{ConcIdx, PremIdx};
        use crate::tools::equation_store::SplitId;
        use std::cmp::Ordering;
        use tamarin_term::term::lit;
        use tamarin_term::vterm::Lit;

        let t = lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
        let fa = LNFact::new(FactTag::Out, vec![t.clone()]);
        let ordered = [
            Goal::Action(node("i"), fa.clone()),
            Goal::Chain((node("i"), ConcIdx(0)), (node("j"), PremIdx(0))),
            Goal::Premise((node("i"), PremIdx(0)), fa.clone()),
            Goal::Split(SplitId(0)),
            Goal::Disj(Disj::new(vec![gtrue()])),
            Goal::Subterm((t.clone(), t.clone())),
        ];
        for (i, a) in ordered.iter().enumerate() {
            for (j, b) in ordered.iter().enumerate() {
                assert_eq!(
                    cmp_goal(a, b),
                    i.cmp(&j),
                    "constructor rank {i} vs {j}: {a:?} / {b:?}"
                );
            }
        }

        // Same-constructor tie-break: `ActionG` compares its `LVar` first, and
        // `Ord LVar` is idx-major (LTerm.hs:546-548), so `#i.1` precedes
        // `#a.2` despite sorting after it by name.
        let lo = Goal::Action(LVar::new("i", LSort::Node, 1), fa.clone());
        let hi = Goal::Action(LVar::new("a", LSort::Node, 2), fa.clone());
        assert_eq!(cmp_goal(&lo, &hi), Ordering::Less);
        // Equal node ids fall through to the fact, which orders by tag then
        // terms with annotations ignored (Model/Fact.hs:173-174).
        let fresh = LNFact::new(FactTag::Fresh, vec![t.clone()]);
        let a_out = Goal::Action(node("i"), fa);
        let a_fresh = Goal::Action(node("i"), fresh);
        assert_eq!(cmp_goal(&a_fresh, &a_out), Ordering::Less);
        assert_eq!(cmp_goal(&a_out, &a_out), Ordering::Equal);

        // `SplitG` compares its id; `SubtermG` its term pair left to right.
        assert_eq!(
            cmp_goal(&Goal::Split(SplitId(1)), &Goal::Split(SplitId(2))),
            Ordering::Less
        );
        let u = lit(Lit::Var(LVar::new("y", LSort::Msg, 0)));
        assert_eq!(
            cmp_goal(
                &Goal::Subterm((t.clone(), t.clone())),
                &Goal::Subterm((t.clone(), u))
            ),
            Ordering::Less
        );
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
