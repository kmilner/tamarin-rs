// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Constraint.System.Constraints` —
//! graph-constraint primitives (`Edge`, `LessAtom`), goal types
//! (`Goal`), and small helpers.
//!
//! `Edge`, `LessAtom`, `Disj` and `Goal` carry the `HasFrees` instances
//! Haskell declares for them; the trait itself lives in
//! `tamarin_term::lterm`.  None of them carries a generic `Apply LNSubst`
//! instance: the solver applies substitutions to these constraints directly
//! in `constraint::solver::reduction` (`subst_system` / `subst_system_once`,
//! mirroring Haskell's `substSystem`).

use tamarin_term::lterm::{HasFrees, LNTerm, LVar};

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

/// `instance HasFrees Edge` (Constraints.hs:110-115): the source conclusion
/// before the target premise.  Only the node id of each end is a variable —
/// the conclusion and premise indices are `Int`s, whose instance contributes
/// nothing to the fold and maps to itself (LTerm.hs:820-823).
impl HasFrees for Edge {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.src.0.for_each_free(f);
        self.tgt.0.for_each_free(f);
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        Edge {
            src: (self.src.0.map_free_with(f, monotone), self.src.1),
            tgt: (self.tgt.0.map_free_with(f, monotone), self.tgt.1),
        }
    }
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

/// `instance HasFrees LessAtom` (Constraints.hs:145-150): the smaller node id
/// then the larger one.  The reason tag holds no variable and is carried over
/// by `pure`.
impl HasFrees for LessAtom {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.smaller.for_each_free(f);
        self.larger.for_each_free(f);
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        LessAtom {
            smaller: self.smaller.map_free_with(f, monotone),
            larger: self.larger.map_free_with(f, monotone),
            reason: self.reason,
        }
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

/// `instance HasFrees a => HasFrees (Disj a)` (LTerm.hs:884-889): the
/// disjuncts in list order, through the `Vec` instance.
impl<T: HasFrees> HasFrees for Disj<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        self.0.for_each_free(f);
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        Disj(self.0.map_free_with(f, monotone))
    }
}

// =============================================================================
// Goals
// =============================================================================

/// A `Goal` denotes that a constraint reduction rule is applicable.
///
/// The derived `Ord` mirrors HS's derived `Ord Goal` (Constraints.hs:159-172):
/// constructor rank is declaration order — `ActionG < ChainG < PremiseG <
/// SplitG < DisjG < SubtermG` — so the variants below MUST stay in HS's
/// declaration order (every goal sort in the solver routes through this
/// `Ord`; reordering silently changes the proof shape).  Within a
/// constructor the payloads compare left to right, each through an `Ord`
/// that mirrors its HS counterpart:
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
/// - `Guarded` — its own derived `Ord` (Guarded.hs:129); HS's `Disj` is a
///   newtype over a list, so the wrapper compares lexicographically.
///
/// HS holds `sGoals` in a `Map Goal GoalStatus`, so any `M.toList` walk of
/// it is in ascending `Goal` order; this crate's goal store is a `Vec` in
/// insertion order, so a caller mirroring such a walk sorts by this `Ord`
/// first.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

/// `instance HasFrees Goal` (Constraints.hs:210-232): every variant folds and
/// maps its payloads left to right — the timepoint before the fact of an
/// `Action`, the node id of a `Premise`'s premise before its fact, the
/// conclusion's node id before the premise's for a `Chain`, and both sides of
/// a `Subterm` pair (LTerm.hs:855-860).  A `Premise`/`Chain` index is an
/// `Int`, so only the node id of such a pair is a variable
/// (LTerm.hs:820-823).  `Split` carries a `SplitId`, whose instance is `const
/// mempty` / `pure` (EquationStore.hs:91-94).
impl HasFrees for Goal {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        match self {
            Goal::Action(i, fa) => {
                i.for_each_free(f);
                fa.for_each_free(f);
            }
            Goal::Premise(p, fa) => {
                p.0.for_each_free(f);
                fa.for_each_free(f);
            }
            Goal::Chain(c, p) => {
                c.0.for_each_free(f);
                p.0.for_each_free(f);
            }
            Goal::Split(_) => {}
            Goal::Disj(x) => x.for_each_free(f),
            Goal::Subterm(p) => p.for_each_free(f),
        }
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        match self {
            Goal::Action(i, fa) => {
                Goal::Action(i.map_free_with(f, monotone), fa.map_free_with(f, monotone))
            }
            Goal::Premise((n, i), fa) => Goal::Premise(
                (n.map_free_with(f, monotone), i),
                fa.map_free_with(f, monotone),
            ),
            Goal::Chain((cn, ci), (pn, pi)) => Goal::Chain(
                (cn.map_free_with(f, monotone), ci),
                (pn.map_free_with(f, monotone), pi),
            ),
            Goal::Split(i) => Goal::Split(i),
            Goal::Disj(x) => Goal::Disj(x.map_free_with(f, monotone)),
            Goal::Subterm(p) => Goal::Subterm(p.map_free_with(f, monotone)),
        }
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
        // The test compares the complete projection.  The order of the pair
        // inside an atom is the direction of the ordering edge.  The order
        // of the atoms is the iteration order of the relation.  A check of
        // two endpoints alone leaves both of these orders unchecked.
        assert_eq!(
            get_less_rel(&atoms),
            vec![(node("i"), node("j")), (node("j"), node("k"))]
        );
    }

    // HS's derived `Ord Goal` ranks by constructor first, in declaration
    // order `ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG`
    // (Constraints.hs:159-172), and only then by payload.
    #[test]
    fn goal_ord_ranks_constructors_in_haskell_order() {
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
                    a.cmp(b),
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
        assert_eq!(lo.cmp(&hi), Ordering::Less);
        // Equal node ids fall through to the fact, which orders by tag then
        // terms with annotations ignored (Model/Fact.hs:173-174).
        let fresh = LNFact::new(FactTag::Fresh, vec![t.clone()]);
        let a_out = Goal::Action(node("i"), fa);
        let a_fresh = Goal::Action(node("i"), fresh);
        assert_eq!(a_fresh.cmp(&a_out), Ordering::Less);
        assert_eq!(a_out.cmp(&a_out), Ordering::Equal);

        // `SplitG` compares its id; `SubtermG` its term pair left to right.
        assert_eq!(
            Goal::Split(SplitId(1)).cmp(&Goal::Split(SplitId(2))),
            Ordering::Less
        );
        let u = lit(Lit::Var(LVar::new("y", LSort::Msg, 0)));
        assert_eq!(
            Goal::Subterm((t.clone(), t.clone())).cmp(&Goal::Subterm((t.clone(), u))),
            Ordering::Less
        );
    }

    /// Each `is_*` predicate matches its own variant and no other variant.
    /// The failure mode is a copied `matches!` arm that names the
    /// neighbouring variant.  HS ships exactly that bug in `isSubtermGoal`,
    /// which is a copy of `isDisjGoal`.  See the note on
    /// [`Goal::is_subterm`].
    #[test]
    fn goal_kind_predicates() {
        use crate::fact::{FactTag, LNFact};
        use crate::guarded::gtrue;
        use crate::rule::{ConcIdx, PremIdx};
        use crate::tools::equation_store::SplitId;
        use tamarin_term::term::lit;
        use tamarin_term::vterm::Lit;

        let i = node("i");
        let t = lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
        let out = LNFact::new(FactTag::Out, vec![t.clone()]);
        // The columns are in this order: action, premise, chain, split,
        // disj, subterm.
        let cases = [
            ("Action", Goal::Action(i, out.clone()), [1, 0, 0, 0, 0, 0]),
            (
                "Chain",
                Goal::Chain((i, ConcIdx(0)), (i, PremIdx(0))),
                [0, 0, 1, 0, 0, 0],
            ),
            (
                "Premise",
                Goal::Premise((i, PremIdx(0)), out.clone()),
                [0, 1, 0, 0, 0, 0],
            ),
            ("Split", Goal::Split(SplitId(0)), [0, 0, 0, 1, 0, 0]),
            (
                "Disj",
                Goal::Disj(Disj::new(vec![gtrue()])),
                [0, 0, 0, 0, 1, 0],
            ),
            (
                "Subterm",
                Goal::Subterm((t.clone(), t.clone())),
                [0, 0, 0, 0, 0, 1],
            ),
        ];
        for (name, g, want) in &cases {
            let got = [
                g.is_action(),
                g.is_premise(),
                g.is_chain(),
                g.is_split(),
                g.is_disj(),
                g.is_subterm(),
            ];
            assert_eq!(got, want.map(|b| b == 1), "{name}");
        }
        // `is_standard_action` is the only predicate that does more than a
        // variant match.  `KU(_)` action goals are the intruder-knowledge
        // goals that the solver handles as a special case.  They are not
        // standard.
        assert!(Goal::Action(i, out).is_standard_action());
        assert!(!Goal::Action(i, LNFact::new(FactTag::Ku, vec![t])).is_standard_action());
        assert!(!Goal::Split(SplitId(0)).is_standard_action());
    }

    // =========================================================================
    // HasFrees instances
    // =========================================================================

    use tamarin_term::lterm::frees_list;

    fn node_at(name: &str, idx: u64) -> NodeId {
        LVar::new(name, LSort::Node, idx)
    }

    fn msg_var(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }

    fn msg_term(name: &str, idx: u64) -> LNTerm {
        tamarin_term::term::lit(tamarin_term::vterm::Lit::Var(msg_var(name, idx)))
    }

    /// An `Out` fact whose two arguments carry a variable each, so a walk that
    /// visits the fact shows both of them in argument order.
    fn out_fact() -> crate::fact::LNFact {
        crate::fact::LNFact::new(
            crate::fact::FactTag::Out,
            vec![msg_term("x", 5), msg_term("y", 6)],
        )
    }

    /// A guarded atom over two free node leaves.
    fn guarded_pair() -> Guarded {
        use crate::atom::ProtoAtom;
        use tamarin_term::lterm::{BVar, LSort, LVar};
        use tamarin_term::vterm::var_term;
        let leaf = |name: &str, idx: u64| var_term(BVar::Free(LVar::new(name, LSort::Node, idx)));
        Guarded::Atom(ProtoAtom::Less(leaf("g", 8), leaf("h", 9)))
    }

    /// Add 100 to the index of every variable the map reaches.  The rename is
    /// injective, so a payload the map leaves alone keeps its own index and the
    /// assertions can tell the two apart.
    fn shifted<T: HasFrees>(t: T) -> T {
        t.map_free(&mut |v: LVar| LVar::new(v.name, v.sort, v.idx + 100))
    }

    /// `instance HasFrees Edge` (Constraints.hs:110-115): source then target,
    /// and the two indices are not variables.
    #[test]
    fn edge_visits_the_source_before_the_target() {
        let e = Edge {
            src: (node_at("i", 1), ConcIdx(2)),
            tgt: (node_at("j", 3), PremIdx(4)),
        };
        assert_eq!(frees_list(&e), vec![node_at("i", 1), node_at("j", 3)]);
        assert_eq!(
            shifted(e),
            Edge {
                src: (node_at("i", 101), ConcIdx(2)),
                tgt: (node_at("j", 103), PremIdx(4)),
            }
        );
    }

    /// `instance HasFrees LessAtom` (Constraints.hs:145-150): smaller then
    /// larger, with the reason carried over.  `PartialEq LessAtom` ignores the
    /// reason, so the fields are compared one by one.
    #[test]
    fn less_atom_visits_smaller_then_larger_and_keeps_the_reason() {
        let la = LessAtom::new(node_at("i", 1), node_at("j", 2), Reason::InjectiveFacts);
        assert_eq!(frees_list(&la), vec![node_at("i", 1), node_at("j", 2)]);
        let mapped = shifted(la);
        assert_eq!(mapped.smaller, node_at("i", 101));
        assert_eq!(mapped.larger, node_at("j", 102));
        assert_eq!(mapped.reason, Reason::InjectiveFacts);
    }

    /// `instance HasFrees a => HasFrees (Disj a)` (LTerm.hs:884-889): list
    /// order in both directions, with no sorting of the disjuncts.
    #[test]
    fn disj_visits_its_items_in_list_order() {
        let d = Disj::new(vec![node_at("b", 2), node_at("a", 1)]);
        assert_eq!(frees_list(&d), vec![node_at("b", 2), node_at("a", 1)]);
        assert_eq!(shifted(d).0, vec![node_at("b", 102), node_at("a", 101)]);
    }

    /// `instance HasFrees Goal`'s fold (Constraints.hs:210-218), one variant
    /// per row and a variable of its own in every payload, so the sequence
    /// pins which payload comes first.
    #[test]
    fn goal_visits_its_payloads_in_haskell_order() {
        let cases: Vec<(Goal, Vec<LVar>)> = vec![
            (
                Goal::Action(node_at("i", 1), out_fact()),
                vec![node_at("i", 1), msg_var("x", 5), msg_var("y", 6)],
            ),
            (
                Goal::Premise((node_at("i", 1), PremIdx(7)), out_fact()),
                vec![node_at("i", 1), msg_var("x", 5), msg_var("y", 6)],
            ),
            (
                Goal::Chain((node_at("i", 1), ConcIdx(7)), (node_at("j", 2), PremIdx(8))),
                vec![node_at("i", 1), node_at("j", 2)],
            ),
            (Goal::Split(SplitId(3)), vec![]),
            (
                Goal::Disj(Disj::new(vec![guarded_pair()])),
                vec![node_at("g", 8), node_at("h", 9)],
            ),
            (
                Goal::Subterm((msg_term("s", 3), msg_term("t", 4))),
                vec![msg_var("s", 3), msg_var("t", 4)],
            ),
        ];
        for (g, want) in cases {
            assert_eq!(frees_list(&g), want, "{g:?}");
        }
    }

    /// `instance HasFrees Goal`'s map (Constraints.hs:226-232): every payload
    /// is rewritten, the premise and conclusion indices stay, and a `SplitG`
    /// keeps its id.
    #[test]
    fn goal_map_free_rewrites_every_payload() {
        let shifted_fact = crate::fact::LNFact::new(
            crate::fact::FactTag::Out,
            vec![msg_term("x", 105), msg_term("y", 106)],
        );
        assert_eq!(
            shifted(Goal::Action(node_at("i", 1), out_fact())),
            Goal::Action(node_at("i", 101), shifted_fact.clone())
        );
        assert_eq!(
            shifted(Goal::Premise((node_at("i", 1), PremIdx(7)), out_fact())),
            Goal::Premise((node_at("i", 101), PremIdx(7)), shifted_fact)
        );
        assert_eq!(
            shifted(Goal::Chain(
                (node_at("i", 1), ConcIdx(7)),
                (node_at("j", 2), PremIdx(8))
            )),
            Goal::Chain(
                (node_at("i", 101), ConcIdx(7)),
                (node_at("j", 102), PremIdx(8))
            )
        );
        assert_eq!(shifted(Goal::Split(SplitId(3))), Goal::Split(SplitId(3)));
        assert_eq!(
            frees_list(&shifted(Goal::Disj(Disj::new(vec![guarded_pair()])))),
            vec![node_at("g", 108), node_at("h", 109)]
        );
        assert_eq!(
            shifted(Goal::Subterm((msg_term("s", 3), msg_term("t", 4)))),
            Goal::Subterm((msg_term("s", 103), msg_term("t", 104)))
        );
    }
}
