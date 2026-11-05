// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Theory tags that the parser AST and the elaborated theory both carry.
//!
//! Haskell declares each of these once and its parser builds them directly,
//! because parser and theory model live in the same package. This port puts
//! the parser in a crate below `tamarin-theory`, so the tags live here, in
//! the crate both depend on, and `tamarin-theory` re-exports them beside the
//! types that hold them.

/// HS `TraceQuantifier` (Items/LemmaItem.hs): whether a lemma claims
/// validity over all traces or satisfiability by one.  The variant order is
/// HS's declaration order, which its derived `Ord` reads off.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceQuantifier {
    ExistsTrace,
    AllTraces,
}

/// HS `LemmaAttribute` (Items/LemmaItem.hs): an attribute written in a
/// lemma's `[...]` list.  HS's `LemmaTactic` has no counterpart here: no
/// spelling in `lemmaAttribute` (Theory/Text/Parser/Lemma.hs) builds
/// one, so nothing can carry it.  The variant order is HS's declaration order
/// with that one gap, which its derived `Ord` reads off.
#[derive(Debug, Clone, PartialEq)]
pub enum LemmaAttr {
    /// `SourceLemma`, spelled `sources` or `typing`.
    Sources,
    /// `ReuseLemma`.
    Reuse,
    /// `ReuseDiffLemma`.
    DiffReuse,
    /// `InvariantLemma`, spelled `use_induction`.
    UseInduction,
    /// `HideLemma`.
    HideLemma(String),
    /// `LHSLemma`, spelled `left`.
    Left,
    /// `RHSLemma`, spelled `right`.
    Right,
    /// `LemmaHeuristic`, holding the goal-ranking string as written.
    Heuristic(String),
    /// Per-lemma search selection, below an explicitly forced frontend choice.
    StopOnTrace(CutStrategy),
    /// `LemmaModule`, holding the module names of `output=[...]`.
    Output(Vec<String>),
}

/// HS `FactAnnotation` (Theory/Model/Fact.hs): a property carried
/// beside a fact for dot rendering and goal ranking, with no effect on the
/// fact's semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactAnnotation {
    SolveFirst,
    SolveLast,
    NoSources,
}

/// How the auto-prover cuts the proof tree around solved leaves,
/// mirroring HS `SolutionExtractor` (Theory/Proof.hs) as selected
/// by `runAutoProver` (Theory/Proof.hs).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum CutStrategy {
    /// HS `CutDFS` → `cutOnSolvedDFS` (Theory/Proof.hs): parallel
    /// iterative-deepening DFS, doubling `dMax` from 4.  Selects the leftmost
    /// (preorder, CaseName order) solved leaf among those shallower than the
    /// first `dMax` (4, 8, 16, …) to admit any solved leaf — within that
    /// depth bucket a deeper-but-leftmost leaf beats a shallower one further
    /// right, so this is NOT globally-shallowest.  The default when
    /// `--stop-on-trace` is absent
    /// (HS `constructAutoProver`: `fromMaybe CutDFS`, TheoryLoader.hs).
    #[default]
    Dfs,
    /// HS `CutSingleThreadDFS` → `cutOnSolvedSingleThreadDFS`
    /// (Theory/Proof.hs): single-thread depth-first with NO depth
    /// bound and NO iterative deepening.  `findSolved`'s `foldMap` over the
    /// children map descends the leftmost branch (CaseName order) to
    /// completion before its siblings and stops at the first solved leaf, so
    /// a deep solved leaf under the leftmost branch wins over a shallower one
    /// further right even when the shallower leaf sits inside `Dfs`'s first
    /// depth bucket (where `Dfs` would cut the deep branch off and pick it).
    SeqDfs,
    /// HS `CutBFS` → `cutOnSolvedBFS` (Theory/Proof.hs): iterative
    /// level-deepening over the DFS proof tree.  At each level `l` the tree
    /// is forced to depth `l` and walked in CaseName order with threaded
    /// state: a Solved leaf at exactly depth `l` flips TraceFound; a node
    /// still pending at depth `l` is cut to `sorry /* bound reached */`
    /// (`sorry /* ignored (attack exists) */` once TraceFound).  On
    /// TraceFound the CUT tree is the result — those sorry leaves are part
    /// of the printed proof; a level that completes with nothing pending
    /// returns the full tree unchanged.
    Bfs,
    /// HS `CutNothing` → `id` (Theory/Proof.hs): no cut at all — the
    /// full proof tree is built and printed; sibling exploration does not
    /// stop when a trace is found.
    Nothing,
    /// HS `CutAfterSorry` → `cutAfterFirstSorry` (Theory/Proof.hs):
    /// preorder walk in CaseName order; the first `Sorry` or Solved leaf
    /// aborts, and every node visited after the abort becomes a bare
    /// `sorry` leaf (children dropped, system annotation kept).  Under the
    /// unbounded default prover the only aborter is a Solved leaf, so this
    /// reads as "stop at the first trace, sorry out the remainder".
    AfterSorry,
}

impl CutStrategy {
    pub fn parse(raw: &str) -> Option<Self> {
        match raw.to_ascii_lowercase().as_str() {
            "dfs" => Some(Self::Dfs),
            "bfs" => Some(Self::Bfs),
            "seqdfs" => Some(Self::SeqDfs),
            "none" => Some(Self::Nothing),
            "sorry" => Some(Self::AfterSorry),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Dfs => "DFS",
            Self::Bfs => "BFS",
            Self::SeqDfs => "SEQDFS",
            Self::Nothing => "NONE",
            Self::AfterSorry => "SORRY",
        }
    }
}
