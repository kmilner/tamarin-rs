// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Theory tags that the parser AST and the elaborated theory both carry.
//!
//! Haskell declares each of these once and its parser builds them directly,
//! because parser and theory model live in the same package. This port puts
//! the parser in a crate below `tamarin-theory`, so the tags live here, in
//! the crate both depend on, and `tamarin-theory` re-exports them beside the
//! types that hold them.

/// HS `TraceQuantifier` (Items/LemmaItem.hs:42-44): whether a lemma claims
/// validity over all traces or satisfiability by one.  The variant order is
/// HS's declaration order, which its derived `Ord` reads off.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceQuantifier {
    ExistsTrace,
    AllTraces,
}

/// HS `LemmaAttribute` (Items/LemmaItem.hs:27-40): an attribute written in a
/// lemma's `[...]` list.  HS's `LemmaTactic` has no counterpart here: no
/// spelling in `lemmaAttribute` (Theory/Text/Parser/Lemma.hs:38-53) builds
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
    /// `LemmaModule`, holding the module names of `output=[...]`.
    Output(Vec<String>),
}

/// HS `FactAnnotation` (Theory/Model/Fact.hs:151-155): a property carried
/// beside a fact for dot rendering and goal ranking, with no effect on the
/// fact's semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactAnnotation {
    SolveFirst,
    SolveLast,
    NoSources,
}
