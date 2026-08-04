// Currently GPL 3.0 until granted permission by the following authors:
//   addap, meiersi, Mathias-AURAND, Divya19gupta, rkunnema,
//   Esslingen-Security-Privacy, cascremers, sans-sucre, arcz,
//   felixlinker, jdreier, yavivanov, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/System/Dot.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Abbreviation.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Graph.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Simplification.hs,
//   lib/theory/src/Theory/Constraint/System/JSON.hs,
//   lib/utils/src/Text/Dot.hs, src/Web/Utils.hs

//! Graph representation, simplification, abbreviations.
//!
//! This module itself is the top-level `Graph.hs`: it holds [`Graph`] and
//! [`system_to_graph`], the single pipeline both renderers
//! (`handlers::dot` -> `Dot.hs`, [`json`] -> `JSON.hs`) consume.  The rest
//! mirrors the layout of `lib/theory/src/Theory/Constraint/System/Graph/`:
//!
//! - [`repr`]         -> `GraphRepr.hs`
//! - [`simplify`]     -> `Simplification.hs`
//! - [`abbreviation`] -> `Abbreviation.hs`
//! - [`options`]      -> the `Graph.hs` `GraphOptions` record.
//!
//! Two further modules serve the JSON graph endpoint:
//!
//! - [`json`]              -> `Theory/Constraint/System/JSON.hs`
//! - [`web_utils_abbrev`]  -> `src/Web/Utils.hs`
//!
//! and [`color`] holds the `nodeColorMap` palette both renderers key node
//! fills off (`Dot.hs`).

pub mod abbreviation;
pub mod color;
pub mod json;
pub mod options;
pub mod render_system;
pub mod repr;
pub mod simplify;
pub mod web_utils_abbrev;

pub use render_system::RenderSystem;

pub use abbreviation::{
    apply_abbreviations_fact, compute_abbreviations, AbbreviationOptions, Abbreviations,
};
pub use options::{graph_options_from_params, graph_options_from_query, GraphOptions};
pub use repr::{
    add_cluster_by_role, add_intelligent_cluster_using_similar_names, compute_basic_graph_repr,
    Cluster, GEdge, GNode, GraphRepr, MissingHint, NodeType,
};
pub use simplify::{compress_system, simplify_system, SimplificationLevel};

use tamarin_theory::constraint::system::System;

/// Mirror of HS `Graph` (Graph.hs:76-81) restricted to the fields the two
/// renderers read.
pub struct Graph<'a> {
    /// HS `_gSystem`: the ORIGINAL, un-compressed/un-simplified system handed
    /// to [`system_to_graph`].  `resolveNodePremFact`/`resolveNodeConcFact`
    /// (Graph.hs:87-96) look facts up in it, so BOTH renderers type and colour
    /// an edge from this system's rules — `dotEdge`'s `check` (Dot.hs:391-392)
    /// and `getRelationType`/`colorEdge` (JSON.hs:434-435/452-453) — even for an
    /// endpoint the compression hid.
    pub system: &'a System,
    /// The compressed/simplified copy [`Graph::repr`] was computed from.  These
    /// nodes decide ONLY the record PORT an edge endpoint renders as, matching
    /// the `dsConcs`/`dsPrems` state HS fills while emitting the repr's nodes
    /// (Dot.hs:264-268) and reads back in `dotGenEdge` (Dot.hs:403-406).
    pub simplified: RenderSystem,
    /// HS `_gRepr`.
    pub repr: GraphRepr,
    /// HS `_gAbbreviations`.
    pub abbreviations: Abbreviations,
}

/// Port of `systemToGraph` (Graph.hs:153-165).
///
/// Abbreviations are computed unconditionally: `goAbbreviate` gates only their
/// APPLICATION — in the DOT renderer at `renderLNFact` (Dot.hs:228-236) and at
/// `when abbreviate generateLegend` (Dot.hs:538), and not at all in the JSON
/// export, which lists them verbatim while leaving node terms unabbreviated
/// (the frontend performs the substitution).
pub fn system_to_graph<'a>(sys: &'a System, options: &GraphOptions) -> Graph<'a> {
    // Clone-for-render boundary: the compress/simplify passes mutate their
    // working copy in ways that leave the `subst_system` stamps meaningless,
    // so they run on a write-sealed `RenderSystem`.
    let working = RenderSystem::from_prover(sys.clone());
    let working = if options.compress {
        compress_system(working)
    } else {
        working
    };
    let simplified = simplify_system(options.simplification_level, working);
    // `compute_basic_graph_repr` takes `&System`; `&RenderSystem` derefs to it.
    let mut repr = compute_basic_graph_repr(&simplified);
    if options.clustering_similar_names {
        add_intelligent_cluster_using_similar_names(&mut repr);
    } else {
        add_cluster_by_role(&mut repr);
    }
    let abbreviations = compute_abbreviations(&repr, &AbbreviationOptions::default());
    Graph {
        system: sys,
        simplified,
        repr,
        abbreviations,
    }
}
