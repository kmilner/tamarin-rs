// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Graph representation, simplification, abbreviations.
//!
//! This module itself is the top-level `Graph.hs`: it holds [`Graph`] and
//! [`system_to_graph`], the single pipeline both renderers
//! ([`super::dot`] -> `Dot.hs`, [`super::json`] -> `JSON.hs`) consume.  The
//! rest mirrors the layout of
//! `lib/theory/src/Theory/Constraint/System/Graph/`:
//!
//! - [`repr`]         -> `GraphRepr.hs`
//! - [`simplify`]     -> `Simplification.hs`
//! - [`abbreviation`] -> `Abbreviation.hs`
//! - [`options`]      -> the `Graph.hs` `GraphOptions` record (reading it out
//!                       of a web request's query parameters is HS
//!                       `getOptions`, `Web/Handler.hs`, and stays in
//!                       `tamarin-server`).
//!
//! and [`color`] holds the `nodeColorMap` palette both renderers key node
//! fills off (`Dot.hs`).

pub mod abbreviation;
pub mod color;
pub mod options;
pub mod render_system;
pub mod repr;
pub mod simplify;

// The three names consumers reach for by the short `graph::` path; everything
// else in the submodules is addressed through the submodule itself.
pub use options::GraphOptions;
pub use render_system::RenderSystem;
pub use simplify::SimplificationLevel;

use abbreviation::{compute_abbreviations, AbbreviationOptions, Abbreviations};
// `Graph.hs` builds on `computeBasicGraphRepr` without exporting it.
use repr::{
    add_cluster_by_role, add_intelligent_cluster_using_similar_names, compute_basic_graph_repr,
    GraphRepr,
};
use simplify::{compress_system, simplify_system};

use crate::constraint::system::System;

/// Mirror of HS `Graph` (Graph.hs:76-81) restricted to the fields the two
/// renderers read.
pub struct Graph<'a> {
    /// HS `_gSystem`: the ORIGINAL, un-compressed/un-simplified system handed
    /// to [`system_to_graph`].  `resolveNodePremFact`/`resolveNodeConcFact`
    /// (Graph.hs:87-96) look facts up in it, so BOTH renderers type and colour
    /// an edge from this system's rules — `dotEdge`'s `check` (System/Dot.hs:391-392)
    /// and `getRelationType`/`colorEdge` (JSON.hs:434-435/452-453) — even for an
    /// endpoint the compression hid.
    pub system: &'a System,
    /// HS `_gRepr`.
    pub repr: GraphRepr,
    /// HS `_gAbbreviations`.
    pub abbreviations: Abbreviations,
}

/// Port of `systemToGraph` (Graph.hs:153-165).
///
/// Abbreviations are computed unconditionally: `goAbbreviate` gates only their
/// APPLICATION — in the DOT renderer at `renderLNFact` (System/Dot.hs:228-236) and at
/// `when abbreviate generateLegend` (System/Dot.hs:538), and not at all in the JSON
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
        repr,
        abbreviations,
    }
}
