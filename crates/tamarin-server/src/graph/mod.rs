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
//! Mirrors the layout of `lib/theory/src/Theory/Constraint/System/Graph/`:
//!
//! - [`repr`]         -> `GraphRepr.hs`
//! - [`simplify`]     -> `Simplification.hs`
//! - [`abbreviation`] -> `Abbreviation.hs`
//! - [`options`]      -> the top-level `Graph.hs` `GraphOptions` record.
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
