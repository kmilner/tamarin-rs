//! Graph representation, simplification, abbreviations.
//!
//! Mirrors the layout of `lib/theory/src/Theory/Constraint/System/Graph/`:
//!
//! - [`repr`]         -> `GraphRepr.hs`
//! - [`simplify`]     -> `Simplification.hs`
//! - [`abbreviation`] -> `Abbreviation.hs`
//! - [`options`]      -> the top-level `Graph.hs` `GraphOptions` record.

pub mod abbreviation;
pub mod options;
pub mod render_system;
pub mod repr;
pub mod simplify;

pub use render_system::RenderSystem;

pub use options::{GraphOptions, graph_options_from_query, graph_options_from_params};
pub use repr::{
    add_cluster_by_role, add_intelligent_cluster_using_similar_names,
    compute_basic_graph_repr, Cluster, GEdge,
    GNode, GraphRepr, MissingHint, NodeType,
};
pub use simplify::{compress_system, simplify_system, SimplificationLevel};
pub use abbreviation::{
    apply_abbreviations_fact, compute_abbreviations,
    AbbreviationOptions, Abbreviations,
};
