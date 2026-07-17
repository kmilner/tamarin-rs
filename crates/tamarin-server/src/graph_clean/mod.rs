//! # graph-clean
//!
//! A clean-room reimplementation of the tamarin-prover web-UI constraint-system
//! graph payload — the graphviz DOT text served at
//! `/thy/trace/N/interactive-graph-def/proof/…`.
//!
//! Everything here was derived from BLACK-BOX observation of captured payloads
//! and live probing of the compiled server; see `workspace/BEHAVIOR.md` for the
//! observed spec and `workspace/QUERIES.log` for the oracle interactions. No
//! tamarin-prover source was consulted.
//!
//! ## What it does
//! * [`model`] — an independent graph data model (nodes, edges, clusters, legend).
//! * [`dot::to_dot`] — a **byte-exact** DOT serializer for that model.
//! * [`term`] — a small term model backing abbreviation expansions.
//! * [`abbrev`] — node abbreviation: prefix derivation, per-prefix numbering,
//!   and byte-exact legend-table HTML.
//!
//! ## Clustering / simplification trigger
//! The compact (clustered) header is used exactly when a graph carries a node
//! with a role other than `Undefined`; [`model::Graph::infer_header`] applies
//! this observed rule.
//!
//! ```ignore
//! use graph_clean::model::*;
//! let mut g = Graph::new(Header::Simple);
//! g.push(Stmt::Node(Node::ellipse("n7", Ellipse::new("#vf : isend"))));
//! let dot = graph_clean::dot::to_dot(&g);
//! assert!(dot.starts_with("digraph \"G\" {\nnodesep=\"0.3\";"));
//! assert!(dot.ends_with("\n\n}\n"));
//! ```

pub mod abbrev;
pub mod dot;
pub mod model;
pub mod term;

pub use dot::to_dot;
pub use model::{Graph, Header};
pub use term::Term;
