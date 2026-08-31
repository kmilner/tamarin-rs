// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of the `GraphOptions` record from `Graph.hs`.
//!
//! Reading the record out of a render request's query parameters is HS
//! `getOptions` (`src/Web/Handler.hs`) and lives with the web handlers, in
//! `tamarin-server`.

use super::simplify::SimplificationLevel;

/// Options for graph generation.  Mirror of `GraphOptions`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GraphOptions {
    pub simplification_level: SimplificationLevel,
    pub show_auto_source: bool,
    /// If `true`, cluster by similar rule names; if `false`, cluster
    /// by role.  Matches Haskell `goClustering`.
    pub clustering_similar_names: bool,
    pub abbreviate: bool,
    pub compress: bool,
}

impl Default for GraphOptions {
    fn default() -> Self {
        // Mirror of `defaultGraphOptions` (Graph.hs:66-73).
        GraphOptions {
            simplification_level: SimplificationLevel::SL2,
            show_auto_source: false,
            clustering_similar_names: false,
            abbreviate: true,
            compress: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_match_haskell() {
        let o = GraphOptions::default();
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
        assert!(!o.show_auto_source);
        assert!(!o.clustering_similar_names);
        assert!(o.abbreviate);
        assert!(o.compress);
    }
}
