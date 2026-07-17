// Currently GPL 3.0 until granted permission by the following authors:
//   Artur Cygan, Simon Meier, Adrian Dapprich, Felix Linker, Jannik Dreier,
//   Cas Cremers, "Jackie" (github kanakanajm), Ralf Sasse, Yann Colomb,
//   "Tom" (github BTom-GH), Benedikt Schmidt, Alexander Dax, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/System/Graph/Graph.hs,
//   src/Web/Handler.hs

//! Port of `GraphOptions` from `Graph.hs`.

// this module's `HashMap<String, String>` values are
// query-parameter maps (from the request query string / axum's `Query`
// extractor), consumed by keyed lookup (`.get`) only — never iterated into
// output.  They are also off the batch `--prove` byte-parity surface (server
// UI only).  std kept: axum's `Query<HashMap<..>>` requires the std type.
#![allow(clippy::disallowed_types)]

use std::collections::HashMap;

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
        // Mirror of `defaultGraphOptions` (Graph.hs).
        GraphOptions {
            simplification_level: SimplificationLevel::SL2,
            show_auto_source: false,
            clustering_similar_names: false,
            abbreviate: true,
            compress: true,
        }
    }
}

/// Build `GraphOptions` from a render-request query string.
///
/// Faithful port of Haskell `getOptions` (`Web/Handler.hs`).
/// The flags are presence-based (`un*`/`no-*` toggles arrive with an empty
/// value, so presence, not value, is what matters):
/// - `uncompress`     present => `compress = false`        (HS `isNothing`)
/// - `unabbreviate`   present => `abbreviate = false`      (HS `isNothing`)
/// - `no-auto-sources` present => `show_auto_source = false` (HS `isNothing`;
///   absent => `true`, which overrides the struct default of `false`)
/// - `clustering`     present => `clustering_similar_names = true` (HS `isJust`)
/// - `simplification` value read with `SimplificationLevel`'s derived `Read`,
///   i.e. only the tokens `SL0..SL3` parse (numeric `0..3`, the value the UI
///   actually sends, fails to parse); anything else falls back to `SL2`
///   (HS `fromMaybe SL2 (simpl >>= readMaybe . T.unpack)`).
///
/// The `uncompact`/`CompactBoringNodes` flag belongs to `DotOptions`
/// (`Handler.hs`), not `GraphOptions`, so it is not handled here.
///
/// Convenience wrapper that parses the query string and delegates to
/// [`graph_options_from_params`]; live handlers go through
/// `graph_options_from_params` directly, so this entry point is used
/// only where a raw query string is on hand (and in tests).
pub fn graph_options_from_query(qs: &str) -> GraphOptions {
    let params: HashMap<String, String> = qs.split('&')
        .filter(|kv| !kv.is_empty())
        .map(|kv| {
            let mut it = kv.splitn(2, '=');
            let k = it.next().unwrap_or("");
            let v = it.next().unwrap_or("");
            (k.to_string(), v.to_string())
        }).collect();
    graph_options_from_params(&params)
}

/// Build `GraphOptions` from an already-parsed query parameter map.
/// Shares the keyed-lookup logic of [`graph_options_from_query`] so callers
/// that already hold a `HashMap` need not re-serialise it to a query string.
pub fn graph_options_from_params(params: &HashMap<String, String>) -> GraphOptions {
    let simplification_level = params
        .get("simplification")
        .and_then(|v| read_simplification_level(v))
        .unwrap_or(SimplificationLevel::SL2);

    GraphOptions {
        simplification_level,
        // `isNothing <$> lookupGetParam "no-auto-sources"`: absent => true.
        show_auto_source: !params.contains_key("no-auto-sources"),
        // `_goClustering = isJust clustering`.
        clustering_similar_names: params.contains_key("clustering"),
        // `isNothing <$> lookupGetParam "unabbreviate"`.
        abbreviate: !params.contains_key("unabbreviate"),
        // `isNothing <$> lookupGetParam "uncompress"`.
        compress: !params.contains_key("uncompress"),
    }
}

/// Parse a `SimplificationLevel` exactly as Haskell's derived `Read` would.
///
/// The data type is `data SimplificationLevel = SL0 | SL1 | SL2 | SL3`
/// (`Graph.hs`), so its derived `Read` parses only the bare
/// constructor tokens. Following `Read`'s lexer it skips leading/trailing
/// whitespace and accepts one or more matched pairs of surrounding parentheses;
/// numeric input (e.g. `"2"`) fails. Returns `None` on any non-match.
fn read_simplification_level(s: &str) -> Option<SimplificationLevel> {
    let mut t = s.trim();
    // Derived `Read` allows one (or more) matched pairs of surrounding parens.
    while let (Some(inner), true) = (t.strip_prefix('('), t.ends_with(')')) {
        t = inner.strip_suffix(')')?.trim();
    }
    match t {
        "SL0" => Some(SimplificationLevel::SL0),
        "SL1" => Some(SimplificationLevel::SL1),
        "SL2" => Some(SimplificationLevel::SL2),
        "SL3" => Some(SimplificationLevel::SL3),
        _ => None,
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

    #[test]
    fn empty_query_matches_haskell_getoptions_defaults() {
        // With no params HS `getOptions` yields: compress/abbreviate true
        // (uncompress/unabbreviate absent => isNothing => True), clustering
        // false (isJust Nothing), simplification SL2 (readMaybe of Nothing =>
        // fromMaybe SL2), and show_auto_source TRUE -- note this differs from
        // the struct default (False), because `no-auto-sources` is absent so
        // `isNothing` yields True.
        let o = graph_options_from_query("");
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
        assert!(o.compress);
        assert!(o.abbreviate);
        assert!(!o.clustering_similar_names);
        assert!(o.show_auto_source);
    }

    #[test]
    fn full_query_mirrors_getoptions() {
        // The UI sends numeric simplification=2, which HS derived `Read` for
        // SimplificationLevel cannot parse (only SL0..SL3), so it falls back to
        // SL2. The presence flags flip their respective options off (or on, for
        // clustering).
        let o = graph_options_from_query(
            "simplification=2&clustering=true&uncompress=&unabbreviate=&no-auto-sources=",
        );
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
        assert!(o.clustering_similar_names);
        assert!(!o.compress);
        assert!(!o.abbreviate);
        assert!(!o.show_auto_source);
    }

    #[test]
    fn simplification_numeric_falls_back_to_sl2() {
        // HS readMaybe on "0".."3" returns Nothing (derived Read wants SL0..SL3).
        for n in ["0", "1", "2", "3"] {
            let o = graph_options_from_query(&format!("simplification={n}"));
            assert_eq!(
                o.simplification_level,
                SimplificationLevel::SL2,
                "numeric simplification={n} must fall back to SL2"
            );
        }
    }

    #[test]
    fn simplification_sl_tokens_parse() {
        assert_eq!(
            graph_options_from_query("simplification=SL0").simplification_level,
            SimplificationLevel::SL0
        );
        assert_eq!(
            graph_options_from_query("simplification=SL1").simplification_level,
            SimplificationLevel::SL1
        );
        assert_eq!(
            graph_options_from_query("simplification=SL3").simplification_level,
            SimplificationLevel::SL3
        );
        // Derived `Read` is case-sensitive and tolerates surrounding parens.
        assert_eq!(read_simplification_level("(SL3)"), Some(SimplificationLevel::SL3));
        assert_eq!(read_simplification_level(" ( SL3 ) "), Some(SimplificationLevel::SL3));
        assert_eq!(read_simplification_level("sl2"), None);
        assert_eq!(read_simplification_level("2"), None);
        assert_eq!(read_simplification_level("SL4"), None);
        assert_eq!(read_simplification_level(""), None);
    }

    #[test]
    fn presence_flag_with_value_still_counts() {
        // `un*`/`no-*` flags are presence-based; a non-empty value (or no `=`)
        // is still "present".
        let o = graph_options_from_query("uncompress");
        assert!(!o.compress);
        let o2 = graph_options_from_query("clustering");
        assert!(o2.clustering_similar_names);
    }

    #[test]
    fn parse_query_unknown_param_keeps_haskell_defaults() {
        // Unknown params do not touch any field; result equals the empty-query
        // (getOptions) outcome, which has show_auto_source = true.
        let o = graph_options_from_query("unknown=42");
        assert_eq!(o, graph_options_from_query(""));
        assert!(o.show_auto_source);
    }
}
