// Currently GPL 3.0 until granted permission by the following authors:
//   addap, meiersi, rkunnema, Mathias-AURAND, Divya19gupta, sans-sucre,
//   yavivanov, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Constraint/System/Dot.hs,
//   lib/theory/src/Theory/Constraint/System/JSON.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/utils/src/Text/Dot.hs

//! Per-rule node colouring shared by the two graph renderers.
//!
//! Holds the port of HS `nodeColorMap` / `NodeColorMap` (Dot.hs:88,
//! Dot.hs:190-218) — the size-dependent light-HSV palette keyed by a rule's
//! `rInfo` — together with the less-edge `reasonColor` table and the
//! `prettyLNFact` `Doc` both renderers label facts with.  `handlers::dot`
//! (DOT output) and [`crate::graph::json`] (JSON output) are both consumers,
//! so this module sits under `graph/` rather than inside either renderer.

use tamarin_theory::constraint::constraints::{NodeId, Reason};
use tamarin_theory::fact::LNFact;
use tamarin_theory::pretty_hpj::Doc;
use tamarin_theory::rule::{IntrRuleACInfo, ProtoRuleName, RuleACInst, RuleInfo};

/// The `Doc` of an `LNFact` exactly as Haskell `renderLNFact =
/// prettyLNFact` (Dot.hs:225-233, Fact.hs:549-550, see line 551).  `prettyLNFact` builds the
/// argument list with `nestShort' (n++"(") ")" . fsep . punctuate comma`
/// (Fact.hs:539-546), which — unlike a bare `name(a, b)` — emits the
/// HughesPJ INNER-PAREN SPACES `!KU( ~ltk )` when the fact fits on one line.
/// We therefore reuse the *same* faithful `Doc` path the proof pretty-
/// printer uses for goals (`solve_goal_to_doc` → `pretty_formula::fact_doc`
/// on the parser-AST projection), NOT `pretty_system::pretty_fact` (which
/// omits those spaces).
pub(crate) fn fact_doc_of(fa: &LNFact) -> Doc {
    tamarin_theory::pretty_formula::fact_doc(&tamarin_theory::pretty_theory::lnfact_to_parser(fa))
}

/// HS `toColor` — the per-`Reason` less-edge colour, spelled identically in
/// the DOT renderer (`dotLessAtom.toColor`, Dot.hs:624-630) and in the JSON
/// serialiser (`colorEdge`'s `LessEdge` arm, JSON.hs:446-453).
pub(crate) fn reason_color(r: Reason) -> &'static str {
    match r {
        Reason::Adversary => "red",
        Reason::Formula => "black",
        Reason::Fresh => "blue3",
        Reason::InjectiveFacts => "purple",
        Reason::NormalForm => "darkorange3",
    }
}

/// Key of HS `NodeColorMap` (Dot.hs:88-88): a rule's `rInfo`
/// (`RuleInfo ProtoRuleACInstInfo IntrRuleACInfo`).
pub(crate) type RInfo = RuleInfo<tamarin_theory::rule::ProtoRuleACInstInfo, IntrRuleACInfo>;

/// Faithful port of HS `NodeColorMap` (Dot.hs:88-88) — the per-rule fill palette,
/// keyed by a rule's `rInfo`. Built by [`build_node_color_map`] (port of
/// `nodeColorMap`, Dot.hs:190-218). `rInfo` is not `Hash`/`Ord` in the Rust
/// port (`ProtoRuleACInstInfo` only derives `PartialEq`), so we keep an
/// association list and resolve lookups by equality. HS builds the map with
/// `M.fromList`, which keeps the LAST value for equal keys, so [`lookup`]
/// scans in reverse and returns the last matching entry.
///
/// [`lookup`]: NodeColorMap::lookup
pub(crate) struct NodeColorMap<'a> {
    entries: Vec<(&'a RInfo, tamarin_utils::color::Rgb)>,
}

impl NodeColorMap<'_> {
    /// HS `M.lookup rInfoVal colorMap` (Dot.hs:236-379, see line 255). Returns the LAST entry
    /// whose `rInfo` equals `info` (matching `M.fromList`'s last-wins), or
    /// `None` when the rInfo is absent (→ `"white"` at the call site).
    pub(crate) fn lookup(&self, info: &RInfo) -> Option<tamarin_utils::color::Rgb> {
        self.entries
            .iter()
            .rev()
            .find(|(k, _)| **k == *info)
            .map(|(_, c)| *c)
    }
}

/// HS `nodeColorMap.groupIdx` (Dot.hs:196-200): partition a rule into one of
/// four colour groups. Guard order matters and mirrors HS exactly:
///   * `isDestrRule` (DestrRule or IEqualityRule)               → 0
///   * `isConstrRule` (Constr/Fresh/Pub/Nat constr or Coerce)   → 2
///   * `isFreshRule` (proto `Fresh`) or `isISendRule`           → 3
///   * otherwise (protocol rules, IRecv, …)                     → 1
fn group_idx(ru: &RuleACInst) -> usize {
    use tamarin_theory::rule::{
        is_coerce_rule_info, is_constr_rule_info, is_destr_rule_info, is_fresh_constr_rule_info,
        is_iequality_rule_info, is_isend_rule_info, is_nat_constr_rule_info,
        is_pub_constr_rule_info,
    };
    match &ru.info {
        RuleInfo::Intr(i) => {
            if is_destr_rule_info(i) || is_iequality_rule_info(i) {
                0
            } else if is_constr_rule_info(i)
                || is_fresh_constr_rule_info(i)
                || is_pub_constr_rule_info(i)
                || is_nat_constr_rule_info(i)
                || is_coerce_rule_info(i)
            {
                2
            } else if is_isend_rule_info(i) {
                3
            } else {
                1
            }
        }
        // `isDestrRule`/`isConstrRule`/`isISendRule` are all intruder-only, so
        // a protocol rule only ever hits `isFreshRule` (the reserved `Fresh`
        // rule) → 3, else the `otherwise` group → 1.
        RuleInfo::Proto(p) => {
            if p.name == ProtoRuleName::Fresh {
                3
            } else {
                1
            }
        }
    }
}

/// Faithful port of HS `nodeColorMap` (Dot.hs:190-218).
///
/// HS: `M.fromList [ (get rInfo ru, getColorForRule (ruleAttributes ru) gIdx
/// mIdx) | (gIdx, grp) <- groups, (mIdx, ru) <- zip [0..] grp ]`, with the
/// four `groups` filtered from `rules` by [`group_idx`] and coloured via
/// `colors = lightColorGroups intruderHue (map (length . snd) groups)` and
/// `intruderHue = 18 % 360` (Dot.hs:190-218, see line 208,217-218).
///
/// `rules` here is `M.elems $ get sNodes se` (Dot.hs:481-487, see line 485) — the raw system's
/// nodes in NodeId order — so we sort by NodeId (`M.Map` key order) first.
/// Each entry's colour follows `getColorForRule attrs gIdx mIdx = fromMaybe
/// defaultColor (ruleColor attrs)` (Dot.hs:190-218, see line 212): a rule with an explicit
/// `color:` attribute maps to THAT colour, otherwise to the palette default
/// (`defaultColor = hsvToRGB (getColor (gIdx, mIdx))`, Dot.hs:190-218, see line 214).  This map
/// value is what `dotNodeCompact` feeds to `colorUsesWhiteFont` (Dot.hs:236-379, see line 255,
/// 258) to pick a node's font colour — so a SAPiC rule with a dark `color:`
/// attribute must map to that dark colour (→ white font), not to the light
/// palette default.  (The FILL colour is resolved separately via
/// `explicit_rule_color` at the call site, so carrying the explicit colour
/// here changes only the font decision, never the fill.)
pub(crate) fn build_node_color_map(nodes: &[(NodeId, RuleACInst)]) -> NodeColorMap<'_> {
    use tamarin_utils::color::{hsv_to_rgb, light_color_groups, Hsv, Rgb};

    // `M.elems $ get sNodes se`: iterate in NodeId (Map key) order.
    let mut ordered: Vec<&(NodeId, RuleACInst)> = nodes.iter().collect();
    ordered.sort_by_key(|a| a.0);

    // `groups = [ (gIdx, [ru | ru <- rules, gIdx == groupIdx ru]) | gIdx <- 0..3 ]`
    // — order-preserving partition into four groups.
    let mut groups: [Vec<&RuleACInst>; 4] = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
    for pair in &ordered {
        let ru = &pair.1;
        groups[group_idx(ru)].push(ru);
    }
    let sizes: [usize; 4] = [
        groups[0].len(),
        groups[1].len(),
        groups[2].len(),
        groups[3].len(),
    ];

    // `colors = M.fromList $ lightColorGroups intruderHue (map (length . snd)
    // groups)`, `intruderHue = 18 % 360`. The palette is exact `Rational` in
    // HS; the f64 port matches `rgbToHex`'s `floor(256*f)` quantisation for all
    // realistic group sizes (verified: 0/4.28M hex divergences).
    const INTRUDER_HUE: f64 = 18.0 / 360.0;
    let palette = light_color_groups(INTRUDER_HUE, &sizes);
    let get_color = |gi: usize, mi: usize| -> Hsv {
        palette
            .iter()
            .find(|((g, m), _)| *g == gi && *m == mi)
            .map(|(_, hsv)| *hsv)
            // `getColor idx = fromMaybe (HSV 0 1 1) (M.lookup idx colors)`
            // (Dot.hs:190-218, see line 209) — unreachable for a valid (gIdx, mIdx).
            .unwrap_or_else(|| Hsv::new(0.0, 1.0, 1.0))
    };

    let mut entries: Vec<(&RInfo, Rgb)> = Vec::new();
    for (gi, grp) in groups.iter().enumerate() {
        for (mi, ru) in grp.iter().enumerate() {
            // `getColorForRule attrs gIdx mIdx = fromMaybe defaultColor
            // (ruleColor attrs)` (Dot.hs:190-218, see line 212): explicit `color:` wins, else the
            // palette default.  `ruleAttributes ru = praciAttributes` for a
            // RuleACInst (Rule.hs:673-675, see line 674) — the same attributes `explicit_rule_color`
            // reads, so a coloured rule maps to its own dark fill colour.
            let color = match &ru.info {
                RuleInfo::Proto(p) => p
                    .attributes
                    .color
                    .unwrap_or_else(|| hsv_to_rgb(get_color(gi, mi))),
                _ => hsv_to_rgb(get_color(gi, mi)),
            };
            entries.push((&ru.info, color));
        }
    }
    NodeColorMap { entries }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_theory::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName as PRN, Rule as TRule, RuleAttributes,
        RuleInfo as TRuleInfo,
    };

    /// A bare intruder-rule node (no facts) with the given `IntrRuleACInfo`.
    fn intr_node(info: IntrRuleACInfo) -> RuleACInst {
        TRule::new(TRuleInfo::Intr(info), Vec::new(), Vec::new(), Vec::new())
    }
    fn destr(n: &[u8]) -> IntrRuleACInfo {
        IntrRuleACInfo::DestrRule(n.to_vec(), 0, false, false, vec![])
    }
    fn hex_of(cm: &NodeColorMap, ru: &RuleACInst) -> String {
        tamarin_utils::color::rgb_to_hex(cm.lookup(&ru.info).unwrap())
    }

    #[test]
    fn group_idx_partition_matches_hs() {
        // HS groupIdx (Dot.hs:196-200).
        assert_eq!(group_idx(&intr_node(destr(b"x"))), 0); // isDestrRule
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::IEquality)), 0);
        assert_eq!(
            group_idx(&intr_node(IntrRuleACInfo::ConstrRule(
                b"c".to_vec(),
                tamarin_term::function_symbols::FunSym::List
            ))),
            2
        );
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::Coerce)), 2); // isConstrRule
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::FreshConstr)), 2);
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::PubConstr)), 2);
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::NatConstr)), 2);
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::ISend)), 3); // isISendRule
        assert_eq!(group_idx(&named_proto_node(PRN::Fresh)), 3); // isFreshRule
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::IRecv)), 1); // otherwise
        assert_eq!(group_idx(&named_proto_node(PRN::Stand("R"))), 1); // otherwise
    }

    #[test]
    fn node_color_map_palette_hex_matches_hs() {
        // Expected hexes are hand-computed from HS `nodeColorMap` in EXACT
        // Rational arithmetic (lightColorGroups intruderHue sizes; intruderHue
        // = 18 % 360; hsvToRGB; rgbToHex = floor(256*f)), cross-checked against
        // the f64 port over 4.28M size combinations (0 divergences).

        // ---- one rule per group: sizes = [1, 1, 1, 1] ----
        let n1111: Vec<(NodeId, RuleACInst)> = vec![
            (nid(0), intr_node(destr(b"d"))),            // g0 (0,0)
            (nid(1), named_proto_node(PRN::Stand("R"))), // g1 (1,0)
            (
                nid(2),
                intr_node(IntrRuleACInfo::ConstrRule(
                    b"c".to_vec(),
                    tamarin_term::function_symbols::FunSym::List,
                )),
            ), // g2 (2,0)
            (nid(3), named_proto_node(PRN::Fresh)),      // g3 (3,0)
        ];
        let cm = build_node_color_map(&n1111);
        assert_eq!(hex_of(&cm, &n1111[0].1), "#ce90ac"); // (0,0)
        assert_eq!(hex_of(&cm, &n1111[1].1), "#d5d897"); // (1,0)
        assert_eq!(hex_of(&cm, &n1111[2].1), "#9ee1c3"); // (2,0)
        assert_eq!(hex_of(&cm, &n1111[3].1), "#a8a4eb"); // (3,0)

        // ---- sizes = [2, 1, 3, 1], member index tracks NodeId order ----
        let n2131: Vec<(NodeId, RuleACInst)> = vec![
            (nid(0), intr_node(destr(b"d1"))),           // g0 (0,0)
            (nid(1), intr_node(destr(b"d2"))),           // g0 (0,1)
            (nid(2), named_proto_node(PRN::Stand("R"))), // g1 (1,0)
            (
                nid(3),
                intr_node(IntrRuleACInfo::ConstrRule(
                    b"c1".to_vec(),
                    tamarin_term::function_symbols::FunSym::List,
                )),
            ), // g2 (2,0)
            (
                nid(4),
                intr_node(IntrRuleACInfo::ConstrRule(
                    b"c2".to_vec(),
                    tamarin_term::function_symbols::FunSym::List,
                )),
            ), // g2 (2,1)
            (nid(5), intr_node(IntrRuleACInfo::Coerce)), // g2 (2,2)
            (nid(6), named_proto_node(PRN::Fresh)),      // g3 (3,0)
        ];
        let cm = build_node_color_map(&n2131);
        assert_eq!(hex_of(&cm, &n2131[0].1), "#ce90ac"); // (0,0)
        assert_eq!(hex_of(&cm, &n2131[1].1), "#d19292"); // (0,1)
        assert_eq!(hex_of(&cm, &n2131[2].1), "#d5d897"); // (1,0)
        assert_eq!(hex_of(&cm, &n2131[3].1), "#9ee1c3"); // (2,0)
        assert_eq!(hex_of(&cm, &n2131[4].1), "#9fe3d9"); // (2,1)
        assert_eq!(hex_of(&cm, &n2131[5].1), "#a0dbe5"); // (2,2)
        assert_eq!(hex_of(&cm, &n2131[6].1), "#a8a4eb"); // (3,0)
    }

    #[test]
    fn node_color_map_sorts_by_nodeid_not_insertion_order() {
        // HS keys on `M.elems sNodes` = NodeId order, so member indices must
        // follow NodeId order even when nodes are inserted out of order. Insert
        // the second destr first; after the NodeId sort the (0,0)/(0,1) split
        // must still land by NodeId, matching the in-order [2,1,3,1] map.
        let shuffled: Vec<(NodeId, RuleACInst)> = vec![
            (nid(1), intr_node(destr(b"d2"))), // (0,1) after sort
            (nid(0), intr_node(destr(b"d1"))), // (0,0) after sort
        ];
        let cm = build_node_color_map(&shuffled);
        // d1 (nid 0) is member 0; d2 (nid 1) is member 1 — regardless of the
        // insertion order above.
        assert_eq!(hex_of(&cm, &shuffled[1].1), "#ce90ac"); // d1 -> (0,0)
        assert_eq!(hex_of(&cm, &shuffled[0].1), "#d19292"); // d2 -> (0,1)
    }

    #[test]
    fn node_color_map_last_wins_on_duplicate_rinfo() {
        // Two nodes sharing an identical rInfo collapse to one key; HS
        // `M.fromList` keeps the LAST, so both resolve to the (1,1) colour,
        // not (1,0). sizes = [0, 2, 0, 0]: (1,0)=#d5d897, (1,1)=#badb99.
        let dup: Vec<(NodeId, RuleACInst)> = vec![
            (nid(0), named_proto_node(PRN::Stand("R"))), // (1,0)
            (nid(1), named_proto_node(PRN::Stand("R"))), // (1,1) — same rInfo
        ];
        let cm = build_node_color_map(&dup);
        // Both look up the LAST member's colour.
        assert_eq!(hex_of(&cm, &dup[0].1), "#badb99");
        assert_eq!(hex_of(&cm, &dup[1].1), "#badb99");
    }

    /// A bare protocol-rule node (no facts) with the given name.
    fn named_proto_node(name: PRN) -> RuleACInst {
        TRule::new(
            TRuleInfo::Proto(ProtoRuleACInstInfo {
                name,
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    }
    fn nid(i: u64) -> NodeId {
        LVar::new("i", LSort::Node, i)
    }
}
