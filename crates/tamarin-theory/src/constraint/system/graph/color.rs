// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Per-rule node colouring shared by the two graph renderers.
//!
//! Holds the port of HS `nodeColorMap` / `NodeColorMap` (Dot.hs:88,
//! Dot.hs:190-218) — the size-dependent light-HSV palette keyed by a rule's
//! `rInfo` — together with the less-edge `reasonColor` table and the
//! `prettyLNFact` `Doc` both renderers label facts with.
//! [`crate::constraint::system::dot`] (DOT output) and
//! [`crate::constraint::system::json`] (JSON output) are both consumers, so
//! this module sits under `graph/` rather than inside either renderer.

use std::collections::BTreeMap;

use crate::constraint::constraints::{NodeId, Reason};
use crate::constraint::system::nodes_in_map_order;
use crate::fact::LNFact;
use crate::pretty_hpj::Doc;
use crate::rule::{IntrRuleACInfo, ProtoRuleName, RuleACInst, RuleInfo};

/// The `Doc` of an `LNFact` exactly as Haskell `prettyLNFact`
/// (Fact.hs:581-582), the printer `renderLNFact` (Dot.hs:227-233) feeds
/// after abbreviation replacement.  `prettyLNFact` builds the
/// argument list with `nestShort' (n++"(") ")" . fsep . punctuate comma`
/// (`prettyFact`'s `ppFact`, Fact.hs:567-574, see line 572), which — unlike a bare `name(a, b)` — emits the
/// HughesPJ INNER-PAREN SPACES `!KU( ~ltk )` when the fact fits on one line.
/// We therefore reuse the *same* faithful `Doc` path the proof pretty-
/// printer uses for goals (`solve_goal_to_doc` → `pretty_formula::fact_doc`
/// on the parser-AST projection), NOT `pretty_system::pretty_fact` (which
/// omits those spaces).
pub(crate) fn fact_doc_of(fa: &LNFact) -> Doc {
    crate::pretty_formula::fact_doc(&crate::pretty_theory::lnfact_to_parser(fa))
}

/// HS `toColor` — the per-`Reason` less-edge colour, spelled identically in
/// the DOT renderer (`dotLessAtom.toColor`, Dot.hs:624-630) and in the JSON
/// serialiser (`colorEdge`'s `LessEdge` arm, JSON.hs:444-455, see line 455).
pub(crate) fn reason_color(r: Reason) -> &'static str {
    match r {
        Reason::Adversary => "red",
        Reason::Formula => "black",
        Reason::Fresh => "blue3",
        Reason::InjectiveFacts => "purple",
        Reason::NormalForm => "darkorange3",
    }
}

/// Key of HS `NodeColorMap` (Dot.hs:91): a rule's `rInfo`
/// (`RuleInfo ProtoRuleACInstInfo IntrRuleACInfo`).
pub(crate) type RInfo = RuleInfo<crate::rule::ProtoRuleACInstInfo, IntrRuleACInfo>;

/// Faithful port of HS `NodeColorMap` (Dot.hs:91) — the per-rule fill
/// palette, keyed in HS by a rule's `rInfo`. Built by [`build_node_color_map`]
/// (port of `nodeColorMap`, Dot.hs:190-218).
///
/// `rInfo` is not `Hash`/`Ord` in the Rust port (`ProtoRuleACInstInfo` only
/// derives `PartialEq`), and both renderers reach the palette from a node whose
/// `NodeId` they already hold, so the map is stored keyed by `NodeId`: each
/// entry is the colour that node's `rInfo` RESOLVES to under HS `M.fromList`,
/// which keeps the LAST value for equal keys — so two nodes sharing an `rInfo`
/// both carry the later entry's colour. The collapse is done once in
/// [`build_node_color_map`], leaving [`lookup_node`] free of `rInfo` equality.
///
/// [`lookup_node`]: NodeColorMap::lookup_node
pub(crate) struct NodeColorMap {
    by_node: BTreeMap<NodeId, tamarin_utils::color::Rgb>,
}

impl NodeColorMap {
    /// HS `M.lookup rInfoVal colorMap` (Dot.hs:236-379, see line 255) for the
    /// node that `id` names: the colour of the LAST map entry sharing that
    /// node's `rInfo` (matching `M.fromList`'s last-wins), or `None` when the
    /// node contributed no entry (→ `"white"` in the DOT renderer, an omitted
    /// `jgnColor` in the JSON one).
    pub(crate) fn lookup_node(&self, id: &NodeId) -> Option<tamarin_utils::color::Rgb> {
        self.by_node.get(id).copied()
    }
}

/// Bucketing key for the `M.fromList` collapse in [`build_node_color_map`]: a
/// cheap `Ord` projection of an [`RInfo`] that any two EQUAL `rInfo`s share, so
/// the structural `rInfo` comparison only ever runs between nodes in the same
/// bucket. The protocol arm stops at the rule name because
/// `ProtoRuleACInstInfo`'s `attributes` carry an `Option<PlainProcess>` — a
/// whole SAPIC process tree — that comparing is far from free.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum ClassKey<'a> {
    Proto(ProtoRuleName),
    Intr(&'a IntrRuleACInfo),
}

fn class_key(info: &RInfo) -> ClassKey<'_> {
    match info {
        RuleInfo::Proto(p) => ClassKey::Proto(p.name),
        RuleInfo::Intr(i) => ClassKey::Intr(i),
    }
}

/// HS `nodeColorMap.groupIdx` (Dot.hs:196-200): partition a rule into one of
/// four colour groups. Guard order matters and mirrors HS exactly:
///   * `isDestrRule` (DestrRule or IEqualityRule)               → 0
///   * `isConstrRule` (Constr/Fresh/Pub/Nat constr or Coerce)   → 2
///   * `isFreshRule` (proto `Fresh`) or `isISendRule`           → 3
///   * otherwise (protocol rules, IRecv, …)                     → 1
fn group_idx(ru: &RuleACInst) -> usize {
    use crate::rule::{
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
/// `rules` here is `M.elems $ get sNodes se` (Dot.hs:506-512, see line 510) — the raw system's
/// nodes in `M.Map` key order, materialised by [`nodes_in_map_order`].
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
pub(crate) fn build_node_color_map(nodes: &[(NodeId, RuleACInst)]) -> NodeColorMap {
    use tamarin_utils::color::{hsv_to_rgb, light_color_groups, Hsv, Rgb};

    let ordered = nodes_in_map_order(nodes);

    // `groups = [ (gIdx, [ru | ru <- rules, gIdx == groupIdx ru]) | gIdx <- 0..3 ]`
    // — order-preserving partition into four groups.
    let mut groups: [Vec<&(NodeId, RuleACInst)>; 4] =
        [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
    for pair in &ordered {
        groups[group_idx(&pair.1)].push(pair);
    }
    let sizes: [usize; 4] = std::array::from_fn(|i| groups[i].len());

    // `colors = M.fromList $ lightColorGroups intruderHue (map (length . snd)
    // groups)`, `intruderHue = 18 % 360`. The palette is exact `Rational` in
    // HS; the f64 port matches `rgbToHex`'s `floor(256*f)` quantisation for all
    // realistic group sizes (verified: 0/4.28M hex divergences).
    const INTRUDER_HUE: f64 = 18.0 / 360.0;
    let palette: BTreeMap<(usize, usize), Hsv> = light_color_groups(INTRUDER_HUE, &sizes)
        .into_iter()
        .collect();
    let get_color = |gi: usize, mi: usize| -> Hsv {
        // `getColor idx = fromMaybe (HSV 0 1 1) (M.lookup idx colors)`
        // (Dot.hs:190-218, see line 209) — unreachable for a valid (gIdx, mIdx).
        palette
            .get(&(gi, mi))
            .copied()
            .unwrap_or_else(|| Hsv::new(0.0, 1.0, 1.0))
    };

    // The list HS hands to `M.fromList`, walked in its own order (group-major,
    // NodeId-ordered within a group).  Equal `rInfo`s collapse to ONE key whose
    // value is the LAST entry's colour, so every entry is filed into an
    // equivalence class of `rInfo`s (`class_info`) whose colour (`class_color`)
    // the later entries overwrite.  `classes` buckets those classes by
    // `class_key`, confining `rInfo` equality to same-key entries.
    let mut classes: BTreeMap<ClassKey<'_>, Vec<usize>> = BTreeMap::new();
    let mut class_info: Vec<&RInfo> = Vec::new();
    let mut class_color: Vec<Rgb> = Vec::new();
    let mut node_class: Vec<(NodeId, usize)> = Vec::with_capacity(ordered.len());
    for (gi, grp) in groups.iter().enumerate() {
        for (mi, pair) in grp.iter().enumerate() {
            let info = &pair.1.info;
            // `getColorForRule attrs gIdx mIdx = fromMaybe defaultColor
            // (ruleColor attrs)` (Dot.hs:190-218, see line 212): explicit `color:` wins, else the
            // palette default.  `ruleAttributes ru = praciAttributes` for a
            // RuleACInst (Rule.hs:673-675, see line 674) — the same attributes `explicit_rule_color`
            // reads, so a coloured rule maps to its own dark fill colour.
            let color = match info {
                RuleInfo::Proto(p) => p
                    .attributes
                    .color
                    .unwrap_or_else(|| hsv_to_rgb(get_color(gi, mi))),
                _ => hsv_to_rgb(get_color(gi, mi)),
            };
            let bucket = classes.entry(class_key(info)).or_default();
            let ci = match bucket.iter().copied().find(|&ci| *class_info[ci] == *info) {
                Some(ci) => {
                    class_color[ci] = color;
                    ci
                }
                None => {
                    class_info.push(info);
                    class_color.push(color);
                    bucket.push(class_info.len() - 1);
                    class_info.len() - 1
                }
            };
            node_class.push((pair.0, ci));
        }
    }
    // Every node takes its class's FINAL colour — the value `M.lookup
    // rInfoVal colorMap` would return for it.
    let by_node = node_class
        .into_iter()
        .map(|(id, ci)| (id, class_color[ci]))
        .collect();
    NodeColorMap { by_node }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName as PRN, Rule as TRule, RuleAttributes,
        RuleInfo as TRuleInfo,
    };
    use tamarin_term::lterm::{LSort, LVar};

    /// A bare intruder-rule node (no facts) with the given `IntrRuleACInfo`.
    fn intr_node(info: IntrRuleACInfo) -> RuleACInst {
        TRule::new(TRuleInfo::Intr(info), Vec::new(), Vec::new(), Vec::new())
    }
    fn destr(n: &[u8]) -> IntrRuleACInfo {
        IntrRuleACInfo::DestrRule {
            name: n.to_vec(),
            remaining_applications: 0,
            rhs_is_proper_subterm: false,
            rhs_is_constant: false,
            funs: vec![],
        }
    }
    fn hex_of(cm: &NodeColorMap, id: NodeId) -> String {
        tamarin_utils::color::rgb_to_hex(cm.lookup_node(&id).unwrap())
    }

    /// Direct transcription of HS `M.lookup rInfoVal (nodeColorMap rules)`
    /// (Dot.hs:190-218/255): rebuild the association list HS hands to
    /// `M.fromList` and scan it in reverse for the last entry with an equal
    /// `rInfo` — the semantics [`build_node_color_map`] resolves per node.
    fn reference_lookup(
        nodes: &[(NodeId, RuleACInst)],
        info: &RInfo,
    ) -> Option<tamarin_utils::color::Rgb> {
        use tamarin_utils::color::{hsv_to_rgb, light_color_groups, Hsv, Rgb};
        let mut ordered: Vec<&(NodeId, RuleACInst)> = nodes.iter().collect();
        ordered.sort_by_key(|a| a.0);
        let mut groups: [Vec<&RuleACInst>; 4] = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
        for pair in &ordered {
            groups[group_idx(&pair.1)].push(&pair.1);
        }
        let sizes: [usize; 4] = [
            groups[0].len(),
            groups[1].len(),
            groups[2].len(),
            groups[3].len(),
        ];
        let palette: BTreeMap<(usize, usize), Hsv> = light_color_groups(18.0 / 360.0, &sizes)
            .into_iter()
            .collect();
        let mut entries: Vec<(&RInfo, Rgb)> = Vec::new();
        for (gi, grp) in groups.iter().enumerate() {
            for (mi, ru) in grp.iter().enumerate() {
                let default = hsv_to_rgb(palette[&(gi, mi)]);
                let color = match &ru.info {
                    RuleInfo::Proto(p) => p.attributes.color.unwrap_or(default),
                    _ => default,
                };
                entries.push((&ru.info, color));
            }
        }
        entries
            .iter()
            .rev()
            .find(|(k, _)| **k == *info)
            .map(|(_, c)| *c)
    }

    #[test]
    fn group_idx_partition_matches_hs() {
        // HS groupIdx (Dot.hs:196-200).
        assert_eq!(group_idx(&intr_node(destr(b"x"))), 0); // isDestrRule
        assert_eq!(group_idx(&intr_node(IntrRuleACInfo::IEquality)), 0);
        assert_eq!(
            group_idx(&intr_node(IntrRuleACInfo::ConstrRule {
                name: b"c".to_vec(),
                fun: tamarin_term::function_symbols::FunSym::List
            })),
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
                intr_node(IntrRuleACInfo::ConstrRule {
                    name: b"c".to_vec(),
                    fun: tamarin_term::function_symbols::FunSym::List,
                }),
            ), // g2 (2,0)
            (nid(3), named_proto_node(PRN::Fresh)),      // g3 (3,0)
        ];
        let cm = build_node_color_map(&n1111);
        assert_eq!(hex_of(&cm, nid(0)), "#ce90ac"); // (0,0)
        assert_eq!(hex_of(&cm, nid(1)), "#d5d897"); // (1,0)
        assert_eq!(hex_of(&cm, nid(2)), "#9ee1c3"); // (2,0)
        assert_eq!(hex_of(&cm, nid(3)), "#a8a4eb"); // (3,0)

        // ---- sizes = [2, 1, 3, 1], member index tracks NodeId order ----
        let n2131: Vec<(NodeId, RuleACInst)> = vec![
            (nid(0), intr_node(destr(b"d1"))),           // g0 (0,0)
            (nid(1), intr_node(destr(b"d2"))),           // g0 (0,1)
            (nid(2), named_proto_node(PRN::Stand("R"))), // g1 (1,0)
            (
                nid(3),
                intr_node(IntrRuleACInfo::ConstrRule {
                    name: b"c1".to_vec(),
                    fun: tamarin_term::function_symbols::FunSym::List,
                }),
            ), // g2 (2,0)
            (
                nid(4),
                intr_node(IntrRuleACInfo::ConstrRule {
                    name: b"c2".to_vec(),
                    fun: tamarin_term::function_symbols::FunSym::List,
                }),
            ), // g2 (2,1)
            (nid(5), intr_node(IntrRuleACInfo::Coerce)), // g2 (2,2)
            (nid(6), named_proto_node(PRN::Fresh)),      // g3 (3,0)
        ];
        let cm = build_node_color_map(&n2131);
        assert_eq!(hex_of(&cm, nid(0)), "#ce90ac"); // (0,0)
        assert_eq!(hex_of(&cm, nid(1)), "#d19292"); // (0,1)
        assert_eq!(hex_of(&cm, nid(2)), "#d5d897"); // (1,0)
        assert_eq!(hex_of(&cm, nid(3)), "#9ee1c3"); // (2,0)
        assert_eq!(hex_of(&cm, nid(4)), "#9fe3d9"); // (2,1)
        assert_eq!(hex_of(&cm, nid(5)), "#a0dbe5"); // (2,2)
        assert_eq!(hex_of(&cm, nid(6)), "#a8a4eb"); // (3,0)
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
        assert_eq!(hex_of(&cm, nid(0)), "#ce90ac"); // d1 -> (0,0)
        assert_eq!(hex_of(&cm, nid(1)), "#d19292"); // d2 -> (0,1)
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
        assert_eq!(hex_of(&cm, nid(0)), "#badb99");
        assert_eq!(hex_of(&cm, nid(1)), "#badb99");
    }

    #[test]
    fn node_color_map_separates_same_named_rules_with_distinct_rinfo() {
        // Same `ProtoRuleName` — hence the same `class_key` bucket — but
        // unequal `rInfo`s (one carries a `role:` attribute), so `M.fromList`
        // keeps TWO keys and only the two equal ones collapse.
        // sizes = [0, 3, 0, 0]: (1,0)=#d5d897, (1,1)=#c3da98, (1,2)=#b1dc9a.
        let mut roled = named_proto_node(PRN::Stand("R"));
        if let TRuleInfo::Proto(p) = &mut roled.info {
            p.attributes.role = Some("A".to_string());
        }
        let mixed: Vec<(NodeId, RuleACInst)> = vec![
            (nid(0), named_proto_node(PRN::Stand("R"))), // (1,0)
            (nid(1), roled),                             // (1,1) — distinct rInfo
            (nid(2), named_proto_node(PRN::Stand("R"))), // (1,2) — equal to nid 0
        ];
        let cm = build_node_color_map(&mixed);
        // nid 0 collapses onto the LAST attribute-free "R" entry, nid 2.
        assert_eq!(hex_of(&cm, nid(0)), "#b1dc9a");
        assert_eq!(hex_of(&cm, nid(1)), "#c3da98");
        assert_eq!(hex_of(&cm, nid(2)), "#b1dc9a");
    }

    #[test]
    fn lookup_node_matches_rinfo_keyed_reverse_scan() {
        // Every node's stored colour is the one its `rInfo` resolves to under
        // `M.fromList`. The node set mixes both `rInfo` arms, duplicated
        // `rInfo`s, same-name-but-unequal `rInfo`s, and an explicit `color:`.
        let mut roled = named_proto_node(PRN::Stand("R"));
        if let TRuleInfo::Proto(p) = &mut roled.info {
            p.attributes.role = Some("A".to_string());
        }
        let mut painted = named_proto_node(PRN::Stand("P"));
        if let TRuleInfo::Proto(p) = &mut painted.info {
            p.attributes.color = Some(tamarin_utils::color::Rgb::new(0.1, 0.2, 0.3));
        }
        let nodes: Vec<(NodeId, RuleACInst)> = vec![
            (nid(0), named_proto_node(PRN::Stand("R"))),
            (nid(1), intr_node(destr(b"d1"))),
            (nid(2), roled),
            (nid(3), intr_node(destr(b"d1"))),
            (nid(4), painted.clone()),
            (nid(5), named_proto_node(PRN::Stand("R"))),
            (nid(6), intr_node(IntrRuleACInfo::ISend)),
            (nid(7), named_proto_node(PRN::Fresh)),
            (nid(8), painted),
            (nid(9), intr_node(IntrRuleACInfo::Coerce)),
        ];
        let cm = build_node_color_map(&nodes);
        for (id, ru) in &nodes {
            assert_eq!(
                cm.lookup_node(id),
                reference_lookup(&nodes, &ru.info),
                "node {}",
                id
            );
        }
    }

    #[test]
    fn node_color_map_lookup_node_absent_is_none() {
        // A node id that contributed no entry has no colour — HS `M.lookup`
        // returning `Nothing`, which the renderers turn into `"white"` / an
        // omitted `jgnColor`.
        let one: Vec<(NodeId, RuleACInst)> = vec![(nid(0), named_proto_node(PRN::Stand("R")))];
        let cm = build_node_color_map(&one);
        assert!(cm.lookup_node(&nid(0)).is_some());
        assert!(cm.lookup_node(&nid(7)).is_none());
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
