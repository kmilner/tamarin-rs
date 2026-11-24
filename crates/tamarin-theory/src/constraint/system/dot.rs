// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of HS `Theory.Constraint.System.Dot` (`dotSystemCompact`): render a
//! `System`'s graph (Graph.hs, GraphRepr.hs) as a Graphviz DOT document.
//!
//! This module holds the content layer — labels, colours (`nodeColorMap`,
//! `roleColor`), row filtering and ordering; `showdot` builds the `Text.Dot`
//! element tree and renders it through `showDot`. The batch `--output-dot`
//! writer renders at each trace's label, the web routes at `"G"`.
//!
//! HS `DotOptions`' `FullBoringNodes` (`uncompact`) is not ported: nodes
//! always render compact, the HS default.

use crate::constraint::system::{NodeRuleMap, System};
use crate::fact::{FactTag, LNFact};
use crate::pretty_hpj::{self, Doc, DEFAULT_LINE_LENGTH, DEFAULT_RIBBON};
use crate::rule::{
    prefix_if_reserved, rule_name_string, ProtoRuleName, Rule, RuleACInst, RuleInfo,
};
use tamarin_term::lterm::{LNTerm, LVar};

use crate::constraint::system::graph::abbreviation::{
    apply_abbreviations_fact, lookup_abbreviation, order_abbreviations_for_json, Abbreviations,
};
use crate::constraint::system::graph::color::{
    build_node_color_map, fact_doc_of, reason_color, NodeColorMap,
};
use crate::constraint::system::graph::options::GraphOptions;
use crate::constraint::system::graph::repr::{
    extract_base_name, extract_role, GEdge, GNode, MissingHint, NodeType,
};
use crate::constraint::system::graph::{
    resolve_node_conc_fact, resolve_node_prem_fact, system_to_graph, Graph,
};

// ---------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------

/// Render a [`System`] into a Graphviz DOT document under the given
/// options — the interactive graph routes' entry point.
///
/// HS `dotGraphString` (`Web/Theory.hs`), which backs
/// `getTheoryInteractiveGraphR` (`Handler.hs`), serialises the same
/// `dotSystemCompact graphOptions dotOptions system` the batch `--output-dot`
/// writer does (`Batch.hs`) through `D.showDot`, at the fixed label `"G"`.
/// So this is [`system_to_dot_labeled`] at that label.  `getTheoryGraphR`
/// (`Handler.hs`) reaches the same call through `imgThyPath`, whose
/// `prefixedShowDot` (`Web/Theory.hs`) prepends two `//` comment
/// lines before handing the file to graphviz — comments graphviz discards, so
/// the SVG that route answers with is this document's.
pub fn system_to_dot_with(sys: &System, opts: &GraphOptions) -> String {
    system_to_dot_labeled(sys, opts, "G")
}

fn abbreviate_rule(ru: &RuleACInst, abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>) -> RuleACInst {
    let map_facts = |facts: &[LNFact]| {
        facts
            .iter()
            .map(|fact| apply_abbreviations_fact(abbrev, fact))
            .collect()
    };
    Rule {
        info: ru.info.clone(),
        premises: map_facts(&ru.premises),
        conclusions: map_facts(&ru.conclusions),
        actions: map_facts(&ru.actions),
        new_vars: ru.new_vars.clone(),
    }
}

/// The `<TABLE …>` opening tag `abbrevLabel`'s `tableAttributes`
/// (`[Border 1, CellBorder 0, CellSpacing 3, CellPadding 1]`, System/Dot.hs)
/// print as.  Both legend serializers open with it; in the batch one its
/// WIDTH is additionally the continuation indent of the rows below.
const LEGEND_TABLE_OPEN: &str =
    "<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"3\" CELLPADDING=\"1\">";

/// Haskell `round :: Double -> Int` — IEEE round-half-to-EVEN (banker's
/// rounding), unlike Rust's `f64::round` (half-away-from-zero).  The
/// balanced widths (`conv = max 30 . round . (*1.3)`), the ribbon
/// (`round (w / 1.5)` in `fullRender`) and `scaleIndent`'s space count all
/// go through HS `round`, and half cases DO occur (e.g. `130/1.5 =
/// 86.66→87`, `1.5*23 = 34.5→34`).
fn round_half_even(x: f64) -> i64 {
    let f = x.floor();
    let diff = x - f;
    if diff > 0.5 {
        f as i64 + 1
    } else if diff < 0.5 {
        f as i64
    } else {
        let fi = f as i64;
        if fi % 2 == 0 {
            fi
        } else {
            fi + 1
        }
    }
}

/// HS `renderBalanced 100 (max 30 . round . (*1.3))` + `scaleIndent`
/// (System/Dot.hs), the layout engine for record-row fields: each doc of
/// a row is rendered at a line length PROPORTIONAL to its one-line length
/// (`renderStyle (defaultStyle { lineLength = w })`, i.e. PageMode with
/// ribbon `round (w / 1.5)`), so a lone fact in a row gets width
/// `max 30 (round 130) = 130` (ribbon 87) while four facts share the
/// 100-column budget.  `usedWidths` measure the OneLineMode render
/// (`Doc::one_line_render`), which turns every fill/sep break point into
/// one space.
///
/// `scaleIndent` is applied to the WHOLE rendered string (HS's `line`
/// binding spans the full render): `span isSpace` therefore only rescales
/// whitespace at the very START of the FIRST line — a no-op for every
/// label whose first char is text, exactly as in HS.
fn render_balanced(docs: Vec<Doc>) -> Vec<String> {
    if docs.is_empty() {
        return Vec::new();
    }
    let used: Vec<f64> = docs
        .iter()
        .map(|d| d.one_line_render().chars().count() as f64)
        .collect();
    let total: f64 = used.iter().sum();
    let ratio = 100.0 / total;
    docs.into_iter()
        .zip(used)
        .map(|(d, u)| {
            // conv (ratio * w) with conv = max 30 . round . (*1.3).
            let w = std::cmp::max(30, round_half_even((ratio * u) * 1.3));
            // `renderStyle (defaultStyle { lineLength = w })` keeps
            // ribbonsPerLine = 1.5 → ribbon = round (w / 1.5)
            // (pretty-1.1.3.6 `fullRender`).
            let ribbon = round_half_even(w as f64 / 1.5);
            scale_indent(d.render_with(w as usize, ribbon as usize))
        })
        .collect()
}

/// HS `scaleIndent` (System/Dot.hs) — see `render_balanced`.
fn scale_indent(s: String) -> String {
    let leading = s.chars().take_while(|c| c.is_whitespace()).count();
    if leading == 0 {
        return s;
    }
    let rest: String = s.chars().skip(leading).collect();
    let n = round_half_even(1.5 * leading as f64);
    let mut out = String::with_capacity(n as usize + rest.len());
    for _ in 0..n {
        out.push(' ');
    }
    out.push_str(&rest);
    out
}

/// Mirror Haskell `ruleLabelM.isNotDiffAnnotation` (System/Dot.hs): the action
/// fact equal to the synthetic diff annotation
/// `Fact (ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0) S.empty []`
/// is dropped before rendering. `getRuleNameDiff` (Theory/Model/Rule.hs) prefixes
/// the rule's `getRuleName` with `"Intr"`/`"Proto"` depending on the rule
/// kind. Returns `true` when the fact should be KEPT.
fn diff_annotation_name(ru: &RuleACInst) -> String {
    match &ru.info {
        RuleInfo::Intr(_) => format!("DiffIntr{}", rule_name_string(ru)),
        RuleInfo::Proto(_) => format!("DiffProto{}", rule_name_string(ru)),
    }
}

fn is_not_diff_annotation(diff_fact_name: &str, fa: &LNFact) -> bool {
    let is_diff = matches!(&fa.tag,
        FactTag::Proto(crate::fact::Multiplicity::Linear, n, 0)
            if **n == *diff_fact_name)
        && fa.terms.is_empty();
    !is_diff
}

/// Mirror Haskell `ruleLabelM.isAutoSource`/`hasAutoLabel` (System/Dot.hs):
/// a fact whose `showFactTag` begins with one of the auto-source label
/// prefixes is an auto-source fact. These labels are linear proto facts, so
/// `showFactTag` reduces to the bare proto name here (no `!` prefix), which
/// `fact_tag_name` returns.
fn is_auto_source(fa: &LNFact) -> bool {
    use crate::fact::fact_tag_name;
    let name = fact_tag_name(&fa.tag);
    name.starts_with("AUTO_IN_TERM_")
        || name.starts_with("AUTO_IN_FACT_")
        || name.starts_with("AUTO_OUT_TERM_")
        || name.starts_with("AUTO_OUT_FACT_")
}

/// HS `isIntruderRule ru || isFreshRule ru` (Theory/Model/Rule.hs): the
/// predicate gating `mkNode`'s `CompactBoringNodes` branch (System/Dot.hs).
/// True for any intruder rule and for the reserved proto `Fresh` rule.
fn is_intruder_or_fresh(ru: &RuleACInst) -> bool {
    match &ru.info {
        RuleInfo::Intr(_) => true,
        RuleInfo::Proto(p) => p.name == ProtoRuleName::Fresh,
    }
}

/// Build the rule-node label Doc — HS `ruleLabelM` (System/Dot.hs):
/// `prettyNodeId v <-> colon <-> text (showDotRuleCaseName ru) <> (if null lbl
/// then mempty else brackets (vcat (punctuate comma lbl)))`. `<->` is
/// space-separated (`#i : name`) but the action bracket is joined with `<>`
/// (NO space before `[`), and the actions stack VERTICALLY (`vcat`,
/// comma-punctuated) when there are several. Actions are filtered exactly
/// as HS (`is_not_diff_annotation`; drop `AUTO_*` only when
/// `goShowAutoSource`).  The caller lays this Doc out via
/// `render_balanced` (HS `asM = renderRow [(Nothing, ruleLabel)]`,
/// System/Dot.hs — a single-doc row, i.e. width 130 / ribbon 87).
fn rule_label_doc(nid: &LVar, ru: &RuleACInst, opts: &GraphOptions) -> Doc {
    let diff_fact_name = diff_annotation_name(ru);
    let act_docs: Vec<Doc> = ru
        .actions
        .iter()
        .filter(|fa| is_not_diff_annotation(&diff_fact_name, fa))
        .filter(|fa| !opts.show_auto_source || !is_auto_source(fa))
        .map(fact_doc_of)
        .collect();
    // `prettyNodeId v <-> colon <-> text name` — three same-line text
    // tokens joined by single spaces; layout-equivalent to one fused text
    // run of the same width (no break points inside a `<>`/`<+>` chain).
    let header = Doc::text(format!("{} : {}", nid, rule_case_name(ru)));
    if act_docs.is_empty() {
        header
    } else {
        // `brackets (vcat $ punctuate comma lbl)` (System/Dot.hs).
        header
            .beside(Doc::text("["))
            .beside(pretty_hpj::vcat(pretty_hpj::punctuate(
                Doc::text(","),
                act_docs,
            )))
            .beside(Doc::text("]"))
    }
}

/// Mirror Haskell's `showDotRuleCaseName` for `RuleACInst`
/// (Theory/Model/Rule.hs via `prettyDotProtoRuleName`,
/// Theory/Model/Rule.hs).
fn rule_case_name(ru: &RuleACInst) -> String {
    match &ru.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => {
                if p.attributes.is_sapic_rule {
                    if s.starts_with("new") {
                        // chr 957 (ν) : ' ' : drop 3 (trimSapicName s)
                        let trimmed = trim_sapic_name(s);
                        let dropped: String = trimmed.chars().skip(3).collect();
                        format!("\u{3bd} {}", dropped)
                    } else {
                        trim_sapic_name(s)
                    }
                } else {
                    prefix_if_reserved(s)
                }
            }
            ProtoRuleName::Fresh => "Fresh".to_string(),
        },
        // `prettyIntrRuleACInfo`, shared with the intruder-variants printer.
        RuleInfo::Intr(i) => crate::pretty_formula::intr_rule_name(i),
    }
}

/// Mirror Haskell `trimSapicName` (Theory/Model/Rule.hs): strips a
/// trailing `_<digits>_<digits>` suffix from a SAPiC rule name.
fn trim_sapic_name(name: &str) -> String {
    if let Some((prefix, m)) = name.rsplit_once('_')
        && let Some((base, n)) = prefix.rsplit_once('_')
    {
        // Haskell `all isDigit s` is True for the empty string too.
        let all_digits = |s: &str| s.chars().all(|c| c.is_ascii_digit());
        if all_digits(n) && all_digits(m) {
            return base.to_string();
        }
    }
    name.to_string()
}

/// HS `ruleColor'` (System/Dot.hs): `rgbToHex` of the proto rule's explicit
/// `color:` attribute, if any. `None` for intruder rules / no attribute.
fn explicit_rule_color(ru: &RuleACInst) -> Option<String> {
    if let RuleInfo::Proto(p) = &ru.info
        && let Some(rgb) = p.attributes.color
    {
        return Some(tamarin_utils::color::rgb_to_hex(rgb));
    }
    None
}

/// Pick a rule node's fill colour with HS `dotNodeCompact`'s priority
/// (System/Dot.hs): `fromMaybe (maybe "white" rgbToHex color)
/// (ruleColor' <|> manualNodeColor)` — the explicit `color:` attribute wins,
/// then the cluster's `manualNodeColor`, then the `nodeColorMap` palette
/// fallback (`maybe "white" rgbToHex (M.lookup rInfo colorMap)`): a node
/// present in the map yields its palette hex, an absent one yields `"white"`.
fn rule_fillcolor(
    ru: &RuleACInst,
    nid: &LVar,
    manual_color: Option<&str>,
    color_map: &NodeColorMap,
) -> String {
    explicit_rule_color(ru)
        .or_else(|| manual_color.map(|c| c.to_string()))
        .unwrap_or_else(|| match color_map.lookup_node(nid) {
            Some(rgb) => tamarin_utils::color::rgb_to_hex(rgb),
            None => "white".to_string(),
        })
}

/// HS `dotNodeCompact.colorUsesWhiteFont` (System/Dot.hs): a node uses a white
/// font iff it HAS a palette colour and that colour is "dark" in apparent
/// (linear) luminance, `0.2126 r + 0.7152 g + 0.0722 b < 0.5`. An absent colour
/// (`None`) ⇒ black font. Keyed off the palette colour (`M.lookup rInfo
/// colorMap`), not the resolved fill.
fn color_uses_white_font(color: Option<tamarin_utils::color::Rgb>) -> bool {
    match color {
        Some(c) => 0.2126 * c.r + 0.7152 * c.g + 0.0722 * c.b < 0.5,
        None => false,
    }
}

/// Which arm of `dotEdge`'s `SystemEdge` guard chain (System/Dot.hs) an edge
/// falls into.  The classification is decided here; its sole consumer,
/// `dot_showdot`, spells the resulting attributes (`json.rs` carries its own
/// `EdgeClass` for the JSON edge palette).
enum EdgeKind {
    /// `check isProtoFact`; `persistent` is the nested `check isPersistentFact`
    /// that adds `color=gray50`.
    Proto { persistent: bool },
    /// `check isKFact`.
    K,
    /// The fallthrough.
    Other,
}

/// `dotEdge`'s `SystemEdge` guard chain (System/Dot.hs), split out so the
/// classification is decided here and spelled as attributes by the serializer.
fn classify_edge(
    orig_node_map: &NodeRuleMap<'_>,
    src: &crate::constraint::constraints::NodeConc,
    tgt: &crate::constraint::constraints::NodePrem,
) -> EdgeKind {
    // Look up tag of the source-conclusion or target-premise.
    let conc_tag = resolve_node_conc_fact(src, orig_node_map).map(|fa| fa.tag);
    let prem_tag = resolve_node_prem_fact(tgt, orig_node_map).map(|fa| fa.tag);
    let is_proto = |t: Option<&FactTag>| -> bool { matches!(t, Some(FactTag::Proto(_, _, _))) };
    // HS `isPersistentFact` (Theory/Model/Fact.hs) reads the tag's
    // multiplicity, and HS `factTagMultiplicity` (Theory/Model/Fact.hs)
    // makes `KUFact`/`KDFact`
    // persistent alongside `ProtoFact Persistent _ _`.  Only the proto arm can
    // fire below: the branch is gated on `check isProtoFact`, and both endpoints
    // of an `Edge` carry the same tag because HS `insertEdges`
    // (Reduction.hs) unifies the two facts through `solveFactEqs`, whose
    // first act is `contradictoryIf` on unequal tags (Reduction.hs).
    let is_persistent = |t: Option<&FactTag>| -> bool {
        t.is_some_and(|tag| {
            crate::fact::fact_tag_multiplicity(tag) == crate::fact::Multiplicity::Persistent
        })
    };
    let is_k = |t: Option<&FactTag>| -> bool { matches!(t, Some(FactTag::Ku) | Some(FactTag::Kd)) };
    if is_proto(conc_tag.as_ref()) || is_proto(prem_tag.as_ref()) {
        EdgeKind::Proto {
            persistent: is_persistent(conc_tag.as_ref()) || is_persistent(prem_tag.as_ref()),
        }
    } else if is_k(conc_tag.as_ref()) || is_k(prem_tag.as_ref()) {
        EdgeKind::K
    } else {
        EdgeKind::Other
    }
}

/// Port of Haskell `roleColor` (System/Dot.hs): a deterministic per-role
/// `#RRGGBBAA` colour. `simpleHash name = foldl (\acc c -> acc*31 + ord c) 7`
/// (System/Dot.hs) over the role's base name (Haskell `Int`, i.e. 64-bit
/// two's-complement wrapping), `generateValue = (hash `mod` 360) / 360`
/// (System/Dot.hs; Haskell `mod` is non-negative for a positive divisor —
/// `rem_euclid` here), then
/// `hsvToRGB (HSV (v*360) 0.75 0.85)` with each channel `floor(f*255)` and a
/// fixed alpha `floor(255*0.3) = 76`. Hex digits are UPPERCASE (`%02X`), and
/// the channel scale is `*255` (not `*256` as in `rgb_to_hex`), so this does
/// not reuse `rgb_to_hex`.
fn role_color(name: &str) -> String {
    // simpleHash: `Int` arithmetic, wraps on overflow.
    let hash: i64 = name
        .chars()
        .fold(7i64, |acc, c| acc.wrapping_mul(31).wrapping_add(c as i64));
    let v = (hash.rem_euclid(360)) as f64 / 360.0;
    let rgb =
        tamarin_utils::color::hsv_to_rgb(tamarin_utils::color::Hsv::new(v * 360.0, 0.75, 0.85));
    let chan = |f: f64| -> i64 { (f * 255.0).floor() as i64 };
    let alpha: i64 = (255.0 * 0.3_f64).floor() as i64; // = 76
    format!(
        "#{:02X}{:02X}{:02X}{:02X}",
        chan(rgb.r),
        chan(rgb.g),
        chan(rgb.b),
        alpha
    )
}

#[path = "dot_showdot.rs"]
mod showdot;
pub use showdot::system_to_dot_labeled;

#[cfg(test)]
#[path = "dot_tests.rs"]
mod tests;
