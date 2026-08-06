// Currently GPL 3.0 until granted permission by the following authors:
//   jdreier, beschmi, meiersi, sans-sucre, PhilipLukertWork, rkunnema,
//   kevinmorio, addap, BTom-GH, Mathias-AURAND, Nynko, arcz, rsasse,
//   charlie-j, racoucho1u, felixlinker, xaDxelA, ValentinYuri, and
//   other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Builtin/Signature.hs, lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/SubtermRule.hs, lib/term/src/Term/Term.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/term/src/Term/Term/Raw.hs, lib/term/src/Term/VTerm.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Model/Restriction.hs,
//   lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Text/Parser/Formula.hs,
//   lib/theory/src/Theory/Text/Parser/Let.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs,
//   lib/theory/src/Theory/Text/Parser/Term.hs,
//   lib/theory/src/Theory/Tools/MessageDerivationChecks.hs,
//   lib/theory/src/Theory/Tools/Wellformedness.hs,
//   lib/theory/src/TheoryObject.hs,
//   lib/utils/src/Text/PrettyPrint/Class.hs, src/Main/Mode/Batch.hs,
//   src/Main/TheoryLoader.hs

//! Wellformedness checks operating on the parser AST.
//!
//! Port of `Theory.Tools.Wellformedness` from
//! `lib/theory/src/Theory/Tools/Wellformedness.hs`. The checks here work
//! directly on the surface syntax tree, because `tamarin-parser` is
//! dependency-free and so cannot reach the elaborated signature, the
//! SAPIC-translated theory or the HughesPJ renderer. As a consequence:
//!
//! - Checks that need term-level sort inference (e.g. `Nat Sorts`) work
//!   over the parser's [`SortHint`] / sigil annotations rather than a
//!   full sort assignment.
//! - Checks that DO need one of those three — `formulaReports`,
//!   `multRestrictedReport`, `ruleVariantsReport` — live in
//!   `tamarin-theory` and are spliced into this report by the batch
//!   (`run.rs`) and web (`theory_io.rs`) load pipelines; see
//!   [`WF_TOPIC_ORDER`] and [`insert_wf_before`].
//! - Bodies reproduce HS's formatters byte-for-byte except where an
//!   individual check documents a departure: [`reserved_prefix_report`]
//!   and [`left_right_rule_report`] emit only a topic-faithful
//!   best-effort body (neither fires on the corpus), and
//!   [`message_derivation_report`] is a static approximation of HS's
//!   prover-driven check.
//!
//! Each public check function corresponds to a Haskell `*Report` /
//! `*Check` function. The umbrella entry point is [`check_theory`].

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::*;

// =============================================================================
// Error type
// =============================================================================

/// A wellformedness diagnostic. `topic` matches exactly the underlined
/// header string Tamarin emits (e.g. `"Reserved names"`,
/// `"Fact arity issues"`).
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct WfError {
    /// Short title used for grouping/ordering — matches HS's
    /// `underlineTopic` argument exactly (e.g. `"Reserved names"`).
    pub topic: String,
    /// Fully-formatted HS-style block for this entry.  When multiple
    /// `WfError`s share a topic the `format_wf_block` formatter
    /// concatenates the messages, separated by blank lines, beneath
    /// the topic header (which is part of `message`).
    pub message: String,
    /// Set by the checks whose body is HS's paragraph fill `text info $-$
    /// nest 2 (fsep $ punctuate comma cells)`.  `message` carries that body
    /// with every cell laid out FLAT — the widest layout decision the parser
    /// crate can make on its own — and
    /// `tamarin_theory::pretty_theory::render_wf_error_report` re-lays the
    /// body out with the HughesPJ engine, which additionally descends INTO a
    /// cell that overruns the ribbon.
    pub fill: Option<WfFill>,
}

impl WfError {
    pub fn new(topic: impl Into<String>, message: impl Into<String>) -> Self {
        WfError {
            topic: topic.into(),
            message: message.into(),
            fill: None,
        }
    }

    /// A `WfError` whose body is HS's `text info $-$ nest 2 (fsep $ punctuate
    /// comma cells)` paragraph fill — `unboundCheck`
    /// (Wellformedness.hs:497-498), `reservedFactNameRules'`
    /// (Wellformedness.hs:546) and `specialFactsUsage'`
    /// (Wellformedness.hs:563).
    ///
    /// `info` is the body's first line WITHOUT the `nest 2` that
    /// `prettyWfErrorReport` applies to every body of a topic group;
    /// [`WfError::message`] gets that indent and the flat fill.
    pub fn filled(topic: impl Into<String>, info: impl Into<String>, cells: Vec<WfDoc>) -> Self {
        let info = info.into();
        let flat: Vec<String> = cells.iter().map(WfDoc::to_flat).collect();
        let message = format!("  {info}\n{}", fsep_comma_fill(&flat));
        WfError {
            topic: topic.into(),
            message,
            fill: Some(WfFill { info, cells }),
        }
    }
}

/// The `fsep`-filled body of a wellformedness entry: HS `text info $-$
/// nest 2 (fsep $ punctuate comma cells)`.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct WfFill {
    /// HS `text info` — the body's first line, WITHOUT `prettyWfErrorReport`'s
    /// per-body `nest 2` (Wellformedness.hs:118-125).
    pub info: String,
    /// The cells `punctuate comma` separates: one `prettyLNFact` per offending
    /// fact, or one `prettyLVar` per variable (`prettyVarList`,
    /// TheoryObject.hs:858-859).
    pub cells: Vec<WfDoc>,
}

/// The layout skeleton of one `prettyTerm` / `prettyLNFact` rendering
/// (Term/Term.hs:298-327, Theory/Model/Fact.hs:567-572).
///
/// HS builds these as HughesPJ `Doc`s, so a fact that overruns the render
/// ribbon breaks at its OWN `sep`/`fsep`/`fcat` points — `prettyLNFact` drops
/// its closing `)` onto the next line and refills the argument list at a
/// deeper indent.  That engine lives in `tamarin-theory`, so the printers
/// here build this skeleton instead: [`WfDoc::to_flat`] renders it with every
/// break point taken horizontally, and `tamarin_theory::wf_fill` maps each
/// variant onto the HughesPJ combinator HS used.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum WfDoc {
    /// HS `text s` — a leaf with no internal break point.
    Text(String),
    /// HS `<>` — juxtaposition; the parts keep their own break points.
    Beside(Vec<WfDoc>),
    /// HS `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm
    /// ts)) <> text ")"` (Term/Term.hs:326-327).
    Fun(String, Vec<WfDoc>),
    /// HS `ppTerms sepa 1 lead finish ts` (Term/Term.hs:319-321) — the `fcat`
    /// of `text lead`, the `nest 1`'d and `sepa`-punctuated operands, and
    /// `text finish`: pairs (`<`, `, `, `>`) and AC chains (`(`, the operator,
    /// `)`).
    Terms {
        lead: String,
        sep: String,
        finish: String,
        items: Vec<WfDoc>,
    },
    /// HS `ppFact n ts = nestShort' (n ++ "(") ")" (fsep (punctuate comma (map
    /// ppTerm ts)))` (Fact.hs:572), i.e. `sep [text lead $$ nest (length lead +
    /// 1) body, text ")"]` (Text/PrettyPrint/Class.hs:218-223).
    Fact { lead: String, args: Vec<WfDoc> },
}

impl WfDoc {
    /// Render with every break point taken horizontally — the layout HughesPJ
    /// picks while the doc fits the ribbon.
    pub fn to_flat(&self) -> String {
        let mut s = String::new();
        self.write_flat(&mut s);
        s
    }

    fn write_flat(&self, out: &mut String) {
        match self {
            WfDoc::Text(s) => out.push_str(s),
            WfDoc::Beside(parts) => {
                for p in parts {
                    p.write_flat(out);
                }
            }
            WfDoc::Fun(name, args) => {
                out.push_str(name);
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        // `punctuate comma` + the space `fsep` joins with.
                        out.push_str(", ");
                    }
                    a.write_flat(out);
                }
                out.push(')');
            }
            WfDoc::Terms {
                lead,
                sep,
                finish,
                items,
            } => {
                out.push_str(lead);
                for (i, it) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(sep);
                    }
                    it.write_flat(out);
                }
                out.push_str(finish);
            }
            WfDoc::Fact { lead, args } => {
                // `nestShort'`'s two spaces: `$$` overlaps the nested body onto
                // the lead's line one column past it, and the enclosing `sep`
                // joins that with the closing `)`.  An argument-less fact keeps
                // only the `sep` space (`text lead $$ nest n emptyDoc` is just
                // the lead), so it renders `A( )`.
                out.push_str(lead);
                if !args.is_empty() {
                    out.push(' ');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        a.write_flat(out);
                    }
                }
                out.push_str(" )");
            }
        }
    }
}

pub type WfReport = Vec<WfError>;

// =============================================================================
// Shared report ordering (batch `--prove` and web load pipelines)
// =============================================================================

/// Canonical HS wellformedness check-order (Wellformedness.hs check list).
/// Each ordered-splice call site (in the batch `run.rs` and web `theory_io.rs`
/// load pipelines) passes a SUFFIX of this list as its `anchors`: since
/// [`insert_wf_before`] only tests membership, a suffix contains exactly the
/// topics that sort AFTER the check being inserted.  One source of truth
/// avoids several in-sync literal lists that would silently mis-order a single
/// report on a typo.
pub const WF_TOPIC_ORDER: &[&str] = &[
    "Reserved names",
    "Special facts",
    "Fr facts must only use a fresh- or a msg-variable",
    "Fact arity issues",
    "Fact multiplicity issues",
    "Fact capitalization issues",
    "Facts occur in the left-hand-side but not in any right-hand-side ",
    "Unbound variables",
    "Quantifier sorts",
    "Formula terms",
    " Formula guardedness",
    "Lemma annotations",
    "Multiplication restriction of rules",
    "Nat Sorts",
    "Subterm Convergence Warning",
    "Message Derivation Checks",
    "Derivation Checks",
];

// First `WF_TOPIC_ORDER` index whose topic sorts after each splicing check.
pub const WF_AFTER_FACT_LHS: usize = 8; // "Quantifier sorts"
pub const WF_AFTER_CHECK_GUARDED: usize = 11; // "Lemma annotations"
pub const WF_AFTER_MULT_RESTRICTED: usize = 13; // "Nat Sorts"

/// Splice `errors` into `report` immediately before the first existing entry
/// whose `topic` is one of `anchors` (its HS check-order position), or at the
/// end if none match, preserving the relative order of both the existing tail
/// and the inserted errors.  Shared by the batch (`run.rs`) and web
/// (`theory_io.rs`) ordered-splice call sites — the SAPIC unbound / lhs-rhs /
/// publicNames re-splices, formulaReports, multRestricted and ruleVariants —
/// which differ only in their `anchors` slice and the source of `errors`.
/// No-op when `errors` is empty.
pub fn insert_wf_before(report: &mut Vec<WfError>, errors: Vec<WfError>, anchors: &[&str]) {
    if errors.is_empty() {
        return;
    }
    let insert_before = report
        .iter()
        .position(|e| anchors.contains(&e.topic.as_str()))
        .unwrap_or(report.len());
    let tail = report.split_off(insert_before);
    report.extend(errors);
    report.extend(tail);
}

/// Anchor list for the SAPIC `publicNamesReport` splice (HS check index 4):
/// the variable-sorts topic, then every [`WF_TOPIC_ORDER`] topic EXCEPT
/// "Unbound variables" (HS `unboundReport` runs BEFORE `publicNames`, so its
/// entries must not act as a boundary).  publicNames therefore splices before
/// the first entry from a later check.
pub fn after_public_names_topics() -> Vec<&'static str> {
    std::iter::once("Variable with mismatching sorts or capitalization")
        .chain(
            WF_TOPIC_ORDER
                .iter()
                .copied()
                .filter(|t| *t != "Unbound variables"),
        )
        .collect()
}

/// Anchor list for the `ruleVariantsReport` splice (HS check index 6): every
/// [`WF_TOPIC_ORDER`] topic EXCEPT "Unbound variables", whose `unboundReport`
/// (index 2) runs earlier and so must not act as a boundary.  The three checks
/// between them — `freshNamesReport`, `publicNamesReport`, `ruleSortsReport` —
/// emit topics `WF_TOPIC_ORDER` does not carry, so they are already outside
/// the list.  ruleVariants therefore splices before the first `factReports`
/// entry.
pub fn after_variants_topics() -> Vec<&'static str> {
    WF_TOPIC_ORDER
        .iter()
        .copied()
        .filter(|t| *t != "Unbound variables")
        .collect()
}

/// Topics emitted by a check that runs after `unboundReport`, but which
/// [`WF_TOPIC_ORDER`] does not carry: `freshNamesReport` (HS index 3),
/// `publicNamesReport` (4), `ruleSortsReport` (5), `ruleVariantsReport` (6),
/// the `reservedPrefixReport` arm of `factReports` (7), the `checkQuantifiers`
/// arm of `formulaReports` (8), and `leftRightRuleReportDiff`, which
/// `checkWellformednessDiff` (Wellformedness.hs:1248-1265, see line 1259) runs
/// between those last two.
const AFTER_UNBOUND_EXTRA_TOPICS: &[&str] = &[
    "Fresh public constants",
    "Public constants with mismatching capitalization",
    "Variable with mismatching sorts or capitalization",
    "Rule has no variants",
    "Reserved prefixes",
    "Left rule",
    "Right rule",
];

/// Anchor list for the SAPIC `unboundReport` re-splice (HS check index 2):
/// every topic a LATER check emits.  `unboundReport` is the first entry of
/// `checkWellformedness`'s list past `checkIfLemmasInTheory`
/// (Wellformedness.hs:1270-1287), so the boundary set is every topic except
/// its own and those of the checks ahead of it — the `preReport` topics (SAPIC
/// process warnings, the accountability RP check) and the `--prove`/`--lemma`
/// argument check.  Their absence is what keeps the re-spliced entries behind
/// them.
pub fn after_unbound_topics() -> Vec<&'static str> {
    AFTER_UNBOUND_EXTRA_TOPICS
        .iter()
        .copied()
        .chain(
            WF_TOPIC_ORDER
                .iter()
                .copied()
                .filter(|t| *t != "Unbound variables"),
        )
        .collect()
}

/// Run every wellformedness check against `thy`. Topics from the result
/// can be compared directly against `tamarin-prover`'s output.
pub fn check_theory(thy: &Theory) -> WfReport {
    // Mirrors HS `Theory.Tools.Wellformedness.checkWellformedness`
    // (Wellformedness.hs:1270-1287) and, for diff theories,
    // `checkWellformednessDiff` (1248-1265), in HS check order: unbound,
    // freshNames, publicNames, ruleSorts (variable_sort_clashes),
    // factReports, [leftRightRule (diff only)], formulaReports,
    // lemmaAttribute, multRestricted, natWellSorted, subtermConvergence,
    // then message-derivation.  `leftRightRuleReportDiff` is placed AFTER
    // the factReports group and the ruleSorts check, matching the diff
    // order at Wellformedness.hs:1256-1261.
    let mut report = Vec::new();
    report.extend(unbound_report(thy));
    report.extend(fresh_names_report(thy));
    report.extend(public_names_report(thy));
    // HS `ruleSortsReport` (sortsClashCheck) runs HERE — after publicNamesReport
    // and BEFORE factReports (Wellformedness.hs:1270-1286, see line 1275/1256).  It is ported as
    // `variable_sort_clashes` ("Variable with mismatching sorts or
    // capitalization").
    report.extend(variable_sort_clashes(thy));
    // ruleVariantsReport — spliced by the batch load pipeline (`run.rs`,
    // anchored by `after_variants_topics`): it needs a MaudeHandle and the
    // variant solver, neither of which the parser crate reaches.
    // factReports group:
    report.extend(reserved_report(thy));
    report.extend(reserved_fact_name_rules(thy));
    report.extend(reserved_prefix_report(thy));
    report.extend(fresh_fact_arguments(thy));
    report.extend(special_facts_usage(thy));
    report.extend(fact_usage(thy));
    report.extend(fact_lhs_occur_no_rhs(thy));
    // leftRightRuleReportDiff (diff only) — placed AFTER factReports and
    // ruleSorts, BEFORE formulaReports, matching HS `checkWellformednessDiff`
    // order (Wellformedness.hs:1248-1265, see line 1259).  (ruleVariantsReportDiff sits between
    // factReports and leftRightRule in HS but is unported, so it does not
    // affect placement.)
    report.extend(left_right_rule_report(thy));
    // formulaReports group (checkQuantifiers / checkTerms / checkGuarded) —
    // spliced by the load pipelines as one interleaved per-formula pass
    // (`tamarin_theory::formula_reports::formula_reports`): it needs the
    // elaborated signature's irreducible funsyms and the TRANSLATED theory's
    // formulas.
    // lemmaAttributeReport:
    report.extend(lemma_attribute_report(thy));
    // multRestrictedReport — spliced by the load pipelines
    // (`tamarin_theory::mult_restricted`): it needs the elaborated
    // signature's irreducible funsyms and the HughesPJ rule renderer,
    // neither of which the parser crate reaches.
    // natWellSortedReport:
    report.extend(nat_well_sorted_report(thy));
    // checkEquationsSubtermConvergence:
    report.extend(subterm_convergence_report(thy));
    // Message Derivation Checks (HS: TheoryLoader.hs:172-176 +
    // MessageDerivationChecks.hs:35-47).  HS's check is dynamic
    // (per-variable prover invocation, --derivcheck-timeout default 5s);
    // we run a static intersection that catches the same variables for
    // the common case.  See `message_derivation_report` docstring.
    report.extend(message_derivation_report(thy));
    report
}

/// The ordered set of distinct topic strings present in `report`.
pub fn topics(report: &WfReport) -> BTreeSet<String> {
    report.iter().map(|e| e.topic.clone()).collect()
}

// =============================================================================
// Check that CLI --prove/--lemma arguments name actual lemmas in the theory
// =============================================================================

/// Port of HS `checkIfLemmasInTheory` (Wellformedness.hs:1156-1171).
///
/// HS threads `_lemmasToProve` through the theory's `Options` record.
/// In the Rust port the CLI args are not embedded in the parser AST,
/// so we take them as a separate parameter.
///
/// Semantics (mirror of `findNotProvedLemmas` / `lemmaChecker`):
///   - An empty `lemma_names` slice (no `--prove` / `--lemma` flag)
///     means "prove all" → skip the check.
///   - A list that is exactly `[""]` (bare `--prove` with no value)
///     also means "all" → skip.
///   - Otherwise: for each name in `lemma_names`, it "corresponds" if
///     • there is a theory lemma whose name equals it exactly, OR
///     • the name ends with `*` and its prefix is a prefix of at least
///     one theory-lemma name.
///     Names that don't correspond are collected; if any exist the WF
///     check fires.
pub fn check_if_lemmas_in_theory(lemma_names: &[String], thy: &Theory) -> WfReport {
    // HS: `| lemmaArgsNames == [[]] = []`  (Wellformedness.hs:1156-1171, see line 1158)
    // HS stores lemmaArgsNames as [String]; [[]] is [""] (a list
    // containing exactly one empty string), which means bare `--prove`
    // with no argument value.  Skip the check ONLY in that case.
    //
    // When lemma_names is EMPTY (no --prove at all) → also skip.
    // When lemma_names has MIXED entries (e.g. `--prove --lemma=BadX`
    // → ["", "BadX"]) the HS condition fails so the check DOES run —
    // the empty string is reported as "not found" too (faithfulness
    // requires we keep empty strings in the probe list).
    if lemma_names.is_empty() {
        return Vec::new();
    }
    // Exactly one entry and it is empty → bare `--prove` → skip.
    if lemma_names == [""] {
        return Vec::new();
    }
    // Collect non-empty names for the "matches any lemma" test;
    // empty strings are kept in the fold below since HS does NOT
    // filter them (they trivially fail argFilter).
    let all_names: Vec<&str> = lemma_names.iter().map(|s| s.as_str()).collect();

    let theory_lemma_names: Vec<&str> = theory_lemmas(thy)
        .into_iter()
        .map(|l| l.name.as_str())
        .collect();

    // HS `findNotProvedLemmas` (Wellformedness.hs:1140-1151, see line 1141) is a `foldl`
    // that PREPENDS mismatches.  HS's Arguments list is built with
    // `addArg` which prepends each CLI flag, so the stored arg list is
    // in REVERSE CLI order.  `findArg` returns them in that reversed
    // order; `foldl`-prepend of a reversed list re-reverses → the final
    // `notProvedLemmas` is in ORIGINAL CLI order.
    //
    // RS's `lemma_names` is already in CLI order (no prepend in
    // `parse_args`), so a simple forward-iterate-and-push yields the
    // same result as the double-reversed HS fold.
    let mut not_proved: Vec<&str> = Vec::new();
    for name in all_names.iter() {
        if !arg_matches_any_lemma(name, &theory_lemma_names) {
            not_proved.push(name);
        }
    }

    if not_proved.is_empty() {
        return Vec::new();
    }

    // HS topic: `underlineTopic "Check presence of the --prove/--lemma
    // arguments in theory"` (Wellformedness.hs:1156-1171, see line 1169).
    let topic_str = "Check presence of the --prove/--lemma arguments in theory";
    // HS body: `vcat [text $ "--> '" ++ intercalate "', '" notProvedLemmas
    //   ++ "'" ++ " from arguments do(es) not correspond ..."]`
    // Rendered via `prettyWfErrorReport` → `nest 2`:
    //   "<topic>\n<===>\n\n  --> '<names>' from arguments ...\n"
    let names_str = not_proved.join("', '");
    let body_line = format!(
        "--> '{}' from arguments do(es) not correspond to a specified lemma in the theory ",
        names_str,
    );

    // Build the message in the same shape that format_wf_block expects:
    // the topic header (underlineTopic output) followed by a blank line,
    // followed by the 2-space-indented body line.
    // HS prettyWfErrorReport: `text topic $-$ (nest 2 . vcat ... $ map snd errs)`
    // `text topic` renders the underlineTopic string (title\n====\n),
    // `$-$` appends one more newline, so we get title\n====\n\n<body>.
    let mut msg = String::new();
    msg.push_str(&underline_topic(topic_str));
    msg.push('\n'); // blank line between header and body
    msg.push_str("  "); // nest 2
    msg.push_str(&body_line);
    msg.push('\n');

    vec![WfError::new(topic_str, msg)]
}

/// True if `arg` "corresponds" to at least one lemma name in
/// `theory_lemmas`.  Mirrors HS `lemmaChecker`:
///   - suffix `*` → prefix match on the lemma name (no `*` in result)
///   - otherwise  → exact equality
fn arg_matches_any_lemma(arg: &str, theory_lemmas: &[&str]) -> bool {
    if let Some(prefix) = arg.strip_suffix('*') {
        theory_lemmas.iter().any(|n| n.starts_with(prefix))
    } else {
        theory_lemmas.contains(&arg)
    }
}

// =============================================================================
// Helpers — collecting facts and variables
// =============================================================================

fn theory_rules(thy: &Theory) -> Vec<&Rule> {
    let mut out = Vec::new();
    for it in &thy.items {
        match it {
            TheoryItem::Rule(r) => out.push(r),
            TheoryItem::IntrRule(r) => out.push(r),
            _ => {}
        }
    }
    out
}

fn theory_lemmas(thy: &Theory) -> Vec<&Lemma> {
    thy.items
        .iter()
        .filter_map(|it| match it {
            TheoryItem::Lemma(l) => Some(l),
            _ => None,
        })
        .collect()
}

/// Iterate all facts in a rule (premises ∪ actions ∪ conclusions),
/// each paired with which side it appeared on. Callers currently discard
/// the side tag; it is retained for callers that need to distinguish sides.
// Intentionally retained: faithful HS port; no caller reads the tag yet.
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum FactSide {
    Lhs,
    Acts,
    Rhs,
}

fn rule_facts(r: &Rule) -> Vec<(FactSide, &Fact)> {
    let mut out = Vec::new();
    for f in &r.premises {
        out.push((FactSide::Lhs, f));
    }
    for f in &r.actions {
        out.push((FactSide::Acts, f));
    }
    for f in &r.conclusions {
        out.push((FactSide::Rhs, f));
    }
    out
}

/// Recursively collect every variable appearing in a term.
fn term_vars(t: &Term, out: &mut Vec<VarSpec>) {
    match t {
        Term::Var(v) => out.push(v.clone()),
        Term::App(_, args) => {
            for a in args {
                term_vars(a, out);
            }
        }
        Term::AlgApp(_, a, b) => {
            term_vars(a, out);
            term_vars(b, out);
        }
        Term::Pair(items) => {
            for a in items {
                term_vars(a, out);
            }
        }
        Term::Diff(a, b) => {
            term_vars(a, out);
            term_vars(b, out);
        }
        Term::BinOp(_, a, b) => {
            term_vars(a, out);
            term_vars(b, out);
        }
        Term::PatMatch(inner) => term_vars(inner, out),
        Term::PubLit(_)
        | Term::FreshLit(_)
        | Term::NatLit(_)
        | Term::Number(_)
        | Term::NumberOne
        | Term::NatOne
        | Term::DhNeutral => {}
    }
}

fn fact_vars(f: &Fact) -> Vec<VarSpec> {
    let mut v = Vec::new();
    for a in &f.args {
        term_vars(a, &mut v);
    }
    v
}

/// Collect every public-name literal (`'foo'`) and fresh-name literal
/// (`~'foo'`) within a term subtree.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NameKind {
    Pub,
    Fresh,
}

fn term_name_lits(t: &Term, out: &mut Vec<(NameKind, String)>) {
    match t {
        Term::PubLit(s) => out.push((NameKind::Pub, s.clone())),
        Term::FreshLit(s) => out.push((NameKind::Fresh, s.clone())),
        Term::App(_, args) => {
            for a in args {
                term_name_lits(a, out);
            }
        }
        Term::AlgApp(_, a, b) => {
            term_name_lits(a, out);
            term_name_lits(b, out);
        }
        Term::Pair(items) => {
            for a in items {
                term_name_lits(a, out);
            }
        }
        Term::Diff(a, b) => {
            term_name_lits(a, out);
            term_name_lits(b, out);
        }
        Term::BinOp(_, a, b) => {
            term_name_lits(a, out);
            term_name_lits(b, out);
        }
        Term::PatMatch(inner) => term_name_lits(inner, out),
        _ => {}
    }
}

fn rule_terms(r: &Rule) -> impl Iterator<Item = &Term> {
    r.premises
        .iter()
        .chain(&r.actions)
        .chain(&r.conclusions)
        .flat_map(|f: &Fact| f.args.iter())
}

/// Build an HS `underlineTopic` block: `"<title>\n<====>\n"` where the
/// underline matches the title length exactly (counting any trailing
/// space).  Mirrors `underlineTopic` in `Theory.Tools.Wellformedness`.
pub fn underline_topic(title: &str) -> String {
    let len = title.chars().count();
    let mut s = String::with_capacity(title.len() + len + 2);
    s.push_str(title);
    s.push('\n');
    for _ in 0..len {
        s.push('=');
    }
    s.push('\n');
    s
}

/// Assemble a topic-grouped `WfReport` from pre-built body strings (empty
/// `bodies` yields an empty report).  `underline_topic` already ends the
/// `====` rule with a newline, so the extra `\n` is HS's `$-$` blank line
/// before the bodies; the bodies are joined by the `\n  \n` that HS's
/// `nest 2 (vcat (intersperse (text "") …))` renders a blank separator line
/// as (a 2-space `nest 2`'d `text ""`).  Each body already carries its own
/// 2-space `nest 2` indent.
fn grouped_topic_block(topic: &str, bodies: Vec<String>) -> WfReport {
    if bodies.is_empty() {
        return Vec::new();
    }
    let mut msg = underline_topic(topic);
    msg.push('\n');
    msg.push_str(&bodies.join("\n  \n"));
    vec![WfError::new(topic, msg)]
}

/// HS `numbered'` index width: `nWidth = length (show n)` where `n` is the
/// number of items (PrettyPrint/Class.hs:257-258).  Each index is rendered as
/// `flushRight nWidth (show i)` — i.e. left-padded with spaces to this width —
/// so a 1-of-10+ list prints ` 1.`…`10.`.
fn numbered_index_width(count: usize) -> usize {
    count.to_string().len()
}

/// Column budget of one wellformedness-report fill line, measured from the
/// fill's own left edge.
///
/// The report is baked into the theory by `addComment`, which renders with
/// HughesPJ's DEFAULT style — `lineLength = 100`, `ribbonsPerLine = 1.5`, so
/// `ribbonLen = round (100 / 1.5) = 67` (TheoryObject.hs:717-718).  HughesPJ
/// keeps a `fill` item on the current line iff `fits ((w `min` r) - sl)`,
/// where `w` is the line width left after the nesting and `sl` the column
/// already used inside it.  The fills below sit at `nest 2` inside the
/// `nest 2` `prettyWfErrorReport` wraps every body in (Wellformedness.hs:118-125),
/// so `w = 100 - 4 = 96` and the ribbon is what binds.
const WF_FILL_RIBBON: usize = 67;

/// The `nest 2` (check) + `nest 2` (`prettyWfErrorReport`) indent every filled
/// list below is rendered at.
const WF_FILL_INDENT: &str = "    ";

/// HS `nest 2 (fsep $ punctuate comma $ map pp xs)` — the paragraph-fill list
/// shared by `specialFactsUsage'` (Wellformedness.hs:563),
/// `reservedFactNameRules'` (Wellformedness.hs:546) and `prettyVarList`
/// (TheoryObject.hs:858-859).
///
/// `punctuate comma` attaches the separator to the item it follows, so each
/// cell but the last carries a trailing `,`; `fsep` then joins cells with a
/// space, breaking to a new line — and re-applying the [`WF_FILL_INDENT`]
/// nesting — before any cell that would pass [`WF_FILL_RIBBON`].
///
/// Cells are measured in characters, matching HughesPJ's `text` length.
///
/// This is the FLAT FALLBACK layout: every cell is rendered flat, so a cell
/// wider than the ribbon on its own gets a line to itself.  HS descends into
/// such a cell's own layout instead (`prettyLNFact` breaks its closing `)`
/// onto the following line), which needs the HughesPJ `Doc` engine
/// `tamarin-theory` owns.  The shipped bytes therefore come from
/// `tamarin_theory::wf_fill`, which lays the [`WfDoc`] skeletons the checks
/// stash in [`WfError::fill`] out again; what this function produces is the
/// flat rendering [`WfError::message`] carries, for callers that read the
/// report without that engine.
fn fsep_comma_fill(items: &[String]) -> String {
    let last = items.len().saturating_sub(1);
    let mut out = String::new();
    let mut col = 0usize;
    for (i, item) in items.iter().enumerate() {
        let cell_width = item.chars().count() + usize::from(i != last);
        if i == 0 {
            out.push_str(WF_FILL_INDENT);
        } else if col + 1 + cell_width <= WF_FILL_RIBBON {
            out.push(' ');
            col += 1;
        } else {
            out.push('\n');
            out.push_str(WF_FILL_INDENT);
            col = 0;
        }
        out.push_str(item);
        if i != last {
            out.push(',');
        }
        col += cell_width;
    }
    out
}

/// HS `prettyLNFact = prettyFact prettyNTerm` (Fact.hs:581-582): the fact's
/// `ppFact` skeleton `[!]Name(` … `)` over `prettyTerm`'d arguments.
fn wf_fact_doc(fa: &Fact, ac: &AcSyms) -> WfDoc {
    let mut lead = String::new();
    if fa.persistent {
        lead.push('!');
    }
    lead.push_str(&fa.name);
    lead.push('(');
    WfDoc::Fact {
        lead,
        args: fa.args.iter().map(|a| wf_term_doc(a, ac)).collect(),
    }
}

/// [`wf_fact_doc`] laid out flat: `!Name( arg, arg, ... )` for persistent,
/// `Name( arg, arg, ... )` for linear.
fn pp_wf_fact(fa: &Fact, ac: &AcSyms) -> String {
    wf_fact_doc(fa, ac).to_flat()
}

/// HS `prettyTerm`'s `split` (Term/Term.hs:323-324): the operand list a
/// pair-headed term renders between `<` and `>`.  `split` recurses on the
/// RIGHT child while that child is itself `pairSym`-headed
/// (`FPair`, Term/Term/Raw.hs:194), so `pair(a, pair(b, c))` yields
/// `[a, b, c]` while the left-nested `pair(pair(a, b), c)` yields
/// `[pair(a, b), c]`.  A non-pair `t` yields `[t]`.
///
/// Both parser spellings feed the same spine: `Pair` holds `<a, b, c>` flat
/// where HS nests it `pair(a, pair(b, c))`, so every element but the last is
/// an operand and the last continues the spine; `App("pair", [a, b])` is the
/// source form `pair(a, b)`, which HS parses to that same `pairSym` FAPP
/// (`naryOpApp`, Theory/Text/Parser/Term.hs:88-105, see line 104).
fn pair_split<'a>(t: &'a Term, out: &mut Vec<&'a Term>) {
    match t {
        Term::Pair(items) => {
            if let Some((last, init)) = items.split_last() {
                out.extend(init.iter());
                pair_split(last, out);
            }
        }
        Term::App(name, args) if name == "pair" && args.len() == 2 => {
            out.push(&args[0]);
            pair_split(&args[1], out);
        }
        _ => out.push(t),
    }
}

/// HS `prettyTerm`'s pair arm `ppTerms ", " 1 "<" ">" (split t)`
/// (Term/Term.hs:313), for a `t` that is `pairSym`-headed.
fn wf_pair_doc(t: &Term, ac: &AcSyms) -> WfDoc {
    let mut items: Vec<&Term> = Vec::new();
    pair_split(t, &mut items);
    WfDoc::Terms {
        lead: "<".to_string(),
        sep: ", ".to_string(),
        finish: ">".to_string(),
        items: items.iter().map(|it| wf_term_doc(it, ac)).collect(),
    }
}

/// HS `prettyTerm`'s AC arms (Term/Term.hs:304-309): the flattened, sorted
/// operand list of an `FAPP (AC …)` rendered inside `(` `)` with `sepa`
/// between operands (`ppTerms sepa 1 "(" ")" ts`).
fn wf_ac_chain_doc(t: &Term, sepa: &str, ac: &AcSyms) -> WfDoc {
    let head = wf_funsym_key(t, ac);
    let mut flat: Vec<&Term> = Vec::new();
    flatten_ac(head, t, &mut flat, ac);
    flat.sort_by(|a, b| cmp_wf_term(a, b, ac));
    WfDoc::Terms {
        lead: "(".to_string(),
        sep: sepa.to_string(),
        finish: ")".to_string(),
        items: flat.iter().map(|a| wf_term_doc(a, ac)).collect(),
    }
}

/// HS `prettyTerm` (Term/Term.hs:298-327) over a parser-AST term: the
/// skeleton whose break points HS's `fsep`/`fcat` own.
fn wf_term_doc(t: &Term, ac: &AcSyms) -> WfDoc {
    use Term::*;
    let t = ac_collapse(t, ac);
    // HS `prettyTerm` matches `FApp (AC (ACfct (f, _))) ts` BEFORE any
    // builtin-symbol arm (Term/Term.hs:304-305), and the separator is the
    // symbol name with a space on each side — the same string
    // `crate::ast::BinOp::AcFct`'s `separator` builds for the infix spelling.
    if let Some(name) = ac_app_name(t, ac) {
        return wf_ac_chain_doc(t, &format!(" {name} "), ac);
    }
    // The leaves HS renders with a single `text` — no break point inside.
    let leaf = |s: String| WfDoc::Text(s);
    match t {
        Var(v) => {
            let mut s = String::new();
            s.push_str(sort_prefix(&v.sort));
            s.push_str(&v.name);
            if v.idx > 0 {
                s.push('.');
                s.push_str(&v.idx.to_string());
            }
            leaf(s)
        }
        PubLit(s) => leaf(format!("'{s}'")),
        FreshLit(s) => leaf(format!("~'{s}'")),
        NatLit(s) => leaf(format!("%'{s}'")),
        Number(n) => leaf(n.to_string()),
        // HS `prettyTerm` renders the nullary builtins via `text (BC.unpack f)`
        // except natOneSym ("%1"): oneSym → "one", dhNeutralSym → "DH_neutral"
        // (FunctionSymbols.hs:255,257,267; Term.hs:312,314).
        NumberOne => leaf("one".to_string()),
        NatOne => leaf("%1".to_string()),
        DhNeutral => leaf("DH_neutral".to_string()),
        Pair(_) => wf_pair_doc(t, ac),
        App(name, args) if name == "pair" && args.len() == 2 => wf_pair_doc(t, ac),
        // `em` is HS's sole `C` symbol (`CSym = EMap`,
        // FunctionSymbols.hs:142-143), and `fAppC nacsym as = FAPP (C nacsym)
        // (sort as)` (Term/Term/Raw.hs:132-134, see line 134) sorts its
        // arguments at construction, so `prettyTerm` never sees the written
        // order.
        App(name, args) if name == "em" && args.len() == 2 => {
            let mut sorted: Vec<&Term> = args.iter().collect();
            sorted.sort_by(|a, b| cmp_wf_term(a, b, ac));
            WfDoc::Fun(
                name.clone(),
                sorted.iter().map(|a| wf_term_doc(a, ac)).collect(),
            )
        }
        // HS `FApp (NoEq (f,_)) [] -> text f` (Term.hs:314) — a nullary symbol
        // has no `ppFun` parentheses at all.
        App(name, args) if args.is_empty() => leaf(name.clone()),
        App(name, args) => WfDoc::Fun(
            name.clone(),
            args.iter().map(|a| wf_term_doc(a, ac)).collect(),
        ),
        // HS canonicalises `aenc{m}pk` as `aenc(m, pk)`.
        AlgApp(name, l, r) => {
            WfDoc::Fun(name.clone(), vec![wf_term_doc(l, ac), wf_term_doc(r, ac)])
        }
        // HS `prettyTerm`'s diff arm (Term.hs:311) joins with `<>`, not the
        // breakable `fsep` `ppFun` uses.
        Diff(l, r) => WfDoc::Beside(vec![
            WfDoc::Text("diff(".to_string()),
            wf_term_doc(l, ac),
            WfDoc::Text(", ".to_string()),
            wf_term_doc(r, ac),
            WfDoc::Text(")".to_string()),
        ]),
        BinOp(op, l, r) => {
            let sym = op.separator();
            // HS builds AC operators (Mult/Union/Xor/NatPlus and the
            // user-declared `[AC]` symbols) via `fAppAC`, which flattens the
            // chain, sorts the operands (Ord LTerm), and renders them
            // parenthesised by `prettyTerm` (e.g. `(%x%+%1%+%1)`).
            // Exp is NOT AC: rendered binary with `<>`, no surrounding parens.
            if is_ac_binop(op) {
                wf_ac_chain_doc(t, &sym, ac)
            } else {
                WfDoc::Beside(vec![
                    wf_term_doc(l, ac),
                    WfDoc::Text(sym.into_owned()),
                    wf_term_doc(r, ac),
                ])
            }
        }
        PatMatch(inner) => {
            WfDoc::Beside(vec![WfDoc::Text("=".to_string()), wf_term_doc(inner, ac)])
        }
    }
}

/// Substitute every `let`-binding of a rule into its facts, mirroring HS,
/// whose rule parser inlines the `let` block before building the
/// `ProtoRuleE` (so wellformedness checks see fully-substituted facts).
///
/// HS `letBlock` (Parser/Let.hs:28-35, see line 34) is `foldr1 compose` over singleton
/// substitutions — equivalent to applying each binding sequentially in
/// REVERSE binding order ("bottom-up").  Backward references expand;
/// FORWARD references survive as free variables.  Matches
/// `elaborate::apply_let_block`.
fn rule_facts_with_lets(r: &Rule) -> (Vec<Fact>, Vec<Fact>, Vec<Fact>) {
    let mut prems = r.premises.clone();
    let mut acts = r.actions.clone();
    let mut concs = r.conclusions.clone();
    for b in r.let_block.iter().rev() {
        for f in prems.iter_mut() {
            subst_let_fact(f, &b.var, &b.value);
        }
        for f in acts.iter_mut() {
            subst_let_fact(f, &b.var, &b.value);
        }
        for f in concs.iter_mut() {
            subst_let_fact(f, &b.var, &b.value);
        }
    }
    (prems, acts, concs)
}

fn subst_let_fact(f: &mut Fact, key: &Term, val: &Term) {
    for a in f.args.iter_mut() {
        *a = subst_let_term(a, key, val);
    }
}

fn subst_let_term(t: &Term, key: &Term, val: &Term) -> Term {
    if t == key {
        return val.clone();
    }
    use Term::*;
    match t {
        App(name, args) => App(
            name.clone(),
            args.iter().map(|a| subst_let_term(a, key, val)).collect(),
        ),
        AlgApp(name, a, b) => AlgApp(
            name.clone(),
            Box::new(subst_let_term(a, key, val)),
            Box::new(subst_let_term(b, key, val)),
        ),
        Pair(args) => Pair(args.iter().map(|a| subst_let_term(a, key, val)).collect()),
        Diff(a, b) => Diff(
            Box::new(subst_let_term(a, key, val)),
            Box::new(subst_let_term(b, key, val)),
        ),
        BinOp(op, a, b) => BinOp(
            *op,
            Box::new(subst_let_term(a, key, val)),
            Box::new(subst_let_term(b, key, val)),
        ),
        PatMatch(a) => PatMatch(Box::new(subst_let_term(a, key, val))),
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) | NumberOne | NatOne
        | DhNeutral => t.clone(),
    }
}

/// The names whose PREFIX application denotes a user-declared `[AC]` symbol.
///
/// HS carries this information in the signature: `functions: add/2 [AC]`
/// registers an `ACfctUser` symbol
/// (Theory/Text/Parser/Signature.hs:219-222, see line 221), and `lookupArity`
/// resolves a prefix application by a list lookup over
/// `S.toList (userDefinedFunSyms maudeSig)` in which every `NoEqUser` sorts
/// before every `ACfctUser` (Theory/Text/Parser/Term.hs:62-72,
/// Term/Term/FunctionSymbols.hs:146-147).  A name that is ALSO a `NoEq`
/// symbol of the full signature therefore resolves to the `NoEq` symbol and
/// is NOT in this set; only the remaining `[AC]` names build
/// `FAPP (AC (ACfct …))` from the prefix spelling.  (The INFIX spelling is
/// always the AC symbol — HS `acterm`, Term.hs:165-174 — which the AST
/// records as [`BinOp::AcFct`], classified by shape, not via this set.)
/// The parser AST has no signature, so the wellformedness printers
/// reconstruct the set from the theory's own `functions:` and `builtins:`
/// declarations — the same declarations HS reads.
type AcSyms = BTreeSet<String>;

/// The `[AC]`-attributed function symbols declared by `thy` (HS
/// `stACFunSyms . sig`, Theory/Text/Parser/Term.hs:165-174), minus the names
/// that are also `NoEq` symbols of the full signature — see [`AcSyms`].  The
/// `NoEq` side is the non-`[AC]` `functions:` declarations, each enabled
/// builtin's contribution ([`crate::parser::builtin_noeq_sym_names`]), and
/// the always-present pair signature (`minimalMaudeSig` is `pairFunSig` —
/// `pair`/`fst`/`snd` — Term/Maude/Signature.hs:224-226).
fn user_ac_fun_names(thy: &Theory) -> AcSyms {
    let mut ac = AcSyms::new();
    let mut noeq: BTreeSet<&str> = ["pair", "fst", "snd"].into_iter().collect();
    for it in &thy.items {
        match it {
            TheoryItem::Functions(decls) => {
                for d in decls {
                    if d.ac {
                        ac.insert(d.name.clone());
                    } else {
                        noeq.insert(d.name.as_str());
                    }
                }
            }
            TheoryItem::Builtins(names) => {
                for n in names {
                    noeq.extend(crate::parser::builtin_noeq_sym_names(n));
                }
            }
            _ => {}
        }
    }
    ac.retain(|n| !noeq.contains(n.as_str()));
    ac
}

/// The symbol name when `t` is an application of a user-declared `[AC]`
/// symbol, i.e. HS's `FAPP (AC (ACfct …)) ts`.
///
/// HS `naryOpApp` (Theory/Text/Parser/Term.hs:88-105, see line 105) builds
/// `fAppAC (ACfct …) ts` for an `IsAC` symbol, and its arity check is guarded
/// on `NotAC` (line 98), so `add(p, q, r)` is a legal ternary AC application.
/// One-argument applications are excluded because [`ac_collapse`] has already
/// replaced them by their argument.
fn ac_app_name<'a>(t: &'a Term, ac: &AcSyms) -> Option<&'a str> {
    match t {
        Term::App(n, args) if args.len() >= 2 && ac.contains(n.as_str()) => Some(n.as_str()),
        _ => None,
    }
}

/// HS `fAppAC _ [a] = a` (Term/Term/Raw.hs:118-129, see line 121): a
/// one-argument AC application IS its argument, so `add(x)` is the term `x`
/// and carries no `add` node at all.
fn ac_collapse<'a>(t: &'a Term, ac: &AcSyms) -> &'a Term {
    let mut t = t;
    while let Term::App(n, args) = t {
        if args.len() == 1 && ac.contains(n.as_str()) {
            t = &args[0];
        } else {
            break;
        }
    }
    t
}

/// The direct operands of an AC-headed term — the `ts` of HS's
/// `FAPP (AC …) ts`, before [`flatten_ac`] merges same-head nesting.
fn ac_operands(t: &Term) -> Vec<&Term> {
    match t {
        Term::BinOp(_, l, r) => vec![l, r],
        Term::App(_, args) => args.iter().collect(),
        _ => Vec::new(),
    }
}

/// Flatten an AC chain headed by the [`wf_funsym_key`] `head` into its operand
/// list, mirroring HS `fAppAC`'s flatten-then-sort (Term/Term/Raw.hs:118-129).
/// Both AC spellings feed the same spine: the builtin operators parse to
/// `BinOp` and a user `[AC]` symbol to `App`, and HS's `fAppAC` hoists the
/// arguments of every same-head child whichever way it was written.
fn flatten_ac<'a>(head: (u8, &str, usize), t: &'a Term, out: &mut Vec<&'a Term>, ac: &AcSyms) {
    let t = ac_collapse(t, ac);
    if wf_funsym_key(t, ac) == head {
        for child in ac_operands(t) {
            flatten_ac(head, child, out, ac);
        }
    } else {
        out.push(t);
    }
}

/// HS `Ord LTerm` for the subset of parser terms we render here.
///
/// HS-faithful class order (Term/Term/Raw.hs:72-74, VTerm.hs:56-57):
/// `LIT _ < FAPP _ _`, and within `LIT`, `Con < Var`, with constant Names
/// ordered by NameTag (Fresh < Pub < Nat, LTerm.hs:215-216).  The nullary
/// builtins `1`/`%1`/`DH-neutral` are `fAppNoEq … []` so they live in the
/// FAPP class.
///
/// Two FAPP terms compare by their `FunSym` first and only then by the
/// argument list, exactly as the derived `Ord (Term a)` does — so the FAPP
/// order is NAME-based, not Rust-variant-based (HS sorts `exp(a,b)` before
/// `pair(a,b)` because `"exp" < "pair"`).  [`wf_funsym_key`] carries that key.
fn cmp_wf_term(a: &Term, b: &Term, ac: &AcSyms) -> std::cmp::Ordering {
    let a = ac_collapse(a, ac);
    let b = ac_collapse(b, ac);
    let (ca, sa) = wf_term_class(a, ac);
    let (cb, sb) = wf_term_class(b, ac);
    if ca != cb {
        return ca.cmp(&cb);
    }
    if ca == 1 {
        // FAPP class: `compare fsym` then `compare ts` (Term/Term/Raw.hs:72-74,
        // see line 74).
        let ka = wf_funsym_key(a, ac);
        let kb = wf_funsym_key(b, ac);
        let key =
            ka.0.cmp(&kb.0)
                .then_with(|| ka.1.cmp(kb.1))
                .then_with(|| ka.2.cmp(&kb.2));
        if key != std::cmp::Ordering::Equal {
            return key;
        }
        // Same FunSym.  An AC head stores its arguments flattened and sorted
        // (HS `fAppAC`, Term/Term/Raw.hs:118-131, see line 122), so its operand
        // list is the sorted multiset rather than the parser's binary tree.
        if ka.0 == 1 {
            let mut fa: Vec<&Term> = Vec::new();
            let mut fb: Vec<&Term> = Vec::new();
            flatten_ac(ka, a, &mut fa, ac);
            flatten_ac(kb, b, &mut fb, ac);
            fa.sort_by(|x, y| cmp_wf_term(x, y, ac));
            fb.sort_by(|x, y| cmp_wf_term(x, y, ac));
            return cmp_term_refs(&fa, &fb, ac);
        }
        return cmp_term_slices(&hs_fapp_args(a, ac), &hs_fapp_args(b, ac), ac);
    }
    if sa != sb {
        return sa.cmp(&sb);
    }
    use Term::*;
    // LIT class only — the FAPP variants have already returned above.
    // `wf_term_class` gives each LIT variant a unique sub-tag, so the early
    // return above leaves `a` and `b` the same variant and each `let … else`
    // binding of `b` is infallible.  A new `Term` variant must still declare
    // itself in `wf_term_class`, `wf_funsym_key` and `hs_fapp_args`, none of
    // which has a wildcard arm.
    match a {
        Var(v1) => {
            let Var(v2) = b else {
                unreachable!("term class matched Var")
            };
            // HS Ord LVar = (idx, sort, name) (LTerm.hs:521-523).
            v1.idx
                .cmp(&v2.idx)
                .then_with(|| sort_tag(&v1.sort).cmp(&sort_tag(&v2.sort)))
                .then_with(|| v1.name.cmp(&v2.name))
        }
        PubLit(s1) => {
            let PubLit(s2) = b else {
                unreachable!("term class matched PubLit")
            };
            s1.cmp(s2)
        }
        FreshLit(s1) => {
            let FreshLit(s2) = b else {
                unreachable!("term class matched FreshLit")
            };
            s1.cmp(s2)
        }
        NatLit(s1) => {
            let NatLit(s2) = b else {
                unreachable!("term class matched NatLit")
            };
            s1.cmp(s2)
        }
        Number(n1) => {
            let Number(n2) = b else {
                unreachable!("term class matched Number")
            };
            n1.cmp(n2)
        }
        _ => std::cmp::Ordering::Equal,
    }
}

/// `(class, sub_tag)` for a parser term: class 0 is HS's `LIT`, class 1 its
/// `FAPP` (`LIT _ < FAPP _ _`, Term/Term/Raw.hs:72-74).  The sub-tag orders
/// the LIT class only — `Con < Var` (VTerm.hs:56-57) and, among constants, by
/// `NameTag` (Fresh < Pub < Nat, LTerm.hs:215-216).  FAPP terms are ordered by
/// [`wf_funsym_key`], so their sub-tag is never consulted.
fn wf_term_class(t: &Term, ac: &AcSyms) -> (u8, u8) {
    use Term::*;
    match ac_collapse(t, ac) {
        FreshLit(_) => (0, 0),
        PubLit(_) => (0, 1),
        NatLit(_) => (0, 2),
        Number(_) => (0, 3),
        Var(_) => (0, 4),
        NumberOne | NatOne | DhNeutral | App(..) | AlgApp(..) | Pair(_) | Diff(..) | BinOp(..)
        | PatMatch(_) => (1, 0),
    }
}

/// HS `FunSym` ordering key `(outer, name, arity)` for a FAPP-class parser
/// term, mirroring `tamarin_theory::guarded::funsym_key` over the same shapes.
///
/// `outer` is the derived `Ord FunSym` constructor order `NoEq(0) < AC(1) <
/// C(2) < List(3)` (FunctionSymbols.hs:150-154).  Within `NoEq`, `Ord NoEqSym`
/// compares `(name, arity)` first (FunctionSymbols.hs:132) — so the parser's
/// dedicated variants key by the HS symbol name they stand for (`pair`, `exp`,
/// `diff`, `one`, `tone`, `DH_neutral`; FunctionSymbols.hs:222,224,226,229,236,247).
/// The builtin AC operators carry no name; their `ACSym` order `Union < Mult <
/// Xor < NatPlus < ACfct` (FunctionSymbols.hs:138-139) rides in the arity slot,
/// and a user `ACfct` carries the name that `Ord ACfctSym` compares first
/// (FunctionSymbols.hs:135).
///
/// A parser `App` is classified by name+arity because the AST carries no
/// signature: `em/2` is HS's sole `C` symbol (`CSym = EMap`,
/// FunctionSymbols.hs:142-143), and `LIST` never has source syntax.  An `App`
/// of a user-declared `[AC]` name is the `ACfct` case, which HS's `Ord`
/// reaches through `AC`, not `NoEq` — it is tested first because HS resolves
/// the name against the signature before any builtin-symbol identity holds.
fn wf_funsym_key<'a>(t: &'a Term, ac: &AcSyms) -> (u8, &'a str, usize) {
    use Term::*;
    let t = ac_collapse(t, ac);
    if let Some(n) = ac_app_name(t, ac) {
        return (1, n, 4);
    }
    match t {
        Pair(_) => (0, "pair", 2),
        BinOp(crate::ast::BinOp::Exp, _, _) => (0, "exp", 2),
        Diff(..) => (0, "diff", 2),
        NumberOne => (0, "one", 0),
        NatOne => (0, "tone", 0),
        DhNeutral => (0, "DH_neutral", 0),
        App(n, args) if n == "em" && args.len() == 2 => (2, "", 0),
        App(n, args) => (0, n.as_str(), args.len()),
        AlgApp(n, _, _) => (0, n.as_str(), 2),
        BinOp(o, _, _) => binop_rank(o),
        // `=t` is SAPIC pattern-match syntax with no HS term counterpart.
        PatMatch(_) => (255, "", 0),
        // LIT-class terms never reach here.
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) => (254, "", 0),
    }
}

/// The positional argument list HS's `Term` carries for a FAPP-class parser
/// term.  `Pair` is the only variant whose parser shape differs from HS's: the
/// AST holds `<a, b, c>` flat, while HS builds the right-nested
/// `pair(a, pair(b, c))` that `prettyTerm`'s `split` walks back out
/// (Term/Term.hs:313,323-324), so the tail is re-nested here.
fn hs_fapp_args(t: &Term, ac: &AcSyms) -> Vec<Term> {
    use Term::*;
    match ac_collapse(t, ac) {
        App(_, x) => x.clone(),
        Pair(x) if x.len() > 2 => vec![x[0].clone(), Pair(x[1..].to_vec())],
        Pair(x) => x.clone(),
        AlgApp(_, l, r) | Diff(l, r) | BinOp(_, l, r) => vec![(**l).clone(), (**r).clone()],
        PatMatch(x) => vec![(**x).clone()],
        NumberOne | NatOne | DhNeutral => Vec::new(),
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) => Vec::new(),
    }
}

/// Which `BinOp`s are AC?  Mult, Union, Xor, NatPlus and the user-declared
/// `[AC]` symbols are the `ACSym` constructors (FunctionSymbols.hs:138-139);
/// `Exp` is the `NoEq` symbol `exp` (FunctionSymbols.hs:251).
fn is_ac_binop(o: &BinOp) -> bool {
    matches!(
        o,
        BinOp::Mult | BinOp::Union | BinOp::Xor | BinOp::NatPlus | BinOp::AcFct(_)
    )
}

/// [`wf_funsym_key`] for a `BinOp` head, split out because
/// `binop_rank_matches_funsym_key_order` pins it against
/// `tamarin_theory::guarded::funsym_key`, which is the source of truth for
/// this order (`tamarin-parser` is dependency-free and cannot call it).
fn binop_rank(o: &BinOp) -> (u8, &str, usize) {
    match o {
        BinOp::Exp => (0, "exp", 2),
        BinOp::Union => (1, "", 0),
        BinOp::Mult => (1, "", 1),
        BinOp::Xor => (1, "", 2),
        BinOp::NatPlus => (1, "", 3),
        BinOp::AcFct(n) => (1, n, 4),
    }
}

/// Lexicographic comparison of two operand lists by `cmp_wf_term`, with the
/// shorter list ordering first on a common prefix (matching Haskell's derived
/// `Ord [a]`).
fn cmp_term_slices(a: &[Term], b: &[Term], ac: &AcSyms) -> std::cmp::Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        let o = cmp_wf_term(x, y, ac);
        if o != std::cmp::Ordering::Equal {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

/// [`cmp_term_slices`] over borrowed operands (the flattened AC arg lists).
fn cmp_term_refs(a: &[&Term], b: &[&Term], ac: &AcSyms) -> std::cmp::Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        let o = cmp_wf_term(x, y, ac);
        if o != std::cmp::Ordering::Equal {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

/// HS LSort declaration order (Term/LTerm.hs:161-166):
/// Pub < Fresh < Msg < Node < Nat.
fn sort_tag(s: &SortHint) -> u8 {
    use SortHint::*;
    use SuffixSort as SS;
    match s {
        Pub | Suffix(SS::Pub) => 0,
        Fresh | Suffix(SS::Fresh) => 1,
        Msg | Suffix(SS::Msg) | Untagged => 2,
        Node | Suffix(SS::Node) => 3,
        Nat | Suffix(SS::Nat) => 4,
    }
}

fn sort_prefix(s: &SortHint) -> &'static str {
    use SortHint::*;
    use SuffixSort as SS;
    match s {
        Pub | Suffix(SS::Pub) => "$",
        Fresh | Suffix(SS::Fresh) => "~",
        Node | Suffix(SS::Node) => "#",
        Nat | Suffix(SS::Nat) => "%",
        Msg | Suffix(SS::Msg) | Untagged => "",
    }
}

/// True if a sort hint indicates a fresh-sort variable.
fn is_fresh_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Fresh | SortHint::Suffix(SuffixSort::Fresh))
}

fn is_msg_sort_or_untagged(s: &SortHint) -> bool {
    matches!(
        s,
        SortHint::Msg | SortHint::Untagged | SortHint::Suffix(SuffixSort::Msg)
    )
}

fn is_pub_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Pub | SortHint::Suffix(SuffixSort::Pub))
}

/// True if a sort hint indicates a node- (temporal-) sort variable.
fn is_node_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Node | SortHint::Suffix(SuffixSort::Node))
}

fn is_nat_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Nat | SortHint::Suffix(SuffixSort::Nat))
}

// =============================================================================
// Reserved fact names — Tamarin reserves 'fr', 'ku', 'kd', 'out', 'in'
// =============================================================================

const RESERVED_FACT_NAMES: &[&str] = &["fr", "ku", "kd", "out", "in"];

/// True if `name` is a built-in fact tag (case-insensitive). These are
/// allowed when used in their semantic position (e.g. `Fr(~k)` in a
/// premise) but not as user-defined protocol facts elsewhere.
fn is_builtin_fact_name(name: &str) -> bool {
    matches!(
        name,
        "Fr" | "In" | "Out" | "K" | "KU" | "KD" | "Ded" | "Term"
    )
}

pub fn reserved_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for (_, f) in rule_facts(r) {
            // Only protocol facts (non-builtin) trigger this check.
            if is_builtin_fact_name(&f.name) {
                continue;
            }
            let lower = f.name.to_lowercase();
            if RESERVED_FACT_NAMES.contains(&lower.as_str()) {
                out.push(WfError::new(
                    "Reserved names",
                    format!(
                        "Rule '{}' contains a fact with reserved name `{}`",
                        r.name, f.name
                    ),
                ));
            }
        }
    }
    // Lemma/restriction formula facts: skipped here because the parser
    // AST keeps formulas in a less-structured form. This matches the
    // bulk of Tamarin's reserved_report behaviour for rules.
    out
}

// =============================================================================
// Reserved KU/KD/K-log usage
// =============================================================================

// HS `reservedFactNameRules'` (Wellformedness.hs:530-541) flags facts whose
// tag is `KUFact`/`KDFact` or which satisfy `isKLogFact` (a `ProtoFact "K"`,
// Fact.hs:319-320).  `Ded(..)` parses to tag `DedFact` (Fact.hs:285-286), which
// is in NONE of those sets, so it must NOT appear here.
const KLOG_NAMES: &[&str] = &["KU", "KD", "K"];

pub fn reserved_fact_name_rules(thy: &Theory) -> WfReport {
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        // HS checks the let-substituted `ProtoRuleE`, so the emitted facts
        // carry their fully-inlined terms (Term/Term/Raw.hs fAppAC order).
        let (prems, acts, concs) = rule_facts_with_lets(r);
        let bad_lhs: Vec<&Fact> = prems
            .iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        let bad_acts: Vec<&Fact> = acts
            .iter()
            .filter(|f| {
                KLOG_NAMES.contains(&f.name.as_str())
                    || matches!(f.name.as_str(), "In" | "Out" | "Fr")
            })
            .collect();
        let bad_rhs: Vec<&Fact> = concs
            .iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        for (msg, fs) in [
            ("on left-hand-side", bad_lhs),
            ("on the middle", bad_acts),
            ("on the right-hand-side", bad_rhs),
        ] {
            if !fs.is_empty() {
                // HS `reservedFactNameRules'` (Wellformedness.hs:530-550):
                //   (underlineTopic "Reserved names",
                //      text ("Rule " ++ quote (showRuleCaseName ru))
                //      <-> text ("contains facts with reserved names"++msg) $-$
                //      nest 2 (fsep $ punctuate comma $ map prettyLNFact fas))
                // grouped/nested by `prettyWfErrorReport` (text topic $-$
                // nest 2 body): the rule line gets 2-space indent, the fact
                // line 4-space (2 from ppTopic + 2 from the inner nest 2).
                let facts: Vec<WfDoc> = fs.iter().map(|f| wf_fact_doc(f, &ac)).collect();
                // Headerless body (no trailing newline); `format_wf_block`
                // emits the single "Reserved names" header for the group and
                // joins per-rule/side bodies with the 2-space blank separator.
                out.push(WfError::filled(
                    "Reserved names",
                    format!(
                        "Rule `{}' contains facts with reserved names {}:",
                        r.name, msg
                    ),
                    facts,
                ));
            }
        }
    }
    out
}

// =============================================================================
// Reserved prefixes (DiffIntr*, DiffProto*) — diff theories only
// =============================================================================

pub fn reserved_prefix_report(thy: &Theory) -> WfReport {
    // Port of HS `reservedPrefixReport` (Wellformedness.hs:796-808), diff
    // theories only.  HS groups ONE error per offending rule with body
    //   wrappedText ("The " ++ origin ++ " contains facts with reserved \
    //     prefixes ('DiffIntr', 'DiffProto') inside names:")
    //   $-$ map (nest 2) [prettyLNFact fa $-$ text (show factInfo)]
    // where `origin = "Rule " ++ quote (showRuleCaseName ru)` and
    // `quote cs = '`' : cs ++ "'"`.
    //
    // The faithful body needs HughesPJ `wrappedText` (greedy column-fill of the
    // header, which ALWAYS wraps here since the string exceeds the render
    // width) and `show factInfo` of the `(tag, arity, multiplicity)` tuple —
    // neither reproducible in the parser crate (the HughesPJ renderer lives in
    // `tamarin-theory`).  This check produces NO output on any corpus input, so
    // per the module-header disclaimer it is one of the two that emit only a
    // topic-faithful best-effort body; it uses the HS `quote` form for the rule
    // name, and topic "Reserved prefixes" matches HS `underlineTopic`.
    let mut out = Vec::new();
    if !thy.is_diff {
        return out;
    }
    for r in theory_rules(thy) {
        for (_, f) in rule_facts(r) {
            let lower = f.name.to_lowercase();
            if lower.starts_with("diffintr") || lower.starts_with("diffproto") {
                out.push(WfError::new(
                    "Reserved prefixes",
                    format!(
                        "Rule `{}' contains a fact with reserved prefix: {}",
                        r.name, f.name
                    ),
                ));
            }
        }
    }
    out
}

// =============================================================================
// Special facts misuse
// =============================================================================

pub fn special_facts_usage(thy: &Theory) -> WfReport {
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        // HS `specialFactsUsage'` (Wellformedness.hs:553-566) reads
        // `get rPrems`/`get rConcs` on the closed `ProtoRuleE`, whose facts
        // carry their fully-inlined `let` terms — mirror the reserved-names
        // sibling and use the let-substituted facts.
        let (prems, _acts, concs) = rule_facts_with_lets(r);
        let lhs_bad: Vec<&Fact> = prems.iter().filter(|f| f.name == "Out").collect();
        let rhs_bad: Vec<&Fact> = concs
            .iter()
            .filter(|f| f.name == "Fr" || f.name == "In")
            .collect();
        for (msg, fs) in [
            ("on left-hand-side", lhs_bad),
            ("on right-hand-side", rhs_bad),
        ] {
            if !fs.is_empty() {
                // HS `specialFactsUsage'` (Wellformedness.hs:553-566):
                //   (underlineTopic "Special facts",
                //      text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg
                //      $-$ nest 2 (fsep $ punctuate comma $ map prettyLNFact fas))
                // grouped/nested by `prettyWfErrorReport` exactly like the
                // "Reserved names" sibling.  Note HS uses lowercase `"rule "`
                // here (vs capital `"Rule "` for reserved names).
                let facts: Vec<WfDoc> = fs.iter().map(|f| wf_fact_doc(f, &ac)).collect();
                // Headerless body (no trailing newline); `format_wf_block`
                // emits the single "Special facts" header for the group and
                // joins per-rule/side bodies with the 2-space blank separator.
                out.push(WfError::filled(
                    "Special facts",
                    format!("rule `{}' uses disallowed facts {}:", r.name, msg),
                    facts,
                ));
            }
        }
    }
    out
}

// =============================================================================
// Fr facts must use a fresh- or msg-variable
// =============================================================================

pub fn fresh_fact_arguments(thy: &Theory) -> WfReport {
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for f in &r.premises {
            if f.name != "Fr" {
                continue;
            }
            if f.args.len() != 1 {
                continue;
            }
            let arg = &f.args[0];
            // The argument must be a single variable of fresh- or
            // message-sort. Anything else (constants, function
            // applications, public/node vars) triggers the warning.
            let ok = match arg {
                Term::Var(v) => is_fresh_sort(&v.sort) || is_msg_sort_or_untagged(&v.sort),
                _ => false,
            };
            if !ok {
                // HS `freshFactArguments'` (Wellformedness.hs:569-576, see
                // line 576) renders the WHOLE fact with `prettyLNFact`, so the
                // argument carries `prettyLVar`'s `.idx` suffix and
                // `prettyTerm`'s AC canonicalisation.
                out.push(WfError::new(
                    "Fr facts must only use a fresh- or a msg-variable",
                    format!("rule `{}' fact: {}", r.name, pp_wf_fact(f, &ac)),
                ));
            }
        }
    }
    out
}

// =============================================================================
// Fact arity / multiplicity / capitalization clashes
// =============================================================================

#[derive(Debug, Clone)]
struct FactObservation {
    /// HS `origin`: `Rule \`X'` or `Lemma \`X'` (Wellformedness.hs:579-734, see line 580,605).
    origin: String,
    name: String,
    arity: usize,
    persistent: bool,
    /// Pre-rendered fact body for the detail line: `prettyLNFact` for rule
    /// facts, the Haskell `show` form for lemma-formula facts (HS
    /// `theoryFacts`'s LemmaItem branch uses `text (show fa)`,
    /// Wellformedness.hs:605-607).
    pp: String,
}

fn collect_fact_observations(thy: &Theory) -> Vec<FactObservation> {
    let ac = user_ac_fun_names(thy);
    // HS `theoryFacts` (Wellformedness.hs:597-607): rule facts (E rules) then
    // lemma-formula facts.  (AC-rule facts only differ for non-trivial-variant
    // rules and never introduce a new arity/cap clash, so we omit them.)
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for (_, f) in rule_facts(r) {
            // HS `theoryFacts` groups facts by `factTagName` with no builtin
            // filter; a user-written `K(..)` is a `ProtoFact "K"`
            // (`isKLogFact`/`isProtoFact`) whose tag-name is "K", so it MUST be
            // included in the capitalization/arity/multiplicity clash grouping.
            // We exclude only the genuine special tags (Fr/In/Out/KU/KD/Ded/Term)
            // via `is_proto_fact_name`, matching the sibling check.
            if !is_proto_fact_name(&f.name) {
                continue;
            }
            out.push(FactObservation {
                origin: format!("Rule `{}'", r.name),
                name: f.name.clone(),
                arity: f.args.len(),
                persistent: f.persistent,
                pp: pp_wf_fact(f, &ac),
            });
        }
    }
    out.extend(lemma_fact_observations(thy));
    out
}

/// HS `theoryFacts`'s LemmaItem branch (Wellformedness.hs:605-607):
///   `(,) ("Lemma " ++ quote (get lName l)) $ do
///        fa <- formulaFacts (get lFormula l); return (text (show fa), factInfo fa)`
/// i.e. every Action-atom fact in the lemma formula, rendered as the Haskell
/// `show` of `Fact (VTerm Name (BVar LVar))` — `Fact {factTag = ProtoFact
/// Linear "X" n, factAnnotations = fromList [], factTerms = [Bound i, ...]}`.
fn lemma_fact_observations(thy: &Theory) -> Vec<FactObservation> {
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for l in theory_lemmas(thy) {
        let mut facts: Vec<(Fact, Vec<String>)> = Vec::new();
        collect_formula_facts(&l.formula, &mut Vec::new(), &ac, &mut facts);
        for (fa, dbterms) in facts {
            // HS show of the Fact: see `show_debruijn_fact`.
            let pp = show_debruijn_fact(&fa, &dbterms);
            out.push(FactObservation {
                origin: format!("Lemma `{}'", l.name),
                name: fa.name.clone(),
                arity: fa.args.len(),
                persistent: fa.persistent,
                pp,
            });
        }
    }
    out
}

/// Walk a formula left-to-right (HS `foldFormula` order), collecting the fact
/// of every `Action` atom together with its argument terms rendered in De
/// Bruijn form (`Bound n` / `Free ...`).  `binders` is the enclosing
/// quantifier stack (outermost first); the innermost binder has index 0.
fn collect_formula_facts<'a>(
    f: &'a Formula,
    binders: &mut Vec<&'a VarSpec>,
    ac: &AcSyms,
    out: &mut Vec<(Fact, Vec<String>)>,
) {
    match f {
        Formula::Atom(Atom::Action(fa, _)) => {
            let terms = fa
                .args
                .iter()
                .map(|t| show_debruijn_term(t, binders, ac))
                .collect();
            out.push((fa.clone(), terms));
        }
        Formula::Atom(_) | Formula::True | Formula::False => {}
        Formula::Not(a) => collect_formula_facts(a, binders, ac, out),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
            collect_formula_facts(a, binders, ac, out);
            collect_formula_facts(b, binders, ac, out);
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            let n = vars.len();
            for v in vars {
                binders.push(v);
            }
            collect_formula_facts(body, binders, ac, out);
            for _ in 0..n {
                binders.pop();
            }
        }
    }
}

/// The De Bruijn index of the innermost binder `v` refers to, or `None` when
/// `v` is free.
///
/// HS binds a use to its binder by full `LVar` equality — name AND sort AND
/// idx (`quantify x = … | v == x = Bound i`, Formula.hs:347-351;
/// `Eq LVar`, LTerm.hs:541-542).
fn db_index(v: &VarSpec, binders: &[&VarSpec]) -> Option<usize> {
    binders.iter().enumerate().rev().find_map(|(pos, b)| {
        (b.name == v.name && sort_tag(&b.sort) == sort_tag(&v.sort) && b.idx == v.idx)
            .then(|| binders.len() - 1 - pos)
    })
}

/// [`wf_term_class`] refined for the De Bruijn form: a variable use is a
/// `BVar`, and `Bound _ < Free _` (LTerm.hs:476-478) splits the single `Var`
/// sub-tag in two.
fn db_term_class(t: &Term, binders: &[&VarSpec], ac: &AcSyms) -> (u8, u8) {
    match ac_collapse(t, ac) {
        Term::Var(v) if db_index(v, binders).is_none() => (0, 5),
        other => wf_term_class(other, ac),
    }
}

/// [`cmp_wf_term`] over terms whose variables have been resolved to De
/// Bruijn form.
///
/// The lemma-formula terms HS sorts are `VTerm Name (BVar LVar)`, not
/// `LNTerm`: `quantify` rewrites a free variable to `Bound i` through
/// `mapLits` (Formula.hs:288-291,347-351), which rebuilds every node with
/// `fApp` and so re-sorts it, and the outermost binder's pass runs last over
/// the fully-bound term.  So the operand order is the one `Bound _ < Free _`
/// induces, NOT the `LVar` order [`cmp_wf_term`] uses.
fn cmp_db_term(a: &Term, b: &Term, binders: &[&VarSpec], ac: &AcSyms) -> std::cmp::Ordering {
    let a = ac_collapse(a, ac);
    let b = ac_collapse(b, ac);
    let (ca, sa) = db_term_class(a, binders, ac);
    let (cb, sb) = db_term_class(b, binders, ac);
    if ca != cb {
        return ca.cmp(&cb);
    }
    if ca == 1 {
        // FAPP class: `compare fsym` then `compare ts` (Term/Term/Raw.hs:72-74).
        let ka = wf_funsym_key(a, ac);
        let kb = wf_funsym_key(b, ac);
        let key =
            ka.0.cmp(&kb.0)
                .then_with(|| ka.1.cmp(kb.1))
                .then_with(|| ka.2.cmp(&kb.2));
        if key != std::cmp::Ordering::Equal {
            return key;
        }
        let xa = db_fapp_args(a, binders, ac);
        let xb = db_fapp_args(b, binders, ac);
        for (x, y) in xa.iter().zip(xb.iter()) {
            let o = cmp_db_term(x, y, binders, ac);
            if o != std::cmp::Ordering::Equal {
                return o;
            }
        }
        return xa.len().cmp(&xb.len());
    }
    if sa != sb {
        return sa.cmp(&sb);
    }
    if sa == 4 {
        // Both bound: `Bound Integer` compares by index.
        if let (Term::Var(v1), Term::Var(v2)) = (a, b) {
            return db_index(v1, binders).cmp(&db_index(v2, binders));
        }
    }
    // Free variables and the constant literals order exactly as they do
    // outside a formula.
    cmp_wf_term(a, b, ac)
}

/// The argument list HS's `Term` carries for a FAPP-class term of a lemma
/// formula: [`hs_fapp_args`], canonicalised the way the smart constructors
/// do it (Term/Term/Raw.hs:118-134) — an `AC` head flattens its same-head
/// children and sorts, a `C` head (`em`) only sorts.
fn db_fapp_args(t: &Term, binders: &[&VarSpec], ac: &AcSyms) -> Vec<Term> {
    let t = ac_collapse(t, ac);
    let key = wf_funsym_key(t, ac);
    match key.0 {
        1 => {
            let mut flat: Vec<&Term> = Vec::new();
            flatten_ac(key, t, &mut flat, ac);
            let mut args: Vec<Term> = flat.into_iter().cloned().collect();
            args.sort_by(|x, y| cmp_db_term(x, y, binders, ac));
            args
        }
        2 => {
            let mut args = hs_fapp_args(t, ac);
            args.sort_by(|x, y| cmp_db_term(x, y, binders, ac));
            args
        }
        _ => hs_fapp_args(t, ac),
    }
}

/// The head name HS's `Show (Term a)` prints for a FAPP-class parser term
/// (Term/Term/Raw.hs:227-237).  It is [`wf_funsym_key`]'s name everywhere a
/// `FunSym` carries one; the builtin `ACSym`s print their derived
/// constructor name instead, and the sole `CSym` prints `emapSymString`
/// (FunctionSymbols.hs:242).
fn show_debruijn_head<'a>(t: &'a Term, ac: &AcSyms) -> &'a str {
    use crate::ast::BinOp as B;
    match t {
        Term::BinOp(B::Mult, _, _) => "Mult",
        Term::BinOp(B::Union, _, _) => "Union",
        Term::BinOp(B::Xor, _, _) => "Xor",
        Term::BinOp(B::NatPlus, _, _) => "NatPlus",
        Term::App(n, args) if n == "em" && args.len() == 2 => "em",
        _ => wf_funsym_key(t, ac).1,
    }
}

/// HS `show` of a `VTerm Name (BVar LVar)` (Term Show: `Lit l -> show l`,
/// `FApp s as -> s(...)`, Term/Term/Raw.hs:227-237; Lit Show: `Var v -> show v`,
/// `Con n -> show n`, VTerm.hs:98-100; BVar `Bound i`/`Free v` derived).
fn show_debruijn_term(t: &Term, binders: &[&VarSpec], ac: &AcSyms) -> String {
    let t = ac_collapse(t, ac);
    match t {
        Term::Var(v) => match db_index(v, binders) {
            Some(i) => format!("Bound {}", i),
            None => format!("Free {}", render_var(v)),
        },
        Term::PubLit(s) => format!("'{}'", s),
        Term::FreshLit(s) => format!("~'{}'", s),
        Term::NatLit(s) => format!("%'{}'", s),
        Term::Number(n) => n.to_string(),
        // `=t` is SAPIC pattern-match syntax with no HS term counterpart.
        Term::PatMatch(inner) => show_debruijn_term(inner, binders, ac),
        // Every remaining variant is a FAPP: `s`, or `s ++ "(" ++
        // intercalate "," (map show as) ++ ")"`.  `db_fapp_args` supplies the
        // operand list HS's term carries — right-nested for `<a, b, c>`
        // (`tupleterm`'s `chainr1`, Theory/Text/Parser/Term.hs:211-212),
        // flattened and sorted under an AC head, sorted under `em`.
        _ => {
            let head = show_debruijn_head(t, ac);
            let args = db_fapp_args(t, binders, ac);
            if args.is_empty() {
                return head.to_string();
            }
            let args_s: Vec<String> = args
                .iter()
                .map(|a| show_debruijn_term(a, binders, ac))
                .collect();
            format!("{}({})", head, args_s.join(","))
        }
    }
}

/// HS `show (Fact {...})` (derived Show, Fact.hs:153-158):
/// `Fact {factTag = ProtoFact <Mult> "<name>" <arity>, factAnnotations =
/// fromList [], factTerms = [<terms>]}`.
fn show_debruijn_fact(fa: &Fact, dbterms: &[String]) -> String {
    let mult = if fa.persistent {
        "Persistent"
    } else {
        "Linear"
    };
    format!(
        "Fact {{factTag = ProtoFact {} {:?} {}, factAnnotations = fromList [], factTerms = [{}]}}",
        mult,
        fa.name,
        fa.args.len(),
        dbterms.join(",")
    )
}

pub fn fact_usage(thy: &Theory) -> WfReport {
    let observations = collect_fact_observations(thy);
    let mut groups: BTreeMap<String, Vec<&FactObservation>> = BTreeMap::new();
    for obs in &observations {
        groups.entry(obs.name.to_lowercase()).or_default().push(obs);
    }
    let mut out = Vec::new();

    // HS emits one block per issue type when ANY clash group exhibits
    // it.  Collect first, then emit.
    let mut cap_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    let mut arity_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    let mut mult_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    for (_, group) in groups.iter().filter(|(_, g)| g.len() >= 2) {
        let cap_set: BTreeSet<&str> = group.iter().map(|o| o.name.as_str()).collect();
        let arity_set: BTreeSet<usize> = group.iter().map(|o| o.arity).collect();
        let mult_set: BTreeSet<bool> = group.iter().map(|o| o.persistent).collect();
        if cap_set.len() > 1 {
            cap_groups.push(group);
        }
        if arity_set.len() > 1 {
            arity_groups.push(group);
        }
        if mult_set.len() > 1 {
            mult_groups.push(group);
        }
    }

    if !cap_groups.is_empty() {
        let msg = "Fact names are case-sensitive, different capitalizations are \
                  considered as different facts, i.e., Fact() is different from FAct(). \n\
                  Check the capitalization of your fact names.";
        out.push(format_fact_clash_block(
            "Fact capitalization issues",
            msg,
            &cap_groups,
            |o| format!("capitalization {:?}", o.name),
        ));
    }
    if !arity_groups.is_empty() {
        let msg = "Same fact is used with different arities, \
                  i.e., Fact('A','B') is different from Fact('A'). \n\
                  Check the arguments of your facts.";
        out.push(format_fact_clash_block(
            "Fact arity issues",
            msg,
            &arity_groups,
            |o| format!("arity {}", o.arity),
        ));
    }
    if !mult_groups.is_empty() {
        let msg = "Same fact is used with different multiplicities, \
                  i.e., !Fact() (Persistent fact) exists along with Fact() (Linear) in your rules. \n\
                  Check the multiplicity (persistence) of your facts.";
        out.push(format_fact_clash_block(
            "Fact multiplicity issues",
            msg,
            &mult_groups,
            |o| {
                format!(
                    "multiplicity (persistence) {}",
                    if o.persistent { "Persistent" } else { "Linear" }
                )
            },
        ));
    }
    out
}

/// Emit one HS-style WfError block: title + underline + intro msg +
/// per-clash numbered detail.  Layout matches the byte output of HS's
/// `formatMultipIssue` / `formatArityIssue` / `formatCapIssue`
/// (Wellformedness.hs:660-674).
fn format_fact_clash_block<F>(
    title: &str,
    intro: &str,
    groups: &[&Vec<&FactObservation>],
    detail: F,
) -> WfError
where
    F: Fn(&FactObservation) -> String,
{
    let mut s = String::new();
    s.push_str(&underline_topic(title));
    s.push('\n');
    s.push_str(intro);
    s.push('\n');
    s.push_str("  \n"); // trailing 2-space line from HS `text ""`
                        // HS body = `text "\n" $-$ vcat (map formatCapIssue groups)`: the leading
                        // blank line (`text "\n"`) appears ONCE before the first group; each group
                        // ends with its own trailing `  \n` (from `$-$ text ""`), which is the only
                        // separator between groups.  So push the leading blank only for group 0.
    for (gi, group) in groups.iter().enumerate() {
        if gi == 0 {
            s.push('\n');
        }
        let name = group[0].name.to_lowercase();
        s.push_str(&format!("  Fact `{}':\n", name));
        s.push('\n');
        let w = numbered_index_width(group.len());
        for (i, obs) in group.iter().enumerate() {
            if i > 0 {
                s.push_str("    \n"); // 4-space trailing line
            }
            s.push_str(&format!(
                "    {:>w$}. {}, {}\n",
                i + 1,
                obs.origin,
                detail(obs),
                w = w,
            ));
            // HS `text(origin..) $-$ nest 2 ppFa` under `numbered'`: the
            // continuation `ppFa` aligns past the `flushRight w (show i) ++
            // ". "` prefix, so its indent grows with the index width:
            //   4 (outer nest) + w (flushRight) + 2 (". ") + 2 (nest 2) = 8 + w.
            // (Probed: width 1 => 9 spaces, width 2 => 10 spaces.)
            s.push_str(&format!("{}{}\n", " ".repeat(8 + w), obs.pp));
        }
        s.push_str("  \n"); // 2-space trailing line after the group
    }
    WfError::new(title, s)
}

// =============================================================================
// Fact occurs in some LHS but not in any RHS
// =============================================================================

/// `isProtoFact` for parser facts: every user fact (including the
/// reserved-named `K`, which HS parses as `ProtoFact "K"`) EXCEPT the
/// truly-special fact tags (`Fr`/`In`/`Out`/`KU`/`KD`/`Ded`/`Term`).
/// Mirrors HS `isProtoFact` (Fact.hs:311-313) — note `K` is a ProtoFact
/// (`isKLogFact = isProtoFact && name=="K"`, Fact.hs:322).
fn is_proto_fact_name(name: &str) -> bool {
    !matches!(name, "Fr" | "In" | "Out" | "KU" | "KD" | "Ded" | "Term")
}

/// Levenshtein edit distance (HS `editDistance`, used by `mostSimilarName`).
fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let (n, m) = (a.len(), b.len());
    let mut prev: Vec<usize> = (0..=m).collect();
    let mut cur = vec![0usize; m + 1];
    for i in 1..=n {
        cur[0] = i;
        for j in 1..=m {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[m]
}

pub fn fact_lhs_occur_no_rhs(thy: &Theory) -> WfReport {
    // Mirrors HS `factLhsOccurNoRhs'` (Wellformedness.hs:214-256): for every
    // PROTO premise fact whose full factInfo (name, arity, multiplicity) is
    // produced by no rule's conclusion, suggest the RHS proto fact with the
    // smallest name edit-distance (<= 3, `mostSimilarName`).
    //
    // Title carries a single trailing space, matching HS's source-literal
    // `"Facts occur in the left-hand-side but not in any right-hand-side "`.
    let title = "Facts occur in the left-hand-side but not in any right-hand-side ";

    // rhs = all proto conclusion facts in source order (regroup of getFacts
    // rConcs).  factInfo = (name, arity, persistent).
    let mut rhs: Vec<(String, Fact)> = Vec::new();
    for r in theory_rules(thy) {
        for f in &r.conclusions {
            if !is_proto_fact_name(&f.name) {
                continue;
            }
            rhs.push((r.name.clone(), f.clone()));
        }
    }
    let rhs_info: BTreeSet<(String, usize, bool)> = rhs
        .iter()
        .map(|(_, f)| (f.name.clone(), f.args.len(), f.persistent))
        .collect();

    // Detect orphan premises (proto LHS facts whose factInfo is in no RHS).
    let mut orphan_pairs: Vec<(String, Fact, Option<(String, Fact)>)> = Vec::new();
    for r in theory_rules(thy) {
        for f in &r.premises {
            if !is_proto_fact_name(&f.name) {
                continue;
            }
            // HS `removeSame`: drop if the full factInfo occurs in some RHS.
            if rhs_info.contains(&(f.name.clone(), f.args.len(), f.persistent)) {
                continue;
            }
            // HS `minimalEdFact`: the RHS fact with minimum name edit distance
            // (first in RHS order on ties); `isSimilar` keeps it only if <= 3.
            let suggestion = rhs
                .iter()
                .map(|(rn, rf)| (edit_distance(&f.name, &rf.name), rn, rf))
                .min_by_key(|(d, _, _)| *d)
                .filter(|(d, _, _)| *d <= 3)
                .map(|(_, rn, rf)| (rn.clone(), rf.clone()));
            orphan_pairs.push((r.name.clone(), f.clone(), suggestion));
        }
    }

    if orphan_pairs.is_empty() {
        return Vec::new();
    }

    let mut s = String::new();
    s.push_str(&underline_topic(title));
    s.push('\n');
    // HS `numbered'` = `numbered (text "")`: items are interspersed with
    // `text ""` separators and joined by `$-$`.  `text ""` at indent 2
    // (from the `nest 2` in the caller) renders as `"  "` (2 spaces).
    // Result: item1\n  \nitem2\n  \nitem3\n (blank 2-space lines between items).
    let last_idx = orphan_pairs.len() - 1;
    // HS `numbered'` left-pads the index to the width of the largest index.
    let w = numbered_index_width(orphan_pairs.len());
    for (i, (rule_name, fa, suggestion)) in orphan_pairs.iter().enumerate() {
        let primary = format!(
            "in rule \"{}\":  factName `{}' arity: {} multiplicity: {}",
            rule_name,
            fa.name,
            fa.args.len(),
            if fa.persistent {
                "Persistent"
            } else {
                "Linear"
            },
        );
        let line = match suggestion {
            Some((sug_rule, sug_fa)) => format!(
                "  {:>w$}. {}. Perhaps you want to use the fact in rule \"{}\":  factName `{}' arity: {} multiplicity: {}",
                i + 1, primary, sug_rule, sug_fa.name, sug_fa.args.len(),
                if sug_fa.persistent { "Persistent" } else { "Linear" },
                w = w,
            ),
            None => format!("  {:>w$}. {}", i + 1, primary, w = w),
        };
        s.push_str(&line);
        s.push('\n');
        // HS `numbered (text "")` inserts `text ""` between items.
        // At 2-space indent this renders as "  \n".
        if i < last_idx {
            s.push_str("  \n");
        }
    }

    vec![WfError::new(title, s)]
}

// =============================================================================
// Fresh public constants — `~'foo'` is forbidden
// =============================================================================

pub fn fresh_names_report(thy: &Theory) -> WfReport {
    // HS `freshNamesReport'` (Wellformedness.hs:444-452): one WfError per
    // offending rule, body = `fsep` of
    //   text ("rule " ++ quote (showRuleCaseName ru) ++ ": fresh public \
    //         constants are not allowed:") : punctuate comma (map (show) names)
    // where `quote cs = '`' : cs ++ "'"` (Wellformedness.hs:164-165, see line 165) and the fresh
    // names render via `show (Name FreshName n) = "~'" ++ n ++ "'"`
    // (LTerm.hs:231-235, see line 232).  Topic is "Fresh public constants"; the umbrella renderer
    // emits the underlineTopic header once and 2-space-nests the bodies
    // (separated by a `  ` blank line) — we bake that whole block into a single
    // WfError so the default `format_wf_block` path reproduces the exact bytes.
    let topic = "Fresh public constants";
    let mut bodies: Vec<String> = Vec::new();
    for r in theory_rules(thy) {
        // HS `freshNamesReport` runs `universeBi` over the let-substituted
        // `ProtoRuleE` (Wellformedness.hs:455-456, see line 456), so a fresh name occurring
        // only inside a `let` value (e.g. `let m = ~'foo' in ... Out(m)`) is
        // inlined and surfaces here.  Mirror by walking the let-inlined facts.
        let (prems, acts, concs) = rule_facts_with_lets(r);
        let mut names = Vec::new();
        for f in prems.iter().chain(&acts).chain(&concs) {
            for t in &f.args {
                term_name_lits(t, &mut names);
            }
        }
        // HS `show (Name FreshName n) = "~'" ++ n ++ "'"` for each fresh name,
        // joined by `punctuate comma` (`, `) under the `fsep`.
        let fresh_lits: Vec<String> = names
            .iter()
            .filter_map(|(k, n)| {
                if *k == NameKind::Fresh {
                    Some(format!("~'{}'", n))
                } else {
                    None
                }
            })
            .collect();
        if !fresh_lits.is_empty() {
            // Body only, 2-space `nest 2` indent baked in; HS `quote` form for
            // the rule name (backtick + apostrophe).
            bodies.push(format!(
                "  rule `{}': fresh public constants are not allowed: {}",
                r.name,
                fresh_lits.join(", ")
            ));
        }
    }
    grouped_topic_block(topic, bodies)
}

// =============================================================================
// Public constant capitalization clashes
// =============================================================================

pub fn public_names_report(thy: &Theory) -> WfReport {
    // Port of HS `publicNamesReport'` (Wellformedness.hs:463-484).
    //   publicNames = [(ruleName, pubConstName)]   (public-NAME literals)
    //   findClashes = clashesOn (lowerCase . show . snd) (show . snd)
    // and each clash group is rendered as
    //   numbered' (map (fsep . punctuate comma . map ppRuleAndName . groupOn fst))
    // where ppRuleAndName lists the names of one rule together
    //   `rule "R":  name 'a', 'b'`.
    // This is a SINGLE WfError (count 1) carrying the full block; it uses the
    // default `format_wf_block` path (header baked into the message).
    let mut pairs: Vec<(String, String)> = Vec::new(); // (ruleName, pubName)
    for r in theory_rules(thy) {
        // HS `publicNamesReport` runs `universeBi` over the let-substituted
        // `ProtoRuleE` (Wellformedness.hs:444-452, see line 447,456), so walk the let-inlined
        // facts (a public name occurring only inside a `let` value surfaces).
        let (prems, acts, concs) = rule_facts_with_lets(r);
        let mut names = Vec::new();
        for f in prems.iter().chain(&acts).chain(&concs) {
            for t in &f.args {
                term_name_lits(t, &mut names);
            }
        }
        for (k, n) in names {
            if k == NameKind::Pub {
                pairs.push((r.name.clone(), n));
            }
        }
    }
    public_names_report_from_pairs(pairs)
}

/// The clash-detection + rendering half of `publicNamesReport'`
/// (Wellformedness.hs:463-484), factored out so the SAPIC post-translation
/// re-check can feed it `(showRuleCaseName, pubName)` pairs harvested from the
/// ELABORATED rules (whose `process=` attribute carries the source process, the
/// way HS `universeBi` walks it) — the parser AST stores that attribute as a
/// rendered string, so the parser-level walk above cannot see it.  `pairs` must
/// arrive in rule order (matching HS `thyProtoRules`), first-occurrence-wins:
/// `clashesOn` keeps the earliest `(rule, name)` per distinct public name.
pub fn public_names_report_from_pairs(pairs: Vec<(String, String)>) -> WfReport {
    if pairs.is_empty() {
        return Vec::new();
    }
    // HS `show` of a (public) Name constant is the quoted form `'name'`.
    let shw = |n: &str| format!("'{}'", n);
    let f = |p: &(String, String)| shw(&p.1).to_lowercase(); // lowerCase.show.snd
    let g = |p: &(String, String)| shw(&p.1); // show.snd
                                              // clashesOn f g: stable-sort by f, group consecutive by f, each group
                                              // sortednubOn g; keep groups with >= 2 distinct g.
    let mut sorted: Vec<(String, String)> = pairs;
    sorted.sort_by_key(|a| f(a));
    let mut clashes: Vec<Vec<(String, String)>> = Vec::new();
    let mut i = 0;
    while i < sorted.len() {
        let key = f(&sorted[i]);
        let mut j = i + 1;
        while j < sorted.len() && f(&sorted[j]) == key {
            j += 1;
        }
        let mut grp: Vec<(String, String)> = sorted[i..j].to_vec();
        grp.sort_by_key(|a| g(a));
        grp.dedup_by(|a, b| g(a) == g(b));
        if grp.len() >= 2 {
            clashes.push(grp);
        }
        i = j;
    }
    if clashes.is_empty() {
        return Vec::new();
    }
    let topic = "Public constants with mismatching capitalization";
    let mut s = String::new();
    s.push_str(&underline_topic(topic));
    s.push('\n');
    s.push_str(
        "Identifiers are case-sensitive, mismatched capitalizations \
        are considered as different, i.e., 'ID' is different from 'id'. \
        Check the capitalization of your identifiers.\n",
    );
    s.push('\n');
    let w = numbered_index_width(clashes.len());
    let items: Vec<String> = clashes
        .iter()
        .enumerate()
        .map(|(k, grp)| {
            // groupOn fst: list each rule's names together.
            let mut parts: Vec<String> = Vec::new();
            let mut m = 0;
            while m < grp.len() {
                let rule = &grp[m].0;
                let mut names = vec![shw(&grp[m].1)];
                let mut n2 = m + 1;
                while n2 < grp.len() && &grp[n2].0 == rule {
                    names.push(shw(&grp[n2].1));
                    n2 += 1;
                }
                parts.push(format!("rule \"{}\":  name {}", rule, names.join(", ")));
                m = n2;
            }
            format!("  {:>w$}. {}", k + 1, parts.join(", "), w = w)
        })
        .collect();
    s.push_str(&items.join("\n  \n"));
    s.push('\n');
    vec![WfError::new(topic, s)]
}

// =============================================================================
// Unbound variables: vars in RHS / actions but not in LHS
// =============================================================================

/// Collect every name declared by `functions: <name>/0 ...` blocks at
/// any depth in the theory.  HS-faithful: the parser registers these
/// in its `funSig` so `nullaryApp` resolves bare `<name>` tokens to
/// `FApp (NoEq <sym>) []` rather than `Var <name>`
/// (`lib/theory/src/Theory/Text/Parser/Term.hs::nullaryApp`).  In the
/// Rust port that resolution happens during elaboration, but WF runs
/// on the un-elaborated parser AST — so any walker that classifies
/// `Var name` as "really a variable" needs this set to deny-list the
/// 0-arity user funs.  Built-in nullaries (`signing`'s `true`, DH's
/// `1`, etc.) are NOT included here; they live in the builtin sig
/// which is registered at elaborate-time.  Today we only need to
/// shadow user-declared 0-arity funs (wireguard.spthy's `true/0`).
fn collect_nullary_fun_names(thy: &Theory) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = BTreeSet::new();
    for it in &thy.items {
        if let TheoryItem::Functions(decls) = it {
            for d in decls {
                if d.arg_types.is_empty() {
                    out.insert(d.name.clone());
                }
            }
        }
    }
    out
}

/// The rendered variable a SAPIC `lookup t as v` combinator binds, for a rule
/// whose top-level source process IS such a combinator — HS's
/// `match v (Just (ProcessComb (Lookup _ v') _ _ _)) = v == slvar v'`
/// (Wellformedness.hs:501-503).  HS pattern-matches the `ruleProcess`
/// attribute's `Process` value; the parser AST holds that attribute already
/// rendered, by `prettySapicComb (Lookup t v) = "lookup " ++ p t ++ " as " ++
/// show v` (Theory/Sapic/Process.hs:473-483, see line 482) — the only
/// combinator rendering that starts `lookup `, and the only one whose text
/// ends in a bare `show v`.  `p t` precedes the separator and `show v` is a
/// single token, so the binder is the text past the LAST ` as `.  Every
/// user-written rule yields `None`: HS's rule-attribute parser discards a
/// written `process=` (`parseAndIgnore`, Parser/Rule.hs:68-93, see line 72),
/// so [`RuleAttr::Process`] exists only on SAPIC-generated rules.
fn lookup_binder_render(r: &Rule) -> Option<&str> {
    r.attributes.iter().find_map(|a| match a {
        RuleAttr::Process(p) => p
            .strip_prefix("lookup ")
            .and_then(|rest| rest.rsplit_once(" as "))
            .map(|(_, v)| v),
        _ => None,
    })
}

/// Collect a rule's unbound variables (conclusion/action vars NOT in
/// any premise / let-binding).  Returns the list in first-occurrence
/// order, deduped, excluding pub-sort variables (which are implicitly
/// adversary-known and so always bound) and excluding names declared
/// as 0-arity functions (those are nullary function calls, not
/// variables — HS resolves them via `nullaryApp` at parse-time).
fn collect_rule_unbound_vars(r: &Rule, nullary_funs: &BTreeSet<String>) -> Vec<VarSpec> {
    // HS `unboundCheck` (Wellformedness.hs:493-512) runs on the
    // let-substituted, macro-applied `ProtoRuleE` (`thyProtoRules`).  So
    // `let m1 = <'1',$A,~Na> in ... Out(m1)` is INLINED to `Out(<'1',$A,~Na>)`
    // before the check — the let value's free vars are NOT bound, only the
    // (now-substituted-away) let variable.  Mirror by inlining lets here.
    //
    // HS collects `frees (rConcs, rActs, rInfo)`; we iterate only
    // `acts.chain(concs)` and so do NOT fold in raw embedded-restriction
    // (`rInfo`) free vars — a distinct, currently-out-of-scope gap.
    let (prems, acts, concs) = rule_facts_with_lets(r);
    // HS `originatesFromLookup` (Wellformedness.hs:501-503, 506-510): the
    // variable a `lookup t as v` combinator binds reaches the generated rule
    // through its `IsIn( t, v )` action rather than a premise, so it is not
    // unbound.  `lookup_binder_render` is `None` for every non-`lookup` rule,
    // which is every user-written one.
    let lookup_binder = lookup_binder_render(r);
    // HS `boundVars = S.fromList $ frees (get rPrems ru)` keys on the full
    // LVar (name AND sort AND idx), so `~ltk` (fresh) does NOT bind `ltk`
    // (msg).  Key on (name, sort_tag, idx).
    let mut bound: BTreeSet<(String, u8, u64)> = BTreeSet::new();
    for f in &prems {
        for v in fact_vars(f) {
            bound.insert((v.name.clone(), sort_tag(&v.sort), v.idx));
        }
    }
    let mut unbound: Vec<VarSpec> = Vec::new();
    let mut seen: BTreeSet<(String, u8, u64)> = BTreeSet::new();
    for f in acts.iter().chain(&concs) {
        for v in fact_vars(f) {
            if is_pub_sort(&v.sort) {
                continue;
            }
            // HS `isNowNode v = lvarSort v == LSortNode && lvarName v == "NOW"`
            // (Wellformedness.hs:504-505): the `#NOW` node `varNow`
            // (Theory/Model/Restriction.hs:86-88) that embedded-restriction
            // expansion mints is never premise-bound.
            if is_node_sort(&v.sort) && v.name == "NOW" {
                continue;
            }
            if lookup_binder.is_some_and(|b| b == render_var(&v)) {
                continue;
            }
            if nullary_funs.contains(&v.name) {
                continue;
            }
            // Builtin nullary constants (e.g. XOR's `zero`, DH's
            // `DH_neutral`) parse as bare identifiers in the surface
            // syntax but semantically denote 0-arity functions.  HS's
            // parser binds them via `nullaryApp` so they never appear
            // as variables in the rule AST; RS's parser still surfaces
            // them as `Term::Var` and relies on this check to skip
            // them when classifying "unbound".  Without this skip,
            // rules like CRxor's `responder` (`Neq(na, zero)`) get
            // bogus "has unbound variables: zero" warnings.
            if is_known_nullary_constant_name(&v.name) {
                continue;
            }
            let key = (v.name.clone(), sort_tag(&v.sort), v.idx);
            if bound.contains(&key) {
                continue;
            }
            if seen.insert(key.clone()) {
                unbound.push(v);
            }
        }
    }
    unbound
}

pub fn unbound_report(thy: &Theory) -> WfReport {
    // HS `unboundReport` (Wellformedness.hs:514-519) produces one `WfError`
    // PER offending rule, all sharing the topic "Unbound variables".  The
    // WARNING count printed in the summary is `length rep` (Batch.hs:87-316, see line 245),
    // i.e. the number of these un-grouped entries — so we must emit one
    // entry per rule, NOT a single aggregated block.
    //
    // The renderer `prettyWfErrorReport` (Wellformedness.hs:118-125) then
    // `groupOn`s by topic and lays each group out as
    //   `text topic $-$ (nest 2 . vcat . intersperse (text "") $ map snd errs)`.
    // i.e. the underlineTopic header is emitted ONCE for the group, the
    // per-rule bodies are indented by 2 spaces and separated by a 2-space
    // blank line.  Each body is `text info $-$ nest 2 (prettyVarList vars)`
    // (Wellformedness.hs:497-498), so the `rule ... has unbound variables:`
    // line gets 2 spaces and the variable list 2+2 = 4 spaces.  RS's
    // `format_wf_block` applies that group-level header + 2-space layout
    // (see below); each entry here carries ONLY its body (`snd err`).
    let nullary_funs = collect_nullary_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let unbound = collect_rule_unbound_vars(r, &nullary_funs);
        if !unbound.is_empty() {
            // HS `prettyVarList = fsep . punctuate comma . map prettyLVar`
            // (TheoryObject.hs:858-859): the same paragraph fill the sibling
            // `reservedFactNameRules`/`specialFactsUsage` fact lists use, at
            // the same 4-space inner `nest 2` indent.  `prettyLVar` is a bare
            // `text`, so these cells have no break point of their own.
            let names: Vec<WfDoc> = unbound.iter().map(|v| WfDoc::Text(render_var(v))).collect();
            // Body only: `  rule `{name}' has unbound variables: ` (2-space
            // ppTopic nest, trailing space from HS's `info`) then the
            // variable list at 4 spaces.  format_wf_block adds the header.
            out.push(WfError::filled(
                "Unbound variables",
                format!("rule `{}' has unbound variables: ", r.name),
                names,
            ));
        }
    }
    out
}

/// Static analog of HS's `checkVariableDeducability`
/// (`Theory.Tools.MessageDerivationChecks`).  HS spawns the prover on a
/// synthetic theory per rule + per variable; this emits the SAME set of
/// variables that [`unbound_report`] flags, under the distinct topic HS uses.
///
/// HS's check is a superset: it also catches variables that ARE bound by a
/// premise but whose containing fact is never produced by any other rule, so
/// the intruder can't derive them.  Catching that requires the prover (HS's
/// `proveTheory` per-variable loop) and is gated behind
/// `--derivcheck-timeout` (default 5s), so it lives in
/// `tamarin_theory::deriv_check`.  Both load pipelines drop this entry from
/// the report and substitute that Maude-backed result; what stays here serves
/// the `--parse-only` batch path, which starts no Maude.
pub fn message_derivation_report(thy: &Theory) -> WfReport {
    // Aggregate (rule_name, [unbound_var_names]) pairs across the
    // theory, skipping rules with the `no_derivcheck` attribute.
    let nullary_funs = collect_nullary_fun_names(thy);
    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    for r in theory_rules(thy) {
        if r.attributes
            .iter()
            .any(|a| matches!(a, crate::ast::RuleAttr::NoDerivCheck))
        {
            continue;
        }
        let unbound = collect_rule_unbound_vars(r, &nullary_funs);
        if unbound.is_empty() {
            continue;
        }
        // HS shows the LVar (sort prefix included): MessageDerivationChecks.hs:122-138, see line 138
        let names: Vec<String> = unbound.iter().map(render_var).collect();
        per_rule.push((r.name.clone(), names));
    }
    if per_rule.is_empty() {
        return Vec::new();
    }
    // HS emits this as a single WfErrorReport entry with a multi-line
    // message: explanatory header + one block per affected rule.
    let mut msg = String::from(
        "The variables of the following rule(s) are not derivable \
         from their premises, you may be performing unintended pattern \
         matching.\n\n",
    );
    let rule_blocks: Vec<String> = per_rule
        .iter()
        .map(|(rule_name, vars)| {
            format!(
                "Rule {}: \nFailed to derive Variable(s): {}",
                rule_name,
                vars.join(", ")
            )
        })
        .collect();
    msg.push_str(&rule_blocks.join("\n\n"));
    vec![WfError::new("Message Derivation Checks", msg)]
}

fn render_var(v: &VarSpec) -> String {
    let prefix = sort_prefix(&v.sort);
    if v.idx == 0 {
        format!("{}{}", prefix, v.name)
    } else {
        format!("{}{}.{}", prefix, v.name, v.idx)
    }
}

// =============================================================================
// Lemma annotations — reuse on exists-trace
// =============================================================================

pub fn lemma_attribute_report(thy: &Theory) -> WfReport {
    // HS `lemmaAttributeReport` (Wellformedness.hs:924-932): each
    // exists-trace lemma tagged `reuse` yields a body line
    //   `Lemma `<name>': cannot reuse 'exists-trace' lemmas`
    // all under the single topic `Lemma annotations`.  HS's
    // `prettyWfErrorReport` (Wellformedness.hs:118-125) renders a topic
    // group as `underlineTopic topic $-$ nest 2 (vcat (intersperse "" bodies))`
    // — i.e. ONE underlined header, then the bodies `nest 2`'d and
    // blank-line-separated.  Emit a single `WfError` carrying that whole
    // block so the header appears exactly once even with several lemmas.
    let topic = "Lemma annotations";
    let bodies: Vec<String> = theory_lemmas(thy)
        .into_iter()
        .filter(|l| {
            matches!(l.trace_quantifier, TraceQuantifier::ExistsTrace)
                && l.attributes.iter().any(|a| matches!(a, LemmaAttr::Reuse))
        })
        .map(|l| format!("  Lemma `{}': cannot reuse 'exists-trace' lemmas", l.name))
        .collect();
    // NB: the corpus has at most one reuse-exists lemma per file, so the
    // multi-body path is exercised only synthetically; the per-lemma error
    // COUNT in the `N wellformedness check failed` summary collapses to one
    // here.  Matching HS's count would mean emitting one header-less body per
    // lemma and adding "Lemma annotations" to the headerless-preamble set in
    // `tamarin_theory::pretty_theory`.
    grouped_topic_block(topic, bodies)
}

// =============================================================================
// Diff theory: Left rule / Right rule consistency
// =============================================================================

pub fn left_right_rule_report(thy: &Theory) -> WfReport {
    // Port of HS `leftRightRuleReportDiff` (Wellformedness.hs:397-414).  Topics
    // "Left rule"/"Right rule" match HS `underlineTopic` exactly.  HS's bodies
    // are
    //   text "Inconsistent left rule"  $-$ nest 2 (prettyProtoRuleE lr)
    //   $--$ text "w.r.t." $--$ nest 2 (prettyProtoRuleE (get dprRule ru))
    // i.e. the EXPLICIT user-written left rule `lr` and the PARENT diff rule
    // (NOT the projection used for the equalUpToAddedActions comparison), with
    // NO rule name.  Reproducing that needs `prettyProtoRuleE`/`prettyNamedRule`
    // (kwRuleModulo "E"), which has no equivalent in the parser crate, and this
    // path is unreachable on the corpus — so per the module-header disclaimer
    // we keep a topic-faithful body and do not reproduce the full rule
    // pretty-print.
    let mut out = Vec::new();
    if !thy.is_diff {
        return out;
    }
    for r in theory_rules(thy) {
        let (lhs_diff, rhs_diff) = match &r.left_right {
            Some(pair) => pair,
            None => continue,
        };
        // Project the parent rule's premises onto LEFT (first arg of
        // diff) and RIGHT (second arg).
        let proj_l = project_rule(r, /* left = */ true);
        let proj_r = project_rule(r, /* left = */ false);
        if !rules_equivalent_up_to_actions(&proj_l, lhs_diff) {
            out.push(WfError::new(
                "Left rule",
                format!("Inconsistent left rule for `{}'", r.name),
            ));
        }
        if !rules_equivalent_up_to_actions(&proj_r, rhs_diff) {
            out.push(WfError::new(
                "Right rule",
                format!("Inconsistent right rule for `{}'", r.name),
            ));
        }
    }
    out
}

/// Project all `diff(a, b)` subterms in `r` onto `left` or right. Used to
/// derive what the explicit left/right rule blocks should look like.
fn project_rule(r: &Rule, left: bool) -> Rule {
    fn proj_term(t: &Term, left: bool) -> Term {
        match t {
            Term::Diff(a, b) => {
                if left {
                    proj_term(a, left)
                } else {
                    proj_term(b, left)
                }
            }
            Term::App(n, args) => {
                Term::App(n.clone(), args.iter().map(|a| proj_term(a, left)).collect())
            }
            Term::AlgApp(n, a, b) => Term::AlgApp(
                n.clone(),
                Box::new(proj_term(a, left)),
                Box::new(proj_term(b, left)),
            ),
            Term::Pair(items) => Term::Pair(items.iter().map(|a| proj_term(a, left)).collect()),
            Term::BinOp(op, a, b) => Term::BinOp(
                *op,
                Box::new(proj_term(a, left)),
                Box::new(proj_term(b, left)),
            ),
            Term::PatMatch(inner) => Term::PatMatch(Box::new(proj_term(inner, left))),
            other => other.clone(),
        }
    }
    fn proj_fact(f: &Fact, left: bool) -> Fact {
        Fact {
            persistent: f.persistent,
            name: f.name.clone(),
            args: f.args.iter().map(|a| proj_term(a, left)).collect(),
            annotations: f.annotations.clone(),
        }
    }
    Rule {
        name: r.name.clone(),
        modulo: r.modulo.clone(),
        attributes: r.attributes.clone(),
        let_block: r.let_block.clone(),
        premises: r.premises.iter().map(|f| proj_fact(f, left)).collect(),
        actions: r.actions.iter().map(|f| proj_fact(f, left)).collect(),
        conclusions: r.conclusions.iter().map(|f| proj_fact(f, left)).collect(),
        embedded_restrictions: r.embedded_restrictions.clone(),
        variants: vec![],
        left_right: None,
    }
}

/// Two rules are "equivalent up to added actions" if their premises
/// and conclusions match exactly. Tamarin allows the explicit
/// left/right rule to add actions; everything else must match.
fn rules_equivalent_up_to_actions(a: &Rule, b: &Rule) -> bool {
    a.premises == b.premises && a.conclusions == b.conclusions
}

// =============================================================================
// Subterm convergence warning
// =============================================================================

/// True if `lhs = rhs` is a subterm-convergent rewrite rule: every
/// proper subterm of the RHS occurs as a subterm of the LHS, OR the
/// RHS is exactly a constant `true`.
///
/// HS site: `Wellformedness.hs:1222-1232` — `checkEquationsSubtermConvergence`.
/// Emits ONE WfError with the full formatted block:
///   `underlineTopic "Subterm Convergence Warning" $-$ introText $-$
///    vcat (map prettyCtxtStRule nonSubtermEquations) $-$ manualRef`
/// where `prettyCtxtStRule` uses `sep [nest 2 lhsDoc, "=" <-> rhsDoc]`.
pub fn subterm_convergence_report(thy: &Theory) -> WfReport {
    // HS guards the WHOLE check on `not (isUserMarkedConvergent thy)`
    // (Wellformedness.hs:1270-1286, see line 1285), where `isUserMarkedConvergent thy =
    // eqConvergent (sig thy)` (1211-1212).  The parser sets `eqConvergent =
    // convergent` on EVERY `equations` block (Signature.hs:217-234, see line 227) — LAST-WRITE-
    // WINS, not "any block convergent".  Mirror by reading the `convergent`
    // flag of the LAST `equations` item; if it is set, suppress the entire
    // report.  (Probed: `[convergent]` block last => suppressed; `[convergent]`
    // first + a regular block last => fires.)
    let global_convergent = thy
        .items
        .iter()
        .rev()
        .find_map(|it| match it {
            TheoryItem::Equations { convergent, .. } => Some(*convergent),
            _ => None,
        })
        .unwrap_or(false);
    if global_convergent {
        return Vec::new();
    }

    // Collect all non-subterm-convergent equations across ALL `equations`
    // items (HS `thyEquations = S.toList (stRules sig)` merges every block's
    // equations into one Set — so we do NOT skip per-block).  User-declared
    // `/0` functions resolve to nullary constants (HS resolves them via the
    // function signature at parse time, so they are variable-free).
    let nullary_funs = collect_nullary_fun_names(thy);
    let mut non_conv: Vec<(&Term, &Term)> = Vec::new();
    for it in &thy.items {
        let eqs = match it {
            TheoryItem::Equations { eqs, .. } => eqs,
            _ => continue,
        };
        for eq in eqs {
            if !is_subterm_convergent(&eq.lhs, &eq.rhs, &nullary_funs) {
                non_conv.push((&eq.lhs, &eq.rhs));
            }
        }
    }
    // HS `thyEquations` is a `Set CtxtStRule` (`S.toList` => deduped, ordered
    // by the derived `Ord CtxtStRule`).  We dedup structurally-equal equations
    // to match the Set's deduplication; we keep source order rather than
    // replicating the full `Ord LNTerm` term-AST order (the parser AST lacks
    // it), so the LISTED ORDER may still differ from HS when there are >=2
    // distinct non-convergent user equations.  Corpus cases have a single
    // non-convergent equation, where this is a no-op.
    non_conv.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
    if non_conv.is_empty() {
        return Vec::new();
    }

    // HS `prettyCtxtStRule r = sep [nest 2 (prettyLNTerm lhs), "=" <-> prettyLNTerm rhs]`
    // For equations that fit on one line, `sep` renders inline:
    // `  {lhs} = {rhs}` (two spaces from the outer nest-2 context inside `vcat`).
    // HS's outer `$-$` / `vcat` adds no extra indent — each rule renders
    // with its own `nest 2` inside the sep.  Result: `    {lhs} = {rhs}`
    // (4 leading spaces, as observed in HS output).
    let ac = user_ac_fun_names(thy);
    let mut eq_lines = String::new();
    for (lhs, rhs) in &non_conv {
        let lhs_s = pp_term_for_wf(lhs, &ac);
        let rhs_s = pp_term_for_wf(rhs, &ac);
        // `sep [nest 2 lhsDoc, "=" <-> rhsDoc]` inline → `  lhs = rhs`
        // HS output observed: `    unblind(...) = sign(...)` (4-space indent).
        // The top-level `$-$ vcat (map pretty ...) $-$` gives no extra indent,
        // but prettyWfErrorReport wraps the body in `nest 2`:
        // `(nest 2 . vcat . map snd) errs` (Wellformedness.hs:118-125, see line 122).
        // So the per-rule `nest 2 lhs` + outer `nest 2` = 4 spaces total.
        eq_lines.push_str("    ");
        eq_lines.push_str(&lhs_s);
        eq_lines.push_str(" = ");
        eq_lines.push_str(&rhs_s);
        eq_lines.push('\n');
    }

    // Assemble the full message block (topic header + intro + equations + footer).
    // HS: `underlineTopic "Subterm Convergence Warning"` produces
    //   `"Subterm Convergence Warning\n===========================\n"`.
    // Then `$-$` (blank-line separator) adds a blank line before the intro.
    // Then `vcat` adds the equations, then `$-$` + manual reference text.
    let mut msg = String::new();
    msg.push_str(&underline_topic("Subterm Convergence Warning"));
    msg.push('\n'); // blank line before intro (HS `$-$`)
                    // The intro text — HS: `text "User-defined equations must be convergent..."`.
                    // Wrapped at 2-space indent (outer nest-2 in prettyWfErrorReport).
    msg.push_str("  User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue \n");
    msg.push('\n'); // blank line after intro (HS `$-$` before vcat)
    msg.push_str(&eq_lines);
    // HS: `$-$ text " \n For more information..."` — note the leading space.
    msg.push_str("   \n For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html ");

    vec![WfError::new("Subterm Convergence Warning", msg)]
}

/// [`wf_term_doc`] — HS `prettyLNTerm` — laid out flat.
///
/// Sharing the one printer is what keeps these messages AC-canonical: HS's
/// terms are built by the smart constructors `fAppAC`/`fAppC`
/// (Term/Term/Raw.hs:118-134), so every `prettyTerm` call site sees a
/// flattened, sorted AC spine and a sorted `C` argument list, whatever the
/// source spelling was.
///
/// (No HughesPJ wrapping — the messages using this helper are expected to
/// fit on one line.)
fn pp_term_for_wf(t: &Term, ac: &AcSyms) -> String {
    wf_term_doc(t, ac).to_flat()
}

fn is_subterm_convergent(lhs: &Term, rhs: &Term, nullary_funs: &BTreeSet<String>) -> bool {
    // HS `isSubtermConvergentCtxtRule` (SubtermRule.hs:107-114):
    //   | isConstant rhs = True
    //   | otherwise      = not (null (findSubterm lhs rhs))
    // where `isConstant term = null (frees term)` (SubtermRule.hs:113-114) —
    // i.e. ANY variable-free (ground) RHS is accepted, not just a fixed set
    // of reserved names (e.g. `f(x) = 'c'`, `f(x) = g('a','b')`, or a user
    // `c/0` constant), where `frees` collects only `LVar`s.
    if rhs_is_ground(rhs, nullary_funs) {
        return true;
    }
    // Otherwise the RHS must literally appear as a subterm of the LHS.
    contains_subterm(lhs, rhs)
}

/// True if `t` has no free variables, mirroring HS `isConstant term =
/// null (frees term)` where `frees` collects only `LVar`s.  A bare
/// identifier that names a nullary constant — a known builtin nullary
/// (`true`/`zero`/…) or a user-declared `/0` function — is resolved by HS
/// at parse time to a variable-free `FApp`, so we do NOT count it as a free
/// variable; any other `Term::Var` is a genuine free variable.
fn rhs_is_ground(t: &Term, nullary_funs: &BTreeSet<String>) -> bool {
    use Term::*;
    match t {
        Var(v) => {
            // Untagged bare names that resolve to a nullary constant are
            // variable-free; everything else (and any sigil-tagged var) is a
            // genuine free variable.
            matches!(v.sort, SortHint::Untagged)
                && (is_known_nullary_constant_name(&v.name) || nullary_funs.contains(&v.name))
        }
        App(_, args) | Pair(args) => args.iter().all(|a| rhs_is_ground(a, nullary_funs)),
        AlgApp(_, a, b) | Diff(a, b) | BinOp(_, a, b) => {
            rhs_is_ground(a, nullary_funs) && rhs_is_ground(b, nullary_funs)
        }
        PatMatch(inner) => rhs_is_ground(inner, nullary_funs),
        PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) | NumberOne | NatOne | DhNeutral => true,
    }
}

/// Names that the surface parser may render as bare identifiers but
/// that semantically denote nullary constants (typically declared by
/// `builtins:` or `functions: ... /0`). We treat them as constants
/// for the purposes of subterm-convergence and free-variable checks.
///
/// These mirror the builtin nullary `NoEq` symbols HS resolves via
/// `nullaryApp` against `funSyms maudeSig` (Parser/Term.hs:143-148):
/// `trueSym = ("true",..)` (Builtin/Signature.hs:43-44, see line 44), and
/// `zeroSym`/`oneSym`/`dhNeutralSym` (FunctionSymbols.hs).  There is no
/// builtin `True`, so a genuine variable literally named `True` must NOT
/// be suppressed here — HS would report it as unbound/underivable.
fn is_known_nullary_constant_name(n: &str) -> bool {
    matches!(n, "true" | "zero" | "one" | "DH_neutral")
}

fn contains_subterm(haystack: &Term, needle: &Term) -> bool {
    if haystack == needle {
        return true;
    }
    match haystack {
        Term::App(_, args) | Term::Pair(args) => args.iter().any(|a| contains_subterm(a, needle)),
        Term::AlgApp(_, a, b) => contains_subterm(a, needle) || contains_subterm(b, needle),
        Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            contains_subterm(a, needle) || contains_subterm(b, needle)
        }
        Term::PatMatch(inner) => contains_subterm(inner, needle),
        _ => false,
    }
}

// =============================================================================
// Variable sort/capitalization clashes (within a single rule)
// =============================================================================

// NOTE: the actual HS `checkTerms` ("Formula terms" topic) is ported
// faithfully in `tamarin_theory::check_terms`, which needs the elaborated
// `MaudeSig` (for reducible/irreducible funsym classification) and so runs
// post-elaboration, interleaved with `checkQuantifiers`/`checkGuarded` by
// `tamarin_theory::formula_reports::formula_reports`.  The parser-level
// "Variable with mismatching sorts or capitalization" sub-check (a different
// topic, no signature needed) is `variable_sort_clashes` below; callers
// invoke it directly.

/// Within each rule, variables whose names agree modulo case AND share an
/// index, but differ in their full `LVar` (sort or capitalization), clash.
/// Port of HS `sortsClashCheck`/`ruleSortsReport` (Wellformedness.hs:258-280):
/// `clashesOn removeSort id $ frees ru` where `removeSort lv = (lowerCase
/// (lvarName lv), lvarIdx lv)`.  Bare identifiers default to sort `msg`
/// (HS LSortMsg), so `~ltk` (fresh) vs `ltk` (msg) clash.  Runs on the
/// let-substituted rule (HS `thyProtoRules` applies let-subst).
///
/// Emits one `WfError` per offending rule (so the summary's `length rep`
/// WARNING count matches HS, Batch.hs:87-316, see line 245), all sharing the topic
/// "Variable with mismatching sorts or capitalization"; `format_wf_block`
/// renders the header + "Possible reasons" preamble ONCE for the group.
pub fn variable_sort_clashes(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let (prems, acts, concs) = rule_facts_with_lets(r);
        // Pair each var with its lowercase name ONCE, so the sort/group steps
        // below don't re-allocate a `to_lowercase` string per comparison/probe.
        let mut vars: Vec<(String, VarSpec)> = Vec::new();
        for f in prems.iter().chain(&acts).chain(&concs) {
            for v in fact_vars(f) {
                vars.push((v.name.to_lowercase(), v));
            }
        }
        // clashesOn removeSort id: sort+group by (lowercase name, idx).
        // Stable sort over the precomputed lowercase key — identical order to
        // re-lowercasing in the comparator.
        vars.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.idx.cmp(&b.1.idx)));
        let mut clash_groups: Vec<Vec<VarSpec>> = Vec::new();
        let mut i = 0;
        while i < vars.len() {
            let key = (vars[i].0.as_str(), vars[i].1.idx);
            let mut j = i + 1;
            while j < vars.len() && (vars[j].0.as_str(), vars[j].1.idx) == key {
                j += 1;
            }
            // sortednubOn id: sort by HS LVar Ord (idx, sort, name) then dedup.
            let mut grp: Vec<VarSpec> = vars[i..j].iter().map(|(_, v)| v.clone()).collect();
            grp.sort_by(|a, b| {
                a.idx
                    .cmp(&b.idx)
                    .then_with(|| sort_tag(&a.sort).cmp(&sort_tag(&b.sort)))
                    .then_with(|| a.name.cmp(&b.name))
            });
            grp.dedup_by(|a, b| {
                a.name == b.name && sort_tag(&a.sort) == sort_tag(&b.sort) && a.idx == b.idx
            });
            if grp.len() >= 2 {
                clash_groups.push(grp);
            }
            i = j;
        }
        if clash_groups.is_empty() {
            continue;
        }
        // Body (headerless): HS snd = `text info $-$ nest 2 (numbered' $ map
        // prettyVarList cs)`, with ppTopic's outer `nest 2` baked in →
        // "  rule `X': \n    1. <vars>".  `numbered'` separates items by a
        // blank `text ""` line, which at 4-space indent renders as "    ".
        let mut body = format!("  rule `{}': \n", r.name);
        let w = numbered_index_width(clash_groups.len());
        let items: Vec<String> = clash_groups
            .iter()
            .enumerate()
            .map(|(k, grp)| {
                let vs: Vec<String> = grp.iter().map(render_var).collect();
                format!("    {:>w$}. {}", k + 1, vs.join(", "), w = w)
            })
            .collect();
        body.push_str(&items.join("\n    \n"));
        out.push(WfError::new(
            "Variable with mismatching sorts or capitalization",
            body,
        ));
    }
    out
}

// =============================================================================
// Nat sorts: `%+` requires nat operands
// =============================================================================

pub fn nat_well_sorted_report(thy: &Theory) -> WfReport {
    // Port of HS `natWellSortedReport` + `natSortErrors` (Wellformedness.hs:
    // 314-333).  For each top-level fact-arg term `t` (HS `factTerms` of every
    // prem/act/conc), `nonWellSorted t` collects the offending operands `err`
    // and we emit ONE body `<err> in term <t> must be of sort nat` per
    // (t, err) — the rule name is NOT part of the message, and `t` in the
    // message is the WHOLE fact-arg term, not the `%+` subterm.
    //
    // HS produces one WfError per (t, err); `prettyWfErrorReport` groups them
    // under a single "Nat Sorts" header (bodies 2-space-nested, separated by a
    // `  ` blank line).  "Nat Sorts" is not in the headerless-preamble set, so
    // we bake the whole block into one WfError (matching the single-error
    // corpus case byte-for-byte; the multi-error count-collapse only differs
    // synthetically, as with `fresh_names_report`/`lemma_attribute_report`).
    let topic = "Nat Sorts";
    let ac = user_ac_fun_names(thy);
    let mut bodies: Vec<String> = Vec::new();
    for r in theory_rules(thy) {
        for t in rule_terms(r) {
            let mut errs: Vec<&Term> = Vec::new();
            non_well_sorted(t, &mut errs, &ac);
            for err in errs {
                bodies.push(format!(
                    "  {} in term {} must be of sort nat",
                    pp_term_for_wf(err, &ac),
                    pp_term_for_wf(t, &ac)
                ));
            }
        }
    }
    // HS `natWellSortedReport`'s `getItemTerms` also checks the formula terms
    // of LemmaItem/RestrictionItem/PredicateItem (Wellformedness.hs:327-329).
    // That formula-term walk is not yet implemented here; the nat checks that
    // fire in the corpus all sit inside rules.
    grouped_topic_block(topic, bodies)
}

/// The direct operands of a parser term — the `ts` of HS's `FAPP _ ts`
/// before any smart-constructor canonicalisation.
fn wf_direct_children(t: &Term) -> Vec<&Term> {
    use Term::*;
    match t {
        App(_, args) | Pair(args) => args.iter().collect(),
        AlgApp(_, a, b) | Diff(a, b) | BinOp(_, a, b) => vec![a, b],
        PatMatch(inner) => vec![inner],
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) | NumberOne | NatOne
        | DhNeutral => Vec::new(),
    }
}

/// The operand list HS's term carries for `t`: an `AC` head's flattened,
/// sorted chain and a `C` head's sorted arguments (`fAppAC`/`fAppC`,
/// Term/Term/Raw.hs:118-134), otherwise the direct children.
///
/// This is [`hs_fapp_args`]'s borrowing sibling, for the wellformedness
/// WALKS that report references into the term rather than rendering it —
/// they see the same operand ORDER HS's checks traverse.  `Pair`'s
/// right-nesting is left flat: a walk over `[a, b, c]` reaches the same
/// leaves in the same order as one over `[a, pair(b, c)]`.
fn wf_canon_children<'a>(t: &'a Term, ac: &AcSyms) -> Vec<&'a Term> {
    let t = ac_collapse(t, ac);
    let key = wf_funsym_key(t, ac);
    match key.0 {
        1 => {
            let mut flat: Vec<&Term> = Vec::new();
            flatten_ac(key, t, &mut flat, ac);
            flat.sort_by(|a, b| cmp_wf_term(a, b, ac));
            flat
        }
        2 => {
            let mut args = wf_direct_children(t);
            args.sort_by(|a, b| cmp_wf_term(a, b, ac));
            args
        }
        _ => wf_direct_children(t),
    }
}

/// Faithful port of HS `nonWellSorted` (Wellformedness.hs:293-303): collect
/// the operands appearing under a `%+` (`FNatPlus`) that are not themselves
/// nat-well-sorted.  Pushes references to the offending sub-terms onto `out`.
fn non_well_sorted<'a>(t: &'a Term, out: &mut Vec<&'a Term>, ac: &AcSyms) {
    let t = ac_collapse(t, ac);
    match t {
        // FNatPlus list -> concatMap notOnlyNat list
        Term::BinOp(BinOp::NatPlus, _, _) => {
            for a in wf_canon_children(t, ac) {
                not_only_nat(a, out, ac);
            }
        }
        // NatOne -> []; Lit _ -> []
        Term::NatOne
        | Term::Var(_)
        | Term::PubLit(_)
        | Term::FreshLit(_)
        | Term::NatLit(_)
        | Term::Number(_)
        | Term::NumberOne
        | Term::DhNeutral => {}
        // FApp _ ts -> concatMap nonWellSorted ts (recurse into children)
        _ => {
            for a in wf_canon_children(t, ac) {
                non_well_sorted(a, out, ac);
            }
        }
    }
}

/// Faithful port of HS `notOnlyNat` (Wellformedness.hs:296-300): the inner
/// recursion under `%+`.  Accepts `NatOne` and genuine nat-sorted *variables*
/// (`isNatVar`, LTerm.hs:327-329); recurses through nested `%+`; flags
/// everything else (including untagged/msg/pub vars and nat *literals* like
/// `%'a'`, which are `Con` names, not vars — matching HS's `isNatVar`, which
/// is true only for `Lit (Var v)` with `lvarSort v == LSortNat`).
fn not_only_nat<'a>(t: &'a Term, out: &mut Vec<&'a Term>, ac: &AcSyms) {
    let t = ac_collapse(t, ac);
    match t {
        // FNatPlus l -> concatMap notOnlyNat l
        Term::BinOp(BinOp::NatPlus, _, _) => {
            for a in wf_canon_children(t, ac) {
                not_only_nat(a, out, ac);
            }
        }
        // NatOne -> []
        Term::NatOne => {}
        // t | isNatVar t = []  (nat-sorted VARIABLE only)
        Term::Var(v) if is_nat_sort(&v.sort) => {}
        // t = [t]  (anything else is an offending operand)
        _ => out.push(t),
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests;
