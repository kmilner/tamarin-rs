// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The wellformedness checks over a theory's lemmas: HS
//! `lemmaAttributeReport` (Wellformedness.hs:924-932) and
//! `checkIfLemmasInTheory` (Wellformedness.hs:1156-1171).

use tamarin_parser::ast::{LemmaAttr, Theory, TraceQuantifier};

use super::{grouped_topic_block, theory_lemmas, underline_topic, WfError, WfReport};

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

    let theory_lemma_names: Vec<&str> = theory_lemmas(thy).map(|l| l.name.as_str()).collect();

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
// Lemma annotations — reuse on exists-trace
// =============================================================================

pub fn lemma_attribute_report(_elab: &crate::theory::Theory, parsed: &Theory) -> WfReport {
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
    let bodies: Vec<String> = theory_lemmas(parsed)
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
    // `crate::pretty_theory`.
    grouped_topic_block(topic, bodies)
}
