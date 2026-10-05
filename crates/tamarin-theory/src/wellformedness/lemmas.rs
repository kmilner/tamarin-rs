// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The wellformedness checks over a theory's lemmas: HS
//! `lemmaAttributeReport` (Wellformedness.hs) and
//! `checkIfLemmasInTheory` (Wellformedness.hs).

use crate::theory::{LemmaAttr, Theory, TraceQuantifier};

use super::{underline_topic, WfError, WfReport};

// =============================================================================
// Check that CLI --prove/--lemma arguments name actual lemmas in the theory
// =============================================================================

/// Port of HS `checkIfLemmasInTheory` (Wellformedness.hs).
///
/// The probe list is the theory's own `_lemmasToProve`
/// (Wellformedness.hs), which HS's `addLemmaToProve` fills from the
/// `--prove`/`--lemma` values (TheoryLoader.hs) and both load
/// drivers write before this pass runs.
///
/// Semantics (mirror of `findNotProvedLemmas` / `lemmaChecker`):
///   - A list that is exactly `[""]` (bare `--prove` with no value)
///     means "all" → skip.
///   - Otherwise: for each name, it "corresponds" if
///     • there is a theory lemma whose name equals it exactly, OR
///     • the name ends with `*` and its prefix is a prefix of at least
///     one theory-lemma name.
///     Names that don't correspond are collected; if any exist the WF
///     check fires.
pub fn check_if_lemmas_in_theory(thy: &Theory) -> WfReport {
    // HS: `| lemmaArgsNames == [[]] = []`  (Wellformedness.hs)
    // HS stores lemmaArgsNames as [String]; [[]] is [""] (a list
    // containing exactly one empty string), which means bare `--prove`
    // with no argument value.  Skip the check ONLY in that case.
    //
    // MIXED entries (e.g. `--prove --lemma=BadX` → ["", "BadX"]) fail the
    // HS condition, so the check DOES run and the empty string is reported
    // as "not found" too — faithfulness requires keeping empty strings in
    // the probe list.  An EMPTY list yields an empty fold below, hence an
    // empty report, which is HS's `null notProvedLemmas` guard.
    let lemma_args_names = &thy.options.lemmas_to_prove;
    if lemma_args_names.len() == 1 && lemma_args_names[0].is_empty() {
        return Vec::new();
    }

    let theory_lemma_names: Vec<&str> = thy.lemmas().map(|l| l.name.as_str()).collect();

    // HS `findNotProvedLemmas` (Wellformedness.hs) is
    // a `foldl` that PREPENDS mismatches, so it reverses its input.  That
    // input is `lemmas_to_prove`, HS's `lemmaNames` (TheoryLoader.hs):
    // the `--prove` values then the `--lemma` values, each flag's values
    // reversed.  The report therefore lists the `--lemma` values in
    // command-line order, then the `--prove` values in command-line order.
    let mut not_proved: Vec<&str> = Vec::new();
    for name in lemma_args_names.iter() {
        if !arg_matches_any_lemma(name, &theory_lemma_names) {
            not_proved.insert(0, name);
        }
    }

    if not_proved.is_empty() {
        return Vec::new();
    }

    // HS topic: `underlineTopic "Check presence of the --prove/--lemma
    // arguments in theory"` (Wellformedness.hs).
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

/// Port of HS `lemmaAttributeReport` (Wellformedness.hs): a
/// list-monad `do` over `theoryLemmas` that returns ONE entry per
/// exists-trace lemma tagged `reuse`, so the trailing
/// `WARNING: N wellformedness check failed!` count (Batch.hs) counts
/// each of them.
///
/// Each body is HS's `text "Lemma" <-> quote name <> colon <-> text
/// "cannot reuse 'exists-trace' lemmas"`, carrying neither the topic
/// header nor `prettyWfErrorReport`'s `nest 2`; both come from
/// `crate::pretty_theory`'s headerless-preamble path.
pub fn lemma_attribute_report(thy: &Theory) -> WfReport {
    thy.lemmas()
        .filter(|l| {
            l.trace_quantifier == TraceQuantifier::ExistsTrace
                && l.attributes.contains(&LemmaAttr::Reuse)
        })
        .map(|l| {
            WfError::new(
                "Lemma annotations",
                format!("Lemma `{}': cannot reuse 'exists-trace' lemmas", l.name),
            )
        })
        .collect()
}

#[cfg(test)]
#[path = "lemmas_tests.rs"]
mod tests;
