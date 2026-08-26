// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins HS `ruleVariantsReport` (Wellformedness.hs:375-382) and the rule drop
//! that shares its verdict.
//!
//! `variantsCheck`'s `guard (null recomputedVariants)` arm
//! (Wellformedness.hs:362-366) fires when `variantsProtoRule` returns
//! `Nothing`.  The canonical shape is a rule with both `Fr(~x)` and `In(~x)`
//! among its premises: `~x` cannot be sent before it is generated, so every
//! candidate substitution is fresh-redundant.  `closeProtoRule`
//! (lib/theory/src/Rule.hs:82-86) then produces no closed rule for it, and the
//! batch driver drops it from the theory on the same verdict.
//!
//! The expected block is the pinned oracle's (Git revision ef3f0468).

use tamarin_parser::parse_theory;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::theory::{Theory, TheoryItem};
use tamarin_theory::tools::rule_variants::{open_rule_has_no_variants, populate_rule_variants};
use tamarin_theory::wellformedness::rules::rule_variants_report;

/// Absolute maude locations probed before `PATH` is walked.
///
/// This probe mirrors the crate-shared `src/test_maude.rs` one (an
/// integration test cannot see a `#[cfg(test)]` module of the library it
/// links) — keep the two in sync.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Last resort, after `PATH`: the linuxbrew prefix this project's maude lives
/// under on the development box, which is deliberately not on `PATH`.
const MAUDE_LINUXBREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The maude every case below runs against: `$MAUDE_PATH`, else the first
/// existing [`MAUDE_CANDIDATES`] entry, else a `PATH` walk, else
/// [`MAUDE_LINUXBREW`].
///
/// Resolving NOTHING is a misconfiguration, not a reason to skip: every case
/// in this file opens with `let mp = match maude_path() { Some(p) => p, None
/// => return }`, so a `None` here reports the same green run with and without
/// maude installed.  Panic instead — unless `TAM_ALLOW_NO_MAUDE=1` explicitly
/// asks for the silent skip (a box that genuinely has no maude).  A
/// `MAUDE_PATH` naming a file that does not exist is the same
/// misconfiguration and panics too.
fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?} / PATH / {MAUDE_LINUXBREW}, or point it at a \
             real maude — skipping every case here would report green vacuously"
        );
        return Some(p);
    }
    if let Some(c) = MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
    {
        return Some((*c).to_string());
    }
    // `PATH` walk, kept dependency-free like every other copy of this probe.
    if let Some(p) = std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|d| d.join("maude"))
            .find(|p| p.is_file())
    }) {
        return Some(p.to_string_lossy().into_owned());
    }
    if std::path::Path::new(MAUDE_LINUXBREW).exists() {
        return Some(MAUDE_LINUXBREW.to_string());
    }
    if std::env::var("TAM_ALLOW_NO_MAUDE").as_deref() == Ok("1") {
        return None;
    }
    panic!(
        "no maude found: MAUDE_PATH unset, none of {MAUDE_CANDIDATES:?} exist, \
         nothing named `maude` on PATH, and no {MAUDE_LINUXBREW}. Every case in \
         this file would skip and the run would be green having proved nothing. \
         Install maude, set MAUDE_PATH, or set TAM_ALLOW_NO_MAUDE=1 to accept \
         the silent skip."
    );
}

/// A theory with one rule that has no variants (`NoVar`) and one that has the
/// trivial one (`Ok`).
const SRC: &str = "theory NoVariants\nbegin\n\
                   builtins: symmetric-encryption\n\
                   rule NoVar:\n  [ In(~x), Fr(~x) ] --[ N(~x) ]-> [ ]\n\
                   rule Ok:\n  [ Fr(~k), In(c) ] --[ O(~k) ]-> [ Out(sdec(c, ~k)) ]\n\
                   end\n";

/// The elaborated theory with `populate_rule_variants` applied, as the batch
/// driver hands it to the wellformedness pass, and a handle on its signature.
fn loaded(mp: &str) -> (Theory, MaudeHandle) {
    let parsed = parse_theory(SRC, &[]).expect("parse");
    let mut elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let maude =
        MaudeHandle::start(mp, elaborated.signature.maude_sig.clone()).expect("start maude");
    populate_rule_variants(&mut elaborated, &maude, None);
    (elaborated, maude)
}

/// The oracle's `Rule has no variants` body, once, for `NoVar` alone.  "For
/// exaple" is spelled that way in the HS source (Wellformedness.hs:366).
#[test]
fn no_variant_rule_is_reported() {
    let Some(mp) = maude_path() else { return };
    let (thy, maude) = loaded(&mp);
    let report = rule_variants_report(&thy, Some(&maude));
    assert_eq!(report.len(), 1, "only `NoVar` has no variants: {report:?}");
    assert_eq!(report[0].topic, "Rule has no variants");
    assert_eq!(
        report[0].message,
        "Rule has no variants\n====================\n\n  \
         Rule NoVar has no variants.\n  \n  \
         Most likely, this means that the rule's use of fresh variables is \
         contradictory. For exaple, a rule with the premises In(~x) and Fr(~x) \
         has no variants because ~x cannot be sent before it is generated.\n"
    );
}

/// The web load path has no Maude process at wellformedness time and so emits
/// no such block.
#[test]
fn no_maude_reports_nothing() {
    let Some(mp) = maude_path() else { return };
    let (thy, _maude) = loaded(&mp);
    assert!(rule_variants_report(&thy, None).is_empty());
}

/// HS `closeProtoRule` (lib/theory/src/Rule.hs:82-86) drops a rule with no
/// variants from the closed theory.  The batch driver's `retain` reads this
/// predicate, not the report, so a rule name that `showRuleCaseName` prefixes
/// still matches.
#[test]
fn only_the_no_variant_rule_is_dropped() {
    let Some(mp) = maude_path() else { return };
    let (mut thy, maude) = loaded(&mp);
    thy.items.retain(|item| match item {
        TheoryItem::Rule(opr) => !open_rule_has_no_variants(&maude, opr),
        _ => true,
    });
    let names: Vec<&str> = thy.rules().map(|opr| opr.name()).collect();
    assert_eq!(names, vec!["Ok"]);
}
