// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus probes over the TRANSLATED theory — the internal theory as the
//! driver leaves it after `elaborate`, `apply_sapic` and
//! `tamarin_accountability::translate` (run.rs `translate_theory`).  The
//! lemmas and restrictions those two translations inject are the ones the
//! other corpus nets do not reach.
//!
//! `translated_items_carry_both_formulas` walks the two formulas such an item
//! stores — `_lFormula` / `_rstrFormula`, macro- and predicate-expanded, and
//! the `_lOriginalFormula` / `_rstrOriginalFormula` that
//! `applyMacroInLemma` / `applyMacroInRestriction` record for every item of a
//! closed theory (lib/theory/src/Lemma.hs:83-89,
//! Theory/Model/Restriction.hs:164-166).
//! `every_translated_item_has_one_lookup` checks the lookup a printer that
//! reads an item by name depends on (`Theory::lookup_lemma` /
//! `lookup_restriction`) over everything the two translations add.

use crate::corpus_util;
use crate::corpus_util::{deep_pool, rel, LoadSkip};
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_theory::formula::LNFormula;
use tamarin_theory::pretty_formula::pretty_lnformula;
use tamarin_theory::theory::{Theory, TheoryItem};

/// Which stage of the pipeline a file reached.
#[derive(PartialEq)]
enum Outcome {
    Translated,
    Skipped(LoadSkip),
    /// `apply_sapic` or the accountability translation reported an error or
    /// panicked; the driver turns both into a process exit (run.rs).
    SkippedTranslate,
}

const SKIP_TRANSLATE: &str = "SAPIC/accountability translation rejects this example";
const EXPECTED_TRANSLATION_SKIPS: &[(&str, &str)] = &[
    (
        "sapic/not-suitable-for-regression/issue-missing-unlock.spthy",
        SKIP_TRANSLATE,
    ),
    (
        "sapic/not-working/fairexchange-asw/asw-mod-weak-locks.spthy",
        SKIP_TRANSLATE,
    ),
    (
        "sapic/not-working/fairexchange-asw/aswAB-mod.spthy",
        SKIP_TRANSLATE,
    ),
    (
        "sapic/not-working/fairexchange-asw/aswAB.spthy",
        SKIP_TRANSLATE,
    ),
    (
        "sapic/not-working/fairexchange-gjm/gjm-locks-fakepcsbranch.spthy",
        SKIP_TRANSLATE,
    ),
    ("sapic/not-working/fairexchange-km/km.spthy", SKIP_TRANSLATE),
    ("testParser/right-assoc.spthy", SKIP_TRANSLATE),
];

/// Both probes' findings for one file, plus what they counted.
struct FileProbe {
    outcome: Outcome,
    /// Formulas walked by [`translated_items_carry_both_formulas`].
    items: usize,
    /// Names looked up by [`every_translated_item_has_one_lookup`].
    pairs: usize,
    /// Names the translations leave as they found them, counted and not
    /// looked up.
    sided: usize,
    formulas: Vec<String>,
    lookups: Vec<String>,
    elapsed: Duration,
}

impl FileProbe {
    fn skipped(outcome: Outcome) -> Self {
        FileProbe {
            outcome,
            items: 0,
            pairs: 0,
            sided: 0,
            formulas: Vec::new(),
            lookups: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// The lemmas and restrictions of a theory: each labelled the way a
/// wellformedness report names its item, with the two formulas it stores.
fn items(thy: &Theory) -> Vec<(String, &LNFormula, Option<&LNFormula>)> {
    thy.items
        .iter()
        .filter_map(|item| match item {
            TheoryItem::Lemma(l) => Some((
                format!("lemma `{}'", l.name),
                &l.formula,
                l.original_formula.as_ref(),
            )),
            TheoryItem::Restriction(r) => Some((
                format!("restriction `{}'", r.name),
                &r.formula,
                r.original_formula.as_ref(),
            )),
            _ => None,
        })
        .collect()
}

/// Both formulas of every lemma and restriction of the translated theory:
/// each is present and renders, which walks every atom and term it holds.
/// The original one is what HS's `applyMacroInLemma` /
/// `applyMacroInRestriction` fill in for every item of a closed theory, the
/// injected ones included (CloseRule.hs:82-85).
fn probe_formulas(thy: &Theory, at: &dyn Fn(&str) -> String) -> Vec<String> {
    let mut out = Vec::new();
    for (label, formula, original) in items(thy) {
        let where_ = |what: &str| at(&format!("{label}: {what}"));
        if pretty_lnformula(formula).is_empty() {
            out.push(where_("formula renders empty"));
        }
        match original {
            None => out.push(where_("no original formula")),
            Some(o) => {
                if pretty_lnformula(o).is_empty() {
                    out.push(where_("original_formula renders empty"));
                }
            }
        }
    }
    out
}

/// The `(kind, name)` list of the theory's lemmas and restrictions, in item
/// order.
fn item_names(thy: &Theory) -> Vec<(&'static str, &str)> {
    thy.items
        .iter()
        .filter_map(|item| match item {
            TheoryItem::Lemma(l) => Some(("lemma", l.name.as_str())),
            TheoryItem::Restriction(r) => Some(("restriction", r.name.as_str())),
            _ => None,
        })
        .collect()
}

/// Every lemma and restriction the two translations add is found exactly once
/// under its own name — the lookup `Theory::lookup_lemma` /
/// `lookup_restriction` performs.  A name the translations leave alone keeps
/// whatever multiplicity the source gave it: a diff theory declares one name
/// per side, HS keys those by `(Side, name)` (`EitherLemmaItem` /
/// `EitherRestrictionItem`, Items/TheoryItem.hs:78-79), and the flat internal
/// theory holds both — it carries no side attribute, the non-diff restriction
/// parser accepting none (Theory/Text/Parser/Restriction.hs:77-81).  Returns
/// the findings, the number of names looked up and the number carried over
/// untouched.
fn probe_lookups(
    thy: &Theory,
    before: &[(&'static str, &str)],
    after: &[(&'static str, &str)],
    at: &dyn Fn(&str) -> String,
) -> (Vec<String>, usize, usize) {
    let occurrences = |xs: &[(&str, &str)], kind: &str, name: &str| {
        xs.iter().filter(|(k, n)| *k == kind && *n == name).count()
    };
    let mut out = Vec::new();
    let (mut pairs, mut carried) = (0usize, 0usize);
    let mut seen: Vec<(&str, &str)> = Vec::new();
    for (kind, name) in after {
        if seen.contains(&(kind, name)) {
            continue;
        }
        seen.push((kind, name));
        let found = occurrences(after, kind, name);
        if found == 1 {
            pairs += 1;
            let looked_up = match *kind {
                "lemma" => thy.lookup_lemma(name).map(|item| item.name.as_str()),
                "restriction" => thy.lookup_restriction(name).map(|item| item.name.as_str()),
                _ => unreachable!("item_names returns only lemmas and restrictions"),
            };
            if looked_up != Some(*name) {
                out.push(at(&format!(
                    "{kind} `{name}' lookup returned {looked_up:?}"
                )));
            }
            continue;
        }
        if found == occurrences(before, kind, name) {
            carried += 1;
            continue;
        }
        pairs += 1;
        out.push(at(&format!(
            "{kind} `{name}' occurs {found} times after translation"
        )));
    }
    (out, pairs, carried)
}

/// The driver's load pipeline for one file, up to the point where the
/// translated theory is complete — the load ladder, then the SAPIC and the
/// accountability translation (run.rs `translate_theory`) — then both
/// probes over that theory.
fn probe(path: &Path, root: &Path) -> FileProbe {
    let start = Instant::now();
    let mut elab = match corpus_util::load_elaborated(path, root) {
        Ok(loaded) => (*loaded).clone(),
        Err(skip) => return FileProbe::skipped(Outcome::Skipped(skip)),
    };
    let found = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // The names the source declares, against which the translations'
        // additions are read.
        let before: Vec<(&str, String)> = item_names(&elab)
            .into_iter()
            .map(|(k, n)| (k, n.to_string()))
            .collect();
        let user_set_heuristic = !elab.heuristic.is_empty();
        tamarin_sapic::apply::apply_sapic(&mut elab, user_set_heuristic).map_err(|e| e.message)?;
        tamarin_accountability::translate(&mut elab).map_err(|e| e.to_string())?;
        let file = rel(path, root).display().to_string();
        let at = |what: &str| format!("{file}: {what}");
        let before: Vec<(&str, &str)> = before.iter().map(|(k, n)| (*k, n.as_str())).collect();
        Ok::<_, String>((
            items(&elab).len(),
            probe_formulas(&elab, &at),
            probe_lookups(&elab, &before, &item_names(&elab), &at),
        ))
    }));
    let Ok(Ok((count, formulas, (lookups, pairs, sided)))) = found else {
        return FileProbe::skipped(Outcome::SkippedTranslate);
    };
    FileProbe {
        outcome: Outcome::Translated,
        // Both the stored and the original formula are walked.
        items: 2 * count,
        pairs,
        sided,
        formulas,
        lookups,
        elapsed: start.elapsed(),
    }
}

/// The corpus root, its `.spthy` files, and both probes over all of them.
type Corpus = (PathBuf, Vec<PathBuf>, Vec<FileProbe>);

/// [`probe`] over the whole tree, run once for both tests: the load
/// pipeline is the expensive half and both read the same findings.  `None`
/// when the root is missing and `TAM_ALLOW_NO_CORPUS=1` allows the skip.
fn corpus() -> Option<&'static Corpus> {
    static CORPUS: OnceLock<Option<Corpus>> = OnceLock::new();
    CORPUS
        .get_or_init(|| {
            let (root, files) = corpus_util::corpus_files("corpus")?;
            let probes =
                deep_pool().install(|| files.par_iter().map(|p| probe(p, &root)).collect());
            Some((root, files, probes))
        })
        .as_ref()
}

/// The header both probes print: how many files reached the translated
/// theory, where the rest stopped, and the file the load pipeline spent
/// longest on.
fn census(corpus: &Corpus) -> String {
    let (root, files, probes) = corpus;
    let count = |f: fn(&Outcome) -> bool| probes.iter().filter(|p| f(&p.outcome)).count();
    let slowest = probes
        .iter()
        .zip(files)
        .max_by_key(|(p, _)| p.elapsed)
        .map(|(p, path)| format!("{} ({:?})", rel(path, root).display(), p.elapsed))
        .unwrap_or_default();
    let rejected: Vec<String> = probes
        .iter()
        .zip(files)
        .filter(|(p, _)| p.outcome == Outcome::SkippedTranslate)
        .map(|(_, path)| rel(path, root).display().to_string())
        .collect();
    format!(
        "files={} loaded={} skipped_listed={} skipped_parse={} skipped_elab={} \
         skipped_translate={:?} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::Translated)),
        count(|o| matches!(o, Outcome::Skipped(LoadSkip::Listed))),
        count(|o| matches!(o, Outcome::Skipped(LoadSkip::Parse))),
        count(|o| matches!(o, Outcome::Skipped(LoadSkip::Elab))),
        rejected,
    )
}

/// The files that reached the translated theory, and the whole tree.
fn assert_expected_skips(corpus: &Corpus) {
    let (root, files, probes) = corpus;
    let expected: Vec<_> = corpus_util::EXPECTED_LOAD_SKIPS
        .iter()
        .chain(EXPECTED_TRANSLATION_SKIPS)
        .copied()
        .collect();
    corpus_util::assert_expected_skips(
        root,
        files.iter().zip(probes).filter_map(|(path, probe)| {
            let reason = match probe.outcome {
                Outcome::Translated => return None,
                Outcome::Skipped(skip) => skip.reason(),
                Outcome::SkippedTranslate => SKIP_TRANSLATE,
            };
            Some((path.as_path(), reason))
        }),
        &expected,
    );
}

#[test]
fn translated_items_carry_both_formulas() {
    let Some(corpus) = corpus() else {
        return;
    };
    let probes = &corpus.2;
    let items: usize = probes.iter().map(|p| p.items).sum();
    let failures: Vec<&String> = probes.iter().flat_map(|p| &p.formulas).collect();
    eprintln!(
        "s3 formulas: {} items={items} failures={}",
        census(corpus),
        failures.len()
    );
    for f in &failures {
        eprintln!("FAILURE {f}");
    }
    assert_expected_skips(corpus);
    assert!(items > 0, "no formulas walked");
    assert!(
        failures.is_empty(),
        "{} formulas missing or unrenderable; first: {}",
        failures.len(),
        failures[0]
    );
}

#[test]
fn every_translated_item_has_one_lookup() {
    let Some(corpus) = corpus() else {
        return;
    };
    let probes = &corpus.2;
    let pairs: usize = probes.iter().map(|p| p.pairs).sum();
    let carried: usize = probes.iter().map(|p| p.sided).sum();
    let failures: Vec<&String> = probes.iter().flat_map(|p| &p.lookups).collect();
    eprintln!(
        "s3 lookups: {} pairs={pairs} carried={carried} failures={}",
        census(corpus),
        failures.len()
    );
    for f in &failures {
        eprintln!("FAILURE {f}");
    }
    assert_expected_skips(corpus);
    assert!(pairs > 0, "no names looked up");
    assert!(
        failures.is_empty(),
        "{} names without exactly one lookup; first: {}",
        failures.len(),
        failures[0]
    );
}
