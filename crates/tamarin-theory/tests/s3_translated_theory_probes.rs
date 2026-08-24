// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus probes over the TRANSLATED theory pair — the parser theory and
//! the elaborated theory as the driver leaves them after
//! `lift_rule_restrictions`, `elaborate`, `apply_sapic` and
//! `tamarin_accountability::translate` (run.rs `translate_theory`).  The
//! lemmas and restrictions those two translations inject are the ones the
//! other corpus nets do not reach, and they are the ones an
//! internal-formula lemma field has to hold.
//!
//! `from_parser_is_total_after_translation` builds both formulas such an
//! item stores — the macro- and predicate-expanded one and the
//! predicate-only one — for every lemma and restriction of the translated
//! parser theory.  `every_parsed_lemma_and_restriction_has_one_elaborated_twin`
//! checks the lookup a printer that reads the elaborated item by name
//! depends on (`Theory::lookup_lemma` / `lookup_restriction`).

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_parser::ast as p;
use tamarin_theory::formula::{from_parser, to_lnformula};
use tamarin_theory::theory::{LemmaAttr, Theory, TheoryItem};

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count.
/// Neither file is in the prove or pretty gate corpus
/// (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// The examples tree, or the override in `CORPUS_ROOT`.
fn corpus_root() -> PathBuf {
    if let Ok(root) = std::env::var("CORPUS_ROOT") {
        return PathBuf::from(root);
    }
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
}

/// `path` relative to the corpus root, as the report names it.
fn rel<'a>(path: &'a Path, root: &Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

fn spthy_files(root: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.extension().is_some_and(|x| x == "spthy"))
        .collect();
    files.sort();
    files
}

/// Which stage of the pipeline a file reached.
#[derive(PartialEq)]
enum Outcome {
    Translated,
    SkippedListed,
    SkippedParse,
    SkippedLift,
    SkippedElab,
    /// `apply_sapic` or the accountability translation reported an error or
    /// panicked; the driver turns both into a process exit (run.rs).
    SkippedTranslate,
}

/// Both probes' findings for one file, plus what they counted.
struct FileProbe {
    outcome: Outcome,
    /// Formulas converted by [`from_parser_is_total_after_translation`].
    items: usize,
    /// Items paired by [`every_parsed_lemma_and_restriction_has_one_elaborated_twin`].
    pairs: usize,
    /// Items that carry a `left` / `right` attribute, counted and not paired.
    sided: usize,
    conversions: Vec<String>,
    twins: Vec<String>,
    elapsed: Duration,
}

impl FileProbe {
    fn skipped(outcome: Outcome) -> Self {
        FileProbe {
            outcome,
            items: 0,
            pairs: 0,
            sided: 0,
            conversions: Vec::new(),
            twins: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// The lemma and restriction formulas of a parser theory, each labelled the
/// way a wellformedness report names its item.
fn formulas(thy: &p::Theory) -> Vec<(String, &p::Formula)> {
    thy.items
        .iter()
        .filter_map(|item| match item {
            p::TheoryItem::Lemma(l) => Some((format!("lemma `{}'", l.name), &l.formula)),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                Some((format!("restriction `{}'", r.name), &r.formula))
            }
            _ => None,
        })
        .collect()
}

/// The two formulas an internal-formula lemma or restriction stores, for
/// every lemma and restriction of `parsed`: `formula` is macro- and
/// predicate-expanded, as `elaborate` builds it, and `original_formula` is
/// the predicate-only one HS's `applyMacroInLemma` records
/// (lib/theory/src/Lemma.hs:83-89).  Both have to reach `LNFormula`.
fn probe_conversions(
    parsed: &p::Theory,
    elab: &Theory,
    at: &dyn Fn(&str) -> String,
) -> Vec<String> {
    let msig = &elab.signature.maude_sig;
    let mut out = Vec::new();
    let mut expanded = parsed.clone();
    tamarin_theory::macro_expand::expand_theory_macros(&mut expanded);
    // `expand_items` rewrites the item list in place and adds and removes
    // nothing (macro_expand.rs), which is what lets the predicate-only list
    // below pair with this one positionally.
    if expanded.items.len() != parsed.items.len() {
        out.push(at("macro expansion changed the item count"));
    }
    let mut predicate_only = parsed.clone();
    for thy in [&mut expanded, &mut predicate_only] {
        if let Err(e) = tamarin_theory::predicate_expand::expand_theory_formulas(thy) {
            out.push(at(&format!("predicate expansion failed: {}", e.message)));
        }
    }
    for (which, thy) in [
        ("formula", &expanded),
        ("original_formula", &predicate_only),
    ] {
        for (label, f) in formulas(thy) {
            let where_ = |what: &str| at(&format!("{label} [{which}]: {what}"));
            match from_parser(f, msig) {
                Err(e) => out.push(where_(&format!("from_parser: {}", e.message))),
                Ok(ln) => {
                    if to_lnformula(&ln).is_none() {
                        out.push(where_("to_lnformula: residual sugar"));
                    }
                }
            }
        }
    }
    out
}

/// A `left` / `right` lemma or restriction attribute: HS keys such an item
/// by `(Side, name)` inside a diff theory (`EitherLemmaItem` /
/// `EitherRestrictionItem`, Items/TheoryItem.hs:78-79), so the name repeats
/// across the two sides, and `elaborate` lowers both into the one flat
/// `Theory`.
fn is_sided(item: &p::TheoryItem) -> bool {
    match item {
        p::TheoryItem::Lemma(l) => l
            .attributes
            .iter()
            .any(|a| matches!(a, p::LemmaAttr::Left | p::LemmaAttr::Right)),
        p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => !r.attributes.is_empty(),
        _ => false,
    }
}

/// Every parsed lemma and restriction that is not a diff-theory side item
/// resolves to exactly one elaborated item of the same kind and name — the
/// lookup `Theory::lookup_lemma`/`lookup_restriction` performs.  Returns the
/// findings, the number of items paired and the number of side items.
fn probe_twins(
    parsed: &p::Theory,
    elab: &Theory,
    at: &dyn Fn(&str) -> String,
) -> (Vec<String>, usize, usize) {
    let mut out = Vec::new();
    let (mut pairs, mut sided) = (0usize, 0usize);
    for item in &parsed.items {
        let (kind, name) = match item {
            p::TheoryItem::Lemma(l) => ("lemma", &l.name),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                ("restriction", &r.name)
            }
            _ => continue,
        };
        if is_sided(item) {
            sided += 1;
            continue;
        }
        pairs += 1;
        let twins = elab
            .items
            .iter()
            .filter(|i| match (kind, i) {
                ("lemma", TheoryItem::Lemma(l)) => {
                    &l.name == name
                        && !l
                            .attributes
                            .iter()
                            .any(|a| matches!(a, LemmaAttr::Left | LemmaAttr::Right))
                }
                ("restriction", TheoryItem::Restriction(r)) => &r.name == name,
                _ => false,
            })
            .count();
        if twins != 1 {
            out.push(at(&format!("{kind} `{name}' has {twins} elaborated twins")));
        }
    }
    (out, pairs, sided)
}

/// The driver's load pipeline for one file, up to the point where the
/// theory pair is complete — parse, lift the embedded restrictions,
/// elaborate, translate the SAPIC process, translate the accountability
/// lemmas (run.rs `translate_theory`) — then both probes over that pair.
/// A diff-operator theory is parsed again with the `diff` define, the way
/// `-D=diff` enables the operator on the CLI.
fn probe(path: &Path, root: &Path) -> FileProbe {
    let start = Instant::now();
    if BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref()) {
        return FileProbe::skipped(Outcome::SkippedListed);
    }
    let Ok(src) = std::fs::read_to_string(path) else {
        return FileProbe::skipped(Outcome::SkippedParse);
    };
    let base = path.parent().map(Path::to_path_buf);
    let parsed = std::panic::catch_unwind(|| {
        tamarin_parser::parser::parse_theory_with_base(&src, &[], base.clone())
            .or_else(|_| tamarin_parser::parser::parse_theory_with_base(&src, &["diff"], base))
            .ok()
    });
    let Ok(Some(mut parsed)) = parsed else {
        return FileProbe::skipped(Outcome::SkippedParse);
    };
    let lifted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parsed).is_ok()
    }));
    if !matches!(lifted, Ok(true)) {
        return FileProbe::skipped(Outcome::SkippedLift);
    }
    let elab = std::panic::catch_unwind(|| tamarin_theory::elaborate::elaborate(&parsed).ok());
    let Ok(Some(mut elab)) = elab else {
        return FileProbe::skipped(Outcome::SkippedElab);
    };
    let found = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let user_set_heuristic = !elab.heuristic.is_empty();
        tamarin_sapic::apply::apply_sapic(&mut parsed, &mut elab, user_set_heuristic)
            .map_err(|e| e.message)?;
        tamarin_accountability::translate(&mut parsed, &mut elab).map_err(|e| e.to_string())?;
        let file = rel(path, root).display().to_string();
        let at = |what: &str| format!("{file}: {what}");
        Ok::<_, String>((
            formulas(&parsed).len(),
            probe_conversions(&parsed, &elab, &at),
            probe_twins(&parsed, &elab, &at),
        ))
    }));
    let Ok(Ok((items, conversions, (twins, pairs, sided)))) = found else {
        return FileProbe::skipped(Outcome::SkippedTranslate);
    };
    FileProbe {
        outcome: Outcome::Translated,
        // Both the expanded and the predicate-only list are converted.
        items: 2 * items,
        pairs,
        sided,
        conversions,
        twins,
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
            let root = corpus_root();
            if !root.is_dir() {
                if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
                    eprintln!("corpus: root {} missing, skipped", root.display());
                    return None;
                }
                panic!(
                    "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
                    root.display()
                );
            }
            let files = spthy_files(&root);
            // The parser, the translations and the formula walks recurse
            // along the input; the web server renders on 64 MiB tokio
            // threads (run.rs), so the workers get the same stacks.
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(64 * 1024 * 1024)
                .build()
                .expect("rayon pool");
            let probes = pool.install(|| files.par_iter().map(|p| probe(p, &root)).collect());
            Some((root, files, probes))
        })
        .as_ref()
}

/// A probe over the corpus is a net only while it covers the tree: a change
/// that makes a stage of the pipeline reject files has to fail here instead
/// of shrinking the probe.  The tree has 19 parser rejects in 1037 files,
/// the same floor the stage-0 net holds.
fn assert_corpus_covered(loaded: usize, files: usize) {
    assert!(
        loaded * 20 >= files * 19,
        "only {loaded} of {files} files reached the probe"
    );
}

/// The header both probes print: how many files reached the pair, where the
/// rest stopped, and the file the load pipeline spent longest on.
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
        "files={} loaded={} skipped_listed={} skipped_parse={} skipped_lift={} skipped_elab={} \
         skipped_translate={:?} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::Translated)),
        count(|o| matches!(o, Outcome::SkippedListed)),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
        rejected,
    )
}

/// The files that reached the theory pair, and the whole tree.
fn coverage(probes: &[FileProbe]) -> (usize, usize) {
    let loaded = probes
        .iter()
        .filter(|p| p.outcome == Outcome::Translated)
        .count();
    (loaded, probes.len())
}

#[test]
fn from_parser_is_total_after_translation() {
    let Some(corpus) = corpus() else {
        return;
    };
    let probes = &corpus.2;
    let items: usize = probes.iter().map(|p| p.items).sum();
    let failures: Vec<&String> = probes.iter().flat_map(|p| &p.conversions).collect();
    eprintln!(
        "s3 from_parser: {} items={items} failures={}",
        census(corpus),
        failures.len()
    );
    for f in &failures {
        eprintln!("FAILURE {f}");
    }
    let (loaded, files) = coverage(probes);
    assert_corpus_covered(loaded, files);
    assert!(items > 0, "no formulas converted");
    assert!(
        failures.is_empty(),
        "{} conversions failed; first: {}",
        failures.len(),
        failures[0]
    );
}

#[test]
fn every_parsed_lemma_and_restriction_has_one_elaborated_twin() {
    let Some(corpus) = corpus() else {
        return;
    };
    let probes = &corpus.2;
    let pairs: usize = probes.iter().map(|p| p.pairs).sum();
    let sided: usize = probes.iter().map(|p| p.sided).sum();
    let failures: Vec<&String> = probes.iter().flat_map(|p| &p.twins).collect();
    eprintln!(
        "s3 twins: {} pairs={pairs} sided={sided} failures={}",
        census(corpus),
        failures.len()
    );
    for f in &failures {
        eprintln!("FAILURE {f}");
    }
    let (loaded, files) = coverage(probes);
    assert_corpus_covered(loaded, files);
    assert!(pairs > 0, "no items paired");
    assert!(
        failures.is_empty(),
        "{} items without exactly one twin; first: {}",
        failures.len(),
        failures[0]
    );
}
