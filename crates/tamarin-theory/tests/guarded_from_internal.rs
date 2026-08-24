// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net for the parser-AST entry into a guarded formula: every lemma
//! and restriction of every `.spthy` under the examples tree is converted
//! with `formula_to_guarded_parsed` and with the two steps that wrapper
//! performs — `from_parser` plus `to_lnformula`, then `formula_to_guarded`
//! — and the two `Result<Guarded, String>`s are compared.
//!
//! What the comparison holds is the wrapper's totality: a formula the
//! internal-formula lemma field has to hold reaches `LNFormula`, so neither
//! `from_parser` nor `to_lnformula` turns a convertible formula into a
//! guardedness error.  Both failures are reported as findings, and
//! [`RESIDUE`] — the sorted list of them — is empty.
//!
//! The comparison is the derived structural `==`, never `cmp_guarded`:
//! `cmp_guarded`'s AC arm flattens and re-sorts both sides, where this `==`
//! and the derived `Hash` beside it are what the solver's `stores_contains`
//! membership and the implied-formula dedup key on.

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_parser::ast as p;
use tamarin_theory::formula::{from_parser, to_lnformula};
use tamarin_theory::guarded::{formula_to_guarded, formula_to_guarded_parsed, Guarded};
use tamarin_theory::pretty_formula::pretty_guarded;

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count.  Neither
/// file is in the prove or pretty gate corpus (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// Every formula of the tree on which the wrapper and its two steps
/// disagree.  Empty: `from_parser` and `to_lnformula` reach every lemma and
/// restriction the elaborated theory holds.
const RESIDUE: &[&str] = &[];

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

/// How far one file got.
enum Outcome {
    Elaborated,
    SkippedListed,
    SkippedParse,
    SkippedLift,
    SkippedElab,
}

/// One formula on which the two routes disagree.
struct Finding {
    /// The [`RESIDUE`] line: where the disagreement is.
    entry: String,
    parsed: String,
    ln: String,
}

/// One file's comparison: how many formulas it contributed and what
/// disagreed.
struct FileReport {
    outcome: Outcome,
    formulas: usize,
    findings: Vec<Finding>,
    elapsed: Duration,
}

impl FileReport {
    fn skipped(outcome: Outcome) -> Self {
        FileReport {
            outcome,
            formulas: 0,
            findings: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// One route's outcome, as the report prints it.
fn show(g: &Result<Guarded, String>) -> String {
    match g {
        Ok(g) => pretty_guarded(g),
        Err(e) => format!("error: {e}"),
    }
}

/// Both routes on one formula: `formula_to_guarded_parsed`, and the two
/// steps it performs written out.  A formula that cannot reach `LNFormula`
/// is itself a finding — the internal-formula lemma field has to hold every
/// one of them.
fn compare(
    label: &str,
    f: &p::Formula,
    msig: &tamarin_term::maude_sig::MaudeSig,
    at: &dyn Fn(&str) -> String,
) -> Option<Finding> {
    let fail = |what: String| Finding {
        entry: at(&format!("{label}: {what}")),
        parsed: String::new(),
        ln: String::new(),
    };
    let parsed = formula_to_guarded_parsed(f, msig).map_err(|e| e.message);
    let ln = match from_parser(f, msig) {
        Err(e) => return Some(fail(format!("from_parser: {}", e.message))),
        Ok(syn) => match to_lnformula(&syn) {
            None => return Some(fail("to_lnformula: residual sugar".to_string())),
            Some(plain) => formula_to_guarded(&plain).map_err(|e| e.message),
        },
    };
    if parsed == ln {
        return None;
    }
    Some(Finding {
        entry: at(label),
        parsed: show(&parsed),
        ln: show(&ln),
    })
}

/// Parse, lift the embedded restrictions and elaborate one file, then
/// compare both routes on every lemma and restriction the elaborated theory
/// holds — the formulas `prove`, `auto_sources` and the printer convert.  A
/// diff-operator theory is parsed again with the `diff` define, the way
/// `-D=diff` enables the operator on the CLI.
fn file_phase(path: &Path, root: &Path) -> FileReport {
    let start = Instant::now();
    if BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref()) {
        return FileReport::skipped(Outcome::SkippedListed);
    }
    let Ok(src) = std::fs::read_to_string(path) else {
        return FileReport::skipped(Outcome::SkippedParse);
    };
    let base = path.parent().map(Path::to_path_buf);
    let parsed = std::panic::catch_unwind(|| {
        tamarin_parser::parser::parse_theory_with_base(&src, &[], base.clone())
            .or_else(|_| tamarin_parser::parser::parse_theory_with_base(&src, &["diff"], base))
            .ok()
    });
    let Ok(Some(mut parsed)) = parsed else {
        return FileReport::skipped(Outcome::SkippedParse);
    };
    let lifted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parsed).is_ok()
    }));
    if !matches!(lifted, Ok(true)) {
        return FileReport::skipped(Outcome::SkippedLift);
    }
    let elab = std::panic::catch_unwind(|| tamarin_theory::elaborate::elaborate(&parsed).ok());
    let Ok(Some(elab)) = elab else {
        return FileReport::skipped(Outcome::SkippedElab);
    };
    let file = rel(path, root).display().to_string();
    let at = |what: &str| format!("{file}: {what}");
    let msig = &elab.signature.maude_sig;
    let items: Vec<(String, &p::Formula)> = elab
        .lemmas()
        .map(|l| (format!("lemma `{}'", l.name), &l.formula))
        .chain(
            elab.restrictions()
                .map(|r| (format!("restriction `{}'", r.name), &r.formula)),
        )
        .collect();
    let findings = items
        .iter()
        .filter_map(|(label, f)| compare(label, f, msig, &at))
        .collect();
    FileReport {
        outcome: Outcome::Elaborated,
        formulas: items.len(),
        findings,
        elapsed: start.elapsed(),
    }
}

/// The corpus root, its `.spthy` files, and the comparison over all of them.
type Corpus = (PathBuf, Vec<PathBuf>, Vec<FileReport>);

/// [`file_phase`] over the whole tree.  `None` when the root is missing and
/// `TAM_ALLOW_NO_CORPUS=1` allows the skip.
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
            // The parser and both conversions recurse along the input; the
            // web server renders on 64 MiB tokio threads (run.rs), so the
            // workers get the same stacks.
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(64 * 1024 * 1024)
                .build()
                .expect("rayon pool");
            let reports = pool.install(|| files.par_iter().map(|p| file_phase(p, &root)).collect());
            Some((root, files, reports))
        })
        .as_ref()
}

/// A comparison over the corpus is a net only while it covers the tree: a
/// change that makes the parser, the lifting or the elaboration reject files
/// has to fail here instead of shrinking the comparison.  The tree has 19
/// parser rejects in 1037 files, the same floor the stage-0 net holds.
fn assert_corpus_covered(elaborated: usize, files: usize) {
    assert!(
        elaborated * 20 >= files * 19,
        "only {elaborated} of {files} files reached the comparison"
    );
}

#[test]
fn corpus_the_parsed_conversion_reaches_the_internal_formula() {
    let start = Instant::now();
    let Some((root, files, reports)) = corpus() else {
        return;
    };
    let count = |f: fn(&Outcome) -> bool| reports.iter().filter(|r| f(&r.outcome)).count();
    let elaborated = count(|o| matches!(o, Outcome::Elaborated));
    let formulas: usize = reports.iter().map(|r| r.formulas).sum();
    let findings: Vec<&Finding> = reports.iter().flat_map(|r| &r.findings).collect();
    let slowest = reports
        .iter()
        .zip(files)
        .max_by_key(|(r, _)| r.elapsed)
        .map(|(r, path)| format!("{} ({:?})", rel(path, root).display(), r.elapsed))
        .unwrap_or_default();
    eprintln!(
        "guarded routes: files={} elaborated={elaborated} skipped_listed={} skipped_parse={} \
         skipped_lift={} skipped_elab={} formulas={formulas} mismatches={} wall={:?} \
         slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::SkippedListed)),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
        findings.len(),
        start.elapsed(),
    );
    for f in &findings {
        eprintln!(
            "MISMATCH {}\n--- formula_to_guarded_parsed\n{}\n--- from_parser + formula_to_guarded\n{}",
            f.entry, f.parsed, f.ln
        );
    }
    assert_corpus_covered(elaborated, files.len());
    assert!(formulas > 0, "no formulas compared");
    for f in &findings {
        assert_eq!(
            f.parsed, f.ln,
            "the wrapper and its two steps disagree on {}",
            f.entry
        );
    }
    let mut entries: Vec<&str> = findings.iter().map(|f| f.entry.as_str()).collect();
    entries.sort();
    assert_eq!(entries, RESIDUE);
}
