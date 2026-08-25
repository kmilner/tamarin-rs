// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net over the three rule-walking wellformedness checks of the
//! translated theory: `tamarin_theory::translated_rule_wf`'s ports read the
//! elaborated rules, `tamarin_parser::wf`'s twins read the macro-expanded
//! parser theory, and the load path emits the twins' bytes.
//!
//! For every examples file the probe drives the loader's pipeline to the
//! post-translation state — parse, lift the embedded restrictions, elaborate,
//! translate the SAPIC process, translate the accountability lemmas (run.rs
//! `translate_theory`), as `tests/s3_translated_theory_probes.rs` does — and
//! compares the two reports entry by entry, topic and rendered body, for each
//! of the three topics.

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_theory::theory::Theory;

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count, so the
/// translation alone outlasts the whole rest of the corpus.  Neither file is
/// in the prove or pretty gate corpus (scripts/parity_corpus.txt).
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

/// One file's findings and what they covered.
struct FileProbe {
    outcome: Outcome,
    /// Entries compared, summed over the three topics.
    entries: usize,
    mismatches: Vec<String>,
    elapsed: Duration,
}

impl FileProbe {
    fn skipped(outcome: Outcome) -> Self {
        FileProbe {
            outcome,
            entries: 0,
            mismatches: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// The entry's rendered body, as `render_wf_error_report` takes it: the
/// laid-out fill for the checks that hand over their cells, the pre-rendered
/// message for the rest.
fn body(e: &WfError) -> String {
    match &e.fill {
        Some(fill) => tamarin_theory::wf_fill::fill_body(fill),
        None => e.message.clone(),
    }
}

/// The three topics, each with the parser-AST check the load path emits and
/// the internal port that reads the elaborated rules.
fn compare(parsed: &p::Theory, elab: &Theory, at: &dyn Fn(&str) -> String) -> (usize, Vec<String>) {
    // The parser-level checks read the theory with the macros expanded, which
    // is what the load path hands them (`splice_translated_wf_reports`).
    let post = tamarin_theory::macro_expand::macro_expanded_clone(parsed);
    let topics: [(&str, Vec<WfError>, Vec<WfError>); 3] = [
        (
            "unbound_report",
            tamarin_parser::wf::unbound_report(&post),
            tamarin_theory::translated_rule_wf::unbound_report(elab),
        ),
        (
            "fact_lhs_occur_no_rhs",
            tamarin_parser::wf::fact_lhs_occur_no_rhs(&post),
            tamarin_theory::translated_rule_wf::fact_lhs_occur_no_rhs(elab),
        ),
        (
            "nat_well_sorted_report",
            tamarin_parser::wf::nat_well_sorted_report(&post),
            tamarin_theory::translated_rule_wf::nat_well_sorted_report(elab),
        ),
    ];
    let mut entries = 0;
    let mut out = Vec::new();
    for (check, ast, internal) in topics {
        entries += ast.len();
        if ast.len() != internal.len() {
            out.push(at(&format!(
                "{check}: {} AST entries, {} internal entries",
                ast.len(),
                internal.len()
            )));
            continue;
        }
        for (i, (a, b)) in ast.iter().zip(&internal).enumerate() {
            if a.topic != b.topic {
                out.push(at(&format!(
                    "{check} #{i}: topic {:?} vs {:?}",
                    a.topic, b.topic
                )));
            }
            let (ab, bb) = (body(a), body(b));
            if ab != bb {
                out.push(at(&format!("{check} #{i}: body {ab:?} vs {bb:?}")));
            }
        }
    }
    (entries, out)
}

/// The driver's load pipeline for one file, up to the post-translation state,
/// then the comparison over that theory pair.  A diff-operator theory is
/// parsed again with the `diff` define, the way `-D=diff` enables the operator
/// on the CLI.
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
        Ok::<_, String>(compare(&parsed, &elab, &at))
    }));
    let Ok(Ok((entries, mismatches))) = found else {
        return FileProbe::skipped(Outcome::SkippedTranslate);
    };
    FileProbe {
        outcome: Outcome::Translated,
        entries,
        mismatches,
        elapsed: start.elapsed(),
    }
}

/// The corpus root, its `.spthy` files, and the probe over all of them.
type Corpus = (PathBuf, Vec<PathBuf>, Vec<FileProbe>);

/// [`probe`] over the whole tree.  `None` when the root is missing and
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
            // The parser, the translations and the term walks recurse along
            // the input; the web server renders on 64 MiB tokio threads
            // (run.rs), so the workers get the same stacks.
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(64 * 1024 * 1024)
                .build()
                .expect("rayon pool");
            let probes = pool.install(|| files.par_iter().map(|p| probe(p, &root)).collect());
            Some((root, files, probes))
        })
        .as_ref()
}

#[test]
fn internal_checks_match_the_ast_checks() {
    let Some((root, files, probes)) = corpus() else {
        return;
    };
    let count = |f: fn(&Outcome) -> bool| probes.iter().filter(|p| f(&p.outcome)).count();
    let loaded = count(|o| matches!(o, Outcome::Translated));
    let entries: usize = probes.iter().map(|p| p.entries).sum();
    let slowest = probes
        .iter()
        .zip(files)
        .max_by_key(|(p, _)| p.elapsed)
        .map(|(p, path)| format!("{} ({:?})", rel(path, root).display(), p.elapsed))
        .unwrap_or_default();
    let failures: Vec<&String> = probes.iter().flat_map(|p| &p.mismatches).collect();
    eprintln!(
        "s7 translated rule wf: files={} loaded={loaded} skipped_listed={} skipped_parse={} \
         skipped_lift={} skipped_elab={} skipped_translate={} entries={entries} \
         mismatches={} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::SkippedListed)),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
        count(|o| matches!(o, Outcome::SkippedTranslate)),
        failures.len(),
    );
    for f in &failures {
        eprintln!("FAILURE {f}");
    }
    // A probe over the corpus is a net only while it covers the tree: a change
    // that makes a stage of the pipeline reject files has to fail here instead
    // of shrinking the probe.  The tree has 19 parser rejects in 1037 files,
    // the same floor the stage-0 net holds.
    assert!(
        loaded * 20 >= files.len() * 19,
        "only {loaded} of {} files reached the probe",
        files.len()
    );
    assert!(entries > 0, "no wellformedness entries compared");
    assert!(
        failures.is_empty(),
        "{} entries differ; first: {}",
        failures.len(),
        failures[0]
    );
}
