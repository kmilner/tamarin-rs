// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net between the two renderings of a protocol rule: the internal
//! ports in `tamarin_theory::rule` / `tamarin_theory::theory` read the
//! elaborated rule, the printer in `tamarin_theory::pretty_theory` reads the
//! parser AST, and the load path emits the printer's bytes.
//!
//! For every examples file the probe drives the loader's pipeline to the
//! post-translation state — parse, lift the embedded restrictions, elaborate,
//! translate the SAPIC process, translate the accountability lemmas — as
//! `tests/s7_translated_wf_probes.rs` does, then per rule compares
//!
//!   * `pretty_proto_rule_e` against `render_rule_e_block`,
//!   * `rule::is_trivial_proto_variant_ac` against the printer's predicate,
//!
//! and per file `contains_manual_rule_variants` over the merged internal
//! items against the printer's parsed-item scan.

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_parser::ast as p;
use tamarin_theory::theory::{OpenProtoRule, Theory};

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
    /// Rules whose two renderings and two triviality verdicts were compared.
    rules: usize,
    /// Rules carrying a `variants (modulo AC)` block, which closes into one
    /// rule per block (lib/theory/src/Rule.hs:86) and so has no single AC
    /// half to put opposite the printer's per-item predicate.
    manual_variant_rules: usize,
    mismatches: Vec<String>,
    elapsed: Duration,
}

impl FileProbe {
    fn skipped(outcome: Outcome) -> Self {
        FileProbe {
            outcome,
            rules: 0,
            manual_variant_rules: 0,
            mismatches: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// The parsed rule items paired with their elaborated counterparts, by name
/// and occurrence ordinal — the printer's own resolution
/// (`pretty_theory::pair_elaborated_rules`).  Names repeat only after partial
/// evaluation and the auto-sources unfold, neither of which this pipeline
/// runs, so the ordinal is 0 throughout.
fn pairs<'a>(parsed: &'a p::Theory, elab: &'a Theory) -> Vec<(&'a p::Rule, &'a OpenProtoRule)> {
    let mut counts: tamarin_utils::FastMap<&str, usize> = Default::default();
    let mut out = Vec::new();
    for item in &parsed.items {
        let p::TheoryItem::Rule(r) = item else {
            continue;
        };
        let c = counts.entry(r.name.as_str()).or_default();
        let occ = *c;
        *c += 1;
        if let Some(er) = elab.rules().filter(|e| e.name() == r.name).nth(occ) {
            out.push((r, er));
        }
    }
    out
}

/// The two comparisons per rule plus the per-theory gate comparison.
fn compare(parsed: &p::Theory, elab: &Theory, at: &dyn Fn(&str) -> String) -> FileProbe {
    let arity1 = tamarin_theory::elaborate::arity1_noeq_names(elab.signature.maude_sig());
    let macros: Vec<p::Macro> = parsed
        .items
        .iter()
        .flat_map(|i| match i {
            p::TheoryItem::Macros(ms) => ms.as_slice(),
            _ => &[],
        })
        .cloned()
        .collect();
    let mut probe = FileProbe {
        outcome: Outcome::Translated,
        rules: 0,
        manual_variant_rules: 0,
        mismatches: Vec::new(),
        elapsed: Duration::ZERO,
    };
    for (pr, er) in pairs(parsed, elab) {
        let ast_block = tamarin_theory::pretty_theory::render_rule_e_block(pr, &arity1);
        let internal_block = tamarin_theory::rule::pretty_proto_rule_e(er.rule_e()).render();
        if internal_block != ast_block.0 {
            probe.mismatches.push(at(&format!(
                "rule {}: modulo-E block {:?} vs {:?}",
                pr.name, ast_block.0, internal_block
            )));
        }
        let ast_trivial = tamarin_theory::pretty_theory::is_trivial_proto_variant_ac(
            &ast_block.1,
            &ast_block.2,
            &ast_block.3,
            er,
            &macros,
        );
        let acs = tamarin_theory::theory::closed_rules_ac(er);
        if acs.len() != 1 {
            probe.manual_variant_rules += 1;
        } else {
            let internal_trivial =
                tamarin_theory::rule::is_trivial_proto_variant_ac(&acs[0], er.rule_e());
            if internal_trivial != ast_trivial {
                probe.mismatches.push(at(&format!(
                    "rule {}: trivial AC variant {ast_trivial} vs {internal_trivial}",
                    pr.name
                )));
            }
        }
        probe.rules += 1;
    }
    let ast_manual =
        tamarin_theory::pretty_theory::contains_manual_rule_variants(parsed, elab, false);
    let merged = tamarin_theory::theory::merge_open_proto_rules(&elab.items);
    let internal_manual = tamarin_theory::theory::contains_manual_rule_variants(&merged);
    if ast_manual != internal_manual {
        probe.mismatches.push(at(&format!(
            "contains_manual_rule_variants {ast_manual} vs {internal_manual}"
        )));
    }
    probe
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
    let Ok(Ok(mut probe)) = found else {
        return FileProbe::skipped(Outcome::SkippedTranslate);
    };
    probe.elapsed = start.elapsed();
    probe
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
fn internal_rule_render_matches_the_ast_renderer() {
    let Some((root, files, probes)) = corpus() else {
        return;
    };
    let count = |f: fn(&Outcome) -> bool| probes.iter().filter(|p| f(&p.outcome)).count();
    let loaded = count(|o| matches!(o, Outcome::Translated));
    let rules: usize = probes.iter().map(|p| p.rules).sum();
    let manual: usize = probes.iter().map(|p| p.manual_variant_rules).sum();
    let skipped_listed: Vec<String> = files
        .iter()
        .zip(probes)
        .filter(|(_, p)| matches!(p.outcome, Outcome::SkippedListed))
        .map(|(f, _)| rel(f, root).display().to_string())
        .collect();
    let slowest = probes
        .iter()
        .zip(files)
        .max_by_key(|(p, _)| p.elapsed)
        .map(|(p, path)| format!("{} ({:?})", rel(path, root).display(), p.elapsed))
        .unwrap_or_default();
    let failures: Vec<&String> = probes.iter().flat_map(|p| &p.mismatches).collect();
    eprintln!(
        "s7 render parity: files={} loaded={loaded} skipped_listed={} skipped_parse={} \
         skipped_lift={} skipped_elab={} skipped_translate={} rules={rules} \
         manual_variant_rules={manual} mismatches={} skip_list={} slowest_file={slowest}",
        files.len(),
        skipped_listed.len(),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
        count(|o| matches!(o, Outcome::SkippedTranslate)),
        failures.len(),
        skipped_listed.join(","),
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
    assert!(rules > 0, "no rules compared");
    assert!(
        failures.is_empty(),
        "{} rules differ; first: {}",
        failures.len(),
        failures[0]
    );
}
