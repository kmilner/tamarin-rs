// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus equality net for the locally-nameless formula printers: every
//! formula of every `.spthy` under the examples tree, built exactly as the
//! production renderers build their `Doc` input, is printed through the
//! parser-AST printer and through `syntactic_lnformula_doc` (and
//! `lnformula_doc` where the sugar strips), and the renders are compared
//! through both production wrappers.

use super::*;
use crate::elaborate::{
    canonicalize_ac_in_formula as canon, rewrite_arity1_formula, CollectedUserFuns,
};
use crate::formula::{from_parser, to_lnformula};
use crate::macro_expand::apply_macros_formula;
use crate::pretty_theory::{collect_macros, collect_predicates, expand_predicates_for_display};
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count, so a
/// session-4 lemma takes about a minute through the six renders below and
/// session 5 overflows the stack.  Neither file is in the prove or pretty
/// gate corpus (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// One formula to compare, tagged with where it came from.
struct Item {
    label: String,
    formula: p::Formula,
}

/// The examples tree, or the override in `CORPUS_ROOT`.
fn corpus_root() -> PathBuf {
    if let Ok(root) = std::env::var("CORPUS_ROOT") {
        return PathBuf::from(root);
    }
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
}

/// `path` relative to the corpus root, as the listing and the report name it.
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

/// SAPIC condition formulas and embedded-rule restrictions of a process,
/// AC-canonicalised as `pretty_sapic` renders them (pretty_sapic.rs `Msr`
/// and `Cond` arms).
fn process_formulas(proc_: &p::Process, label: &str, out: &mut Vec<Item>) {
    match proc_ {
        p::Process::Null | p::Process::Call { .. } => {}
        p::Process::Action { action, body } => {
            if let p::SapicAction::Msr { restrictions, .. } = action {
                for (i, f) in restrictions.iter().enumerate() {
                    out.push(Item {
                        label: format!("{label}/msr-restriction-{i}"),
                        formula: canon(f),
                    });
                }
            }
            process_formulas(body, label, out);
        }
        p::Process::Comb { comb, left, right } => {
            if let p::ProcessComb::Cond(p::Condition::Formula(f)) = comb {
                out.push(Item {
                    label: format!("{label}/cond"),
                    formula: canon(f),
                });
            }
            process_formulas(left, label, out);
            process_formulas(right, label, out);
        }
        p::Process::Replication(body) | p::Process::AtAnnotation(body, _) => {
            process_formulas(body, label, out);
        }
    }
}

/// Every formula the theory prints, built as the production renderer
/// builds it: lemma and restriction headers are predicate-expanded,
/// arity-1-folded and AC-canonicalised (`render_parsed_lemma`,
/// `render_parsed_restriction`), and their guarded-block variant applies
/// the theory's macros first when there are any (`render_guarded_block`);
/// accountability lemmas and case tests are arity-1-folded and
/// canonicalised; predicate bodies are only arity-1-folded.
fn theory_formulas(parsed: &p::Theory, arity1: &dyn Fn(&p::Formula) -> p::Formula) -> Vec<Item> {
    let macros = collect_macros(parsed);
    let predicates = collect_predicates(parsed);
    let header = |f: &p::Formula| canon(&arity1(&expand_predicates_for_display(f, &predicates)));
    let header_items = |out: &mut Vec<Item>, kind: &str, name: &str, f: &p::Formula| {
        out.push(Item {
            label: format!("{kind} {name}"),
            formula: header(f),
        });
        if !macros.is_empty() {
            out.push(Item {
                label: format!("{kind} {name} (macros)"),
                formula: header(&apply_macros_formula(&macros, f)),
            });
        }
    };
    let mut out = Vec::new();
    for item in &parsed.items {
        match item {
            p::TheoryItem::Lemma(lem) => header_items(&mut out, "lemma", &lem.name, &lem.formula),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                header_items(&mut out, "restriction", &r.name, &r.formula)
            }
            p::TheoryItem::AccLemma(al) => out.push(Item {
                label: format!("acclemma {}", al.name),
                formula: canon(&arity1(&al.formula)),
            }),
            p::TheoryItem::CaseTest(ct) => out.push(Item {
                label: format!("casetest {}", ct.name),
                formula: canon(&arity1(&ct.formula)),
            }),
            p::TheoryItem::Predicates(ps) => {
                for pr in ps {
                    out.push(Item {
                        label: format!("predicate {}", pr.fact.name),
                        formula: arity1(&pr.formula),
                    });
                }
            }
            p::TheoryItem::ProcessDef(pd) => {
                process_formulas(&pd.body, &format!("let {}", pd.name), &mut out)
            }
            p::TheoryItem::TopLevelProcess(pr) | p::TheoryItem::DiffEquivLemma(pr) => {
                process_formulas(pr, "process", &mut out)
            }
            p::TheoryItem::EquivLemma(l, r) => {
                process_formulas(l, "equivlemma-left", &mut out);
                process_formulas(r, "equivlemma-right", &mut out);
            }
            _ => {}
        }
    }
    out
}

enum Outcome {
    Parsed,
    SkippedListed,
    SkippedParse,
    SkippedLift,
    SkippedElab,
}

/// What the file-level phase leaves for the formula-level phase.
struct FileReport {
    outcome: Outcome,
    items: Vec<Item>,
    user_funs: CollectedUserFuns,
    elapsed: Duration,
}

/// Parse, lift the embedded restrictions, elaborate and collect the
/// formulas of one file; a failure or panic in one of those steps skips
/// the file.  A diff-operator theory is parsed again with the `diff`
/// define, the way `-D=diff` enables the operator on the CLI.
fn file_phase(path: &Path, root: &Path) -> FileReport {
    let start = Instant::now();
    let mut rep = FileReport {
        outcome: Outcome::SkippedParse,
        items: Vec::new(),
        user_funs: CollectedUserFuns::default(),
        elapsed: Duration::ZERO,
    };
    if BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref()) {
        rep.outcome = Outcome::SkippedListed;
        return rep;
    }
    let Ok(src) = std::fs::read_to_string(path) else {
        return rep;
    };
    let base = path.parent().map(Path::to_path_buf);
    let parsed = std::panic::catch_unwind(|| {
        tamarin_parser::parser::parse_theory_with_base(&src, &[], base.clone())
            .or_else(|_| tamarin_parser::parser::parse_theory_with_base(&src, &["diff"], base))
            .ok()
    });
    let Ok(Some(mut parsed)) = parsed else {
        return rep;
    };
    let lifted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::rule_restriction::lift_rule_restrictions(&mut parsed).is_ok()
    }));
    if !matches!(lifted, Ok(true)) {
        rep.outcome = Outcome::SkippedLift;
        return rep;
    }
    let elab = std::panic::catch_unwind(|| crate::elaborate::elaborate(&parsed).ok());
    let Ok(Some(elab)) = elab else {
        rep.outcome = Outcome::SkippedElab;
        return rep;
    };
    rep.user_funs = crate::elaborate::collect_user_funs_for_theory(&parsed);
    let _guard = crate::elaborate::set_user_funs_from_collected(&rep.user_funs);
    let arity1_names = crate::elaborate::arity1_noeq_names(elab.signature.maude_sig());
    let arity1 = |f: &p::Formula| rewrite_arity1_formula(f, &arity1_names);
    rep.items = theory_formulas(&parsed, &arity1);
    rep.outcome = Outcome::Parsed;
    rep.elapsed = start.elapsed();
    rep
}

/// `(label, parser-AST render, locally-nameless render)` of one disagreement.
type Mismatch = (String, String, String);

/// Both printers on one formula through both production wrappers; the
/// thread-local user-function bundle is the one the file's renderers run
/// under.
fn compare(item: &Item, user_funs: &CollectedUserFuns) -> Vec<Mismatch> {
    let _guard = crate::elaborate::set_user_funs_from_collected(user_funs);
    let f = &item.formula;
    let ast = formula_to_doc(f, &[], &mut avoid_precise_formula(f));
    let ast_header = lemma_header_line_doc("all-traces", ast.clone());
    let ast_nested = doublequoted_nested_doc(ast, 2);
    let ln = match from_parser(f) {
        Ok(ln) => ln,
        Err(e) => {
            return vec![(
                item.label.clone(),
                ast_header,
                format!("from_parser: {}", e.message),
            )]
        }
    };
    let mut docs = vec![("syntactic", syntactic_lnformula_doc(&ln))];
    if let Some(plain) = to_lnformula(&ln) {
        docs.push(("plain", lnformula_doc(&plain)));
    }
    let mut mismatches = Vec::new();
    for (kind, doc) in docs {
        let header = lemma_header_line_doc("all-traces", doc.clone());
        if header != ast_header {
            mismatches.push((
                format!("{} [{kind} header]", item.label),
                ast_header.clone(),
                header,
            ));
            continue;
        }
        let nested = doublequoted_nested_doc(doc, 2);
        if nested != ast_nested {
            mismatches.push((
                format!("{} [{kind} nested]", item.label),
                ast_nested.clone(),
                nested,
            ));
        }
    }
    mismatches
}

#[test]
fn corpus_lnformula_doc_matches_ast_printer() {
    let root = corpus_root();
    if !root.is_dir() {
        if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
            eprintln!("corpus: root {} missing, skipped", root.display());
            return;
        }
        panic!(
            "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
            root.display()
        );
    }
    let files = spthy_files(&root);
    let start = Instant::now();
    // The parser and the Doc builders recurse along the input; the web
    // server renders on 64 MiB tokio threads (run.rs), so the workers get
    // the same.
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool");
    let reports: Vec<FileReport> = pool.install(|| {
        files
            .par_iter()
            .map(|path| file_phase(path, &root))
            .collect()
    });
    let count = |o: fn(&Outcome) -> bool| reports.iter().filter(|r| o(&r.outcome)).count();
    let parsed = count(|o| matches!(o, Outcome::Parsed));
    let skipped_listed = count(|o| matches!(o, Outcome::SkippedListed));
    let skipped_parse = count(|o| matches!(o, Outcome::SkippedParse));
    let skipped_lift = count(|o| matches!(o, Outcome::SkippedLift));
    let skipped_elab = count(|o| matches!(o, Outcome::SkippedElab));
    let slowest_file = reports
        .iter()
        .zip(&files)
        .max_by_key(|(r, _)| r.elapsed)
        .map(|(r, path)| format!("{} ({:?})", rel(path, &root).display(), r.elapsed))
        .unwrap_or_default();
    let work: Vec<(usize, &Item)> = reports
        .iter()
        .enumerate()
        .flat_map(|(i, r)| r.items.iter().map(move |it| (i, it)))
        .collect();
    let formulas = work.len();
    let results: Vec<(usize, Duration, Vec<Mismatch>)> = pool.install(|| {
        work.par_iter()
            .map(|(i, item)| {
                let t = Instant::now();
                let found = compare(item, &reports[*i].user_funs);
                (*i, t.elapsed(), found)
            })
            .collect()
    });
    let slowest_formula = results
        .iter()
        .zip(&work)
        .max_by_key(|((_, d, _), _)| *d)
        .map(|((i, d, _), (_, item))| {
            format!(
                "{}: {} ({d:?})",
                rel(&files[*i], &root).display(),
                item.label
            )
        })
        .unwrap_or_default();
    let mismatches: Vec<(String, String, String, String)> = results
        .iter()
        .flat_map(|(i, _, found)| {
            let file = rel(&files[*i], &root);
            found.iter().map(move |(label, ast, ln)| {
                (
                    file.display().to_string(),
                    label.clone(),
                    ast.clone(),
                    ln.clone(),
                )
            })
        })
        .collect();
    eprintln!(
        "corpus: files={} parsed={parsed} skipped_listed={skipped_listed} skipped_parse={skipped_parse} \
         skipped_lift={skipped_lift} skipped_elab={skipped_elab} formulas={formulas} mismatches={} \
         wall={:?} slowest_file={slowest_file} slowest_formula={slowest_formula}",
        files.len(),
        mismatches.len(),
        start.elapsed()
    );
    for (file, label, ast, ln) in &mismatches {
        eprintln!("MISMATCH {file}: {label}\n--- ast\n{ast}\n--- ln\n{ln}");
    }
    // The comparison is a net only while it covers the tree: a change that
    // makes the parser, the lifting or the elaboration reject files has to
    // fail here instead of shrinking the comparison.  The tree has 11
    // parser rejects in 1037 files.
    assert!(
        parsed * 20 >= files.len() * 19,
        "only {parsed} of {} files reached the comparison",
        files.len()
    );
    assert!(formulas > 0, "no formulas compared");
    assert!(
        mismatches.is_empty(),
        "{} mismatches; first: {:#?}",
        mismatches.len(),
        mismatches.iter().take(20).collect::<Vec<_>>()
    );
}
