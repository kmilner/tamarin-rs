// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net for the locally-nameless formula conversions: every formula
//! of every `.spthy` under the examples tree, built exactly as the
//! production renderers build their `Doc` input, is
//!
//!   * printed through the parser-AST printer and through
//!     `syntactic_lnformula_doc` (and `lnformula_doc` where the sugar
//!     strips), and the renders compared through both production wrappers
//!     and through the flat render the guarded-conversion error text uses;
//!   * converted with `from_parser` from both the raw and the
//!     print-preprocessed parser AST, and the two results compared;
//!   * checked for the two parser-AST shapes the round trip cannot carry
//!     back — source-order fact annotations and a `VarSpec` type tag.

use super::*;
use crate::elaborate::{canonicalize_ac_in_formula as canon, rewrite_arity1_formula};
use crate::fact::FactAnnotation;
use crate::formula::{from_parser, sapic_from_parser, to_lnformula};
use crate::macro_expand::apply_macros_formula;
use crate::pretty_sapic::render_sapic;
use crate::pretty_theory::{collect_macros, collect_predicates, expand_predicates_for_display};
use crate::sapic::to_lformula;
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count, so a
/// session-4 lemma takes minutes through the renders below and session 5
/// overflows the stack.  Neither file is in the prove or pretty
/// gate corpus (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// One formula to compare, tagged with where it came from.
///
/// `pre` is the formula before the printer's own preprocessing — for a
/// lemma or restriction header the predicate-expanded (and, in the
/// `(macros)` variant, macro-expanded) formula, for a SAPIC condition or
/// embedded `_restrict` the formula as written.  `formula` is `pre` after
/// the arity-1 fold and the AC canonicalisation the matching renderer
/// applies.  `sapic` marks the items a SAPIC process prints, whose
/// internal form is built by [`sapic_from_parser`].
struct Item {
    label: String,
    formula: p::Formula,
    pre: p::Formula,
    sapic: bool,
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
/// both as written and AC-canonicalised the way the `Msr` and `Cond` arms
/// of `pretty_sapic` render them.
fn process_formulas(proc_: &p::Process, label: &str, out: &mut Vec<Item>) {
    match proc_ {
        p::Process::Null | p::Process::Call { .. } => {}
        p::Process::Action { action, body } => {
            if let p::SapicAction::Msr { restrictions, .. } = action {
                for (i, f) in restrictions.iter().enumerate() {
                    out.push(Item {
                        label: format!("{label}/msr-restriction-{i}"),
                        formula: canon(f),
                        pre: f.clone(),
                        sapic: true,
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
                    pre: f.clone(),
                    sapic: true,
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
    let item = |label: String, pre: p::Formula, formula: p::Formula| Item {
        label,
        formula,
        pre,
        sapic: false,
    };
    let header_items = |out: &mut Vec<Item>, kind: &str, name: &str, f: &p::Formula| {
        let pre = expand_predicates_for_display(f, &predicates);
        out.push(item(
            format!("{kind} {name}"),
            pre.clone(),
            canon(&arity1(&pre)),
        ));
        if !macros.is_empty() {
            let pre = expand_predicates_for_display(&apply_macros_formula(&macros, f), &predicates);
            out.push(item(
                format!("{kind} {name} (macros)"),
                pre.clone(),
                canon(&arity1(&pre)),
            ));
        }
    };
    let mut out = Vec::new();
    for it in &parsed.items {
        match it {
            p::TheoryItem::Lemma(lem) => header_items(&mut out, "lemma", &lem.name, &lem.formula),
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                header_items(&mut out, "restriction", &r.name, &r.formula)
            }
            p::TheoryItem::AccLemma(al) => out.push(item(
                format!("acclemma {}", al.name),
                al.formula.clone(),
                canon(&arity1(&al.formula)),
            )),
            p::TheoryItem::CaseTest(ct) => out.push(item(
                format!("casetest {}", ct.name),
                ct.formula.clone(),
                canon(&arity1(&ct.formula)),
            )),
            p::TheoryItem::Predicates(ps) => {
                for pr in ps {
                    out.push(item(
                        format!("predicate {}", pr.fact.name),
                        pr.formula.clone(),
                        arity1(&pr.formula),
                    ));
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
    msig: std::sync::Arc<tamarin_term::maude_sig::MaudeSig>,
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
        msig: std::sync::Arc::new(tamarin_term::maude_sig::MaudeSig::default()),
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
    rep.msig = std::sync::Arc::new(elab.signature.maude_sig.clone());
    let arity1_names = crate::elaborate::arity1_noeq_names(elab.signature.maude_sig());
    let arity1 = |f: &p::Formula| rewrite_arity1_formula(f, &arity1_names);
    rep.items = theory_formulas(&parsed, &arity1);
    rep.outcome = Outcome::Parsed;
    rep.elapsed = start.elapsed();
    rep
}

/// The corpus root, its `.spthy` files, and the file-level phase over all
/// of them.
type Corpus = (PathBuf, Vec<PathBuf>, Vec<FileReport>);

/// A pool whose workers can take the parser's and the Doc builders'
/// recursion along the input; the web server renders on 64 MiB tokio
/// threads (run.rs), so they get the same stacks.
fn deep_pool() -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool")
}

/// Parse, lift, elaborate and collect the whole tree.  `None` when the
/// root is missing and `TAM_ALLOW_NO_CORPUS=1` allows the skip.
fn corpus_phase() -> Option<Corpus> {
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
    let reports: Vec<FileReport> = deep_pool().install(|| {
        files
            .par_iter()
            .map(|path| file_phase(path, &root))
            .collect()
    });
    Some((root, files, reports))
}

/// [`corpus_phase`] run once for every test in this module: they read the
/// same items, and parsing, lifting and elaborating the tree is the
/// expensive half.
fn corpus() -> Option<&'static Corpus> {
    static CORPUS: OnceLock<Option<Corpus>> = OnceLock::new();
    CORPUS.get_or_init(corpus_phase).as_ref()
}

/// Files that reached the formula-level phase, and the whole tree.
fn file_counts(reports: &[FileReport]) -> (usize, usize) {
    let parsed = reports
        .iter()
        .filter(|r| matches!(r.outcome, Outcome::Parsed))
        .count();
    (parsed, reports.len())
}

/// A comparison over the corpus is a net only while it covers the tree: a
/// change that makes the parser, the lifting or the elaboration reject
/// files has to fail here instead of shrinking the comparison.  The tree
/// has 19 parser rejects in 1037 files.
fn assert_corpus_covered(parsed: usize, files: usize) {
    assert!(
        parsed * 20 >= files * 19,
        "only {parsed} of {files} files reached the comparison"
    );
}

/// Every item of the tree, each with the index of the file it came from —
/// which is where its label and its signature are read.
fn all_items(corpus: &Corpus) -> Vec<(usize, &Item)> {
    corpus
        .2
        .iter()
        .enumerate()
        .flat_map(|(i, r)| r.items.iter().map(move |it| (i, it)))
        .collect()
}

/// `<file>: <label>` of one finding.
fn at(corpus: &Corpus, i: usize, label: &str) -> String {
    format!("{}: {label}", rel(&corpus.1[i], &corpus.0).display())
}

/// `(label, parser-AST render, locally-nameless render)` of one disagreement.
type Mismatch = (String, String, String);

/// Both printers on one formula through all three production shapes: the
/// lemma header, the nested restriction body, and the flat one-line string
/// the guarded-conversion error text quotes.
fn compare(item: &Item, msig: &tamarin_term::maude_sig::MaudeSig) -> Vec<Mismatch> {
    let f = &item.formula;
    let ast = formula_to_doc(f, &[], &mut avoid_precise_formula(f));
    let ast_header = lemma_header_line_doc("all-traces", ast.clone());
    let ast_nested = doublequoted_nested_doc(ast, 2);
    let ast_flat = pretty_formula(f);
    let ln = match from_parser(f, msig) {
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
        let nested = doublequoted_nested_doc(doc.clone(), 2);
        if nested != ast_nested {
            mismatches.push((
                format!("{} [{kind} nested]", item.label),
                ast_nested.clone(),
                nested,
            ));
        }
        let flat = doc.render_with(FLAT_WIDTH, FLAT_WIDTH);
        if flat != ast_flat {
            mismatches.push((
                format!("{} [{kind} flat]", item.label),
                ast_flat.clone(),
                flat,
            ));
        }
    }
    mismatches
}

#[test]
fn corpus_lnformula_doc_matches_ast_printer() {
    let start = Instant::now();
    let Some(corpus) = corpus() else {
        return;
    };
    let (root, files, reports) = corpus;
    let count = |o: fn(&Outcome) -> bool| reports.iter().filter(|r| o(&r.outcome)).count();
    let parsed = count(|o| matches!(o, Outcome::Parsed));
    let skipped_listed = count(|o| matches!(o, Outcome::SkippedListed));
    let skipped_parse = count(|o| matches!(o, Outcome::SkippedParse));
    let skipped_lift = count(|o| matches!(o, Outcome::SkippedLift));
    let skipped_elab = count(|o| matches!(o, Outcome::SkippedElab));
    let slowest_file = reports
        .iter()
        .zip(files)
        .max_by_key(|(r, _)| r.elapsed)
        .map(|(r, path)| format!("{} ({:?})", rel(path, root).display(), r.elapsed))
        .unwrap_or_default();
    let work = all_items(corpus);
    let formulas = work.len();
    let results: Vec<(usize, Duration, Vec<Mismatch>)> = deep_pool().install(|| {
        work.par_iter()
            .map(|(i, item)| {
                let t = Instant::now();
                let found = compare(item, &reports[*i].msig);
                (*i, t.elapsed(), found)
            })
            .collect()
    });
    let slowest_formula = results
        .iter()
        .zip(&work)
        .max_by_key(|((_, d, _), _)| *d)
        .map(|((i, d, _), (_, item))| at(corpus, *i, &format!("{} ({d:?})", item.label)))
        .unwrap_or_default();
    let mismatches: Vec<(String, String, String)> = results
        .iter()
        .flat_map(|(i, _, found)| {
            found
                .iter()
                .map(move |(label, ast, ln)| (at(corpus, *i, label), ast.clone(), ln.clone()))
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
    for (where_, ast, ln) in &mismatches {
        eprintln!("MISMATCH {where_}\n--- ast\n{ast}\n--- ln\n{ln}");
    }
    assert_corpus_covered(parsed, files.len());
    assert!(formulas > 0, "no formulas compared");
    assert!(
        mismatches.is_empty(),
        "{} mismatches; first: {:#?}",
        mismatches.len(),
        mismatches.iter().take(20).collect::<Vec<_>>()
    );
}

#[test]
fn corpus_from_parser_absorbs_the_print_preprocessing() {
    let start = Instant::now();
    let Some(corpus) = corpus() else {
        return;
    };
    let (parsed, files) = file_counts(&corpus.2);
    let work = all_items(corpus);
    let formulas = work.len();
    let build = |f: &p::Formula, msig: &tamarin_term::maude_sig::MaudeSig| {
        from_parser(f, msig).map_err(|e| e.message)
    };
    let mismatches: Vec<String> = deep_pool().install(|| {
        work.par_iter()
            .filter_map(|(i, item)| {
                let msig = &corpus.2[*i].msig;
                let raw = build(&item.pre, msig);
                let pre_passed = build(&item.formula, msig);
                (raw != pre_passed).then(|| {
                    format!(
                        "MISMATCH {}\n--- from_parser(pre)\n{raw:?}\n--- from_parser(preprocessed)\n{pre_passed:?}",
                        at(corpus, *i, &item.label)
                    )
                })
            })
            .collect()
    });
    eprintln!(
        "corpus from_parser: files={files} parsed={parsed} formulas={formulas} mismatches={} wall={:?}",
        mismatches.len(),
        start.elapsed()
    );
    for m in &mismatches {
        eprintln!("{m}");
    }
    assert_corpus_covered(parsed, files);
    assert!(formulas > 0, "no formulas compared");
    assert!(
        mismatches.is_empty(),
        "{} mismatches; first: {}",
        mismatches.len(),
        mismatches[0]
    );
}

/// The `VarSpec`s and the fact-carrying atoms of one formula, in traversal
/// order.
#[derive(Default)]
struct Shapes<'a> {
    vars: Vec<&'a p::VarSpec>,
    facts: Vec<&'a p::Fact>,
}

fn collect_term<'a>(t: &'a p::Term, out: &mut Shapes<'a>) {
    match t {
        p::Term::Var(v) => out.vars.push(v),
        p::Term::App(_, ts) | p::Term::Pair(ts) => ts.iter().for_each(|t| collect_term(t, out)),
        p::Term::AlgApp(_, a, b) | p::Term::BinOp(_, a, b) => {
            collect_term(a, out);
            collect_term(b, out);
        }
        p::Term::Diff(a, b) => {
            collect_term(a, out);
            collect_term(b, out);
        }
        p::Term::PatMatch(inner) => collect_term(inner, out),
        p::Term::PubLit(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => {}
    }
}

fn collect_fact<'a>(f: &'a p::Fact, out: &mut Shapes<'a>) {
    out.facts.push(f);
    f.args.iter().for_each(|t| collect_term(t, out));
}

fn collect_atom<'a>(a: &'a p::Atom, out: &mut Shapes<'a>) {
    match a {
        p::Atom::Eq(x, y)
        | p::Atom::Less(x, y)
        | p::Atom::LessMset(x, y)
        | p::Atom::Subterm(x, y) => {
            collect_term(x, out);
            collect_term(y, out);
        }
        p::Atom::Action(f, t) => {
            collect_fact(f, out);
            collect_term(t, out);
        }
        p::Atom::Last(t) => collect_term(t, out),
        p::Atom::Pred(f) => collect_fact(f, out),
    }
}

fn collect_formula<'a>(f: &'a p::Formula, out: &mut Shapes<'a>) {
    match f {
        p::Formula::True | p::Formula::False => {}
        p::Formula::Atom(a) => collect_atom(a, out),
        p::Formula::Not(g) => collect_formula(g, out),
        p::Formula::And(x, y)
        | p::Formula::Or(x, y)
        | p::Formula::Implies(x, y)
        | p::Formula::Iff(x, y) => {
            collect_formula(x, out);
            collect_formula(y, out);
        }
        p::Formula::Forall(vs, g) | p::Formula::Exists(vs, g) => {
            out.vars.extend(vs.iter());
            collect_formula(g, out);
        }
    }
}

fn shapes(f: &p::Formula) -> Shapes<'_> {
    let mut out = Shapes::default();
    collect_formula(f, &mut out);
    out
}

/// The internal annotation a parser annotation converts to
/// (`elaborate::copy_fact_annotations`), whose `Ord` orders the `BTreeSet`
/// the internal fact stores (`fact.rs:39-44`, `:97`).
fn internal_annotation(a: &p::FactAnnotation) -> FactAnnotation {
    match a {
        p::FactAnnotation::SolveFirst => FactAnnotation::SolveFirst,
        p::FactAnnotation::SolveLast => FactAnnotation::SolveLast,
        p::FactAnnotation::NoSources => FactAnnotation::NoSources,
    }
}

/// Whether a parser fact's source-order annotation list is what the
/// internal fact's `BTreeSet` gives back: strictly increasing under the
/// internal `Ord`, so neither reordered nor duplicated.
fn annotations_are_ord_sorted(annotations: &[p::FactAnnotation]) -> bool {
    let anns: Vec<FactAnnotation> = annotations.iter().map(internal_annotation).collect();
    anns.windows(2).all(|w| w[0] < w[1])
}

#[test]
fn annotations_written_out_of_ord_order_are_not_ord_sorted() {
    assert!(annotations_are_ord_sorted(&[
        p::FactAnnotation::SolveFirst,
        p::FactAnnotation::NoSources,
    ]));
    assert!(!annotations_are_ord_sorted(&[
        p::FactAnnotation::NoSources,
        p::FactAnnotation::SolveFirst,
    ]));
    assert!(!annotations_are_ord_sorted(&[
        p::FactAnnotation::SolveLast,
        p::FactAnnotation::SolveLast,
    ]));
}

#[test]
fn corpus_fact_annotations_are_ord_sorted() {
    let start = Instant::now();
    let Some(corpus) = corpus() else {
        return;
    };
    let (parsed, files) = file_counts(&corpus.2);
    let work = all_items(corpus);
    let formulas = work.len();
    let mut annotated = 0usize;
    let mut mismatches: Vec<String> = Vec::new();
    for (i, item) in &work {
        for fact in shapes(&item.formula).facts {
            if fact.annotations.is_empty() {
                continue;
            }
            annotated += 1;
            if !annotations_are_ord_sorted(&fact.annotations) {
                mismatches.push(format!(
                    "MISMATCH {} fact {}: {:?}",
                    at(corpus, *i, &item.label),
                    fact.name,
                    fact.annotations
                ));
            }
        }
    }
    eprintln!(
        "corpus annotations: files={files} parsed={parsed} formulas={formulas} \
         annotated_facts={annotated} mismatches={} wall={:?}",
        mismatches.len(),
        start.elapsed()
    );
    for m in &mismatches {
        eprintln!("{m}");
    }
    assert_corpus_covered(parsed, files);
    assert!(formulas > 0, "no formulas walked");
    assert!(
        mismatches.is_empty(),
        "{} facts whose annotations the BTreeSet round trip reorders; first: {}",
        mismatches.len(),
        mismatches[0]
    );
}

#[test]
fn corpus_no_typed_varspec_in_theory_formulas() {
    let start = Instant::now();
    let Some(corpus) = corpus() else {
        return;
    };
    let (parsed, files) = file_counts(&corpus.2);
    let work = all_items(corpus);
    let formulas = work.len();
    let mut vars = 0usize;
    let mut sapic_typed = 0usize;
    let mut mismatches: Vec<String> = Vec::new();
    for (i, item) in &work {
        for v in shapes(&item.formula).vars {
            vars += 1;
            if v.typ.is_none() {
                continue;
            }
            // A SAPIC condition is parsed by `standardFormula sapicvar
            // sapicnodevar` (Theory/Text/Parser/Sapic.hs:253-254), whose
            // variables carry the SAPIC type annotation; `sapic_from_parser`
            // is the instantiation that keeps it.
            if item.sapic {
                sapic_typed += 1;
            } else {
                mismatches.push(format!(
                    "MISMATCH {} variable {}:{:?}",
                    at(corpus, *i, &item.label),
                    v.name,
                    v.typ
                ));
            }
        }
    }
    eprintln!(
        "corpus varspec types: files={files} parsed={parsed} formulas={formulas} variables={vars} \
         sapic_typed={sapic_typed} mismatches={} wall={:?}",
        mismatches.len(),
        start.elapsed()
    );
    for m in &mismatches {
        eprintln!("{m}");
    }
    assert_corpus_covered(parsed, files);
    assert!(vars > 0, "no variables walked");
    assert!(
        mismatches.is_empty(),
        "{} typed variables outside a SAPIC formula; first: {}",
        mismatches.len(),
        mismatches[0]
    );
}

/// The two SAPIC assertions on one item, and whether the process printer's
/// own width breaks the formula over more than one line.
///
/// A `Cond` and an embedded `_restrict` are parsed by `standardFormula
/// sapicvar sapicnodevar` (Theory/Text/Parser/Sapic.hs:253-254), so
/// [`sapic_from_parser`] is the instantiation that builds them, and the
/// printer drops the type tags with `toLFormula` first
/// (`prettySyntacticSapicFormula`, Theory/Sapic/Term.hs:174-175).  Dropping
/// them has to land on the formula [`from_parser`] builds directly.  The
/// render comparison is against [`pretty_formula`], which is always flat, so
/// it runs at [`FLAT_WIDTH`] and compares content — AC operand order, atom
/// shape, spelling — and not layout.
fn compare_sapic(item: &Item, msig: &tamarin_term::maude_sig::MaudeSig) -> Result<bool, Mismatch> {
    let raw = &item.pre;
    let label = |what: &str| format!("{} [{what}]", item.label);
    let sapic = match sapic_from_parser(raw, msig) {
        Ok(f) => f,
        Err(e) => return Err((label("sapic_from_parser"), String::new(), e.message)),
    };
    let ln = match from_parser(raw, msig) {
        Ok(f) => f,
        Err(e) => return Err((label("from_parser"), String::new(), e.message)),
    };
    let dropped = to_lformula(&sapic);
    if dropped != ln {
        return Err((
            label("to_lformula"),
            format!("{ln:?}"),
            format!("{dropped:?}"),
        ));
    }
    let doc = syntactic_lnformula_doc(&dropped);
    let flat = doc.clone().render_with(FLAT_WIDTH, FLAT_WIDTH);
    let ast = pretty_formula(&item.formula);
    if flat != ast {
        return Err((label("render"), ast, flat));
    }
    Ok(render_sapic(doc) != flat)
}

#[test]
fn corpus_sapic_condition_render_matches_the_internal_printer() {
    let start = Instant::now();
    let Some(corpus) = corpus() else {
        return;
    };
    let (parsed, files) = file_counts(&corpus.2);
    let work: Vec<(usize, &Item)> = all_items(corpus)
        .into_iter()
        .filter(|(_, it)| it.sapic)
        .collect();
    let sapic_items = work.len();
    let results: Vec<(usize, &Item, Result<bool, Mismatch>)> = deep_pool().install(|| {
        work.par_iter()
            .map(|&(i, item)| (i, item, compare_sapic(item, &corpus.2[i].msig)))
            .collect()
    });
    let mismatches: Vec<String> = results
        .iter()
        .filter_map(|(i, _, r)| match r {
            Err((label, expected, got)) => Some(format!(
                "MISMATCH {}\n--- expected\n{expected}\n--- got\n{got}",
                at(corpus, *i, label)
            )),
            Ok(_) => None,
        })
        .collect();
    // The census, not an assertion: these are the items whose bytes move
    // when the process printer renders the condition and each `_restrict`
    // as a `Doc` at HS's own width instead of flat.
    let wrapping: Vec<String> = results
        .iter()
        .filter_map(|(i, item, r)| match r {
            Ok(true) => Some(at(corpus, *i, &item.label)),
            _ => None,
        })
        .collect();
    eprintln!(
        "corpus sapic: files={files} parsed={parsed} sapic_items={sapic_items} mismatches={} \
         wrapping_items={} wall={:?}",
        mismatches.len(),
        wrapping.len(),
        start.elapsed()
    );
    for item in &wrapping {
        eprintln!("WRAPS {item}");
    }
    for m in &mismatches {
        eprintln!("{m}");
    }
    assert_corpus_covered(parsed, files);
    assert!(sapic_items > 0, "no SAPIC formulas compared");
    assert!(
        mismatches.is_empty(),
        "{} mismatches; first: {}",
        mismatches.len(),
        mismatches[0]
    );
}
