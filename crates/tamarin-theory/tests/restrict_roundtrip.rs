// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net for the locally-nameless → parser-AST bridge
//! [`syntactic_lnformula_to_parser`], measured through the one pass that
//! consumes its output: the `_restrict` lifting.
//!
//! For every `_restrict` formula of a protocol rule and every SAPIC condition
//! and embedded-MSR restriction of the examples tree, two one-rule
//! `p::Rule`s are lifted with `rule_restriction::lift_one_rule` — one
//! carrying the parsed formula, one carrying that formula closed with
//! `formula::from_parser` and reopened with the bridge — and the generated
//! restrictions and the rewritten rule must be equal.  That comparison covers
//! predicate expansion, `rewrite`'s abstraction (whose fresh-variable counter
//! and granularity depend on the term shapes), the `frees_sorted` binder list
//! of the generated restriction and the `Restr_*` action inserted into the
//! rule, in one shot.

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use tamarin_parser::ast as p;
use tamarin_term::maude_sig::MaudeSig;
use tamarin_theory::elaborate::canonicalize_ac_in_formula;
use tamarin_theory::formula::from_parser;
use tamarin_theory::pretty_formula::syntactic_lnformula_to_parser;
use tamarin_theory::rule_restriction::{lift_one_rule, lift_rule_restrictions};

/// One formula to round-trip, tagged with where it came from.
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

/// The condition formulas and embedded-MSR restrictions of a process.
fn process_formulas(proc_: &p::Process, label: &str, out: &mut Vec<Item>) {
    match proc_ {
        p::Process::Null | p::Process::Call { .. } => {}
        p::Process::Action { action, body } => {
            if let p::SapicAction::Msr { restrictions, .. } = action {
                for (i, f) in restrictions.iter().enumerate() {
                    out.push(Item {
                        label: format!("{label}/msr-restriction-{i}"),
                        formula: f.clone(),
                    });
                }
            }
            process_formulas(body, label, out);
        }
        p::Process::Comb { comb, left, right } => {
            if let p::ProcessComb::Cond(p::Condition::Formula(f)) = comb {
                out.push(Item {
                    label: format!("{label}/cond"),
                    formula: f.clone(),
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

/// Every formula that reaches [`lift_one_rule`]: a rule's `_restrict`
/// formulas, and the SAPIC conditions and embedded-MSR restrictions the
/// translation turns into rule restrictions.
fn theory_formulas(parsed: &p::Theory) -> Vec<Item> {
    let mut out = Vec::new();
    for item in &parsed.items {
        match item {
            p::TheoryItem::Rule(rule) => {
                for (i, f) in rule.embedded_restrictions.iter().enumerate() {
                    out.push(Item {
                        label: format!("rule {}/restrict-{i}", rule.name),
                        formula: f.clone(),
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

fn predicates(parsed: &p::Theory) -> Vec<p::Predicate> {
    parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Predicates(ps) => Some(ps.clone()),
            _ => None,
        })
        .flatten()
        .collect()
}

/// What one file leaves for the formula-level phase.
struct FileReport {
    items: Vec<Item>,
    predicates: Vec<p::Predicate>,
    msig: MaudeSig,
    /// The file has items but no signature to close them against.
    skipped: bool,
}

/// Parse one file, collect its formulas, and elaborate it for the signature
/// `from_parser` closes against.  A file with no such formula costs a parse.
/// A diff-operator theory is parsed again with the `diff` define, the way
/// `-D=diff` enables the operator on the CLI.
fn file_phase(path: &Path) -> FileReport {
    let mut rep = FileReport {
        items: Vec::new(),
        predicates: Vec::new(),
        msig: MaudeSig::default(),
        skipped: false,
    };
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
    let items = theory_formulas(&parsed);
    if items.is_empty() {
        return rep;
    }
    // Elaboration runs on the lifted theory, as the production path does.
    let lifted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        lift_rule_restrictions(&mut parsed).is_ok()
    }));
    let elab = match lifted {
        Ok(true) => std::panic::catch_unwind(|| tamarin_theory::elaborate::elaborate(&parsed).ok()),
        _ => Ok(None),
    };
    let Ok(Some(elab)) = elab else {
        rep.skipped = true;
        return rep;
    };
    rep.msig = elab.signature.maude_sig.clone();
    rep.predicates = predicates(&parsed);
    rep.items = items;
    rep
}

/// The one-rule theory item `lift_one_rule` consumes: a rule whose only
/// content is the formula under test.
fn one_rule(f: &p::Formula) -> p::Rule {
    p::Rule {
        name: "C_2".to_string(),
        modulo: None,
        attributes: Vec::new(),
        let_block: Vec::new(),
        premises: Vec::new(),
        actions: Vec::new(),
        conclusions: Vec::new(),
        embedded_restrictions: vec![f.clone()],
        variants: Vec::new(),
        left_right: None,
    }
}

/// The outcome of one formula's round trip.
enum Outcome {
    Equal,
    /// `from_parser` rejects the formula (a SAPIC `=t` pattern term).
    Unconvertible(String),
    /// Predicate expansion fails on both sides alike.
    ExpandError,
    Mismatch(String),
}

/// The parsed formula and its round trip, lifted and compared.
///
/// The parsed side is AC-canonicalised first: closing a formula builds its
/// terms through `f_app_ac`, which sorts the arguments of an AC symbol, so
/// the round trip returns the canonical order while the source AST keeps the
/// written one.  Both renderers canonicalise before printing
/// (`render_rule`'s `canonicalize_ac_in_pfact`,
/// `render_parsed_restriction`'s `canonicalize_ac_in_formula`), so the
/// comparison is over the shapes that reach the output.
fn compare(item: &Item, preds: &[p::Predicate], msig: &MaudeSig) -> Outcome {
    let ln = match from_parser(&item.formula, msig) {
        Ok(ln) => ln,
        Err(e) => return Outcome::Unconvertible(format!("{}: {}", item.label, e.message)),
    };
    let reopened = syntactic_lnformula_to_parser(&ln);
    let direct = lift_one_rule(one_rule(&canonicalize_ac_in_formula(&item.formula)), preds);
    let through = lift_one_rule(one_rule(&reopened), preds);
    match (direct, through) {
        (Ok(a), Ok(b)) if a == b => Outcome::Equal,
        (Ok(a), Ok(b)) => Outcome::Mismatch(format!(
            "{}\n--- from the parsed formula\n{a:#?}\n--- through the round trip\n{b:#?}",
            item.label
        )),
        (Err(_), Err(_)) => Outcome::ExpandError,
        (a, b) => Outcome::Mismatch(format!(
            "{}: lifting agrees on neither side ({:?} / {:?})",
            item.label,
            a.err().map(|e| e.message),
            b.err().map(|e| e.message)
        )),
    }
}

#[test]
fn lift_one_rule_agrees_across_the_locally_nameless_round_trip() {
    let root = corpus_root();
    if !root.is_dir() {
        if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
            eprintln!(
                "restrict_roundtrip: root {} missing, skipped",
                root.display()
            );
            return;
        }
        panic!(
            "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
            root.display()
        );
    }
    let files = spthy_files(&root);
    // The parser recurses along the input; the web server renders on 64 MiB
    // tokio threads (run.rs), so the workers get the same.
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool");
    let reports: Vec<FileReport> =
        pool.install(|| files.par_iter().map(|p| file_phase(p)).collect());
    let files_with_items = reports.iter().filter(|r| !r.items.is_empty()).count();
    let restrict_items = reports
        .iter()
        .flat_map(|r| r.items.iter())
        .filter(|it| it.label.starts_with("rule "))
        .count();
    let skipped = reports.iter().filter(|r| r.skipped).count();
    let work: Vec<(usize, &Item)> = reports
        .iter()
        .enumerate()
        .flat_map(|(i, r)| r.items.iter().map(move |it| (i, it)))
        .collect();
    let formulas = work.len();
    let outcomes: Vec<(usize, Outcome)> = pool.install(|| {
        work.par_iter()
            .map(|(i, item)| {
                let r = &reports[*i];
                (*i, compare(item, &r.predicates, &r.msig))
            })
            .collect()
    });
    let count = |f: fn(&Outcome) -> bool| outcomes.iter().filter(|(_, o)| f(o)).count();
    let equal = count(|o| matches!(o, Outcome::Equal));
    let expand_errors = count(|o| matches!(o, Outcome::ExpandError));
    let unconvertible: Vec<String> = outcomes
        .iter()
        .filter_map(|(i, o)| match o {
            Outcome::Unconvertible(m) => Some(format!("{}: {m}", rel(&files[*i], &root).display())),
            _ => None,
        })
        .collect();
    let mismatches: Vec<String> = outcomes
        .iter()
        .filter_map(|(i, o)| match o {
            Outcome::Mismatch(m) => Some(format!("{}: {m}", rel(&files[*i], &root).display())),
            _ => None,
        })
        .collect();
    eprintln!(
        "restrict_roundtrip: files={} files_with_formulas={files_with_items} skipped={skipped} \
         formulas={formulas} rule_restricts={restrict_items} equal={equal} \
         expand_errors={expand_errors} unconvertible={} mismatches={}",
        files.len(),
        unconvertible.len(),
        mismatches.len()
    );
    for m in &mismatches {
        eprintln!("MISMATCH {m}");
    }
    for u in &unconvertible {
        eprintln!("UNCONVERTIBLE {u}");
    }
    // The comparison is a net only while it covers the tree: 129 formulas
    // over 48 files, of which 98 are rule `_restrict`s, all of them lifted on
    // both sides.  A change that stops the parser, the lifting or the
    // elaboration from reaching them has to fail here instead of shrinking
    // the comparison.
    assert!(
        equal >= 120 && restrict_items >= 90,
        "only {equal} of {formulas} formulas ({restrict_items} rule restrictions) \
         reached the comparison"
    );
    assert!(
        unconvertible.is_empty(),
        "{} formulas did not close: {:#?}",
        unconvertible.len(),
        unconvertible.iter().take(20).collect::<Vec<_>>()
    );
    assert!(
        mismatches.is_empty(),
        "{} mismatches; first: {:#?}",
        mismatches.len(),
        mismatches.iter().take(5).collect::<Vec<_>>()
    );
}
