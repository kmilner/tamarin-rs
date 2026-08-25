// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus census of what the guarded store actually holds: every lemma and
//! restriction of every `.spthy` under the examples tree is elaborated,
//! converted with `formula_to_guarded`, and the resulting [`Guarded`] is
//! walked leaf by leaf.
//!
//! HS's guarded formula is `Guarded (String, LSort) Name LVar`
//! (`Guarded.hs:391`) — its atoms are `Atom (VTerm c (BVar v))`
//! (`Guarded.hs:121`) over the internal term, where the port's atoms carry
//! parser-AST terms.  Each row below measures one difference between the two
//! payloads over the whole tree, so the size of the difference is read off
//! the corpus rather than assumed:
//!
//! * `p::VarSpec` carries a SAPIC type annotation inside `GTerm`'s derived
//!   `PartialEq`/`Hash`; `LVar` has no such field;
//! * a substitution keyed on `(name, idx)` and one keyed on the whole `LVar`
//!   agree exactly while no two free variables of one formula share a name
//!   and an index across two sorts;
//! * `em(a, b)` is the commutative symbol `canonicalize_ac_in_atom` sorts
//!   name-keyed (`elaborate.rs`, HS `fAppC`, `Term/Term/Raw.hs:133-134`),
//!   where `gterm_to_doc`'s `App` arm prints its two arguments in stored
//!   order (`pretty_formula.rs`) — a binary `em` in the guarded store is
//!   where the two orders part;
//! * and [`MOVED_FORMULAS`] counts the formulas whose stored AC argument
//!   lists are not the ones `fApp` builds (`Term/Term/Raw.hs:111-115`,
//!   `:119-129`).  `cmp_term` orders a variable leaf through `cmp_bvar`,
//!   which puts `Bound` before `Free` exactly as HS's derived `Ord BVar` does
//!   (`LTerm.hs:476-478`), so `canonicalize_ac_in_guarded` sorts the way an
//!   internal term does and its disagreement list is the measurement.

use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_term::lterm::LSort;
use tamarin_theory::atom::ProtoAtom;
use tamarin_theory::guarded::{
    canonicalize_ac_in_guarded, formula_to_guarded, BVar, GAtom, GFact, GTerm, Guarded,
};

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count.  Neither
/// file is in the prove or pretty gate corpus (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// How many corpus formulas disagree with their own AC-canonicalisation, and
/// how many files hold them.
///
/// `blnatom_to_parser` lowers each atom with every binder open and sorts its
/// AC arguments under `Ord LVar`; `subst_free_term_at_depth` then retags the
/// drawn leaves `Bound` where they stand.  A chain whose order under
/// `Ord LVar` differs from its order under the De Bruijn indices therefore
/// keeps the open order, where a term rebuilt through `fApp` carries the
/// closed one.  Every such formula is printed with both spellings; the two
/// counts are the stop condition.
const MOVED_FORMULAS: usize = 708;
const MOVED_FILES: usize = 173;

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

/// One row of the census: which formula, and what the walk found in it.
struct Finding {
    entry: String,
    detail: String,
}

/// What one guarded formula holds.
#[derive(Default)]
struct Payload {
    /// How many facts the walk reached.
    facts: usize,
    /// Free leaves carrying a SAPIC type.
    typed: Vec<String>,
    /// The sorts each `(name, idx)` is seen at.
    frees: BTreeMap<(String, u64), BTreeSet<LSort>>,
    /// Binary applications of the commutative `em`.
    emap: Vec<String>,
}

fn walk_term(t: &GTerm, out: &mut Payload) {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            if v.typ.is_some() {
                out.typed.push(format!("{v:?}"));
            }
            out.frees
                .entry((v.name.clone(), v.idx))
                .or_default()
                .insert(v.sort);
        }
        GTerm::Var(BVar::Bound(_))
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => {}
        GTerm::App(n, args) => {
            if &**n == "em" && args.len() == 2 {
                out.emap.push(format!("{t:?}"));
            }
            for a in args.iter() {
                walk_term(a, out);
            }
        }
        GTerm::Pair(items) => {
            for a in items.iter() {
                walk_term(a, out);
            }
        }
        GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
            walk_term(a, out);
            walk_term(b, out);
        }
        GTerm::PatMatch(inner) => walk_term(inner, out),
    }
}

fn walk_fact(f: &GFact, out: &mut Payload) {
    out.facts += 1;
    for a in f.terms.iter() {
        walk_term(a, out);
    }
}

fn walk_atom(a: &GAtom, out: &mut Payload) {
    match a {
        ProtoAtom::EqE(x, y) | ProtoAtom::Less(x, y) | ProtoAtom::Subterm(x, y) => {
            walk_term(x, out);
            walk_term(y, out);
        }
        ProtoAtom::Action(t, f) => {
            walk_fact(f, out);
            walk_term(t, out);
        }
        ProtoAtom::Last(t) => walk_term(t, out),
        ProtoAtom::Syntactic(_) => {}
    }
}

fn walk_guarded(g: &Guarded, out: &mut Payload) {
    match g {
        Guarded::Atom(a) => walk_atom(a, out),
        Guarded::Disj(items) | Guarded::Conj(items) => {
            for x in items.iter() {
                walk_guarded(x, out);
            }
        }
        Guarded::GGuarded { guards, body, .. } => {
            for a in guards.iter() {
                walk_atom(a, out);
            }
            walk_guarded(body, out);
        }
    }
}

/// One file's census.
#[derive(Default)]
struct FileReport {
    outcome: Option<Outcome>,
    formulas: usize,
    facts: usize,
    unguardable: usize,
    typed: Vec<Finding>,
    sort_collisions: Vec<Finding>,
    emap: Vec<Finding>,
    moved: Vec<Finding>,
    elapsed: Duration,
}

impl FileReport {
    fn skipped(outcome: Outcome) -> Self {
        FileReport {
            outcome: Some(outcome),
            ..FileReport::default()
        }
    }
}

/// Parse, lift the embedded restrictions and elaborate one file, then walk
/// the guarded form of every lemma and restriction the elaborated theory
/// holds — the formulas the solver converts.  A diff-operator theory is
/// parsed again with the `diff` define, the way `-D=diff` enables the
/// operator on the CLI.
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
    let items: Vec<(String, &tamarin_theory::formula::LNFormula)> = elab
        .items
        .iter()
        .filter_map(|it| match it {
            tamarin_theory::theory::TheoryItem::Lemma(l) => {
                Some((format!("lemma `{}'", l.name), &l.formula))
            }
            tamarin_theory::theory::TheoryItem::Restriction(r) => {
                Some((format!("restriction `{}'", r.name), &r.formula))
            }
            _ => None,
        })
        .collect();

    let mut report = FileReport {
        outcome: Some(Outcome::Elaborated),
        ..FileReport::default()
    };
    for (label, f) in &items {
        let entry = format!("{file}: {label}");
        let Ok(g) = formula_to_guarded(f) else {
            report.unguardable += 1;
            continue;
        };
        report.formulas += 1;
        let mut payload = Payload::default();
        walk_guarded(&g, &mut payload);
        report.facts += payload.facts;
        let row = |detail: String| Finding {
            entry: entry.clone(),
            detail,
        };
        report.typed.extend(payload.typed.into_iter().map(&row));
        report.emap.extend(payload.emap.into_iter().map(&row));
        for ((name, idx), sorts) in payload.frees {
            if sorts.len() > 1 {
                report
                    .sort_collisions
                    .push(row(format!("{name}.{idx} at {sorts:?}")));
            }
        }
        let canonical = canonicalize_ac_in_guarded(&g);
        if canonical != g {
            report
                .moved
                .push(row(format!("stored {g:?}\n  canonical {canonical:?}")));
        }
    }
    report.elapsed = start.elapsed();
    report
}

/// The corpus root, its `.spthy` files, and the census over all of them.
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
            // The parser, the elaboration and the walk recurse along the
            // input; the web server renders on 64 MiB tokio threads (run.rs),
            // so the workers get the same stacks.
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(64 * 1024 * 1024)
                .build()
                .expect("rayon pool");
            let reports = pool.install(|| files.par_iter().map(|p| file_phase(p, &root)).collect());
            Some((root, files, reports))
        })
        .as_ref()
}

/// The census line, and the floors that keep a walk over nothing from
/// passing: the tree has 19 parser rejects in 1037 files, the same floor
/// `guarded_from_internal.rs` holds, and the walked formulas and facts are
/// counted.  `None` when the corpus root is absent and the skip is allowed.
fn census(label: &str) -> Option<&'static [FileReport]> {
    let (root, files, reports) = corpus()?;
    let count = |f: fn(&Outcome) -> bool| {
        reports
            .iter()
            .filter(|r| r.outcome.as_ref().is_some_and(f))
            .count()
    };
    let elaborated = count(|o| matches!(o, Outcome::Elaborated));
    let formulas: usize = reports.iter().map(|r| r.formulas).sum();
    let facts: usize = reports.iter().map(|r| r.facts).sum();
    let unguardable: usize = reports.iter().map(|r| r.unguardable).sum();
    let slowest = reports
        .iter()
        .zip(files)
        .max_by_key(|(r, _)| r.elapsed)
        .map(|(r, path)| format!("{} ({:?})", rel(path, root).display(), r.elapsed))
        .unwrap_or_default();
    eprintln!(
        "guarded payload [{label}]: files={} elaborated={elaborated} skipped_listed={} \
         skipped_parse={} skipped_lift={} skipped_elab={} formulas={formulas} \
         unguardable={unguardable} facts={facts} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::SkippedListed)),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
    );
    assert!(
        elaborated * 20 >= files.len() * 19,
        "only {elaborated} of {} files reached the walk",
        files.len()
    );
    assert!(elaborated > 400, "only {elaborated} files reached the walk");
    assert!(formulas > 400, "only {formulas} formulas walked");
    assert!(facts > 0, "no facts walked");
    Some(reports)
}

/// Print every row of one census column and return its entries, sorted.
fn rows(reports: &[FileReport], column: fn(&FileReport) -> &[Finding], tag: &str) -> Vec<String> {
    let findings: Vec<&Finding> = reports.iter().flat_map(column).collect();
    for f in &findings {
        eprintln!("{tag} {}\n  {}", f.entry, f.detail);
    }
    let mut entries: Vec<String> = findings.iter().map(|f| f.entry.clone()).collect();
    entries.sort();
    entries
}

#[test]
fn corpus_guarded_variable_leaves_carry_no_sapic_type() {
    let Some(reports) = census("sapic types") else {
        return;
    };
    let entries = rows(reports, |r| &r.typed, "SAPIC-TYPE");
    assert!(
        entries.is_empty(),
        "guarded variable leaves carry a SAPIC type in: {entries:?}"
    );
}

#[test]
fn corpus_guarded_free_variables_never_collide_across_sorts() {
    let Some(reports) = census("sort collisions") else {
        return;
    };
    let entries = rows(reports, |r| &r.sort_collisions, "SORT-COLLISION");
    assert!(
        entries.is_empty(),
        "one name and index carry two sorts in: {entries:?}"
    );
}

#[test]
fn corpus_guarded_terms_never_head_a_binary_em() {
    let Some(reports) = census("emap") else {
        return;
    };
    let entries = rows(reports, |r| &r.emap, "EMAP");
    assert!(
        entries.is_empty(),
        "binary `em` applications reach the guarded store: {entries:?}"
    );
}

#[test]
fn corpus_guarded_ac_arguments_move_only_in_the_measured_set() {
    let Some(reports) = census("ac argument order") else {
        return;
    };
    let entries = rows(reports, |r| &r.moved, "MOVED");
    let files = reports.iter().filter(|r| !r.moved.is_empty()).count();
    assert_eq!(
        (entries.len(), files),
        (MOVED_FORMULAS, MOVED_FILES),
        "the set of formulas whose AC arguments move has changed"
    );
}
