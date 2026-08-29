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
//! (`Guarded.hs:121`) over the internal term.  Each row below is a property
//! of that store read off the corpus rather than assumed:
//!
//! * a substitution keyed on `(name, idx)` and one keyed on the whole `LVar`
//!   agree exactly while no two free variables of one formula share a name
//!   and an index across two sorts;
//! * `em` is the commutative symbol `fAppC` sorts (`Term/Term/Raw.hs:
//!   133-134`), and the printer's application arm writes its arguments in
//!   stored order (`pretty_formula.rs`) — a binary `em` in the guarded store
//!   is where a stored order could differ from a printed one;
//! * and [`NON_CANONICAL_FORMULAS`] counts the formulas whose stored AC and
//!   `C` argument lists are not the ones `fApp` builds
//!   (`Term/Term/Raw.hs:111-115`, `:119-134`).

use crate::corpus_util;
use crate::corpus_util::{deep_pool, rel, LoadSkip};
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_term::function_symbols::{CSym, FunSym};
use tamarin_term::lterm::{BVar, LSort};
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;
use tamarin_theory::atom::{Atom, ProtoAtom};
use tamarin_theory::fact::Fact;
use tamarin_theory::formula::BLNTerm;
use tamarin_theory::guarded::{formula_to_guarded, is_ac_canonical, Guarded};

/// How many corpus formulas hold an AC or `C` argument list `fApp` would
/// order differently, and how many files hold them.
///
/// Every atom of the store is built through `fApp` (`f_app`, `f_app_ac`,
/// `f_app_c`), which flattens and sorts those two argument lists, so the
/// census expects none.  Any row printed here is a construction path that
/// bypassed `fApp`.
const NON_CANONICAL_FORMULAS: usize = 0;
const NON_CANONICAL_FILES: usize = 0;

/// How far one file got.
enum Outcome {
    Elaborated,
    Skipped(LoadSkip),
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
    /// The sorts each `(name, idx)` is seen at.
    frees: BTreeMap<(String, u64), BTreeSet<LSort>>,
    /// Binary applications of the commutative `em`.
    emap: Vec<String>,
}

fn walk_term(t: &BLNTerm, out: &mut Payload) {
    match t {
        Term::Lit(Lit::Var(BVar::Free(v))) => {
            out.frees
                .entry((v.name.to_string(), v.idx))
                .or_default()
                .insert(v.sort);
        }
        Term::Lit(_) => {}
        Term::App(sym, args) => {
            if matches!(sym, FunSym::C(CSym::EMap)) && args.len() == 2 {
                out.emap.push(format!("{t:?}"));
            }
            for a in args.iter() {
                walk_term(a, out);
            }
        }
    }
}

fn walk_fact(f: &Fact<BLNTerm>, out: &mut Payload) {
    out.facts += 1;
    for a in f.terms.iter() {
        walk_term(a, out);
    }
}

fn walk_atom(a: &Atom<BLNTerm>, out: &mut Payload) {
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
    sort_collisions: Vec<Finding>,
    emap: Vec<Finding>,
    non_canonical: Vec<Finding>,
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

/// Run one file through the load ladder, then walk the guarded form of
/// every lemma and restriction the elaborated theory holds — the formulas
/// the solver converts.
fn file_phase(path: &Path, root: &Path) -> FileReport {
    let start = Instant::now();
    let elab = match corpus_util::load_elaborated(path, root) {
        Ok(loaded) => loaded,
        Err(skip) => return FileReport::skipped(Outcome::Skipped(skip)),
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
        report.emap.extend(payload.emap.into_iter().map(&row));
        for ((name, idx), sorts) in payload.frees {
            if sorts.len() > 1 {
                report
                    .sort_collisions
                    .push(row(format!("{name}.{idx} at {sorts:?}")));
            }
        }
        if !is_ac_canonical(&g) {
            report.non_canonical.push(row(format!("stored {g:?}")));
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
            let (root, files) = corpus_util::corpus_files("corpus")?;
            let reports =
                deep_pool().install(|| files.par_iter().map(|p| file_phase(p, &root)).collect());
            Some((root, files, reports))
        })
        .as_ref()
}

/// The census line, and the floors that keep a walk over nothing from
/// passing: the shared coverage floor, and counts of the walked formulas
/// and facts.  `None` when the corpus root is absent and the skip is
/// allowed.
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
         skipped_parse={} skipped_elab={} formulas={formulas} \
         unguardable={unguardable} facts={facts} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::Skipped(LoadSkip::Listed))),
        count(|o| matches!(o, Outcome::Skipped(LoadSkip::Parse))),
        count(|o| matches!(o, Outcome::Skipped(LoadSkip::Elab))),
    );
    corpus_util::assert_expected_skips(
        root,
        files
            .iter()
            .zip(reports)
            .filter_map(|(path, report)| match report.outcome.as_ref()? {
                Outcome::Elaborated => None,
                Outcome::Skipped(skip) => Some((path.as_path(), skip.reason())),
            }),
        corpus_util::EXPECTED_LOAD_SKIPS,
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
fn corpus_guarded_ac_arguments_are_canonical() {
    let Some(reports) = census("ac argument order") else {
        return;
    };
    let entries = rows(reports, |r| &r.non_canonical, "NON-CANONICAL");
    let files = reports
        .iter()
        .filter(|r| !r.non_canonical.is_empty())
        .count();
    assert_eq!(
        (entries.len(), files),
        (NON_CANONICAL_FORMULAS, NON_CANONICAL_FILES),
        "a stored formula holds an argument list `fApp` would order differently"
    );
}
