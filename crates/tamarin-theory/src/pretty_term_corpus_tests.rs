// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net for `prettyTerm` over the internal term
//! (`tamarin_term::pretty::pretty_term`, `Term/Term.hs:299-327`): every
//! `LNTerm` the elaborated theories of the examples tree hold renders the
//! same three ways.
//!
//! * through `pretty_nterm` — the `Doc` built from the internal term;
//! * through `pretty_theory::lnterm_to_parser` + the AC canonicaliser +
//!   `pretty_formula::term_doc` — the parser-AST projection the print
//!   sites hand to the AST renderer;
//! * flat, against `pretty_lnterm`, the `String` printer the JSON
//!   abbreviation sort key and the contradiction text use.
//!
//! The two `Doc`s are compared at three shapes rather than flat, because a
//! difference in `Doc` structure — a break point one side has and the
//! other does not — is invisible on a line that fits.

use rayon::prelude::*;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use tamarin_term::lterm::LNTerm;
use tamarin_term::pretty::{pretty_lnterm, pretty_nterm};
use tamarin_term::term::Term;

use crate::elaborate::canonicalize_ac_in_pterm;
use crate::pretty_formula as pf;
use crate::pretty_hpj::{DEFAULT_LINE_LENGTH, DEFAULT_RIBBON, FLAT_WIDTH, LINE_LENGTH, RIBBON};
use crate::pretty_theory::lnterm_to_parser;
use crate::rule::{ProtoRuleE, ProtoRuleName};
use crate::test_corpus::{beyond_budget, corpus_root, parse_file, rel, spthy_files};
use crate::theory::Theory;

/// `(line length, ribbon, start column)` of every render the comparison
/// runs: the console width the `--prove` theory echo uses, the HughesPJ
/// default width the wellformedness and partial-evaluation reports use,
/// and that default width with the first line's budget shrunk by 5, which
/// is what a `Doc` laid out after a leading prefix gets (`render_at`'s
/// `sl_initial`).
const SHAPES: [(usize, usize, usize); 3] = [
    (LINE_LENGTH, RIBBON, 0),
    (DEFAULT_LINE_LENGTH, DEFAULT_RIBBON, 0),
    (DEFAULT_LINE_LENGTH, DEFAULT_RIBBON, 5),
];

/// `t` and every one of its sub-terms, outermost first.
fn subterms<'a>(t: &'a LNTerm, out: &mut Vec<&'a LNTerm>) {
    out.push(t);
    if let Term::App(_, args) = t {
        for a in args.iter() {
            subterms(a, out);
        }
    }
}

fn rule_name(r: &ProtoRuleE) -> String {
    match &r.info.name {
        ProtoRuleName::Stand(s) => (*s).to_string(),
        ProtoRuleName::Fresh => "Fresh".to_string(),
    }
}

/// Every term of one rule body, labelled by where it sits.
fn rule_terms(r: &ProtoRuleE) -> Vec<(String, &LNTerm)> {
    let name = rule_name(r);
    let mut out: Vec<(String, &LNTerm)> = Vec::new();
    for (side, facts) in [
        ("premise", &r.premises),
        ("action", &r.actions),
        ("conclusion", &r.conclusions),
    ] {
        for (i, fa) in facts.iter().enumerate() {
            for (j, t) in fa.terms.iter().enumerate() {
                out.push((format!("rule `{name}' {side} {i} term {j}"), t));
            }
        }
    }
    for (i, t) in r.new_vars.iter().enumerate() {
        out.push((format!("rule `{name}' new var {i}"), t));
    }
    out
}

/// Every distinct term of one theory, with the label of where it was first
/// seen.  A rule body repeats its sub-terms across variants and sides, so
/// the comparison runs once per distinct term.
fn theory_terms(elab: &Theory) -> Vec<(String, &LNTerm)> {
    let mut roots: Vec<(String, &LNTerm)> = Vec::new();
    for item in elab.rules() {
        // The E-rule, plus the abstracted body the modulo-AC comment block
        // prints when the rule has reducible-headed sub-terms.
        for body in [Some(&item.rule), item.abstracted_rule.as_ref()]
            .into_iter()
            .flatten()
        {
            roots.extend(rule_terms(body));
        }
    }
    for (i, r) in elab.signature.maude_sig.st_rules.iter().enumerate() {
        roots.push((format!("equation {i} lhs"), &r.lhs));
        roots.push((format!("equation {i} rhs"), &r.rhs.term));
    }
    let mut seen: BTreeSet<&LNTerm> = BTreeSet::new();
    let mut out: Vec<(String, &LNTerm)> = Vec::new();
    for (label, root) in roots {
        let mut all: Vec<&LNTerm> = Vec::new();
        subterms(root, &mut all);
        for t in all {
            if seen.insert(t) {
                out.push((label.clone(), t));
            }
        }
    }
    out
}

/// The first shape at which the internal `Doc` and the projected one
/// disagree, with both renders quoted.
fn compare_doc(label: &str, t: &LNTerm) -> Option<String> {
    let internal = pretty_nterm(t);
    let projected = pf::term_doc(&canonicalize_ac_in_pterm(&lnterm_to_parser(t)));
    for (line_length, ribbon, column) in SHAPES {
        let a = internal.clone().render_at(line_length, ribbon, column);
        let b = projected.clone().render_at(line_length, ribbon, column);
        if a != b {
            return Some(format!(
                "{label} at ({line_length},{ribbon},{column})\n\
                 --- internal\n{a}\n--- projected\n{b}"
            ));
        }
    }
    None
}

/// The flat render against the `String` printer.
fn compare_flat(label: &str, t: &LNTerm) -> Option<String> {
    let flat = pretty_nterm(t).render_with(FLAT_WIDTH, FLAT_WIDTH);
    let string = pretty_lnterm(t);
    (flat != string).then(|| format!("{label}\n--- flat Doc\n{flat}\n--- pretty_lnterm\n{string}"))
}

/// Which stage of the load pipeline a file reached.
enum Outcome {
    Elaborated,
    SkippedListed,
    SkippedParse,
    SkippedLift,
    SkippedElab,
}

/// The comparison's findings for one file, plus what it counted.
struct FileProbe {
    outcome: Outcome,
    terms: usize,
    doc_findings: Vec<String>,
    flat_findings: Vec<String>,
    elapsed: Duration,
}

impl FileProbe {
    fn skipped(outcome: Outcome) -> Self {
        FileProbe {
            outcome,
            terms: 0,
            doc_findings: Vec::new(),
            flat_findings: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// Parse, lift the embedded restrictions and elaborate one file, then
/// compare every term of the theory that leaves.
fn probe(path: &Path, root: &Path) -> FileProbe {
    let start = Instant::now();
    if beyond_budget(path, root) {
        return FileProbe::skipped(Outcome::SkippedListed);
    }
    let Some(mut parsed) = parse_file(path) else {
        return FileProbe::skipped(Outcome::SkippedParse);
    };
    let lifted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::rule_restriction::lift_rule_restrictions(&mut parsed).is_ok()
    }));
    if !matches!(lifted, Ok(true)) {
        return FileProbe::skipped(Outcome::SkippedLift);
    }
    let elab = std::panic::catch_unwind(|| crate::elaborate::elaborate(&parsed).ok());
    let Ok(Some(elab)) = elab else {
        return FileProbe::skipped(Outcome::SkippedElab);
    };
    let file = rel(path, root).display().to_string();
    let terms = theory_terms(&elab);
    let mut doc_findings = Vec::new();
    let mut flat_findings = Vec::new();
    for (label, t) in &terms {
        let at = format!("{file}: {label}");
        doc_findings.extend(compare_doc(&at, t));
        flat_findings.extend(compare_flat(&at, t));
    }
    FileProbe {
        outcome: Outcome::Elaborated,
        terms: terms.len(),
        doc_findings,
        flat_findings,
        elapsed: start.elapsed(),
    }
}

/// The corpus root, its `.spthy` files, and the comparison over all of them.
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
            // The parser and the Doc builders recurse along the input; the
            // web server renders on 64 MiB tokio threads (run.rs), so the
            // workers get the same stacks.
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(64 * 1024 * 1024)
                .build()
                .expect("rayon pool");
            let probes = pool.install(|| files.par_iter().map(|p| probe(p, &root)).collect());
            Some((root, files, probes))
        })
        .as_ref()
}

/// A comparison over the corpus is a net only while it covers the tree: a
/// change that makes a stage of the pipeline reject files has to fail here
/// instead of shrinking the comparison.  The tree has 19 parser rejects in
/// 1037 files, the same floor the other corpus nets hold.
fn assert_corpus_covered(loaded: usize, files: usize) {
    assert!(
        loaded * 20 >= files * 19,
        "only {loaded} of {files} files reached the comparison"
    );
}

/// The census line every test of this module shares, and the terms counted.
fn census(what: &str, start: Instant) -> usize {
    let Some((root, files, probes)) = corpus() else {
        return 0;
    };
    let count = |f: fn(&Outcome) -> bool| probes.iter().filter(|p| f(&p.outcome)).count();
    let terms: usize = probes.iter().map(|p| p.terms).sum();
    let slowest = probes
        .iter()
        .zip(files)
        .max_by_key(|(p, _)| p.elapsed)
        .map(|(p, path)| format!("{} ({:?})", rel(path, root).display(), p.elapsed))
        .unwrap_or_default();
    eprintln!(
        "{what}: files={} elaborated={} skipped_listed={} skipped_parse={} skipped_lift={} \
         skipped_elab={} terms={terms} wall={:?} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::Elaborated)),
        count(|o| matches!(o, Outcome::SkippedListed)),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
        start.elapsed()
    );
    assert_corpus_covered(count(|o| matches!(o, Outcome::Elaborated)), files.len());
    terms
}

#[test]
fn corpus_pretty_nterm_matches_the_projected_doc() {
    let start = Instant::now();
    let Some((_, _, probes)) = corpus() else {
        return;
    };
    let terms = census("prettyTerm vs projection", start);
    let findings: Vec<&String> = probes.iter().flat_map(|p| &p.doc_findings).collect();
    for f in &findings {
        eprintln!("DISAGREEMENT {f}");
    }
    assert!(terms > 0, "no terms compared");
    assert!(
        findings.is_empty(),
        "{} disagreements; first: {}",
        findings.len(),
        findings[0]
    );
}

#[test]
fn corpus_pretty_lnterm_matches_the_flat_doc() {
    let start = Instant::now();
    let Some((_, _, probes)) = corpus() else {
        return;
    };
    let terms = census("prettyTerm flat vs pretty_lnterm", start);
    let findings: Vec<&String> = probes.iter().flat_map(|p| &p.flat_findings).collect();
    for f in &findings {
        eprintln!("DISAGREEMENT {f}");
    }
    assert!(terms > 0, "no terms compared");
    assert!(
        findings.is_empty(),
        "{} disagreements; first: {}",
        findings.len(),
        findings[0]
    );
}
