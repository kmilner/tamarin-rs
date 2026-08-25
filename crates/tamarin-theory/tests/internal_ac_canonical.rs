// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net for the print-time AC re-sort: the parser-AST projection of
//! an internal fact or term renders the same with and without
//! `canonicalize_ac_in_pfact` / `canonicalize_ac_in_pterm`.
//!
//! That inertness is what lets a print site holding an internal value hand
//! it straight to the internal printer, as HS does: `fAppAC` sorts an AC
//! argument list at construction (`Term/Term/Raw.hs:117-129#fAppAC`) and
//! `prettyFact` (`Theory/Model/Fact.hs:567-574#prettyFact`) prints what it
//! is handed.  The canonicaliser stays where the rendered body is the
//! PARSED rule's rather than an internal one's
//! (`pretty_theory::render_rule_body`,
//! `pretty_theory::render_unfolded_variants_block`), since the order the
//! source wrote is not the order the constructor picks.
//!
//! The two projections are not structurally equal, and the assertion here
//! is not structural equality: `lnterm_to_parser` folds an AC argument
//! list LEFT while `canonicalize_ac_in_pterm` sorts it and re-folds it
//! RIGHT.  `prettyTerm` re-flattens an AC chain before printing it
//! (`Term/Term.hs:299-327#prettyTerm`, the `ppTerms` arms), so the fold
//! direction is invisible to the renderer.  What this test measures is
//! whether anything else the canonicaliser does — the argument sort of an
//! AC chain, and the argument sort of a commutative `em(a, b)` — is
//! visible either.
//!
//! Every fact of every rule body and both sides of every subterm rewrite
//! rule of the signature, over the examples tree as the driver leaves it
//! after parsing, lifting the embedded restrictions, elaborating,
//! translating the SAPIC process and translating the accountability
//! lemmas (run.rs `translate_theory`), rendered both ways at the three
//! shapes the print sites use.

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_term::lterm::LNTerm;
use tamarin_theory::elaborate::{canonicalize_ac_in_pfact, canonicalize_ac_in_pterm};
use tamarin_theory::fact::LNFact;
use tamarin_theory::pretty_formula as pf;
use tamarin_theory::pretty_hpj::{Doc, DEFAULT_LINE_LENGTH, DEFAULT_RIBBON, LINE_LENGTH, RIBBON};
use tamarin_theory::pretty_theory::{lnfact_to_parser, lnterm_to_parser};
use tamarin_theory::rule::{ProtoRuleE, ProtoRuleName};
use tamarin_theory::theory::Theory;

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count.
/// Neither file is in the prove or pretty gate corpus
/// (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// `(line length, ribbon, start column)` of every render the comparison
/// runs: the console width the `--prove` theory echo uses, the HughesPJ
/// default width the wellformedness and partial-evaluation reports use,
/// and that default width with the first line's budget shrunk by 5, which
/// is what a Doc laid out after a leading prefix gets (`render_at`'s
/// `sl_initial`).  A layout decision the re-sort could move falls
/// differently under a shrunken budget than on a full line.
const SHAPES: [(usize, usize, usize); 3] = [
    (LINE_LENGTH, RIBBON, 0),
    (DEFAULT_LINE_LENGTH, DEFAULT_RIBBON, 0),
    (DEFAULT_LINE_LENGTH, DEFAULT_RIBBON, 5),
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

/// The first shape at which `projected` and `resorted` disagree, with both
/// renders quoted.
fn disagreement(label: &str, projected: Doc, resorted: Doc) -> Option<String> {
    for (line_length, ribbon, column) in SHAPES {
        let plain = projected.clone().render_at(line_length, ribbon, column);
        let canonical = resorted.clone().render_at(line_length, ribbon, column);
        if plain != canonical {
            return Some(format!(
                "{label} at ({line_length},{ribbon},{column})\n\
                 --- projected\n{plain}\n--- re-sorted\n{canonical}"
            ));
        }
    }
    None
}

/// One fact through both fact-render paths.
fn compare_fact(label: &str, fa: &LNFact) -> Option<String> {
    let projected = lnfact_to_parser(fa);
    let resorted = canonicalize_ac_in_pfact(&projected);
    disagreement(label, pf::fact_doc(&projected), pf::fact_doc(&resorted))
}

/// One term through both term-render paths.
fn compare_term(label: &str, t: &LNTerm) -> Option<String> {
    let projected = lnterm_to_parser(t);
    let resorted = canonicalize_ac_in_pterm(&projected);
    disagreement(label, pf::term_doc(&projected), pf::term_doc(&resorted))
}

fn rule_name(r: &ProtoRuleE) -> String {
    match &r.info.name {
        ProtoRuleName::Stand(s) => (*s).to_string(),
        ProtoRuleName::Fresh => "Fresh".to_string(),
    }
}

/// Every fact of one rule body, labelled by the side it sits on and its
/// index there.
fn rule_facts(r: &ProtoRuleE) -> Vec<(String, &LNFact)> {
    let name = rule_name(r);
    [
        ("premise", &r.premises),
        ("action", &r.actions),
        ("conclusion", &r.conclusions),
    ]
    .into_iter()
    .flat_map(|(side, facts)| {
        let name = name.clone();
        facts
            .iter()
            .enumerate()
            .map(move |(i, fa)| (format!("rule `{name}' {side} {i}"), fa))
    })
    .collect()
}

/// The rule-body facts and the subterm-rule sides of one translated
/// theory, rendered both ways: how many of each, and the disagreements.
fn compare_theory(elab: &Theory, at: &dyn Fn(&str) -> String) -> (usize, usize, Vec<String>) {
    let mut findings = Vec::new();
    let mut facts = 0usize;
    let mut terms = 0usize;
    for item in elab.rules() {
        // The E-rule, plus the two bodies an item holds beside it: the
        // abstracted rule the modulo-AC comment block prints when the rule
        // has reducible-headed sub-terms, and the `cprRuleE` half an
        // `--auto-sources` close leaves behind.
        let bodies = [
            Some(&item.rule),
            item.abstracted_rule.as_ref(),
            item.rule_e.as_deref(),
        ];
        for body in bodies.into_iter().flatten() {
            for (label, fa) in rule_facts(body) {
                facts += 1;
                findings.extend(compare_fact(&at(&label), fa));
            }
        }
    }
    for (i, r) in elab.signature.maude_sig.st_rules.iter().enumerate() {
        terms += 2;
        findings.extend(compare_term(&at(&format!("equation {i} lhs")), &r.lhs));
        findings.extend(compare_term(&at(&format!("equation {i} rhs")), &r.rhs.term));
    }
    (facts, terms, findings)
}

/// Which stage of the load pipeline a file reached.
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

/// The comparison's findings for one file, plus what it counted.
struct FileProbe {
    outcome: Outcome,
    facts: usize,
    terms: usize,
    findings: Vec<String>,
    elapsed: Duration,
}

impl FileProbe {
    fn skipped(outcome: Outcome) -> Self {
        FileProbe {
            outcome,
            facts: 0,
            terms: 0,
            findings: Vec::new(),
            elapsed: Duration::ZERO,
        }
    }
}

/// The driver's load pipeline for one file — parse, lift the embedded
/// restrictions, elaborate, translate the SAPIC process, translate the
/// accountability lemmas (run.rs `translate_theory`) — then
/// [`compare_theory`] over the theory that leaves.  A diff-operator theory
/// is parsed again with the `diff` define, the way `-D=diff` enables the
/// operator on the CLI.
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
        Ok::<_, String>(compare_theory(&elab, &|what: &str| {
            format!("{file}: {what}")
        }))
    }));
    let Ok(Ok((facts, terms, findings))) = found else {
        return FileProbe::skipped(Outcome::SkippedTranslate);
    };
    FileProbe {
        outcome: Outcome::Translated,
        facts,
        terms,
        findings,
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
            // The parser, the translations and the Doc builders recurse
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

#[test]
fn corpus_internal_facts_render_the_same_with_and_without_the_ac_resort() {
    let start = Instant::now();
    let Some((root, files, probes)) = corpus() else {
        return;
    };
    let count = |f: fn(&Outcome) -> bool| probes.iter().filter(|p| f(&p.outcome)).count();
    let translated = count(|o| matches!(o, Outcome::Translated));
    let facts: usize = probes.iter().map(|p| p.facts).sum();
    let terms: usize = probes.iter().map(|p| p.terms).sum();
    let findings: Vec<&String> = probes.iter().flat_map(|p| &p.findings).collect();
    let slowest = probes
        .iter()
        .zip(files)
        .max_by_key(|(p, _)| p.elapsed)
        .map(|(p, path)| format!("{} ({:?})", rel(path, root).display(), p.elapsed))
        .unwrap_or_default();
    eprintln!(
        "internal AC re-sort: files={} translated={translated} skipped_listed={} \
         skipped_parse={} skipped_lift={} skipped_elab={} skipped_translate={} \
         facts={facts} terms={terms} findings={} wall={:?} slowest_file={slowest}",
        files.len(),
        count(|o| matches!(o, Outcome::SkippedListed)),
        count(|o| matches!(o, Outcome::SkippedParse)),
        count(|o| matches!(o, Outcome::SkippedLift)),
        count(|o| matches!(o, Outcome::SkippedElab)),
        count(|o| matches!(o, Outcome::SkippedTranslate)),
        findings.len(),
        start.elapsed()
    );
    for f in &findings {
        eprintln!("DISAGREEMENT {f}");
    }
    assert_corpus_covered(translated, files.len());
    assert!(facts > 0, "no facts compared");
    assert!(terms > 0, "no equation sides compared");
    assert!(
        findings.is_empty(),
        "{} disagreements; first: {}",
        findings.len(),
        findings[0]
    );
}
