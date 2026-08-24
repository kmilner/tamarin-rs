// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Corpus net for the two routes into a guarded formula: every lemma and
//! restriction of every `.spthy` under the examples tree is converted from
//! the parser AST `elaborate` stores (`formula_to_guarded`) and from the
//! locally-nameless formula the same AST closes into
//! (`formula_to_guarded_ln` over `from_parser` and `to_lnformula`), and the
//! two `Result<Guarded, String>`s are compared.
//!
//! The comparison is the derived structural `==`, never `cmp_guarded`:
//! `cmp_guarded`'s AC arm flattens and re-sorts both sides, which is exactly
//! the class of difference — the AC fold direction and the argument order a
//! freshened binder can move — this net exists to catch.  The same `==` and
//! the derived `Hash` beside it are what the solver's `stores_contains`
//! membership and the implied-formula dedup key on.
//!
//! [`RESIDUE`] lists the formulas where the two routes disagree, with two
//! causes:
//!
//! * 32 of them differ in the ARGUMENT ORDER of a `++` chain.  HS's
//!   `openFormulaPrefix` substitutes the freshened binders into the body
//!   through `mapLits`, whose `fApp` re-sorts the AC arguments under the
//!   drawn `LVar`s (Theory/Model/Formula.hs:279-284, Term/Term/Raw.hs:118-129),
//!   and `Ord LVar` reads the index first (LTerm.hs:545-548); the parser-AST
//!   route sorts once up front under the source variables and carries the
//!   freshened names in the diagnostic alone.  Every one of these files binds
//!   one name in two sibling quantifier prefixes, so the second prefix draws
//!   `b3.1` where the source wrote `b3`.  All 32 are marked `canonical forms
//!   agree`: `canonicalize_ac_in_guarded`, which every solver entry applies
//!   (simplify.rs, reduction.rs), maps the two values together.  The pinned
//!   oracle rejects all ten files at load — six on a parse error the port
//!   does not raise, four on a Maude failure — so none of them is in the
//!   prove or pretty gate corpus (scripts/parity_corpus.txt).
//! * one differs in the SURFACE SPELLING of a binary application: the parser
//!   AST records `sdec{m}k` as `Term::AlgApp` and `sdec(m, k)` as
//!   `Term::App`, while HS `binaryAlgApp` builds one `fAppNoEq` for both
//!   (Theory/Text/Parser/Term.hs:109-121), so an internal term cannot say
//!   which of them the source spells.  The two spellings share a `cmp_term`
//!   key and a printed form, and they differ under the derived `PartialEq`.
//!   This one is on a gate-corpus file.

use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use tamarin_parser::ast as p;
use tamarin_theory::formula::{from_parser, to_lnformula};
use tamarin_theory::guarded::{
    canonicalize_ac_in_guarded, formula_to_guarded, formula_to_guarded_ln, Guarded,
};
use tamarin_theory::pretty_formula::pretty_guarded;

/// Examples beyond this test's budget, relative to the corpus root and
/// reported as `skipped_listed`: the accountability lemmas of the mixvote
/// multi-session family grow geometrically with the session count.  Neither
/// file is in the prove or pretty gate corpus (scripts/parity_corpus.txt).
const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// Every formula of the tree on which the two routes disagree, sorted, with
/// whether `canonicalize_ac_in_guarded` maps the two values together.  A
/// diff theory elaborates a left and a right lemma of one name, so its
/// entries appear twice.  The module header states the two causes.
const RESIDUE: &[&str] = &[
    "csf20-disputeResolution/mixvote_ShHh_RF.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF.spthy: lemma `VoterC' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalLHS.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalLHS.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalLHS.spthy: lemma `VoterC' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalLHS.spthy: lemma `VoterC' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalRHS.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalRHS.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalRHS.spthy: lemma `VoterC' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_functionalRHS.spthy: lemma `VoterC' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_reuseAsRestriction.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf20-disputeResolution/mixvote_ShHh_RF_reuseAsRestriction.spthy: lemma `VoterC' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF.spthy: lemma `VoterC' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF.spthy: lemma `VoterC' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF_reuseAsRestriction.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF_reuseAsRestriction.spthy: lemma `TimelyP' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF_reuseAsRestriction.spthy: lemma `VoterC' [canonical forms agree]",
    "csf26-ac/multiset-UD/csf20-disputeResolution/mixvote_ShHh_RF_reuseAsRestriction.spthy: lemma `VoterC' [canonical forms agree]",
    "loops/Typing_and_Destructors.spthy: lemma `type_assertion' [canonical forms differ]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF.spthy: lemma `DRvoterC' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF.spthy: lemma `DRvoterT' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_LHS.spthy: lemma `DRvoterC' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_LHS.spthy: lemma `DRvoterC' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_LHS.spthy: lemma `DRvoterT' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_LHS.spthy: lemma `DRvoterT' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_RHS.spthy: lemma `DRvoterC' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_RHS.spthy: lemma `DRvoterC' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_RHS.spthy: lemma `DRvoterT' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_functional_RHS.spthy: lemma `DRvoterT' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_reuseAsRestriction.spthy: lemma `DRvoterC' [canonical forms agree]",
    "thesis-LaraSchmid-evoting/chapter4_DisputeResolution/aletheaDR_ShHh_RF_reuseAsRestriction.spthy: lemma `DRvoterT' [canonical forms agree]",
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
    /// The [`RESIDUE`] line: where it is and whether the canonical forms
    /// agree.
    entry: String,
    ast: String,
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

/// The guarded formula at the AC order every solver entry puts it in.
fn canonical(g: &Result<Guarded, String>) -> Result<Guarded, String> {
    match g {
        Ok(g) => Ok(canonicalize_ac_in_guarded(g)),
        Err(e) => Err(e.clone()),
    }
}

/// Both routes on one formula: the parser AST as `elaborate` stores it, and
/// the locally-nameless formula `from_parser` closes it into.  A formula
/// that cannot reach `LNFormula` is itself a finding — the internal-formula
/// lemma field has to hold every one of them.
fn compare(
    label: &str,
    f: &p::Formula,
    msig: &tamarin_term::maude_sig::MaudeSig,
    at: &dyn Fn(&str) -> String,
) -> Option<Finding> {
    let fail = |what: String| Finding {
        entry: at(&format!("{label}: {what}")),
        ast: String::new(),
        ln: String::new(),
    };
    let ast = formula_to_guarded(f).map_err(|e| e.message);
    let ln = match from_parser(f, msig) {
        Err(e) => return Some(fail(format!("from_parser: {}", e.message))),
        Ok(syn) => match to_lnformula(&syn) {
            None => return Some(fail("to_lnformula: residual sugar".to_string())),
            Some(plain) => formula_to_guarded_ln(&plain).map_err(|e| e.message),
        },
    };
    if ast == ln {
        return None;
    }
    let canon = if canonical(&ast) == canonical(&ln) {
        "canonical forms agree"
    } else {
        "canonical forms differ"
    };
    Some(Finding {
        entry: at(&format!("{label} [{canon}]")),
        ast: show(&ast),
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
fn corpus_guarded_agrees_across_the_locally_nameless_route() {
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
            "MISMATCH {}\n--- parser AST route\n{}\n--- locally-nameless route\n{}",
            f.entry, f.ast, f.ln
        );
    }
    assert_corpus_covered(elaborated, files.len());
    assert!(formulas > 0, "no formulas compared");
    let mut entries: Vec<&str> = findings.iter().map(|f| f.entry.as_str()).collect();
    entries.sort();
    assert_eq!(entries, RESIDUE);
}
