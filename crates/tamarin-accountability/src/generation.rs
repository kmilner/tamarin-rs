// Currently GPL 3.0 until granted permission by the following authors:
//   kevinmorio, arcz, rkunnema, xaDxelA, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/accountability/src/Accountability/Generation.hs,
//   lib/theory/src/Items/AccLemmaItem.hs,
//   lib/theory/src/Items/CaseTestItem.hs

//! Port of `Accountability.Generation` (lib/accountability/src/Accountability/Generation.hs):
//! the seven verification-condition generators and their fresh-counter
//! threading.
//!
//! Each accountability lemma expands to one lemma per condition family, in the
//! order `casesLemmas` fixes (Generation.hs:249-261): all `suff`, then
//! `verif_empty`, then all `verif_nonempty`, `min`, `uniq`, `inj`, `single`.
//! A single fresh counter starting at 0 (HS `evalFreshT (casesLemmas ..) 0`,
//! Generation.hs:263-264, see line 264) is threaded through the families that call `rename`
//! (`suff`, `min`, `single`), in exactly that visitation order.

use tamarin_parser::ast as p;

use crate::formula::{
    corrupt_subset_frees, fold_conn, fold_l1, fold_r1, free_var_term, frees, lvar_eq,
    proto_fact_formula, quantify_frees, quantify_vars, rename, strict_subset_of, temp_var,
    to_intermediate, vars_eq, Conn, Fm, Quant,
};

/// A resolved case test (HS `CaseTest`, Items/CaseTestItem.hs:20-24).
pub(crate) struct CaseTestData {
    pub(crate) name: String,
    pub(crate) formula: Fm,
}

/// A resolved accountability lemma (HS `AccLemma`, Items/AccLemmaItem.hs).  The
/// lemma's `_aAttributes` are held separately by the caller and copied onto each
/// generated lemma at injection time.
pub(crate) struct AccData {
    pub(crate) name: String,
    pub(crate) formula: Fm,
    pub(crate) case_tests: Vec<CaseTestData>,
}

/// One generated lemma (HS `ProtoLemma SyntacticLNFormula ProofSkeleton`);
/// the formula is still locally-nameless and gets opened to `p::Formula` by the
/// caller.
pub(crate) struct GenLemma {
    pub(crate) name: String,
    pub(crate) quantifier: p::TraceQuantifier,
    pub(crate) formula: Fm,
}

/// HS `toLemma accLemma quantifier suffix formula` (Generation.hs:26-33): wraps
/// the generated formula with its name and trace quantifier.  The accountability
/// lemma's attributes (HS `_aAttributes`) are copied onto each generated lemma
/// by the injection step in `lib.rs`.
fn to_lemma(quantifier: p::TraceQuantifier, name: String, formula: Fm) -> GenLemma {
    GenLemma { name, quantifier, formula }
}

/// HS `caseTestFormulasExcept` (Generation.hs:107-109): the formulas of all
/// case tests except `ct`, in order.
fn case_test_formulas_except(acc: &AccData, ct: &CaseTestData) -> Vec<Fm> {
    acc.case_tests
        .iter()
        .filter(|c| c.name != ct.name)
        .map(|c| c.formula.clone())
        .collect()
}

/// HS `andIf p a b = if p then a .&&. b else a` (Generation.hs:97-98).  `b` is
/// evaluated lazily (HS is non-strict): the `noOther` conjunct is a `foldr1`
/// that is undefined on the empty case-test-formula list, so it must not be
/// forced when `p_` is false.
fn and_if(p_: bool, a: Fm, b: impl FnOnce() -> Fm) -> Fm {
    if p_ {
        a.and(b())
    } else {
        a
    }
}

/// HS `singleMatch t` (Generation.hs:101-105):
/// `rename t; rename t; t1 .&&. ∀ frees(t2). (t2 ⇒ varsEq (frees t2) (frees t1))`.
fn single_match(t: &Fm, counter: &mut u64) -> Fm {
    let t1 = rename(t, counter);
    let t2 = rename(t, counter);
    let f2 = frees(&t2);
    let f1 = frees(&t1);
    let body = t2.implies(vars_eq(&f2, &f1));
    t1.and(quantify_vars(Quant::All, &f2, body))
}

/// HS `noOther fms = foldr1 (.&&.) (map (Not . quantifyFrees exists) fms)`
/// (Generation.hs:94-95).
fn no_other(taus: &[Fm]) -> Fm {
    fold_r1(
        Conn::And,
        taus.iter().map(|t| quantify_frees(Quant::Ex, t.clone()).not()).collect(),
    )
}

/// HS `freesSubsetCorrupt vars` (Generation.hs:65-69):
/// `foldl1 (.&&.) [ ∃ i. Corrupted(var)@i | var <- vars ]`.
fn frees_subset_corrupt(vars: &[p::VarSpec]) -> Fm {
    fold_l1(
        Conn::And,
        vars.iter()
            .map(|v| {
                quantify_vars(
                    Quant::Ex,
                    &[temp_var("i")],
                    proto_fact_formula(
                        "Corrupted",
                        vec![free_var_term(v.clone())],
                        free_var_term(temp_var("i")),
                    ),
                )
            })
            .collect(),
    )
}

/// HS `sufficiency` (Generation.hs:172-182).
fn sufficiency(acc: &AccData, ct: &CaseTestData, counter: &mut u64) -> GenLemma {
    let name = format!("{}_{}_suff", acc.name, ct.name);
    let taus = case_test_formulas_except(acc, ct);
    let t1 = single_match(&ct.formula, counter);
    let f1 = frees(&t1);
    let inner = t1.clone().and(and_if(
        !taus.is_empty(),
        corrupt_subset_frees(&f1),
        || no_other(&taus),
    ));
    let formula = quantify_frees(Quant::Ex, inner);
    to_lemma(p::TraceQuantifier::ExistsTrace, name, to_intermediate(formula))
}

/// HS `verifiabilityEmpty` (Generation.hs:184-191).  NOTE: the only family
/// that does NOT apply `toIntermediate` — the formula is returned raw.
fn verifiability_empty(acc: &AccData) -> GenLemma {
    let name = format!("{}_verif_empty", acc.name);
    let taus: Vec<Fm> = acc.case_tests.iter().map(|c| c.formula.clone()).collect();
    let lhs = fold_conn(
        Conn::Or,
        taus.into_iter().map(|t| quantify_frees(Quant::Ex, t)).collect(),
    )
    .not();
    let phi = acc.formula.clone();
    let formula = quantify_frees(Quant::All, lhs.implies(phi));
    to_lemma(p::TraceQuantifier::AllTraces, name, formula)
}

/// HS `verifiabilityNonEmpty` (Generation.hs:193-200).
fn verifiability_nonempty(acc: &AccData, ct: &CaseTestData) -> GenLemma {
    let name = format!("{}_{}_verif_nonempty", acc.name, ct.name);
    let tau = ct.formula.clone();
    let phi = acc.formula.clone();
    let formula = quantify_frees(Quant::All, tau.implies(phi.not()));
    to_lemma(p::TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `minimality` (Generation.hs:202-214).
fn minimality(acc: &AccData, ct: &CaseTestData, counter: &mut u64) -> GenLemma {
    let name = format!("{}_{}_min", acc.name, ct.name);
    let taus: Vec<Fm> = acc.case_tests.iter().map(|c| c.formula.clone()).collect();
    let t1 = rename(&ct.formula, counter);
    let tts: Vec<Fm> = taus.iter().map(|t| rename(t, counter)).collect();
    let f1 = frees(&t1);
    let rhs: Vec<Fm> = tts
        .iter()
        .map(|t| {
            let ft = frees(t);
            quantify_vars(Quant::Ex, &ft, t.clone().and(strict_subset_of(&ft, &f1))).not()
        })
        .collect();
    let formula = quantify_frees(Quant::All, t1.implies(fold_conn(Conn::And, rhs)));
    to_lemma(p::TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `uniqueness` (Generation.hs:216-222).
fn uniqueness(acc: &AccData, ct: &CaseTestData) -> GenLemma {
    let name = format!("{}_{}_uniq", acc.name, ct.name);
    let tau = ct.formula.clone();
    let ftau = frees(&tau);
    let formula = quantify_frees(Quant::All, tau.implies(frees_subset_corrupt(&ftau)));
    to_lemma(p::TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `injective` (Generation.hs:225-231):
/// `∀ frees(tau). tau ⇒ foldl (.&&.) ⊤ [ ¬(x = y) | x, y <- frees tau, x ≠ y ]`.
fn injective(acc: &AccData, ct: &CaseTestData) -> GenLemma {
    let name = format!("{}_{}_inj", acc.name, ct.name);
    let tau = ct.formula.clone();
    let ftau = frees(&tau);
    let mut acc_fm = Fm::Tf(true);
    for x in &ftau {
        for y in &ftau {
            if !lvar_eq(x, y) {
                acc_fm = acc_fm.and(vars_eq(std::slice::from_ref(x), std::slice::from_ref(y)).not());
            }
        }
    }
    let formula = quantify_frees(Quant::All, tau.implies(acc_fm));
    to_lemma(p::TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `singlematched` (Generation.hs:233-243).
fn singlematched(acc: &AccData, ct: &CaseTestData, counter: &mut u64) -> GenLemma {
    let name = format!("{}_{}_single", acc.name, ct.name);
    let taus = case_test_formulas_except(acc, ct);
    let t1 = single_match(&ct.formula, counter);
    let inner = and_if(!taus.is_empty(), t1, || no_other(&taus));
    let formula = quantify_frees(Quant::Ex, inner);
    to_lemma(p::TraceQuantifier::ExistsTrace, name, to_intermediate(formula))
}

/// HS `casesLemmas` (Generation.hs:249-261): builds the seven families in the
/// fixed order, threading `counter` through the `rename`-using families
/// (`suff`, `min`, `single`) in visitation order.
fn cases_lemmas(acc: &AccData, counter: &mut u64) -> Vec<GenLemma> {
    let mut out = Vec::new();
    for ct in &acc.case_tests {
        out.push(sufficiency(acc, ct, counter));
    }
    out.push(verifiability_empty(acc));
    for ct in &acc.case_tests {
        out.push(verifiability_nonempty(acc, ct));
    }
    for ct in &acc.case_tests {
        out.push(minimality(acc, ct, counter));
    }
    for ct in &acc.case_tests {
        out.push(uniqueness(acc, ct));
    }
    for ct in &acc.case_tests {
        out.push(injective(acc, ct));
    }
    for ct in &acc.case_tests {
        out.push(singlematched(acc, ct, counter));
    }
    out
}

/// HS `generateAccountabilityLemmas accLemma = evalFreshT (casesLemmas accLemma) 0`
/// (Generation.hs:263-264): the fresh counter resets to 0 per accountability
/// lemma.
pub(crate) fn generate_accountability_lemmas(acc: &AccData) -> Vec<GenLemma> {
    let mut counter: u64 = 0;
    cases_lemmas(acc, &mut counter)
}
