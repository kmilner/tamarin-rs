// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Accountability.Generation` (lib/accountability/src/Accountability/Generation.hs):
//! the seven verification-condition generators, their fresh-counter threading
//! and the intermediate transformation they end in (Generation.hs:264-300).
//!
//! Each accountability lemma expands to one lemma per condition family, in the
//! order `casesLemmas` fixes (Generation.hs:243-255): all `suff`, then
//! `verif_empty`, then all `verif_nonempty`, `min`, `uniq`, `inj`, `single`.
//! A single fresh counter starting at 0 (HS `evalFreshT (casesLemmas ..) 0`,
//! Generation.hs:257-258) is threaded through the families that call `rename`
//! (`suff`, `min`, `single`), in exactly that visitation order.

use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::atom::ProtoAtom;
use tamarin_theory::formula::{
    formula_frees, shift_free_indices, ProtoFormula, SyntacticLNFormula,
};
use tamarin_theory::theory::TraceQuantifier;

use crate::formula::{
    corrupt_subset_frees, fold_conn, fold_l1, fold_r1, free_term, proto_fact_formula,
    quantify_frees, quantify_vars, rename, strict_subset_of, temp_var, vars_eq, Conn, Quant,
};

/// A resolved case test (HS `CaseTest`, Items/CaseTestItem.hs:25-29).
pub(crate) struct CaseTestData {
    pub(crate) name: String,
    pub(crate) formula: SyntacticLNFormula,
}

/// A resolved accountability lemma (HS `AccLemma`, Items/AccLemmaItem.hs).  The
/// lemma's `_aAttributes` are held separately by the caller and copied onto each
/// generated lemma at injection time.
pub(crate) struct AccData {
    pub(crate) name: String,
    pub(crate) formula: SyntacticLNFormula,
    pub(crate) case_tests: Vec<CaseTestData>,
}

/// One generated lemma (HS `ProtoLemma SyntacticLNFormula ProofSkeleton`),
/// as `generate_accountability_lemmas` builds it: the injection step in
/// `lib.rs` predicate-expands the formula and applies the theory's macros.
pub(crate) struct GenLemma {
    pub(crate) name: String,
    pub(crate) quantifier: TraceQuantifier,
    pub(crate) formula: SyntacticLNFormula,
}

/// HS `toLemma accLemma quantifier suffix formula` (Generation.hs:25-32): wraps
/// the generated formula with its name and trace quantifier.  The accountability
/// lemma's attributes (HS `_aAttributes`) are copied onto each generated lemma
/// by the injection step in `lib.rs`.
fn to_lemma(quantifier: TraceQuantifier, name: String, formula: SyntacticLNFormula) -> GenLemma {
    GenLemma {
        name,
        quantifier,
        formula,
    }
}

/// HS `caseTestFormulasExcept` (Generation.hs:101-103): the formulas of all
/// case tests except `ct`, in order.
fn case_test_formulas_except(acc: &AccData, ct: &CaseTestData) -> Vec<SyntacticLNFormula> {
    acc.case_tests
        .iter()
        .filter(|c| c.name != ct.name)
        .map(|c| c.formula.clone())
        .collect()
}

/// HS `andIf p a b = if p then a .&&. b else a` (Generation.hs:91-92).  `b` is
/// evaluated lazily (HS is non-strict): the `noOther` conjunct is a `foldr1`
/// that is undefined on the empty case-test-formula list, so it must not be
/// forced when `p_` is false.
fn and_if(
    p_: bool,
    a: SyntacticLNFormula,
    b: impl FnOnce() -> SyntacticLNFormula,
) -> SyntacticLNFormula {
    if p_ {
        a.and(b())
    } else {
        a
    }
}

/// HS `singleMatch t` (Generation.hs:95-99):
/// `rename t; rename t; t1 .&&. ∀ frees(t2). (t2 ⇒ varsEq (frees t2) (frees t1))`.
fn single_match(t: &SyntacticLNFormula, counter: &mut u64) -> SyntacticLNFormula {
    let t1 = rename(t, counter);
    let t2 = rename(t, counter);
    let f2 = formula_frees(&t2);
    let f1 = formula_frees(&t1);
    let body = t2.implies(vars_eq(&f2, &f1));
    t1.and(quantify_vars(Quant::All, &f2, body))
}

/// HS `noOther fms = foldr1 (.&&.) (map (Not . quantifyFrees exists) fms)`
/// (Generation.hs:88-89).
fn no_other(taus: &[SyntacticLNFormula]) -> SyntacticLNFormula {
    fold_r1(
        Conn::And,
        taus.iter()
            .map(|t| quantify_frees(Quant::Ex, t.clone()).not())
            .collect(),
    )
}

/// HS `freesSubsetCorrupt vars` (Generation.hs:59-63):
/// `foldl1 (.&&.) [ ∃ i. Corrupted(var)@i | var <- vars ]`.
fn frees_subset_corrupt(vars: &[LVar]) -> SyntacticLNFormula {
    fold_l1(
        Conn::And,
        vars.iter()
            .map(|v| {
                quantify_vars(
                    Quant::Ex,
                    &[temp_var("i")],
                    proto_fact_formula("Corrupted", vec![free_term(*v)], free_term(temp_var("i"))),
                )
            })
            .collect(),
    )
}

/// HS `sufficiency` (Generation.hs:166-176).
fn sufficiency(acc: &AccData, ct: &CaseTestData, counter: &mut u64) -> GenLemma {
    let name = format!("{}_{}_suff", acc.name, ct.name);
    let taus = case_test_formulas_except(acc, ct);
    let t1 = single_match(&ct.formula, counter);
    let f1 = formula_frees(&t1);
    let inner = t1.and(and_if(!taus.is_empty(), corrupt_subset_frees(&f1), || {
        no_other(&taus)
    }));
    let formula = quantify_frees(Quant::Ex, inner);
    to_lemma(TraceQuantifier::ExistsTrace, name, to_intermediate(formula))
}

/// HS `verifiabilityEmpty` (Generation.hs:178-185).  NOTE: the only family
/// that does NOT apply `toIntermediate` — the formula is returned raw.
fn verifiability_empty(acc: &AccData) -> GenLemma {
    let name = format!("{}_verif_empty", acc.name);
    let taus: Vec<SyntacticLNFormula> = acc.case_tests.iter().map(|c| c.formula.clone()).collect();
    let lhs = fold_conn(
        Conn::Or,
        taus.into_iter()
            .map(|t| quantify_frees(Quant::Ex, t))
            .collect(),
    )
    .not();
    let phi = acc.formula.clone();
    let formula = quantify_frees(Quant::All, lhs.implies(phi));
    to_lemma(TraceQuantifier::AllTraces, name, formula)
}

/// HS `verifiabilityNonEmpty` (Generation.hs:187-194).
fn verifiability_nonempty(acc: &AccData, ct: &CaseTestData) -> GenLemma {
    let name = format!("{}_{}_verif_nonempty", acc.name, ct.name);
    let tau = ct.formula.clone();
    let phi = acc.formula.clone();
    let formula = quantify_frees(Quant::All, tau.implies(phi.not()));
    to_lemma(TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `minimality` (Generation.hs:196-208).
fn minimality(acc: &AccData, ct: &CaseTestData, counter: &mut u64) -> GenLemma {
    let name = format!("{}_{}_min", acc.name, ct.name);
    let taus: Vec<SyntacticLNFormula> = acc.case_tests.iter().map(|c| c.formula.clone()).collect();
    let t1 = rename(&ct.formula, counter);
    let tts: Vec<SyntacticLNFormula> = taus.iter().map(|t| rename(t, counter)).collect();
    let f1 = formula_frees(&t1);
    let rhs: Vec<SyntacticLNFormula> = tts
        .iter()
        .map(|t| {
            let ft = formula_frees(t);
            quantify_vars(Quant::Ex, &ft, t.clone().and(strict_subset_of(&ft, &f1))).not()
        })
        .collect();
    let formula = quantify_frees(Quant::All, t1.implies(fold_conn(Conn::And, rhs)));
    to_lemma(TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `uniqueness` (Generation.hs:210-216).
fn uniqueness(acc: &AccData, ct: &CaseTestData) -> GenLemma {
    let name = format!("{}_{}_uniq", acc.name, ct.name);
    let tau = ct.formula.clone();
    let ftau = formula_frees(&tau);
    let formula = quantify_frees(Quant::All, tau.implies(frees_subset_corrupt(&ftau)));
    to_lemma(TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `injective` (Generation.hs:219-225):
/// `∀ frees(tau). tau ⇒ foldl (.&&.) ⊤ [ ¬(x = y) | x, y <- frees tau, x ≠ y ]`.
fn injective(acc: &AccData, ct: &CaseTestData) -> GenLemma {
    let name = format!("{}_{}_inj", acc.name, ct.name);
    let tau = ct.formula.clone();
    let ftau = formula_frees(&tau);
    let mut acc_fm = ProtoFormula::ltrue();
    for x in &ftau {
        for y in &ftau {
            if x != y {
                acc_fm =
                    acc_fm.and(vars_eq(std::slice::from_ref(x), std::slice::from_ref(y)).not());
            }
        }
    }
    let formula = quantify_frees(Quant::All, tau.implies(acc_fm));
    to_lemma(TraceQuantifier::AllTraces, name, to_intermediate(formula))
}

/// HS `singlematched` (Generation.hs:227-237).
fn singlematched(acc: &AccData, ct: &CaseTestData, counter: &mut u64) -> GenLemma {
    let name = format!("{}_{}_single", acc.name, ct.name);
    let taus = case_test_formulas_except(acc, ct);
    let t1 = single_match(&ct.formula, counter);
    let inner = and_if(!taus.is_empty(), t1, || no_other(&taus));
    let formula = quantify_frees(Quant::Ex, inner);
    to_lemma(TraceQuantifier::ExistsTrace, name, to_intermediate(formula))
}

/// HS `casesLemmas` (Generation.hs:243-255): builds the seven families in the
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
/// (Generation.hs:257-258): the fresh counter resets to 0 per accountability
/// lemma.
pub(crate) fn generate_accountability_lemmas(acc: &AccData) -> Vec<GenLemma> {
    let mut counter: u64 = 0;
    cases_lemmas(acc, &mut counter)
}

// =============================================================================
// Intermediate transformation (Generation.hs:264-300) and the first-order
// simplification it ends in (Theory/Model/Formula.hs:379-412)
// =============================================================================

/// HS `pull_l`/`pull_r`/`pull_2` (Generation.hs:285-287): bind `x` over
/// `p op q` and keep pulling inside.  The three HS variants differ only in
/// which operand's free indices shift under the new binder, which the callers
/// below do.
fn pull(
    quans: &[Quant],
    qua: Quant,
    op: Conn,
    x: (String, LSort),
    p_: SyntacticLNFormula,
    q: SyntacticLNFormula,
) -> SyntacticLNFormula {
    let combined = ProtoFormula::Conn(op, Box::new(p_), Box::new(q));
    ProtoFormula::Qua(qua, x, Box::new(pull_quantifiers(quans, combined)))
}

/// HS `pullQuantifiers` (Generation.hs:267-287).
fn pull_quantifiers(quans: &[Quant], fm: SyntacticLNFormula) -> SyntacticLNFormula {
    let ProtoFormula::Conn(c, a, b) = fm else {
        return fm;
    };
    match (c, *a, *b) {
        (Conn::And, ProtoFormula::Qua(Quant::All, x, p_), ProtoFormula::Qua(Quant::All, x2, q))
            if x == x2 =>
        {
            pull(quans, Quant::All, Conn::And, x, *p_, *q)
        }
        (Conn::Or, ProtoFormula::Qua(Quant::Ex, x, p_), ProtoFormula::Qua(Quant::Ex, x2, q))
            if x == x2 =>
        {
            pull(quans, Quant::Ex, Conn::Or, x, *p_, *q)
        }
        (Conn::And, ProtoFormula::Qua(qua, x, p_), q) if quans.contains(&qua) => {
            pull(quans, qua, Conn::And, x, *p_, shift_free_indices(1, q))
        }
        (Conn::And, p_, ProtoFormula::Qua(qua, x, q)) if quans.contains(&qua) => {
            pull(quans, qua, Conn::And, x, shift_free_indices(1, p_), *q)
        }
        (Conn::Or, ProtoFormula::Qua(qua, x, p_), q) if quans.contains(&qua) => {
            pull(quans, qua, Conn::Or, x, *p_, shift_free_indices(1, q))
        }
        (Conn::Or, p_, ProtoFormula::Qua(qua, x, q)) if quans.contains(&qua) => {
            pull(quans, qua, Conn::Or, x, shift_free_indices(1, p_), *q)
        }
        (Conn::Imp, ProtoFormula::Qua(Quant::Ex, x, p_), q) if quans.contains(&Quant::All) => pull(
            quans,
            Quant::All,
            Conn::Imp,
            x,
            *p_,
            shift_free_indices(1, q),
        ),
        (c, a, b) => ProtoFormula::Conn(c, Box::new(a), Box::new(b)),
    }
}

/// HS `mergeQuantifiers = mergeQuantifiers1 [All, Ex]` (Generation.hs:289-300).
fn merge_quantifiers(fm: SyntacticLNFormula) -> SyntacticLNFormula {
    merge_quantifiers1(&[Quant::All, Quant::Ex], fm)
}

fn merge_quantifiers1(quans: &[Quant], fm: SyntacticLNFormula) -> SyntacticLNFormula {
    match fm {
        ProtoFormula::Not(p_) => ProtoFormula::Not(Box::new(merge_quantifiers1(quans, *p_))),
        ProtoFormula::Qua(qua, x, p_) => {
            ProtoFormula::Qua(qua, x, Box::new(merge_quantifiers1(&[qua], *p_)))
        }
        ProtoFormula::Conn(c @ (Conn::And | Conn::Or | Conn::Imp), p_, q) => pull_quantifiers(
            quans,
            ProtoFormula::Conn(
                c,
                Box::new(merge_quantifiers1(quans, *p_)),
                Box::new(merge_quantifiers1(quans, *q)),
            ),
        ),
        // HS `Conn Iff p q -> pullQuantifiers quans $ (mq p .==>. mq q) .&&.
        // (mq q .==>. mq p)` (Generation.hs:298-299): the biconditional
        // expands to the conjunction of both implications.
        ProtoFormula::Conn(Conn::Iff, p_, q) => {
            let mp = merge_quantifiers1(quans, *p_);
            let mq = merge_quantifiers1(quans, *q);
            let inner = mp.clone().implies(mq.clone()).and(mq.implies(mp));
            pull_quantifiers(quans, inner)
        }
        other => other,
    }
}

/// HS `simplifyFormula` (Theory/Model/Formula.hs:379-412).
fn simplify_formula(fm: SyntacticLNFormula) -> SyntacticLNFormula {
    match fm {
        ProtoFormula::Atom(a) => simplify_formula1(ProtoFormula::Atom(a)),
        ProtoFormula::Not(p_) => {
            simplify_formula1(ProtoFormula::Not(Box::new(simplify_formula(*p_))))
        }
        ProtoFormula::Conn(c, p_, q) => simplify_formula1(ProtoFormula::Conn(
            c,
            Box::new(simplify_formula(*p_)),
            Box::new(simplify_formula(*q)),
        )),
        ProtoFormula::Qua(qua, x, p_) => {
            simplify_formula1(ProtoFormula::Qua(qua, x, Box::new(simplify_formula(*p_))))
        }
        other => other,
    }
}

/// HS `simplifyFormula1` (Theory/Model/Formula.hs:391-412).
fn simplify_formula1(fm: SyntacticLNFormula) -> SyntacticLNFormula {
    use Conn::*;
    match fm {
        ProtoFormula::Atom(ProtoAtom::EqE(l, r)) => {
            if l == r {
                ProtoFormula::Tf(true)
            } else {
                ProtoFormula::Atom(ProtoAtom::EqE(l, r))
            }
        }
        ProtoFormula::Not(p_) => match *p_ {
            ProtoFormula::Tf(b) => ProtoFormula::Tf(!b),
            other => ProtoFormula::Not(Box::new(other)),
        },
        ProtoFormula::Conn(And, p_, q) => match (*p_, *q) {
            (ProtoFormula::Tf(false), _) => ProtoFormula::Tf(false),
            (_, ProtoFormula::Tf(false)) => ProtoFormula::Tf(false),
            (ProtoFormula::Tf(true), q) => q,
            (p_, ProtoFormula::Tf(true)) => p_,
            (p_, q) => ProtoFormula::Conn(And, Box::new(p_), Box::new(q)),
        },
        ProtoFormula::Conn(Or, p_, q) => match (*p_, *q) {
            (ProtoFormula::Tf(false), q) => q,
            (p_, ProtoFormula::Tf(false)) => p_,
            (ProtoFormula::Tf(true), _) => ProtoFormula::Tf(true),
            (_, ProtoFormula::Tf(true)) => ProtoFormula::Tf(true),
            (p_, q) => ProtoFormula::Conn(Or, Box::new(p_), Box::new(q)),
        },
        ProtoFormula::Conn(Imp, p_, q) => match (*p_, *q) {
            (ProtoFormula::Tf(false), _) => ProtoFormula::Tf(true),
            (ProtoFormula::Tf(true), q) => q,
            (_, ProtoFormula::Tf(true)) => ProtoFormula::Tf(true),
            (p_, ProtoFormula::Tf(false)) => ProtoFormula::Not(Box::new(p_)),
            (p_, q) => ProtoFormula::Conn(Imp, Box::new(p_), Box::new(q)),
        },
        ProtoFormula::Conn(Iff, p_, q) => match (*p_, *q) {
            (ProtoFormula::Tf(true), q) => q,
            (p_, ProtoFormula::Tf(true)) => p_,
            (ProtoFormula::Tf(false), ProtoFormula::Tf(false)) => ProtoFormula::Tf(true),
            (ProtoFormula::Tf(false), q) => ProtoFormula::Not(Box::new(q)),
            (p_, ProtoFormula::Tf(false)) => ProtoFormula::Not(Box::new(p_)),
            (p_, q) => ProtoFormula::Conn(Iff, Box::new(p_), Box::new(q)),
        },
        ProtoFormula::Qua(qua, x, p_) => match *p_ {
            ProtoFormula::Tf(b) => ProtoFormula::Tf(b),
            body => ProtoFormula::Qua(qua, x, Box::new(body)),
        },
        other => other,
    }
}

/// HS `toIntermediate = simplifyFormula . mergeQuantifiers` (Generation.hs:264-265).
fn to_intermediate(fm: SyntacticLNFormula) -> SyntacticLNFormula {
    simplify_formula(merge_quantifiers(fm))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{BVar, LSort};
    use tamarin_term::vterm::var_term;

    fn msg_var_idx(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }

    fn at_bound(name: &str, i: u64) -> SyntacticLNFormula {
        proto_fact_formula(name, Vec::new(), var_term(BVar::Bound(i)))
    }

    /// `simplifyFormula` collapses `⇒ ⊤` to `⊤` and quantifiers over `⊤` to
    /// `⊤` — the acc_*_inj single-var case
    /// (Theory/Model/Formula.hs:391-412, see line 404,411).
    #[test]
    fn simplify_true_implication_and_quantifier() {
        // ∀ x. (P => ⊤)  ->  ⊤
        let inner = at_bound("P", 0).implies(ProtoFormula::Tf(true));
        let f = ProtoFormula::for_all(("x".to_string(), LSort::Msg), inner);
        assert_eq!(simplify_formula(f), ProtoFormula::Tf(true));
    }

    /// `simplifyFormula1` rewrites a reflexive equality `t = t` to `⊤`
    /// (Theory/Model/Formula.hs:379-412, see line 392) and leaves a
    /// non-reflexive one alone.
    #[test]
    fn simplify_reflexive_equality() {
        let x = msg_var_idx("x", 0);
        let y = msg_var_idx("y", 0);
        let eq = |a: LVar, b: LVar| -> SyntacticLNFormula {
            ProtoFormula::Atom(ProtoAtom::EqE(free_term(a), free_term(b)))
        };
        assert_eq!(simplify_formula(eq(x, x)), ProtoFormula::Tf(true));
        // x = y is preserved.
        assert_eq!(simplify_formula(eq(x, y)), eq(x, y));
    }

    /// `pullQuantifiers` pulls a universal out of a conjunction and shifts the
    /// OTHER conjunct's dangling bound indices up by one (Generation.hs:267-287, see line 274,285):
    /// `(∀ j. A@j) ∧ B@Bound(0)` becomes `∀ j. (A@Bound(0) ∧ B@Bound(1))`.
    #[test]
    fn pull_quantifiers_shifts_dangling_bound() {
        let all_j = ProtoFormula::for_all(("j".to_string(), LSort::Node), at_bound("A", 0));
        // B@Bound(0): a reference dangling past this formula.
        let pulled = pull_quantifiers(&[Quant::All], all_j.and(at_bound("B", 0)));
        // Expect: ∀ j. (A@Bound(0) ∧ B@Bound(1)).
        let ProtoFormula::Qua(Quant::All, _, body) = pulled else {
            panic!("expected a universal at the top");
        };
        let ProtoFormula::Conn(Conn::And, l, r) = *body else {
            panic!("expected a conjunction under the binder");
        };
        assert_eq!(*l, at_bound("A", 0));
        assert_eq!(*r, at_bound("B", 1));
    }

    /// `mergeQuantifiers` pulls an existential out of an implication's guard,
    /// turning it universal: `(∃ i. P@i) ⇒ Q` becomes `∀ i. (P@i ⇒ Q)`.
    #[test]
    fn merge_pulls_exists_through_implication() {
        // (Ex #i. P@i) => (Q)  with Q closed (a nullary fact @ a fresh bound)
        let guard = ProtoFormula::exists(("i".to_string(), LSort::Node), at_bound("P", 0));
        let f = guard.implies(ProtoFormula::Tf(false));
        let merged = merge_quantifiers(f);
        // The merge leaves a universal binder over #i at the top.  That
        // binder carries the original binder name and sort.  The body of the
        // guard becomes the antecedent of the implication, and it still
        // refers to `Bound(0)`.
        let ProtoFormula::Qua(Quant::All, b, body) = merged else {
            panic!("expected a universal at the top");
        };
        assert_eq!(b, ("i".to_string(), LSort::Node));
        assert_eq!(*body, at_bound("P", 0).implies(ProtoFormula::Tf(false)));
    }
}
