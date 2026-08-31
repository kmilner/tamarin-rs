// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! The formula utilities `Accountability.Generation` builds its verification
//! conditions from (lib/accountability/src/Accountability/Generation.hs:22-160).
//!
//! The formula is `tamarin_theory::formula::SyntacticLNFormula`, the type HS
//! writes these generators over (Generation.hs:37-45): binders are De Bruijn
//! (`BVar::Bound`), free variables are `LVar`s, and the atoms carry the
//! internal terms.  The generators themselves and the intermediate
//! transformation are in `generation.rs`.

use tamarin_term::function_symbols::pair_sym;
use tamarin_term::lterm::{BVar, LSort, LVar};
use tamarin_term::term::f_app_no_eq;
use tamarin_term::vterm::var_term;
use tamarin_theory::atom::{ProtoAtom, SyntacticSugar};
use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
use tamarin_theory::formula::{
    apply_rename, exists_var, for_all_var, for_each_formula_atom, formula_facts, formula_frees,
    BLNTerm, ProtoFormula, SyntacticLNFormula,
};

// The connective/quantifier enums (HS Theory/Model/Formula.hs:107,111) are
// shared with the ProtoFormula data-type port in `tamarin_theory::formula`.
pub(crate) use tamarin_theory::formula::{Connective as Conn, Quantifier as Quant};

// =============================================================================
// Term / atom builders (Generation.hs:44-86)
// =============================================================================

/// HS `tempVar name = LVar name LSortNode 0` (Generation.hs:53-54).
pub(crate) fn temp_var(name: &str) -> LVar {
    LVar::new(name, LSort::Node, 0)
}

/// HS `msgVar name = LVar name LSortMsg 0` (Generation.hs:56-57).
fn msg_var(name: &str) -> LVar {
    LVar::new(name, LSort::Msg, 0)
}

/// A term that is a single free logical variable (HS `varTerm $ Free v`).
pub(crate) fn free_term(v: LVar) -> BLNTerm {
    var_term(BVar::Free(v))
}

/// HS `tempTerm name = varTerm $ Free $ LVar name LSortNode 0`
/// (Generation.hs:47-48).
fn temp_term(name: &str) -> BLNTerm {
    free_term(temp_var(name))
}

/// HS `msgTerm name = varTerm $ Free $ LVar name LSortMsg 0`
/// (Generation.hs:50-51).
fn msg_term(name: &str) -> BLNTerm {
    free_term(msg_var(name))
}

/// HS `protoFactFormula name terms at = Ato $ Action at $ protoFact Linear
/// name terms` (Generation.hs:44-45), where `protoFact` tags the fact with
/// its name and argument count (Theory/Model/Fact.hs:311-312).
pub(crate) fn proto_fact_formula(
    name: &str,
    terms: Vec<BLNTerm>,
    at: BLNTerm,
) -> SyntacticLNFormula {
    let tag = FactTag::Proto(
        Multiplicity::Linear,
        tamarin_term::intern::intern_str(name),
        terms.len(),
    );
    ProtoFormula::Atom(ProtoAtom::Action(at, Fact::new(tag, terms)))
}

/// HS `eq x y = Ato $ EqE (varTerm $ Free x) (varTerm $ Free y)`
/// (Generation.hs:72-73).
fn eq_vars(x: &LVar, y: &LVar) -> SyntacticLNFormula {
    ProtoFormula::Atom(ProtoAtom::EqE(free_term(*x), free_term(*y)))
}

/// HS `ntuple vars = foldr1 (curry fAppPair) (map (varTerm . Free) vars)`
/// (Generation.hs:82-83): a singleton is the bare term, longer lists nest to
/// the right through `fAppPair` (Term/Term.hs:161-163).
fn ntuple(vars: &[LVar]) -> BLNTerm {
    let mut it = vars.iter().rev().copied().map(free_term);
    let mut acc = it.next().expect("ntuple: empty variable list");
    for t in it {
        acc = f_app_no_eq(pair_sym(), vec![t, acc]);
    }
    acc
}

/// HS `varsEq l r = Ato $ EqE (ntuple l) (ntuple r)` (Generation.hs:85-86).
pub(crate) fn vars_eq(l: &[LVar], r: &[LVar]) -> SyntacticLNFormula {
    ProtoFormula::Atom(ProtoAtom::EqE(ntuple(l), ntuple(r)))
}

/// HS `isElem v vars = foldr1 (.||.) (map (eq v) vars)` (Generation.hs:70-73).
fn is_elem(v: &LVar, vars: &[LVar]) -> SyntacticLNFormula {
    fold_r1(Conn::Or, vars.iter().map(|w| eq_vars(v, w)).collect())
}

/// HS `corruptSubsetFrees vars` (Generation.hs:65-68):
/// `∀ a i. Corrupted(a)@i ⇒ isElem a vars`.
pub(crate) fn corrupt_subset_frees(vars: &[LVar]) -> SyntacticLNFormula {
    let body = proto_fact_formula("Corrupted", vec![msg_term("a")], temp_term("i"))
        .implies(is_elem(&msg_var("a"), vars));
    quantify_vars(Quant::All, &[msg_var("a"), temp_var("i")], body)
}

/// HS `strictSubsetOf lhs rhs = subset lhs rhs .&&. strict lhs rhs`
/// (Generation.hs:75-80).
pub(crate) fn strict_subset_of(lhs: &[LVar], rhs: &[LVar]) -> SyntacticLNFormula {
    // subset xs ys = foldr1 (.&&.) (map (\x -> foldr1 (.||.) (map (eq x) ys)) xs)
    let subset = fold_r1(
        Conn::And,
        lhs.iter()
            .map(|x| fold_r1(Conn::Or, rhs.iter().map(|y| eq_vars(x, y)).collect()))
            .collect(),
    );
    // strict xs ys = foldr1 (.||.) (map (\y -> foldr1 (.&&.) (map (Not . eq y) xs)) ys)
    let strict = fold_r1(
        Conn::Or,
        rhs.iter()
            .map(|y| fold_r1(Conn::And, lhs.iter().map(|x| eq_vars(y, x).not()).collect()))
            .collect(),
    );
    subset.and(strict)
}

// =============================================================================
// Connective folds (Generation.hs:105-110)
// =============================================================================

/// HS `foldr1 op` for a non-empty list; right-associative.
pub(crate) fn fold_r1(op: Conn, mut fms: Vec<SyntacticLNFormula>) -> SyntacticLNFormula {
    let last = fms.pop().expect("fold_r1: empty list");
    fms.into_iter().rev().fold(last, |acc, f| {
        ProtoFormula::Conn(op, Box::new(f), Box::new(acc))
    })
}

/// HS `foldl1 op` for a non-empty list; left-associative.
pub(crate) fn fold_l1(op: Conn, fms: Vec<SyntacticLNFormula>) -> SyntacticLNFormula {
    let mut it = fms.into_iter();
    let first = it.next().expect("fold_l1: empty list");
    it.fold(first, |acc, f| {
        ProtoFormula::Conn(op, Box::new(acc), Box::new(f))
    })
}

/// HS `foldConn` (Generation.hs:105-110): a singleton is itself, otherwise
/// `foldl1 op`.
pub(crate) fn fold_conn(op: Conn, fms: Vec<SyntacticLNFormula>) -> SyntacticLNFormula {
    if fms.len() == 1 {
        fms.into_iter().next().unwrap()
    } else {
        fold_l1(op, fms)
    }
}

// =============================================================================
// Quantifier introduction (Generation.hs:37-42)
// =============================================================================

/// HS `hinted quan v = quan (hint v) v` (Theory/Model/Formula.hs:364-365):
/// the hint is the variable's name and sort (Theory/Model/Formula.hs:227-228).
fn qua_var(quant: Quant, x: &LVar, fm: SyntacticLNFormula) -> SyntacticLNFormula {
    let hint = (x.name.to_string(), x.sort);
    match quant {
        Quant::All => for_all_var(hint, x, fm),
        Quant::Ex => exists_var(hint, x, fm),
    }
}

/// HS `quantifyVars quan vars fm = foldr (hinted quan) fm vars`
/// (Generation.hs:37-38): `vars[0]` is the OUTERMOST binder, `vars[last]` the
/// innermost.
pub(crate) fn quantify_vars(
    quant: Quant,
    vars: &[LVar],
    fm: SyntacticLNFormula,
) -> SyntacticLNFormula {
    vars.iter().rev().fold(fm, |acc, v| qua_var(quant, v, acc))
}

/// HS `quantifyFrees quan fm = quantifyVars quan (frees fm) fm`
/// (Generation.hs:41-42).
pub(crate) fn quantify_frees(quant: Quant, fm: SyntacticLNFormula) -> SyntacticLNFormula {
    let vs = formula_frees(&fm);
    quantify_vars(quant, &vs, fm)
}

// =============================================================================
// rename (Term/LTerm.hs:634-645)
// =============================================================================

/// HS `rename` (Term/LTerm.hs:638-645): shift every free variable's index by
/// `freshStart - minVarIdx`, drawing `maxVarIdx - minVarIdx + 1` fresh
/// identifiers from `counter`.  `formula_frees` is sorted by `Ord LVar`,
/// which compares the index first (LTerm.hs:546-548), so its ends are the
/// bounds HS `boundsVarIdx` folds (LTerm.hs:673-675).
pub(crate) fn rename(fm: &SyntacticLNFormula, counter: &mut u64) -> SyntacticLNFormula {
    let vars = formula_frees(fm);
    let (Some(first), Some(last)) = (vars.first(), vars.last()) else {
        return fm.clone();
    };
    let (min, max) = (first.idx, last.idx);
    let fresh_start = *counter;
    *counter += max - min + 1;
    let shift = fresh_start as i64 - min as i64;
    apply_rename(fm.clone(), &mut |v| {
        LVar::new(v.name, v.sort, (v.idx as i64 + shift) as u64)
    })
}

// =============================================================================
// Atom queries (Generation.hs:112-118)
// =============================================================================

/// HS `formulaActionFacts` (Generation.hs:112-118): the `Fact`s appearing in
/// `Action` atoms of a formula.
pub(crate) fn formula_action_facts(fm: &SyntacticLNFormula) -> Vec<Fact<BLNTerm>> {
    formula_facts(fm).into_iter().cloned().collect()
}

/// The `Fact`s appearing in the predicate-sugar atoms of a formula — the
/// atoms HS `expandFormula` resolves against the theory's predicates
/// (Theory/Syntactic/Predicate.hs:82-92).
pub(crate) fn formula_pred_facts(fm: &SyntacticLNFormula) -> Vec<Fact<BLNTerm>> {
    let mut out = Vec::new();
    for_each_formula_atom(fm, &mut |a| {
        if let ProtoAtom::Syntactic(SyntacticSugar::Pred(f)) = a {
            out.push(f.clone());
        }
    });
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn msg_var_idx(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }

    /// A( x ) @ Bound(0) with x free — the public-names case test body,
    /// under its temporal binder.
    fn action_a_x_at_i(x_idx: u64) -> SyntacticLNFormula {
        proto_fact_formula(
            "A",
            vec![free_term(msg_var_idx("x", x_idx))],
            var_term(BVar::Bound(0)),
        )
    }

    /// `rename` shifts free-var indices and advances the counter by the
    /// (max-min+1) span (HS Term/LTerm.hs:638-645).
    #[test]
    fn rename_shifts_and_advances_counter() {
        let fm = ProtoFormula::exists(("i".to_string(), LSort::Node), action_a_x_at_i(0));
        let mut counter = 0u64;
        let t1 = rename(&fm, &mut counter);
        assert_eq!(counter, 1); // one free var, span 1
        assert_eq!(formula_frees(&t1)[0].idx, 0); // shift 0
        let t2 = rename(&fm, &mut counter);
        assert_eq!(counter, 2);
        assert_eq!(formula_frees(&t2)[0].idx, 1); // shift 1 → x.1
    }
}
