//! Locally-nameless `SyntacticLNFormula` and the pure transforms the
//! accountability lemma generation runs on it.
//!
//! Mirrors HS `Theory.Model.Formula`'s `ProtoFormula syn s c v` specialised to
//! `SyntacticLNFormula = ProtoFormula SyntacticSugar (String, LSort) Name (BVar LVar)`
//! (Formula.hs:114-127, 261).  Bound variables are De-Bruijn (`BVar::Bound`),
//! free variables carry a full `LVar` (`BVar::Free`); the atom/term leaves reuse
//! `tamarin_theory::guarded_types` (`GAtom`/`GFact`/`GTerm`), whose Free↔Bound
//! substitution helpers implement HS's `quantify`/open/close discipline.
//!
//! The transforms are `frees`, `quantify`/`forAll`/`exists`, `rename`
//! (Term/LTerm.hs:614-621), `shiftFreeIndices` (Formula.hs:457-462),
//! `pullQuantifiers`/`mergeQuantifiers` (Generation.hs:273-306) and
//! `simplifyFormula` (Formula.hs:377-409), plus the `p::Formula` ↔
//! locally-nameless converters that let the generated lemmas reuse the parser-AST
//! rendering and guarded-proving paths.

use tamarin_parser::ast as p;
use tamarin_theory::guarded_types::{
    self as gt, atom_to_gatom_free, close_subst, collect_free_atom, gatom_to_atom,
    lvar_to_binding, map_free_atom, normalise_msg_sort, open_subst,
    subst_bound_atom_at_depth, subst_free_atom_at_depth, BVar, GAtom, GBinding,
    GFact, GTerm,
};

// The connective/quantifier enums (HS Formula.hs:104,108) are shared with the
// ProtoFormula data-type port in `tamarin_theory::formula`.
pub(crate) use tamarin_theory::formula::{Connective as Conn, Quantifier as Quant};

/// A `SyntacticLNFormula` in locally-nameless form.
///
/// `Qua` carries a `GBinding` (name + sort hint, HS `(String, LSort)`); the
/// binder's identity is positional (De-Bruijn), so the body refers to it via
/// `BVar::Bound(depth)` in its `GAtom` leaves.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Fm {
    Ato(GAtom),
    Tf(bool),
    Not(Box<Fm>),
    Conn(Conn, Box<Fm>, Box<Fm>),
    Qua(Quant, GBinding, Box<Fm>),
}

impl Fm {
    pub(crate) fn not(self) -> Fm {
        Fm::Not(Box::new(self))
    }
    pub(crate) fn and(self, other: Fm) -> Fm {
        Fm::Conn(Conn::And, Box::new(self), Box::new(other))
    }
    pub(crate) fn implies(self, other: Fm) -> Fm {
        Fm::Conn(Conn::Imp, Box::new(self), Box::new(other))
    }
}

// =============================================================================
// LVar Ord + sort ranking (HS LVar Ord: compare idx <> sort <> name,
// LTerm.hs:522-524; LSort order Pub<Fresh<Msg<Node<Nat, LTerm.hs:161-166).
// =============================================================================

/// Rank a `SortHint` to mirror HS `LSort` Ord.  A bare (`Untagged`) message
/// variable is `LSortMsg`.
///
/// NOT interchangeable with `guarded::sort_hint_tag`/`cmp_varspec`: those
/// rank `Untagged` LAST (99) so unresolved hints stay distinct, whereas here
/// `Untagged` ranks AS `Msg` — `frees` must dedup a bare `x` against `x:msg`
/// (HS compares real `LSort`s, where both are already `LSortMsg`).
pub(crate) fn sort_rank(s: p::SortHint) -> u8 {
    use p::{SortHint::*, SuffixSort};
    match s {
        Pub | Suffix(SuffixSort::Pub) => 0,
        Fresh | Suffix(SuffixSort::Fresh) => 1,
        Msg | Suffix(SuffixSort::Msg) | Untagged => 2,
        Node | Suffix(SuffixSort::Node) => 3,
        Nat | Suffix(SuffixSort::Nat) => 4,
    }
}

/// HS `LVar` Ord: `compare idx <> compare sort <> compare name`.
/// Compares via [`sort_rank`], so `Untagged` == `Msg` (see its doc for why
/// this deliberately differs from `guarded::cmp_varspec`).
fn cmp_lvar(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx
        .cmp(&b.idx)
        .then(sort_rank(a.sort).cmp(&sort_rank(b.sort)))
        .then(a.name.cmp(&b.name))
}

// =============================================================================
// Term / atom builders (HS Generation.hs helpers)
// =============================================================================

/// HS `tempVar name = LVar name LSortNode 0`.
pub(crate) fn temp_var(name: &str) -> p::VarSpec {
    p::VarSpec { name: name.to_string(), idx: 0, sort: p::SortHint::Node, typ: None }
}

/// HS `msgVar name = LVar name LSortMsg 0`.
pub(crate) fn msg_var(name: &str) -> p::VarSpec {
    p::VarSpec { name: name.to_string(), idx: 0, sort: p::SortHint::Msg, typ: None }
}

fn free_term(v: p::VarSpec) -> GTerm {
    GTerm::Var(BVar::Free(v))
}

/// A term that is a single free logical variable (HS `varTerm $ Free v`).
pub(crate) fn free_var_term(v: p::VarSpec) -> GTerm {
    free_term(v)
}

/// HS `LVar` `==`: equal name, sort AND index (LTerm.hs:517-518).  Sorts are
/// compared after normalising to their concrete base (a bare `Untagged`
/// message variable is `LSortMsg`).
pub(crate) fn lvar_eq(a: &p::VarSpec, b: &p::VarSpec) -> bool {
    a.idx == b.idx
        && a.name == b.name
        && normalise_msg_sort(a.sort) == normalise_msg_sort(b.sort)
}

/// HS `tempTerm name = varTerm $ Free $ LVar name LSortNode 0`.
fn temp_term(name: &str) -> GTerm {
    free_term(temp_var(name))
}

/// HS `msgTerm name = varTerm $ Free $ LVar name LSortMsg 0`.
fn msg_term(name: &str) -> GTerm {
    free_term(msg_var(name))
}

/// HS `protoFactFormula name terms at = Ato $ Action at $ protoFact Linear name terms`.
pub(crate) fn proto_fact_formula(name: &str, terms: Vec<GTerm>, at: GTerm) -> Fm {
    Fm::Ato(GAtom::Action(
        GFact { persistent: false, name: name.to_string(), args: terms, annotations: Vec::new() },
        at,
    ))
}

/// HS `eq x y = Ato $ EqE (varTerm $ Free x) (varTerm $ Free y)`.
fn eq_vars(x: &p::VarSpec, y: &p::VarSpec) -> Fm {
    Fm::Ato(GAtom::Eq(free_term(x.clone()), free_term(y.clone())))
}

/// HS `ntuple vars = foldr1 (curry fAppPair) (map (varTerm . Free) vars)`.
/// A singleton is the bare term; longer lists fold right into pairs (RS's
/// `mk_gpair` canonicalises the right-nested form to a flat `Pair`).
fn ntuple(vars: &[p::VarSpec]) -> GTerm {
    let terms: Vec<GTerm> = vars.iter().cloned().map(free_term).collect();
    let mut it = terms.into_iter().rev();
    let mut acc = it.next().expect("ntuple: empty variable list");
    for t in it {
        acc = gt::mk_gpair(vec![t, acc]);
    }
    acc
}

/// HS `varsEq l r = Ato $ EqE (ntuple l) (ntuple r)`.
pub(crate) fn vars_eq(l: &[p::VarSpec], r: &[p::VarSpec]) -> Fm {
    Fm::Ato(GAtom::Eq(ntuple(l), ntuple(r)))
}

/// HS `isElem v vars = foldr1 (.||.) (map (eq v) vars)`.
pub(crate) fn is_elem(v: &p::VarSpec, vars: &[p::VarSpec]) -> Fm {
    fold_r1(Conn::Or, vars.iter().map(|w| eq_vars(v, w)).collect())
}

/// HS `corruptSubsetFrees vars` (Generation.hs:71-74):
/// `∀ a i. Corrupted(a)@i ⇒ isElem a vars`.
pub(crate) fn corrupt_subset_frees(vars: &[p::VarSpec]) -> Fm {
    let body = proto_fact_formula("Corrupted", vec![msg_term("a")], temp_term("i"))
        .implies(is_elem(&msg_var("a"), vars));
    quantify_vars(Quant::All, &[msg_var("a"), temp_var("i")], body)
}

/// HS `strictSubsetOf lhs rhs = subset lhs rhs .&&. strict lhs rhs`
/// (Generation.hs:81-86).
pub(crate) fn strict_subset_of(lhs: &[p::VarSpec], rhs: &[p::VarSpec]) -> Fm {
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
// Connective folds
// =============================================================================

/// HS `foldr1 op` for a non-empty list; right-associative.
pub(crate) fn fold_r1(op: Conn, mut fms: Vec<Fm>) -> Fm {
    let last = fms.pop().expect("fold_r1: empty list");
    fms.into_iter().rev().fold(last, |acc, f| Fm::Conn(op, Box::new(f), Box::new(acc)))
}

/// HS `foldl1 op` for a non-empty list; left-associative.
pub(crate) fn fold_l1(op: Conn, mut fms: Vec<Fm>) -> Fm {
    let mut it = fms.drain(..);
    let first = it.next().expect("fold_l1: empty list");
    it.fold(first, |acc, f| Fm::Conn(op, Box::new(acc), Box::new(f)))
}

/// HS `foldConn` (Generation.hs:111-116): a singleton is itself, otherwise
/// `foldl1 op`.
pub(crate) fn fold_conn(op: Conn, fms: Vec<Fm>) -> Fm {
    if fms.len() == 1 {
        fms.into_iter().next().unwrap()
    } else {
        fold_l1(op, fms)
    }
}

// =============================================================================
// frees (HS `frees = sortednub . freesList`, LTerm.hs:589-590)
// =============================================================================

pub(crate) fn frees(fm: &Fm) -> Vec<p::VarSpec> {
    let mut out = Vec::new();
    collect_frees(fm, &mut out);
    out.sort_by(cmp_lvar);
    out.dedup_by(|a, b| cmp_lvar(a, b) == std::cmp::Ordering::Equal);
    out
}

fn collect_frees(fm: &Fm, out: &mut Vec<p::VarSpec>) {
    match fm {
        Fm::Ato(a) => collect_free_atom(a, out),
        Fm::Tf(_) => {}
        Fm::Not(p_) => collect_frees(p_, out),
        Fm::Conn(_, a, b) => {
            collect_frees(a, out);
            collect_frees(b, out);
        }
        Fm::Qua(_, _, body) => collect_frees(body, out),
    }
}

/// Minimum and maximum free-var index (HS `boundsVarIdx`, LTerm.hs:650-651).
fn free_bounds(fm: &Fm) -> Option<(u64, u64)> {
    let mut vs = Vec::new();
    collect_frees(fm, &mut vs);
    let mut it = vs.iter();
    let first = it.next()?;
    let (mut lo, mut hi) = (first.idx, first.idx);
    for v in it {
        lo = lo.min(v.idx);
        hi = hi.max(v.idx);
    }
    Some((lo, hi))
}

// =============================================================================
// quantify / forAll / exists (Formula.hs:344-357)
// =============================================================================

/// HS `quantify x = mapAtoms (\i a -> ... subst i ...)`: replace free
/// occurrences of `x` with `Bound(depth)` (Formula.hs:344-349).
fn quantify(x: &p::VarSpec, fm: Fm) -> Fm {
    quantify_at(x, fm, 0)
}

fn quantify_at(x: &p::VarSpec, fm: Fm, depth: u32) -> Fm {
    match fm {
        Fm::Ato(a) => Fm::Ato(subst_free_atom_at_depth(&a, &[(x.clone(), 0)], depth)),
        Fm::Tf(b) => Fm::Tf(b),
        Fm::Not(p_) => quantify_at(x, *p_, depth).not(),
        Fm::Conn(c, a, b) => Fm::Conn(
            c,
            Box::new(quantify_at(x, *a, depth)),
            Box::new(quantify_at(x, *b, depth)),
        ),
        Fm::Qua(q, h, body) => Fm::Qua(q, h, Box::new(quantify_at(x, *body, depth + 1))),
    }
}

fn qua_var(quant: Quant, x: &p::VarSpec, fm: Fm) -> Fm {
    Fm::Qua(quant, lvar_to_binding(x), Box::new(quantify(x, fm)))
}

/// HS `quantifyVars quan vars fm = foldr (hinted quan) fm vars` (Generation.hs:43-44):
/// `vars[0]` is the OUTERMOST binder, `vars[last]` the innermost.
pub(crate) fn quantify_vars(quant: Quant, vars: &[p::VarSpec], fm: Fm) -> Fm {
    vars.iter().rev().fold(fm, |acc, v| qua_var(quant, v, acc))
}

/// HS `quantifyFrees quan fm = quantifyVars quan (frees fm) fm` (Generation.hs:47-48).
pub(crate) fn quantify_frees(quant: Quant, fm: Fm) -> Fm {
    let vs = frees(&fm);
    quantify_vars(quant, &vs, fm)
}

// =============================================================================
// rename (Term/LTerm.hs:614-621)
// =============================================================================

/// HS `rename`: shift every free variable's index by
/// `freshStart - minVarIdx`, drawing `maxVarIdx - minVarIdx + 1` fresh
/// identifiers from `counter`.
pub(crate) fn rename(fm: &Fm, counter: &mut u64) -> Fm {
    match free_bounds(fm) {
        None => fm.clone(),
        Some((min, max)) => {
            let count = max - min + 1;
            let fresh_start = *counter;
            *counter += count;
            let shift = fresh_start as i64 - min as i64;
            map_free_fm(fm, &mut |v| {
                let mut w = v.clone();
                w.idx = (v.idx as i64 + shift) as u64;
                w
            })
        }
    }
}

fn map_free_fm<F: FnMut(&p::VarSpec) -> p::VarSpec>(fm: &Fm, f: &mut F) -> Fm {
    match fm {
        Fm::Ato(a) => Fm::Ato(map_free_atom(a, f)),
        Fm::Tf(b) => Fm::Tf(*b),
        Fm::Not(p_) => Fm::Not(Box::new(map_free_fm(p_, f))),
        Fm::Conn(c, a, b) => {
            Fm::Conn(*c, Box::new(map_free_fm(a, f)), Box::new(map_free_fm(b, f)))
        }
        Fm::Qua(q, h, body) => Fm::Qua(*q, h.clone(), Box::new(map_free_fm(body, f))),
    }
}

// =============================================================================
// shiftFreeIndices (Formula.hs:457-462)
// =============================================================================

/// HS `shiftFreeIndices n`: at binder-depth `i`, bump every `Bound(j)` with
/// `j >= i` (a reference dangling past this formula) by `n`.
fn shift_free_indices(n: u32, fm: &Fm) -> Fm {
    shift_free_at(n, fm, 0)
}

fn shift_free_at(n: u32, fm: &Fm, depth: u32) -> Fm {
    match fm {
        Fm::Ato(a) => Fm::Ato(shift_bound_atom(a, depth, n)),
        Fm::Tf(b) => Fm::Tf(*b),
        Fm::Not(p_) => Fm::Not(Box::new(shift_free_at(n, p_, depth))),
        Fm::Conn(c, a, b) => Fm::Conn(
            *c,
            Box::new(shift_free_at(n, a, depth)),
            Box::new(shift_free_at(n, b, depth)),
        ),
        Fm::Qua(q, h, body) => {
            Fm::Qua(*q, h.clone(), Box::new(shift_free_at(n, body, depth + 1)))
        }
    }
}

fn shift_bound_atom(a: &GAtom, threshold: u32, n: u32) -> GAtom {
    match a {
        GAtom::Eq(x, y) => GAtom::Eq(shift_bound_term(x, threshold, n), shift_bound_term(y, threshold, n)),
        GAtom::Less(x, y) => GAtom::Less(shift_bound_term(x, threshold, n), shift_bound_term(y, threshold, n)),
        GAtom::LessMset(x, y) => {
            GAtom::LessMset(shift_bound_term(x, threshold, n), shift_bound_term(y, threshold, n))
        }
        GAtom::Subterm(x, y) => {
            GAtom::Subterm(shift_bound_term(x, threshold, n), shift_bound_term(y, threshold, n))
        }
        GAtom::Action(f, t) => {
            GAtom::Action(shift_bound_fact(f, threshold, n), shift_bound_term(t, threshold, n))
        }
        GAtom::Last(t) => GAtom::Last(shift_bound_term(t, threshold, n)),
        GAtom::Pred(f) => GAtom::Pred(shift_bound_fact(f, threshold, n)),
    }
}

fn shift_bound_fact(f: &GFact, threshold: u32, n: u32) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|a| shift_bound_term(a, threshold, n)).collect(),
        annotations: f.annotations.clone(),
    }
}

fn shift_bound_term(t: &GTerm, threshold: u32, n: u32) -> GTerm {
    match t {
        GTerm::Var(BVar::Bound(j)) => {
            let nj = if *j < threshold { *j } else { *j + n };
            GTerm::Var(BVar::Bound(nj))
        }
        GTerm::Var(BVar::Free(_))
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => t.clone(),
        GTerm::App(name, args) => GTerm::App(
            name.clone(),
            args.iter().map(|a| shift_bound_term(a, threshold, n)).collect(),
        ),
        GTerm::AlgApp(name, a, b) => GTerm::AlgApp(
            name.clone(),
            gt::ga(shift_bound_term(a, threshold, n)),
            gt::ga(shift_bound_term(b, threshold, n)),
        ),
        GTerm::Pair(items) => {
            GTerm::Pair(items.iter().map(|a| shift_bound_term(a, threshold, n)).collect())
        }
        GTerm::Diff(a, b) => GTerm::Diff(
            gt::ga(shift_bound_term(a, threshold, n)),
            gt::ga(shift_bound_term(b, threshold, n)),
        ),
        GTerm::BinOp(op, a, b) => GTerm::BinOp(
            *op,
            gt::ga(shift_bound_term(a, threshold, n)),
            gt::ga(shift_bound_term(b, threshold, n)),
        ),
        GTerm::PatMatch(inner) => GTerm::PatMatch(gt::ga(shift_bound_term(inner, threshold, n))),
    }
}

// =============================================================================
// pullQuantifiers / mergeQuantifiers (Generation.hs:273-306)
// =============================================================================

fn pull_l(qua: Quant, op: Conn, x: GBinding, p_: Fm, q: Fm, quans: &[Quant]) -> Fm {
    let combined = Fm::Conn(op, Box::new(p_), Box::new(shift_free_indices(1, &q)));
    Fm::Qua(qua, x, Box::new(pull_quantifiers(quans, combined)))
}

fn pull_r(qua: Quant, op: Conn, x: GBinding, p_: Fm, q: Fm, quans: &[Quant]) -> Fm {
    let combined = Fm::Conn(op, Box::new(shift_free_indices(1, &p_)), Box::new(q));
    Fm::Qua(qua, x, Box::new(pull_quantifiers(quans, combined)))
}

fn pull_2(qua: Quant, op: Conn, x: GBinding, p_: Fm, q: Fm, quans: &[Quant]) -> Fm {
    let combined = Fm::Conn(op, Box::new(p_), Box::new(q));
    Fm::Qua(qua, x, Box::new(pull_quantifiers(quans, combined)))
}

pub(crate) fn pull_quantifiers(quans: &[Quant], fm: Fm) -> Fm {
    let Fm::Conn(c, a, b) = fm else { return fm };
    match (c, *a, *b) {
        (Conn::And, Fm::Qua(Quant::All, x, p_), Fm::Qua(Quant::All, x2, q)) if x == x2 => {
            pull_2(Quant::All, Conn::And, x, *p_, *q, quans)
        }
        (Conn::Or, Fm::Qua(Quant::Ex, x, p_), Fm::Qua(Quant::Ex, x2, q)) if x == x2 => {
            pull_2(Quant::Ex, Conn::Or, x, *p_, *q, quans)
        }
        (Conn::And, Fm::Qua(qua, x, p_), q) if quans.contains(&qua) => {
            pull_l(qua, Conn::And, x, *p_, q, quans)
        }
        (Conn::And, p_, Fm::Qua(qua, x, q)) if quans.contains(&qua) => {
            pull_r(qua, Conn::And, x, p_, *q, quans)
        }
        (Conn::Or, Fm::Qua(qua, x, p_), q) if quans.contains(&qua) => {
            pull_l(qua, Conn::Or, x, *p_, q, quans)
        }
        (Conn::Or, p_, Fm::Qua(qua, x, q)) if quans.contains(&qua) => {
            pull_r(qua, Conn::Or, x, p_, *q, quans)
        }
        (Conn::Imp, Fm::Qua(Quant::Ex, x, p_), q) if quans.contains(&Quant::All) => {
            pull_l(Quant::All, Conn::Imp, x, *p_, q, quans)
        }
        (c, a, b) => Fm::Conn(c, Box::new(a), Box::new(b)),
    }
}

/// HS `mergeQuantifiers = mergeQuantifiers1 [All, Ex]` (Generation.hs:295-306).
pub(crate) fn merge_quantifiers(fm: Fm) -> Fm {
    merge_quantifiers1(&[Quant::All, Quant::Ex], fm)
}

fn merge_quantifiers1(quans: &[Quant], fm: Fm) -> Fm {
    match fm {
        Fm::Not(p_) => Fm::Not(Box::new(merge_quantifiers1(quans, *p_))),
        Fm::Qua(qua, x, p_) => Fm::Qua(qua, x, Box::new(merge_quantifiers1(&[qua], *p_))),
        Fm::Conn(Conn::And, p_, q) => pull_quantifiers(
            quans,
            Fm::Conn(
                Conn::And,
                Box::new(merge_quantifiers1(quans, *p_)),
                Box::new(merge_quantifiers1(quans, *q)),
            ),
        ),
        Fm::Conn(Conn::Or, p_, q) => pull_quantifiers(
            quans,
            Fm::Conn(
                Conn::Or,
                Box::new(merge_quantifiers1(quans, *p_)),
                Box::new(merge_quantifiers1(quans, *q)),
            ),
        ),
        Fm::Conn(Conn::Imp, p_, q) => pull_quantifiers(
            quans,
            Fm::Conn(
                Conn::Imp,
                Box::new(merge_quantifiers1(quans, *p_)),
                Box::new(merge_quantifiers1(quans, *q)),
            ),
        ),
        // HS `Conn Iff p q -> pullQuantifiers quans $ (mq p .==>. mq q) .&&.
        // (mq q .==>. mq p)` (Generation.hs:304-305): the biconditional
        // expands to the conjunction of both implications.
        Fm::Conn(Conn::Iff, p_, q) => {
            let mp = merge_quantifiers1(quans, *p_);
            let mq = merge_quantifiers1(quans, *q);
            let inner = mp.clone().implies(mq.clone()).and(mq.implies(mp));
            pull_quantifiers(quans, inner)
        }
        other => other,
    }
}

// =============================================================================
// simplifyFormula (Formula.hs:377-409)
// =============================================================================

pub(crate) fn simplify_formula(fm: Fm) -> Fm {
    match fm {
        Fm::Ato(a) => simplify_formula1(Fm::Ato(a)),
        Fm::Not(p_) => simplify_formula1(Fm::Not(Box::new(simplify_formula(*p_)))),
        Fm::Conn(Conn::And, p_, q) => simplify_formula1(Fm::Conn(
            Conn::And,
            Box::new(simplify_formula(*p_)),
            Box::new(simplify_formula(*q)),
        )),
        Fm::Conn(Conn::Or, p_, q) => simplify_formula1(Fm::Conn(
            Conn::Or,
            Box::new(simplify_formula(*p_)),
            Box::new(simplify_formula(*q)),
        )),
        Fm::Conn(Conn::Imp, p_, q) => simplify_formula1(Fm::Conn(
            Conn::Imp,
            Box::new(simplify_formula(*p_)),
            Box::new(simplify_formula(*q)),
        )),
        Fm::Conn(Conn::Iff, p_, q) => simplify_formula1(Fm::Conn(
            Conn::Iff,
            Box::new(simplify_formula(*p_)),
            Box::new(simplify_formula(*q)),
        )),
        Fm::Qua(qua, x, p_) => simplify_formula1(Fm::Qua(qua, x, Box::new(simplify_formula(*p_)))),
        other => other,
    }
}

fn simplify_formula1(fm: Fm) -> Fm {
    use Conn::*;
    match fm {
        Fm::Ato(GAtom::Eq(l, r)) => {
            if l == r {
                Fm::Tf(true)
            } else {
                Fm::Ato(GAtom::Eq(l, r))
            }
        }
        Fm::Not(p_) => match *p_ {
            Fm::Tf(b) => Fm::Tf(!b),
            other => Fm::Not(Box::new(other)),
        },
        Fm::Conn(And, p_, q) => match (*p_, *q) {
            (Fm::Tf(false), _) => Fm::Tf(false),
            (_, Fm::Tf(false)) => Fm::Tf(false),
            (Fm::Tf(true), q) => q,
            (p_, Fm::Tf(true)) => p_,
            (p_, q) => Fm::Conn(And, Box::new(p_), Box::new(q)),
        },
        Fm::Conn(Or, p_, q) => match (*p_, *q) {
            (Fm::Tf(false), q) => q,
            (p_, Fm::Tf(false)) => p_,
            (Fm::Tf(true), _) => Fm::Tf(true),
            (_, Fm::Tf(true)) => Fm::Tf(true),
            (p_, q) => Fm::Conn(Or, Box::new(p_), Box::new(q)),
        },
        Fm::Conn(Imp, p_, q) => match (*p_, *q) {
            (Fm::Tf(false), _) => Fm::Tf(true),
            (Fm::Tf(true), q) => q,
            (_, Fm::Tf(true)) => Fm::Tf(true),
            (p_, Fm::Tf(false)) => Fm::Not(Box::new(p_)),
            (p_, q) => Fm::Conn(Imp, Box::new(p_), Box::new(q)),
        },
        Fm::Conn(Iff, p_, q) => match (*p_, *q) {
            (Fm::Tf(true), q) => q,
            (p_, Fm::Tf(true)) => p_,
            (Fm::Tf(false), Fm::Tf(false)) => Fm::Tf(true),
            (Fm::Tf(false), q) => Fm::Not(Box::new(q)),
            (p_, Fm::Tf(false)) => Fm::Not(Box::new(p_)),
            (p_, q) => Fm::Conn(Iff, Box::new(p_), Box::new(q)),
        },
        Fm::Qua(qua, x, p_) => match *p_ {
            Fm::Tf(b) => Fm::Tf(b),
            body => Fm::Qua(qua, x, Box::new(body)),
        },
        other => other,
    }
}

/// HS `toIntermediate = simplifyFormula . mergeQuantifiers` (Generation.hs:270-271).
pub(crate) fn to_intermediate(fm: Fm) -> Fm {
    simplify_formula(merge_quantifiers(fm))
}

// =============================================================================
// p::Formula  ->  Fm  (close: named binders → De-Bruijn)
// =============================================================================

/// Resolve a binder's sort hint to its concrete base sort (a bare binder is
/// `LSortMsg`), matching the concrete sorts HS's parser assigns.
fn resolve_binder(v: &p::VarSpec) -> p::VarSpec {
    let mut w = v.clone();
    w.sort = normalise_msg_sort(v.sort);
    w
}

/// Convert a parser-AST formula to locally-nameless form.  `scope` holds the
/// enclosing binders (outer→inner, concrete-sorted); each atom is lifted with
/// all-Free leaves, then closed against `scope`, then its remaining free
/// variables get their concrete by-position sort.
pub(crate) fn from_p_formula(f: &p::Formula) -> Fm {
    from_p(f, &[])
}

fn from_p(f: &p::Formula, scope: &[p::VarSpec]) -> Fm {
    match f {
        p::Formula::True => Fm::Tf(true),
        p::Formula::False => Fm::Tf(false),
        p::Formula::Atom(a) => {
            let ga = atom_to_gatom_free(a);
            let ga = subst_free_atom_at_depth(&ga, &close_subst(scope), 0);
            Fm::Ato(resolve_atom_sorts(&ga))
        }
        p::Formula::Not(p_) => Fm::Not(Box::new(from_p(p_, scope))),
        p::Formula::And(a, b) => {
            Fm::Conn(Conn::And, Box::new(from_p(a, scope)), Box::new(from_p(b, scope)))
        }
        p::Formula::Or(a, b) => {
            Fm::Conn(Conn::Or, Box::new(from_p(a, scope)), Box::new(from_p(b, scope)))
        }
        p::Formula::Implies(a, b) => {
            Fm::Conn(Conn::Imp, Box::new(from_p(a, scope)), Box::new(from_p(b, scope)))
        }
        p::Formula::Iff(a, b) => {
            Fm::Conn(Conn::Iff, Box::new(from_p(a, scope)), Box::new(from_p(b, scope)))
        }
        p::Formula::Forall(vs, body) => from_p_qua(Quant::All, vs, body, scope),
        p::Formula::Exists(vs, body) => from_p_qua(Quant::Ex, vs, body, scope),
    }
}

fn from_p_qua(quant: Quant, vs: &[p::VarSpec], body: &p::Formula, scope: &[p::VarSpec]) -> Fm {
    // A collapsed `∀ x y z.` block is `Qua x (Qua y (Qua z ..))` in HS's
    // locally-nameless form: explode it to nested single binders (innermost
    // last).
    let vs_resolved: Vec<p::VarSpec> = vs.iter().map(resolve_binder).collect();
    let mut new_scope = scope.to_vec();
    new_scope.extend(vs_resolved.iter().cloned());
    let mut result = from_p(body, &new_scope);
    for v in vs_resolved.iter().rev() {
        result = Fm::Qua(quant, lvar_to_binding(v), Box::new(result));
    }
    result
}

/// Give every Free leaf its concrete by-position sort (HS's parser assigns
/// `LSortNode` to temporal positions, `LSortMsg` to bare message positions).
fn resolve_atom_sorts(a: &GAtom) -> GAtom {
    match a {
        GAtom::Eq(x, y) => GAtom::Eq(resolve_term_sorts(x, false), resolve_term_sorts(y, false)),
        GAtom::Less(x, y) => GAtom::Less(resolve_term_sorts(x, true), resolve_term_sorts(y, true)),
        GAtom::LessMset(x, y) => {
            GAtom::LessMset(resolve_term_sorts(x, false), resolve_term_sorts(y, false))
        }
        GAtom::Subterm(x, y) => {
            GAtom::Subterm(resolve_term_sorts(x, false), resolve_term_sorts(y, false))
        }
        GAtom::Action(f, t) => {
            GAtom::Action(resolve_fact_sorts(f), resolve_term_sorts(t, true))
        }
        GAtom::Last(t) => GAtom::Last(resolve_term_sorts(t, true)),
        GAtom::Pred(f) => GAtom::Pred(resolve_fact_sorts(f)),
    }
}

fn resolve_fact_sorts(f: &GFact) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|t| resolve_term_sorts(t, false)).collect(),
        annotations: f.annotations.clone(),
    }
}

fn resolve_term_sorts(t: &GTerm, temporal: bool) -> GTerm {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            let mut w = v.clone();
            w.sort = if temporal { p::SortHint::Node } else { normalise_msg_sort(v.sort) };
            GTerm::Var(BVar::Free(w))
        }
        GTerm::Var(_)
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => t.clone(),
        GTerm::App(name, args) => GTerm::App(
            name.clone(),
            args.iter().map(|a| resolve_term_sorts(a, false)).collect(),
        ),
        GTerm::AlgApp(name, a, b) => GTerm::AlgApp(
            name.clone(),
            gt::ga(resolve_term_sorts(a, false)),
            gt::ga(resolve_term_sorts(b, false)),
        ),
        GTerm::Pair(items) => {
            GTerm::Pair(items.iter().map(|a| resolve_term_sorts(a, false)).collect())
        }
        GTerm::Diff(a, b) => GTerm::Diff(
            gt::ga(resolve_term_sorts(a, false)),
            gt::ga(resolve_term_sorts(b, false)),
        ),
        GTerm::BinOp(op, a, b) => GTerm::BinOp(
            *op,
            gt::ga(resolve_term_sorts(a, false)),
            gt::ga(resolve_term_sorts(b, false)),
        ),
        GTerm::PatMatch(inner) => GTerm::PatMatch(gt::ga(resolve_term_sorts(inner, false))),
    }
}

// =============================================================================
// Fm  ->  p::Formula  (open: De-Bruijn → named binders)
// =============================================================================

/// Convert a closed locally-nameless formula back to parser-AST form.  Each
/// binder is opened to a fresh named `VarSpec` (a monotonic `counter` keeps
/// every binder's `(name, idx, sort)` identity unique so body occurrences
/// resolve unambiguously and no binder shadows another — the parser-AST
/// analogue of HS's positional De-Bruijn resolution).  Display names are
/// re-derived by the renderer's own `Precise.Fresh` pass, so these indices
/// never surface in output.
pub(crate) fn to_p_formula(fm: &Fm) -> p::Formula {
    let mut counter: u64 = 0;
    to_p(fm, &[], &mut counter)
}

fn to_p(fm: &Fm, opened: &[p::VarSpec], counter: &mut u64) -> p::Formula {
    match fm {
        Fm::Ato(a) => {
            let a = subst_bound_atom_at_depth(a, &open_subst(opened), 0);
            p::Formula::Atom(gatom_to_atom(&a))
        }
        Fm::Tf(true) => p::Formula::True,
        Fm::Tf(false) => p::Formula::False,
        Fm::Not(p_) => p::Formula::Not(Box::new(to_p(p_, opened, counter))),
        Fm::Conn(c, a, b) => {
            let a = Box::new(to_p(a, opened, counter));
            let b = Box::new(to_p(b, opened, counter));
            match c {
                Conn::And => p::Formula::And(a, b),
                Conn::Or => p::Formula::Or(a, b),
                Conn::Imp => p::Formula::Implies(a, b),
                Conn::Iff => p::Formula::Iff(a, b),
            }
        }
        Fm::Qua(quant, binding, body) => {
            let v = p::VarSpec {
                name: binding.name.clone(),
                idx: {
                    let i = *counter;
                    *counter += 1;
                    i
                },
                sort: binding.sort,
                typ: None,
            };
            let mut new_opened = opened.to_vec();
            new_opened.push(v.clone());
            let inner = Box::new(to_p(body, &new_opened, counter));
            match quant {
                Quant::All => p::Formula::Forall(vec![v], inner),
                Quant::Ex => p::Formula::Exists(vec![v], inner),
            }
        }
    }
}

/// HS `formulaActionFacts` (Generation.hs:118-124): the `Fact`s appearing in
/// `Action` atoms of a formula.
pub(crate) fn formula_action_facts(fm: &Fm) -> Vec<GFact> {
    let mut out = Vec::new();
    collect_atom_facts(fm, &mut |a, out| {
        if let GAtom::Action(f, _) = a {
            out.push(f.clone());
        }
    }, &mut out);
    out
}

/// The `Fact`s appearing in `Pred` (predicate-sugar) atoms of a formula — the
/// atoms HS `expandLemma` resolves against the theory's predicates.
pub(crate) fn formula_pred_facts(fm: &Fm) -> Vec<GFact> {
    let mut out = Vec::new();
    collect_atom_facts(fm, &mut |a, out| {
        if let GAtom::Pred(f) = a {
            out.push(f.clone());
        }
    }, &mut out);
    out
}

fn collect_atom_facts<F: FnMut(&GAtom, &mut Vec<GFact>)>(
    fm: &Fm,
    grab: &mut F,
    out: &mut Vec<GFact>,
) {
    match fm {
        Fm::Ato(a) => grab(a, out),
        Fm::Tf(_) => {}
        Fm::Not(p_) => collect_atom_facts(p_, grab, out),
        Fm::Conn(_, a, b) => {
            collect_atom_facts(a, grab, out);
            collect_atom_facts(b, grab, out);
        }
        Fm::Qua(_, _, body) => collect_atom_facts(body, grab, out),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(name: &str, idx: u64) -> p::VarSpec {
        p::VarSpec { name: name.to_string(), idx, sort: p::SortHint::Node, typ: None }
    }

    /// A( x ) @ #i with x free (idx 0) — the public-names case test body,
    /// pre-quantifier.
    fn action_a_x_at_i(x_idx: u64) -> Fm {
        proto_fact_formula(
            "A",
            vec![free_term(msg_var_idx("x", x_idx))],
            GTerm::Var(BVar::Bound(0)),
        )
    }

    fn msg_var_idx(name: &str, idx: u64) -> p::VarSpec {
        p::VarSpec { name: name.to_string(), idx, sort: p::SortHint::Msg, typ: None }
    }

    /// `Ex #i. A(x)@#i` (x free) round-trips p::Formula → Fm → p::Formula
    /// structurally (binder names preserved, De-Bruijn indices resolved).
    #[test]
    fn case_test_round_trip() {
        // Ex #i. A(x)@i, parser AST (x untagged bare, #i node binder).
        let src = p::Formula::Exists(
            vec![node("i", 0)],
            Box::new(p::Formula::Atom(p::Atom::Action(
                p::Fact {
                    persistent: false,
                    name: "A".into(),
                    args: vec![p::Term::Var(p::VarSpec {
                        name: "x".into(),
                        idx: 0,
                        sort: p::SortHint::Untagged,
                        typ: None,
                    })],
                    annotations: vec![],
                },
                p::Term::Var(node("i", 0)),
            ))),
        );
        let fm = from_p_formula(&src);
        // x is the only free var; it resolves to Msg.
        let fv = frees(&fm);
        assert_eq!(fv.len(), 1);
        assert_eq!(fv[0].name, "x");
        assert_eq!(fv[0].sort, p::SortHint::Msg);
        // Round-trip: the temporal binder stays #i, body action A(x)@#i.
        let back = to_p_formula(&fm);
        assert!(matches!(back, p::Formula::Exists(_, _)));
    }

    /// `rename` shifts free-var indices and advances the counter by the
    /// (max-min+1) span (HS Term/LTerm.hs:614-621).
    #[test]
    fn rename_shifts_and_advances_counter() {
        let fm = Fm::Qua(
            Quant::Ex,
            GBinding { name: "i".into(), sort: p::SortHint::Node },
            Box::new(action_a_x_at_i(0)),
        );
        let mut counter = 0u64;
        let t1 = rename(&fm, &mut counter);
        assert_eq!(counter, 1); // one free var, span 1
        assert_eq!(frees(&t1)[0].idx, 0); // shift 0
        let t2 = rename(&fm, &mut counter);
        assert_eq!(counter, 2);
        assert_eq!(frees(&t2)[0].idx, 1); // shift 1 → x.1
    }

    /// `simplifyFormula` collapses `⇒ ⊤` to `⊤` and quantifiers over `⊤`
    /// to `⊤` — the acc_*_inj single-var case (Formula.hs:388-409).
    #[test]
    fn simplify_true_implication_and_quantifier() {
        // ∀ x. (P => ⊤)  ->  ⊤
        let inner = proto_fact_formula("P", vec![], GTerm::Var(BVar::Bound(0)))
            .implies(Fm::Tf(true));
        let f = Fm::Qua(Quant::All, GBinding { name: "x".into(), sort: p::SortHint::Msg }, Box::new(inner));
        assert_eq!(simplify_formula(f), Fm::Tf(true));
    }

    /// `simplifyFormula1` rewrites a reflexive equality `t = t` to `⊤`
    /// (Formula.hs:389) and leaves a non-reflexive one alone.
    #[test]
    fn simplify_reflexive_equality() {
        let x = msg_var_idx("x", 0);
        let y = msg_var_idx("y", 0);
        assert_eq!(
            simplify_formula(Fm::Ato(GAtom::Eq(free_term(x.clone()), free_term(x.clone())))),
            Fm::Tf(true)
        );
        // x = y is preserved.
        let neq = Fm::Ato(GAtom::Eq(free_term(x), free_term(y)));
        assert_eq!(simplify_formula(neq.clone()), neq);
    }

    /// `pullQuantifiers` pulls a universal out of a conjunction and shifts the
    /// OTHER conjunct's dangling bound indices up by one (Generation.hs:280,291):
    /// `(∀ j. A@j) ∧ B@Bound(0)` becomes `∀ j. (A@Bound(0) ∧ B@Bound(1))`.
    #[test]
    fn pull_quantifiers_shifts_dangling_bound() {
        let all_j = Fm::Qua(
            Quant::All,
            GBinding { name: "j".into(), sort: p::SortHint::Node },
            Box::new(proto_fact_formula("A", vec![], GTerm::Var(BVar::Bound(0)))),
        );
        // B@Bound(0): a reference dangling past this formula.
        let b = proto_fact_formula("B", vec![], GTerm::Var(BVar::Bound(0)));
        let pulled = pull_quantifiers(&[Quant::All], all_j.and(b));
        // Expect: ∀ j. (A@Bound(0) ∧ B@Bound(1)).
        let Fm::Qua(Quant::All, _, body) = pulled else {
            panic!("expected a universal at the top");
        };
        let Fm::Conn(Conn::And, l, r) = *body else {
            panic!("expected a conjunction under the binder");
        };
        assert_eq!(*l, proto_fact_formula("A", vec![], GTerm::Var(BVar::Bound(0))));
        assert_eq!(*r, proto_fact_formula("B", vec![], GTerm::Var(BVar::Bound(1))));
    }

    /// `mergeQuantifiers` pulls an existential out of an implication's guard,
    /// turning it universal: `(∃ i. P@i) ⇒ Q` becomes `∀ i. (P@i ⇒ Q)`.
    #[test]
    fn merge_pulls_exists_through_implication() {
        // (Ex #i. P@i) => (Q)  with Q closed (a nullary fact @ a fresh bound)
        let guard = Fm::Qua(
            Quant::Ex,
            GBinding { name: "i".into(), sort: p::SortHint::Node },
            Box::new(proto_fact_formula("P", vec![], GTerm::Var(BVar::Bound(0)))),
        );
        let concl = Fm::Tf(false);
        let f = guard.implies(concl);
        let merged = merge_quantifiers(f);
        // The merge leaves a universal binder over #i at the top.
        assert!(matches!(merged, Fm::Qua(Quant::All, _, _)));
    }
}
