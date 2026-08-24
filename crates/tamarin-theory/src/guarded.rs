// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Constraint.System.Guarded.formulaToGuarded` —
//! the conversion from a surface-formula (lemma / restriction) to the
//! guarded-fragment representation that Tamarin's solver consumes.
//!
//! A guarded formula is one where every quantified variable is bound
//! by an action or equality atom that fires before it's referenced.
//! The check is polarity-aware: `not (Ex x. P(x) @ #i)` becomes
//! equivalent to `All x #i. P(x) @ #i ==> ⊥` and so on.
//!
//! The conversion INPUT is `tamarin_parser::ast::Formula` (named
//! variables, matching HS's `LNFormula`), while the OUTPUT `Guarded`
//! uses the BVar-based, locally-nameless DeBruijn representation
//! (`GAtom`/`GTerm` from `guarded_types`), mirroring HS's
//! `Guarded (String,LSort) Name LVar` whose atoms are
//! `Atom (VTerm c (BVar v))`.

use std::collections::BTreeSet;

use crate::atom::{map_atom, Atom};
use crate::formula::BLNTerm;
use crate::guarded_types::cow_pair_arc;
use tamarin_parser::ast as p;
use tamarin_term::lterm::{sort_prefix, HasFrees, LNTerm, LSort, LVar};
use tamarin_term::term::map_lits;
use tamarin_term::vterm::Lit;
use tamarin_utils::cow::{cow_map_arc, cow_map_vec, cow_pair};

pub use crate::guarded_types::{
    atom_to_gatom_free, close_subst, fact_to_gfact_free, ga, gatom_to_atom, gfact_to_fact,
    gterm_to_term, lvar_to_binding, map_free_atom, map_free_fact, map_free_term, open_subst,
    subst_bound_atom_at_depth, subst_bound_fact_at_depth, subst_bound_term_at_depth,
    subst_free_atom_at_depth, subst_free_fact_at_depth, subst_free_term_at_depth,
    term_to_gterm_free, BVar, GAtom, GBinding, GFact, GTerm,
};

// =============================================================================
// Guarded data type
// =============================================================================

#[derive(Debug, Copy, Clone, PartialEq, Hash)]
pub enum Quant {
    All,
    Ex,
}

// ===========================================================================
// HS-faithful Ord for Guarded
// ===========================================================================
//
// HS's `Theory.Constraint.System.Guarded.Guarded` derives Ord structurally
// (Guarded.hs:121-129):
//
//     data Guarded s c v = GAto  (Atom ...)
//                        | GDisj (Disj (Guarded ...))
//                        | GConj (Conj (Guarded ...))
//                        | GGuarded Quantifier [s] [Atom ...] (Guarded ...)
//
// Constructor order: GAto < GDisj < GConj < GGuarded.
// Within each, lexicographic on contents.
//
// HS's `Set LNGuarded` iterates via `S.toList` which yields elements in
// ascending Ord.  Rust's `sys.formulas: Vec<Guarded>` iterates in
// insertion order, so the impl-pass / reduce-formulas / eval-formula-atoms
// passes see clauses in a DIFFERENT order than HS does — which propagates
// to which clause's matches fire first → goal-nrs of newly-inserted
// Disj formulas → goal pick at downstream proof steps.
//
// This module provides `cmp_guarded` (and helpers `cmp_atom` /
// `cmp_term`) that mirror HS's derived Ord chain.

/// HS-faithful structural comparison for Guarded.  Mirrors HS's derived
/// `Ord (Guarded s c v)` on `Theory.Constraint.System.Guarded.Guarded`.
pub fn cmp_guarded(a: &Guarded, b: &Guarded) -> std::cmp::Ordering {
    let ta = guarded_tag(a);
    let tb = guarded_tag(b);
    if ta != tb {
        return ta.cmp(&tb);
    }
    // Tag equality above guarantees same variant, so each `let … else` binding
    // of `b` is infallible.  Match `a` exhaustively (no wildcard) so a new
    // `Guarded` variant forces a comparison here.
    match a {
        Guarded::Atom(x) => {
            let Guarded::Atom(y) = b else {
                unreachable!("guarded tag matched Atom")
            };
            cmp_atom(x, y)
        }
        Guarded::Disj(xs) => {
            let Guarded::Disj(ys) = b else {
                unreachable!("guarded tag matched Disj")
            };
            cmp_slice(xs, ys, cmp_guarded)
        }
        Guarded::Conj(xs) => {
            let Guarded::Conj(ys) = b else {
                unreachable!("guarded tag matched Conj")
            };
            cmp_slice(xs, ys, cmp_guarded)
        }
        Guarded::GGuarded {
            qua: q1,
            vars: v1,
            guards: g1,
            body: b1,
        } => {
            let Guarded::GGuarded {
                qua: q2,
                vars: v2,
                guards: g2,
                body: b2,
            } = b
            else {
                unreachable!("guarded tag matched GGuarded")
            };
            cmp_quant(q1, q2)
                // HS-faithful: in `LNGuarded = Guarded (String,LSort) Name
                // LVar` (Guarded.hs:391), the `s` parameter — used
                // for GGuarded's binding list — is the TUPLE
                // `(String, LSort)`, NOT `LVar`.  Our `GBinding` carries
                // exactly those two fields, so bindings sort by
                // (name, sort) only (cmp_binding); there is no idx on a
                // binding.  Free-var comparison inside terms still uses
                // cmp_varspec which mirrors HS's `Ord LVar = (idx, sort, name)`.
                .then_with(|| cmp_slice(v1, v2, cmp_binding))
                .then_with(|| cmp_slice(g1, g2, cmp_atom))
                .then_with(|| cmp_guarded(b1, b2))
        }
    }
}

fn guarded_tag(g: &Guarded) -> u8 {
    match g {
        Guarded::Atom(_) => 0,
        Guarded::Disj(_) => 1,
        Guarded::Conj(_) => 2,
        Guarded::GGuarded { .. } => 3,
    }
}

fn cmp_quant(a: &Quant, b: &Quant) -> std::cmp::Ordering {
    let ta = if matches!(a, Quant::All) { 0u8 } else { 1 };
    let tb = if matches!(b, Quant::All) { 0u8 } else { 1 };
    ta.cmp(&tb)
}

/// HS list Ord: element-by-element, shorter < longer.
pub(crate) fn cmp_slice<T, F>(a: &[T], b: &[T], mut f: F) -> std::cmp::Ordering
where
    F: FnMut(&T, &T) -> std::cmp::Ordering,
{
    use std::cmp::Ordering;
    let mut i = 0;
    loop {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => {
                let c = f(x, y);
                if c != Ordering::Equal {
                    return c;
                }
                i += 1;
            }
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (None, None) => return Ordering::Equal,
        }
    }
}

/// HS-faithful Ord for `ProtoAtom`: Action < EqE < Subterm < Less < Last
/// < Syntactic (Theory/Model/Atom.hs:78-84).  Rust's `GAtom` declares
/// variants in a different order; we re-map to HS's order via
/// `atom_tag`.  `LessMset` has no HS equivalent — put at end.
pub fn cmp_atom(a: &GAtom, b: &GAtom) -> std::cmp::Ordering {
    let ta = atom_tag(a);
    let tb = atom_tag(b);
    if ta != tb {
        return ta.cmp(&tb);
    }
    // Tag equality above guarantees same variant, so each `let … else` binding
    // of `b` is infallible.  Match `a` exhaustively (no wildcard) so a new
    // `GAtom` variant forces a comparison here.
    match a {
        // HS `data ProtoAtom s t = Action t (Fact t) | ...` derives Ord
        // (Atom.hs:78-84), so the derived comparison is the timepoint term
        // `t` FIRST, then the `Fact t`.  Rust's `GAtom::Action(GFact, GTerm)`
        // stores fact-then-term, so we must compare the timepoint first.
        GAtom::Action(f1, t1) => {
            let GAtom::Action(f2, t2) = b else {
                unreachable!("atom tag matched Action")
            };
            cmp_term(t1, t2).then_with(|| cmp_fact(f1, f2))
        }
        GAtom::Eq(a1, b1) => {
            let GAtom::Eq(a2, b2) = b else {
                unreachable!("atom tag matched Eq")
            };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
        GAtom::Subterm(a1, b1) => {
            let GAtom::Subterm(a2, b2) = b else {
                unreachable!("atom tag matched Subterm")
            };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
        GAtom::Less(a1, b1) => {
            let GAtom::Less(a2, b2) = b else {
                unreachable!("atom tag matched Less")
            };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
        GAtom::Last(t1) => {
            let GAtom::Last(t2) = b else {
                unreachable!("atom tag matched Last")
            };
            cmp_term(t1, t2)
        }
        GAtom::Pred(f1) => {
            let GAtom::Pred(f2) = b else {
                unreachable!("atom tag matched Pred")
            };
            cmp_fact(f1, f2)
        }
        GAtom::LessMset(a1, b1) => {
            let GAtom::LessMset(a2, b2) = b else {
                unreachable!("atom tag matched LessMset")
            };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
    }
}

fn atom_tag(a: &GAtom) -> u8 {
    match a {
        GAtom::Action(_, _) => 0,
        GAtom::Eq(_, _) => 1,
        GAtom::Subterm(_, _) => 2,
        GAtom::Less(_, _) => 3,
        GAtom::Last(_) => 4,
        GAtom::Pred(_) => 5,
        GAtom::LessMset(_, _) => 6, // Rust-only, no HS equivalent
    }
}

/// HS Term Ord: `Lit < FApp` (Term.hs).  Walks `GTerm`.  Bound vars sort
/// before Free vars (HS `BVar = Bound Int | Free v` declaration order).
pub fn cmp_term(a: &GTerm, b: &GTerm) -> std::cmp::Ordering {
    use GTerm::*;
    let (ca, sa) = term_class(a);
    let (cb, sb) = term_class(b);
    if ca != cb {
        return ca.cmp(&cb);
    }
    // FApp class (ca == cb == 1): HS `Ord (Term a)` compares `FAPP fsym ts`
    // by `compare fsym` THEN `compare ts` (derived Ord on
    // `Term a = LIT a | FAPP FunSym [Term a]`, Term/Term/Raw.hs:71-75, see line 74).  The
    // `FunSym` Ord is `NoEq < AC < C < List`, and within `NoEq` it is
    // `Ord NoEqSym = (name, (arity, privacy, constructability, ndc))`
    // (FunctionSymbols.hs:131-132) — i.e. compared by NAME first.
    //
    // RS special-cases several HS `FAPP (NoEq sym)` terms into dedicated
    // `GTerm` variants (`Pair`=pair, `BinOp Exp`=exp, `Diff`=diff,
    // `NumberOne`=one, `NatOne`=tone, `DhNeutral`=DH_neutral) and AC
    // ops into `BinOp Mult/Union/Xor/NatPlus`.  These must NOT be ordered
    // by RUST VARIANT — HS's `FunSym` Ord is name-based (e.g. HS sorts
    // `exp(...)` BEFORE `pair(...)` because `"exp" < "pair"`), and a
    // variant-based order swaps the `S.toList sFormulas` iteration order
    // in `evalFormulaAtoms`, flipping which co-created SidUpdated DisjG
    // got the lower `gsNr` (UM3 `CK_secure_UM3` abstract-vs-transcript
    // disj swap).
    //
    // Faithful: compare two FApp-class terms by their HS `FunSym` key
    // (`funsym_key`), then by the argument list (flattened+sorted for AC,
    // matching `fAppAC`'s `sort (...)`, Term/Term/Raw.hs:118-129, see line 123).
    if ca == 1 {
        // Borrowed FunSym key (no per-comparison allocation): compare
        // (outer, name-bytes, arity) in HS order without materialising a
        // `Vec`.  `cmp_term` is a very hot path (every BTreeSet/Map op on
        // guarded terms), so the name must be compared as a `&[u8]` slice.
        let (oa, na, aa) = funsym_key(a);
        let (ob, nb, ab) = funsym_key(b);
        let kc = oa
            .cmp(&ob)
            .then_with(|| na.cmp(nb))
            .then_with(|| aa.cmp(&ab));
        if kc != std::cmp::Ordering::Equal {
            return kc;
        }
        // Same FunSym: compare argument lists in HS `[Term a]` order.
        // AC ops compare a sorted, flattened multiset (HS stores args
        // pre-sorted by `fAppAC`); everything else compares positionally.
        if let (BinOp(o1, _, _), BinOp(o2, _, _)) = (a, b) {
            if is_ac_binop(o1) && is_ac_binop(o2) {
                let mut args_a = Vec::new();
                let mut args_b = Vec::new();
                flatten_ac_binop(o1, a, &mut args_a);
                flatten_ac_binop(o2, b, &mut args_b);
                args_a.sort_by(|x, y| cmp_term(x, y));
                args_b.sort_by(|x, y| cmp_term(x, y));
                return cmp_slice(&args_a, &args_b, |x, y| cmp_term(x, y));
            }
        }
        return cmp_fapp_args(a, b);
    }
    match (a, b) {
        // Lit class:
        (Var(v1), Var(v2)) => cmp_bvar(v1, v2),
        (PubLit(s1), PubLit(s2)) => s1.cmp(s2),
        (FreshLit(s1), FreshLit(s2)) => s1.cmp(s2),
        (NatLit(s1), NatLit(s2)) => s1.cmp(s2),
        (Number(n1), Number(n2)) => n1.cmp(n2),
        _ => {
            // Lit-class sub-discriminator (Con < Var; among Con by NameTag
            // then name) — handled by `term_class`'s sub_tag.
            sa.cmp(&sb)
        }
    }
}

/// HS `FunSym` Ord key for a FApp-class `GTerm`.  Returns
/// `(outer, name, arity)` where `outer` mirrors HS's `FunSym` constructor
/// order `NoEq(0) < AC(1) < C(2) < List(3)` (FunctionSymbols.hs:150-154)
/// and, within `NoEq`, `(name, arity)` mirrors `Ord NoEqSym` (compared by
/// name then arity — privacy/constructability never disambiguate two
/// distinct symbols sharing a name+arity).  The builtin AC ops carry no name;
/// their `ACSym` order is `Union < Mult < Xor < NatPlus < ACfct`
/// (FunctionSymbols.hs:138-139), encoded in the third (`arity`) field as an
/// index so AC terms sort among themselves by ACSym and after every NoEq
/// term.  A user-defined `ACfct` carries its name, which sorts after the
/// builtin ops' empty name and orders two `ACfct`s by name — mirroring
/// `Ord ACfctSym`, whose first tuple component is the name.
///
/// `em/2` is HS's sole `C` symbol.  `CSym` is a single nullary constructor
/// (`data CSym = EMap`, FunctionSymbols.hs:142-143), so a `C` key carries
/// neither name nor arity and every `C` term ties on those two fields.
/// The classification is by NAME ALONE: the parser's `naryOpApp` builds
/// `fAppC EMap` for any application written `em(…)`, whether `em` comes from
/// the `bilinear-pairing` builtin or from a user `functions:` declaration
/// (Theory/Text/Parser/Term.hs:103) — so a `GTerm`, which carries only the
/// name, has everything the decision needs.  The `op{t1}t2` spelling is NOT
/// covered: `binaryAlgApp` has no `em` case and builds `fAppNoEq`
/// (Theory/Text/Parser/Term.hs:119-121), matching `AlgApp`'s `NoEq` key below.
/// Arity is pinned to 2 because a `C` term of any other arity is rejected
/// downstream (`viewTerm2`, Term/Term/Raw.hs:190).
fn funsym_key(t: &GTerm) -> (u8, &[u8], usize) {
    use GTerm::*;
    // NoEq syms: outer = 0, key by (name-bytes, arity).  Static byte-string
    // literals (`b"pair"` etc.) are `&'static [u8]` and coerce to the
    // elided output lifetime; `n.as_bytes()` borrows from `t`.  No alloc.
    match t {
        // RS special-cased HS `FAPP (NoEq sym)` terms:
        Pair(_) => (0, b"pair", 2),
        BinOp(p::BinOp::Exp, _, _) => (0, b"exp", 2),
        Diff(_, _) => (0, b"diff", 2),
        NumberOne => (0, b"one", 0),
        NatOne => (0, b"tone", 0),
        DhNeutral => (0, b"DH_neutral", 0),
        // C sym: outer = 2, above every NoEq and AC term whatever its name.
        App(n, args) if &**n == "em" && args.len() == 2 => (2, b"", 0),
        App(n, args) => (0, n.as_bytes(), args.len()),
        AlgApp(n, _, _) => (0, n.as_bytes(), 2),
        // AC ops: outer = 1, ACSym order Union<Mult<Xor<NatPlus> in field 3.
        BinOp(p::BinOp::Union, _, _) => (1, b"", 0),
        BinOp(p::BinOp::Mult, _, _) => (1, b"", 1),
        BinOp(p::BinOp::Xor, _, _) => (1, b"", 2),
        BinOp(p::BinOp::NatPlus, _, _) => (1, b"", 3),
        BinOp(p::BinOp::AcFct(n), _, _) => (1, n.as_bytes(), 4),
        // PatMatch is RS-only with no HS equivalent — sort after all.
        PatMatch(_) => (255, b"", 0),
        // Lit-class terms never reach here (ca != 1).
        _ => (254, b"", 0),
    }
}

/// The HS argument pair `[t1, t2]` of a `pairSym`-headed term, as
/// `(t1, spine)` where `spine` is the operand list of `t2` in the same
/// flattened spelling — so `t2` is `Pair(spine)` when `spine` has two or more
/// elements and `spine[0]` when it has one.
///
/// HS builds nested pairs (`fAppPair (x, y) = fAppNoEq pairSym [x, y]`,
/// Term/Term.hs:163), so `<a, b, c>` is `pair(a, pair(b, c))` and its arity-2
/// argument list is `[a, pair(b, c)]`.  RS stores that spine FLAT in
/// `Pair`, and also carries the source prefix spelling `pair(a, b)` as
/// `App("pair", [a, b])` — both key `(0, "pair", 2)` in [`funsym_key`], so
/// both must expose the same nested argument list to `Ord`.
fn pair_spine(t: &GTerm) -> Option<(&GTerm, &[GTerm])> {
    match t {
        GTerm::Pair(x) if x.len() >= 2 => Some((&x[0], &x[1..])),
        GTerm::App(n, x) if &**n == "pair" && x.len() == 2 => Some((&x[0], &x[1..])),
        GTerm::AlgApp(n, l, r) if &**n == "pair" => Some((l, std::slice::from_ref(&**r))),
        _ => None,
    }
}

/// Compare two pair spines: `x` and `y` each stand for the term
/// `Pair(x)`/`Pair(y)` when they hold two or more elements and for their sole
/// element otherwise.  Recurses down the spine so that, at the position where
/// one side's spine ends and the other's continues, HS's `Ord` pits a plain
/// term against a `pairSym` FAPP — which is why `<a, z>` sorts BEFORE
/// `<a, b, c>` (`z` is a LIT, `pair(b, c)` a FAPP, and `LIT _ < FAPP _ _`,
/// Term/Term/Raw.hs:72-74).
fn cmp_pair_spine(x: &[GTerm], y: &[GTerm]) -> std::cmp::Ordering {
    if x.is_empty() || y.is_empty() {
        return x.len().cmp(&y.len());
    }
    match (x.len(), y.len()) {
        (1, 1) => cmp_term(&x[0], &y[0]),
        (1, _) => cmp_term_vs_pair_spine(&x[0], y),
        (_, 1) => cmp_term_vs_pair_spine(&y[0], x).reverse(),
        _ => cmp_term(&x[0], &y[0]).then_with(|| cmp_pair_spine(&x[1..], &y[1..])),
    }
}

/// Compare a term `t` against the pair `Pair(y)` that spine `y` (two or more
/// elements) stands for, without materialising that `Pair`.  Mirrors
/// `cmp_term`'s dispatch: LIT class first, then the `FunSym` key against
/// `pairSym`, then the argument lists.
fn cmp_term_vs_pair_spine(t: &GTerm, y: &[GTerm]) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    if term_class(t).0 != 1 {
        return Ordering::Less;
    }
    let (o, n, a) = funsym_key(t);
    let key = o
        .cmp(&0)
        .then_with(|| n.cmp(b"pair".as_slice()))
        .then_with(|| a.cmp(&2));
    if key != Ordering::Equal {
        return key;
    }
    match pair_spine(t) {
        Some((h, tail)) => cmp_term(h, &y[0]).then_with(|| cmp_pair_spine(tail, &y[1..])),
        None => Ordering::Equal,
    }
}

/// Compare the argument lists of two same-FunSym, non-AC FApp terms,
/// mirroring HS's positional `compare ts` on `[Term a]`.
fn cmp_fapp_args(a: &GTerm, b: &GTerm) -> std::cmp::Ordering {
    use GTerm::*;
    // A `pairSym` key ties every pair spelling, whose HS argument list is the
    // arity-2 `[t1, t2]` of the RIGHT-NESTED spine rather than RS's flat
    // operand vector — see [`pair_spine`].
    if let (Some((ha, ta)), Some((hb, tb))) = (pair_spine(a), pair_spine(b)) {
        return cmp_term(ha, hb).then_with(|| cmp_pair_spine(ta, tb));
    }
    match (a, b) {
        (App(_, x), App(_, y)) => cmp_slice(x, y, cmp_term),
        (AlgApp(_, l1, r1), AlgApp(_, l2, r2)) => cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        (Diff(l1, r1), Diff(l2, r2)) => cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        (BinOp(_, l1, r1), BinOp(_, l2, r2)) => cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        (PatMatch(x), PatMatch(y)) => cmp_term(x, y),
        // 0-arity builtins (one/tone/DH_neutral): no args.
        (NumberOne, NumberOne) | (NatOne, NatOne) | (DhNeutral, DhNeutral) => {
            std::cmp::Ordering::Equal
        }
        // Cross-variant operands only reach here when funsym_key tied them
        // (e.g. App("exp",[..]) vs BinOp(Exp,..) — both key (0,"exp",2));
        // compare their argument lists positionally.
        _ => cmp_slice(&fapp_args(a), &fapp_args(b), cmp_term),
    }
}

/// Collect the positional argument list of a FApp-class term (for
/// cross-representation comparison when two terms share a FunSym key).
fn fapp_args(t: &GTerm) -> Vec<GTerm> {
    use GTerm::*;
    match t {
        App(_, x) => x.to_vec(),
        Pair(x) => x.to_vec(),
        AlgApp(_, l, r) | Diff(l, r) | BinOp(_, l, r) => vec![(**l).clone(), (**r).clone()],
        PatMatch(x) => vec![(**x).clone()],
        _ => Vec::new(),
    }
}

/// HS `Ord BVar`: derived; `Bound < Free`.  Within each constructor,
/// compare the contents — `Int` for Bound, LVar Ord (idx, sort, name) for Free.
pub fn cmp_bvar(a: &BVar, b: &BVar) -> std::cmp::Ordering {
    match (a, b) {
        (BVar::Bound(_), BVar::Free(_)) => std::cmp::Ordering::Less,
        (BVar::Free(_), BVar::Bound(_)) => std::cmp::Ordering::Greater,
        (BVar::Bound(n1), BVar::Bound(n2)) => n1.cmp(n2),
        (BVar::Free(v1), BVar::Free(v2)) => cmp_varspec(v1, v2),
    }
}

/// Returns `(class, sub_tag)` where class=0 for Lit-like, 1 for FApp-like.
///
/// HS-faithful: a `GTerm` corresponds to `Term (Lit Name (BVar v))`, whose
/// derived `Ord` is `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74), and within
/// `LIT`, `Lit c v = Con c | Var v` derives `Con < Var` (VTerm.hs:56-57).
/// Therefore ALL constant literals (Pub/Fresh/Nat names) sort BEFORE any
/// variable.  Among constants, `Ord Name` compares the `NameTag` first
/// (`FreshName | PubName | NodeName | NatName`, LTerm.hs:219-220) so the literal
/// order is Fresh < Pub < Nat, then by name string.  Variables come last in
/// the `LIT` class.
///
/// The 0-arity builtins `NumberOne`/`NatOne`/`DhNeutral` are NOT literals in
/// HS — they are `fAppNoEq oneSym []` / `fAppNoEq natOneSym []` /
/// `fAppNoEq dhNeutralSym []` (Term/Term.hs:127-130), i.e. nullary function
/// applications, so they belong to the FApp class.
fn term_class(t: &GTerm) -> (u8, u8) {
    use GTerm::*;
    match t {
        // LIT (Con name): constants, ordered by Name's NameTag (Fresh<Pub<Nat).
        FreshLit(_) => (0, 0),
        PubLit(_) => (0, 1),
        NatLit(_) => (0, 2),
        Number(_) => (0, 3),
        // LIT (Var v): variables sort after all constants.
        Var(_) => (0, 4),
        // FAPP: nullary builtins are NoEq function applications, not literals.
        // NB: the second field below is a tie-breaker ONLY within the Lit
        // class (sub-tags 0..4); the FApp sub-tags (1,0)..(1,8) are never
        // consulted for ordering, because `cmp_term` dispatches every
        // FApp-class term through `funsym_key`/`cmp_fapp_args` (the `ca == 1`
        // branch) and returns before the `sa.cmp(&sb)` sub-tag fallthrough.
        NumberOne => (1, 0),
        NatOne => (1, 1),
        DhNeutral => (1, 2),
        App(_, _) => (1, 3),
        AlgApp(_, _, _) => (1, 4),
        Pair(_) => (1, 5),
        Diff(_, _) => (1, 6),
        BinOp(_, _, _) => (1, 7),
        PatMatch(_) => (1, 8),
    }
}

/// HS-faithful: which `BinOp`s are AC (associative-commutative)?
/// Mirrors HS's `MaudeSig`-attribute classification: Mult, Union, Xor,
/// NatPlus and the user-declared `[AC]` symbols are AC; Exp is NOT
/// (right-associative algebraic).
fn is_ac_binop(o: &p::BinOp) -> bool {
    use p::BinOp::*;
    matches!(o, Mult | Union | Xor | NatPlus | AcFct(_))
}

/// Flatten an AC-BinOp chain into a flat operand list, BORROWING the operands.
/// E.g. `BinOp(Union, BinOp(Union, a, b), c)` flattens to `[&a, &b, &c]`.
/// Non-matching outer terms are pushed verbatim (no recursion into
/// nested non-Union/non-same-op subtrees).  Borrowing keeps the hot
/// `cmp_term` AC branch allocation-free per operand.
fn flatten_ac_binop<'a>(op: &p::BinOp, t: &'a GTerm, out: &mut Vec<&'a GTerm>) {
    match t {
        GTerm::BinOp(inner_op, l, r) if inner_op == op => {
            flatten_ac_binop(op, l, out);
            flatten_ac_binop(op, r, out);
        }
        _ => out.push(t),
    }
}

/// HS-faithful Ord for free `LVar`: `(idx, sort, name)` lexicographic
/// (Term/LTerm.hs:545-548).  Rust's `p::VarSpec` has the same fields
/// in a different declaration order — we compare in HS's order.
/// Used for VarSpecs that appear as FREE vars inside terms.
pub fn cmp_varspec(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx
        .cmp(&b.idx)
        .then_with(|| a.sort.cmp(&b.sort))
        .then_with(|| a.name.cmp(&b.name))
}

/// HS-faithful Ord for GGuarded *binding* entries.  In LNGuarded, the
/// binding type is `(String, LSort)` — Guarded.hs:391.  So bindings
/// sort by `(name, sort)` lex.  Our `GBinding` carries only those
/// two fields.
pub fn cmp_binding(a: &GBinding, b: &GBinding) -> std::cmp::Ordering {
    a.name.cmp(&b.name).then_with(|| a.sort.cmp(&b.sort))
}

/// HS Fact Ord (Theory/Model/Fact.hs:173-174): `compare tag tag' <> compare ts
/// ts'`.  Annotations are explicitly IGNORED in `Ord (Fact t)`
/// (Theory/Model/Fact.hs:169-174, whose line-169 comment reads "Ignore
/// annotations in equality and ord testing").  Works on
/// `GFact` (HS `Fact (VTerm c (BVar v))`).
///
/// The HS `FactTag` Ord (Theory/Model/Fact.hs:136-148, derived) compares a `ProtoFact`
/// by `(Multiplicity, String, Int)` where `Multiplicity = Persistent |
/// Linear` orders `Persistent < Linear`, and `Int` is the arity.  Rust's
/// `bool` Ord gives `false < true`, so to reproduce `Persistent < Linear`
/// we must order `persistent == true` BEFORE `persistent == false` — i.e.
/// reverse the bool comparison.  Arity (`args.len()`) is part of the
/// `FactTag` key and is therefore compared BEFORE the term list, exactly
/// as `compare tag tag'` precedes `compare ts ts'`.
///
/// SPECIAL-TAG SEGREGATION: HS `FactTag` (Theory/Model/Fact.hs:136-148, derived Ord) is
/// `ProtoFact Multiplicity String Int | FreshFact | OutFact | InFact |
/// KUFact | KDFact | DedFact | TermFact`.  With a derived `Ord` the
/// *constructor index* dominates, so EVERY `ProtoFact` sorts before EVERY
/// special tag, and the special tags order amongst themselves in that
/// declaration sequence (Fresh < Out < In < KU < KD < Ded < Term).
///
/// `GFact` carries only `(persistent, name)`, not the full `FactTag` enum,
/// but the parser (`fact()` in tamarin-parser, mirroring HS `mkProtoFact`,
/// Parser/Fact.hs:56-63) has already CANONICALISED reserved names to their
/// exact tag spelling — `Fr`, `Out`, `In`, `KU`, `KD`, `Ded` — and fixed
/// their multiplicity (KU/KD persistent, the rest linear).  So we can
/// recover the tag class from the name string with an exact (case-sensitive)
/// match, identical to `fact_to_lnfact`'s mapping in `elaborate.rs`.  Names
/// that are not one of those reserved spellings (including the ordinary
/// proto-fact `K`) are `ProtoFact`s.
fn fact_tag_class(f: &GFact) -> u8 {
    // ProtoFact == 0 so it sorts before all special tags, matching the
    // derived constructor order. Special tags follow Theory/Model/Fact.hs:139-147.
    match f.name.as_str() {
        "Fr" => 1,   // FreshFact
        "Out" => 2,  // OutFact
        "In" => 3,   // InFact
        "KU" => 4,   // KUFact
        "KD" => 5,   // KDFact
        "Ded" => 6,  // DedFact
        "Term" => 7, // TermFact (internal; never parsed, but mapped for completeness)
        _ => 0,      // ProtoFact (incl. "K")
    }
}

pub fn cmp_fact(a: &GFact, b: &GFact) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    // `compare tag tag'`: first by FactTag constructor class.
    let (ca, cb) = (fact_tag_class(a), fact_tag_class(b));
    let tag_ord = ca.cmp(&cb).then_with(|| {
        if ca == 0 {
            // Both ProtoFact: derived Ord compares the inner triple
            // `(Multiplicity, String, Int)` = (multiplicity, name, arity).
            // Persistent < Linear: persistent==true must sort first, so
            // compare `b.persistent` against `a.persistent` to reverse
            // `bool`'s false<true ordering.
            b.persistent
                .cmp(&a.persistent)
                .then_with(|| a.name.cmp(&b.name))
                .then_with(|| a.args.len().cmp(&b.args.len()))
        } else {
            // Both the same special tag: nullary constructors compare
            // equal at the tag level (no inner fields).
            Ordering::Equal
        }
    });
    // `<> compare ts ts'`: tie-break on the term list.
    tag_ord.then_with(|| cmp_slice(&a.args, &b.args, cmp_term))
}

/// HS-faithful Guarded type. Mirrors `Theory.Constraint.System.Guarded.Guarded`.
///
/// Atoms use `GAtom` (which is `Atom (VTerm c (BVar v))` in HS), so a
/// variable leaf inside an atom is either `Bound(n)` (DeBruijn index into
/// the enclosing binder list) or `Free(LVar)`. Bindings carry only name +
/// sort — DeBruijn position determines identity.
///
/// `Hash` is derived alongside the derived `PartialEq` (equal values hash
/// equal), enabling the implied-formula dedup's `fx_hash_one` prefilter.
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Guarded {
    /// One atomic predicate (may contain Bound vars only when nested under
    /// a sufficient number of `GGuarded` binders).
    Atom(GAtom),
    /// Disjunction of guarded sub-formulas.
    Disj(std::sync::Arc<[Guarded]>),
    /// Conjunction of guarded sub-formulas.
    Conj(std::sync::Arc<[Guarded]>),
    /// `qua xs. as ⇒ gf` (when `qua = All`) or `qua xs. as ∧ gf`
    /// (when `qua = Ex`). The `as` are the *guard* atoms, all
    /// quantified `xs` must be bound by them.
    GGuarded {
        qua: Quant,
        vars: std::sync::Arc<[GBinding]>,
        guards: std::sync::Arc<[GAtom]>,
        body: std::sync::Arc<Guarded>,
    },
}

/// Shared empty child slice for the boolean atoms `gtrue`/`gfalse` — cloning
/// it is a refcount bump rather than a per-call allocation.  The empty `Conj`
/// (`gtrue`) and empty `Disj` (`gfalse`) each clone their own static so the two
/// hot constants never contend on a single cache line.
static EMPTY_CONJ: std::sync::OnceLock<std::sync::Arc<[Guarded]>> = std::sync::OnceLock::new();
static EMPTY_DISJ: std::sync::OnceLock<std::sync::Arc<[Guarded]>> = std::sync::OnceLock::new();

/// Boolean atom helper.
pub fn gtrue() -> Guarded {
    Guarded::Conj(
        EMPTY_CONJ
            .get_or_init(|| std::sync::Arc::from(Vec::new()))
            .clone(),
    )
}
pub fn gfalse() -> Guarded {
    Guarded::Disj(
        EMPTY_DISJ
            .get_or_init(|| std::sync::Arc::from(Vec::new()))
            .clone(),
    )
}
pub fn gtf(b: bool) -> Guarded {
    if b {
        gtrue()
    } else {
        gfalse()
    }
}

/// Content-membership test for the `Arc`-wrapped formula stores
/// (`System::formulas` / `solved_formulas` / `lemmas` /
/// `sources_lemma_universals`).  The per-element `Arc` is transparent:
/// the comparison dereferences to the underlying `Guarded` value (via
/// `Arc`'s `Deref`), so this is identical to a plain
/// `Vec<Guarded>::contains` — content equality, never pointer identity.
pub fn stores_contains(store: &[std::sync::Arc<Guarded>], g: &Guarded) -> bool {
    store.iter().any(|f| f.as_ref() == g)
}

/// `True` iff the guarded formula can be reduced by the constraint
/// solver's `insertFormula` decomposition rules. Mirrors
/// `Theory.Constraint.Solver.Reduction.reducibleFormula`.
pub fn reducible_formula(fm: &Guarded) -> bool {
    match fm {
        Guarded::Atom(_) => true,
        Guarded::Conj(_) => true,
        Guarded::GGuarded { qua: Quant::Ex, .. } => true,
        Guarded::GGuarded {
            qua: Quant::All,
            vars,
            guards,
            body,
        } if vars.is_empty() && guards.len() == 1 => {
            let body_is_false = matches!(&**body, Guarded::Disj(v) if v.is_empty());
            body_is_false
                && matches!(
                    &guards[0],
                    GAtom::Less(_, _) | GAtom::Subterm(_, _) | GAtom::Last(_),
                )
        }
        _ => false,
    }
}

/// Smart `Conj` — recursively flatten nested `Conj`s and short-circuit.
/// HS-faithful: mirrors Haskell `gconj` (Guarded.hs), whose helper
/// `flatten (GConj conj) = concatMap flatten $ getConj conj`
/// recursively unwraps every level of nested conjunction.  Must flatten
/// EVERY level (not just one): a binary-And chain parsed as
/// `Conj(Conj(Conj(a, b), c), d)` must collapse to a single 4-item Conj,
/// else the runtime sees a 2-item Conj and mismatches HS's
/// case-enumeration shape.
pub fn gconj(items: Vec<Guarded>) -> Guarded {
    fn flatten(item: Guarded, out: &mut Vec<Guarded>) -> bool {
        // returns true if gfalse encountered (absorbs)
        match item {
            Guarded::Conj(inner) => {
                for x in inner.iter() {
                    if flatten(x.clone(), out) {
                        return true;
                    }
                }
                false
            }
            x if x == gfalse() => true,
            x => {
                out.push(x);
                false
            }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) {
            return gfalse();
        }
    }
    // HS-faithful: mirror `gconj`'s `nub` BEFORE the `[gf] -> gf`
    // singleton unwrap, so the result is a fixpoint of `gconj` itself:
    // `gconj [a, a]` must be `a`, not the non-normal singleton `Conj [a]`
    // that only a second application would unwrap.  `normalise_guarded_cow`
    // relies on this one-pass idempotence.
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) {
            deduped.push(x);
        }
    }
    if deduped.len() == 1 {
        return deduped.into_iter().next().unwrap();
    }
    Guarded::Conj(deduped.into())
}

/// Walk a guarded formula and replace atoms whose truth value the
/// caller's `valuation` returns `Some(_)`. Mirrors Haskell's
/// `Theory.Constraint.System.Guarded.simplifyGuardedOrReturn`.
///
/// Cases:
/// - `Atom a` becomes `gtrue`/`gfalse` if the valuation is decided;
///   otherwise unchanged.
/// - `Conj` / `Disj` recurse and re-build via `gconj` / `gdisj` so
///   short-circuits collapse the right way.
/// - `GGuarded(All, [], guards, body)`: if any guard is False the
///   whole universal is True; otherwise drop guards that evaluate to
///   True and keep only the unknown ones, then recurse on the body.
/// - Guarded quantifiers with bound vars are left intact — the body
///   gets simplified once the quantifier is gone (matches Haskell).
pub fn simplify_guarded_with(
    fm: &Guarded,
    valuation: &dyn Fn(&p::Atom) -> Option<bool>,
) -> Guarded {
    // HS `simplifyGuardedOrReturn` calls `valuation =<< unbindAtom ato`,
    // which is Nothing whenever any Bound var is present in the atom.
    // We mirror by attempting GAtom→p::Atom conversion; on Bound, the
    // round-trip panics, so we use a safe variant.
    let eval = |a: &GAtom| -> Option<bool> { try_gatom_to_atom(a).and_then(|pa| valuation(&pa)) };
    match fm {
        Guarded::Atom(a) => match eval(a) {
            Some(true) => gtrue(),
            Some(false) => gfalse(),
            None => fm.clone(),
        },
        Guarded::Disj(items) => {
            let simplified: Vec<_> = items
                .iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gdisj(simplified)
        }
        Guarded::Conj(items) => {
            let simplified: Vec<_> = items
                .iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gconj(simplified)
        }
        Guarded::GGuarded {
            qua: Quant::All,
            vars,
            guards,
            body,
        } if vars.is_empty() => {
            let evals: Vec<Option<bool>> = guards.iter().map(eval).collect();
            // Any False guard → universal vacuously holds.
            if evals.iter().any(|v| v == &Some(false)) {
                return gtrue();
            }
            // Keep only the Unknown guards — True guards are vacuous.
            let kept: Vec<GAtom> = guards
                .iter()
                .zip(&evals)
                .filter(|(_, v)| v.is_none())
                .map(|(a, _)| a.clone())
                .collect();
            let body_s = simplify_guarded_with(body, valuation);
            // HS-faithful: `simp` builds the universal via `gall [] (...) (simp
            // gf)` (Guarded.hs:665-698, see line 689).  `gall` collapses to the body when the
            // kept guards are empty AND collapses the whole universal to
            // `gtrue` when the simplified body is `gtrue` (Guarded.hs:449-453, see line 452),
            // regardless of whether guards remain.  Building `GGuarded`
            // directly would leave a non-canonical `GGuarded{All,[],kept,
            // gtrue}` where Haskell produces `gtrue`.
            gall(vars.to_vec(), kept, body_s)
        }
        // Quantifiers with bound vars stay as-is — Haskell delays
        // simplification past the binder.
        Guarded::GGuarded { .. } => fm.clone(),
    }
}

/// Convert `GAtom` to `p::Atom` if no Bound vars are present, else None.
/// HS `unbindAtom`.
pub fn try_gatom_to_atom(a: &GAtom) -> Option<p::Atom> {
    Some(match a {
        GAtom::Eq(s, t) => p::Atom::Eq(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::Less(s, t) => p::Atom::Less(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::LessMset(s, t) => p::Atom::LessMset(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::Subterm(s, t) => p::Atom::Subterm(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::Action(f, t) => p::Atom::Action(try_gfact_to_fact(f)?, try_gterm_to_term(t)?),
        GAtom::Last(t) => p::Atom::Last(try_gterm_to_term(t)?),
        GAtom::Pred(f) => p::Atom::Pred(try_gfact_to_fact(f)?),
    })
}

/// Convert `GTerm` to `p::Term` if no Bound vars are present, else None.
pub fn try_gterm_to_term(t: &GTerm) -> Option<p::Term> {
    Some(match t {
        GTerm::Var(BVar::Free(v)) => p::Term::Var(v.clone()),
        GTerm::Var(BVar::Bound(_)) => return None,
        GTerm::PubLit(s) => p::Term::PubLit(s.clone()),
        GTerm::FreshLit(s) => p::Term::FreshLit(s.clone()),
        GTerm::NatLit(s) => p::Term::NatLit(s.clone()),
        GTerm::Number(n) => p::Term::Number(*n),
        GTerm::NumberOne => p::Term::NumberOne,
        GTerm::NatOne => p::Term::NatOne,
        GTerm::DhNeutral => p::Term::DhNeutral,
        GTerm::App(n, args) => {
            let mut acc = Vec::with_capacity(args.len());
            for a in args.iter() {
                acc.push(try_gterm_to_term(a)?);
            }
            p::Term::App(n.to_string(), acc)
        }
        GTerm::AlgApp(n, a, b) => p::Term::AlgApp(
            n.to_string(),
            Box::new(try_gterm_to_term(a)?),
            Box::new(try_gterm_to_term(b)?),
        ),
        GTerm::Pair(items) => {
            let mut acc = Vec::with_capacity(items.len());
            for it in items.iter() {
                acc.push(try_gterm_to_term(it)?);
            }
            p::Term::Pair(acc)
        }
        GTerm::Diff(a, b) => p::Term::Diff(
            Box::new(try_gterm_to_term(a)?),
            Box::new(try_gterm_to_term(b)?),
        ),
        GTerm::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(try_gterm_to_term(a)?),
            Box::new(try_gterm_to_term(b)?),
        ),
        GTerm::PatMatch(t) => p::Term::PatMatch(Box::new(try_gterm_to_term(t)?)),
    })
}

/// Convert `GFact` to `p::Fact` if no Bound vars are present, else None.
pub fn try_gfact_to_fact(f: &GFact) -> Option<p::Fact> {
    let mut args = Vec::with_capacity(f.args.len());
    for a in f.args.iter() {
        args.push(try_gterm_to_term(a)?);
    }
    Some(p::Fact {
        persistent: f.persistent,
        name: f.name.clone(),
        args,
        annotations: f.annotations.clone(),
    })
}

/// Smart `Disj` — flatten one level, short-circuit on `gtrue`, drop
/// `gfalse` items.  Mirrors Haskell's `gdisj` which treats `Disj` as a
/// set semantically: True absorbs, False is the unit.  Without dropping
/// gfalse items, partial_atom_valuation can turn `Disj([Eq(j,i),
/// Less(i,j)])` into `Disj([gfalse, gfalse])` (when j<i is known via
/// the order graph) and we'd split a 2-case Disj goal whose branches
/// both close — Haskell collapses this to `gfalse` directly.
pub fn gdisj(items: Vec<Guarded>) -> Guarded {
    // Recursively flatten nested `Disj`s. HS-faithful: mirrors Haskell
    // `gdisj` (Guarded.hs:426-437) whose helper
    // `flatten (GDisj disj) = concatMap flatten $ getDisj disj`
    // recursively unwraps every level. Must flatten EVERY level (not just
    // one): a 5-way `∨` parsed as a binary `Or` chain
    // (`Disj(Disj(Disj(Disj(a, b), c), d), e)`) must collapse to a single
    // 5-alt Disj goal, else the runtime sees a 2-alt Disj and mismatches
    // the case-enumeration of skeleton proofs like YubiSecure
    // slightly_weaker_invariant.
    fn flatten(item: Guarded, out: &mut Vec<Guarded>) -> bool {
        // returns true if gtrue encountered (absorbs)
        match item {
            Guarded::Disj(inner) => {
                for x in inner.iter() {
                    if flatten(x.clone(), out) {
                        return true;
                    }
                }
                false
            }
            x if x == gtrue() => true,
            x if x == gfalse() => false,
            x => {
                out.push(x);
                false
            }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) {
            return gtrue();
        }
    }
    // HS-faithful: the `[gf] -> gf` singleton unwrap matches the FLATTENED,
    // non-nubbed list (Guarded.hs:426-437, see line 428); `nub` is applied only in the
    // otherwise branch (`GDisj $ Disj $ nub gfs`, Guarded.hs:426-437, see line 434).  So a
    // flattened list like `[a,a]` is not a singleton and yields
    // `Disj (nub [a,a]) = Disj [a]`, NOT bare `a`.  (Note: this `out`
    // already has `gfalse` items dropped — see flatten above — so the
    // empty case below collapses an all-`gfalse` disjunction to `gfalse`.)
    if out.len() == 1 {
        return out.into_iter().next().unwrap();
    }
    // Mirror Haskell `gdisj`'s `nub gfs` (Guarded.hs:426-437, see line 434).
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) {
            deduped.push(x);
        }
    }
    if deduped.is_empty() {
        gfalse()
    } else {
        Guarded::Disj(deduped.into())
    }
}

/// Smart `GGuarded(Ex, ...)` — direct port of Haskell's `gex`:
/// ```text
///   gex []  as  gf                = gconj (map GAto as ++ [gf])
///   gex _   _   gf | gf == gfalse = gfalse
///   gex ss  as  gf                = GGuarded Ex ss as gf
/// ```
pub fn gex(vars: Vec<GBinding>, guards: Vec<GAtom>, body: Guarded) -> Guarded {
    if vars.is_empty() {
        let mut items: Vec<Guarded> = guards.into_iter().map(Guarded::Atom).collect();
        items.push(body);
        return gconj(items);
    }
    if body == gfalse() {
        return gfalse();
    }
    Guarded::GGuarded {
        qua: Quant::Ex,
        vars: vars.into(),
        guards: guards.into(),
        body: std::sync::Arc::new(body),
    }
}

/// Smart `GGuarded(All, ...)` — direct port of Haskell's `gall`:
/// ```text
///   gall _   []   gf              = gf
///   gall _   _    gf | gf == gtrue = gtrue
///   gall ss  atos gf              = GGuarded All ss atos gf
/// ```
pub fn gall(vars: Vec<GBinding>, guards: Vec<GAtom>, body: Guarded) -> Guarded {
    if guards.is_empty() {
        return body;
    }
    if body == gtrue() {
        return gtrue();
    }
    Guarded::GGuarded {
        qua: Quant::All,
        vars: vars.into(),
        guards: guards.into(),
        body: std::sync::Arc::new(body),
    }
}

// =============================================================================
// Errors
// =============================================================================

#[derive(Debug, Clone)]
pub struct GuardError {
    pub message: String,
    /// The sub-formula at the point of failure — HS's `f0` in
    /// `convert polarity f0@(Qua qua0 _ _)` (Guarded.hs:499), the innermost
    /// quantifier whose guard check failed.  Callers quote it above the
    /// whole formula, as HS's `ppError` does (Guarded.hs:477-479):
    ///   ```text
    ///   <error_text>
    ///     "<sub_formula>"
    ///   in the formula
    ///     "<full_formula>"
    ///   ```
    /// Its enclosing binders are already opened, so it prints on its own
    /// through [`crate::pretty_formula::pretty_lnformula`].  `None` for a
    /// failure outside a quantifier.
    pub subject_formula: Option<crate::formula::LNFormula>,
}

impl std::fmt::Display for GuardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for GuardError {}

fn err(msg: impl Into<String>) -> GuardError {
    GuardError {
        message: msg.into(),
        subject_formula: None,
    }
}

/// HS `bvarToLVar` (Guarded.hs:322-327): read an atom of a locally-nameless
/// formula whose binders are all opened as an atom over plain `LVar`s.  A
/// surviving `Bound` index is HS's `boundError`.
pub fn bvar_to_lvar(a: &Atom<BLNTerm>) -> Atom<LNTerm> {
    use tamarin_term::lterm::BVar;
    map_atom(a, &mut |t| {
        map_lits(t, &mut |l| match l {
            Lit::Con(c) => Lit::Con(*c),
            Lit::Var(BVar::Free(v)) => Lit::Var(*v),
            Lit::Var(BVar::Bound(i)) => panic!("bvarToLVar: left-over bound variable '{i}'"),
        })
    })
}

/// Returns `true` if the formula is "safety": closed (no free vars)
/// and contains no existential quantifier in its guarded form.
pub fn is_safety_formula(g: &Guarded) -> bool {
    fn no_existential(g: &Guarded) -> bool {
        match g {
            Guarded::Atom(_) => true,
            Guarded::GGuarded { qua: Quant::Ex, .. } => false,
            Guarded::GGuarded {
                qua: Quant::All,
                body,
                ..
            } => no_existential(body),
            Guarded::Disj(inner) => inner.iter().all(no_existential),
            Guarded::Conj(inner) => inner.iter().all(no_existential),
        }
    }
    free_vars(g).is_empty() && no_existential(g)
}

/// Compute the set of free (un-quantified) variables in a guarded formula.
///
/// With DeBruijn bindings, Bound vars don't appear in this set — they have
/// no name (their "name" is positional).  We collect VarSpec names from
/// every `BVar::Free` leaf.
pub fn free_vars(g: &Guarded) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for_each_free_var_in_guarded(g, &mut |v| {
        out.insert(v.name.clone());
    });
    out
}

/// Full identity of a logical variable, as `(name, idx, sort)`.
///
/// HS `remainingUnguarded` (Guarded.hs:523-533) works over `[LVar]` and
/// `frees`, so variables are compared by
/// HS `instance Eq LVar` (LTerm.hs:541-542) — `i1 == i2 && s1 == s2 && n1 ==
/// n2`.  A binder `x.1` is therefore a DIFFERENT variable from an enclosing
/// `x`, and `#x` a different variable from `x`.
type VarKey = (String, u64, LSort);

/// Build the [`VarKey`] of a variable occurrence carrying `sort`.
fn var_key(name: &str, idx: u64, sort: LSort) -> VarKey {
    (name.to_string(), idx, sort)
}

/// Collect the identity of every variable leaf in a parser-AST term.  Used
/// by `remaining_unguarded` for the pre-DeBruijn unguarded-variable check.
fn term_var_keys(t: &p::Term, out: &mut Vec<VarKey>) {
    match t {
        p::Term::Var(v) => out.push(var_key(&v.name, v.idx, v.sort)),
        p::Term::App(_, args) | p::Term::Pair(args) => {
            for a in args {
                term_var_keys(a, out);
            }
        }
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            term_var_keys(a, out);
            term_var_keys(b, out);
        }
        p::Term::PatMatch(inner) => term_var_keys(inner, out),
        _ => {}
    }
}

// =============================================================================
// Walking Guarded with DeBruijn-aware substitution
// =============================================================================

/// Port of HS `mapGuardedAtoms :: (Integer -> a -> b) -> LGuarded a ->
/// LGuarded b`: the single depth-tracking recursor shared by every eager
/// per-atom rewrite over `Guarded`.  `f` receives the scope depth (number
/// of binders crossed) and each atom; the rebuilt tree preserves structure,
/// quantifier blocks, and traversal order.  Guards of a `GGuarded` are
/// mapped — and the body recursed — at `depth + vars.len()`, so an atom
/// under `n` binders is always handed `depth == n`.
fn map_guarded_atoms<F: FnMut(u32, &GAtom) -> GAtom>(g: &Guarded, f: &mut F) -> Guarded {
    fn rec<F: FnMut(u32, &GAtom) -> GAtom>(g: &Guarded, depth: u32, f: &mut F) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(f(depth, a)),
            Guarded::Disj(items) => Guarded::Disj(items.iter().map(|i| rec(i, depth, f)).collect()),
            Guarded::Conj(items) => Guarded::Conj(items.iter().map(|i| rec(i, depth, f)).collect()),
            Guarded::GGuarded {
                qua,
                vars,
                guards,
                body,
            } => {
                let new_depth = depth + vars.len() as u32;
                Guarded::GGuarded {
                    qua: *qua,
                    vars: vars.clone(),
                    guards: guards.iter().map(|a| f(new_depth, a)).collect(),
                    body: std::sync::Arc::new(rec(body, new_depth, f)),
                }
            }
        }
    }
    rec(g, 0, f)
}

/// Mirror HS `substFree :: [(LVar, Integer)] -> LGuarded c -> LGuarded c`.
///
/// Walks the Guarded tracking scope depth (number of binders crossed).
/// At each atom, replaces each `Free(v)` matching some `(v, db)` in `s`
/// with `Bound(db + depth)`.
pub fn subst_free_guarded(g: &Guarded, s: &[(p::VarSpec, u32)]) -> Guarded {
    map_guarded_atoms(g, &mut |d, a| subst_free_atom_at_depth(a, s, d))
}

/// Rebuild a guarded formula bottom-up through the `gconj`/`gdisj` smart
/// constructors, restoring the normal form that formula conversion
/// (`convert`) establishes at creation: flattened, duplicate-free
/// connectives.  Port of HS `normaliseGuarded` (150f5eba).
/// NOTE: disjunctions are normalised CONSTRUCTOR-PRESERVING at every
/// level (`normalise_disj_list`), not via the full `gdisj`: a singleton
/// disjunction wrapping a conjunction is load-bearing for the S_∀
/// saturation dedup — `insert_formula` STORES disjunctions (formula +
/// `Goal::Disj` twin) but DECOMPOSES bare conjunctions without storing
/// them, so unwrapping the singleton turns a storable, dedupable derived
/// instance into one that re-fires every simplifier iteration (livelock
/// on ake/bilinear/TAK1_eCK_like.spthy).  Conjunctions use the full
/// `gconj` (their singleton unwrap is harmless because conjunctions are
/// decomposed on insertion anyway); this requires `gconj` to be
/// idempotent — see the note on `gconj`.
///
/// Copy-on-write: returns `None` when normalisation leaves `g` structurally
/// unchanged (so an owning caller can reuse `g` by move with zero
/// allocation), `Some(rebuilt)` otherwise.  Mirrors the `subst_guarded_cow` /
/// `cac_rec_guarded_cow` convention (recursion returns `None` when all
/// children are unchanged).
pub fn normalise_guarded_cow(g: &Guarded) -> Option<Guarded> {
    match g {
        // An atom carries no connectives to flatten → always unchanged.
        Guarded::Atom(_) => None,
        Guarded::Disj(items) => normalise_disj_list_cow(items).map(|v| Guarded::Disj(v.into())),
        Guarded::Conj(items) => {
            // Normalise children first (COW), then re-run the `gconj`
            // smart-constructor step (flatten nested Conj / absorb gfalse /
            // dedup / singleton-unwrap).  When no child changed AND `gconj`
            // is a structural no-op on the (already-normalised) children, the
            // whole node is unchanged.  Otherwise the rebuild is exactly
            // `gconj(children)`.
            let mapped = cow_map_vec(items, normalise_guarded_cow);
            let children: &[Guarded] = mapped.as_deref().unwrap_or(&items[..]);
            if mapped.is_none() && gconj_is_structural_noop(children) {
                None
            } else {
                Some(gconj(children.to_vec()))
            }
        }
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } =>
        // Only `body` can change; qua/vars/guards are cloned verbatim.
        {
            normalise_guarded_cow(body).map(|b| Guarded::GGuarded {
                qua: *qua,
                vars: vars.clone(),
                guards: guards.clone(),
                body: std::sync::Arc::new(b),
            })
        }
    }
}

/// `gconj(items) == Guarded::Conj(items)` — i.e. the `gconj` smart
/// constructor is a structural no-op on this (already child-normalised)
/// list.  True iff none of `gconj`'s transformations fire: no nested-`Conj`
/// child to flatten (including an empty `Conj` = `gtrue`, which `gconj`
/// drops), no `gfalse` (`Disj([])`) child to absorb, no duplicate to `nub`,
/// and length != 1 (which would singleton-unwrap).  Keep in exact lock-step
/// with `gconj`.
fn gconj_is_structural_noop(items: &[Guarded]) -> bool {
    if items.len() == 1 {
        return false;
    }
    for (i, x) in items.iter().enumerate() {
        if matches!(x, Guarded::Conj(_)) {
            return false; // flatten (incl. empty Conj = gtrue drop)
        }
        if matches!(x, Guarded::Disj(v) if v.is_empty()) {
            return false; // gfalse absorption
        }
        if items[..i].contains(x) {
            return false; // nub drops a duplicate
        }
    }
    true
}

/// Normalise the disjunct list of a stored disjunction WITHOUT changing
/// its constructor: each disjunct normalised, nested disjunctions
/// flattened one level, duplicates dropped — but no singleton unwrap and
/// no truth-value absorption, so a `Guarded::Disj` formula and its
/// `Goal::Disj` twin (same payload, different wrapper) stay in LOCKSTEP.
/// Port of HS `normaliseDisjList` (150f5eba); see that commit for why
/// full `gdisj` here desynchronises the twin stores (gcm livelock).
pub fn normalise_disj_list(items: &[Guarded]) -> Vec<Guarded> {
    normalise_disj_list_cow(items).unwrap_or_else(|| items.to_vec())
}

/// Copy-on-write variant of [`normalise_disj_list`]: `None` when the
/// constructor-preserving normalisation leaves the disjunct list unchanged
/// (every disjunct normalises in place, none is a nested `Disj` to flatten,
/// no duplicate to drop), `Some(rebuilt)` otherwise.  BYTE-IDENTICAL to
/// `normalise_disj_list(items)` in the `Some` case.
fn normalise_disj_list_cow(items: &[Guarded]) -> Option<Vec<Guarded>> {
    // Normalise each disjunct (COW); `children` is the normalised list — the
    // originals when `mapped` is `None` (all disjuncts unchanged).
    let mapped = cow_map_vec(items, normalise_guarded_cow);
    let children: &[Guarded] = mapped.as_deref().unwrap_or(items);
    if mapped.is_none() && disj_flatten_is_structural_noop(children) {
        None
    } else {
        Some(flatten_dedup_disj(children))
    }
}

/// `flatten_dedup_disj(items) == items` — the constructor-preserving disjunct
/// normalisation (one-level flatten of a nested `Disj`, then `nub`) is a
/// no-op.  True iff no disjunct is itself a `Disj` (any `Disj` has its wrapper
/// spliced away) and there is no duplicate.  Lock-step with
/// `flatten_dedup_disj`.
fn disj_flatten_is_structural_noop(items: &[Guarded]) -> bool {
    for (i, x) in items.iter().enumerate() {
        if matches!(x, Guarded::Disj(_)) {
            return false; // one-level flatten removes the Disj wrapper
        }
        if items[..i].contains(x) {
            return false; // nub drops a duplicate
        }
    }
    true
}

/// One-level flatten of nested `Disj`s + duplicate drop over an
/// already-normalised disjunct list.  This is the outer-loop body of
/// `normalise_disj_list` factored out so it runs on the COW-normalised
/// children; BYTE-IDENTICAL to that original loop (same push/dedup order).
fn flatten_dedup_disj(children: &[Guarded]) -> Vec<Guarded> {
    fn push(g: Guarded, out: &mut Vec<Guarded>) {
        if !out.contains(&g) {
            out.push(g);
        }
    }
    let mut out: Vec<Guarded> = Vec::new();
    for it in children {
        match it {
            Guarded::Disj(ds) => {
                for d in ds.iter() {
                    push(d.clone(), &mut out);
                }
            }
            g => push(g.clone(), &mut out),
        }
    }
    out
}

/// Normalise a formula for storage in the constraint system: full
/// smart-constructor normal form, except that a TOP-LEVEL disjunction
/// keeps its `Disj` constructor (via the constructor-preserving
/// `normalise_disj_list_cow`) so it stays in lockstep with its `Goal::Disj`
/// twin.  Port of HS `normaliseStoredFormula` (150f5eba).
///
/// Copy-on-write: `None` when unchanged, `Some(rebuilt)` otherwise.
pub fn normalise_stored_formula_cow(g: &Guarded) -> Option<Guarded> {
    match g {
        Guarded::Disj(items) => normalise_disj_list_cow(items).map(|v| Guarded::Disj(v.into())),
        _ => normalise_guarded_cow(g),
    }
}

/// Owned fast path for [`normalise_stored_formula_cow`]: consumes `g`,
/// returning it by MOVE (zero allocation) when normalisation is a no-op, else
/// the rebuilt tree.  For callers that own their input and immediately
/// reassign it.
pub fn normalise_stored_formula_owned(g: Guarded) -> Guarded {
    match normalise_stored_formula_cow(&g) {
        Some(n) => n,
        None => g,
    }
}

/// Mirror HS `substBound :: [(Integer, LVar)] -> LGuarded c -> LGuarded c`.
///
/// Walks the Guarded tracking scope depth.  At each atom, replaces each
/// `Bound(n)` matching some `(i, v)` in `s` (where `n = i + depth`) with
/// `Free(v)`.
pub fn subst_bound_guarded(g: &Guarded, s: &[(u32, p::VarSpec)]) -> Guarded {
    map_guarded_atoms(g, &mut |d, a| subst_bound_atom_at_depth(a, s, d))
}

/// Mirror HS `closeGuarded :: Quantifier -> [LVar] -> [Atom] -> LGuarded -> LGuarded`.
///
/// Takes named LVars `xs`, parser-AST atoms `atoms`, and an already-built
/// body `gf`.  Closes the binder:
///   - Lifts each atom from `p::Atom` to `GAtom` (initially all Free).
///   - Substitutes every Free LVar matching `xs[i]` with `Bound(k-1-i)` in
///     the atoms (depth 0) and the body (depth-tracked through nested
///     binders).
///   - Strips the binder list down to `(name, sort)` pairs (`GBinding`).
///
/// HS:
/// ```text
///   closeGuarded qua vs as gf = ((case qua of Ex -> gex; All -> gall) vs' as' gf'
///     where  as'   = map (substFreeAtom s . fmap (fmapTerm (fmap Free))) as
///            gf'   = substFree s gf
///            s     = zip (reverse vs) [0..]
///            vs'   = map (lvarName &&& lvarSort) vs
/// ```
pub fn close_guarded(
    qua: Quant,
    xs: Vec<p::VarSpec>,
    atoms: Vec<p::Atom>,
    body: Guarded,
) -> Guarded {
    let close_s = close_subst(&xs);
    let new_guards: Vec<GAtom> = atoms
        .iter()
        .map(|a| {
            let ga = atom_to_gatom_free(a);
            subst_free_atom_at_depth(&ga, &close_s, 0)
        })
        .collect();
    let new_body = subst_free_guarded(&body, &close_s);
    let vs: Vec<GBinding> = xs.iter().map(lvar_to_binding).collect();
    match qua {
        Quant::Ex => gex(vs, new_guards, new_body),
        Quant::All => gall(vs, new_guards, new_body),
    }
}

/// Compute which of `xs` are NOT bound by any of `atoms`, as POSITIONS in
/// `xs`. Mirrors Haskell's `remainingUnguarded` (Guarded.hs:523-533), whose
/// `ug0 \\ frees ...` likewise preserves the prefix order of the survivors.
/// Positions rather than variables so the caller can name each survivor from
/// the parallel freshened prefix (see [`unguarded_error`]).
///
/// Variables are tracked by full [`VarKey`] identity, not by name: HS's
/// working set is a `[LVar]` and `\\`/`intersect` use `Eq LVar`
/// (name + sort + idx).  So under `All x. ... ==> All x.1 z. <x.1,z> = x`,
/// the guard covers the binders `x.1` and `z` even though its right-hand
/// side mentions the *outer* `x`, which is a different variable.
fn remaining_unguarded(xs: &[p::VarSpec], atoms: &[p::Atom]) -> Vec<usize> {
    let mut sorted_atoms: Vec<&p::Atom> = atoms.iter().collect();
    // Action atoms first, then equalities.
    sorted_atoms.sort_by_key(|a| match a {
        p::Atom::Action(_, _) => 0,
        _ => 1,
    });
    let mut unguarded: BTreeSet<VarKey> =
        xs.iter().map(|v| var_key(&v.name, v.idx, v.sort)).collect();
    for atom in &sorted_atoms {
        match atom {
            // HS `frees (a, fa)` over `GAction a fa`: every variable of the
            // fact and of the timepoint.
            p::Atom::Action(fact, t) => {
                let mut frees = Vec::new();
                for arg in &fact.args {
                    term_var_keys(arg, &mut frees);
                }
                term_var_keys(t, &mut frees);
                for k in frees {
                    unguarded.remove(&k);
                }
            }
            p::Atom::Eq(s, t) => {
                let mut sv = Vec::new();
                let mut tv = Vec::new();
                term_var_keys(s, &mut sv);
                term_var_keys(t, &mut tv);
                let s_covered = sv.iter().all(|k| !unguarded.contains(k));
                let t_covered = tv.iter().all(|k| !unguarded.contains(k));
                if s_covered {
                    for k in tv {
                        unguarded.remove(&k);
                    }
                } else if t_covered {
                    for k in sv {
                        unguarded.remove(&k);
                    }
                }
            }
            _ => {}
        }
    }
    xs.iter()
        .enumerate()
        .filter(|(_, v)| unguarded.contains(&var_key(&v.name, v.idx, v.sort)))
        .map(|(i, _)| i)
        .collect()
}

/// Render HS `noUnguardedVars` (Guarded.hs:507-514) for the survivors at
/// `positions` of the quantifier prefix.  The names come from `freshened` —
/// the prefix as `openFormulaPrefix` renamed it — so a binder shadowing an
/// already-opened one is reported as `x.1`, not `x`.
fn unguarded_error(positions: &[usize], freshened: &[p::VarSpec]) -> GuardError {
    // HS: `map (quotes . text . show) unguarded` (Guarded.hs:507-514, see line 511) over
    // `[LVar]`.  Each LVar is rendered by the EXPLICIT `instance Show LVar`
    // (LTerm.hs:550-557): `show (LVar v s i) = sortPrefix s ++ body`, where
    // `sortPrefix` (LTerm.hs:193-199) is "" (Msg) / "~" (Fresh) / "$" (Pub)
    // / "#" (Node) / "%" (Nat), and `body` is `v` when `i == 0` else
    // `v ++ "." ++ show i`.  `quotes` then single-quotes the result, so the
    // rendered output is e.g. `'#i'` or `'x.5'` — NOT a bare `'name'`.
    let show_lvar = |v: &p::VarSpec| -> String {
        let prefix = sort_prefix(v.sort);
        let body = if v.name.is_empty() {
            v.idx.to_string()
        } else if v.idx == 0 {
            v.name.clone()
        } else {
            format!("{}.{}", v.name, v.idx)
        };
        format!("'{}{}'", prefix, body)
    };
    let names: Vec<String> = positions
        .iter()
        .map(|&i| show_lvar(&freshened[i]))
        .collect();
    err(format!(
        "unguarded variable(s) {} in the subformula",
        names.join(", ")
    ))
}

// =============================================================================
// Conversion to a guarded formula
// =============================================================================

/// HS `formulaToGuarded` (Guarded.hs:471-479): the whole traversal runs
/// inside one `Precise.FreshT` seeded with `avoidPrecise fmOrig`, so every
/// quantifier prefix it opens draws its binders from a single supply.
///
/// The atoms are lowered into the `GTerm` world one at a time
/// ([`crate::guarded_types::blnatom_to_gatom`]).  `convert` descends
/// through every quantifier before it meets an atom, so each atom is
/// all-`Free` when it is lowered, under the binders `open_formula_prefix`
/// drew and with its AC arguments sorted under them: opening substitutes each
/// drawn `LVar` through `map_lits` as HS's `openFormula` does through
/// `mapLits`, whose `fAppAC` sorts (Theory/Model/Formula.hs:277-284,
/// :288-291, Term/Term/Raw.hs:118-129), and the lowering's
/// `canonicalize_ac_in_atom` re-establishes the same order over the parser
/// AST ([`cmp_varspec`] is `Ord LVar`).  `Ord LVar` reads the index first
/// (LTerm.hs:545-548), so a binder drawn at a non-zero index sorts where its
/// name alone would not put it — the argument order of a `++` chain under two
/// sibling prefixes that bind one name follows the second prefix's `b3.1`.
/// That order reaches the solver through the derived `PartialEq`/`Hash` on
/// [`Guarded`], never the printed formula, which re-sorts AC arguments under
/// the names it opens the binders with (`sort_ac_args_for_display`,
/// `pretty_formula.rs`).
pub fn formula_to_guarded(f: &crate::formula::LNFormula) -> Result<Guarded, GuardError> {
    let mut fresh = crate::formula::avoid_precise_lnformula(f);
    convert(false, f, &mut fresh)
}

/// [`formula_to_guarded`] on a parser-AST formula, closed by
/// [`crate::formula::from_parser`] and stripped of its sugar by
/// [`crate::formula::to_lnformula`].  Both steps report a [`GuardError`], so
/// a caller that cannot build the internal formula still renders the same
/// block a guardedness failure renders.
///
/// Callers: the `--parse-only` open renderers (`pretty_theory.rs`,
/// `is_safety_formula_parsed` among them), and the disjunction arm of
/// `elaborate::goal_from_parsed`, which reads a stored goal's disjuncts
/// against the theory's signature.
pub fn formula_to_guarded_parsed(
    f: &p::Formula,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Result<Guarded, GuardError> {
    let syn = crate::formula::from_parser(f, sig).map_err(|e| err(e.message))?;
    let plain = crate::formula::to_lnformula(&syn).ok_or_else(|| err("unexpanded predicate"))?;
    formula_to_guarded(&plain)
}

/// The binder `close_guarded` and `remaining_unguarded` match on, as
/// [`crate::pretty_theory::lnterm_to_parser`] writes a variable leaf.
fn lvar_to_varspec(v: &tamarin_term::lterm::LVar) -> p::VarSpec {
    p::VarSpec {
        name: v.name.to_string(),
        idx: v.idx,
        sort: v.sort,
        typ: None,
    }
}

/// HS `convert` (Guarded.hs:481-505,565-566).  `polarity` is the implicit
/// negation the conversion carries: at `True` the guarded formula returned
/// is equivalent to the negation of `f`.
fn convert(
    polarity: bool,
    f: &crate::formula::LNFormula,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    use crate::formula::{open_formula_prefix, Connective, ProtoFormula, Quantifier};
    match f {
        ProtoFormula::Tf(b) => Ok(gtf(polarity != *b)),
        ProtoFormula::Atom(a) => {
            let ga = crate::guarded_types::blnatom_to_gatom(a);
            if polarity {
                Ok(gnot_atom(&ga))
            } else {
                Ok(Guarded::Atom(ga))
            }
        }
        ProtoFormula::Not(g) => convert(!polarity, g, fresh),
        ProtoFormula::Conn(Connective::And, a, b) => {
            let sub = vec![convert(polarity, a, fresh)?, convert(polarity, b, fresh)?];
            Ok(if polarity { gdisj(sub) } else { gconj(sub) })
        }
        ProtoFormula::Conn(Connective::Or, a, b) => {
            let sub = vec![convert(polarity, a, fresh)?, convert(polarity, b, fresh)?];
            Ok(if polarity { gconj(sub) } else { gdisj(sub) })
        }
        ProtoFormula::Conn(Connective::Imp, a, b) => {
            // p ⇒ q is ¬p ∨ q.
            let nag = convert(!polarity, a, fresh)?;
            let cag = convert(polarity, b, fresh)?;
            let sub = vec![nag, cag];
            Ok(if polarity { gconj(sub) } else { gdisj(sub) })
        }
        // p ↔ q is (p ⇒ q) ∧ (q ⇒ p), and HS conjoins the two arms at both
        // polarities (Guarded.hs:565-566).
        ProtoFormula::Conn(Connective::Iff, a, b) => {
            let lhs = ProtoFormula::Conn(Connective::Imp, a.clone(), b.clone());
            let rhs = ProtoFormula::Conn(Connective::Imp, b.clone(), a.clone());
            Ok(gconj(vec![
                convert(polarity, &lhs, fresh)?,
                convert(polarity, &rhs, fresh)?,
            ]))
        }
        // The quantifier decides whether the body must be a top-level
        // implication (`convAll`) or a conjunction (`convEx`); the polarity
        // decides which quantifier the guarded formula carries and which
        // polarity the sub-formulas take (Guarded.hs:499-505).  The whole
        // prefix of like quantifiers is opened at once, each binder drawn
        // fresh and substituted into the body, so the guard check and the
        // diagnostic name the binders HS names.
        ProtoFormula::Qua(qua0, _, _) => {
            let (xs, _, body) = open_formula_prefix(f, fresh);
            let xs: Vec<p::VarSpec> = xs.iter().map(lvar_to_varspec).collect();
            let result = match qua0 {
                Quantifier::All => {
                    let out_qua = if polarity { Quant::Ex } else { Quant::All };
                    convert_all(&xs, &body, polarity, out_qua, fresh)
                }
                Quantifier::Ex => {
                    let out_qua = if polarity { Quant::All } else { Quant::Ex };
                    convert_ex(&xs, &body, polarity, out_qua, fresh)
                }
            };
            // Both throws of this arm quote `ppFormula f0`, the quantifier
            // sub-formula they were reached through (Guarded.hs:513, :562),
            // and the exception carries that quote out unchanged — so the
            // innermost quantifier is the one named, which the guard below
            // reproduces by setting the field once.
            result.map_err(|mut e| {
                if e.subject_formula.is_none() {
                    e.subject_formula = Some(f.clone());
                }
                e
            })
        }
    }
}

/// HS `convEx` (Guarded.hs:535-543): the body is a conjunction whose action
/// and equality atoms guard the prefix.
fn convert_ex(
    xs: &[p::VarSpec],
    body: &crate::formula::LNFormula,
    polarity: bool,
    out_qua: Quant,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    let (atoms, others) = split_conj_actions_eqs(body);
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded, xs));
    }
    let mut converted = Vec::with_capacity(others.len());
    for f in &others {
        converted.push(convert(polarity, f, fresh)?);
    }
    let body_guarded = if polarity {
        gdisj(converted)
    } else {
        gconj(converted)
    };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}

/// HS `convAll` (Guarded.hs:546-563): the body is an implication whose
/// antecedent guards the prefix.
fn convert_all(
    xs: &[p::VarSpec],
    body: &crate::formula::LNFormula,
    polarity: bool,
    out_qua: Quant,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    use crate::formula::{Connective, ProtoFormula};
    let ProtoFormula::Conn(Connective::Imp, ante, succ) = body else {
        return Err(err("universal quantifier without toplevel implication"));
    };
    let (atoms, ante_others) = split_conj_actions_eqs(ante);
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded, xs));
    }
    let mut sub = Vec::with_capacity(ante_others.len() + 1);
    for f in &ante_others {
        sub.push(convert(!polarity, f, fresh)?);
    }
    sub.push(convert(polarity, succ, fresh)?);
    let body_guarded = if polarity { gconj(sub) } else { gdisj(sub) };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}

/// HS `conjActionsEqs` (Guarded.hs:516-519): split a conjunction into the
/// action and equality atoms that can guard a binder and the sub-formulas
/// that cannot.  The atoms are lowered to the parser AST that
/// [`remaining_unguarded`] and [`close_guarded`] read
/// ([`crate::guarded_types::blnatom_to_parser`], HS's `bvarToLVar` plus the
/// projection).
fn split_conj_actions_eqs(
    f: &crate::formula::LNFormula,
) -> (Vec<p::Atom>, Vec<crate::formula::LNFormula>) {
    use crate::atom::ProtoAtom;
    use crate::formula::{Connective, ProtoFormula};
    fn rec(
        f: &crate::formula::LNFormula,
        atoms: &mut Vec<p::Atom>,
        others: &mut Vec<crate::formula::LNFormula>,
    ) {
        match f {
            ProtoFormula::Conn(Connective::And, a, b) => {
                rec(a, atoms, others);
                rec(b, atoms, others);
            }
            ProtoFormula::Atom(a @ (ProtoAtom::Action(_, _) | ProtoAtom::EqE(_, _))) => {
                atoms.push(crate::guarded_types::blnatom_to_parser(a))
            }
            other => others.push(other.clone()),
        }
    }
    let mut atoms = Vec::new();
    let mut others = Vec::new();
    rec(f, &mut atoms, &mut others);
    (atoms, others)
}

// =============================================================================
// Negate atoms (`gnotAtom` in Haskell)
// =============================================================================

/// `gnotAtom` — port of Haskell `Theory.Constraint.System.Guarded.gnotAtom`
/// (lib/theory/src/Theory/Constraint/System/Guarded.hs:410-412):
///
/// ```text
/// gnotAtom a = GGuarded All [] [a] gfalse
/// ```
///
/// Uniformly negates every atom by wrapping it in a universal
/// guarded ⊥: "for all traces in which `a` holds, ⊥" ≡ ¬a. This
/// is the right encoding for Less/Eq/Action/Last/Pred/Subterm alike,
/// independent of the term sort.
///
/// Do NOT decompose ¬EqE / ¬Less into `gdisj [Less, Less]`, nor encode
/// ¬Action as `gex [] [a] gfalse` (those belong only to
/// `toInductionHypothesis`, which DOES decompose Less for induction): the
/// disjunction form is semantically wrong for term-sort EqE since Less is
/// undefined between Msg/Fresh/Pub terms, and the Ex form is semantically
/// False rather than ¬Action.  See `Guarded.hs:410-412` vs
/// `Guarded.hs:618`.
fn gnot_atom(a: &GAtom) -> Guarded {
    Guarded::GGuarded {
        qua: Quant::All,
        vars: Vec::new().into(),
        guards: vec![a.clone()].into(),
        body: std::sync::Arc::new(gfalse()),
    }
}

// =============================================================================
// Top-level negation — port of Haskell's `gnot`.
// =============================================================================

/// Substitution mapping a free LVar (keyed by `(name, idx)`) to a
/// replacement parser-AST term.  Applied to `Guarded` formulas via
/// `subst_guarded` (e.g. witness-LVar canonicalisation below).
///
/// Keyed by the *interned* `&'static str` name (see [`tamarin_term::intern`]):
/// `LVar.name` is already interned, so LVar-sourced builds key with zero
/// alloc, and the (rare, construction-time) parser-`VarSpec`-sourced inserts
/// intern via `intern_str`.  The per-leaf *lookups* on the substitution-apply
/// hot path (`subst_term` / `subst_gterm_cow`) do NOT intern: they probe with
/// the borrowed [`VarSubstKey`], which hashes and compares by content exactly
/// like the owned key — skipping the intern pool entirely (its probe plus the
/// map's own hash cost ~3% of stateverif at 1 core, and its lock traffic
/// ping-pongs across workers at 16).  Key equality is unchanged —
/// `&str`/`String` both hash/compare by content — so the key set is identical
/// to a `(String, u64)` map.
///
/// `IndexMap` (Fx-hashed) rather than a std `HashMap`: `IndexMap` supports
/// the borrowed-key `Equivalent` probe above, and its iteration order is
/// insertion order (deterministic).  Byte-safe: no `VarSubst` is ever
/// iterated toward output — every consumer is a keyed
/// `get`/`insert`/`is_empty`/`len` (the `subst_*` fns, `collect_witness_vars`,
/// `match_atom_via_maude`), and the sole iteration (`combine_substs`' union) is
/// order-independent in both its `Some`/`None` outcome and its resulting map.
pub type VarSubst = indexmap::IndexMap<(&'static str, u64), p::Term, rustc_hash::FxBuildHasher>;

/// Borrowed lookup key for [`VarSubst`]: probes by *content* so the
/// substitution-apply leaves need not intern the leaf's name first.
///
/// Hash-consistency with the owned `(&'static str, u64)` key is by
/// construction: the derived tuple `Hash` feeds `self.0.hash(state)` then
/// `self.1.hash(state)`, and this impl performs the identical two calls on
/// the identical value types (`&str`, `u64`), so equal content ⇒ equal hash
/// under any hasher.  `Equivalent` compares the same two fields, so a probe
/// hits exactly the entries the interned-key probe would.
struct VarSubstKey<'a>(&'a str, u64);

impl std::hash::Hash for VarSubstKey<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl indexmap::Equivalent<(&'static str, u64)> for VarSubstKey<'_> {
    fn equivalent(&self, key: &(&'static str, u64)) -> bool {
        self.1 == key.1 && self.0 == key.0
    }
}

/// Rewrite every Maude-witness LVar named `x` (any idx) to its canonical
/// `idx == 0` form.  Used to dedup implied formulas in
/// `insertImpliedFormulas` where Maude unification mints a fresh witness
/// per call: two structurally-identical derivations from the same
/// (restriction, action-node) pair would otherwise have different witness
/// idx and bypass `Vec::contains`, causing solved_formulas to grow without
/// bound and the simplify loop to never converge.
///
/// We touch ONLY witness vars (name == "x"), canonicalising their idx to 0
/// while preserving name and sort — every other LVar (real protocol vars,
/// distinct named fresh values) keeps its identity, so the dedup doesn't
/// over-merge legitimately-distinct implications.
///
/// Copy-on-write: returns `None` when `g` carries no `x`-named witness var
/// (the common case — `collect_witness_vars` finds nothing) OR when the
/// witness substitution touches no leaf (`subst_guarded_cow` returns
/// `None`), so a caller can reuse `g` by move/borrow instead of cloning.
pub fn normalize_witness_lvars_cow(g: &Guarded) -> Option<Guarded> {
    let mut subst: VarSubst = VarSubst::default();
    collect_witness_vars(g, &mut subst);
    if subst.is_empty() {
        return None;
    }
    subst_guarded_cow(g, &subst)
}

/// Canonicalise AC-`BinOp` argument ordering inside a `Guarded` so two
/// formulas differing only by AC permutation compare equal under `==`.
///
/// HS-faithful rationale.  HS represents formulas using LNTerm (which
/// stores AC operators as flat sorted argument lists via `f_app_ac`).
/// Every HS `mapFrees` / `apply` over LNTerm routes through `f_app_ac`,
/// so AC heads stay in canonical sorted order after substitution.  Rust
/// stores formulas in parser-AST `BinOp(op, l, r)` (strict arity-2), and
/// `subst_term` / `subst_gterm_cow` recurse into the children without
/// re-sorting.
///
/// After `rename_precise_system` renumbers free vars (e.g. `ekR.5 →
/// ekR.0`, `ltkI.7 → ltkI.0`), the LVar `Ord` (`idx`-first ⇒
/// `name`-only on ties) flips: an originally-sorted
/// `Mult(ltkI.5, ekR.7)` (`ltkI < ekR` by idx) becomes a NOW-unsorted
/// `Mult(ltkI.0, ekR.0)` (`ekR < ltkI` by name).  The PARSER-AST slots
/// stay in original order — no re-sort happens.  Meanwhile a fresh
/// implied-formula built via `lnterm_to_term`-of-`f_app_ac` output
/// arrives in canonical sorted form (`Mult(ekR.0, ltkI.0)`).  Dedup via
/// bare `==` (or via `apply_canon`'s witness/bound normalisation) then
/// fails, and `insert_implied_formulas_pass` adds a structurally-
/// duplicate formula on every subsequent `simplifySystem` call —
/// breaking idempotency.
///
/// This pass mirrors HS's invariant explicitly: for every AC head
/// (`Mult`, `Union`, `Xor`, `NatPlus`), flatten the binary chain into
/// the full multiset, sort it via `cmp_term` (the existing HS-faithful
/// parser-AST Ord), then re-fold into a right-leaning canonical
/// `BinOp(op, x0, BinOp(op, x1, ...))`.  Two AC-permuted parser-AST
/// representations of the same multiset collapse to the same shape.
pub fn canonicalize_ac_in_guarded(g: &Guarded) -> Guarded {
    canonicalize_ac_in_guarded_with(g, cmp_term)
}

/// Copy-on-write variant of [`canonicalize_ac_in_guarded`]: returns `None` when
/// `g` is already AC-canonical (no AC subterm anywhere needed re-sorting), so a
/// caller holding an OWNED `g` can reuse it by move instead of allocating a
/// rebuilt deep copy.  `Some(_)` is byte-identical to the eager entry point.
pub fn canonicalize_ac_in_guarded_cow(g: &Guarded) -> Option<Guarded> {
    cac_rec_guarded_cow(g, cmp_term)
}

type GCmp = fn(&GTerm, &GTerm) -> std::cmp::Ordering;

fn cac_rec_term(t: &GTerm, cmp: GCmp) -> GTerm {
    // Wrapper: materialise the COW result, reusing `t` when nothing changed.
    match cac_rec_term_cow(t, cmp) {
        Some(g) => g,
        None => t.clone(),
    }
}

/// Copy-on-write core of `cac_rec_term`.  Returns `None` when the subtree is
/// already in canonical form (no AC chain needed re-sorting and no descendant
/// changed), so the caller can reuse the input `Arc` without allocating a
/// rebuilt copy.  `Some(g)` carries the rebuilt subtree.
///
/// The produced canonical form is byte-identical to the eager version: every
/// `None`-reuse path is gated on the recursive results being structurally
/// unchanged, and the AC branch only returns `None` after confirming the
/// re-folded sorted chain equals the input (`acc == *t`).
fn cac_rec_term_cow(t: &GTerm, cmp: GCmp) -> Option<GTerm> {
    match t {
        GTerm::Var(_)
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => None,
        // `em(a, b)` is the sole COMMUTATIVE (C) function symbol (EMap,
        // bilinear pairing).  HS stores every C application in sorted-arg
        // form: `fAppC nacsym as = FAPP (C nacsym) (sort as)` (Term/Term/Raw.hs:133-134;
        // `fAppEMap (x,y) = fAppC EMap [x,y]`, Term/Term.hs:166-167, see line 167).  So in HS
        // `em('P', x)` and `em(x, 'P')` are byte-identical, and the
        // structural `S.member sSolvedFormulas` guard in `insertImpliedFormulas`
        // always matches a re-derived instance against the solved one.
        //
        // The C-symbol `em` must be sorted here too, not just the AC
        // operators (`Mult/Union/Xor/NatPlus`).  If `em` args are left in
        // whatever order substitution produced them, then after a
        // reuse-lemma's abstract key var `s` is bound (e.g.
        // `s ↦ KDF(em('P', ini_share)^…)`), `substSolvedFormulas` rewrites
        // the solved disjunction with one `em` arg order while a fresh
        // `impliedFormulas` match against the `Secret('KEY', …)` action
        // produces the other order — so the `solved_formulas` dedup fails
        // and RS re-inserts (and re-solves) a disjunction HS had already
        // discharged (idbased/BP_IBS bilinear divergence: extra
        // `secrecy_session_key` reuse-lemma instance after `splitEqs`).
        // Mirror HS: sort `em`'s two args so both sides canonicalise alike.
        GTerm::App(n, args) if &**n == "em" && args.len() == 2 => {
            let a2 = cac_rec_term(&args[0], cmp);
            let b2 = cac_rec_term(&args[1], cmp);
            let (first, second) = if cmp(&a2, &b2) != std::cmp::Ordering::Greater {
                (a2, b2)
            } else {
                (b2, a2)
            };
            let sorted: std::sync::Arc<[GTerm]> = std::sync::Arc::from(vec![first, second]);
            // Reuse the input only when the children were unchanged AND
            // already in sorted order (byte-identical to the rebuilt form).
            if sorted.as_ref() == args.as_ref() {
                None
            } else {
                Some(GTerm::App(n.clone(), sorted))
            }
        }
        GTerm::App(n, args) => cac_rec_slice(args, cmp).map(|new| GTerm::App(n.clone(), new)),
        GTerm::Pair(args) => cac_rec_slice(args, cmp).map(GTerm::Pair),
        GTerm::AlgApp(n, a, b) => {
            cow_pair_arc(a, cac_rec_term_cow(a, cmp), b, cac_rec_term_cow(b, cmp))
                .map(|(a, b)| GTerm::AlgApp(n.clone(), a, b))
        }
        GTerm::Diff(a, b) => cow_pair_arc(a, cac_rec_term_cow(a, cmp), b, cac_rec_term_cow(b, cmp))
            .map(|(a, b)| GTerm::Diff(a, b)),
        GTerm::BinOp(op, l, r) => {
            if is_ac_binop(op) {
                // Recurse into children first, then flatten the whole AC
                // chain rooted here and rebuild in sorted multiset order.
                let l2 = cac_rec_term(l, cmp);
                let r2 = cac_rec_term(r, cmp);
                let mut flat = Vec::new();
                flatten_ac_binop(op, &l2, &mut flat);
                flatten_ac_binop(op, &r2, &mut flat);
                flat.sort_by(|x, y| cmp(x, y));
                // Right-fold to a binary chain.  At least 2 args.
                let mut iter = flat.into_iter().rev();
                let last = iter.next().expect("AC BinOp always flattens to >=2 args");
                let mut acc = last.clone();
                for prev in iter {
                    acc = GTerm::BinOp(*op, ga(prev.clone()), ga(acc));
                }
                // Reuse the input only if the canonical chain is byte-identical
                // (children unchanged AND already sorted+right-leaning).
                if acc == *t {
                    None
                } else {
                    Some(acc)
                }
            } else {
                cow_pair_arc(l, cac_rec_term_cow(l, cmp), r, cac_rec_term_cow(r, cmp))
                    .map(|(l, r)| GTerm::BinOp(*op, l, r))
            }
        }
        GTerm::PatMatch(inner) => cac_rec_term_cow(inner, cmp).map(|g| GTerm::PatMatch(ga(g))),
    }
}

/// COW over a slice of `Arc<[GTerm]>` children: returns `None` if every child
/// is unchanged, else `Some` of the rebuilt slice (reusing unchanged children
/// by cloning their `Arc`).  Single-pass: the output `Vec` is allocated lazily
/// only when (and after) the first child changes.
fn cac_rec_slice(args: &std::sync::Arc<[GTerm]>, cmp: GCmp) -> Option<std::sync::Arc<[GTerm]>> {
    cow_map_arc(args, |a| cac_rec_term_cow(a, cmp))
}

// Copy-on-write canonicalisation, one level up from `cac_rec_term_cow`: each
// `*_cow` returns `None` when nothing under it needed re-sorting, so an
// all-unchanged formula propagates a single `None` to the root and the owned
// caller reuses its input by move (no rebuild).  Every `Some(_)` materialises
// EXACTLY what the eager rebuild produces (changed children rebuilt,
// unchanged children cloned), so the output is byte-identical — the parity gate
// verifies.  The lazy single-pass bookkeeping (clone the unchanged prefix on the
// first change) lives once in `tamarin_utils::cow::{cow_map_arc, cow_pair}`.

fn cac_rec_fact_cow(f: &GFact, cmp: GCmp) -> Option<GFact> {
    cow_map_arc(&f.args, |a| cac_rec_term_cow(a, cmp)).map(|args| GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args,
        annotations: f.annotations.clone(),
    })
}

/// COW of a GTerm pair: `None` when BOTH are unchanged.
fn cac_pair_cow(x: &GTerm, y: &GTerm, cmp: GCmp) -> Option<(GTerm, GTerm)> {
    cow_pair(x, cac_rec_term_cow(x, cmp), y, cac_rec_term_cow(y, cmp))
}

fn cac_rec_atom_cow(a: &GAtom, cmp: GCmp) -> Option<GAtom> {
    match a {
        GAtom::Action(f, t) => cow_pair(f, cac_rec_fact_cow(f, cmp), t, cac_rec_term_cow(t, cmp))
            .map(|(f, t)| GAtom::Action(f, t)),
        GAtom::Eq(x, y) => cac_pair_cow(x, y, cmp).map(|(a, b)| GAtom::Eq(a, b)),
        GAtom::Less(x, y) => cac_pair_cow(x, y, cmp).map(|(a, b)| GAtom::Less(a, b)),
        GAtom::LessMset(x, y) => cac_pair_cow(x, y, cmp).map(|(a, b)| GAtom::LessMset(a, b)),
        GAtom::Subterm(x, y) => cac_pair_cow(x, y, cmp).map(|(a, b)| GAtom::Subterm(a, b)),
        GAtom::Last(t) => cac_rec_term_cow(t, cmp).map(GAtom::Last),
        GAtom::Pred(f) => cac_rec_fact_cow(f, cmp).map(GAtom::Pred),
    }
}

fn cac_rec_guarded_cow(g: &Guarded, cmp: GCmp) -> Option<Guarded> {
    match g {
        Guarded::Atom(a) => cac_rec_atom_cow(a, cmp).map(Guarded::Atom),
        Guarded::Disj(items) => {
            cow_map_arc(items, |i| cac_rec_guarded_cow(i, cmp)).map(Guarded::Disj)
        }
        Guarded::Conj(items) => {
            cow_map_arc(items, |i| cac_rec_guarded_cow(i, cmp)).map(Guarded::Conj)
        }
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => cow_pair(
            guards,
            cow_map_arc(guards, |a| cac_rec_atom_cow(a, cmp)),
            &**body,
            cac_rec_guarded_cow(body, cmp),
        )
        .map(|(guards, body)| Guarded::GGuarded {
            qua: *qua,
            vars: vars.clone(),
            guards,
            body: std::sync::Arc::new(body),
        }),
    }
}

fn canonicalize_ac_in_guarded_with(g: &Guarded, cmp: GCmp) -> Guarded {
    cac_rec_guarded_cow(g, cmp).unwrap_or_else(|| g.clone())
}

fn collect_witness_vars(g: &Guarded, out: &mut VarSubst) {
    // The witness set is exactly the Free-leaf set that
    // `for_each_free_var_in_guarded` enumerates (guards + body, all GAtom
    // variants); we keep only the "x"-named leaves, canonicalising idx→0.
    // `out` is keyed by (interned name, idx), so visitation order is
    // irrelevant to the resulting map.
    //
    // Every accepted leaf has name == "x", so intern the key root once
    // (loop-invariant hoist) instead of per leaf.
    let x_name: &'static str = tamarin_term::intern::intern_str("x");
    for_each_free_var_in_guarded(g, &mut |v| {
        if v.name == "x" {
            let canonical = p::VarSpec {
                name: v.name.clone(),
                idx: 0, // canonical idx
                sort: v.sort,
                typ: v.typ.clone(),
            };
            out.insert((x_name, v.idx), p::Term::Var(canonical));
        }
    });
}

/// Convert the eq-store's `Subst<Name, LVar>` to a parser-AST
/// `VarSubst` so it can be applied to `Guarded` formulas.  Used to
/// canonicalize implied formulas during `insertImpliedFormulas` dedup:
/// Maude unification mints fresh witness LVars per call, so
/// structurally-identical derivations would otherwise be treated as
/// distinct entries.
pub fn var_subst_from_eq_store(eq_store: &crate::tools::equation_store::EquationStore) -> VarSubst {
    use crate::elaborate::lnterm_to_term;
    use tamarin_term::lterm::LVar;
    let mut out: VarSubst = VarSubst::default();
    let pairs: Vec<(LVar, _)> = eq_store.subst.to_list();
    for (lv, lt) in pairs {
        // `lv.name` is already an interned `&'static str` — zero-alloc key.
        out.insert((lv.name, lv.idx), lnterm_to_term(&lt));
    }
    out
}

pub fn subst_term(t: &p::Term, s: &VarSubst) -> p::Term {
    use p::Term;
    match t {
        Term::Var(v) => {
            // Content-keyed probe (`VarSubstKey`): no intern-pool traffic,
            // no allocation — one hash of the (name, idx) pair.
            if let Some(target) = s.get(&VarSubstKey(&v.name, v.idx)) {
                target.clone()
            } else {
                Term::Var(v.clone())
            }
        }
        Term::PubLit(_)
        | Term::FreshLit(_)
        | Term::NatLit(_)
        | Term::Number(_)
        | Term::NumberOne
        | Term::NatOne
        | Term::DhNeutral => t.clone(),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter().map(|a| subst_term(a, s)).collect(),
        ),
        Term::AlgApp(name, a, b) => Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
        Term::Pair(items) => Term::Pair(items.iter().map(|i| subst_term(i, s)).collect()),
        Term::Diff(a, b) => Term::Diff(Box::new(subst_term(a, s)), Box::new(subst_term(b, s))),
        Term::BinOp(op, a, b) => {
            Term::BinOp(*op, Box::new(subst_term(a, s)), Box::new(subst_term(b, s)))
        }
        Term::PatMatch(t) => Term::PatMatch(Box::new(subst_term(t, s))),
    }
}

/// Apply a `VarSubst` to a parser-AST fact.
pub fn subst_fact(f: &p::Fact, s: &VarSubst) -> p::Fact {
    p::Fact {
        args: f.args.iter().map(|a| subst_term(a, s)).collect(),
        ..f.clone()
    }
}

/// Apply a `VarSubst` to a parser-AST atom.
pub fn subst_atom(a: &p::Atom, s: &VarSubst) -> p::Atom {
    use p::Atom;
    match a {
        Atom::Eq(x, y) => Atom::Eq(subst_term(x, s), subst_term(y, s)),
        Atom::Less(x, y) => Atom::Less(subst_term(x, s), subst_term(y, s)),
        Atom::LessMset(x, y) => Atom::LessMset(subst_term(x, s), subst_term(y, s)),
        Atom::Subterm(x, y) => Atom::Subterm(subst_term(x, s), subst_term(y, s)),
        Atom::Action(f, t) => Atom::Action(subst_fact(f, s), subst_term(t, s)),
        Atom::Last(t) => Atom::Last(subst_term(t, s)),
        Atom::Pred(f) => Atom::Pred(subst_fact(f, s)),
    }
}

/// Apply a `VarSubst` to a guarded formula. Substitutes through
/// guards, body, and every nested term/atom — but only Free LVar
/// leaves (Bound vars are positional and cannot collide).
///
/// With HS-faithful DeBruijn bindings, no capture-avoidance dance is
/// needed: Bound vars carry no LVar idx, so a free-var substitution
/// cannot accidentally capture them.
/// Mirrors HS `applySkGuarded subst = mapGuardedAtoms (const $ apply subst)`.
pub fn subst_guarded(g: &Guarded, s: &VarSubst) -> Guarded {
    if s.is_empty() {
        return g.clone();
    }
    subst_guarded_inner(g, s)
}

fn subst_guarded_inner(g: &Guarded, s: &VarSubst) -> Guarded {
    subst_guarded_cow(g, s).unwrap_or_else(|| g.clone())
}

/// Copy-on-write core of `subst_guarded_inner`: returns `None` when the
/// substitution touches no Free leaf anywhere in `g` (and no `mk_gpair` flatten
/// fires), so a caller can reuse `g` instead of deep-rebuilding the whole
/// connective tree.  One level up from `subst_gterm_cow`, mirroring its shape;
/// every `Some(_)` is byte-identical to the eager rebuild (changed children
/// rebuilt, unchanged children cloned, in positional order).
pub fn subst_guarded_cow(g: &Guarded, s: &VarSubst) -> Option<Guarded> {
    match g {
        Guarded::Atom(a) => subst_gatom_cow(a, s).map(Guarded::Atom),
        Guarded::Disj(items) => cow_map_arc(items, |i| subst_guarded_cow(i, s)).map(Guarded::Disj),
        Guarded::Conj(items) => cow_map_arc(items, |i| subst_guarded_cow(i, s)).map(Guarded::Conj),
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => cow_pair(
            guards,
            cow_map_arc(guards, |a| subst_gatom_cow(a, s)),
            &**body,
            subst_guarded_cow(body, s),
        )
        .map(|(guards, body)| Guarded::GGuarded {
            qua: *qua,
            vars: vars.clone(),
            guards,
            body: std::sync::Arc::new(body),
        }),
    }
}

/// Substitute Free LVar leaves in a `GAtom`.  Replacement targets are
/// parser-AST terms (`p::Term`), which we lift to `GTerm` with all-Free
/// leaves — those Free LVars are at the system's top-level scope and
/// cannot collide with any binder.
fn subst_gatom_cow(a: &GAtom, s: &VarSubst) -> Option<GAtom> {
    match a {
        GAtom::Eq(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| GAtom::Eq(a, b)),
        GAtom::Less(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| GAtom::Less(a, b)),
        GAtom::LessMset(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| GAtom::LessMset(a, b)),
        GAtom::Subterm(x, y) => subst_gpair_cow(x, y, s).map(|(a, b)| GAtom::Subterm(a, b)),
        GAtom::Action(f, t) => cow_pair(f, subst_gfact_cow(f, s), t, subst_gterm_cow(t, s))
            .map(|(f, t)| GAtom::Action(f, t)),
        GAtom::Last(t) => subst_gterm_cow(t, s).map(GAtom::Last),
        GAtom::Pred(f) => subst_gfact_cow(f, s).map(GAtom::Pred),
    }
}

fn subst_gpair_cow(x: &GTerm, y: &GTerm, s: &VarSubst) -> Option<(GTerm, GTerm)> {
    cow_pair(x, subst_gterm_cow(x, s), y, subst_gterm_cow(y, s))
}

/// Substitute Free LVar leaves in a `GFact`.
fn subst_gfact_cow(f: &GFact, s: &VarSubst) -> Option<GFact> {
    cow_map_arc(&f.args, |a| subst_gterm_cow(a, s)).map(|args| GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args,
        annotations: f.annotations.clone(),
    })
}

/// Copy-on-write substitution of Free LVar leaves in a `GTerm`.  Returns `None` when the subtree
/// contains no variable in the substitution's domain (so no leaf is replaced
/// and no `mk_gpair` flattening can fire), letting the caller reuse the input
/// `Arc` without rebuilding.  `Some(g)` carries the rebuilt subtree.
///
/// Faithfulness: the result is byte-identical to a full rebuild that maps
/// every leaf and re-runs `mk_gpair` at every `Pair` node.
/// - A `None`-reuse on `App`/`AlgApp`/`Diff`/`BinOp`/`PatMatch` is gated on
///   every child returning `None`, i.e. no substitution touched the subtree.
/// - The `Pair` case is the delicate one: `mk_gpair` flattens a *trailing*
///   `Pair` child even under an empty-effect substitution.  So `None` comes
///   back only when no child changed AND the input's last element is not a
///   `Pair` (i.e. it is already in `mk_gpair`-canonical form, hence
///   `mk_gpair(items) == *t`).  When any child changed, or the tail is a
///   `Pair`, `mk_gpair` runs.
fn subst_gterm_cow(t: &GTerm, s: &VarSubst) -> Option<GTerm> {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            // Content-keyed probe (`VarSubstKey`): no intern-pool traffic,
            // no allocation — one hash of the (name, idx) pair.
            match s.get(&VarSubstKey(&v.name, v.idx)) {
                None => None,
                // Value-equality COW, mirroring the term side's compare-based
                // COW (`map_free_term_cow` in lterm.rs, `if &nl != l`):
                // a hit whose replacement reproduces THIS exact leaf reports
                // `None` so the caller reuses the input instead of rebuilding.
                // `term_to_gterm_free(t) == GTerm::Var(BVar::Free(v))` holds
                // iff `t` is a `Var(spec)` with `spec == v`.  A replacement
                // that normalises spelling (a dropped `typ`) compares unequal
                // and rebuilds, so the leaf canonicalisation of
                // `term_to_gterm_free` is preserved.
                Some(p::Term::Var(spec)) if spec == v => None,
                Some(t) => Some(term_to_gterm_free(t)),
            }
        }
        GTerm::Var(_)
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => None,
        GTerm::App(n, args) => subst_gterm_slice(args, s).map(|new| GTerm::App(n.clone(), new)),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(a, subst_gterm_cow(a, s), b, subst_gterm_cow(b, s))
            .map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
        // Canonicalise via `mk_gpair`: substituting a pair-valued var into a
        // tuple tail (`<..,matchingComm>` with `matchingComm := <a,b>`) would
        // otherwise leave a non-canonical `Pair([..,Pair([a,b])])` that no
        // longer structurally matches the flat form produced by the
        // `impliedFormulas`/LNTerm path — defeating the `solved_formulas`
        // dedup and re-deriving discharged disjunctions.  See `mk_gpair`.
        GTerm::Pair(items) => {
            // `mk_gpair` flattens a trailing `Pair` even under an
            // empty-effect substitution.  Reuse the input (`None`) only if
            // nothing changed AND it is already `mk_gpair`-canonical (tail
            // not a `Pair`).  Otherwise materialise the full child list and
            // run `mk_gpair`.  Single-pass: allocate the rebuild `Vec`
            // lazily on the first changed child.
            let mut out: Option<Vec<GTerm>> = None;
            for (i, it) in items.iter().enumerate() {
                match subst_gterm_cow(it, s) {
                    Some(g) => out.get_or_insert_with(|| items[..i].to_vec()).push(g),
                    None => {
                        if let Some(v) = out.as_mut() {
                            v.push(it.clone());
                        }
                    }
                }
            }
            match out {
                Some(rebuilt) => Some(crate::guarded_types::mk_gpair(rebuilt)),
                None => {
                    // No child changed.  Flatten only if the tail is a `Pair`.
                    if matches!(items.last(), Some(GTerm::Pair(_))) {
                        Some(crate::guarded_types::mk_gpair(items.to_vec()))
                    } else {
                        None
                    }
                }
            }
        }
        GTerm::Diff(a, b) => cow_pair_arc(a, subst_gterm_cow(a, s), b, subst_gterm_cow(b, s))
            .map(|(a, b)| GTerm::Diff(a, b)),
        GTerm::BinOp(op, a, b) => cow_pair_arc(a, subst_gterm_cow(a, s), b, subst_gterm_cow(b, s))
            .map(|(a, b)| GTerm::BinOp(*op, a, b)),
        GTerm::PatMatch(inner) => subst_gterm_cow(inner, s).map(|g| GTerm::PatMatch(ga(g))),
    }
}

/// COW over an `Arc<[GTerm]>` argument slice: `None` if every child is
/// unchanged, else `Some` of the rebuilt slice (unchanged children reuse their
/// `Arc`).  Used by the non-`Pair` n-ary case (`App`), which never flattens.
/// Single-pass: the output `Vec` is allocated lazily on first change.
fn subst_gterm_slice(
    args: &std::sync::Arc<[GTerm]>,
    s: &VarSubst,
) -> Option<std::sync::Arc<[GTerm]>> {
    cow_map_arc(args, |a| subst_gterm_cow(a, s))
}

/// Read-only visitor over every `BVar::Free` leaf of a guarded formula,
/// covering the identical leaf set that `map_lvars_in_guarded` remaps
/// (walk Disj/Conj/GGuarded, hit each Free leaf in guards + body). The
/// single free-var fold behind [`max_var_idx`] and the `HasFrees` impl for
/// [`Guarded`], so the idx-bound walks stay in lockstep with the
/// freshen/shift mapper without rebuilding the tree.
pub fn for_each_free_var_in_guarded<F: FnMut(&p::VarSpec)>(g: &Guarded, f: &mut F) {
    fn rec_term<F: FnMut(&p::VarSpec)>(t: &GTerm, f: &mut F) {
        match t {
            GTerm::Var(BVar::Free(v)) => f(v),
            GTerm::Var(BVar::Bound(_)) => {}
            GTerm::App(_, args) | GTerm::Pair(args) => {
                for a in args.iter() {
                    rec_term(a, f);
                }
            }
            GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
                rec_term(a, f);
                rec_term(b, f);
            }
            GTerm::PatMatch(t) => rec_term(t, f),
            _ => {}
        }
    }
    fn rec_atom<F: FnMut(&p::VarSpec)>(a: &GAtom, f: &mut F) {
        match a {
            GAtom::Eq(x, y) | GAtom::Less(x, y) | GAtom::LessMset(x, y) | GAtom::Subterm(x, y) => {
                rec_term(x, f);
                rec_term(y, f);
            }
            // HS `Foldable ProtoAtom` folds the timepoint BEFORE the fact:
            // `foldMap f (Action i fa) = f i `mappend` foldMap f fa`
            // (Atom.hs:130-131).
            GAtom::Action(fa, t) => {
                rec_term(t, f);
                for arg in fa.args.iter() {
                    rec_term(arg, f);
                }
            }
            GAtom::Last(t) => rec_term(t, f),
            GAtom::Pred(fa) => {
                for a in fa.args.iter() {
                    rec_term(a, f);
                }
            }
        }
    }
    fn rec<F: FnMut(&p::VarSpec)>(g: &Guarded, f: &mut F) {
        match g {
            Guarded::Atom(a) => rec_atom(a, f),
            Guarded::Disj(xs) | Guarded::Conj(xs) => {
                for x in xs.iter() {
                    rec(x, f);
                }
            }
            Guarded::GGuarded { guards, body, .. } => {
                // Bindings carry no idx in the DeBruijn representation.
                for a in guards.iter() {
                    rec_atom(a, f);
                }
                rec(body, f);
            }
        }
    }
    rec(g, f);
}

/// Find the maximum variable idx used in a guarded formula. Used
/// to allocate fresh indices without collisions.
pub fn max_var_idx(g: &Guarded) -> u64 {
    let mut m = 0u64;
    for_each_free_var_in_guarded(g, &mut |v: &p::VarSpec| {
        if v.idx > m {
            m = v.idx;
        }
    });
    m
}

/// `gnot`: structural negation of a guarded formula.
///   - `Atom a`        → `gnot_atom a`
///   - `Disj xs`       → `Conj (map gnot xs)`
///   - `Conj xs`       → `Disj (map gnot xs)`
///   - `All vs gs. gf` → `Ex vs. (gs ∧ ¬gf)` (i.e. `gs ∧ ¬gf` is the new body)
///   - `Ex vs gs. gf`  → `All vs. (gs ⇒ ¬gf)`
pub fn gnot(g: &Guarded) -> Guarded {
    match g {
        Guarded::Atom(a) => gnot_atom(a),
        Guarded::Disj(xs) => gconj(xs.iter().map(gnot).collect()),
        Guarded::Conj(xs) => gdisj(xs.iter().map(gnot).collect()),
        // Use the smart constructors `gex`/`gall` (NOT direct
        // GGuarded build) so that empty-quantifier collapses fire:
        // - `gnot(GGuarded(All, [], [Less i j], gfalse))` (== ¬(i<j))
        //   goes through `gex [] [Less i j] gtrue` → `gconj([Less i j, gtrue])`
        //   → `Less i j` (the atom), not a stale `GGuarded(Ex, [], [Less i j], gtrue)`.
        // Without this collapse, `to_induction_hypothesis` sees the body
        // as nested GGuarded and produces extra `¬(Less)` disjuncts in
        // the IH instead of collapsing them down — leading to a much
        // larger Disj at goal-split time. Mirrors Haskell:
        //   go (GGuarded All ss as gf) = gex  ss as (go gf)
        //   go (GGuarded Ex  ss as gf) = gall ss as (go gf)
        Guarded::GGuarded {
            qua: Quant::All,
            vars,
            guards,
            body,
        } => gex(vars.to_vec(), guards.to_vec(), gnot(body)),
        Guarded::GGuarded {
            qua: Quant::Ex,
            vars,
            guards,
            body,
        } => gall(vars.to_vec(), guards.to_vec(), gnot(body)),
    }
}

// =============================================================================
// Induction — port of `Theory.Constraint.System.Guarded.ginduct`
// =============================================================================

/// `satisfiedByEmptyTrace`: does the formula hold under the empty
/// trace (no actions)? Returns `Err` for atoms outside the scope of a
/// quantifier (formula is not doubly guarded).
pub fn satisfied_by_empty_trace(g: &Guarded) -> Result<bool, String> {
    match g {
        Guarded::Atom(_) => Err("atom outside the scope of a quantifier".to_string()),
        Guarded::Disj(xs) => {
            let mut any = false;
            for x in xs.iter() {
                if satisfied_by_empty_trace(x)? {
                    any = true;
                }
            }
            Ok(any)
        }
        Guarded::Conj(xs) => {
            // HS `liftM and . sequence . getConj` (Guarded.hs:588-594, see line 593):
            // `sequence` forces ALL conjuncts (failing if any is `Left`)
            // BEFORE reducing with `and`.  So we must evaluate every
            // conjunct and propagate any error rather than short-circuiting
            // on the first `Ok(false)`.
            let mut all = true;
            for x in xs.iter() {
                if !satisfied_by_empty_trace(x)? {
                    all = false;
                }
            }
            Ok(all)
        }
        Guarded::GGuarded { qua, .. } => Ok(matches!(qua, Quant::All)),
    }
}

/// Does the formula contain at least one action atom (anywhere)?
/// `containsAction` from Haskell's `ginduct`.
pub fn contains_action(g: &Guarded) -> bool {
    match g {
        // Haskell `containsAction = foldGuarded (const True) ...`
        // (Guarded.hs:636-637): the bare-atom handler is `const True`, so
        // EVERY atom (Action/Eq/Less/Last/Subterm/Pred) yields True — not
        // only Action atoms.
        Guarded::Atom(_) => true,
        Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().any(contains_action),
        Guarded::GGuarded { guards, body, .. } => {
            // Haskell `Guarded.hs:636-637`: `\_ _ as body -> not (null as) || body`.
            !guards.is_empty() || contains_action(body)
        }
    }
}

/// Is `g` closed (no free variables)?
fn is_closed(g: &Guarded) -> bool {
    free_vars(g).is_empty()
}

/// Test whether an atom is a `Last(_)` predicate.
fn is_last_atom(a: &GAtom) -> bool {
    matches!(a, GAtom::Last(_))
}

/// `toInductionHypothesis`: rewrite a doubly guarded formula into its
/// induction hypothesis form. Errors out on non-last-free formulas.
pub fn to_induction_hypothesis(g: &Guarded) -> Result<Guarded, String> {
    match g {
        Guarded::GGuarded {
            qua,
            vars,
            guards,
            body,
        } => {
            if guards.iter().any(is_last_atom) {
                return Err("formula not last-free".to_string());
            }
            let body2 = to_induction_hypothesis(body)?;
            // Emit `Last(v)` for every node-sorted bound variable.
            // Mirrors Haskell's
            //   lastAtos = [ Last (varTerm (Bound j))
            //              | (j, (_, LSortNode)) <- zip [0..] (reverse ss) ]
            // Haskell `reverse ss` (Guarded.hs:613-616, see line 615) — node-sorted binders
            // emitted in REVERSE quantifier order.  For `∀ k #i #j`, ss
            // reversed = [#j, #i, k] → lastAtos = [Last(#j), Last(#i)].
            // Without `.rev()`, our disj order is [#i, #j] (matches HS
            // case_2 first), inverting `case_1`/`case_2` labels for the
            // `last`-disjunction split and breaking proof-tree shape diff.
            // HS `lastAtos = do (j, (_, LSortNode)) <- zip [0..] (reverse ss);
            //                   return $ Last (varTerm (Bound j))`.
            // Iterate vars inner-to-outer (rev), filter to node-sorted,
            // assign DeBruijn `j = 0, 1, ...` in that order.
            let last_atos: Vec<Guarded> = vars
                .iter()
                .rev()
                .enumerate()
                .filter(|(_, v)| v.sort == LSort::Node)
                .map(|(j, _)| Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Bound(j as u32)))))
                .collect();
            match qua {
                Quant::All => {
                    // gex ss as (gconj (map gnotAtom lastAtos ++ [gf']))
                    let mut items: Vec<Guarded> = last_atos.iter().map(gnot).collect();
                    items.push(body2);
                    Ok(gex(vars.to_vec(), guards.to_vec(), gconj(items)))
                }
                Quant::Ex => {
                    // gall ss as (gdisj (map GAto lastAtos ++ [gf']))
                    let mut items = last_atos;
                    items.push(body2);
                    Ok(gall(vars.to_vec(), guards.to_vec(), gdisj(items)))
                }
            }
        }
        Guarded::Atom(GAtom::Less(i, j)) => Ok(Guarded::Disj(
            vec![
                Guarded::Atom(GAtom::Eq(i.clone(), j.clone())),
                Guarded::Atom(GAtom::Less(j.clone(), i.clone())),
            ]
            .into(),
        )),
        Guarded::Atom(GAtom::Last(_)) => Err("formula not last-free".to_string()),
        Guarded::Atom(a) => Ok(gnot_atom(a)),
        Guarded::Disj(xs) => {
            let xs2 = xs
                .iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gconj(xs2))
        }
        Guarded::Conj(xs) => {
            let xs2 = xs
                .iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gdisj(xs2))
        }
    }
}

/// `ginduct`: try to prove `g` by induction over the trace. Returns
/// `(base_case, step_case)` formulas.
///
/// - `base_case`: `gtrue`/`gfalse` depending on whether the empty
///   trace satisfies `g`.
/// - `step_case`: `g ∧ induction_hypothesis(g)`.
pub fn ginduct(g: &Guarded) -> Result<(Guarded, Guarded), String> {
    if !is_closed(g) {
        return Err("formula not closed".to_string());
    }
    if !contains_action(g) {
        return Err("formula contains no action atom".to_string());
    }
    let base = satisfied_by_empty_trace(g)?;
    let gf_ih = to_induction_hypothesis(g)?;
    let base_case = gtf(base);
    let step_case = gconj(vec![g.clone(), gf_ih]);
    Ok((base_case, step_case))
}

/// Apply a `VarSpec → VarSpec` transformation to every FREE variable
/// reference in a `Guarded` formula.  Variables bound by an enclosing
/// `GGuarded` are NOT passed to `f` — they stay verbatim.  It is the map body
/// of this module's `HasFrees` instance, through which a whole-system
/// `mapFrees` (Theory/Constraint/System.hs:1863-1877) reaches the formulas,
/// solved formulas and lemmas a `System` stores.
pub fn map_lvars_in_guarded<F>(g: &Guarded, mut f: F) -> Guarded
where
    F: FnMut(&p::VarSpec) -> p::VarSpec,
{
    // With DeBruijn bindings, only `BVar::Free` leaves carry an LVar
    // identity — `Bound` is positional and skipped automatically.
    // No bound-set tracking needed; the depth handed by the combinator is
    // irrelevant here since `map_free_atom` rewrites Free leaves in place.
    map_guarded_atoms(g, &mut |_d, a| map_free_atom(a, &mut f))
}

/// HS `instance HasFrees (Guarded (String, LSort) c LVar)`
/// (Guarded.hs:272-277): `foldFrees f = foldMap (foldFrees f)` over the
/// `Foldable` instance (Guarded.hs:259-263) and `mapFrees f =
/// traverseGuarded (mapFrees f)` (Guarded.hs:265-270) — atoms in tree order,
/// `GGuarded` guards before body, the binder list left alone.
///
/// The port's leaves are parser `VarSpec`s, so both directions cross
/// [`crate::elaborate::varspec_to_lvar`], which reads the leaf's name, sort
/// and index and interns the name.  `map_free_with` writes the mapped
/// variable's name and index back into the leaf and keeps the leaf's own
/// `sort` and `typ`, so a rename leaves the surface spelling of the formula
/// alone.
///
/// The `monotone` flag has no effect here: no `GTerm` constructor sorts its
/// arguments, so the `Monotone` and the `Arbitrary` map rebuild the same
/// tree.
impl HasFrees for Guarded {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for_each_free_var_in_guarded(self, &mut |v: &p::VarSpec| {
            f(&crate::elaborate::varspec_to_lvar(v))
        });
    }

    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, _monotone: bool) -> Self {
        map_lvars_in_guarded(&self, |v: &p::VarSpec| {
            let w = f(crate::elaborate::varspec_to_lvar(v));
            p::VarSpec {
                name: w.name.to_string(),
                idx: w.idx,
                sort: v.sort,
                typ: v.typ.clone(),
            }
        })
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "guarded_tests.rs"]
mod tests;
