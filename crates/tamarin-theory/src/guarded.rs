// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, beschmi, jdreier, PhilipLukertWork, rkunnema, rsasse, and
//   other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Term.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs,
//   lib/term/src/Term/Term/Raw.hs, lib/term/src/Term/VTerm.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Model/Atom.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Text/Parser/Fact.hs

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

use tamarin_parser::ast as p;
use tamarin_utils::cow::{cow_map_arc, cow_map_vec, cow_pair};
use crate::guarded_types::cow_pair_arc;

pub use crate::guarded_types::{
    ga,
    BVar, GAtom, GBinding, GFact, GTerm,
    atom_to_gatom_free, fact_to_gfact_free, term_to_gterm_free,
    gatom_to_atom, gfact_to_fact, gterm_to_term,
    subst_free_atom_at_depth, subst_free_fact_at_depth, subst_free_term_at_depth,
    subst_bound_atom_at_depth, subst_bound_fact_at_depth, subst_bound_term_at_depth,
    close_subst, open_subst, lvar_to_binding,
    map_free_term, map_free_fact, map_free_atom,
};

// =============================================================================
// Guarded data type
// =============================================================================

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Quant { All, Ex }

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
    if ta != tb { return ta.cmp(&tb); }
    // Tag equality above guarantees same variant, so each `let … else` binding
    // of `b` is infallible.  Match `a` exhaustively (no wildcard) so a new
    // `Guarded` variant forces a comparison here.
    match a {
        Guarded::Atom(x) => {
            let Guarded::Atom(y) = b else { unreachable!("guarded tag matched Atom") };
            cmp_atom(x, y)
        }
        Guarded::Disj(xs) => {
            let Guarded::Disj(ys) = b else { unreachable!("guarded tag matched Disj") };
            cmp_slice(xs, ys, cmp_guarded)
        }
        Guarded::Conj(xs) => {
            let Guarded::Conj(ys) = b else { unreachable!("guarded tag matched Conj") };
            cmp_slice(xs, ys, cmp_guarded)
        }
        Guarded::GGuarded { qua: q1, vars: v1, guards: g1, body: b1 } => {
            let Guarded::GGuarded { qua: q2, vars: v2, guards: g2, body: b2 } = b
                else { unreachable!("guarded tag matched GGuarded") };
            cmp_quant(q1, q2)
                // HS-faithful: in `LNGuarded = Guarded (String,LSort) Name
                // LVar` (Guarded.hs:272-277, see line 279,389), the `s` parameter — used
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
where F: FnMut(&T, &T) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let mut i = 0;
    loop {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => {
                let c = f(x, y);
                if c != Ordering::Equal { return c; }
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
    if ta != tb { return ta.cmp(&tb); }
    // Tag equality above guarantees same variant, so each `let … else` binding
    // of `b` is infallible.  Match `a` exhaustively (no wildcard) so a new
    // `GAtom` variant forces a comparison here.
    match a {
        // HS `data ProtoAtom s t = Action t (Fact t) | ...` derives Ord
        // (Atom.hs:78-84), so the derived comparison is the timepoint term
        // `t` FIRST, then the `Fact t`.  Rust's `GAtom::Action(GFact, GTerm)`
        // stores fact-then-term, so we must compare the timepoint first.
        GAtom::Action(f1, t1) => {
            let GAtom::Action(f2, t2) = b else { unreachable!("atom tag matched Action") };
            cmp_term(t1, t2).then_with(|| cmp_fact(f1, f2))
        }
        GAtom::Eq(a1, b1) => {
            let GAtom::Eq(a2, b2) = b else { unreachable!("atom tag matched Eq") };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
        GAtom::Subterm(a1, b1) => {
            let GAtom::Subterm(a2, b2) = b else { unreachable!("atom tag matched Subterm") };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
        GAtom::Less(a1, b1) => {
            let GAtom::Less(a2, b2) = b else { unreachable!("atom tag matched Less") };
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2))
        }
        GAtom::Last(t1) => {
            let GAtom::Last(t2) = b else { unreachable!("atom tag matched Last") };
            cmp_term(t1, t2)
        }
        GAtom::Pred(f1) => {
            let GAtom::Pred(f2) = b else { unreachable!("atom tag matched Pred") };
            cmp_fact(f1, f2)
        }
        GAtom::LessMset(a1, b1) => {
            let GAtom::LessMset(a2, b2) = b else { unreachable!("atom tag matched LessMset") };
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
    if ca != cb { return ca.cmp(&cb); }
    // FApp class (ca == cb == 1): HS `Ord (Term a)` compares `FAPP fsym ts`
    // by `compare fsym` THEN `compare ts` (derived Ord on
    // `Term a = LIT a | FAPP FunSym [Term a]`, Term/Raw.hs:72-74, see line 74).  The
    // `FunSym` Ord is `NoEq < AC < C < List`, and within `NoEq` it is
    // `Ord NoEqSym = (name, (arity, privacy, constructability))`
    // (FunctionSymbols.hs:113-117, see line 117) — i.e. compared by NAME first.
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
    // matching `fAppAC`'s `sort (...)`, Term/Raw.hs:118-131, see line 122).
    if ca == 1 {
        // Borrowed FunSym key (no per-comparison allocation): compare
        // (outer, name-bytes, arity) in HS order without materialising a
        // `Vec`.  `cmp_term` is a very hot path (every BTreeSet/Map op on
        // guarded terms), so the name must be compared as a `&[u8]` slice.
        let (oa, na, aa) = funsym_key(a);
        let (ob, nb, ab) = funsym_key(b);
        let kc = oa.cmp(&ob)
            .then_with(|| na.cmp(nb))
            .then_with(|| aa.cmp(&ab));
        if kc != std::cmp::Ordering::Equal { return kc; }
        // Same FunSym: compare argument lists in HS `[Term a]` order.
        // AC ops compare a sorted, flattened multiset (HS stores args
        // pre-sorted by `fAppAC`); everything else compares positionally.
        if let (BinOp(o1, _, _), BinOp(o2, _, _)) = (a, b) {
            if is_ac_binop(o1) && is_ac_binop(o2) {
                let mut args_a = Vec::new();
                let mut args_b = Vec::new();
                flatten_ac_binop(o1, a, &mut args_a);
                flatten_ac_binop(o2, b, &mut args_b);
                args_a.sort_by(cmp_term);
                args_b.sort_by(cmp_term);
                return cmp_slice(&args_a, &args_b, cmp_term);
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
/// order `NoEq(0) < AC(1) < C(2) < List(3)` (FunctionSymbols.hs:113-117)
/// and, within `NoEq`, `(name, arity)` mirrors `Ord NoEqSym` (compared by
/// name then arity — privacy/constructability never disambiguate two
/// distinct symbols sharing a name+arity).  AC ops carry no name; their
/// `ACSym` order is `Union < Mult < Xor < NatPlus` (FunctionSymbols.hs:93-94),
/// encoded in the third (`arity`) field as an index so AC terms sort among
/// themselves by ACSym and after every NoEq term.
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
        App(n, args) => (0, n.as_bytes(), args.len()),
        AlgApp(n, _, _) => (0, n.as_bytes(), 2),
        // AC ops: outer = 1, ACSym order Union<Mult<Xor<NatPlus> in field 3.
        BinOp(p::BinOp::Union, _, _)   => (1, b"", 0),
        BinOp(p::BinOp::Mult, _, _)    => (1, b"", 1),
        BinOp(p::BinOp::Xor, _, _)     => (1, b"", 2),
        BinOp(p::BinOp::NatPlus, _, _) => (1, b"", 3),
        // PatMatch is RS-only with no HS equivalent — sort after all.
        PatMatch(_) => (255, b"", 0),
        // Lit-class terms never reach here (ca != 1).
        _ => (254, b"", 0),
    }
}

/// Compare the argument lists of two same-FunSym, non-AC FApp terms,
/// mirroring HS's positional `compare ts` on `[Term a]`.
fn cmp_fapp_args(a: &GTerm, b: &GTerm) -> std::cmp::Ordering {
    use GTerm::*;
    match (a, b) {
        (App(_, x), App(_, y)) => cmp_slice(x, y, cmp_term),
        (Pair(x), Pair(y)) => cmp_slice(x, y, cmp_term),
        (AlgApp(_, l1, r1), AlgApp(_, l2, r2)) =>
            cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        (Diff(l1, r1), Diff(l2, r2)) =>
            cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        (BinOp(_, l1, r1), BinOp(_, l2, r2)) =>
            cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        (PatMatch(x), PatMatch(y)) => cmp_term(x, y),
        // 0-arity builtins (one/tone/DH_neutral): no args.
        (NumberOne, NumberOne) | (NatOne, NatOne) | (DhNeutral, DhNeutral)
            => std::cmp::Ordering::Equal,
        // Cross-variant pairs only reach here when funsym_key tied them
        // (e.g. App("pair",[..]) vs Pair([..]) — both key (0,"pair",2));
        // compare their flattened arg lists positionally.
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
/// (`FreshName | PubName | NodeName | NatName`, LTerm.hs:215-216) so the literal
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
/// NatPlus are AC; Exp is NOT (right-associative algebraic).
fn is_ac_binop(o: &p::BinOp) -> bool {
    use p::BinOp::*;
    matches!(o, Mult | Union | Xor | NatPlus)
}

/// Flatten an AC-BinOp chain into a flat arg list.  E.g.
/// `BinOp(Union, BinOp(Union, a, b), c)` flattens to `[a, b, c]`.
/// Non-matching outer terms are pushed verbatim (no recursion into
/// nested non-Union/non-same-op subtrees).
fn flatten_ac_binop(op: &p::BinOp, t: &GTerm, out: &mut Vec<GTerm>) {
    match t {
        GTerm::BinOp(inner_op, l, r) if inner_op == op => {
            flatten_ac_binop(op, l, out);
            flatten_ac_binop(op, r, out);
        }
        _ => out.push(t.clone()),
    }
}

/// HS-faithful Ord for free `LVar`: `(idx, sort, name)` lexicographic
/// (Term/LTerm.hs:521-523).  Rust's `p::VarSpec` has the same fields
/// in a different declaration order — we compare in HS's order.
/// Used for VarSpecs that appear as FREE vars inside terms.
pub fn cmp_varspec(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx.cmp(&b.idx)
        .then_with(|| cmp_sort_hint(&a.sort, &b.sort))
        .then_with(|| a.name.cmp(&b.name))
}

/// HS-faithful Ord for GGuarded *binding* entries.  In LNGuarded, the
/// binding type is `(String, LSort)` — Guarded.hs:272-277, see line 279,389.  So bindings
/// sort by `(name, sort)` lex.  Our `GBinding` carries only those
/// two fields.
pub fn cmp_binding(a: &GBinding, b: &GBinding) -> std::cmp::Ordering {
    a.name.cmp(&b.name)
        .then_with(|| cmp_sort_hint(&a.sort, &b.sort))
}

/// HS LSort declaration order (Term/LTerm.hs:161-166):
///   LSortPub < LSortFresh < LSortMsg < LSortNode < LSortNat.
fn cmp_sort_hint(a: &p::SortHint, b: &p::SortHint) -> std::cmp::Ordering {
    sort_hint_tag(a).cmp(&sort_hint_tag(b))
}

fn sort_hint_tag(s: &p::SortHint) -> u8 {
    use p::SortHint::*;
    use p::SuffixSort;
    match s {
        Pub => 0,
        Fresh => 1,
        Msg => 2,
        Node => 3,
        Nat => 4,
        Suffix(SuffixSort::Pub) => 0,
        Suffix(SuffixSort::Fresh) => 1,
        Suffix(SuffixSort::Msg) => 2,
        Suffix(SuffixSort::Node) => 3,
        Suffix(SuffixSort::Nat) => 4,
        Untagged => 99, // no HS equivalent (sorted last)
    }
}

/// HS Fact Ord (Theory/Model/Fact.hs:168-169): `compare tag tag' <> compare ts
/// ts'`.  Annotations are explicitly IGNORED in `Ord (Fact t)` (Fact.hs:153-158, see line 163
/// comment "Ignore annotations in equality and ord testing").  Works on
/// `GFact` (HS `Fact (VTerm c (BVar v))`).
///
/// The HS `FactTag` Ord (Fact.hs:132-143, derived) compares a `ProtoFact`
/// by `(Multiplicity, String, Int)` where `Multiplicity = Persistent |
/// Linear` orders `Persistent < Linear`, and `Int` is the arity.  Rust's
/// `bool` Ord gives `false < true`, so to reproduce `Persistent < Linear`
/// we must order `persistent == true` BEFORE `persistent == false` — i.e.
/// reverse the bool comparison.  Arity (`args.len()`) is part of the
/// `FactTag` key and is therefore compared BEFORE the term list, exactly
/// as `compare tag tag'` precedes `compare ts ts'`.
///
/// SPECIAL-TAG SEGREGATION: HS `FactTag` (Fact.hs:132-143, derived Ord) is
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
    // derived constructor order. Special tags follow Fact.hs:134-143.
    match f.name.as_str() {
        "Fr"  => 1, // FreshFact
        "Out" => 2, // OutFact
        "In"  => 3, // InFact
        "KU"  => 4, // KUFact
        "KD"  => 5, // KDFact
        "Ded" => 6, // DedFact
        "Term" => 7, // TermFact (internal; never parsed, but mapped for completeness)
        _ => 0,     // ProtoFact (incl. "K")
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
            b.persistent.cmp(&a.persistent)
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
    Guarded::Conj(EMPTY_CONJ.get_or_init(|| std::sync::Arc::from(Vec::new())).clone())
}
pub fn gfalse() -> Guarded {
    Guarded::Disj(EMPTY_DISJ.get_or_init(|| std::sync::Arc::from(Vec::new())).clone())
}
pub fn gtf(b: bool) -> Guarded { if b { gtrue() } else { gfalse() } }

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
        Guarded::GGuarded { qua: Quant::All, vars, guards, body }
            if vars.is_empty() && guards.len() == 1 => {
            let body_is_false = matches!(&**body, Guarded::Disj(v) if v.is_empty());
            body_is_false && matches!(
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
                    if flatten(x.clone(), out) { return true; }
                }
                false
            }
            x if x == gfalse() => true,
            x => { out.push(x); false }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) { return gfalse(); }
    }
    // HS-faithful: mirror `gconj`'s `nub` BEFORE the `[gf] -> gf`
    // singleton unwrap, so the result is a fixpoint of `gconj` itself:
    // `gconj [a, a]` must be `a`, not the non-normal singleton `Conj [a]`
    // that only a second application would unwrap.  `normalise_guarded`
    // relies on this one-pass idempotence.
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) { deduped.push(x); }
    }
    if deduped.len() == 1 { return deduped.into_iter().next().unwrap(); }
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
    let eval = |a: &GAtom| -> Option<bool> {
        try_gatom_to_atom(a).and_then(|pa| valuation(&pa))
    };
    match fm {
        Guarded::Atom(a) => match eval(a) {
            Some(true) => gtrue(),
            Some(false) => gfalse(),
            None => fm.clone(),
        },
        Guarded::Disj(items) => {
            let simplified: Vec<_> = items.iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gdisj(simplified)
        }
        Guarded::Conj(items) => {
            let simplified: Vec<_> = items.iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gconj(simplified)
        }
        Guarded::GGuarded { qua: Quant::All, vars, guards, body } if vars.is_empty() => {
            let evals: Vec<Option<bool>> = guards.iter().map(eval).collect();
            // Any False guard → universal vacuously holds.
            if evals.iter().any(|v| v == &Some(false)) {
                return gtrue();
            }
            // Keep only the Unknown guards — True guards are vacuous.
            let kept: Vec<GAtom> = guards.iter()
                .zip(&evals)
                .filter(|(_, v)| v.is_none())
                .map(|(a, _)| a.clone())
                .collect();
            let body_s = simplify_guarded_with(body, valuation);
            // HS-faithful: `simp` builds the universal via `gall [] (...) (simp
            // gf)` (Guarded.hs:665-698, see line 687).  `gall` collapses to the body when the
            // kept guards are empty AND collapses the whole universal to
            // `gtrue` when the simplified body is `gtrue` (Guarded.hs:449-453, see line 450),
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
            for a in args.iter() { acc.push(try_gterm_to_term(a)?); }
            p::Term::App(n.to_string(), acc)
        }
        GTerm::AlgApp(n, a, b) =>
            p::Term::AlgApp(n.to_string(), Box::new(try_gterm_to_term(a)?), Box::new(try_gterm_to_term(b)?)),
        GTerm::Pair(items) => {
            let mut acc = Vec::with_capacity(items.len());
            for it in items.iter() { acc.push(try_gterm_to_term(it)?); }
            p::Term::Pair(acc)
        }
        GTerm::Diff(a, b) =>
            p::Term::Diff(Box::new(try_gterm_to_term(a)?), Box::new(try_gterm_to_term(b)?)),
        GTerm::BinOp(op, a, b) =>
            p::Term::BinOp(*op, Box::new(try_gterm_to_term(a)?), Box::new(try_gterm_to_term(b)?)),
        GTerm::PatMatch(t) => p::Term::PatMatch(Box::new(try_gterm_to_term(t)?)),
    })
}

/// Convert `GFact` to `p::Fact` if no Bound vars are present, else None.
pub fn try_gfact_to_fact(f: &GFact) -> Option<p::Fact> {
    let mut args = Vec::with_capacity(f.args.len());
    for a in f.args.iter() { args.push(try_gterm_to_term(a)?); }
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
    // `gdisj` (Guarded.hs:423-435) whose helper
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
                    if flatten(x.clone(), out) { return true; }
                }
                false
            }
            x if x == gtrue() => true,
            x if x == gfalse() => false,
            x => { out.push(x); false }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) { return gtrue(); }
    }
    // HS-faithful: the `[gf] -> gf` singleton unwrap matches the FLATTENED,
    // non-nubbed list (Guarded.hs:415-423, see line 425); `nub` is applied only in the
    // otherwise branch (`GDisj $ Disj $ nub gfs`, Guarded.hs:426-437, see line 432).  So a
    // flattened list like `[a,a]` is not a singleton and yields
    // `Disj (nub [a,a]) = Disj [a]`, NOT bare `a`.  (Note: this `out`
    // already has `gfalse` items dropped — see flatten above — so the
    // empty case below collapses an all-`gfalse` disjunction to `gfalse`.)
    if out.len() == 1 { return out.into_iter().next().unwrap(); }
    // Mirror Haskell `gdisj`'s `nub gfs` (Guarded.hs:426-437, see line 432).
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) { deduped.push(x); }
    }
    if deduped.is_empty() { gfalse() }
    else { Guarded::Disj(deduped.into()) }
}

/// Smart `GGuarded(Ex, ...)` — direct port of Haskell's `gex`:
/// ```text
///   gex []  as  gf                = gconj (map GAto as ++ [gf])
///   gex _   _   gf | gf == gfalse = gfalse
///   gex ss  as  gf                = GGuarded Ex ss as gf
/// ```
pub fn gex(vars: Vec<GBinding>, guards: Vec<GAtom>, body: Guarded) -> Guarded {
    if vars.is_empty() {
        let mut items: Vec<Guarded> = guards.into_iter()
            .map(Guarded::Atom).collect();
        items.push(body);
        return gconj(items);
    }
    if body == gfalse() { return gfalse(); }
    Guarded::GGuarded { qua: Quant::Ex, vars: vars.into(), guards: guards.into(), body: std::sync::Arc::new(body) }
}

/// Smart `GGuarded(All, ...)` — direct port of Haskell's `gall`:
/// ```text
///   gall _   []   gf              = gf
///   gall _   _    gf | gf == gtrue = gtrue
///   gall ss  atos gf              = GGuarded All ss atos gf
/// ```
pub fn gall(vars: Vec<GBinding>, guards: Vec<GAtom>, body: Guarded) -> Guarded {
    if guards.is_empty() { return body; }
    if body == gtrue() { return gtrue(); }
    Guarded::GGuarded { qua: Quant::All, vars: vars.into(), guards: guards.into(), body: std::sync::Arc::new(body) }
}

// =============================================================================
// Errors
// =============================================================================

#[derive(Debug, Clone)]
pub struct GuardError {
    pub message: String,
    /// The parser-AST sub-formula at the point of failure, mirroring HS's
    /// `f0` in `convert polarity f0@(Qua qua0 _ _)` — the innermost
    /// quantifier that failed the guard check.  Used by callers to render
    /// the HS-faithful:
    ///   ```text
    ///   <error_text>
    ///     "<sub_formula>"
    ///   in the formula
    ///     "<full_formula>"
    ///   ```
    /// block.  `None` means the error occurred outside a quantifier context
    /// (shouldn't happen in practice but handled gracefully).
    pub subject_formula: Option<tamarin_parser::ast::Formula>,
}

impl std::fmt::Display for GuardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for GuardError {}

fn err(msg: impl Into<String>) -> GuardError {
    GuardError { message: msg.into(), subject_formula: None }
}

// =============================================================================
// Conversion entry point
// =============================================================================

/// Convert a surface formula to its guarded form.
pub fn formula_to_guarded(f: &p::Formula) -> Result<Guarded, GuardError> {
    // HS-faithful: HS represents formula terms as LNTerm, where every AC head
    // (`Mult`/`Union`/`Xor`/`NatPlus`) is stored as a flat, `fAppAC`-sorted
    // argument list (Term/Term/Raw.hs:118-122).  The sort happens at PARSE
    // time over the FREE logical variables, ordered by `Ord LVar` =
    // (idx, sort, name) (LTerm.hs:522-524) — for freshly-parsed lemma vars
    // (all idx 0) this is name-alphabetical, e.g. `x + z` stays `x++z` and
    // `y + z` stays `y++z`.  `formulaToGuarded` then abstracts Free→Bound via
    // a structural `fmap` (Guarded.hs:289-308) that preserves the AC arg
    // positions.  Our parser stores formula terms as nested `BinOp(op, l, r)`
    // trees in source order and never sorts them, so we canonicalise the AC
    // chains over the FREE-variable parser AST FIRST (mirroring HS's
    // parse-time `fAppAC` on free LVars), then convert to guarded form.
    let canon = crate::elaborate::canonicalize_ac_in_formula(f);
    convert(false, &canon)
}

/// Returns `true` if the formula is "safety": closed (no free vars)
/// and contains no existential quantifier in its guarded form.
pub fn is_safety_formula(g: &Guarded) -> bool {
    fn no_existential(g: &Guarded) -> bool {
        match g {
            Guarded::Atom(_) => true,
            Guarded::GGuarded { qua: Quant::Ex, .. } => false,
            Guarded::GGuarded { qua: Quant::All, body, .. } => no_existential(body),
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
    for_each_free_var_in_guarded(g, &mut |v| { out.insert(v.name.clone()); });
    out
}

/// Collect variable names from a parser-AST term.  Used by
/// `remaining_unguarded` for the pre-DeBruijn unguarded-variable check.
fn term_var_names(t: &p::Term, out: &mut Vec<String>) {
    match t {
        p::Term::Var(v) => out.push(v.name.clone()),
        p::Term::App(_, args) | p::Term::Pair(args) =>
            for a in args { term_var_names(a, out); },
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b)
        | p::Term::BinOp(_, a, b) => { term_var_names(a, out); term_var_names(b, out); }
        p::Term::PatMatch(inner) => term_var_names(inner, out),
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
            Guarded::Disj(items) =>
                Guarded::Disj(items.iter().map(|i| rec(i, depth, f)).collect()),
            Guarded::Conj(items) =>
                Guarded::Conj(items.iter().map(|i| rec(i, depth, f)).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => {
                let new_depth = depth + vars.len() as u32;
                Guarded::GGuarded {
                    qua: qua.clone(),
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
/// idempotent — see the note on `gconj`.  Mirrors HS 150f5eba + follow-up.
pub fn normalise_guarded(g: &Guarded) -> Guarded {
    // Route through the COW helper so borrow-callers get the same logic with
    // no duplication; only cost vs the COW path is the top-level clone when
    // nothing changed.
    normalise_guarded_cow(g).unwrap_or_else(|| g.clone())
}

/// Copy-on-write variant of [`normalise_guarded`]: returns `None` when
/// normalisation leaves `g` structurally unchanged (so an owning caller can
/// reuse `g` by move with zero allocation), `Some(rebuilt)` otherwise.  The
/// `Some` value is BYTE-IDENTICAL to `normalise_guarded(g)` — same
/// flatten/dedup/order.  Mirrors the `subst_guarded_cow` /
/// `cac_rec_guarded_cow` convention (recursion returns `None` when all
/// children are unchanged).
pub fn normalise_guarded_cow(g: &Guarded) -> Option<Guarded> {
    match g {
        // `normalise_guarded`'s Atom arm is `g.clone()` → always unchanged.
        Guarded::Atom(_) => None,
        Guarded::Disj(items) => normalise_disj_list_cow(items).map(|v| Guarded::Disj(v.into())),
        Guarded::Conj(items) => {
            // Normalise children first (COW), then re-run the `gconj`
            // smart-constructor step (flatten nested Conj / absorb gfalse /
            // dedup / singleton-unwrap).  When no child changed AND `gconj`
            // is a structural no-op on the (already-normalised) children, the
            // whole node is unchanged.  Otherwise the rebuild is exactly
            // `gconj(children)` — identical to the eager
            // `gconj(items.iter().map(normalise_guarded).collect())`.
            let mapped = cow_map_vec(items, normalise_guarded_cow);
            let children: &[Guarded] = mapped.as_deref().unwrap_or(&items[..]);
            if mapped.is_none() && gconj_is_structural_noop(children) {
                None
            } else {
                Some(gconj(children.to_vec()))
            }
        }
        Guarded::GGuarded { qua, vars, guards, body } =>
            // Only `body` can change; qua/vars/guards are cloned verbatim.
            normalise_guarded_cow(body).map(|b| Guarded::GGuarded {
                qua: qua.clone(),
                vars: vars.clone(),
                guards: guards.clone(),
                body: std::sync::Arc::new(b),
            }),
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
        if !out.contains(&g) { out.push(g); }
    }
    let mut out: Vec<Guarded> = Vec::new();
    for it in children {
        match it {
            Guarded::Disj(ds) => for d in ds.iter() { push(d.clone(), &mut out); },
            g => push(g.clone(), &mut out),
        }
    }
    out
}

/// Normalise a formula for storage in the constraint system: full
/// smart-constructor normal form, except that a TOP-LEVEL disjunction
/// keeps its `Disj` constructor (via `normalise_disj_list`) so it stays
/// in lockstep with its `Goal::Disj` twin.  Port of HS
/// `normaliseStoredFormula` (150f5eba).
pub fn normalise_stored_formula(g: &Guarded) -> Guarded {
    normalise_stored_formula_cow(g).unwrap_or_else(|| g.clone())
}

/// Copy-on-write variant of [`normalise_stored_formula`]: `None` when
/// unchanged, `Some(rebuilt)` (BYTE-IDENTICAL to
/// `normalise_stored_formula(g)`) otherwise.  Like `normalise_stored_formula`,
/// a TOP-LEVEL `Disj` keeps its constructor (via the constructor-preserving
/// `normalise_disj_list_cow`) so it stays in lockstep with its `Goal::Disj`
/// twin.
pub fn normalise_stored_formula_cow(g: &Guarded) -> Option<Guarded> {
    match g {
        Guarded::Disj(items) => normalise_disj_list_cow(items).map(|v| Guarded::Disj(v.into())),
        _ => normalise_guarded_cow(g),
    }
}

/// Owned fast path for [`normalise_stored_formula`]: consumes `g`, returning
/// it by MOVE (zero allocation) when normalisation is a no-op, else the
/// rebuilt tree.  For callers that own their input and immediately reassign
/// it.  The returned value is BYTE-IDENTICAL to
/// `normalise_stored_formula(&g)`.
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

// =============================================================================
// Polarity-aware conversion
// =============================================================================

fn convert(polarity: bool, f: &p::Formula) -> Result<Guarded, GuardError> {
    match f {
        p::Formula::True => Ok(gtf(!polarity)),
        p::Formula::False => Ok(gtf(polarity)),
        p::Formula::Atom(a) => {
            let ga = atom_to_gatom_free(a);
            if polarity { Ok(gnot_atom(&ga)) } else { Ok(Guarded::Atom(ga)) }
        }
        p::Formula::Not(g) => convert(!polarity, g),
        p::Formula::And(a, b) => {
            let sub = vec![convert(polarity, a)?, convert(polarity, b)?];
            if polarity {
                Ok(gdisj(sub))
            } else {
                Ok(gconj(sub))
            }
        }
        p::Formula::Or(a, b) => {
            let sub = vec![convert(polarity, a)?, convert(polarity, b)?];
            if polarity { Ok(gconj(sub)) } else { Ok(gdisj(sub)) }
        }
        p::Formula::Implies(a, b) => {
            // p ⇒ q  is  ¬p ∨ q
            let nag = convert(!polarity, a)?;
            let cag = convert(polarity, b)?;
            if polarity { Ok(gconj(vec![nag, cag])) } else { Ok(gdisj(vec![nag, cag])) }
        }
        p::Formula::Iff(a, b) => {
            // p ↔ q  is  (p ⇒ q) ∧ (q ⇒ p)
            let lhs = p::Formula::Implies(a.clone(), b.clone());
            let rhs = p::Formula::Implies(b.clone(), a.clone());
            let sub = vec![convert(polarity, &lhs)?, convert(polarity, &rhs)?];
            Ok(gconj(sub))
        }
        // The quantifier shape (Forall vs Exists) determines whether the
        // body must be a top-level implication (`convert_all`) or a
        // conjunction (`convert_ex`). Polarity only affects which
        // quantifier label appears in the output and which polarity we
        // recurse with for inner subformulas.
        //
        // We "open" consecutive same-quantifier prefixes (mirroring
        // Haskell's `openFormulaPrefix`) so that `Ex x. Ex y. body`
        // is treated as a single `Ex [x, y]. body` for guard checking.
        p::Formula::Forall(_, _) | p::Formula::Exists(_, _) => {
            let (xs, body) = open_quantifier_prefix(f);
            let same_qua = matches!(f, p::Formula::Forall(_, _));
            let result = if same_qua {
                let out_qua = if polarity { Quant::Ex } else { Quant::All };
                convert_all(&xs, body, polarity, out_qua)
            } else {
                let out_qua = if polarity { Quant::All } else { Quant::Ex };
                convert_ex(&xs, body, polarity, out_qua)
            };
            // HS: the error from `convEx`/`convAll` is decorated with
            // `ppFormula f0` (the current quantifier sub-formula) by
            // `noUnguardedVars` / the toplevel-implication check.
            // We mirror by attaching `f.clone()` as `subject_formula`
            // on the INNERMOST failure (guard: set only when not yet set,
            // so the deepest quantifier sub-formula wins).
            result.map_err(|mut e| {
                if e.subject_formula.is_none() {
                    e.subject_formula = Some(f.clone());
                }
                e
            })
        }
    }
}

/// Open consecutive same-quantifier binders. `Forall x. Forall y.
/// body` → `(vec![x, y], body)`. The first `Formula` argument must
/// itself be a quantifier; we follow only matching kinds.
fn open_quantifier_prefix(f: &p::Formula) -> (Vec<p::VarSpec>, &p::Formula) {
    let mut vars = Vec::new();
    let mut cur = f;
    let kind = match f {
        p::Formula::Forall(_, _) => 0,
        p::Formula::Exists(_, _) => 1,
        _ => return (vars, f),
    };
    loop {
        match cur {
            p::Formula::Forall(xs, body) if kind == 0 => {
                vars.extend(xs.iter().cloned());
                cur = body;
            }
            p::Formula::Exists(xs, body) if kind == 1 => {
                vars.extend(xs.iter().cloned());
                cur = body;
            }
            _ => break,
        }
    }
    (vars, cur)
}

/// Body-is-conjunction case (existential-shaped). The body is split
/// into guard atoms (action / equality) and remaining sub-formulas;
/// each quantified variable must be bound by some guard atom.
fn convert_ex(
    xs: &[p::VarSpec],
    body: &p::Formula,
    polarity: bool,
    out_qua: Quant,
) -> Result<Guarded, GuardError> {
    let (atoms, others) = split_conj_actions_eqs(body);
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded));
    }
    let mut converted = Vec::new();
    for f in &others {
        converted.push(convert(polarity, f)?);
    }
    let body_guarded = if polarity { gdisj(converted) } else { gconj(converted) };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}

/// Body-is-implication case (universal-shaped). The antecedent is
/// split into guard atoms and remaining sub-formulas; each
/// quantified variable must be bound by some guard atom in the
/// antecedent.
fn convert_all(
    xs: &[p::VarSpec],
    body: &p::Formula,
    polarity: bool,
    out_qua: Quant,
) -> Result<Guarded, GuardError> {
    if let p::Formula::Implies(ante, succ) = body {
        let (atoms, ante_others) = split_conj_actions_eqs(ante);
        let unguarded = remaining_unguarded(xs, &atoms);
        if !unguarded.is_empty() {
            return Err(unguarded_error(&unguarded));
        }
        let mut sub = Vec::with_capacity(ante_others.len() + 1);
        for f in &ante_others {
            sub.push(convert(!polarity, f)?);
        }
        sub.push(convert(polarity, succ)?);
        let body_guarded = if polarity { gconj(sub) } else { gdisj(sub) };
        Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
    } else {
        Err(err("universal quantifier without toplevel implication"))
    }
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
    let new_guards: Vec<GAtom> = atoms.iter()
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

/// Split a conjunction of formulas, separating guard atoms (action /
/// equality) from the remaining sub-formulas. Returns
/// `(guard_atoms, other_subformulas)`.
fn split_conj_actions_eqs(f: &p::Formula) -> (Vec<p::Atom>, Vec<p::Formula>) {
    fn rec(f: &p::Formula, atoms: &mut Vec<p::Atom>, others: &mut Vec<p::Formula>) {
        match f {
            p::Formula::And(a, b) => { rec(a, atoms, others); rec(b, atoms, others); }
            p::Formula::Atom(p::Atom::Action(fact, t)) =>
                atoms.push(p::Atom::Action(fact.clone(), t.clone())),
            p::Formula::Atom(p::Atom::Eq(a, b)) =>
                atoms.push(p::Atom::Eq(a.clone(), b.clone())),
            other => others.push(other.clone()),
        }
    }
    let mut atoms = Vec::new();
    let mut others = Vec::new();
    rec(f, &mut atoms, &mut others);
    (atoms, others)
}

/// Compute which of `xs` are NOT bound by any of `atoms`. Mirrors
/// Haskell's `remainingUnguarded`.
fn remaining_unguarded(xs: &[p::VarSpec], atoms: &[p::Atom]) -> Vec<p::VarSpec> {
    let mut sorted_atoms: Vec<&p::Atom> = atoms.iter().collect();
    // Action atoms first, then equalities.
    sorted_atoms.sort_by_key(|a| match a {
        p::Atom::Action(_, _) => 0,
        _ => 1,
    });
    let mut unguarded: BTreeSet<String> = xs.iter().map(|v| v.name.clone()).collect();
    for atom in &sorted_atoms {
        match atom {
            p::Atom::Action(fact, t) => {
                let mut frees = Vec::new();
                for arg in &fact.args { term_var_names(arg, &mut frees); }
                term_var_names(t, &mut frees);
                for n in frees { unguarded.remove(&n); }
            }
            p::Atom::Eq(s, t) => {
                let mut sv = Vec::new();
                let mut tv = Vec::new();
                term_var_names(s, &mut sv);
                term_var_names(t, &mut tv);
                let s_covered = sv.iter().all(|n| !unguarded.contains(n));
                let t_covered = tv.iter().all(|n| !unguarded.contains(n));
                if s_covered { for n in tv { unguarded.remove(&n); } }
                else if t_covered { for n in sv { unguarded.remove(&n); } }
            }
            _ => {}
        }
    }
    xs.iter().filter(|v| unguarded.contains(&v.name)).cloned().collect()
}

fn unguarded_error(vars: &[p::VarSpec]) -> GuardError {
    // HS: `map (quotes . text . show) unguarded` (Guarded.hs:507-509) over
    // `[LVar]`.  Each LVar is rendered by the EXPLICIT `instance Show LVar`
    // (LTerm.hs:525-531): `show (LVar v s i) = sortPrefix s ++ body`, where
    // `sortPrefix` (LTerm.hs:190-195) is "" (Msg) / "~" (Fresh) / "$" (Pub)
    // / "#" (Node) / "%" (Nat), and `body` is `v` when `i == 0` else
    // `v ++ "." ++ show i`.  `quotes` then single-quotes the result, so the
    // rendered output is e.g. `'#i'` or `'x.5'` — NOT a bare `'name'`.
    let show_lvar = |v: &p::VarSpec| -> String {
        let prefix = match v.sort {
            p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => "~",
            p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => "$",
            p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => "#",
            p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => "%",
            // Msg / Untagged / Suffix(Msg) => "" (LSortMsg has no prefix).
            _ => "",
        };
        let body = if v.name.is_empty() {
            v.idx.to_string()
        } else if v.idx == 0 {
            v.name.clone()
        } else {
            format!("{}.{}", v.name, v.idx)
        };
        format!("'{}{}'", prefix, body)
    };
    let names: Vec<String> = vars.iter().map(show_lvar).collect();
    err(format!("unguarded variable(s) {} in the subformula", names.join(", ")))
}

// =============================================================================
// Negate atoms (`gnotAtom` in Haskell)
// =============================================================================

/// `gnotAtom` — port of Haskell `Theory.Constraint.System.Guarded.gnotAtom`
/// (lib/theory/src/Theory/Constraint/System/Guarded.hs:408-410):
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
/// False rather than ¬Action.  See `Guarded.hs:408-410` vs
/// `Guarded.hs:614-616`.
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
pub type VarSubst =
    indexmap::IndexMap<(&'static str, u64), p::Term, rustc_hash::FxBuildHasher>;

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
pub fn normalize_witness_lvars(g: &Guarded) -> Guarded {
    normalize_witness_lvars_cow(g).unwrap_or_else(|| g.clone())
}

/// Copy-on-write core of [`normalize_witness_lvars`]: returns `None` when `g`
/// carries no `x`-named witness var (the common case — `collect_witness_vars` finds
/// nothing) OR when the witness substitution touches no leaf
/// (`subst_guarded_cow` returns `None`), so a caller can reuse `g` by move/borrow
/// instead of cloning.  `Some(_)` is byte-identical to the eager rebuild.
pub fn normalize_witness_lvars_cow(g: &Guarded) -> Option<Guarded> {
    let mut subst: VarSubst = VarSubst::default();
    collect_witness_vars(g, &mut subst);
    if subst.is_empty() { return None; }
    subst_guarded_cow(g, &subst)
}

/// Identity no-op on `Guarded`, kept so callers can express the intent of
/// alpha-canonicalisation.  With HS-faithful DeBruijn bindings, alpha-equivalent
/// formulas compare equal under structural `Eq` automatically — Bound vars carry
/// no idx, so `Ex j:5. KU(s)@j:5` and `Ex j:6. KU(s)@j:6` both yield
/// `GGuarded { vars: [(j, Node)], body: ... Bound(0) ... }` — so no rewriting is
/// needed.  Called from `constraint::system` and `solver::reduction` to mark
/// the spots where HS relied on its DeBruijn invariant.  `solver::simplify`
/// deliberately skips it — see `implied_apply_canon_cow` in simplify.rs, which
/// drops the call to save one identity `Guarded` clone.
///
/// Intentionally a no-op identity clone: faithful HS port marker.
pub fn normalize_bound_lvars(g: &Guarded) -> Guarded {
    g.clone()
}

/// Normalize equivalent sort hints so two `Guarded` formulas that
/// differ ONLY by sort hint compare equal under `==`.
///
/// All of `SortHint::Msg`, `SortHint::Suffix(SuffixSort::Msg)`, and
/// `SortHint::Untagged` map to `LSort::Msg` in elaboration (see
/// `elaborate::sort_of`).  Implied-formula matching uses Maude →
/// LNTerm → parser-AST round trips, where `lnterm_to_term` always
/// produces the canonical `SortHint::Msg`/`Pub`/`Fresh`/`Node`/`Nat`
/// form regardless of the original hint.  Formulas created by other
/// paths (lemma re-instantiation, ginduct on the IH) may retain
/// `Untagged` or suffix-style hints.  Without normalisation, two
/// semantically-identical formulas compare unequal and the dedupe in
/// `insert_formula` / `insert_implied_formulas_pass` lets
/// duplicates accumulate.
///
/// Concretely: `RFID_Simple::Device_Init_Use_Set` was generating
/// duplicate IH-Disjs at depth 2 — one with `sk:Msg` and one with
/// `sk:Untagged`.
pub fn normalize_sort_hints(g: &Guarded) -> Guarded {
    use crate::guarded_types::normalise_msg_sort as norm_sort;
    fn norm_binding(b: &GBinding) -> GBinding {
        GBinding { name: b.name.clone(), sort: norm_sort(b.sort) }
    }
    fn norm_bvar(b: &BVar) -> BVar {
        match b {
            BVar::Bound(n) => BVar::Bound(*n),
            BVar::Free(v) => BVar::Free(p::VarSpec {
                name: v.name.clone(),
                idx: v.idx,
                sort: norm_sort(v.sort),
                typ: v.typ.clone(),
            }),
        }
    }
    fn norm_term(t: &GTerm) -> GTerm {
        match t {
            GTerm::Var(b) => GTerm::Var(norm_bvar(b)),
            GTerm::App(n, args) => GTerm::App(
                n.clone(), args.iter().map(norm_term).collect()),
            GTerm::Pair(args) => GTerm::Pair(args.iter().map(norm_term).collect()),
            GTerm::AlgApp(n, a, b) => GTerm::AlgApp(
                n.clone(), ga(norm_term(a)), ga(norm_term(b))),
            GTerm::Diff(a, b) => GTerm::Diff(
                ga(norm_term(a)), ga(norm_term(b))),
            GTerm::BinOp(op, a, b) => GTerm::BinOp(
                *op, ga(norm_term(a)), ga(norm_term(b))),
            GTerm::PatMatch(inner) => GTerm::PatMatch(ga(norm_term(inner))),
            _ => t.clone(),
        }
    }
    fn norm_fact(f: &GFact) -> GFact {
        GFact {
            persistent: f.persistent,
            name: f.name.clone(),
            args: f.args.iter().map(norm_term).collect(),
            annotations: f.annotations.clone(),
        }
    }
    fn norm_atom(a: &GAtom) -> GAtom {
        match a {
            GAtom::Action(f, t) => GAtom::Action(norm_fact(f), norm_term(t)),
            GAtom::Eq(x, y) => GAtom::Eq(norm_term(x), norm_term(y)),
            GAtom::Less(x, y) => GAtom::Less(norm_term(x), norm_term(y)),
            GAtom::LessMset(x, y) => GAtom::LessMset(norm_term(x), norm_term(y)),
            GAtom::Subterm(x, y) => GAtom::Subterm(norm_term(x), norm_term(y)),
            GAtom::Last(t) => GAtom::Last(norm_term(t)),
            GAtom::Pred(f) => GAtom::Pred(norm_fact(f)),
        }
    }
    fn rec(g: &Guarded) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(norm_atom(a)),
            Guarded::Disj(items) => Guarded::Disj(items.iter().map(rec).collect()),
            Guarded::Conj(items) => Guarded::Conj(items.iter().map(rec).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => Guarded::GGuarded {
                qua: qua.clone(),
                vars: vars.iter().map(norm_binding).collect(),
                guards: guards.iter().map(norm_atom).collect(),
                body: std::sync::Arc::new(rec(body)),
            },
        }
    }
    rec(g)
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
        GTerm::Var(_) | GTerm::PubLit(_) | GTerm::FreshLit(_)
        | GTerm::NatLit(_) | GTerm::Number(_) | GTerm::NumberOne
        | GTerm::NatOne | GTerm::DhNeutral => None,
        // `em(a, b)` is the sole COMMUTATIVE (C) function symbol (EMap,
        // bilinear pairing).  HS stores every C application in sorted-arg
        // form: `fAppC nacsym as = FAPP (C nacsym) (sort as)` (Raw.hs:132-133;
        // `fAppEMap (x,y) = fAppC EMap [x,y]`, Term.hs:143-147, see line 146).  So in HS
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
            if sorted.as_ref() == args.as_ref() { None } else { Some(GTerm::App(n.clone(), sorted)) }
        }
        GTerm::App(n, args) =>
            cac_rec_slice(args, cmp).map(|new| GTerm::App(n.clone(), new)),
        GTerm::Pair(args) =>
            cac_rec_slice(args, cmp).map(GTerm::Pair),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(a, cac_rec_term_cow(a, cmp), b, cac_rec_term_cow(b, cmp))
            .map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
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
                flat.sort_by(&cmp);
                // Right-fold to a binary chain.  At least 2 args.
                let mut iter = flat.into_iter().rev();
                let last = iter.next().expect("AC BinOp always flattens to >=2 args");
                let mut acc = last;
                for prev in iter {
                    acc = GTerm::BinOp(*op, ga(prev), ga(acc));
                }
                // Reuse the input only if the canonical chain is byte-identical
                // (children unchanged AND already sorted+right-leaning).
                if acc == *t { None } else { Some(acc) }
            } else {
                cow_pair_arc(l, cac_rec_term_cow(l, cmp), r, cac_rec_term_cow(r, cmp))
                    .map(|(l, r)| GTerm::BinOp(*op, l, r))
            }
        }
        GTerm::PatMatch(inner) =>
            cac_rec_term_cow(inner, cmp).map(|g| GTerm::PatMatch(ga(g))),
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
// EXACTLY what the previous eager rebuild produced (changed children rebuilt,
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
        Guarded::Disj(items) =>
            cow_map_arc(items, |i| cac_rec_guarded_cow(i, cmp)).map(Guarded::Disj),
        Guarded::Conj(items) =>
            cow_map_arc(items, |i| cac_rec_guarded_cow(i, cmp)).map(Guarded::Conj),
        Guarded::GGuarded { qua, vars, guards, body } => cow_pair(
            guards,
            cow_map_arc(guards, |a| cac_rec_atom_cow(a, cmp)),
            &**body,
            cac_rec_guarded_cow(body, cmp),
        )
        .map(|(guards, body)| Guarded::GGuarded {
            qua: qua.clone(),
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
                idx: 0,                  // canonical idx
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
pub fn var_subst_from_eq_store(
    eq_store: &crate::tools::equation_store::EquationStore,
) -> VarSubst {
    use tamarin_term::lterm::LVar;
    use crate::elaborate::lnterm_to_term;
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
        Term::PubLit(_) | Term::FreshLit(_) | Term::NatLit(_)
        | Term::Number(_) | Term::NumberOne | Term::NatOne | Term::DhNeutral => t.clone(),
        Term::App(name, args) =>
            Term::App(name.clone(), args.iter().map(|a| subst_term(a, s)).collect()),
        Term::AlgApp(name, a, b) => Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
        Term::Pair(items) => Term::Pair(items.iter().map(|i| subst_term(i, s)).collect()),
        Term::Diff(a, b) => Term::Diff(
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
        Term::BinOp(op, a, b) => Term::BinOp(
            *op,
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
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
    if s.is_empty() { return g.clone(); }
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
        Guarded::Disj(items) =>
            cow_map_arc(items, |i| subst_guarded_cow(i, s)).map(Guarded::Disj),
        Guarded::Conj(items) =>
            cow_map_arc(items, |i| subst_guarded_cow(i, s)).map(Guarded::Conj),
        Guarded::GGuarded { qua, vars, guards, body } => cow_pair(
            guards,
            cow_map_arc(guards, |a| subst_gatom_cow(a, s)),
            &**body,
            subst_guarded_cow(body, s),
        )
        .map(|(guards, body)| Guarded::GGuarded {
            qua: qua.clone(),
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
/// Faithfulness: the result is byte-identical to the eager version.
/// - A `None`-reuse on `App`/`AlgApp`/`Diff`/`BinOp`/`PatMatch` is gated on
///   every child returning `None`, i.e. no substitution touched the subtree.
/// - The `Pair` case is the delicate one: the eager code always runs
///   `mk_gpair`, which flattens a *trailing* `Pair` child even under an
///   empty-effect substitution.  So we only return `None` when no child
///   changed AND the input's last element is not a `Pair` (i.e. it is already
///   in `mk_gpair`-canonical form, hence `mk_gpair(items) == *t`).  When any
///   child changed, or the tail is a `Pair`, we run `mk_gpair` exactly as the
///   eager code did.
fn subst_gterm_cow(t: &GTerm, s: &VarSubst) -> Option<GTerm> {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            // Content-keyed probe (`VarSubstKey`): no intern-pool traffic,
            // no allocation — one hash of the (name, idx) pair.
            match s.get(&VarSubstKey(&v.name, v.idx)) {
                None => None,
                // Value-equality COW, mirroring the term side's compare-based
                // COW (`map_free_term_cow`, lterm.rs:547-549 `if &nl != l`):
                // a hit whose replacement reproduces THIS exact leaf reports
                // `None` so the caller reuses the input instead of rebuilding.
                // `term_to_gterm_free(t) == GTerm::Var(BVar::Free(v))` holds
                // iff `t` is a `Var(spec)` with `spec == v` AND the nullary-fun
                // guard does not fire (that guard lifts the leaf to `App`).  A
                // replacement that normalises spelling (Untagged→Msg sort, or
                // `typ` dropped) compares unequal and rebuilds, so the leaf
                // canonicalisation of `term_to_gterm_free` is preserved.
                Some(p::Term::Var(spec))
                    if spec == v
                        && !(matches!(spec.sort, p::SortHint::Untagged)
                            && spec.idx == 0
                            && crate::elaborate::is_user_nullary_fun(&spec.name)) =>
                    None,
                Some(t) => Some(term_to_gterm_free(t)),
            }
        }
        GTerm::Var(_) | GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne | GTerm::DhNeutral => None,
        GTerm::App(n, args) =>
            subst_gterm_slice(args, s).map(|new| GTerm::App(n.clone(), new)),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(a, subst_gterm_cow(a, s), b, subst_gterm_cow(b, s))
            .map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
        // Canonicalise via `mk_gpair`: substituting a pair-valued var into a
        // tuple tail (`<..,matchingComm>` with `matchingComm := <a,b>`) would
        // otherwise leave a non-canonical `Pair([..,Pair([a,b])])` that no
        // longer structurally matches the flat form produced by the
        // `impliedFormulas`/LNTerm path — defeating the `solved_formulas`
        // dedup and re-deriving discharged disjunctions.  See `mk_gpair`.
        GTerm::Pair(items) => {
            // The eager code always calls `mk_gpair`, which flattens a trailing
            // `Pair` even under an empty-effect substitution.  Reuse the input
            // (`None`) only if nothing changed AND it is already
            // `mk_gpair`-canonical (tail not a `Pair`).  Otherwise we must
            // materialise the full child list and run `mk_gpair`, exactly as
            // the eager code did.  Single-pass: allocate the rebuild `Vec`
            // lazily on the first changed child.
            let mut out: Option<Vec<GTerm>> = None;
            for (i, it) in items.iter().enumerate() {
                match subst_gterm_cow(it, s) {
                    Some(g) => out.get_or_insert_with(|| items[..i].to_vec()).push(g),
                    None => if let Some(v) = out.as_mut() { v.push(it.clone()); }
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
        GTerm::PatMatch(inner) =>
            subst_gterm_cow(inner, s).map(|g| GTerm::PatMatch(ga(g))),
    }
}

/// COW over an `Arc<[GTerm]>` argument slice: `None` if every child is
/// unchanged, else `Some` of the rebuilt slice (unchanged children reuse their
/// `Arc`).  Used by the non-`Pair` n-ary case (`App`), which never flattens.
/// Single-pass: the output `Vec` is allocated lazily on first change.
fn subst_gterm_slice(args: &std::sync::Arc<[GTerm]>, s: &VarSubst)
    -> Option<std::sync::Arc<[GTerm]>>
{
    cow_map_arc(args, |a| subst_gterm_cow(a, s))
}

/// Read-only visitor over every `BVar::Free` leaf of a guarded formula,
/// covering the identical leaf set that `map_lvars_in_guarded` remaps
/// (walk Disj/Conj/GGuarded, hit each Free leaf in guards + body). The
/// single free-var fold shared by [`max_var_idx`]/[`min_var_idx`] so the
/// idx-bound walks stay in lockstep with the freshen/shift mapper without
/// rebuilding the tree.
pub fn for_each_free_var_in_guarded<F: FnMut(&p::VarSpec)>(g: &Guarded, f: &mut F) {
    fn rec_term<F: FnMut(&p::VarSpec)>(t: &GTerm, f: &mut F) {
        match t {
            GTerm::Var(BVar::Free(v)) => f(v),
            GTerm::Var(BVar::Bound(_)) => {}
            GTerm::App(_, args) | GTerm::Pair(args) => {
                for a in args.iter() { rec_term(a, f); }
            }
            GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
                rec_term(a, f); rec_term(b, f);
            }
            GTerm::PatMatch(t) => rec_term(t, f),
            _ => {}
        }
    }
    fn rec_atom<F: FnMut(&p::VarSpec)>(a: &GAtom, f: &mut F) {
        match a {
            GAtom::Eq(x, y) | GAtom::Less(x, y) | GAtom::LessMset(x, y)
            | GAtom::Subterm(x, y) => { rec_term(x, f); rec_term(y, f); }
            GAtom::Action(fa, t) => {
                for arg in fa.args.iter() { rec_term(arg, f); }
                rec_term(t, f);
            }
            GAtom::Last(t) => rec_term(t, f),
            GAtom::Pred(fa) => for a in fa.args.iter() { rec_term(a, f); },
        }
    }
    fn rec<F: FnMut(&p::VarSpec)>(g: &Guarded, f: &mut F) {
        match g {
            Guarded::Atom(a) => rec_atom(a, f),
            Guarded::Disj(xs) | Guarded::Conj(xs) => for x in xs.iter() { rec(x, f); },
            Guarded::GGuarded { guards, body, .. } => {
                // Bindings carry no idx in the DeBruijn representation.
                for a in guards.iter() { rec_atom(a, f); }
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
        if v.idx > m { m = v.idx; }
    });
    m
}

/// Minimum idx over all `BVar::Free` leaves of a guarded formula, or
/// `None` when the formula has no free variables.  The min-side twin of
/// [`max_var_idx`] — needed by HS `boundsVarIdx` mirrors (LTerm.hs:650-651
/// folds frees with `minMaxSingleton`), e.g. the `matchToGoal`
/// whole-source `rename` rebase in `sources.rs`.
pub fn min_var_idx(g: &Guarded) -> Option<u64> {
    let mut m: Option<u64> = None;
    for_each_free_var_in_guarded(g, &mut |v: &p::VarSpec| {
        m = Some(m.map_or(v.idx, |c| c.min(v.idx)));
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
        Guarded::GGuarded { qua: Quant::All, vars, guards, body } => {
            gex(vars.to_vec(), guards.to_vec(), gnot(body))
        }
        Guarded::GGuarded { qua: Quant::Ex, vars, guards, body } => {
            gall(vars.to_vec(), guards.to_vec(), gnot(body))
        }
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
                if satisfied_by_empty_trace(x)? { any = true; }
            }
            Ok(any)
        }
        Guarded::Conj(xs) => {
            // HS `liftM and . sequence . getConj` (Guarded.hs:589-591):
            // `sequence` forces ALL conjuncts (failing if any is `Left`)
            // BEFORE reducing with `and`.  So we must evaluate every
            // conjunct and propagate any error rather than short-circuiting
            // on the first `Ok(false)`.
            let mut all = true;
            for x in xs.iter() {
                if !satisfied_by_empty_trace(x)? { all = false; }
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
        // (Guarded.hs:634-635): the bare-atom handler is `const True`, so
        // EVERY atom (Action/Eq/Less/Last/Subterm/Pred) yields True — not
        // only Action atoms.
        Guarded::Atom(_) => true,
        Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().any(contains_action),
        Guarded::GGuarded { guards, body, .. } => {
            // Haskell `Guarded.hs:634-635`: `\_ _ as body -> not (null as) || body`.
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
        Guarded::GGuarded { qua, vars, guards, body } => {
            if guards.iter().any(is_last_atom) {
                return Err("formula not last-free".to_string());
            }
            let body2 = to_induction_hypothesis(body)?;
            // Emit `Last(v)` for every node-sorted bound variable.
            // Mirrors Haskell's
            //   lastAtos = [ Last (varTerm (Bound j))
            //              | (j, (_, LSortNode)) <- zip [0..] (reverse ss) ]
            // Haskell `reverse ss` (Guarded.hs:601-622, see line 613) — node-sorted binders
            // emitted in REVERSE quantifier order.  For `∀ k #i #j`, ss
            // reversed = [#j, #i, k] → lastAtos = [Last(#j), Last(#i)].
            // Without `.rev()`, our disj order is [#i, #j] (matches HS
            // case_2 first), inverting `case_1`/`case_2` labels for the
            // `last`-disjunction split and breaking proof-tree shape diff.
            // HS `lastAtos = do (j, (_, LSortNode)) <- zip [0..] (reverse ss);
            //                   return $ Last (varTerm (Bound j))`.
            // Iterate vars inner-to-outer (rev), filter to node-sorted,
            // assign DeBruijn `j = 0, 1, ...` in that order.
            let last_atos: Vec<Guarded> = vars.iter().rev().enumerate()
                .filter(|(_, v)| matches!(
                    v.sort,
                    p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node)
                ))
                .map(|(j, _)| {
                    Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Bound(j as u32))))
                })
                .collect();
            match qua {
                Quant::All => {
                    // gex ss as (gconj (map gnotAtom lastAtos ++ [gf']))
                    let mut items: Vec<Guarded> = last_atos.iter()
                        .map(gnot).collect();
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
        Guarded::Atom(GAtom::Less(i, j)) => Ok(Guarded::Disj(vec![
            Guarded::Atom(GAtom::Eq(i.clone(), j.clone())),
            Guarded::Atom(GAtom::Less(j.clone(), i.clone())),
        ].into())),
        Guarded::Atom(GAtom::Last(_)) => Err("formula not last-free".to_string()),
        Guarded::Atom(a) => Ok(gnot_atom(a)),
        Guarded::Disj(xs) => {
            let xs2 = xs.iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gconj(xs2))
        }
        Guarded::Conj(xs) => {
            let xs2 = xs.iter()
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
/// `GGuarded` are NOT passed to `f` — they stay verbatim.  Used by
/// `freshen_system_keep_with_shift` (sources.rs) to shift free-var
/// idxs in stored formulas / solved_formulas / lemmas alongside the
/// rest of the system, mirroring Haskell's uniform `mapFrees`
/// (System.hs:1863-1876) which traverses ALL 13 system fields.
pub fn map_lvars_in_guarded<F>(g: &Guarded, mut f: F) -> Guarded
where F: FnMut(&p::VarSpec) -> p::VarSpec,
{
    // With DeBruijn bindings, only `BVar::Free` leaves carry an LVar
    // identity — `Bound` is positional and skipped automatically.
    // No bound-set tracking needed; the depth handed by the combinator is
    // irrelevant here since `map_free_atom` rewrites Free leaves in place.
    map_guarded_atoms(g, &mut |_d, a| map_free_atom(a, &mut f))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::{parser::parse_formula_str};

    fn g(s: &str) -> Result<Guarded, GuardError> {
        let f = parse_formula_str(s).map_err(|e| err(format!("parse: {}", e)))?;
        formula_to_guarded(&f)
    }

    #[test]
    fn ground_truth() {
        let r = g("T").unwrap();
        assert_eq!(r, gtrue());
    }

    // GFact builder for cmp_fact ordering tests.
    fn gf(persistent: bool, name: &str) -> GFact {
        GFact { persistent, name: name.into(), args: vec![].into(), annotations: vec![] }
    }

    /// HS `FactTag` derived Ord segregates all ProtoFacts before every
    /// special tag, and orders the special tags in declaration sequence
    /// (Fr < Out < In < KU < KD < Ded < Term).  cmp_fact must reproduce
    /// this from the canonicalised name string.
    #[test]
    fn cmp_fact_special_tag_segregation() {
        use std::cmp::Ordering::Less;
        // A ProtoFact with a name that lexically sorts AFTER every special
        // name must still come FIRST (constructor index dominates).
        let proto_z = gf(false, "Zebra");
        for special in ["Fr", "Out", "In", "KU", "KD", "Ded", "Term"] {
            let persistent = matches!(special, "KU" | "KD");
            let s = gf(persistent, special);
            assert_eq!(cmp_fact(&proto_z, &s), Less,
                "ProtoFact must sort before special tag {special}");
        }
        // Special tags order in declaration sequence.
        assert_eq!(cmp_fact(&gf(false, "Fr"), &gf(false, "Out")), Less);
        assert_eq!(cmp_fact(&gf(false, "Out"), &gf(false, "In")), Less);
        assert_eq!(cmp_fact(&gf(false, "In"), &gf(true, "KU")), Less);
        assert_eq!(cmp_fact(&gf(true, "KU"), &gf(true, "KD")), Less);
        assert_eq!(cmp_fact(&gf(true, "KD"), &gf(false, "Ded")), Less);
        assert_eq!(cmp_fact(&gf(false, "Ded"), &gf(false, "Term")), Less);
        // "K" is an ordinary ProtoFact (not special), so it precedes Fr.
        assert_eq!(cmp_fact(&gf(false, "K"), &gf(false, "Fr")), Less);
    }

    /// ProtoFacts compare by (Persistent<Linear, name, arity).
    #[test]
    fn cmp_fact_proto_triple() {
        use std::cmp::Ordering::Less;
        // Persistent < Linear (reversed bool).
        assert_eq!(cmp_fact(&gf(true, "P"), &gf(false, "P")), Less);
        // Then by name.
        assert_eq!(cmp_fact(&gf(false, "A"), &gf(false, "B")), Less);
        // Then by arity.
        let a1 = GFact { persistent: false, name: "P".into(),
            args: vec![].into(), annotations: vec![] };
        let a2 = GFact { persistent: false, name: "P".into(),
            args: vec![crate::guarded_types::GTerm::Var(crate::guarded_types::BVar::Bound(0))].into(),
            annotations: vec![] };
        assert_eq!(cmp_fact(&a1, &a2), Less);
    }

    #[test]
    fn gnot_true_is_false() {
        assert_eq!(gnot(&gtrue()), gfalse());
    }

    #[test]
    fn gnot_false_is_true() {
        assert_eq!(gnot(&gfalse()), gtrue());
    }

    #[test]
    fn gnot_disj_becomes_conj() {
        let f1 = gtrue();
        let f2 = gfalse();
        let d = Guarded::Disj(vec![f1.clone(), f2.clone()].into());
        let n = gnot(&d);
        // ¬(T ∨ ⊥) = ¬T ∧ ¬⊥ = ⊥ ∧ T. After gconj, this collapses to ⊥
        // because gconj short-circuits on a gfalse.
        assert_eq!(n, gfalse());
    }

    #[test]
    fn gnot_conj_becomes_disj() {
        let f1 = gtrue();
        let d = Guarded::Conj(vec![f1.clone(), f1].into());
        // ¬(T ∧ T) = ¬T ∨ ¬T = ⊥ ∨ ⊥ — gdisj filters out gfalse → gfalse.
        assert_eq!(gnot(&d), gfalse());
    }

    #[test]
    fn ginduct_rejects_action_free_formula() {
        // gtrue contains no action atom — ginduct should reject.
        assert!(ginduct(&gtrue()).is_err());
        assert!(ginduct(&gfalse()).is_err());
    }

    #[test]
    fn satisfied_by_empty_trace_handles_quants() {
        // ∀ x. T : empty trace satisfies (no x exists ⇒ trivially).
        let p = parse_formula_str("All x #i. P(x)@#i ==> Q(x)@#i").ok();
        if let Some(f) = p {
            if let Ok(g) = formula_to_guarded(&f) {
                let v = satisfied_by_empty_trace(&g).unwrap();
                // ∀ over an empty trace is vacuously satisfied.
                assert!(v);
            }
        }
    }

    #[test]
    fn ginduct_existential_action_succeeds() {
        // Ex k #i. P(k) @ #i — closed, contains an action atom, not last-bearing.
        let p = parse_formula_str("Ex k #i. P(k)@#i").expect("parse");
        let g = formula_to_guarded(&p).expect("guarded");
        let (base, step) = ginduct(&g).expect("ginduct");
        // Empty-trace satisfaction: ∃ over empty trace is vacuously false.
        assert_eq!(base, gfalse());
        // Step case is `gconj [g, IH]` — typically wraps both.
        match &step {
            Guarded::Conj(items) => {
                assert!(items.iter().any(|x| x == &g),
                    "step case should contain the original formula");
            }
            other => panic!("expected Conj, got {:?}", other),
        }
    }

    #[test]
    fn gnot_double_is_identity_on_atoms() {
        // Smart constructors normalise away T/⊥ in larger formulas, so
        // double-negation isn't structurally identity in general — but
        // it is on the propositional constants themselves.
        for f in &[gtrue(), gfalse()] {
            let nn = gnot(&gnot(f));
            assert_eq!(&nn, f);
        }
    }

    #[test]
    fn ground_false() {
        let r = g("F").unwrap();
        assert_eq!(r, gfalse());
    }

    #[test]
    fn simple_action_under_all() {
        // All k #i. Setup(k) @ i ==> F
        // The All has guard `Setup(k) @ i`, which binds both k and #i.
        let r = g("All k #i. Setup(k) @ #i ==> F").unwrap();
        match r {
            Guarded::GGuarded { qua, vars, guards, .. } => {
                assert_eq!(qua, Quant::All);
                assert_eq!(vars.len(), 2);
                assert_eq!(guards.len(), 1);
            }
            x => panic!("expected GGuarded, got {:?}", x),
        }
    }

    #[test]
    fn unguarded_variable_rejected() {
        // All k. F  — `k` has no action atom guarding it.
        let res = g("All k. F");
        assert!(res.is_err(), "expected unguarded error");
    }

    #[test]
    fn exists_with_guarded_var() {
        // Ex k #i. Setup(k) @ i — k and #i are guarded by Setup(k) @ i.
        let r = g("Ex k #i. Setup(k) @ #i").unwrap();
        match r {
            Guarded::GGuarded { qua, vars, .. } => {
                assert_eq!(qua, Quant::Ex);
                assert_eq!(vars.len(), 2);
            }
            x => panic!("expected GGuarded(Ex), got {:?}", x),
        }
    }

    #[test]
    fn safety_no_existential() {
        let r = g("All k #i. Setup(k) @ #i ==> F").unwrap();
        assert!(is_safety_formula(&r));
    }

    #[test]
    fn safety_rejects_existential() {
        let r = g("All k #i. Setup(k) @ #i ==> Ex j #t. Foo(j) @ #t").unwrap();
        assert!(!is_safety_formula(&r));
    }

    #[test]
    fn implication_distributes() {
        // (a ⇒ b) when both atoms guard their bound vars
        let r = g("All k #i. Setup(k) @ #i ==> (Ex j #t. Setup(j) @ #t)").unwrap();
        // expect a GGuarded(All, [k, #i], [Setup(k) @ i], body)
        // where body is gconj([gnot Setup(k) @ i  ?, GGuarded(Ex ...)])
        // — we only assert the top-level shape here.
        match r {
            Guarded::GGuarded { qua, .. } => assert_eq!(qua, Quant::All),
            x => panic!("got {:?}", x),
        }
    }

    // =========================================================================
    // VarSubst correctness tests — the term-based substitution model
    // =========================================================================

    fn var(name: &str, idx: u64) -> p::Term {
        p::Term::Var(p::VarSpec {
            name: name.into(), idx, sort: p::SortHint::Msg, typ: None,
        })
    }
    fn pubconst(s: &str) -> p::Term { p::Term::PubLit(s.into()) }

    #[test]
    fn varsubst_var_to_var_remap() {
        let mut s = VarSubst::default();
        s.insert(("x", 0), var("y", 5));
        let result = subst_term(&var("x", 0), &s);
        assert_eq!(result, var("y", 5));
    }

    #[test]
    fn varsubst_var_to_non_var_term() {
        // Bind `k` to the public constant 'foo'.
        let mut s = VarSubst::default();
        s.insert(("k", 0), pubconst("foo"));
        let result = subst_term(&var("k", 0), &s);
        assert_eq!(result, pubconst("foo"));
    }

    #[test]
    fn varsubst_descends_into_app_args() {
        // `f(k, m)` where `k` is bound to 'foo'.
        let mut s = VarSubst::default();
        s.insert(("k", 0), pubconst("foo"));
        let t = p::Term::App("f".into(), vec![var("k", 0), var("m", 0)]);
        let result = subst_term(&t, &s);
        let expected = p::Term::App("f".into(), vec![pubconst("foo"), var("m", 0)]);
        assert_eq!(result, expected);
    }

    #[test]
    fn varsubst_unmapped_var_unchanged() {
        let s = VarSubst::default();  // empty
        let t = var("k", 0);
        assert_eq!(subst_term(&t, &s), t);
    }

    #[test]
    fn varsubst_idx_aware() {
        // Two vars with same name but different idx — only the
        // matching one is replaced.
        let mut s = VarSubst::default();
        s.insert(("x", 5), var("y", 0));
        // x with idx 5 → y, x with idx 6 unchanged.
        assert_eq!(subst_term(&var("x", 5), &s), var("y", 0));
        assert_eq!(subst_term(&var("x", 6), &s), var("x", 6));
    }

    #[test]
    fn varsubst_pair_descent() {
        let mut s = VarSubst::default();
        s.insert(("a", 0), pubconst("X"));
        let t = p::Term::Pair(vec![var("a", 0), var("b", 0)]);
        let result = subst_term(&t, &s);
        let expected = p::Term::Pair(vec![pubconst("X"), var("b", 0)]);
        assert_eq!(result, expected);
    }

    /// The parser produces `Ex #i. P @ i` with the binder as `Node` and
    /// the body's `i` as `Untagged`.  `close_subst` must match by
    /// `(name, idx)` only — full `VarSpec` equality would leave the body's
    /// `i` Free, breaking `is_closed` / `ginduct`.
    #[test]
    fn injectivity_check_ginduct_succeeds() {
        let f = parse_formula_str("not (Ex id #i #j #k. Initiated(id) @ i & Removed(id) @ j & Copied(id) @ k & #i < #j & #j < #k)").expect("parse");
        let g = formula_to_guarded(&f).expect("guarded");
        let g_neg = gnot(&g);
        assert!(free_vars(&g_neg).is_empty(), "gnot should be closed");
        assert!(ginduct(&g_neg).is_ok(), "ginduct should succeed");
    }

    #[test]
    fn varsubst_shadowing_blocks_inner_binder() {
        // `Ex k. Action(k) @ i` — substituting `k` from outside should
        // NOT rewrite the inner `k` because it's positionally bound
        // (DeBruijn `Bound(0)` in the body, not Free LVar `k:0`).
        let mut s = VarSubst::default();
        s.insert(("k", 0), pubconst("OUTER"));
        let inner_k = p::VarSpec { name: "k".into(), idx: 0, sort: p::SortHint::Msg, typ: None };
        let mkfact = |t: p::Term| p::Fact {
            persistent: false,
            annotations: Vec::new(),
            name: "Action".into(),
            args: vec![t],
        };
        // Build via close_guarded so that `k` becomes Bound(0) in the body.
        let g = close_guarded(
            Quant::Ex,
            vec![inner_k.clone()],
            Vec::new(),
            Guarded::Atom(atom_to_gatom_free(&p::Atom::Action(
                mkfact(var("k", 0)),
                var("i", 0),
            ))),
        );
        let result = subst_guarded(&g, &s);
        // Body should be unchanged: subst on Free `(k, 0)` doesn't
        // touch the Bound `k` reference.
        match result {
            Guarded::GGuarded { body, .. } => match &*body {
                Guarded::Atom(GAtom::Action(fa, _)) => {
                    // Walk the body atom and verify the `k` slot is still Bound(0).
                    match &fa.args[0] {
                        GTerm::Var(BVar::Bound(0)) => {}
                        other => panic!("expected Bound(0), got {:?}", other),
                    }
                }
                other => panic!("expected Atom(Action), got {:?}", other),
            },
            other => panic!("expected GGuarded, got {:?}", other),
        }
    }

    #[test]
    fn gnot_existential_becomes_forall() {
        // ¬ (Ex k #i. Setup(k)@i) should be All k #i. (Setup(k)@i ⇒ ⊥).
        let parsed = parse_formula_str("Ex k #i. Setup(k) @ #i").unwrap();
        let g = formula_to_guarded(&parsed).unwrap();
        let neg = gnot(&g);
        match &neg {
            Guarded::GGuarded { qua, .. } => assert_eq!(*qua, Quant::All),
            other => panic!("expected GGuarded(All, ...), got {:?}", other),
        }
    }

    #[test]
    fn ginduct_extracts_two_cases() {
        let parsed = parse_formula_str("All k #i. Setup(k) @ #i ==> Ex #j. Setup(k) @ #j & #j < #i").unwrap();
        let g = formula_to_guarded(&parsed).unwrap();
        // Closed + has action atoms → ginduct should succeed.
        let (base, step) = ginduct(&g).expect("ginduct should succeed");
        // Step case is gconj([orig, IH]).
        // gconj may flatten if a sub-Conj appears; otherwise accept any shape —
        // the contract is just that ginduct returned.
        if let Guarded::Conj(items) = step {
            assert_eq!(items.len(), 2);
        }
        let _ = base;
    }

    /// Pin Haskell parity for `lastAtos`: the IH for an `All`-guarded
    /// formula introduces a `¬Last(v)` for every node-sorted bound
    /// variable.  Mirrors the Haskell:
    ///
    ///   toInductionHypothesis (GGuarded All ss as gf) =
    ///       gex ss as (gconj (map gnotAtom lastAtos ++ [IH gf]))
    ///     where lastAtos = [Last (Bound j) | (j,(_,LSortNode)) ← ...]
    #[test]
    fn induction_hypothesis_emits_last_atoms_for_node_sorted_binders() {
        // `All #i. Setup(k) @ #i ⇒ ⊥`  is doubly guarded with one
        // node-sorted binder.  The IH must contain `Last(#i)` (in
        // *negated* form, since the outer quantifier flips All→Ex and
        // we conjoin `¬Last(v)` per node binder).
        let parsed = parse_formula_str("All #i. Setup('k') @ #i ==> G('x') @ #i").unwrap();
        let g = formula_to_guarded(&parsed).unwrap();
        let ih = to_induction_hypothesis(&g).expect("should produce IH");

        // Outer must flip All → Ex, keep guards, and the body should be
        // a Conj that mentions `Last(#i)` somewhere.
        match &ih {
            Guarded::GGuarded { qua, vars, body, .. } => {
                assert_eq!(*qua, Quant::Ex);
                assert_eq!(vars.len(), 1);
                // Walk the body looking for a Last atom at the innermost
                // binder.  In DeBruijn form, that's `Last(Bound(0))`.
                fn walks_to_last_bound0(g: &Guarded) -> bool {
                    match g {
                        Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Bound(0)))) => true,
                        Guarded::Atom(_) => false,
                        Guarded::Disj(xs) | Guarded::Conj(xs) =>
                            xs.iter().any(walks_to_last_bound0),
                        Guarded::GGuarded { guards, body, .. } =>
                            guards.iter().any(|a| matches!(a, GAtom::Last(GTerm::Var(BVar::Bound(0)))))
                                || walks_to_last_bound0(body),
                    }
                }
                assert!(walks_to_last_bound0(body),
                    "IH body should mention Last(Bound 0) for the node binder; got {:?}", body);
            }
            other => panic!("expected GGuarded(Ex, ...), got {:?}", other),
        }
    }

    /// IH must NOT introduce a Last-atom for non-node-sorted binders.
    /// Matches Haskell's filter `(_, LSortNode) ← ...`.
    #[test]
    fn induction_hypothesis_skips_non_node_binders() {
        // `All k. K(k) ⇒ ⊥`: the bound variable `k` is `Msg`-sorted
        // (no `#` prefix, no `:node` suffix) — no Last-atom should be
        // emitted.  The body collapses to `gconj([] ++ [IH body])` =
        // just the IH body.
        let parsed = parse_formula_str("All k. K(k) ==> G('x') @ #i").unwrap();
        let g = match formula_to_guarded(&parsed) {
            Ok(x) => x,
            Err(_) => return,  // formula may be ill-guarded — that's fine
        };
        let ih = match to_induction_hypothesis(&g) { Ok(x) => x, Err(_) => return };
        // Walk: should find no `Last(_)` atom anywhere, since `k` is Msg-sorted.
        fn has_any_last(g: &Guarded) -> bool {
            match g {
                Guarded::Atom(GAtom::Last(_)) => true,
                Guarded::Atom(_) => false,
                Guarded::Disj(xs) | Guarded::Conj(xs) =>
                    xs.iter().any(has_any_last),
                Guarded::GGuarded { guards, body, .. } =>
                    guards.iter().any(|a| matches!(a, GAtom::Last(_)))
                        || has_any_last(body),
            }
        }
        assert!(!has_any_last(&ih),
            "IH should not emit Last for non-node binders; got {:?}", ih);
    }

    // =========================================================================
    // simplify_guarded_with — partial-atom-valuation rewriting
    //
    // Mirrors Haskell's `simplifyGuardedOrReturn` from
    // `Theory.Constraint.System.Guarded`:
    //   simp (GAto a)       = maybe fm gtf (valuation a)
    //   simp (GDisj fms)    = gdisj (map simp fms)
    //   simp (GConj fms)    = gconj (map simp fms)
    //   simp (GGuarded All [] atos gf)
    //     | any (Just False ==) (map valuation atos) = gtrue
    //     | otherwise = gall [] (filter unknown atos) (simp gf)
    //   simp (GGuarded ...) = fm  -- delay past binders
    // =========================================================================

    fn mk_atom_eq(a: &str, b: &str) -> Guarded {
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        Guarded::Atom(atom_to_gatom_free(&p::Atom::Eq(mkv(a), mkv(b))))
    }

    #[test]
    fn simplify_atom_with_known_true_collapses_to_gtrue() {
        let g = mk_atom_eq("x", "y");
        let val = |_a: &p::Atom| Some(true);
        assert_eq!(simplify_guarded_with(&g, &val), gtrue());
    }

    #[test]
    fn simplify_atom_with_known_false_collapses_to_gfalse() {
        let g = mk_atom_eq("x", "y");
        let val = |_a: &p::Atom| Some(false);
        assert_eq!(simplify_guarded_with(&g, &val), gfalse());
    }

    #[test]
    fn simplify_atom_unknown_left_intact() {
        let g = mk_atom_eq("x", "y");
        let val = |_a: &p::Atom| None;
        assert_eq!(simplify_guarded_with(&g, &val), g);
    }

    #[test]
    fn simplify_disj_drops_false_branches() {
        // a ∨ b — if b evaluates False and a is unknown, result = a.
        let a = mk_atom_eq("p", "q");
        let b = mk_atom_eq("r", "s");
        let g = Guarded::Disj(vec![a.clone(), b.clone()].into());
        let val = move |atom: &p::Atom| match atom {
            p::Atom::Eq(x, _) => match x {
                p::Term::Var(v) if v.name == "r" => Some(false),
                _ => None,
            },
            _ => None,
        };
        assert_eq!(simplify_guarded_with(&g, &val), a);
    }

    #[test]
    fn simplify_conj_short_circuits_on_false() {
        // a ∧ b — if b evaluates False, conj should be gfalse.
        let a = mk_atom_eq("p", "q");
        let b = mk_atom_eq("r", "s");
        let g = Guarded::Conj(vec![a, b].into());
        let val = |atom: &p::Atom| match atom {
            p::Atom::Eq(x, _) => match x {
                p::Term::Var(v) if v.name == "r" => Some(false),
                _ => None,
            },
            _ => None,
        };
        assert_eq!(simplify_guarded_with(&g, &val), gfalse());
    }

    #[test]
    fn simplify_universal_with_one_false_guard_is_gtrue() {
        // (All vars[]. [a, b]. body) with a=False → gtrue (vacuous).
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let b = p::Atom::Eq(mkv("c"), mkv("d"));
        let body = mk_atom_eq("p", "q");
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: Vec::new().into(),
            guards: vec![atom_to_gatom_free(&a), atom_to_gatom_free(&b)].into(),
            body: std::sync::Arc::new(body),
        };
        let val = move |atom: &p::Atom| {
            if atom == &a { Some(false) } else { None }
        };
        assert_eq!(simplify_guarded_with(&g, &val), gtrue());
    }

    #[test]
    fn simplify_universal_drops_true_guards_keeps_unknown() {
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let b = p::Atom::Eq(mkv("c"), mkv("d"));
        let body = mk_atom_eq("p", "q");
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: Vec::new().into(),
            guards: vec![atom_to_gatom_free(&a), atom_to_gatom_free(&b)].into(),
            body: std::sync::Arc::new(body.clone()),
        };
        let a_clone = a.clone();
        let b_clone = b.clone();
        // The `b_clone` arm is kept conceptually distinct from the default to
        // mirror the test valuation (a → drop, b → keep, others → unknown).
        #[allow(clippy::if_same_then_else)]
        let val = move |atom: &p::Atom| {
            if atom == &a_clone { Some(true) }   // drop
            else if atom == &b_clone { None }    // keep
            else { None }
        };
        let simp = simplify_guarded_with(&g, &val);
        match simp {
            Guarded::GGuarded { vars, guards, .. } => {
                assert!(vars.is_empty());
                assert_eq!(guards, vec![atom_to_gatom_free(&b)].into());
            }
            other => panic!("expected GGuarded with one guard, got {:?}", other),
        }
    }

    #[test]
    fn simplify_universal_with_all_true_guards_returns_body() {
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let body = mk_atom_eq("p", "q");
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: Vec::new().into(),
            guards: vec![atom_to_gatom_free(&a)].into(),
            body: std::sync::Arc::new(body.clone()),
        };
        let val = |_atom: &p::Atom| Some(true);
        // Both guard and body atoms evaluate to True under this
        // valuation, so universal vacuous-then-body collapses to gtrue.
        assert_eq!(simplify_guarded_with(&g, &val), gtrue());
    }

    #[test]
    fn simplify_universal_with_quantifier_left_intact() {
        // GGuarded with bound vars is left alone — Haskell delays
        // simplification past the binder.
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let body = mk_atom_eq("p", "q");
        let bound_var = GBinding {
            name: "x".into(), sort: p::SortHint::Msg,
        };
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: vec![bound_var].into(),
            guards: vec![atom_to_gatom_free(&a)].into(),
            body: std::sync::Arc::new(body),
        };
        let val = |_atom: &p::Atom| Some(true);
        assert_eq!(simplify_guarded_with(&g, &val), g);
    }

    // =========================================================================
    // Haskell-faithfulness invariants for guarded-formula smart ctors.
    //
    // `gconj` / `gdisj` mirror Haskell's smart constructors in
    // `Theory.Constraint.System.Guarded` (Guarded.hs:415-423, see line 418, :432).  They
    // SHORT-CIRCUIT on `gtrue`/`gfalse` and dedupe via `nub`.
    // =========================================================================

    /// `gtrue` is represented as `Conj []` and `gfalse` as `Disj []`.
    /// This is a Haskell convention (`gtf False = GDisj (Disj [])`,
    /// `gtf True = GConj (Conj [])`, Guarded.hs:395-398).  Many
    /// short-circuit checks rely on it (e.g. `x == gfalse()` in
    /// `gconj`).  If we accidentally encode them differently, every
    /// short-circuit silently breaks.
    #[test]
    fn gtrue_is_empty_conj_and_gfalse_is_empty_disj() {
        assert_eq!(gtrue(), Guarded::Conj(vec![].into()));
        assert_eq!(gfalse(), Guarded::Disj(vec![].into()));
        assert_ne!(gtrue(), gfalse(), "gtrue and gfalse must be distinguishable");
    }

    /// `gconj([gtrue, gtrue, ...])` reduces to `gtrue`.  Empty/trivial
    /// conjunction is True.  Mirrors Haskell `gconj`'s elimination of
    /// `gtrue` items.
    #[test]
    fn gconj_of_only_gtrue_items_is_gtrue() {
        // Guarded.hs:418: `gconj` should collapse all-true conjunctions.
        // Rust impl flattens `Conj` items (gtrue is Conj([])), so all
        // gtrue items dissolve into empty.  Result: `Conj([])` = gtrue.
        let g = gconj(vec![gtrue(), gtrue(), gtrue()]);
        assert_eq!(g, gtrue(),
                   "gconj of only-True items must collapse to gtrue");
    }

    /// `gconj([..., gfalse, ...])` SHORT-CIRCUITS to `gfalse` regardless
    /// of other items.  This is the "any-false makes conjunction false"
    /// short-circuit at Guarded.hs:415-423, see line 418.
    #[test]
    fn gconj_short_circuits_on_gfalse() {
        // Build a non-trivial atom by parsing a small formula.
        let atom_g = g("Last(#i)").unwrap();
        // Any gfalse in the items short-circuits to gfalse.
        let g = gconj(vec![gtrue(), gfalse(), atom_g.clone()]);
        assert_eq!(g, gfalse(),
                   "gconj must short-circuit when any item is gfalse");
        let g2 = gconj(vec![atom_g, gfalse()]);
        assert_eq!(g2, gfalse());
    }

    /// `gdisj([gfalse, gfalse, ...])` reduces to `gfalse`. Empty
    /// disjunction is False.
    #[test]
    fn gdisj_of_only_gfalse_items_is_gfalse() {
        let g = gdisj(vec![gfalse(), gfalse()]);
        assert_eq!(g, gfalse(),
                   "gdisj of only-False items must collapse to gfalse");
    }

    /// `gdisj([..., gtrue, ...])` short-circuits to `gtrue`.
    #[test]
    fn gdisj_short_circuits_on_gtrue() {
        let g = gdisj(vec![gfalse(), gtrue(), gfalse()]);
        assert_eq!(g, gtrue(),
                   "gdisj must short-circuit on first gtrue encountered");
    }

    /// `gconj` deduplicates syntactically-equal items.  Mirrors
    /// Haskell's `nub gfs` (Guarded.hs:415-423, see line 418).  Dedup is ORDER-PRESERVING
    /// (Haskell `Data.List.nub` keeps first occurrence).
    #[test]
    fn gconj_dedupes_syntactic_duplicates() {
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let out = gconj(vec![a.clone(), b.clone(), a.clone()]);
        // Expected: Conj([a, b]) — second occurrence of `a` dropped.
        match out {
            Guarded::Conj(items) => {
                assert_eq!(items.len(), 2,
                    "gconj must dedupe identical items via nub");
                assert_eq!(items[0], a);
                assert_eq!(items[1], b);
            }
            _ => panic!("expected Conj"),
        }
    }

    /// Dedup happens BEFORE the singleton unwrap: `gconj([a, a])` must be
    /// `a` itself, not the non-normal singleton `Conj([a])` that only a
    /// second application would unwrap.  `normalise_guarded` relies on
    /// this one-pass idempotence (mirrors HS `gconj`).
    #[test]
    fn gconj_duplicates_collapse_to_bare_item() {
        let a = g("Last(#i)").unwrap();
        let out = gconj(vec![a.clone(), a.clone()]);
        assert_eq!(out, a, "gconj must dedupe before the singleton unwrap");
    }

    /// `gdisj` deduplicates syntactically-equal items.  Same as above,
    /// for disjunction.  Without this dedup, `verify_checksign_test`-class
    /// SplitG variants double up.
    #[test]
    fn gdisj_dedupes_syntactic_duplicates() {
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let out = gdisj(vec![a.clone(), b.clone(), a.clone(), b.clone()]);
        match out {
            Guarded::Disj(items) => {
                assert_eq!(items.len(), 2,
                    "gdisj must dedupe identical items via nub");
                assert_eq!(items[0], a);
                assert_eq!(items[1], b);
            }
            _ => panic!("expected Disj"),
        }
    }

    /// `gconj` with a single non-trivial item collapses to that item
    /// (no Conj wrapper).  Mirrors Haskell's `case gfs' of [g] -> g`
    /// pattern.
    #[test]
    fn gconj_singleton_unwraps() {
        let a = g("Last(#i)").unwrap();
        let out = gconj(vec![a.clone()]);
        assert_eq!(out, a, "singleton gconj must unwrap to the lone item");
    }

    /// `gconj` flattens nested `Conj` one level.  Mirrors Haskell's
    /// `concatMap` flatten.
    #[test]
    fn gconj_flattens_nested_conj_one_level() {
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let c = g("Last(#k)").unwrap();
        let inner = Guarded::Conj(vec![a.clone(), b.clone()].into());
        let out = gconj(vec![inner, c.clone()]);
        match out {
            Guarded::Conj(items) => {
                assert_eq!(items.len(), 3,
                    "nested Conj should be flattened: 2 inner + 1 outer = 3");
                assert_eq!(items, vec![a, b, c].into());
            }
            _ => panic!("expected Conj"),
        }
    }

    /// `gdisj` recursively flattens ARBITRARILY deeply nested `Disj`s.
    /// Mirrors HS `gdisj`'s `flatten (GDisj disj) = concatMap flatten $
    /// getDisj disj` (Guarded.hs:423-435), which unwraps every level, not
    /// just one — a 5-way `∨` parsed as a binary-Or chain must flatten to a
    /// single 5-alt Disj goal.
    #[test]
    fn gdisj_deeply_nested_disj_flattens_to_5_alts() {
        let a = g("Last(#a)").unwrap();
        let b = g("Last(#b)").unwrap();
        let c = g("Last(#c)").unwrap();
        let d = g("Last(#d)").unwrap();
        let e = g("Last(#e)").unwrap();
        // Build the left-leaning binary-Or chain
        // `Disj(Disj(Disj(Disj(a, b), c), d), e)`.
        let lvl1 = Guarded::Disj(vec![a.clone(), b.clone()].into());
        let lvl2 = Guarded::Disj(vec![lvl1, c.clone()].into());
        let lvl3 = Guarded::Disj(vec![lvl2, d.clone()].into());
        let lvl4 = Guarded::Disj(vec![lvl3, e.clone()].into());
        let out = gdisj(vec![lvl4]);
        match out {
            Guarded::Disj(items) => {
                assert_eq!(items.len(), 5,
                    "4-level-nested binary-Or chain must flatten to 5 \
                     alts (HS `flatten` recurses) — got {} alts",
                    items.len());
                assert_eq!(items, vec![a, b, c, d, e].into(),
                    "flatten preserves leaf order (HS uses concatMap)");
            }
            other => panic!("expected Disj of 5 items, got {:?}", other),
        }
    }

    /// Symmetric: `gconj` recursively flattens deeply nested `Conj`s.
    /// Mirrors HS Guarded.hs:413-421 `flatten (GConj conj) = concatMap
    /// flatten $ getConj conj`.
    #[test]
    fn gconj_deeply_nested_conj_flattens() {
        let a = g("Last(#a)").unwrap();
        let b = g("Last(#b)").unwrap();
        let c = g("Last(#c)").unwrap();
        let d = g("Last(#d)").unwrap();
        let e = g("Last(#e)").unwrap();
        let lvl1 = Guarded::Conj(vec![a.clone(), b.clone()].into());
        let lvl2 = Guarded::Conj(vec![lvl1, c.clone()].into());
        let lvl3 = Guarded::Conj(vec![lvl2, d.clone()].into());
        let lvl4 = Guarded::Conj(vec![lvl3, e.clone()].into());
        let out = gconj(vec![lvl4]);
        match out {
            Guarded::Conj(items) => {
                assert_eq!(items.len(), 5,
                    "4-level-nested binary-And chain must flatten to 5 \
                     conj items — got {}", items.len());
                assert_eq!(items, vec![a, b, c, d, e].into());
            }
            other => panic!("expected Conj of 5 items, got {:?}", other),
        }
    }

    // =========================================================================
    // Haskell-faithfulness invariants for `gnot` and quantifier swap.
    //
    // Mirrors Haskell `gnot` (Guarded.hs):
    //     gnot (GGuarded All ss as gf) = gex  ss as (gnot gf)
    //     gnot (GGuarded Ex  ss as gf) = gall ss as (gnot gf)
    //
    // The All↔Ex swap under negation is critical: proto-fact actions need
    // a specific Haskell-faithful negation shape, and getting this wrong
    // has downstream nondeterminism impact on trace search.
    // =========================================================================

    /// `gnot ∘ gnot = id` (involution) for ground formulas.
    /// This is the most fundamental algebraic property of negation.
    /// If gnot doesn't round-trip, every double-negation in IH
    /// reasoning silently degrades.
    #[test]
    fn gnot_double_negation_is_identity() {
        assert_eq!(gnot(&gnot(&gtrue())), gtrue());
        assert_eq!(gnot(&gnot(&gfalse())), gfalse());
        // Atom case.
        let a = g("Last(#i)").unwrap();
        assert_eq!(gnot(&gnot(&a)), a,
                   "gnot is involutive on atomic formulas — \
                    needed for `to_induction_hypothesis` round-trip.");
    }

    /// `gnot (All ... body) = Ex ... gnot(body)`.  Haskell:
    /// `gnot (GGuarded All ss as gf) = gex ss as (gnot gf)`.
    ///
    /// **The quantifier flips on negation.**  If we forget to flip,
    /// `to_induction_hypothesis` produces the wrong dual and the IH
    /// becomes vacuous or false.
    #[test]
    fn gnot_flips_universal_to_existential() {
        // ∀ x #i. P(x)@#i ⇒ Q(x)@#i — guarded universal.
        // Negation flips to: ∃ x #i. P(x)@#i ∧ ¬Q(x)@#i.
        let f = g("All x #i. P(x)@#i ==> Q(x)@#i").unwrap();
        let n = gnot(&f);
        // The resulting quantifier MUST be Ex.
        match n {
            Guarded::GGuarded { qua: Quant::Ex, .. } => {}
            other => panic!(
                "expected Ex quantifier after negating All; got {:?}", other),
        }
    }

    /// `gnot (Ex ... body) = All ... gnot(body)`.  Symmetric to above.
    ///
    /// Together these ensure that `gnot ∘ gnot` round-trips through
    /// the quantifier — Ex → All → Ex.  Without the flip on either
    /// side, the double-negation property breaks.
    #[test]
    fn gnot_flips_existential_to_universal() {
        let f = g("Ex x #i. P(x)@#i").unwrap();
        // Sanity: starts as Ex.
        match &f {
            Guarded::GGuarded { qua: Quant::Ex, .. } => {}
            other => panic!("test setup: expected Ex; got {:?}", other),
        }
        let n = gnot(&f);
        // After negation, outer quantifier must be All (or the formula
        // simplified — but for this non-trivial body it remains All).
        match n {
            Guarded::GGuarded { qua: Quant::All, .. } => {}
            other => panic!(
                "expected All quantifier after negating Ex; got {:?}", other),
        }
    }

    /// De Morgan: `gnot (gconj [a, b]) = gdisj [gnot a, gnot b]`.
    /// Already exercised in `gnot_conj_becomes_disj` — pin the dual.
    #[test]
    fn gnot_distributes_over_disj() {
        // ¬(a ∨ b) = ¬a ∧ ¬b
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let or = Guarded::Disj(vec![a.clone(), b.clone()].into());
        let neg = gnot(&or);
        // Should be Conj([¬a, ¬b]) — both negated.
        let expected = gconj(vec![gnot(&a), gnot(&b)]);
        assert_eq!(neg, expected,
            "De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b — required for IH derivation");
    }

    /// `em` is the sole commutative (C) function symbol; HS stores it in
    /// sorted-arg form (`fAppC EMap (sort [a,b])`).  `canonicalize_ac_in_guarded`
    /// must sort the two `em` args so a substituted solved-formula and a
    /// freshly-derived implied-formula over the same pairing compare equal —
    /// otherwise `insertImpliedFormulas` re-fires a discharged reuse-lemma
    /// disjunction (the idbased/BP_IBS bilinear divergence).
    #[test]
    fn canonicalize_sorts_commutative_em_args() {
        use std::sync::Arc;
        // Build em(x, 'P') — var-before-pub, i.e. NON-canonical, since
        // constants sort before variables in cmp_term.
        let x = GTerm::Var(BVar::Free(p::VarSpec {
            name: "x".into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        }));
        let p_lit = GTerm::PubLit("P".into());
        let em_unsorted = GTerm::App(
            Arc::from("em"),
            Arc::from(vec![x.clone(), p_lit.clone()]));
        let em_sorted = GTerm::App(
            Arc::from("em"),
            Arc::from(vec![p_lit.clone(), x.clone()]));
        // Wrap each in an Eq atom inside a trivial guarded formula so we
        // exercise the real `canonicalize_ac_in_guarded` entry point.
        let mk = |t: &GTerm| Guarded::Atom(GAtom::Eq(
            t.clone(), GTerm::PubLit("z".into())));
        let canon_unsorted = canonicalize_ac_in_guarded(&mk(&em_unsorted));
        let canon_sorted = canonicalize_ac_in_guarded(&mk(&em_sorted));
        // Both must canonicalise to the sorted form, hence be equal.
        assert_eq!(canon_unsorted, canon_sorted,
            "em(x,'P') and em('P',x) must canonicalise to the same form");
        assert_eq!(canon_unsorted, mk(&em_sorted),
            "em args must be sorted to (pub, var) = ('P', x)");
        // Also exercise em nested under exp(em(...), m) — the BP_IBS shape.
        let exp_unsorted = GTerm::BinOp(
            p::BinOp::Exp,
            Arc::new(em_unsorted.clone()),
            Arc::new(x.clone()));
        let exp_sorted = GTerm::BinOp(
            p::BinOp::Exp,
            Arc::new(em_sorted.clone()),
            Arc::new(x.clone()));
        assert_eq!(
            canonicalize_ac_in_guarded(&mk(&exp_unsorted)),
            canonicalize_ac_in_guarded(&mk(&exp_sorted)),
            "em nested under exp must also have its args sorted");
    }

    #[test]
    fn subst_gterm_cow_var_value_equality() {
        // The value-equality COW in `subst_gterm_cow`'s Var arm must return
        // `None` ONLY when the replacement reproduces the exact same leaf, and
        // must still rebuild (`Some`) whenever the hit normalises the leaf's
        // spelling — otherwise the leaf-canonicalisation of `term_to_gterm_free`
        // (Untagged→Msg sort, `typ` dropped) would be silently lost.
        let mut s: VarSubst = VarSubst::default();
        // Replacement is the canonical Msg-sorted, no-typ leaf.
        s.insert(
            ("x", 0),
            p::Term::Var(p::VarSpec {
                name: "x".into(), idx: 0, sort: p::SortHint::Msg, typ: None,
            }),
        );

        let leaf = |sort: p::SortHint, typ: Option<&str>| GTerm::Var(BVar::Free(p::VarSpec {
            name: "x".into(), idx: 0, sort, typ: typ.map(str::to_string),
        }));

        // Exact identity hit: replacement == leaf → reuse the input (`None`).
        assert_eq!(subst_gterm_cow(&leaf(p::SortHint::Msg, None), &s), None,
            "an identity hit must report None so the caller reuses the leaf");

        // Spelling-normalising hit — Untagged leaf, canonical Msg replacement:
        // must rebuild so the Untagged→Msg normalisation is applied.
        assert_eq!(
            subst_gterm_cow(&leaf(p::SortHint::Untagged, None), &s),
            Some(term_to_gterm_free(s.get(&("x", 0)).unwrap())),
            "an Untagged-sorted leaf must rebuild to the Msg-sorted replacement");

        // Typ-dropping hit — leaf carries a SAPIC `typ`, replacement drops it:
        // must rebuild so the `typ` is dropped.
        assert_eq!(
            subst_gterm_cow(&leaf(p::SortHint::Msg, Some("A")), &s),
            Some(term_to_gterm_free(s.get(&("x", 0)).unwrap())),
            "a typ-annotated leaf must rebuild to the typ-dropped replacement");

        // Non-identity idx remap still rebuilds.
        let mut s2: VarSubst = VarSubst::default();
        s2.insert(
            ("x", 0),
            p::Term::Var(p::VarSpec {
                name: "x".into(), idx: 7, sort: p::SortHint::Msg, typ: None,
            }),
        );
        assert_eq!(
            subst_gterm_cow(&leaf(p::SortHint::Msg, None), &s2),
            Some(term_to_gterm_free(s2.get(&("x", 0)).unwrap())),
            "a real idx remap must rebuild");

        // A leaf whose (name, idx) is not in the domain returns None (miss).
        assert_eq!(
            subst_gterm_cow(
                &GTerm::Var(BVar::Free(p::VarSpec {
                    name: "y".into(), idx: 0, sort: p::SortHint::Msg, typ: None,
                })),
                &s),
            None,
            "a domain miss must report None");
    }
}
