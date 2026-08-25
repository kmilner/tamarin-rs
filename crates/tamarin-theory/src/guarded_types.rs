// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HS-faithful DeBruijn-indexed types for Guarded formulas.
//!
//! Mirrors `Theory.Constraint.System.Guarded`:
//! - `BVar v = Bound Int | Free v`
//! - `Atom (VTerm c (BVar v))` — atom whose term leaves are BVars
//! - `Guarded s c v = ... | GGuarded Quantifier [s] [Atom (VTerm c (BVar v))] (Guarded s c v)`
//! - `LNGuarded = Guarded (String, LSort) Name LVar`
//!
//! In our model: `s = GBinding` (a `(name, sort)` tuple, no idx),
//! `v = VarSpec` (full LVar).
//! `Bound 0` refers to the innermost binder (rightmost in the binder list);
//! `Bound (k-1)` refers to the outermost.

use crate::atom::{fold_atom, map_atom, ProtoAtom};
use crate::fact::Fact;
use crate::guarded::{GAtom, GBinding, GFact};
use tamarin_parser::ast as p;
use tamarin_utils::cow::cow_map_arc;

/// Mirrors HS `BVar v = Bound Integer | Free v`.
///
/// `Bound(n)` is a DeBruijn index; `n=0` refers to the innermost enclosing
/// binder. `Free(v)` is an unbound LVar (kept with full `VarSpec` info).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BVar {
    Bound(u32),
    Free(p::VarSpec),
}

/// Mirrors HS `VTerm c (BVar v)` — a Term whose Var leaves are `BVar`.
///
/// Structurally identical to `p::Term`, but Var carries a `BVar` instead of
/// a raw `VarSpec`. All other variants are unchanged.
// `Hash` (here and on `Guarded`) is derived alongside the derived
// `PartialEq`, so the impl hashes exactly the fields equality compares — the
// consistency (equal values ⇒ equal hashes) the implied-formula dedup's hash
// prefilter relies on (see `fx_hash_one`).  A `GFact` gets the same
// consistency from `Fact`'s hand-written `Eq`/`Hash` pair.
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum GTerm {
    Var(BVar),
    PubLit(String),
    FreshLit(String),
    NatLit(String),
    Number(u64),
    NumberOne,
    NatOne,
    DhNeutral,
    App(std::sync::Arc<str>, std::sync::Arc<[GTerm]>),
    AlgApp(
        std::sync::Arc<str>,
        std::sync::Arc<GTerm>,
        std::sync::Arc<GTerm>,
    ),
    Pair(std::sync::Arc<[GTerm]>),
    Diff(std::sync::Arc<GTerm>, std::sync::Arc<GTerm>),
    BinOp(p::BinOp, std::sync::Arc<GTerm>, std::sync::Arc<GTerm>),
    PatMatch(std::sync::Arc<GTerm>),
}

/// O(1)-clone helper: wrap a recursive `GTerm` child in `Arc`.
#[inline]
pub fn ga(t: GTerm) -> std::sync::Arc<GTerm> {
    std::sync::Arc::new(t)
}

/// COW combinator for a binary `GTerm` node whose two children are
/// `Arc<GTerm>` (`AlgApp`, `Diff`, non-AC `BinOp`): `None` when both children
/// are unchanged; otherwise materialise each side into an `Arc` slot, wrapping
/// the rebuilt child (`ga`) or cloning the original.  The `Arc<GTerm>`-children
/// specialisation of [`tamarin_utils::cow::cow_pair`] (which works on owned
/// fields); the per-variant `match` arm rebuilds the node from the pair.
pub(crate) fn cow_pair_arc(
    a: &std::sync::Arc<GTerm>,
    a2: Option<GTerm>,
    b: &std::sync::Arc<GTerm>,
    b2: Option<GTerm>,
) -> Option<(std::sync::Arc<GTerm>, std::sync::Arc<GTerm>)> {
    if a2.is_none() && b2.is_none() {
        return None;
    }
    Some((
        a2.map(ga).unwrap_or_else(|| a.clone()),
        b2.map(ga).unwrap_or_else(|| b.clone()),
    ))
}

// =============================================================================
// Conversion: p::Term/Atom/Fact → GTerm/GAtom/GFact (open-form: all Free)
// =============================================================================
//
// Used for terms that arrive without DeBruijn (post-opening, or constructed
// fresh by the constraint solver). All variables become `BVar::Free`.

/// Smart constructor for an n-ary `GTerm::Pair`, enforcing the canonical
/// invariant that the LAST element is never itself a `Pair`.
///
/// RS encodes tuples as n-ary `Pair([t1,..,tn])`, corresponding to HS's
/// binary right-nested `<t1, <t2, .. <t_{n-1}, tn>>>`
/// (`fAppPair (x,y) = fAppNoEq pairSym [x,y]`, Term/Term.hs:161-163, see line 163).  Because HS
/// pairs are binary, `<a,b,<c,d>>` and `<a,b,c,d>` are the SAME term; in
/// RS's n-ary encoding those are the *distinct* trees
/// `Pair([a,b,Pair([c,d])])` and `Pair([a,b,c,d])`.  Substituting a
/// pair-valued var into a tuple tail (e.g. `<'UM3',B,A,matchingComm>` with
/// `matchingComm := <'1','g'^~ex>`) produces the nested form, while the
/// `impliedFormulas` / LNTerm round-trip path produces the flat form.
/// Keeping both defeats the structural `==` dedup in `insertFormula`
/// (`solved_formulas` membership) and the goal-store merge — the re-derived
/// formula does not match the substituted solved one, so it re-inserts an
/// open Disj goal and the prover re-solves a disjunction HS already discharged
/// (UM_three_pass `CK_secure_UM3` blow-up).  Canonicalise to the flat form
/// by splicing a trailing `Pair`, exactly the identity HS gets for free
/// from binary pairs.  Only the LAST element is spliced: a `Pair` in a
/// non-tail position (`<<a,b>,c>` = `pair(pair(a,b),c)`) is a genuinely
/// different term and must be preserved.
pub fn mk_gpair(mut items: Vec<GTerm>) -> GTerm {
    while matches!(items.last(), Some(GTerm::Pair(_))) {
        if let Some(GTerm::Pair(inner)) = items.pop() {
            items.extend(inner.iter().cloned());
        }
    }
    GTerm::Pair(items.into())
}

/// Lift `p::Term` to `GTerm` treating every variable as `Free`.
///
/// HS equivalent: `lTermToBTerm` — `fmapTerm (fmap Free)`.
pub fn term_to_gterm_free(t: &p::Term) -> GTerm {
    match t {
        p::Term::Var(v) => GTerm::Var(BVar::Free(v.clone())),
        p::Term::PubLit(s) => GTerm::PubLit(s.clone()),
        p::Term::FreshLit(s) => GTerm::FreshLit(s.clone()),
        p::Term::NatLit(s) => GTerm::NatLit(s.clone()),
        p::Term::Number(n) => GTerm::Number(*n),
        p::Term::NumberOne => GTerm::NumberOne,
        p::Term::NatOne => GTerm::NatOne,
        p::Term::DhNeutral => GTerm::DhNeutral,
        p::Term::App(n, args) => GTerm::App(
            n.as_str().into(),
            args.iter().map(term_to_gterm_free).collect(),
        ),
        p::Term::AlgApp(n, a, b) => GTerm::AlgApp(
            n.as_str().into(),
            ga(term_to_gterm_free(a)),
            ga(term_to_gterm_free(b)),
        ),
        p::Term::Pair(items) => mk_gpair(items.iter().map(term_to_gterm_free).collect()),
        p::Term::Diff(a, b) => GTerm::Diff(ga(term_to_gterm_free(a)), ga(term_to_gterm_free(b))),
        p::Term::BinOp(op, a, b) => {
            GTerm::BinOp(*op, ga(term_to_gterm_free(a)), ga(term_to_gterm_free(b)))
        }
        p::Term::PatMatch(t) => GTerm::PatMatch(ga(term_to_gterm_free(t))),
    }
}

/// Lift `p::Fact` to `GFact` treating every variable as `Free`.
pub fn fact_to_gfact_free(f: &p::Fact) -> GFact {
    Fact::new(
        crate::elaborate::fact_tag_of(f),
        f.args.iter().map(term_to_gterm_free).collect(),
    )
    .with_annotations(crate::elaborate::copy_fact_annotations(f))
}

/// Lift `p::Atom` to `GAtom` treating every variable as `Free`.
///
/// The guarded atom is sugar-free (`Atom t = ProtoAtom Unit2 t`,
/// Atom.hs:100), and a guarded formula is built from an `LNFormula` whose
/// sugar [`crate::formula::to_lnformula`] has already refused
/// (`formula.rs`), so a predicate atom never reaches here.  The multiset
/// order has no arm of its own at all: [`crate::formula::from_parser`]
/// rewrites it into the `Smaller` predicate, as HS's `smallerp` does
/// (Theory/Text/Parser/Formula.hs:30-38).
pub fn atom_to_gatom_free(a: &p::Atom) -> GAtom {
    match a {
        p::Atom::Eq(s, t) => ProtoAtom::EqE(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::Less(s, t) => ProtoAtom::Less(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::Subterm(s, t) => ProtoAtom::Subterm(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::Action(f, t) => ProtoAtom::Action(term_to_gterm_free(t), fact_to_gfact_free(f)),
        p::Atom::Last(t) => ProtoAtom::Last(term_to_gterm_free(t)),
        p::Atom::Pred(_) | p::Atom::LessMset(_, _) => {
            panic!("atom_to_gatom_free: syntactic sugar in a plain atom")
        }
    }
}

// =============================================================================
// Conversion: GTerm/GAtom/GFact → p::Term/Atom/Fact (close-form: no Bound)
// =============================================================================
//
// Inverse direction: convert from BVar-tagged back to raw `p::Term`. Panics if
// any `Bound` is still present (mirrors HS `bTermToLTerm` / `bvarToLVar`'s
// `boundError`).

/// Convert `GTerm` to `p::Term`, panicking if any `Bound` remains.
///
/// HS equivalent: `bTermToLTerm = fmapTerm (fmap (foldBVar boundError id))`.
pub fn gterm_to_term(g: &GTerm) -> p::Term {
    match g {
        GTerm::Var(BVar::Free(v)) => p::Term::Var(v.clone()),
        GTerm::Var(BVar::Bound(n)) => {
            panic!("gterm_to_term: left-over bound variable Bound({})", n)
        }
        GTerm::PubLit(s) => p::Term::PubLit(s.clone()),
        GTerm::FreshLit(s) => p::Term::FreshLit(s.clone()),
        GTerm::NatLit(s) => p::Term::NatLit(s.clone()),
        GTerm::Number(n) => p::Term::Number(*n),
        GTerm::NumberOne => p::Term::NumberOne,
        GTerm::NatOne => p::Term::NatOne,
        GTerm::DhNeutral => p::Term::DhNeutral,
        GTerm::App(n, args) => {
            p::Term::App(n.to_string(), args.iter().map(gterm_to_term).collect())
        }
        GTerm::AlgApp(n, a, b) => p::Term::AlgApp(
            n.to_string(),
            Box::new(gterm_to_term(a)),
            Box::new(gterm_to_term(b)),
        ),
        GTerm::Pair(items) => p::Term::Pair(items.iter().map(gterm_to_term).collect()),
        GTerm::Diff(a, b) => p::Term::Diff(Box::new(gterm_to_term(a)), Box::new(gterm_to_term(b))),
        GTerm::BinOp(op, a, b) => {
            p::Term::BinOp(*op, Box::new(gterm_to_term(a)), Box::new(gterm_to_term(b)))
        }
        GTerm::PatMatch(t) => p::Term::PatMatch(Box::new(gterm_to_term(t))),
    }
}

/// Convert `GFact` to `p::Fact`, panicking on any leftover Bound.
pub fn gfact_to_fact(g: &GFact) -> p::Fact {
    let (name, persistent) = crate::elaborate::fact_tag_to_parser(&g.tag);
    p::Fact {
        persistent,
        name,
        args: g.terms.iter().map(gterm_to_term).collect(),
        annotations: crate::elaborate::fact_annotations_to_parser(&g.annotations),
    }
}

/// Convert `GAtom` to `p::Atom`, panicking on any leftover Bound.
///
/// HS equivalent: `bvarToLVar`.
pub fn gatom_to_atom(a: &GAtom) -> p::Atom {
    match a {
        ProtoAtom::EqE(s, t) => p::Atom::Eq(gterm_to_term(s), gterm_to_term(t)),
        ProtoAtom::Less(s, t) => p::Atom::Less(gterm_to_term(s), gterm_to_term(t)),
        ProtoAtom::Subterm(s, t) => p::Atom::Subterm(gterm_to_term(s), gterm_to_term(t)),
        ProtoAtom::Action(t, f) => p::Atom::Action(gfact_to_fact(f), gterm_to_term(t)),
        ProtoAtom::Last(t) => p::Atom::Last(gterm_to_term(t)),
        ProtoAtom::Syntactic(_) => panic!("gatom_to_atom: syntactic sugar in a plain atom"),
    }
}

// =============================================================================
// Closing: substitute Free LVars → Bound (entering a binder)
// =============================================================================
//
// HS `substFreeAtom`: replaces Free LVars matching the subst keys with Bound.
// The substitution is `[(LVar, Integer)]` where Integer is the DeBruijn index
// the LVar should become at scope depth 0; deeper scopes shift by `depth`.
//
// Convention from `closeGuarded`: `s = zip (reverse vs) [0..]` — last
// element of `vs` (innermost binder) maps to Bound 0, first element to
// Bound (k-1).

/// `subst_free_term_at_depth(t, s, depth)` — for each Free leaf, look up
/// `(lvar, db)` in `s`; if found, replace with `Bound(db + depth)`.
///
/// HS's `substFreeAtom` uses `lookup x s` with full `LVar` `Eq` (name + idx +
/// **sort**), and every occurrence carries the sort its syntactic position
/// gave it in the parser: a variable in temporal position (`@t`, `last(t)`,
/// `t < t`) is `LSortNode`, every other occurrence is the sort its sigil or
/// its bare spelling named.  Matching on all three separates two distinct
/// binders that share a base name across sorts (e.g. `Ex k m #k. … <h, k> …
/// @ k`: the message-position `k` binds to the `k` binder, the temporal `@k`
/// to the `#k` binder).  When a body reference's sort has no matching binder
/// it stays Free, exactly as HS leaves it unguarded (e.g. `Made(k)` under an
/// `Ex ~k.` binder).
pub fn subst_free_term_at_depth(t: &GTerm, s: &[(p::VarSpec, u32)], depth: u32) -> GTerm {
    match subst_free_term_cow(t, s, depth) {
        Some(g) => g,
        None => t.clone(),
    }
}

/// Copy-on-write core of `subst_free_term_at_depth`.  Returns `None` when no
/// Free leaf in the subtree matches a substitution key, so the caller can
/// reuse the input `Arc`.  These `subst_free`/`subst_bound` paths never call
/// `mk_gpair` (they only retag Var leaves Free↔Bound, never inserting a Pair),
/// so `Pair` reuse is unconditional on "no child changed".
fn subst_free_term_cow(t: &GTerm, s: &[(p::VarSpec, u32)], depth: u32) -> Option<GTerm> {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            for (lv, db) in s {
                if lv.name == v.name && lv.idx == v.idx && lv.sort == v.sort {
                    return Some(GTerm::Var(BVar::Bound(db + depth)));
                }
            }
            None
        }
        GTerm::Var(_)
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => None,
        GTerm::App(n, args) => {
            subst_free_slice(args, s, depth).map(|new| GTerm::App(n.clone(), new))
        }
        GTerm::Pair(items) => subst_free_slice(items, s, depth).map(GTerm::Pair),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(
            a,
            subst_free_term_cow(a, s, depth),
            b,
            subst_free_term_cow(b, s, depth),
        )
        .map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
        GTerm::Diff(a, b) => cow_pair_arc(
            a,
            subst_free_term_cow(a, s, depth),
            b,
            subst_free_term_cow(b, s, depth),
        )
        .map(|(a, b)| GTerm::Diff(a, b)),
        GTerm::BinOp(op, a, b) => cow_pair_arc(
            a,
            subst_free_term_cow(a, s, depth),
            b,
            subst_free_term_cow(b, s, depth),
        )
        .map(|(a, b)| GTerm::BinOp(*op, a, b)),
        GTerm::PatMatch(inner) => {
            subst_free_term_cow(inner, s, depth).map(|g| GTerm::PatMatch(ga(g)))
        }
    }
}

fn subst_free_slice(
    args: &std::sync::Arc<[GTerm]>,
    s: &[(p::VarSpec, u32)],
    depth: u32,
) -> Option<std::sync::Arc<[GTerm]>> {
    cow_map_arc(args, |a| subst_free_term_cow(a, s, depth))
}

/// `subst_free_fact_at_depth(f, s, depth)` — analogous for facts.
pub fn subst_free_fact_at_depth(f: &GFact, s: &[(p::VarSpec, u32)], depth: u32) -> GFact {
    f.map_ref(|a| subst_free_term_at_depth(a, s, depth))
}

/// `subst_free_atom_at_depth(a, s, depth)` — applies the Free→Bound subst to
/// every term leaf in an atom. Mirrors HS `substFreeAtom` (with the i+j shift
/// applied externally by the caller — pass `depth` for the j term).
pub fn subst_free_atom_at_depth(a: &GAtom, s: &[(p::VarSpec, u32)], depth: u32) -> GAtom {
    map_atom(a, &mut |t| subst_free_term_at_depth(t, s, depth))
}

// =============================================================================
// Opening: substitute Bound → Free LVars (exiting a binder)
// =============================================================================
//
// HS `substBoundAtom`: replaces Bound `i` with Free `s(i)`. The
// substitution is `[(Integer, LVar)]`. From `openGuarded`:
// `subst xs = zip [0..] (reverse xs)` — Bound 0 → xs[k-1] (innermost
// becomes last-allocated fresh LVar).
//
// At depth `j`, a Bound that refers to the outermost target binder appears
// as `Bound(i+j)`, so we look up using the shifted index.

/// `subst_bound_term_at_depth(t, s, depth)` — for each `Bound(n)` leaf,
/// look up `(i, lvar)` where `n = i + depth`; if found, replace with
/// `Free(lvar)`.
pub fn subst_bound_term_at_depth(t: &GTerm, s: &[(u32, p::VarSpec)], depth: u32) -> GTerm {
    match subst_bound_term_cow(t, s, depth) {
        Some(g) => g,
        None => t.clone(),
    }
}

/// Copy-on-write core of `subst_bound_term_at_depth` (see
/// `subst_free_term_cow` for the COW rationale).  Returns `None` when no
/// `Bound` leaf in the subtree matches a substitution key.
fn subst_bound_term_cow(t: &GTerm, s: &[(u32, p::VarSpec)], depth: u32) -> Option<GTerm> {
    match t {
        GTerm::Var(BVar::Bound(n)) => {
            for (i, lv) in s {
                if let Some(target) = i.checked_add(depth) {
                    if target == *n {
                        return Some(GTerm::Var(BVar::Free(lv.clone())));
                    }
                }
            }
            None
        }
        GTerm::Var(_)
        | GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => None,
        GTerm::App(n, args) => {
            subst_bound_slice(args, s, depth).map(|new| GTerm::App(n.clone(), new))
        }
        GTerm::Pair(items) => subst_bound_slice(items, s, depth).map(GTerm::Pair),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(
            a,
            subst_bound_term_cow(a, s, depth),
            b,
            subst_bound_term_cow(b, s, depth),
        )
        .map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
        GTerm::Diff(a, b) => cow_pair_arc(
            a,
            subst_bound_term_cow(a, s, depth),
            b,
            subst_bound_term_cow(b, s, depth),
        )
        .map(|(a, b)| GTerm::Diff(a, b)),
        GTerm::BinOp(op, a, b) => cow_pair_arc(
            a,
            subst_bound_term_cow(a, s, depth),
            b,
            subst_bound_term_cow(b, s, depth),
        )
        .map(|(a, b)| GTerm::BinOp(*op, a, b)),
        GTerm::PatMatch(inner) => {
            subst_bound_term_cow(inner, s, depth).map(|g| GTerm::PatMatch(ga(g)))
        }
    }
}

fn subst_bound_slice(
    args: &std::sync::Arc<[GTerm]>,
    s: &[(u32, p::VarSpec)],
    depth: u32,
) -> Option<std::sync::Arc<[GTerm]>> {
    cow_map_arc(args, |a| subst_bound_term_cow(a, s, depth))
}

/// `subst_bound_fact_at_depth(f, s, depth)` — analogous for facts.
pub fn subst_bound_fact_at_depth(f: &GFact, s: &[(u32, p::VarSpec)], depth: u32) -> GFact {
    f.map_ref(|a| subst_bound_term_at_depth(a, s, depth))
}

/// `subst_bound_atom_at_depth(a, s, depth)` — applies the Bound→Free subst.
/// Mirrors HS `substBoundAtom` (i+j shift baked into the depth parameter).
pub fn subst_bound_atom_at_depth(a: &GAtom, s: &[(u32, p::VarSpec)], depth: u32) -> GAtom {
    map_atom(a, &mut |t| subst_bound_term_at_depth(t, s, depth))
}

// =============================================================================
// closeGuarded / openGuarded helpers for binder lists
// =============================================================================

/// Build the substitution `[(LVar, Integer)]` used by `closeGuarded` from a
/// binder list. Mirrors HS `s = zip (reverse vs) [0..]`.
///
/// Given `vs = [v0, v1, ..., v_{k-1}]` (outer→inner lexical order),
/// returns `[(v_{k-1}, 0), (v_{k-2}, 1), ..., (v_0, k-1)]`.
pub fn close_subst(vs: &[p::VarSpec]) -> Vec<(p::VarSpec, u32)> {
    let k = vs.len();
    vs.iter()
        .enumerate()
        .rev()
        .map(|(i, v)| (v.clone(), (k - 1 - i) as u32))
        .collect()
}

/// Build the substitution `[(Integer, LVar)]` used by `openGuarded` from a
/// freshly-allocated LVar list. Mirrors HS `subst xs = zip [0..] (reverse xs)`.
///
/// Given `xs = [x0, x1, ..., x_{k-1}]` (binder lexical order),
/// returns `[(0, x_{k-1}), (1, x_{k-2}), ..., (k-1, x_0)]`.
pub fn open_subst(xs: &[p::VarSpec]) -> Vec<(u32, p::VarSpec)> {
    xs.iter()
        .rev()
        .enumerate()
        .map(|(i, v)| (i as u32, v.clone()))
        .collect()
}

/// Project a binder's metadata. HS `vs' = map (lvarName &&& lvarSort) vs`
/// (Guarded.hs:384).
pub fn lvar_to_binding(v: &p::VarSpec) -> GBinding {
    (v.name.clone(), v.sort)
}

// =============================================================================
// Walks: collect free LVars / map over free LVars
// =============================================================================

/// Push every Free LVar reachable from a term into `out`. Bound vars are
/// skipped.
pub fn collect_free_term(t: &GTerm, out: &mut Vec<p::VarSpec>) {
    match t {
        GTerm::Var(BVar::Free(v)) => out.push(v.clone()),
        GTerm::Var(BVar::Bound(_)) => {}
        GTerm::App(_, args) | GTerm::Pair(args) => {
            for a in args.iter() {
                collect_free_term(a, out);
            }
        }
        GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
            collect_free_term(a, out);
            collect_free_term(b, out);
        }
        GTerm::PatMatch(t) => collect_free_term(t, out),
        // Literals carry no variable.  Matched exhaustively (no wildcard) so a
        // new `GTerm` variant forces a decision here.
        GTerm::PubLit(_)
        | GTerm::FreshLit(_)
        | GTerm::NatLit(_)
        | GTerm::Number(_)
        | GTerm::NumberOne
        | GTerm::NatOne
        | GTerm::DhNeutral => {}
    }
}

/// Push every Free LVar reachable from an atom into `out`, in the order HS's
/// `Foldable ProtoAtom` (Atom.hs:129-136) visits the atom's terms.
pub fn collect_free_atom(a: &GAtom, out: &mut Vec<p::VarSpec>) {
    fold_atom(a, &mut |t| collect_free_term(t, out));
}

/// Apply a remapping to every Free LVar in a term. Bound vars are untouched.
pub fn map_free_term<F: FnMut(&p::VarSpec) -> p::VarSpec>(t: &GTerm, f: &mut F) -> GTerm {
    match t {
        GTerm::Var(BVar::Free(v)) => GTerm::Var(BVar::Free(f(v))),
        GTerm::Var(b) => GTerm::Var(b.clone()),
        GTerm::PubLit(s) => GTerm::PubLit(s.clone()),
        GTerm::FreshLit(s) => GTerm::FreshLit(s.clone()),
        GTerm::NatLit(s) => GTerm::NatLit(s.clone()),
        GTerm::Number(n) => GTerm::Number(*n),
        GTerm::NumberOne => GTerm::NumberOne,
        GTerm::NatOne => GTerm::NatOne,
        GTerm::DhNeutral => GTerm::DhNeutral,
        GTerm::App(n, args) => GTerm::App(
            n.clone(),
            args.iter().map(|a| map_free_term(a, f)).collect(),
        ),
        GTerm::AlgApp(n, a, b) => {
            GTerm::AlgApp(n.clone(), ga(map_free_term(a, f)), ga(map_free_term(b, f)))
        }
        GTerm::Pair(items) => GTerm::Pair(items.iter().map(|a| map_free_term(a, f)).collect()),
        GTerm::Diff(a, b) => GTerm::Diff(ga(map_free_term(a, f)), ga(map_free_term(b, f))),
        GTerm::BinOp(op, a, b) => {
            GTerm::BinOp(*op, ga(map_free_term(a, f)), ga(map_free_term(b, f)))
        }
        GTerm::PatMatch(t) => GTerm::PatMatch(ga(map_free_term(t, f))),
    }
}

/// Apply a remapping to every Free LVar in a fact.
pub fn map_free_fact<F: FnMut(&p::VarSpec) -> p::VarSpec>(g: &GFact, f: &mut F) -> GFact {
    g.map_ref(|a| map_free_term(a, f))
}

/// Apply a remapping to every Free LVar in an atom, in the order HS's
/// `Traversable ProtoAtom` (Atom.hs:138-145) visits the atom's terms.
pub fn map_free_atom<F: FnMut(&p::VarSpec) -> p::VarSpec>(a: &GAtom, f: &mut F) -> GAtom {
    map_atom(a, &mut |t| map_free_term(t, f))
}

// =============================================================================
// Lowering an opened locally-nameless atom into the GTerm world
// =============================================================================

/// The parser-AST spelling of an atom of a locally-nameless formula whose
/// binders are all opened: read it over plain `LVar`s
/// ([`crate::guarded::bvar_to_lvar`]), project it
/// (`crate::elaborate::lnatom_to_parser`), give the three nullary
/// constants their parser-AST constructors back ([`restore_nullary_constants`])
/// and put the AC argument lists into canonical order
/// ([`crate::elaborate::canonicalize_ac_in_atom`]).
///
/// The canonicalisation is what makes the two spellings meet.  An internal
/// `FApp (AC f)` holds a flat, sorted argument list (Term/Term/Raw.hs:118-129),
/// which `lnterm_to_parser` writes as a LEFT-folded `BinOp` chain, while the
/// parser AST the guarded store is built from carries the sorted RIGHT fold
/// `canonicalize_ac_in_pterm` produces.
///
/// A binary application arrives in the prefix form `App(name, [a, b])`: an
/// internal term holds one `fAppNoEq` for both the prefix and the braced
/// source spelling (HS `naryOpApp`/`binaryAlgApp`,
/// Theory/Text/Parser/Term.hs:88-106,:109-121), so it does not record the
/// source spelling.  The two share a [`crate::guarded::cmp_term`] key
/// and a printed form (`prettyTerm` has no brace case,
/// Term/Term.hs:298-327); they differ under the derived `PartialEq`.
pub fn blnatom_to_parser(a: &crate::atom::Atom<crate::formula::BLNTerm>) -> p::Atom {
    let projected = crate::elaborate::lnatom_to_parser(&crate::guarded::bvar_to_lvar(a));
    crate::elaborate::canonicalize_ac_in_atom(&crate::macro_expand::map_atom_terms(
        &projected,
        &restore_nullary_constants,
    ))
}

/// `one`, `tone` and `DH_neutral` back in the parser AST's own constructors.
///
/// The three are nullary `NoEq` symbols in a term
/// (Term/Term.hs:147-148,150-151,156-158), which is all `lnterm_to_parser`
/// can see, and the parser AST spells each of them as its own variant, which
/// [`term_to_gterm_free`] carries into [`GTerm::NumberOne`],
/// [`GTerm::NatOne`] and [`GTerm::DhNeutral`].  The variants and the nullary
/// `App` share a [`crate::guarded::cmp_term`] key, so the rewrite moves no AC
/// argument; it decides the derived `PartialEq` and `Hash` the solver's
/// membership tests use.
fn restore_nullary_constants(t: &p::Term) -> p::Term {
    match t {
        p::Term::App(n, args) if args.is_empty() => match n.as_str() {
            "one" => p::Term::NumberOne,
            "tone" => p::Term::NatOne,
            "DH_neutral" => p::Term::DhNeutral,
            _ => t.clone(),
        },
        p::Term::App(n, args) => p::Term::App(
            n.clone(),
            args.iter().map(restore_nullary_constants).collect(),
        ),
        p::Term::AlgApp(n, a, b) => p::Term::AlgApp(
            n.clone(),
            Box::new(restore_nullary_constants(a)),
            Box::new(restore_nullary_constants(b)),
        ),
        p::Term::Pair(items) => {
            p::Term::Pair(items.iter().map(restore_nullary_constants).collect())
        }
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(restore_nullary_constants(a)),
            Box::new(restore_nullary_constants(b)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(restore_nullary_constants(a)),
            Box::new(restore_nullary_constants(b)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(restore_nullary_constants(inner))),
        p::Term::Var(_)
        | p::Term::PubLit(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => t.clone(),
    }
}

/// [`blnatom_to_parser`] lifted into the `GTerm` world, all variables free —
/// HS `GAto a` at an atom whose `BVar`s are all `Free` (Guarded.hs:121,482).
pub fn blnatom_to_gatom(a: &crate::atom::Atom<crate::formula::BLNTerm>) -> GAtom {
    atom_to_gatom_free(&blnatom_to_parser(a))
}

// =============================================================================
// Unit tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    fn vs(name: &str, idx: u64) -> p::VarSpec {
        p::VarSpec {
            name: name.to_string(),
            idx,
            sort: LSort::Msg,
            typ: None,
        }
    }

    fn vs_node(name: &str, idx: u64) -> p::VarSpec {
        p::VarSpec {
            name: name.to_string(),
            idx,
            sort: LSort::Node,
            typ: None,
        }
    }

    /// The guarded atom is sugar-free (Atom.hs:98-100), and `formula_to_guarded`
    /// reads an `LNFormula` whose sugar `toLNFormula` (Theory/Model/Formula.hs:369-373) has
    /// already refused, so a predicate atom cannot reach the lift.
    #[test]
    #[should_panic(expected = "syntactic sugar in a plain atom")]
    fn atom_to_gatom_free_rejects_a_predicate_atom() {
        atom_to_gatom_free(&p::Atom::Pred(p::Fact {
            persistent: false,
            name: "Smaller".to_string(),
            args: vec![p::Term::Var(vs("x", 0)), p::Term::Var(vs("y", 0))],
            annotations: vec![],
        }));
    }

    /// The multiset order is the `Smaller` predicate by the time a formula is
    /// closed (`smallerp`, Theory/Text/Parser/Formula.hs:30-38), so its parser
    /// spelling never reaches the lift either.
    #[test]
    #[should_panic(expected = "syntactic sugar in a plain atom")]
    fn atom_to_gatom_free_rejects_a_multiset_order_atom() {
        atom_to_gatom_free(&p::Atom::LessMset(
            p::Term::Var(vs("x", 0)),
            p::Term::Var(vs("y", 0)),
        ));
    }

    // =========================================================================
    // blnatom_to_gatom
    // =========================================================================

    mod blnatom {
        use super::*;
        use crate::atom::{Atom, ProtoAtom};
        use tamarin_term::function_symbols::{
            AcFctSym, AcSym, Constructability, NdcState, Privacy,
        };
        use tamarin_term::lterm::{BVar as TBVar, LVar};
        use tamarin_term::term::{f_app_ac, f_app_no_eq};
        use tamarin_term::vterm::var_term;

        /// A free message variable of the locally-nameless term type.
        fn v(name: &str) -> crate::formula::BLNTerm {
            var_term(TBVar::Free(LVar::new(name, LSort::Msg, 0)))
        }

        /// The lowered left operand of an equality atom.
        fn lowered(t: crate::formula::BLNTerm) -> GTerm {
            let a: Atom<crate::formula::BLNTerm> = ProtoAtom::EqE(t, v("zzz"));
            match blnatom_to_gatom(&a) {
                ProtoAtom::EqE(l, _) => l,
                other => panic!("an equality atom lowers to an equality atom, got {other:?}"),
            }
        }

        fn user_ac() -> AcFctSym {
            AcFctSym::new(
                b"add".to_vec(),
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            )
        }

        /// An internal AC application holds a flat sorted argument list;
        /// the guarded store holds the RIGHT-leaning `BinOp` chain
        /// `canonicalize_ac_in_pterm` folds, so `x ++ y ++ z` nests to the
        /// right.
        #[test]
        fn blnatom_to_gatom_right_folds_a_three_element_ac_chain() {
            let t = f_app_ac(AcSym::Union, vec![v("x"), v("y"), v("z")]);
            let var = |n: &str| ga(GTerm::Var(BVar::Free(vs(n, 0))));
            assert_eq!(
                lowered(t),
                GTerm::BinOp(
                    p::BinOp::Union,
                    var("x"),
                    ga(GTerm::BinOp(p::BinOp::Union, var("y"), var("z"))),
                )
            );
        }

        /// HS builds `<a, b, c>` as `pair(a, pair(b, c))`; the guarded store
        /// holds the flat n-ary `Pair` [`mk_gpair`] splices out of the right
        /// spine, so the nested spelling and the flat one are one value.
        #[test]
        fn blnatom_to_gatom_splices_a_trailing_pair() {
            let pair = |a, b| f_app_no_eq(tamarin_term::function_symbols::pair_sym(), vec![a, b]);
            let t = pair(v("a"), pair(v("b"), v("c")));
            assert_eq!(
                lowered(t),
                GTerm::Pair(
                    vec![
                        GTerm::Var(BVar::Free(vs("a", 0))),
                        GTerm::Var(BVar::Free(vs("b", 0))),
                        GTerm::Var(BVar::Free(vs("c", 0))),
                    ]
                    .into()
                )
            );
        }

        /// HS renders `exp(a, b)` as the infix `a^b` (Term/Term.hs:310), and
        /// the parser AST spells that `BinOp(Exp, ..)`.
        #[test]
        fn blnatom_to_gatom_writes_exp_as_the_infix_operator() {
            let t = f_app_no_eq(
                tamarin_term::function_symbols::exp_sym(),
                vec![v("a"), v("b")],
            );
            assert_eq!(
                lowered(t),
                GTerm::BinOp(
                    p::BinOp::Exp,
                    ga(GTerm::Var(BVar::Free(vs("a", 0)))),
                    ga(GTerm::Var(BVar::Free(vs("b", 0)))),
                )
            );
        }

        /// HS renders a user-`[AC]` symbol infix (Term/Term.hs:305), which
        /// the parser AST spells `BinOp(AcFct(name), ..)`.
        ///
        /// The nullary arm of that HS case (Term/Term.hs:304) has no reachable
        /// term here: rebuilding a term through `fApp` rejects an empty AC
        /// argument list (`fAppAC`, Term/Term/Raw.hs:120), and every read of
        /// an atom of a locally-nameless formula rebuilds that way
        /// (`bvarToLVar`'s `fmapTerm`, Guarded.hs:322-327).
        #[test]
        fn blnatom_to_gatom_writes_a_user_ac_symbol_as_its_infix_chain() {
            let t: crate::formula::BLNTerm =
                f_app_ac(AcSym::AcFct(user_ac()), vec![v("x"), v("y")]);
            assert_eq!(
                lowered(t),
                GTerm::BinOp(
                    p::BinOp::AcFct(tamarin_term::intern::intern_str("add")),
                    ga(GTerm::Var(BVar::Free(vs("x", 0)))),
                    ga(GTerm::Var(BVar::Free(vs("y", 0)))),
                )
            );
        }

        /// An internal term holds one `fAppNoEq` for `op(t1, t2)` and for
        /// `op{t1}t2` (HS `naryOpApp`/`binaryAlgApp`,
        /// Theory/Text/Parser/Term.hs:88-106,:109-121), so the lowering
        /// writes the prefix `GTerm::App` and never the parser AST's braced
        /// `GTerm::AlgApp`.
        #[test]
        fn blnatom_to_gatom_writes_a_binary_application_in_prefix_form() {
            let sdec = tamarin_term::function_symbols::NoEqSym::new(
                b"sdec".to_vec(),
                2,
                Privacy::Public,
                Constructability::Destructor,
            );
            assert_eq!(
                lowered(f_app_no_eq(sdec, vec![v("m"), v("k")])),
                GTerm::App(
                    "sdec".into(),
                    vec![
                        GTerm::Var(BVar::Free(vs("m", 0))),
                        GTerm::Var(BVar::Free(vs("k", 0))),
                    ]
                    .into(),
                )
            );
        }

        /// `one`, `tone` and `DH_neutral` are nullary `NoEq` symbols in a
        /// term and dedicated variants in the parser AST and in `GTerm`
        /// ([`restore_nullary_constants`]).
        #[test]
        fn blnatom_to_gatom_restores_the_nullary_constants() {
            let sym = tamarin_term::function_symbols::one_sym;
            assert_eq!(lowered(f_app_no_eq(sym(), vec![])), GTerm::NumberOne);
            assert_eq!(
                lowered(f_app_no_eq(
                    tamarin_term::function_symbols::nat_one_sym(),
                    vec![]
                )),
                GTerm::NatOne
            );
            assert_eq!(
                lowered(f_app_no_eq(
                    tamarin_term::function_symbols::dh_neutral_sym(),
                    vec![]
                )),
                GTerm::DhNeutral
            );
        }
    }

    #[test]
    fn term_round_trip_no_bound() {
        let t = p::Term::App(
            "f".to_string(),
            vec![p::Term::Var(vs("x", 0)), p::Term::Var(vs("y", 1))],
        );
        let g = term_to_gterm_free(&t);
        assert_eq!(t, gterm_to_term(&g));
    }

    /// This is [`mk_gpair`]'s canonical invariant.  `mk_gpair` splices a
    /// trailing `Pair`, and it repeats the splice as often as needed.  The
    /// reason is that RS's n-ary `Pair` stands for HS's right-nested binary
    /// `fAppPair`.  In HS, `<a, <b, c>>` and `<a, b, c>` are one term.  Two
    /// spellings of that term here would defeat the structural `==` that
    /// `insertFormula` and the goal-store merge rely on.  A `Pair` in a
    /// non-tail position is a genuinely different term (`pair(pair(a,b),c)`).
    /// It must survive untouched.
    #[test]
    fn mk_gpair_splices_only_a_trailing_pair() {
        let lit = |s: &str| GTerm::PubLit(s.to_string());
        let flat = GTerm::Pair(vec![lit("a"), lit("b"), lit("c")].into());
        assert_eq!(
            mk_gpair(vec![lit("a"), GTerm::Pair(vec![lit("b"), lit("c")].into())]),
            flat,
            "a trailing pair is spliced into the tail"
        );
        assert_eq!(
            mk_gpair(vec![
                lit("a"),
                GTerm::Pair(vec![lit("b"), GTerm::Pair(vec![lit("c")].into())].into()),
            ]),
            flat,
            "splicing repeats while the new tail is itself a pair"
        );
        let head_nested =
            GTerm::Pair(vec![GTerm::Pair(vec![lit("a"), lit("b")].into()), lit("c")].into());
        assert_eq!(
            mk_gpair(vec![GTerm::Pair(vec![lit("a"), lit("b")].into()), lit("c")]),
            head_nested,
            "a pair in a non-tail position is a different term"
        );
        // `term_to_gterm_free` routes every parser `Pair` through `mk_gpair`.
        // The two source spellings therefore lift to the same `GTerm`.
        let p_lit = |s: &str| p::Term::PubLit(s.to_string());
        assert_eq!(
            term_to_gterm_free(&p::Term::Pair(vec![
                p_lit("a"),
                p::Term::Pair(vec![p_lit("b"), p_lit("c")]),
            ])),
            flat
        );
    }

    #[test]
    fn atom_round_trip_no_bound() {
        let a = p::Atom::Eq(p::Term::Var(vs("x", 0)), p::Term::Var(vs("y", 1)));
        let g = atom_to_gatom_free(&a);
        assert_eq!(a, gatom_to_atom(&g));
    }

    /// `closeGuarded` then `openGuarded` reproduces the original (with the
    /// caveat that LVar identities are preserved). HS:
    ///
    /// ```text
    /// closeGuarded vs as gf
    ///   = GGuarded ... (substFreeAtom s as') (substFree s gf')
    /// openGuarded (GGuarded ...) = (xs, substBoundAtom (subst xs) as, substBound ...)
    /// ```
    ///
    /// If we pick `xs = vs`, the round-trip is identity.
    #[test]
    fn close_then_open_atom_identity() {
        // Forall x. P(x)  -- one binder, one Free reference
        let x = vs("x", 0);
        let p_atom = atom_to_gatom_free(&p::Atom::Action(
            p::Fact {
                persistent: false,
                name: "P".to_string(),
                args: vec![p::Term::Var(x.clone())],
                annotations: vec![],
            },
            p::Term::Var(vs_node("t", 0)),
        ));

        // close: x → Bound 0 at depth 0
        let close_s = close_subst(std::slice::from_ref(&x));
        let closed = subst_free_atom_at_depth(&p_atom, &close_s, 0);

        // verify x became Bound(0) in the closed form
        match &closed {
            ProtoAtom::Action(_, f) => match &f.terms[0] {
                GTerm::Var(BVar::Bound(n)) => assert_eq!(*n, 0),
                other => panic!("expected Bound(0), got {:?}", other),
            },
            _ => panic!("expected Action"),
        }

        // open: Bound 0 → x (reuse same LVar identity)
        let open_s = open_subst(std::slice::from_ref(&x));
        let opened = subst_bound_atom_at_depth(&closed, &open_s, 0);

        // round-trip equality
        assert_eq!(opened, p_atom);
    }

    #[test]
    fn close_subst_innermost_is_bound_zero() {
        let binders = vec![vs("a", 0), vs("b", 1), vs("c", 2)];
        // outer→inner: a, b, c
        // HS `zip (reverse vs) [0..]` ⇒ [(c, 0), (b, 1), (a, 2)]
        let s = close_subst(&binders);
        assert_eq!(s.len(), 3);
        assert_eq!(s[0].0.name, "c");
        assert_eq!(s[0].1, 0);
        assert_eq!(s[1].0.name, "b");
        assert_eq!(s[1].1, 1);
        assert_eq!(s[2].0.name, "a");
        assert_eq!(s[2].1, 2);
    }

    #[test]
    fn open_subst_bound_zero_is_innermost() {
        let binders = vec![vs("a", 0), vs("b", 1), vs("c", 2)];
        // HS `zip [0..] (reverse xs)` ⇒ [(0, c), (1, b), (2, a)]
        let s = open_subst(&binders);
        assert_eq!(s.len(), 3);
        assert_eq!(s[0].0, 0);
        assert_eq!(s[0].1.name, "c");
        assert_eq!(s[1].0, 1);
        assert_eq!(s[1].1.name, "b");
        assert_eq!(s[2].0, 2);
        assert_eq!(s[2].1.name, "a");
    }

    /// Nested binder shift: `forall x. forall y. P(x, y)`.
    /// At the outer layer, the inner-binder's body sees y as `Bound 0`
    /// (innermost) and x as `Bound 0` from its own scope-1 perspective.
    /// After closing both layers, the body atom P(x, y) becomes
    /// P(Bound 1, Bound 0) — x is one binder deeper, y is at the
    /// innermost.
    ///
    /// This test only exercises subst_free at depth (the full
    /// Guarded-tree walk lives in `guarded.rs::subst_free_guarded`).
    #[test]
    fn nested_close_shift() {
        // Suppose we already closed `forall y. P(x, y)` — y is Bound 0,
        // x is still Free.
        let x = vs("x", 100);
        let mut inner_body = ProtoAtom::Action(
            GTerm::Var(BVar::Free(vs_node("t", 0))),
            GFact::new(
                crate::fact::FactTag::Proto(
                    crate::fact::Multiplicity::Linear,
                    tamarin_term::intern::intern_str("P"),
                    2,
                ),
                vec![
                    GTerm::Var(BVar::Free(x.clone())),
                    GTerm::Var(BVar::Bound(0)),
                ],
            ),
        );

        // Now close the outer `forall x.` — depth becomes 1 because we're
        // ALREADY inside one (the inner) binder.  Outer's binder list = [x].
        // HS substFree applies at the OUTER LAYER first, then mapGuardedAtoms
        // hands inner atoms a depth ≥ 1.  Substitution: x → Bound 0 at depth 0,
        // so at depth 1 it's Bound 1.
        let close_s = close_subst(std::slice::from_ref(&x));
        inner_body = subst_free_atom_at_depth(&inner_body, &close_s, 1);

        // x should now be Bound(1); y is still Bound(0).
        match &inner_body {
            ProtoAtom::Action(_, f) => {
                match &f.terms[0] {
                    GTerm::Var(BVar::Bound(n)) => assert_eq!(*n, 1, "x should shift to Bound(1)"),
                    other => panic!("expected Bound(1), got {:?}", other),
                }
                match &f.terms[1] {
                    GTerm::Var(BVar::Bound(n)) => assert_eq!(*n, 0, "y stays Bound(0)"),
                    other => panic!("expected Bound(0), got {:?}", other),
                }
            }
            _ => panic!("expected Action"),
        }
    }

    /// Alpha-equivalence test: `forall x. P(x)` and `forall y. P(y)` should
    /// produce IDENTICAL closed atoms (modulo binding name, which lives in the
    /// GBinding/GGuarded layer — stripped of idx — not in the GAtom).
    #[test]
    fn close_alpha_equivalence() {
        let x = vs("x", 0);
        let y = vs("y", 7);

        let body_x = atom_to_gatom_free(&p::Atom::Action(
            p::Fact {
                persistent: false,
                name: "P".to_string(),
                args: vec![p::Term::Var(x.clone())],
                annotations: vec![],
            },
            p::Term::Var(vs_node("t", 0)),
        ));
        let body_y = atom_to_gatom_free(&p::Atom::Action(
            p::Fact {
                persistent: false,
                name: "P".to_string(),
                args: vec![p::Term::Var(y.clone())],
                annotations: vec![],
            },
            p::Term::Var(vs_node("t", 0)),
        ));

        let closed_x = subst_free_atom_at_depth(&body_x, &close_subst(&[x]), 0);
        let closed_y = subst_free_atom_at_depth(&body_y, &close_subst(&[y]), 0);

        // The two closed forms differ only in their binding NAME (which lives
        // in the GBinding/GGuarded, not in GAtom). At the atom level, both
        // contain P(Bound(0)) — structurally identical.
        assert_eq!(closed_x, closed_y);
    }

    #[test]
    fn collect_free_skips_bound() {
        let t = GTerm::App(
            "f".into(),
            vec![
                GTerm::Var(BVar::Free(vs("x", 0))),
                GTerm::Var(BVar::Bound(0)),
                GTerm::Var(BVar::Free(vs("y", 1))),
            ]
            .into(),
        );
        let mut out = Vec::new();
        collect_free_term(&t, &mut out);
        assert_eq!(out.len(), 2);
        assert_eq!(out[0].name, "x");
        assert_eq!(out[1].name, "y");
    }

    #[test]
    fn map_free_skips_bound() {
        let t = GTerm::App(
            "f".into(),
            vec![
                GTerm::Var(BVar::Free(vs("x", 0))),
                GTerm::Var(BVar::Bound(0)),
            ]
            .into(),
        );
        let mapped = map_free_term(&t, &mut |v: &p::VarSpec| p::VarSpec {
            name: v.name.clone(),
            idx: v.idx + 100,
            sort: v.sort,
            typ: v.typ.clone(),
        });
        match &mapped {
            GTerm::App(_, args) => {
                match &args[0] {
                    GTerm::Var(BVar::Free(v)) => assert_eq!(v.idx, 100),
                    other => panic!("free var should be remapped: {:?}", other),
                }
                match &args[1] {
                    GTerm::Var(BVar::Bound(0)) => {}
                    other => panic!("bound should pass through: {:?}", other),
                }
            }
            _ => panic!("expected App"),
        }
    }
}
