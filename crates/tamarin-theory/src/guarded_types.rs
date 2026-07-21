// Currently GPL 3.0 until granted permission by the following authors:
//   only minor contributions per cited ranges (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Sapic/Term.hs

//! HS-faithful DeBruijn-indexed types for Guarded formulas.
//!
//! Mirrors `Theory.Constraint.System.Guarded`:
//! - `BVar v = Bound Int | Free v`
//! - `Atom (VTerm c (BVar v))` — atom whose term leaves are BVars
//! - `Guarded s c v = ... | GGuarded Quantifier [s] [Atom (VTerm c (BVar v))] (Guarded s c v)`
//! - `LNGuarded = Guarded (String, LSort) Name LVar`
//!
//! In our model: `s = GBinding` (name+sort, no idx), `v = VarSpec` (full LVar).
//! `Bound 0` refers to the innermost binder (rightmost in the binder list);
//! `Bound (k-1)` refers to the outermost.

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

/// Mirrors HS `[s] = [(String, LSort)]` — binder lacking idx.
///
/// HS `s = (String, LSort)`; the position of the binding in the `[s]` list
/// determines its DeBruijn index. We keep `name` for display/parsing but
/// the binding's identity is purely positional.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GBinding {
    pub name: String,
    pub sort: p::SortHint,
}

/// Mirrors HS `VTerm c (BVar v)` — a Term whose Var leaves are `BVar`.
///
/// Structurally identical to `p::Term`, but Var carries a `BVar` instead of
/// a raw `VarSpec`. All other variants are unchanged.
// `Hash` (here and on `GFact`/`GAtom`/`Guarded`) is derived alongside the
// derived `PartialEq`, so the impl hashes exactly the fields equality
// compares — the consistency (equal values ⇒ equal hashes) the implied-
// formula dedup's hash prefilter relies on (see `fx_hash_one`).
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
    AlgApp(std::sync::Arc<str>, std::sync::Arc<GTerm>, std::sync::Arc<GTerm>),
    Pair(std::sync::Arc<[GTerm]>),
    Diff(std::sync::Arc<GTerm>, std::sync::Arc<GTerm>),
    BinOp(p::BinOp, std::sync::Arc<GTerm>, std::sync::Arc<GTerm>),
    PatMatch(std::sync::Arc<GTerm>),
}

/// O(1)-clone helper: wrap a recursive `GTerm` child in `Arc`.
#[inline]
pub fn ga(t: GTerm) -> std::sync::Arc<GTerm> { std::sync::Arc::new(t) }

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
    Some((a2.map(ga).unwrap_or_else(|| a.clone()), b2.map(ga).unwrap_or_else(|| b.clone())))
}

/// Mirrors HS `Fact (VTerm c (BVar v))`.
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct GFact {
    pub persistent: bool,
    pub name: String,
    pub args: std::sync::Arc<[GTerm]>,
    pub annotations: Vec<p::FactAnnotation>,
}

/// Mirrors HS `Atom (VTerm c (BVar v))`.
///
/// Same variant set as `p::Atom`, but terms are `GTerm`.
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum GAtom {
    Eq(GTerm, GTerm),
    Less(GTerm, GTerm),
    LessMset(GTerm, GTerm),
    Subterm(GTerm, GTerm),
    Action(GFact, GTerm),
    Last(GTerm),
    Pred(GFact),
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
/// (`fAppPair (x,y) = fAppNoEq pairSym [x,y]`, Term.hs:140-141, see line 142).  Because HS
/// pairs are binary, `<a,b,<c,d>>` and `<a,b,c,d>` are the SAME term; in
/// RS's n-ary encoding those are the *distinct* trees
/// `Pair([a,b,Pair([c,d])])` and `Pair([a,b,c,d])`.  Substituting a
/// pair-valued var into a tuple tail (e.g. `<'UM3',B,A,matchingComm>` with
/// `matchingComm := <'1','g'^~ex>`) produces the nested form, while the
/// `impliedFormulas` / LNTerm round-trip path produces the flat form.
/// Keeping both defeats the structural `==` dedup in `insertFormula`
/// (`solved_formulas` membership) and the goal-store
/// `canonical_goal_for_dedup` merge — the re-derived formula no longer
/// matches the substituted solved one, so it re-inserts an open Disj goal
/// and the prover re-solves a disjunction HS already discharged
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
        // A bare identifier that names a user-declared 0-arity function is a
        // CONSTANT (nullary application), not a variable — mirror HS's
        // `fAppNoEq sym []` and the nullary-fun branch of `term_to_lnterm`
        // (elaborate.rs:1558).  Without
        // this, a declared `true/0`/`false/0` used inside a formula (e.g.
        // OIDC_Implicit's `Verified(...,true)` / `...,false)` restrictions,
        // conjoined into a lemma's proof obligation) is lifted to a FREE
        // variable, so `free_vars`/`is_closed` see a spurious free var,
        // `ginduct` rejects the formula as "not closed", and `[sources]`
        // lemmas silently lose their induction (proof explodes).
        p::Term::Var(v)
            if matches!(v.sort, p::SortHint::Untagged) && v.idx == 0
                && crate::elaborate::is_user_nullary_fun(&v.name) =>
            GTerm::App(v.name.as_str().into(), Vec::<GTerm>::new().into()),
        p::Term::Var(v) => GTerm::Var(BVar::Free(v.clone())),
        p::Term::PubLit(s) => GTerm::PubLit(s.clone()),
        p::Term::FreshLit(s) => GTerm::FreshLit(s.clone()),
        p::Term::NatLit(s) => GTerm::NatLit(s.clone()),
        p::Term::Number(n) => GTerm::Number(*n),
        p::Term::NumberOne => GTerm::NumberOne,
        p::Term::NatOne => GTerm::NatOne,
        p::Term::DhNeutral => GTerm::DhNeutral,
        p::Term::App(n, args) =>
            GTerm::App(n.as_str().into(), args.iter().map(term_to_gterm_free).collect()),
        p::Term::AlgApp(n, a, b) =>
            GTerm::AlgApp(n.as_str().into(), ga(term_to_gterm_free(a)), ga(term_to_gterm_free(b))),
        p::Term::Pair(items) =>
            mk_gpair(items.iter().map(term_to_gterm_free).collect()),
        p::Term::Diff(a, b) =>
            GTerm::Diff(ga(term_to_gterm_free(a)), ga(term_to_gterm_free(b))),
        p::Term::BinOp(op, a, b) =>
            GTerm::BinOp(*op, ga(term_to_gterm_free(a)), ga(term_to_gterm_free(b))),
        p::Term::PatMatch(t) =>
            GTerm::PatMatch(ga(term_to_gterm_free(t))),
    }
}

/// Lift `p::Fact` to `GFact` treating every variable as `Free`.
pub fn fact_to_gfact_free(f: &p::Fact) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(term_to_gterm_free).collect(),
        annotations: f.annotations.clone(),
    }
}

/// Lift `p::Atom` to `GAtom` treating every variable as `Free`.
pub fn atom_to_gatom_free(a: &p::Atom) -> GAtom {
    match a {
        p::Atom::Eq(s, t) => GAtom::Eq(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::Less(s, t) => GAtom::Less(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::LessMset(s, t) => GAtom::LessMset(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::Subterm(s, t) => GAtom::Subterm(term_to_gterm_free(s), term_to_gterm_free(t)),
        p::Atom::Action(f, t) => GAtom::Action(fact_to_gfact_free(f), term_to_gterm_free(t)),
        p::Atom::Last(t) => GAtom::Last(term_to_gterm_free(t)),
        p::Atom::Pred(f) => GAtom::Pred(fact_to_gfact_free(f)),
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
        GTerm::Var(BVar::Bound(n)) =>
            panic!("gterm_to_term: left-over bound variable Bound({})", n),
        GTerm::PubLit(s) => p::Term::PubLit(s.clone()),
        GTerm::FreshLit(s) => p::Term::FreshLit(s.clone()),
        GTerm::NatLit(s) => p::Term::NatLit(s.clone()),
        GTerm::Number(n) => p::Term::Number(*n),
        GTerm::NumberOne => p::Term::NumberOne,
        GTerm::NatOne => p::Term::NatOne,
        GTerm::DhNeutral => p::Term::DhNeutral,
        GTerm::App(n, args) =>
            p::Term::App(n.to_string(), args.iter().map(gterm_to_term).collect()),
        GTerm::AlgApp(n, a, b) =>
            p::Term::AlgApp(n.to_string(), Box::new(gterm_to_term(a)), Box::new(gterm_to_term(b))),
        GTerm::Pair(items) =>
            p::Term::Pair(items.iter().map(gterm_to_term).collect()),
        GTerm::Diff(a, b) =>
            p::Term::Diff(Box::new(gterm_to_term(a)), Box::new(gterm_to_term(b))),
        GTerm::BinOp(op, a, b) =>
            p::Term::BinOp(*op, Box::new(gterm_to_term(a)), Box::new(gterm_to_term(b))),
        GTerm::PatMatch(t) =>
            p::Term::PatMatch(Box::new(gterm_to_term(t))),
    }
}

/// Convert `GFact` to `p::Fact`, panicking on any leftover Bound.
pub fn gfact_to_fact(g: &GFact) -> p::Fact {
    p::Fact {
        persistent: g.persistent,
        name: g.name.clone(),
        args: g.args.iter().map(gterm_to_term).collect(),
        annotations: g.annotations.clone(),
    }
}

/// Convert `GAtom` to `p::Atom`, panicking on any leftover Bound.
///
/// HS equivalent: `bvarToLVar`.
pub fn gatom_to_atom(a: &GAtom) -> p::Atom {
    match a {
        GAtom::Eq(s, t) => p::Atom::Eq(gterm_to_term(s), gterm_to_term(t)),
        GAtom::Less(s, t) => p::Atom::Less(gterm_to_term(s), gterm_to_term(t)),
        GAtom::LessMset(s, t) => p::Atom::LessMset(gterm_to_term(s), gterm_to_term(t)),
        GAtom::Subterm(s, t) => p::Atom::Subterm(gterm_to_term(s), gterm_to_term(t)),
        GAtom::Action(f, t) => p::Atom::Action(gfact_to_fact(f), gterm_to_term(t)),
        GAtom::Last(t) => p::Atom::Last(gterm_to_term(t)),
        GAtom::Pred(f) => p::Atom::Pred(gfact_to_fact(f)),
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

/// Normalise a parser `SortHint` to the concrete `LSort` that HS's formula
/// parser would have assigned to the same *non-temporal* occurrence.
///
/// HS's `msgvar = sortedLVar [LSortFresh, LSortPub, LSortNat, LSortMsg]`
/// assigns a bare (sigil-less) variable `LSortMsg` (the prefix parser for
/// `LSortMsg` consumes no sigil), so our `Untagged` hint maps to `Msg`.
/// `Suffix(X)` is the `:msg|:pub|…` form and folds onto its base sort.
pub fn normalise_msg_sort(s: p::SortHint) -> p::SortHint {
    use p::{SortHint as S, SuffixSort as SS};
    match s {
        S::Untagged => S::Msg,
        S::Suffix(SS::Msg) => S::Msg,
        S::Suffix(SS::Pub) => S::Pub,
        S::Suffix(SS::Fresh) => S::Fresh,
        S::Suffix(SS::Node) => S::Node,
        S::Suffix(SS::Nat) => S::Nat,
        other => other,
    }
}

/// `subst_free_term_at_depth(t, s, depth)` — for each Free leaf, look up
/// `(lvar, db)` in `s`; if found, replace with `Bound(db + depth)`.
///
/// HS faithfulness: HS's `substFreeAtom` uses `lookup x s` with full `LVar`
/// `Eq` (name + idx + **sort**), and HS reaches `closeGuarded` only after the
/// parser has assigned every occurrence a concrete sort *by syntactic
/// position*: a variable in temporal position (`@t`, `last(t)`, `t < t`) is
/// parsed by `nodevar` (always `LSortNode`), every other occurrence by
/// `msgvar` (a bare name → `LSortMsg`).  Our parser instead defers and leaves
/// bare names as `SortHint::Untagged`, so we reconstruct HS's per-occurrence
/// sort here: callers pass `temporal = true` for occurrences in a temporal
/// position, and we then match by (name, idx, resolved-sort).
///
/// This keeps the single-binder-per-name cases working (e.g. `Ex #i. P @ i`:
/// the temporal `i` resolves to `Node`, matching the `#i` binder), while
/// correctly *separating* two distinct binders that share a base name across
/// sorts (e.g. `Ex k m #k. … <h, k> … @ k`: the msg-position `k` resolves to
/// `Msg` and binds to the `k` binder, the temporal `@k` resolves to `Node`
/// and binds to the `#k` binder).  When a body reference's resolved sort has
/// no matching binder it stays Free, exactly as HS leaves it unguarded
/// (e.g. `Made(k)` under an `Ex ~k.` binder).
pub fn subst_free_term_at_depth(t: &GTerm, s: &[(p::VarSpec, u32)], depth: u32) -> GTerm {
    subst_free_term_at_depth_pos(t, s, depth, false)
}

/// Position-aware variant of [`subst_free_term_at_depth`]: `temporal` records
/// whether this term occupies a temporal (timepoint) position in its atom.
pub fn subst_free_term_at_depth_pos(
    t: &GTerm,
    s: &[(p::VarSpec, u32)],
    depth: u32,
    temporal: bool,
) -> GTerm {
    match subst_free_term_cow(t, s, depth, temporal) {
        Some(g) => g,
        None => t.clone(),
    }
}

/// Copy-on-write core of `subst_free_term_at_depth`.  Returns `None` when no
/// Free leaf in the subtree matches a substitution key, so the caller can
/// reuse the input `Arc`.  These `subst_free`/`subst_bound` paths never call
/// `mk_gpair` (they only retag Var leaves Free↔Bound, never inserting a Pair),
/// so `Pair` reuse is unconditional on "no child changed".
fn subst_free_term_cow(
    t: &GTerm,
    s: &[(p::VarSpec, u32)],
    depth: u32,
    temporal: bool,
) -> Option<GTerm> {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            // Resolve this occurrence's sort the way HS's parser would:
            // temporal positions are parsed by `nodevar` (always `LSortNode`),
            // every other occurrence by `msgvar` (bare name → `LSortMsg`).
            let occ_sort = if temporal { p::SortHint::Node } else { normalise_msg_sort(v.sort) };
            for (lv, db) in s {
                if lv.name == v.name
                    && lv.idx == v.idx
                    && normalise_msg_sort(lv.sort) == occ_sort
                {
                    return Some(GTerm::Var(BVar::Bound(db + depth)));
                }
            }
            None
        }
        GTerm::Var(_) | GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne | GTerm::DhNeutral => None,
        // Below a function/pair/operator, sub-terms are never in temporal
        // position (HS parses them via the message-term parser), so descend
        // with `temporal = false`.
        GTerm::App(n, args) => subst_free_slice(args, s, depth)
            .map(|new| GTerm::App(n.clone(), new)),
        GTerm::Pair(items) => subst_free_slice(items, s, depth)
            .map(GTerm::Pair),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(
            a, subst_free_term_cow(a, s, depth, false),
            b, subst_free_term_cow(b, s, depth, false),
        ).map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
        GTerm::Diff(a, b) => cow_pair_arc(
            a, subst_free_term_cow(a, s, depth, false),
            b, subst_free_term_cow(b, s, depth, false),
        ).map(|(a, b)| GTerm::Diff(a, b)),
        GTerm::BinOp(op, a, b) => cow_pair_arc(
            a, subst_free_term_cow(a, s, depth, false),
            b, subst_free_term_cow(b, s, depth, false),
        ).map(|(a, b)| GTerm::BinOp(*op, a, b)),
        GTerm::PatMatch(inner) => subst_free_term_cow(inner, s, depth, false)
            .map(|g| GTerm::PatMatch(ga(g))),
    }
}

fn subst_free_slice(args: &std::sync::Arc<[GTerm]>, s: &[(p::VarSpec, u32)], depth: u32)
    -> Option<std::sync::Arc<[GTerm]>>
{
    cow_map_arc(args, |a| subst_free_term_cow(a, s, depth, false))
}

/// `subst_free_fact_at_depth(f, s, depth)` — analogous for facts.
pub fn subst_free_fact_at_depth(f: &GFact, s: &[(p::VarSpec, u32)], depth: u32) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|a| subst_free_term_at_depth(a, s, depth)).collect(),
        annotations: f.annotations.clone(),
    }
}

/// `subst_free_atom_at_depth(a, s, depth)` — applies the Free→Bound subst to
/// every term leaf in an atom. Mirrors HS `substFreeAtom` (with the i+j shift
/// applied externally by the caller — pass `depth` for the j term).
pub fn subst_free_atom_at_depth(a: &GAtom, s: &[(p::VarSpec, u32)], depth: u32) -> GAtom {
    // `temporal = true` marks term positions parsed by HS via `nodevar`
    // (always `LSortNode`): the `@`-timepoint of an action, the `last(t)`
    // argument, and both operands of `<` (timepoint ordering).  Term equality
    // (`EqE`), multiset comparison and subterm are message-term positions in
    // HS (`termp`/`msetterm`), so an explicitly `#`-sigiled timepoint carries
    // its own `Node` sort while a bare name stays message-sorted.
    match a {
        GAtom::Eq(x, y) => GAtom::Eq(
            subst_free_term_at_depth(x, s, depth),
            subst_free_term_at_depth(y, s, depth),
        ),
        GAtom::Less(x, y) => GAtom::Less(
            subst_free_term_at_depth_pos(x, s, depth, true),
            subst_free_term_at_depth_pos(y, s, depth, true),
        ),
        GAtom::LessMset(x, y) => GAtom::LessMset(
            subst_free_term_at_depth(x, s, depth),
            subst_free_term_at_depth(y, s, depth),
        ),
        GAtom::Subterm(x, y) => GAtom::Subterm(
            subst_free_term_at_depth(x, s, depth),
            subst_free_term_at_depth(y, s, depth),
        ),
        GAtom::Action(f, t) => GAtom::Action(
            subst_free_fact_at_depth(f, s, depth),
            subst_free_term_at_depth_pos(t, s, depth, true),
        ),
        GAtom::Last(t) => GAtom::Last(subst_free_term_at_depth_pos(t, s, depth, true)),
        GAtom::Pred(f) => GAtom::Pred(subst_free_fact_at_depth(f, s, depth)),
    }
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
        GTerm::Var(_) | GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne | GTerm::DhNeutral => None,
        GTerm::App(n, args) => subst_bound_slice(args, s, depth)
            .map(|new| GTerm::App(n.clone(), new)),
        GTerm::Pair(items) => subst_bound_slice(items, s, depth)
            .map(GTerm::Pair),
        GTerm::AlgApp(n, a, b) => cow_pair_arc(
            a, subst_bound_term_cow(a, s, depth),
            b, subst_bound_term_cow(b, s, depth),
        ).map(|(a, b)| GTerm::AlgApp(n.clone(), a, b)),
        GTerm::Diff(a, b) => cow_pair_arc(
            a, subst_bound_term_cow(a, s, depth),
            b, subst_bound_term_cow(b, s, depth),
        ).map(|(a, b)| GTerm::Diff(a, b)),
        GTerm::BinOp(op, a, b) => cow_pair_arc(
            a, subst_bound_term_cow(a, s, depth),
            b, subst_bound_term_cow(b, s, depth),
        ).map(|(a, b)| GTerm::BinOp(*op, a, b)),
        GTerm::PatMatch(inner) => subst_bound_term_cow(inner, s, depth)
            .map(|g| GTerm::PatMatch(ga(g))),
    }
}

fn subst_bound_slice(args: &std::sync::Arc<[GTerm]>, s: &[(u32, p::VarSpec)], depth: u32)
    -> Option<std::sync::Arc<[GTerm]>>
{
    cow_map_arc(args, |a| subst_bound_term_cow(a, s, depth))
}

/// `subst_bound_fact_at_depth(f, s, depth)` — analogous for facts.
pub fn subst_bound_fact_at_depth(f: &GFact, s: &[(u32, p::VarSpec)], depth: u32) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|a| subst_bound_term_at_depth(a, s, depth)).collect(),
        annotations: f.annotations.clone(),
    }
}

/// `subst_bound_atom_at_depth(a, s, depth)` — applies the Bound→Free subst.
/// Mirrors HS `substBoundAtom` (i+j shift baked into the depth parameter).
pub fn subst_bound_atom_at_depth(a: &GAtom, s: &[(u32, p::VarSpec)], depth: u32) -> GAtom {
    match a {
        GAtom::Eq(x, y) => GAtom::Eq(
            subst_bound_term_at_depth(x, s, depth),
            subst_bound_term_at_depth(y, s, depth),
        ),
        GAtom::Less(x, y) => GAtom::Less(
            subst_bound_term_at_depth(x, s, depth),
            subst_bound_term_at_depth(y, s, depth),
        ),
        GAtom::LessMset(x, y) => GAtom::LessMset(
            subst_bound_term_at_depth(x, s, depth),
            subst_bound_term_at_depth(y, s, depth),
        ),
        GAtom::Subterm(x, y) => GAtom::Subterm(
            subst_bound_term_at_depth(x, s, depth),
            subst_bound_term_at_depth(y, s, depth),
        ),
        GAtom::Action(f, t) => GAtom::Action(
            subst_bound_fact_at_depth(f, s, depth),
            subst_bound_term_at_depth(t, s, depth),
        ),
        GAtom::Last(t) => GAtom::Last(subst_bound_term_at_depth(t, s, depth)),
        GAtom::Pred(f) => GAtom::Pred(subst_bound_fact_at_depth(f, s, depth)),
    }
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

/// Project a binder's metadata. HS `vs' = map (lvarName &&& lvarSort) vs`.
pub fn lvar_to_binding(v: &p::VarSpec) -> GBinding {
    GBinding { name: v.name.clone(), sort: v.sort }
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
        GTerm::App(_, args) | GTerm::Pair(args) =>
            for a in args.iter() { collect_free_term(a, out); },
        GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
            collect_free_term(a, out);
            collect_free_term(b, out);
        }
        GTerm::PatMatch(t) => collect_free_term(t, out),
        _ => {}
    }
}

/// Push every Free LVar reachable from an atom into `out`.
pub fn collect_free_atom(a: &GAtom, out: &mut Vec<p::VarSpec>) {
    match a {
        GAtom::Eq(x, y) | GAtom::Less(x, y) | GAtom::LessMset(x, y) | GAtom::Subterm(x, y) => {
            collect_free_term(x, out);
            collect_free_term(y, out);
        }
        GAtom::Action(f, t) => {
            for arg in f.args.iter() { collect_free_term(arg, out); }
            collect_free_term(t, out);
        }
        GAtom::Last(t) => collect_free_term(t, out),
        GAtom::Pred(f) =>
            for arg in f.args.iter() { collect_free_term(arg, out); },
    }
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
        GTerm::App(n, args) =>
            GTerm::App(n.clone(), args.iter().map(|a| map_free_term(a, f)).collect()),
        GTerm::AlgApp(n, a, b) =>
            GTerm::AlgApp(n.clone(), ga(map_free_term(a, f)), ga(map_free_term(b, f))),
        GTerm::Pair(items) =>
            GTerm::Pair(items.iter().map(|a| map_free_term(a, f)).collect()),
        GTerm::Diff(a, b) =>
            GTerm::Diff(ga(map_free_term(a, f)), ga(map_free_term(b, f))),
        GTerm::BinOp(op, a, b) =>
            GTerm::BinOp(*op, ga(map_free_term(a, f)), ga(map_free_term(b, f))),
        GTerm::PatMatch(t) => GTerm::PatMatch(ga(map_free_term(t, f))),
    }
}

/// Apply a remapping to every Free LVar in a fact.
pub fn map_free_fact<F: FnMut(&p::VarSpec) -> p::VarSpec>(g: &GFact, f: &mut F) -> GFact {
    GFact {
        persistent: g.persistent,
        name: g.name.clone(),
        args: g.args.iter().map(|a| map_free_term(a, f)).collect(),
        annotations: g.annotations.clone(),
    }
}

/// Apply a remapping to every Free LVar in an atom.
pub fn map_free_atom<F: FnMut(&p::VarSpec) -> p::VarSpec>(a: &GAtom, f: &mut F) -> GAtom {
    match a {
        GAtom::Eq(x, y) => GAtom::Eq(map_free_term(x, f), map_free_term(y, f)),
        GAtom::Less(x, y) => GAtom::Less(map_free_term(x, f), map_free_term(y, f)),
        GAtom::LessMset(x, y) => GAtom::LessMset(map_free_term(x, f), map_free_term(y, f)),
        GAtom::Subterm(x, y) => GAtom::Subterm(map_free_term(x, f), map_free_term(y, f)),
        GAtom::Action(g, t) => GAtom::Action(map_free_fact(g, f), map_free_term(t, f)),
        GAtom::Last(t) => GAtom::Last(map_free_term(t, f)),
        GAtom::Pred(g) => GAtom::Pred(map_free_fact(g, f)),
    }
}

// =============================================================================
// Unit tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn vs(name: &str, idx: u64) -> p::VarSpec {
        p::VarSpec { name: name.to_string(), idx, sort: p::SortHint::Msg, typ: None }
    }

    fn vs_node(name: &str, idx: u64) -> p::VarSpec {
        p::VarSpec { name: name.to_string(), idx, sort: p::SortHint::Node, typ: None }
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
            GAtom::Action(f, _) => match &f.args[0] {
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
        let vs = vec![
            super::tests::vs("a", 0),
            super::tests::vs("b", 1),
            super::tests::vs("c", 2),
        ];
        // outer→inner: a, b, c
        // HS `zip (reverse vs) [0..]` ⇒ [(c, 0), (b, 1), (a, 2)]
        let s = close_subst(&vs);
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
        let xs = vec![
            super::tests::vs("a", 0),
            super::tests::vs("b", 1),
            super::tests::vs("c", 2),
        ];
        // HS `zip [0..] (reverse xs)` ⇒ [(0, c), (1, b), (2, a)]
        let s = open_subst(&xs);
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
        let mut inner_body = GAtom::Action(
            GFact {
                persistent: false,
                name: "P".to_string(),
                args: vec![
                    GTerm::Var(BVar::Free(x.clone())),
                    GTerm::Var(BVar::Bound(0)),
                ].into(),
                annotations: vec![],
            },
            GTerm::Var(BVar::Free(vs_node("t", 0))),
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
            GAtom::Action(f, _) => {
                match &f.args[0] {
                    GTerm::Var(BVar::Bound(n)) => assert_eq!(*n, 1, "x should shift to Bound(1)"),
                    other => panic!("expected Bound(1), got {:?}", other),
                }
                match &f.args[1] {
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
            ].into(),
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
            ].into(),
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
