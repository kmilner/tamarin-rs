// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Maude.Types`.
//!
//! Converts between our `LNTerm` (logical-named term over `LVar`/`Name`)
//! and an `MTerm` (term over `MaudeLit`) used as the wire format with the
//! Maude subprocess.

use std::collections::BTreeMap;

use crate::lterm::{LNTerm, LSort, LVar, Name, NameTag};
use crate::term::Term;
use crate::vterm::Lit;

/// One literal in a Maude term — either an interned variable, a fresh
/// variable produced by Maude in a substitution, or an interned constant.
///
/// HS `data MaudeLit = MaudeVar Integer LSort | FreshVar Integer LSort |
/// MaudeConst Integer LSort` derives `Ord` in that variant and field order
/// (Term/Maude/Types.hs:42-45); it orders the `ConvCtx` maps and the AC
/// arguments of the terms sent over the Maude wire.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MaudeLit {
    MaudeVar(u64, LSort),
    FreshVar(u64, LSort),
    MaudeConst(u64, LSort),
}

/// An "MTerm" — a `Term` over `MaudeLit`.
pub type MTerm = Term<MaudeLit>;

/// A Maude substitution — list of `((sort, idx), term)` pairs.
pub type MSubst = Vec<((LSort, u64), MTerm)>;

// =============================================================================
// Conversion context
// =============================================================================

/// Two-way binding map between our `LNTerm` literals and `MaudeLit`s. We
/// generate fresh integer ids the first time we see a literal, and remember
/// the assignment so subsequent uses of the same literal share an id (so
/// Maude can recognise variable equality).
#[derive(Debug, Default, Clone)]
pub struct ConvCtx {
    /// Forward: `Lit<Name, LVar> -> MaudeLit`.
    forward: BTreeMap<Lit<Name, LVar>, MaudeLit>,
    /// Inverse map (built when we want to translate back).
    inverse: BTreeMap<MaudeLit, Lit<Name, LVar>>,
    /// Single shared fresh-id counter for ALL variables and constants,
    /// allocated in first-encounter (term-walk) order.
    ///
    /// HS-faithful: HS's `runConversion` (Term/Maude/Types.hs) runs the
    /// `lTermToMTerm` BindT computation under the *global* `FastFresh`
    /// monad (`type FreshState = Integer`), so `freshIdent "x"` (vars) and
    /// `freshIdent "a"` (constants) BOTH draw from ONE Integer counter that
    /// ignores the name hint.  Variables and constants therefore share a
    /// single 0,1,2,… encounter-order numbering (`x2:Fresh`, `p(3)`, `x4:Msg`,
    /// …).  Do NOT split into per-sort counters: Maude's AC-unifier
    /// enumeration is sensitive to variable names, so per-sort numbering
    /// flips the order of the 2 symmetric unifiers on AC-symmetric problems
    /// (e.g. the UM_three_pass `CK_secure_UM3` `R_Complete_case_1↔case_2`
    /// arm swap).
    counter: u64,
}

impl ConvCtx {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate the next id from the single shared encounter-order counter.
    /// Both variables and constants draw from this counter (sort is
    /// ignored), matching HS's global `FreshState = Integer` (see the
    /// `counter` field doc above).
    pub fn fresh_id(&mut self) -> u64 {
        let id = self.counter;
        self.counter += 1;
        id
    }

    pub fn bindings(&self) -> &BTreeMap<MaudeLit, Lit<Name, LVar>> {
        &self.inverse
    }
}

// =============================================================================
// Sort lookup for constants
// =============================================================================

/// Name-id prefix used by `maude_proc.rs` to mark a synthetic skolem
/// constant whose intended Maude sort is `Msg`.
///
/// `NameTag` has no `Msg` variant (a `Name` constant is always Fresh,
/// Pub, Node or Nat), and adding one would require non-exhaustive
/// `match`es across many crates to be updated.  The Maude wire encoding,
/// however, *does* support a `Msg`-sorted constant directly: the emitted
/// theory declares `op c : Nat -> Msg` and `MaudeConst(i, LSort::Msg)`
/// prints as `c(i)`.  So to faithfully mirror HS's
/// `sortOfSkol (SkConst v) = lvarSort v` (Guarded.hs:809-810) — where a
/// skolemized free variable keeps its *own* sort, which may be `Msg` —
/// we carry a `Msg`-sorted skolem as a `NameTag::Pub` `Name` whose id
/// begins with this sentinel, and recognise it here so that
/// `sort_of_name` returns `LSort::Msg` (not the carrier tag's `Pub`).
///
/// `Pub` is a strict subsort of `Msg`, so without this a `Msg` skolem
/// would be emitted as `p(i)` and Maude order-sorted matching would
/// *over-match* (succeeding where HS, treating it as `Msg`, would not).
///
/// This sentinel is namespaced (double-underscore + `skMSG` + double
/// underscore) so it cannot collide with any real protocol constant
/// (which originate from `'...'`/`~'...'` literals).
pub const SKOLEM_MSG_PREFIX: &str = "__skMSG__";

/// `sortOfName` — the sort of a `Name` literal.
pub fn sort_of_name(n: &Name) -> LSort {
    // Msg-sorted skolem constants are carried as `NameTag::Pub` names
    // with a sentinel id prefix; recover their true `Msg` sort here so
    // the Maude wire constant is `c(i)` (Msg), not `p(i)` (Pub).  See
    // `SKOLEM_MSG_PREFIX`.
    if matches!(n.tag, NameTag::Pub) && n.id.as_str().starts_with(SKOLEM_MSG_PREFIX) {
        return LSort::Msg;
    }
    crate::lterm::sort_of_name(n)
}

// =============================================================================
// LNTerm -> MTerm (forward)
// =============================================================================

/// Convert an `LNTerm` to an `MTerm`. Allocates fresh ids in `ctx` for
/// any new literals encountered.
pub fn lterm_to_mterm_global(t: &LNTerm, ctx: &mut ConvCtx) -> MTerm {
    // `map_lits` rebuilds through `f_app`, so AC args are flattened+sorted
    // and C/EMap args sorted by MaudeLit order after the left-to-right literal
    // imports.  This is HS `lTermToMTerm`'s `fApp o <$> mapM go as`
    // (Term/Maude/Types.hs:74-85, Raw.hs:111-131).
    crate::term::map_lits(t, &mut |lit| import_lit(lit, ctx))
}

fn import_lit(l: &Lit<Name, LVar>, ctx: &mut ConvCtx) -> MaudeLit {
    if let Some(m) = ctx.forward.get(l) {
        return m.clone();
    }
    let m = match l {
        Lit::Var(lv) => {
            let id = ctx.fresh_id();
            MaudeLit::MaudeVar(id, lv.sort)
        }
        Lit::Con(n) => {
            let s = sort_of_name(n);
            let id = ctx.fresh_id();
            MaudeLit::MaudeConst(id, s)
        }
    };
    ctx.forward.insert(l.clone(), m.clone());
    ctx.inverse.insert(m.clone(), l.clone());
    m
}

// =============================================================================
// MTerm -> LNTerm (backward)
// =============================================================================

/// Convert an `MTerm` back to an `LNTerm` using the inverse bindings stored
/// in `ctx`. Variables introduced by Maude (`FreshVar`) get fresh `LVar`s
/// with names from `name_hint`. `MaudeConst`s must already be in the
/// bindings; otherwise we panic, mirroring the Haskell behaviour.
pub fn mterm_to_lnterm(
    t: &MTerm,
    ctx: &mut ConvCtx,
    name_hint: &str,
    next_idx: &mut u64,
) -> LNTerm {
    // `map_lits` mirrors HS's `fApp o <$> mapM (go . viewTerm) as`: the leaf
    // imports happen left-to-right, then AC/C applications are reconstructed
    // and sorted under the canonical LVar order.
    crate::term::map_lits(t, &mut |ml| import_mlit(ml, ctx, name_hint, next_idx))
}

fn import_mlit(
    ml: &MaudeLit,
    ctx: &mut ConvCtx,
    name_hint: &str,
    next_idx: &mut u64,
) -> Lit<Name, LVar> {
    // A literal already in the inverse map is one we sent to Maude.
    if let Some(orig) = ctx.inverse.get(ml).cloned() {
        return orig;
    }
    // Sort-tolerant fallback: Maude can return a var with the same idx but a
    // widened sort.  This Rust-side compensation is intentionally stricter
    // than minting a second logical variable; TESLA Scheme1/2 are sensitive.
    if let MaudeLit::MaudeVar(idx, sort) = ml {
        if let Some(orig) = lookup_canonical_var_lit(ctx, *sort, *idx) {
            return orig;
        }
    }
    match ml {
        MaudeLit::FreshVar(_, sort) | MaudeLit::MaudeVar(_, sort) => {
            let lit = Lit::Var(LVar::new(name_hint, *sort, *next_idx));
            *next_idx += 1;
            ctx.inverse.insert(ml.clone(), lit.clone());
            lit
        }
        MaudeLit::MaudeConst(_, _) => panic!("mterm_to_lnterm: unknown constant {:?}", ml),
    }
}

// =============================================================================
// Substitution conversion helpers (vfresh / vfree variants)
// =============================================================================

/// Information needed to translate a Maude substitution back to an LNSubst.
/// The Haskell uses `BindT` to share the variable map. We thread `ConvCtx`
/// explicitly.
pub fn substitute_lookup_var(ctx: &ConvCtx, sort: LSort, idx: u64) -> Option<LVar> {
    // Delegates to `lookup_canonical_var_lit` (identical strict lookup +
    // sort-tolerant fallback over the same candidate array) and projects the
    // hit to its `LVar`.  Every `MaudeVar(idx, sort)` key in `ctx.inverse` is
    // inserted only against a `Lit::Var` (`import_lit` maps Var->MaudeVar /
    // Con->MaudeConst, and the fresh-witness path at `mterm_to_lnterm` inserts
    // `Lit::Var`), so a `MaudeVar` key never resolves to a `Lit::Con`; the
    // per-candidate `Lit::Var` filter can therefore never skip a Con to find a
    // later Var, and the delegated form returns the same LVar for every input.
    //
    // The sort-tolerant fallback in `lookup_canonical_var_lit` is a known
    // Rust-side compensation, NOT yet traced to its upstream cause.  It
    // diverges from HS `msubstToLSubstVFresh`/`VFree`'s `lookupVar s i =
    // lookupBinding (MaudeVar i s)` (Term/Maude/Types.hs:153-157, 173-177), which is
    // strict in the full `MaudeLit` sort and `error`s on a miss — there is no
    // any-sort fallback.  Kept to preserve current corpus parity until the
    // upstream cause is traced; do not change the fallback without a full
    // HS-parity corpus diff (TESLA Scheme1/2 are sensitive, per project
    // memory).
    match lookup_canonical_var_lit(ctx, sort, idx) {
        Some(Lit::Var(lv)) => Some(lv),
        _ => None,
    }
}

/// Like `substitute_lookup_var` but for term-reconstruction: returns
/// the matched literal (not just the LVar) so that callers in
/// `mterm_to_lnterm` can reuse the canonical original LVar instead of
/// fabricating a sort-mismatched fresh one.
pub fn lookup_canonical_var_lit(ctx: &ConvCtx, sort: LSort, idx: u64) -> Option<Lit<Name, LVar>> {
    if let Some(l) = ctx.inverse.get(&MaudeLit::MaudeVar(idx, sort)).cloned() {
        return Some(l);
    }
    for sort_candidate in &[
        LSort::Pub,
        LSort::Fresh,
        LSort::Nat,
        LSort::Msg,
        LSort::Node,
    ] {
        if *sort_candidate == sort {
            continue;
        }
        if let Some(l) = ctx
            .inverse
            .get(&MaudeLit::MaudeVar(idx, *sort_candidate))
            .cloned()
        {
            return Some(l);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The variant order `MaudeVar < FreshVar < MaudeConst`, and inside a
    /// variant the index before the sort, as HS's `MaudeLit` declares them.
    /// It orders the `ConvCtx` maps and the AC arguments of a wire term.
    #[test]
    fn maude_lit_ord_follows_the_haskell_declaration_order() {
        assert!(MaudeLit::MaudeVar(9, LSort::Msg) < MaudeLit::FreshVar(0, LSort::Msg));
        assert!(MaudeLit::FreshVar(9, LSort::Msg) < MaudeLit::MaudeConst(0, LSort::Msg));
        assert!(MaudeLit::MaudeVar(0, LSort::Node) < MaudeLit::MaudeVar(1, LSort::Pub));
        assert!(MaudeLit::MaudeVar(0, LSort::Pub) < MaudeLit::MaudeVar(0, LSort::Fresh));
    }

    #[test]
    fn skolem_msg_constant_sorts_as_msg() {
        use crate::lterm::{Name, NameId, NameTag};
        // A sentinel-prefixed Pub-carrier name is reported as Msg so the
        // Maude wire constant is `c(i)` (HS `sortOfSkol = lvarSort v`).
        let msg_skol = Name {
            tag: NameTag::Pub,
            id: NameId::new(format!("{}0_x_7_M", SKOLEM_MSG_PREFIX)),
        };
        assert_eq!(sort_of_name(&msg_skol), LSort::Msg);
        // A non-skolem Pub constant is still Pub.
        let real_pub = Name {
            tag: NameTag::Pub,
            id: NameId::new("alice"),
        };
        assert_eq!(sort_of_name(&real_pub), LSort::Pub);
        // The sentinel only applies to Pub-tagged carriers.
        let fresh = Name {
            tag: NameTag::Fresh,
            id: NameId::new("k"),
        };
        assert_eq!(sort_of_name(&fresh), LSort::Fresh);
        // The emitted Maude constant also uses the `c` (Msg) symbol.  It does
        // not use the `p` (Pub) symbol that the carrier tag would give.
        let t: LNTerm = Term::Lit(Lit::Con(msg_skol));
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(&t, &mut ctx);
        let wire = String::from_utf8(crate::maude_print::pp_mterm(&mt)).unwrap();
        assert_eq!(wire, "c(0)");
        let real: LNTerm = Term::Lit(Lit::Con(real_pub));
        let mt = lterm_to_mterm_global(&real, &mut ctx);
        let wire = String::from_utf8(crate::maude_print::pp_mterm(&mt)).unwrap();
        assert_eq!(wire, "p(1)");
    }

    /// A variable survives the `LNTerm -> MTerm -> LNTerm` round trip and
    /// keeps its identity.  The forward pass registers the inverse binding,
    /// and the backward pass reads that binding.  The code therefore mints no
    /// new `name_hint` variable, and it leaves `next` unchanged.
    #[test]
    fn round_trip_var() {
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = Term::Lit(Lit::Var(v));
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(&t, &mut ctx);
        assert_eq!(mt, Term::Lit(MaudeLit::MaudeVar(0, LSort::Msg)));
        let mut next = 0;
        let back = mterm_to_lnterm(&mt, &mut ctx, "z", &mut next);
        assert_eq!(t, back);
        assert_eq!(next, 0, "the binding was reused, not re-minted");
    }

    /// Pins the load-bearing sort-tolerant DOMAIN fallback in
    /// `substitute_lookup_var`.  HS `lookupVar s i = lookupBinding
    /// (MaudeVar i s)` (Term/Maude/Types.hs:153-157) is strict and would
    /// `error` on a sort-miss; the Rust fallback instead recovers the
    /// original LVar by (idx, ANY sort).  This test locks the CURRENT Rust
    /// behavior so any change to that fallback is caught and re-validated
    /// against the corpus.  If the upstream registration cause is ever
    /// traced and the fallback removed, this test changes with it.
    #[test]
    fn substitute_lookup_var_recovers_widened_sort() {
        let mut ctx = ConvCtx::new();
        // Bind MaudeVar(6, Fresh) -> ~k1 (a Fresh-sorted LVar).
        let k1 = LVar::new("~k", LSort::Fresh, 1);
        ctx.inverse
            .insert(MaudeLit::MaudeVar(6, LSort::Fresh), Lit::Var(k1));
        // Maude references it back with a WIDENED sort (Msg); the strict
        // (6, Msg) key misses, but the (idx, any-sort) fallback recovers
        // the original Fresh-sorted LVar.
        let got = substitute_lookup_var(&ctx, LSort::Msg, 6);
        assert_eq!(got, Some(k1));
        // A genuinely unknown idx still returns None (no fabrication).
        assert_eq!(substitute_lookup_var(&ctx, LSort::Msg, 99), None);
    }

    /// Pins the load-bearing sort-tolerant RANGE fallback used by
    /// `mterm_to_lnterm` via `lookup_canonical_var_lit`.  HS `importLit`
    /// (Term/Maude/Types.hs:94-106, see line 103) is strict on the full sort and on a miss
    /// mints a FRESH `LVar` at the widened sort; the Rust fallback instead
    /// recovers the original LVar identity.  Locks current Rust behavior.
    #[test]
    fn mterm_to_lnterm_recovers_widened_sort_var() {
        let mut ctx = ConvCtx::new();
        // ctx only has MaudeVar(idx, Fresh) bound.
        let k = LVar::new("~k", LSort::Fresh, 3);
        ctx.inverse
            .insert(MaudeLit::MaudeVar(4, LSort::Fresh), Lit::Var(k));
        // Maude hands back the SAME idx widened to Msg.
        let mt: MTerm = Term::Lit(MaudeLit::MaudeVar(4, LSort::Msg));
        let mut next = 50;
        let back = mterm_to_lnterm(&mt, &mut ctx, "x", &mut next);
        // Rust recovers the original Fresh-sorted LVar rather than minting
        // a fresh Msg-sorted one (which is what HS would do).  next is
        // untouched because no new LVar was allocated.
        assert_eq!(back, Term::Lit(Lit::Var(k)));
        assert_eq!(next, 50);
    }

    /// Regression for #330: `mterm_to_lnterm` must sort `em` (C/EMap) args
    /// by the FINAL `LVar` order, not leave them in Maude's back-conversion
    /// order.  An MTerm `em(<id for x.10>, <id for x.9>)` whose args map
    /// back to `x.10` and `x.9` must come back as `em(x.9, x.10)` (idx-first
    /// `LVar` order), matching HS `mTermToLNTerm`'s `fApp o`/`fAppC EMap`.
    #[test]
    fn emap_args_sorted_by_final_lvar_order() {
        use crate::function_symbols::{CSym, FunSym};
        // Build the MaudeVar ids in the REVERSE-of-sorted order: id 0 binds
        // to the larger var (x.10), id 1 to the smaller (x.9).  So the raw
        // MTerm `em(x0, x1)` is em(x.10, x.9) — unsorted.
        let x10 = LVar::new("x", LSort::Msg, 10);
        let x9 = LVar::new("x", LSort::Msg, 9);
        let mut ctx = ConvCtx::new();
        let m0 = MaudeLit::MaudeVar(0, LSort::Msg);
        let m1 = MaudeLit::MaudeVar(1, LSort::Msg);
        ctx.inverse.insert(m0.clone(), Lit::Var(x10));
        ctx.inverse.insert(m1.clone(), Lit::Var(x9));

        let mt: MTerm = Term::App(
            FunSym::C(CSym::EMap),
            vec![Term::Lit(m0), Term::Lit(m1)].into(),
        );
        let mut next = 100;
        let back = mterm_to_lnterm(&mt, &mut ctx, "x", &mut next);

        // Expected: em(x.9, x.10), with the arguments sorted by index first.
        // The expectation uses the raw constructor and not `f_app_c`.  It
        // therefore cannot inherit the same argument sorting that this test
        // checks.
        assert_eq!(
            back,
            crate::term::unsafe_f_app(
                FunSym::C(CSym::EMap),
                vec![Term::Lit(Lit::Var(x9)), Term::Lit(Lit::Var(x10))],
            )
        );
    }
}
