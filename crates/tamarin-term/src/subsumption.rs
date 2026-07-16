//! Port of `Term.Subsumption` — subsumption ordering on terms.
//!
//! Subsumption: `t1 ≤ t2` iff there exists a substitution `s` such that
//! `s(t1) =AC= t2`. We say `t1` subsumes `t2` when `t1` is the more
//! general (i.e. has at most as much information as) of the two.
//!
//! The Haskell version uses Maude AC matching to decide subsumption.
//! Likewise here: `compare_term_subs` / `eq_term_subs` decide
//! subsumption by issuing two `maude.match_eqs` calls directly against
//! a `&MaudeHandle`.

use std::cmp::Ordering;

use crate::lterm::LNTerm;
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::rewriting::Equal;

/// Compare two terms under the subsumption order modulo the
/// configured equational theory. Returns `None` if the two are
/// incomparable, or `Some(Ord)` otherwise.
///
/// Uses Maude's matcher. Port of HS `compareTermSubs`
/// (`Subsumption.hs`):
///
/// ```haskell
/// compareTermSubs t1 t2 = check <$> solveMatchLNTerm (t1 `matchWith` t2)
///                               <*> solveMatchLNTerm (t2 `matchWith` t1)
///   where check (_:_) []    = Just GT
///         check []    (_:_) = Just LT
///         check (_:_) (_:_) = Just EQ
///         check []    []    = Nothing
/// ```
///
/// `matchWith t p = DelayedMatches [(t, p)]` is `(subject, pattern)`
/// (`Definitions.hs`). So arm A = `t1 matchWith t2` matches
/// **subject t1** against **pattern t2** (∃σ. `t1 =AC σ(t2)`, i.e.
/// `t2` subsumes `t1`); A non-empty + B empty ⇒ `GT`. Hence
/// `Some(Greater)` means `t1` is strictly MORE SPECIFIC than `t2`.
///
/// **Convention trap.** `match_eqs` takes `Equal { lhs = subject,
/// rhs = pattern }` (HS's `Equal subject pattern`, see its doc). So
/// HS's `t1 matchWith t2` ⇒ `Equal { lhs: t1, rhs: t2 }` — keep
/// `lhs = subject`, `rhs = pattern`. Flipping the two would swap
/// `Greater`/`Less` (only `eq_term_subs` is invariant under the swap).
///
/// Intentionally retained: faithful HS port (`Subsumption.hs`);
/// exercised by tests but with no production caller yet.
#[allow(dead_code)]
pub(crate) fn compare_term_subs(
    maude: &MaudeHandle,
    t1: &LNTerm,
    t2: &LNTerm,
) -> Result<Option<Ordering>, MaudeError> {
    // arm A: `t1 matchWith t2` = subject t1, pattern t2.
    let match_a = maude.match_eqs(&[Equal { lhs: t1.clone(), rhs: t2.clone() }])?;
    // arm B: `t2 matchWith t1` = subject t2, pattern t1.
    let match_b = maude.match_eqs(&[Equal { lhs: t2.clone(), rhs: t1.clone() }])?;
    Ok(match (match_a.is_empty(), match_b.is_empty()) {
        (true, true) => None,
        (false, true) => Some(Ordering::Greater),
        (true, false) => Some(Ordering::Less),
        (false, false) => Some(Ordering::Equal),
    })
}

/// Subsumption equality.
///
/// Intentionally retained: faithful HS port (`Subsumption.hs`); no
/// caller yet.
#[allow(dead_code)]
pub(crate) fn eq_term_subs(
    maude: &MaudeHandle,
    t1: &LNTerm,
    t2: &LNTerm,
) -> Result<bool, MaudeError> {
    Ok(matches!(compare_term_subs(maude, t1, t2)?, Some(Ordering::Equal)))
}

// =============================================================================
// `canonizeSubst` — port of `Term.Subsumption.canonizeSubst`
// (Subsumption.hs:67-77).
//
// ```haskell
// canonizeSubst :: LNSubstVFresh -> LNSubstVFresh
// canonizeSubst subst =
//     mapRangeVFresh (applyVTerm renaming) subst
//   where
//     occs         = varOccurences $ rangeVFresh subst
//     vrangeSorted = sortOn (`lookup` occs) (varsRangeVFresh subst)
//     renaming = substFromList $
//                  zipWith (\lv i -> (lv, varTerm $ LVar "x" (lvarSort lv) i))
//                          vrangeSorted [1..]
// ```
//
// Returns a substitution equivalent modulo renaming, with the range
// variables renamed to `x.1`, `x.2`, … in the canonical order induced
// by `sortOn (lookup occs)`:
//
//   * `occs = varOccurences (rangeVFresh subst)` — `rangeVFresh` is
//     `M.elems . svMap`, i.e. the range terms in DOMAIN-KEY order (the
//     `BTreeMap` iteration order).  `varOccurences` returns, for each
//     range var, the SET of context paths (`Occurence = [String]`) in
//     which it appears.  The context path for a var is built innermost-
//     first by `foldFreesOcc` (LTerm.hs:744-748 + the `[a]` instance
//     LTerm.hs:843): the outer `[VTerm]` list prepends `show listIdx`,
//     a `FApp (NoEq o)` prepends `unpack (fst o)` (the symbol name),
//     and a `FApp (AC|C) o` prepends `show o` (the Haskell `Show` of
//     the whole `FunSym`, e.g. `"AC Mult"` / `"C EMap"`), then descends
//     into the arg list (which prepends each arg's `show argIdx`).
//
//   * `vrangeSorted = sortOn (lookup occs) (varsRangeVFresh subst)` —
//     `varsRangeVFresh = varsVTerm . fAppList . rangeVFresh`, i.e. the
//     SORTED-NUB list of range vars (`varsVTerm` = `sortednub`, so
//     ordered by `Ord LVar`).  `sortOn` is STABLE: ties on the
//     occurrence-set key fall back to this `Ord LVar` order.
//     `lookup occs v :: Maybe (S.Set Occurence)` — `Nothing < Just`,
//     and two `Just` sets compare by `Ord (S.Set [String])` =
//     lexicographic over the sorted set elements.
//
//   * `renaming` maps each var in `vrangeSorted` to `x.i` (1-indexed),
//     preserving its sort, and is applied across the whole range.
//
// This is a FAITHFUL port of HS `canonizeSubst` (the occurrence-set
// ordering) — `bpVariantsIntruder` depends on the exact HS ordering to
// dedup BP destructor variants byte-identically.
// =============================================================================

use crate::lterm::LVar;
use crate::subst_vfresh::LNSubstVFresh;
use crate::vterm::{var_term, Lit};
use crate::term::Term;
use crate::function_symbols::{AcSym, CSym, FunSym};
use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// A single context occurrence path, built innermost-first
/// (`Occurence = [String]` in HS, where the path is cons'd as we
/// descend — head is the innermost context label).
type Occurence = Vec<String>;

/// HS `show` of a non-`NoEq` `FunSym` used as a context label
/// (`foldFreesOcc f (show o:c) as` for AC/C symbols, LTerm.hs:748).
/// Mirrors the derived `Show` for `FunSym`/`ACSym`/`CSym`.
fn show_funsym_ac_c(sym: &FunSym) -> String {
    match sym {
        FunSym::Ac(a) => {
            let name = match a {
                AcSym::Union => "Union",
                AcSym::Mult => "Mult",
                AcSym::Xor => "Xor",
                AcSym::NatPlus => "NatPlus",
            };
            format!("AC {}", name)
        }
        FunSym::C(c) => {
            let name = match c {
                CSym::EMap => "EMap",
            };
            format!("C {}", name)
        }
        // `List` and `NoEq` never reach this branch in `foldFreesOcc`
        // (NoEq has its own arm; `List` does not appear in BP ranges),
        // but render defensively to match `show`.
        FunSym::List => "List".to_string(),
        FunSym::NoEq(o) => String::from_utf8_lossy(o.name).into_owned(),
    }
}

/// `foldFreesOcc (\c v -> [(v,c)]) c t` over a single term — collects
/// `(var, context-path)` pairs.  Mirrors the `Term` instance
/// (LTerm.hs:744-748):
///
/// ```haskell
/// foldFreesOcc f c t = case viewTerm t of
///     Lit  l           -> foldFreesOcc f c l
///     FApp (NoEq o) as -> foldFreesOcc f ((unpack (fst o)):c) as
///     FApp o        as -> mconcat $ map (foldFreesOcc f (show o:c)) as
/// ```
///
/// **The NoEq vs AC/C asymmetry is load-bearing**: for a `NoEq` symbol the
/// children `as :: [Term]` are folded via the `[a]` HasFrees instance
/// (LTerm.hs:843), which prepends each child's `show argIdx` to the
/// context.  But for an AC/C symbol HS does `mconcat $ map
/// (foldFreesOcc f (show o:c)) as` — a DIRECT map over the children with
/// the SAME `(show o : c)` context, bypassing the `[a]` instance, so the
/// per-child arg index is NOT added.  AC/C operator children therefore
/// share one context per operator occurrence (which is consistent with
/// AC/C operands being unordered).
fn fold_frees_occ_term(t: &LNTerm, ctx: &Occurence, out: &mut Vec<(LVar, Occurence)>) {
    match t {
        Term::Lit(Lit::Var(v)) => out.push((v.clone(), ctx.clone())),
        Term::Lit(_) => {}
        Term::App(FunSym::NoEq(o), args) => {
            // `FApp (NoEq o) as -> foldFreesOcc f ((unpack (fst o)):c) as`,
            // then the `[a]` instance prepends each child's `show argIdx`.
            let mut node_ctx = ctx.clone();
            node_ctx.insert(0, String::from_utf8_lossy(o.name).into_owned());
            for (i, a) in args.iter().enumerate() {
                let mut arg_ctx = node_ctx.clone();
                arg_ctx.insert(0, i.to_string());
                fold_frees_occ_term(a, &arg_ctx, out);
            }
        }
        Term::App(sym, args) => {
            // `FApp o as -> mconcat $ map (foldFreesOcc f (show o:c)) as` —
            // direct map: prepend `show o` ONCE, NO per-child arg index.
            let mut node_ctx = ctx.clone();
            node_ctx.insert(0, show_funsym_ac_c(sym));
            for a in args.iter() {
                fold_frees_occ_term(a, &node_ctx, out);
            }
        }
    }
}

/// `varOccurences (rangeVFresh subst)` — for each range var, the SET of
/// context paths in which it occurs.  The argument is the list of range
/// terms in domain-key order; the outer `[VTerm]` list instance
/// prepends `show listIdx` to each term's context (LTerm.hs:843).
fn var_occurences(range_terms: &[LNTerm]) -> BTreeMap<LVar, BTreeSet<Occurence>> {
    let mut pairs: Vec<(LVar, Occurence)> = Vec::new();
    for (i, t) in range_terms.iter().enumerate() {
        let ctx = vec![i.to_string()];
        fold_frees_occ_term(t, &ctx, &mut pairs);
    }
    let mut out: BTreeMap<LVar, BTreeSet<Occurence>> = BTreeMap::new();
    for (v, c) in pairs {
        out.entry(v).or_default().insert(c);
    }
    out
}

/// `canonizeSubst` — canonical representative modulo renaming.
/// Faithful port of HS `canonizeSubst` (Subsumption.hs:67-77).
pub fn canonize_subst(subst: &LNSubstVFresh) -> LNSubstVFresh {
    // `rangeVFresh subst = M.elems . svMap` — range terms in domain-key
    // (BTreeMap) order.
    let range_terms: Vec<LNTerm> = subst.range().cloned().collect();

    // `occs = varOccurences (rangeVFresh subst)`.
    let occs = var_occurences(&range_terms);

    // `varsRangeVFresh subst = varsVTerm . fAppList . rangeVFresh` — the
    // sorted-nub (`Ord LVar`) list of range vars.  `subst.vars_range()`
    // already returns exactly this.
    let mut vrange: Vec<LVar> = subst.vars_range();

    // `sortOn (lookup occs)` — STABLE sort by the occurrence-set key
    // (`Maybe (S.Set Occurence)`, `None < Some`), ties broken by the
    // pre-existing `Ord LVar` order of `varsRangeVFresh`.  Rust's
    // `sort_by_key` is stable, so it matches `sortOn`'s stability.
    vrange.sort_by_key(|v| occs.get(v).cloned());

    // `renaming = zipWith (\lv i -> (lv, x.i)) vrangeSorted [1..]`,
    // preserving each var's sort.  The values are `var_term`s so this is the
    // `LNTerm` var→term map `applyVTerm` consumes directly.
    let mut renaming: BTreeMap<LVar, LNTerm> = BTreeMap::new();
    for (i, v) in vrange.iter().enumerate() {
        renaming.insert(v.clone(), var_term(LVar::new("x", v.sort, (i + 1) as u64)));
    }

    // `mapRangeVFresh (applyVTerm renaming) subst`.  `apply_vterm_map` is the
    // `applyVTerm` HS canonizeSubst uses (Subsumption.hs:67-77): it dispatches
    // the `f_app_ac` / `f_app_c` / `f_app_no_eq` / `f_app_list` smart
    // constructors, so it **re-sorts AC/C operand lists** by the renamed `Ord
    // (Term a)`.  This matters: a renaming that reorders two operands of an AC
    // node (e.g. `mult(x3, x4)` with `x3→x.4, x4→x.3`) is re-sorted to
    // `mult(x.3, x.4)`, exactly as HS does — a raw `Term::App` would leave the
    // operands out of canonical order and diverge from HS's printed variants.
    // On a subtree containing no renamed var, `apply_vterm_map`'s COW no-change
    // path returns the original, value-identical subtree (range terms are
    // already AC-canonical, so re-normalising it is the identity).
    LNSubstVFresh::from_list(
        subst
            .to_list()
            .into_iter()
            .map(|(domv, t)| (domv, crate::subst::apply_vterm_map(&renaming, t)))
            .collect::<Vec<_>>(),
    )
}
