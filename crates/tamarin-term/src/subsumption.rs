// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `canonizeSubst` from `Term.Subsumption` (Subsumption.hs:67-76):
//! the canonical renaming of a fresh-range substitution's range variables.

use crate::lterm::LNTerm;

// =============================================================================
// `canonizeSubst` — port of `Term.Subsumption.canonizeSubst`
// (Subsumption.hs:67-76).
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
//     first by `foldFreesOcc` (LTerm.hs:782-785 + the `[a]` instance
//     LTerm.hs:877-882, see line 880): the outer `[VTerm]` list prepends
//     `show listIdx`,
//     a `FApp (NoEq o)` prepends `unpack (fst o)` (the symbol name),
//     and a `FApp (AC|C) o` prepends `show o` (the Haskell `Show` of
//     the whole `FunSym`, e.g. `"AC Mult"` / `"C EMap"`) before mapping
//     directly over its arguments, without adding argument indices.
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

use crate::function_symbols::{show_acfct_sym, AcSym, CSym, FunSym};
use crate::lterm::LVar;
use crate::subst_vfresh::LNSubstVFresh;
use crate::term::Term;
use crate::vterm::{var_term, Lit};
use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// A single context occurrence path, built innermost-first
/// (`Occurence = [String]` in HS, where the path is cons'd as we
/// descend — head is the innermost context label).
type Occurence = Vec<String>;

/// HS `show` of a non-`NoEq` `FunSym` used as a context label
/// (`foldFreesOcc f (show o:c) as` for AC/C symbols, LTerm.hs:782-786, see line 785).
/// Mirrors the derived `Show` for `FunSym`/`ACSym`/`CSym`.
fn show_funsym_ac_c(sym: &FunSym) -> String {
    match sym {
        FunSym::Ac(a) => match a {
            AcSym::Union => "AC Union".to_string(),
            AcSym::Mult => "AC Mult".to_string(),
            AcSym::Xor => "AC Xor".to_string(),
            AcSym::NatPlus => "AC NatPlus".to_string(),
            // Derived `Show` parenthesises the nested constructor
            // application; `show` of the `ACfctSym` tuple follows.
            AcSym::AcFct(s) => format!("AC (ACfct {})", show_acfct_sym(s)),
        },
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
/// (LTerm.hs:782-785):
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
/// (LTerm.hs:877-882, see line 880), which prepends each child's `show argIdx` to the
/// context.  But for an AC/C symbol HS does `mconcat $ map
/// (foldFreesOcc f (show o:c)) as` — a DIRECT map over the children with
/// the SAME `(show o : c)` context, bypassing the `[a]` instance, so the
/// per-child arg index is NOT added.  AC/C operator children therefore
/// share one context per operator occurrence (which is consistent with
/// AC/C operands being unordered).
fn fold_frees_occ_term(
    t: &LNTerm,
    ctx: &mut Occurence,
    out: &mut BTreeMap<LVar, BTreeSet<Occurence>>,
) {
    let mut current = t;
    let mut pending = Vec::new();
    loop {
        match current {
            Term::Lit(Lit::Var(v)) => {
                // The traversal keeps the path outside-in so descent can
                // append and truncate. HS stores it innermost-first.
                out.entry(*v)
                    .or_default()
                    .insert(ctx.iter().rev().cloned().collect());
            }
            Term::Lit(_) => {}
            Term::App(sym, args) if !args.is_empty() => {
                let (label, indexed) = match sym {
                    FunSym::NoEq(o) => (String::from_utf8_lossy(o.name).into_owned(), true),
                    _ => (show_funsym_ac_c(sym), false),
                };
                pending.push((args.iter().enumerate(), ctx.len(), label, indexed));
            }
            Term::App(..) => {}
        }
        loop {
            let Some((children, depth, label, indexed)) = pending.last_mut() else {
                return;
            };
            if let Some((index, child)) = children.next() {
                ctx.truncate(*depth);
                ctx.push(label.clone());
                if *indexed {
                    ctx.push(index.to_string());
                }
                current = child;
                break;
            }
            pending.pop();
        }
    }
}

/// `varOccurences (rangeVFresh subst)` — for each range var, the SET of
/// context paths in which it occurs.  The argument is the list of range
/// terms in domain-key order; the outer `[VTerm]` list instance
/// prepends `show listIdx` to each term's context (LTerm.hs:877-882, see line 880).
fn var_occurences<'a>(
    range_terms: impl IntoIterator<Item = &'a LNTerm>,
) -> BTreeMap<LVar, BTreeSet<Occurence>> {
    let mut out = BTreeMap::new();
    for (i, t) in range_terms.into_iter().enumerate() {
        let mut ctx = vec![i.to_string()];
        fold_frees_occ_term(t, &mut ctx, &mut out);
    }
    out
}

/// `canonizeSubst` — canonical representative modulo renaming.
/// Faithful port of HS `canonizeSubst` (Subsumption.hs:67-76).
pub fn canonize_subst(subst: &LNSubstVFresh) -> LNSubstVFresh {
    // Range terms arrive in domain-key order. Every range variable is a key
    // in the occurrence map, already sorted and deduplicated by `Ord LVar`.
    let occs = var_occurences(subst.range());
    let mut vrange: Vec<LVar> = occs.keys().copied().collect();

    // `sortOn (lookup occs)` — STABLE sort by the occurrence-set key
    // (`Maybe (S.Set Occurence)`, `None < Some`), ties broken by the
    // pre-existing `Ord LVar` order of `varsRangeVFresh`.  Rust's stable
    // slice sort preserves that order when the comparator returns equal.
    vrange.sort_by(|a, b| occs.get(a).cmp(&occs.get(b)));

    // `renaming = zipWith (\lv i -> (lv, x.i)) vrangeSorted [1..]`,
    // preserving each var's sort.  The values are `var_term`s so this is the
    // `LNTerm` var→term map `applyVTerm` consumes directly.
    let mut renaming: BTreeMap<LVar, LNTerm> = BTreeMap::new();
    for (i, v) in vrange.iter().enumerate() {
        renaming.insert(*v, var_term(LVar::new("x", v.sort, (i + 1) as u64)));
    }

    // `mapRangeVFresh (applyVTerm renaming) subst`.  `apply_vterm_map` is the
    // `applyVTerm` HS canonizeSubst uses (Subsumption.hs:67-76): it dispatches
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
            .iter()
            .map(|(domv, t)| (*domv, crate::subst::apply_vterm_map(&renaming, t.clone()))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{hash, hash_sym, msg_var};
    use crate::lterm::LSort;
    use crate::positions::at_pos;

    #[test]
    fn canonical_substitution_handles_deep_range_terms_on_a_small_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            let domain = LVar::new("domain", LSort::Msg, 0);
            let mut range = msg_var("range", 0);
            for _ in 0..8192 {
                range = hash(range);
            }
            let canonical = canonize_subst(&LNSubstVFresh::from_list([(domain, range)]));
            let image = canonical.image_of(&domain).unwrap();
            assert_eq!(at_pos(image, &vec![0; 8192]), Some(msg_var("x", 1)));
        });
    }

    #[test]
    fn canonicalization_preserves_occurrence_ties_and_domain_order() {
        use crate::lterm::LSort;
        let a = LVar::new("a", LSort::Msg, 4);
        let z = LVar::new("z", LSort::Fresh, 1);
        assert_eq!(
            canonize_subst(&LNSubstVFresh::empty()),
            LNSubstVFresh::empty()
        );
        for sym in [
            FunSym::NoEq(crate::function_symbols::pair_sym()),
            FunSym::Ac(AcSym::Mult),
            FunSym::C(CSym::EMap),
            FunSym::List,
        ] {
            let range = crate::term::f_app(sym, vec![var_term(z), var_term(a)]);
            let subst =
                LNSubstVFresh::from_list([(z, crate::lterm::pub_term("ground")), (a, range)]);
            // Retain the previous independent variable collection as an oracle
            // for complete coverage, initial ordering and stable occurrence ties.
            let occs = var_occurences(subst.range());
            let mut vars = subst.vars_range();
            vars.sort_by(|a, b| occs.get(a).cmp(&occs.get(b)));
            let renaming = vars
                .into_iter()
                .enumerate()
                .map(|(i, v)| (v, var_term(LVar::new("x", v.sort, (i + 1) as u64))))
                .collect();
            let expected = LNSubstVFresh::from_list(
                subst
                    .to_list()
                    .into_iter()
                    .map(|(v, t)| (v, crate::subst::apply_vterm_map(&renaming, t))),
            );
            assert_eq!(canonize_subst(&subst), expected);
        }
    }

    #[test]
    fn occurrence_paths_preserve_noeq_indices_and_ac_symmetry() {
        let y = LVar::new("y", LSort::Msg, 0);
        let z = LVar::new("z", LSort::Msg, 0);
        let term = Term::App(
            FunSym::NoEq(hash_sym()),
            vec![
                var_term(y),
                Term::App(
                    FunSym::Ac(AcSym::Mult),
                    vec![var_term(z), var_term(y)].into(),
                ),
            ]
            .into(),
        );

        let occurrences = var_occurences(&[term]);
        assert_eq!(
            occurrences.get(&y).unwrap(),
            &BTreeSet::from([
                vec!["0".into(), "h".into(), "0".into()],
                vec!["AC Mult".into(), "1".into(), "h".into(), "0".into()],
            ])
        );
        assert_eq!(
            occurrences.get(&z).unwrap(),
            &BTreeSet::from([vec!["AC Mult".into(), "1".into(), "h".into(), "0".into(),]])
        );
    }
}
