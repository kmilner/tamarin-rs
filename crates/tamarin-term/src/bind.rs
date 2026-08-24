// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Control.Monad.Bind` (Control/Monad/Bind.hs:53-58,
//! Control/Monad/Bind.hs:114-140) at the key and value type its consumers use,
//! `LVar`, plus the two renamings Haskell builds on it: `someInst`
//! (Term/LTerm.hs:627-632) and `renamePrecise` (Term/LTerm.hs:717-735).
//!
//! Haskell threads the binding store as a `StateT (Bindings k v)` and the
//! identifier supply as a `MonadFresh` layer of the same stack; here both are
//! `&mut` arguments, so a caller that seeds the store (HS
//! `evalBindT … keepVarBindings`) hands in a [`Bindings`] it has filled with
//! [`Bindings::insert`].

use crate::lterm::{HasFrees, LVar};
use tamarin_utils::fresh::{MonadFresh, PreciseFreshState};

/// Binding-store key wrapping the bound `LVar`.
///
/// `Hash` delegates to `LVar`'s content-based derive, so two vars with equal
/// *content* always hash to the same bucket even when their interned name
/// pointers differ (a rare non-canonical literal name vs the pooled copy) —
/// this is what keeps the dedup correct and the `--prove` output byte-identical.
/// Only `Eq` is optimised, via [`lvar_fast_eq`] — same relation as `LVar`'s derive.
#[derive(Clone, Debug)]
struct VarKey(LVar);

impl PartialEq for VarKey {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        lvar_fast_eq(&self.0, &other.0)
    }
}
impl Eq for VarKey {}
impl std::hash::Hash for VarKey {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}
// Lets `get` probe by `&LVar` (no clone) yet run the fast eq.  The probe
// hashes via `LVar`'s derive (identical to `VarKey::hash`), so it lands in the
// bucket holding the owned key.
impl hashbrown::Equivalent<VarKey> for LVar {
    #[inline]
    fn equivalent(&self, key: &VarKey) -> bool {
        lvar_fast_eq(self, &key.0)
    }
}

/// Exactly `LVar`'s content equality, faster: interned names share one
/// canonical pointer (intern guarantees content-equal ⇒ pointer-equal), so a
/// pointer+len match confirms the name without the byte compare; anything else
/// falls back to the full content compare, so the relation is unchanged.
#[inline]
fn lvar_fast_eq(a: &LVar, b: &LVar) -> bool {
    // Destructure without `..` so a new `LVar` field forces an equality decision
    // here, keeping this fast path in step with `LVar`'s derived Eq.
    let LVar {
        name: a_name,
        sort: a_sort,
        idx: a_idx,
    } = a;
    let LVar {
        name: b_name,
        sort: b_sort,
        idx: b_idx,
    } = b;
    // idx (u64) first — most discriminating, cheapest — then sort, so a
    // hash-collision mismatch is rejected before the name is touched.
    if a_idx != b_idx || a_sort != b_sort {
        return false;
    }
    (std::ptr::eq(a_name.as_ptr(), b_name.as_ptr()) && a_name.len() == b_name.len())
        || a_name == b_name
}

/// The store: keyed by [`VarKey`] (content hash, fast pointer eq), hashed with
/// the same `FxBuildHasher` as `FastMap`.  Haskell's `Bindings` is a
/// `Data.Map` (Control/Monad/Bind.hs:53-58); iteration order is never observed here —
/// [`Bindings::iter`]'s only consumers build a `Subst` (a re-sorted
/// `BTreeMap`) and a distinct-key substitution applied by lookup.
type BindMap = hashbrown::HashMap<VarKey, LVar, rustc_hash::FxBuildHasher>;

/// `Bindings LVar LVar` (Control/Monad/Bind.hs:53-58) — one binding per variable, allocated
/// on first occurrence by [`Bindings::import`].
#[derive(Clone, Debug, Default)]
pub struct Bindings {
    map: BindMap,
    changed: bool,
}

impl Bindings {
    /// `noBindings` (Control/Monad/Bind.hs:56-58).
    pub fn new() -> Self {
        Bindings::default()
    }

    /// `importBinding` (Control/Monad/Bind.hs:125-140) at the value constructor both
    /// `someInst` (Term/LTerm.hs:632) and `renamePrecise`
    /// (Term/LTerm.hs:726-735) pass it: the first call for `v` allocates an
    /// `LVar` that keeps `v`'s name and sort and takes its index from `fresh`
    /// under the name hint `v.name`; later calls return that same binding.
    pub fn import<M: MonadFresh>(&mut self, v: &LVar, fresh: &mut M) -> LVar {
        self.import_named(v, v.name, fresh)
    }

    /// `renameDropNamehint` (Term/LTerm.hs:737-740): the same import under the
    /// EMPTY name hint, so the binding keeps `v`'s sort and carries the empty
    /// name.  Two variables that share an index and a sort but differ in name
    /// stay two bindings, each with its own index, which is what lets a
    /// comparison of the results ignore the name hints.
    pub fn import_drop_namehint<M: MonadFresh>(&mut self, v: &LVar, fresh: &mut M) -> LVar {
        self.import_named(v, "", fresh)
    }

    /// `importBinding mkR v name` (Control/Monad/Bind.hs:125-140) where `mkR`
    /// builds an `LVar` from the hint and the drawn index under `v`'s sort: the
    /// first call for `v` draws an index from `fresh` under the hint `name` and
    /// binds `v` to it; later calls return that binding.
    fn import_named<M: MonadFresh>(&mut self, v: &LVar, name: &'static str, fresh: &mut M) -> LVar {
        // Probe by `&LVar` (no clone) via `VarKey`'s `Equivalent` impl, whose
        // `eq` short-circuits on the interned name POINTER — skipping the
        // byte-wise `str` compare that dominated `import`'s confirming-eq self
        // time (`equal_same_length` in the profile) — with a content fallback
        // that keeps the equality RELATION exactly `LVar`'s.  The hash is still
        // content-based (see `VarKey`), so equal-content vars — even with
        // different name pointers — dedup into one slot: output is identical.
        if let Some(bound) = self.map.get(v) {
            return *bound;
        }
        let idx = fresh.fresh_ident(name);
        // Record whether this first binding remaps the variable (the sort is
        // always preserved), so an all-identity prefix leaves `changed` false.
        if idx != v.idx || name != v.name {
            self.changed = true;
        }
        let bound = LVar {
            name,
            sort: v.sort,
            idx,
        };
        // First occurrence only (rare): materialise the owned key.
        self.map.insert(VarKey(*v), bound);
        bound
    }

    /// `insertBinding` (Control/Monad/Bind.hs:119-123).  Overwrites any existing binding of
    /// `k`.  Seeding `k -> k` is how a caller keeps a variable unchanged
    /// across [`some_inst`] (HS `keepVarBindings`).
    pub fn insert(&mut self, k: LVar, v: LVar) {
        if !lvar_fast_eq(&k, &v) {
            self.changed = true;
        }
        self.map.insert(VarKey(k), v);
    }

    /// `lookupBinding` (Control/Monad/Bind.hs:114-117).
    pub fn get(&self, v: &LVar) -> Option<LVar> {
        self.map.get(v).copied()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Whether any binding maps a variable to a different one.
    /// [`Self::import`] preserves name and sort, so over the bindings it
    /// allocated alone this says that some variable takes a new index.
    pub fn changed(&self) -> bool {
        self.changed
    }

    /// Every `(bound variable, its binding)` pair, in the store's own order.
    pub fn iter(&self) -> impl Iterator<Item = (LVar, LVar)> + '_ {
        self.map.iter().map(|(k, v)| (k.0, *v))
    }
}

/// `someInst t` (Term/LTerm.hs:627-632): replace every free variable whose
/// binding the caller has not already determined by a fresh variable of the
/// same name and sort, reusing one binding per variable.
///
/// Two passes where Haskell has one `mapFrees`: the walk allocates the
/// bindings in visit order, then the map applies them by lookup.  The result
/// is the same because a binding depends only on where its variable is first
/// seen, and splitting the pass lets a type walk its fields in Haskell's
/// container order while rebuilding them in its own storage order.
pub fn some_inst<T: HasFrees, M: MonadFresh>(t: T, bindings: &mut Bindings, fresh: &mut M) -> T {
    t.for_each_free(&mut |v| {
        bindings.import(v, fresh);
    });
    t.map_free(&mut |v| bindings.get(&v).unwrap_or(v))
}

/// `renamePrecise t` (Term/LTerm.hs:717-735): replace every free variable with
/// a fresh one, numbering each name from zero, so that two values differing
/// only in variable indices map to the same result.  It is [`some_inst`] over
/// an empty store and a per-name identifier supply.
pub fn rename_precise<T: HasFrees>(t: T) -> T {
    some_inst(
        t,
        &mut Bindings::new(),
        &mut PreciseFreshState::nothing_used(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::LSort;
    use tamarin_utils::fresh::FastFreshState;

    fn msg(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }

    #[test]
    fn bindings_import_is_idempotent() {
        // `importBinding` allocates on the first occurrence and returns the
        // stored binding afterwards, so a repeated variable never draws a
        // second identifier.
        let mut fresh = PreciseFreshState::nothing_used();
        let mut bindings = Bindings::new();
        let x = msg("x", 7);
        let first = bindings.import(&x, &mut fresh);
        let second = bindings.import(&x, &mut fresh);
        assert_eq!(first, msg("x", 0));
        assert_eq!(second, first);
        assert_eq!(bindings.get(&x), Some(first));
        // The next variable of that name takes the next index, which it would
        // not if the second import had consumed one.
        assert_eq!(bindings.import(&msg("x", 9), &mut fresh), msg("x", 1));
    }

    #[test]
    fn bindings_report_a_remap() {
        // The flag distinguishes an all-identity store from one that moved a
        // variable; `import` keeps name and sort, so only the index can move.
        let mut fresh = PreciseFreshState::nothing_used();
        let mut bindings = Bindings::new();
        bindings.import(&msg("x", 0), &mut fresh);
        assert!(!bindings.changed());
        bindings.import(&msg("y", 3), &mut fresh);
        assert!(bindings.changed());

        let mut seeded = Bindings::new();
        seeded.insert(msg("x", 4), msg("x", 4));
        assert!(!seeded.changed());
        seeded.insert(msg("y", 1), msg("y", 2));
        assert!(seeded.changed());
    }

    #[test]
    fn rename_precise_reuses_per_name_counters() {
        // Each name is numbered from zero and a repeated variable keeps its
        // first binding, so the shape of the value survives the rename.
        assert_eq!(
            rename_precise(vec![msg("x", 7), msg("y", 3), msg("x", 7)]),
            vec![msg("x", 0), msg("y", 0), msg("x", 0)]
        );
        // Two different variables of one name take consecutive indices.
        assert_eq!(
            rename_precise(vec![msg("x", 7), msg("x", 2)]),
            vec![msg("x", 0), msg("x", 1)]
        );
    }

    #[test]
    fn some_inst_allocates_once_per_variable_in_visit_order() {
        // The supply is asked for one identifier per distinct variable, in the
        // order `for_each_free` reaches them.  Under the Fast supply the name
        // hint is ignored, so the indices count the allocations.
        let mut fresh = FastFreshState::nothing_used();
        let mut bindings = Bindings::new();
        let renamed = some_inst(
            vec![msg("x", 7), msg("y", 3), msg("x", 7), msg("z", 0)],
            &mut bindings,
            &mut fresh,
        );
        assert_eq!(
            renamed,
            vec![msg("x", 0), msg("y", 1), msg("x", 0), msg("z", 2)]
        );
        // The store outlives the call, so a second value shares the bindings
        // of the variables it has in common with the first.
        let again = some_inst(vec![msg("y", 3), msg("w", 5)], &mut bindings, &mut fresh);
        assert_eq!(again, vec![msg("y", 1), msg("w", 3)]);
    }

    #[test]
    fn some_inst_keeps_seeded_bindings() {
        // HS `evalBindT (someInst sysTh0) keepVarBindings` with
        // `keepVarBindings = M.fromList (map (\v -> (v, v)) vs)`: a variable
        // bound to itself is found in the store, so it is neither renamed nor
        // charged an identifier.
        let mut fresh = FastFreshState::nothing_used();
        let mut bindings = Bindings::new();
        let keep = msg("x", 7);
        bindings.insert(keep, keep);
        let renamed = some_inst(vec![keep, msg("y", 3)], &mut bindings, &mut fresh);
        assert_eq!(renamed, vec![keep, msg("y", 0)]);
    }
}
