//! Port of `Control.Monad.Fresh` and friends.
//!
//! The Haskell originals are monad transformers (`FreshT`) layered over user
//! state. Rust callers just thread a `FreshState` value (or `&mut FreshState`)
//! explicitly — no transformer stack required. We provide both the *fast*
//! flavour (single counter) and the *precise* flavour (per-name counter).

use crate::FastMap;

// =============================================================================
// Fast: single global counter.
// =============================================================================

/// Single-counter fresh-name supply (`Control.Monad.Trans.FastFresh`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FastFreshState {
    next: u64,
}

impl FastFreshState {
    /// Empty supply.
    pub fn nothing_used() -> Self { FastFreshState { next: 0 } }

    /// Supply seeded so the first `fresh_ident` yields `seed` (HS
    /// `evalFresh action seed` over the `FastFresh` `FreshState = Integer`).
    /// Used by `Sapic.States.addStatesChannels`, which seeds the counter at
    /// `initStateChan` (the next free `StateChannel` index).
    pub fn seeded(seed: u64) -> Self { FastFreshState { next: seed } }

    /// Allocate `k` consecutive identifiers and return the first one.
    pub fn fresh_idents(&mut self, k: u64) -> u64 {
        let i = self.next;
        self.next += k;
        i
    }

    /// Allocate one identifier.
    pub fn fresh_ident(&mut self) -> u64 { self.fresh_idents(1) }

    /// Run `f` against this state but discard any allocations it made.
    pub fn scope_freshness<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R {
        let saved = self.next;
        let r = f(self);
        self.next = saved;
        r
    }
}

// =============================================================================
// Precise: per-name counters.
// =============================================================================

/// Per-name fresh-name supply (`Control.Monad.Trans.PreciseFresh`).
///
/// Tracks the next unused index for each *name hint*. The empty-string slot
/// is reserved by `fresh_idents` for storing the maximum index, mirroring the
/// Haskell implementation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreciseFreshState {
    map: FastMap<String, u64>,
}

impl PreciseFreshState {
    pub fn nothing_used() -> Self { PreciseFreshState { map: FastMap::default() } }

    /// Port of HS `avoidPreciseVars` (Term/LTerm.hs:681-684):
    /// `foldl' (\m (name, idx) -> insertWith max name (idx+1) m) empty`.
    /// Seeds the per-name counters so the next `fresh_ident name` yields an
    /// index strictly greater than every avoided `(name, idx)`.  Used by
    /// `Sapic.Typing.renameUnique` to avoid colliding with the process's
    /// existing variables.
    pub fn avoid_precise<I: IntoIterator<Item = (String, u64)>>(vars: I) -> Self {
        let mut map: FastMap<String, u64> = FastMap::default();
        for (name, idx) in vars {
            let want = idx + 1;
            map.entry(name)
                .and_modify(|cur| { if want > *cur { *cur = want; } })
                .or_insert(want);
        }
        PreciseFreshState { map }
    }

    /// Get a fresh identifier for `name`. The next call with the same name
    /// yields the next sequential index.
    pub fn fresh_ident(&mut self, name: &str) -> u64 {
        // Avoid allocating a `String` key on the common cache-hit path; only
        // allocate when inserting a genuinely new name.
        if let Some(entry) = self.map.get_mut(name) {
            let i = *entry;
            *entry = i + 1;
            i
        } else {
            self.map.insert(name.to_string(), 1);
            0
        }
    }

    /// Reserve `k` identifiers across *all* names. Returns the first reserved
    /// index. After this call, every existing name's counter (and "") is set
    /// to `prev_max + k`.
    pub fn fresh_idents(&mut self, k: u64) -> u64 {
        let max_idx = self.map.values().copied().max().unwrap_or(0);
        let next_idx = max_idx + k;
        for v in self.map.values_mut() {
            *v = next_idx;
        }
        self.map.insert(String::new(), next_idx);
        max_idx
    }

    /// Run `f` and roll the state back afterwards.
    pub fn scope_freshness<R, F: FnOnce(&mut Self) -> R>(&mut self, f: F) -> R {
        let saved = self.map.clone();
        let r = f(self);
        self.map = saved;
        r
    }

    /// Read-only view of the underlying counters.
    pub fn as_map(&self) -> &FastMap<String, u64> { &self.map }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fast_increments() {
        let mut s = FastFreshState::nothing_used();
        assert_eq!(s.fresh_ident(), 0);
        assert_eq!(s.fresh_ident(), 1);
        assert_eq!(s.fresh_idents(3), 2);
        assert_eq!(s.fresh_ident(), 5);
    }

    #[test]
    fn fast_scope_rolls_back() {
        let mut s = FastFreshState::nothing_used();
        s.fresh_ident();
        s.scope_freshness(|s| {
            s.fresh_idents(10);
        });
        assert_eq!(s.fresh_ident(), 1);
    }

    #[test]
    fn precise_per_name_counters() {
        let mut s = PreciseFreshState::nothing_used();
        assert_eq!(s.fresh_ident("x"), 0);
        assert_eq!(s.fresh_ident("y"), 0);
        assert_eq!(s.fresh_ident("x"), 1);
        assert_eq!(s.fresh_ident("y"), 1);
    }

    #[test]
    fn precise_fresh_idents_advances_all() {
        let mut s = PreciseFreshState::nothing_used();
        s.fresh_ident("x");
        s.fresh_ident("x"); // x counter = 2
        assert_eq!(s.fresh_idents(5), 2);
        // After fresh_idents, every counter is at 2 + 5 = 7.
        assert_eq!(s.as_map().get("x"), Some(&7));
        assert_eq!(s.as_map().get(""), Some(&7));
    }

    #[test]
    fn precise_scope_rolls_back() {
        let mut s = PreciseFreshState::nothing_used();
        s.fresh_ident("x");
        s.scope_freshness(|s| {
            s.fresh_ident("x");
            s.fresh_ident("y");
        });
        // Outside the scope only the "x" allocation remains.
        assert_eq!(s.fresh_ident("x"), 1);
        assert_eq!(s.fresh_ident("y"), 0);
    }
}
