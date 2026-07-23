// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/utils/src/Control/Monad/Bind.hs

//! Port of `Control.Monad.Bind` from `lib/utils/src/Control/Monad/Bind.hs`.
//!
//! A simple key/value binding store. The Haskell version is a `StateT` over
//! a `Data.Map`; in Rust we expose plain methods on a `Bindings` struct and
//! pair it with a `PreciseFreshState` for `import_binding`.
//!
//! Backed by a `HashMap` rather than the Haskell `Data.Map`; this is safe
//! because bindings are only looked up by key and are never iterated into
//! pretty-printed output (iteration order is therefore not observable).

use std::hash::Hash;

use crate::FastMap;

use crate::fresh::PreciseFreshState;

/// Binding store keyed by `K`, holding values of type `V`.
#[derive(Debug, Clone)]
pub struct Bindings<K, V> {
    map: FastMap<K, V>,
}

impl<K, V> Default for Bindings<K, V> {
    fn default() -> Self {
        Bindings {
            map: FastMap::default(),
        }
    }
}

impl<K, V> Bindings<K, V>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        Bindings::default()
    }

    /// `noBindings`: retained as a named-constructor alias mirroring the
    /// upstream Haskell API; equivalent to [`Bindings::new`].
    pub fn no_bindings() -> Self {
        Bindings::default()
    }

    /// `lookupBinding`.
    pub fn lookup(&self, k: &K) -> Option<&V> {
        self.map.get(k)
    }

    /// `insertBinding`. Overwrites any existing entry.
    pub fn insert(&mut self, k: K, v: V) {
        self.map.insert(k, v);
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// `importBinding mkR k name`: if `k` is already bound, return the
    /// existing value; otherwise allocate a fresh identifier for `name` from
    /// `fresh`, build a new value via `mk`, store it, and return it.
    pub fn import_binding<F>(&mut self, fresh: &mut PreciseFreshState, mk: F, k: K, name: &str) -> V
    where
        K: Clone,
        V: Clone,
        F: FnOnce(&str, u64) -> V,
    {
        if let Some(v) = self.map.get(&k) {
            return v.clone();
        }
        let i = fresh.fresh_ident(name);
        let v = mk(name, i);
        self.map.insert(k, v.clone());
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_and_insert() {
        let mut b: Bindings<&'static str, i32> = Bindings::new();
        assert_eq!(b.lookup(&"x"), None);
        b.insert("x", 7);
        assert_eq!(b.lookup(&"x"), Some(&7));
        b.insert("x", 8);
        assert_eq!(b.lookup(&"x"), Some(&8));
    }

    #[test]
    fn import_binding_caches() {
        let mut fresh = PreciseFreshState::nothing_used();
        let mut b: Bindings<&'static str, (String, u64)> = Bindings::new();
        let mk = |n: &str, i: u64| (n.to_string(), i);

        let v1 = b.import_binding(&mut fresh, mk, "alice", "user");
        let v2 = b.import_binding(&mut fresh, mk, "alice", "user");
        // Cached, so identical:
        assert_eq!(v1, v2);
        // A different key allocates a new identifier:
        let v3 = b.import_binding(&mut fresh, mk, "bob", "user");
        assert_ne!(v1, v3);
        assert_eq!(v3.1, 1);
    }
}
