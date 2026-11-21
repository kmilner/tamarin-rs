//! Request-local identity interning. Keys are full Rust values; hashes are
//! lookup accelerators, never semantic IDs. The reference transition and its
//! injectivity/stable-ID proofs live in the solver's
//! [IdentityTable module](https://github.com/kmilner/tamarin-algebra/blob/ef88e27d00d02a2c1490bd4f3fa7b6248ea52b17/lean/Tamarin/IdentityTable.lean).
//! Rust/C correspondence is still part of the trusted boundary.

use rustc_hash::FxHashMap;
use std::hash::Hash;

pub(crate) struct IdentityTable<K> {
    ids: FxHashMap<K, u64>,
    values: Vec<K>,
}

impl<K> Default for IdentityTable<K> {
    fn default() -> Self {
        Self {
            ids: FxHashMap::default(),
            values: Vec::new(),
        }
    }
}

impl<K: Copy + Eq + Hash> IdentityTable<K> {
    pub(crate) fn len(&self) -> usize {
        self.values.len()
    }

    pub(crate) fn values(&self) -> &[K] {
        &self.values
    }

    /// IDs never truncate and remain stable for the lifetime of the request.
    pub(crate) fn intern(&mut self, value: K) -> Option<u64> {
        if let Some(&id) = self.ids.get(&value) {
            return (self.get(id) == Some(value)).then_some(id);
        }
        let id = u64::try_from(self.values.len()).ok()?;
        self.values.push(value);
        self.ids.insert(value, id);
        Some(id)
    }

    pub(crate) fn id(&self, value: K) -> Option<u64> {
        self.ids.get(&value).copied()
    }

    /// Check both directions before interpreting a kernel's numeric answer.
    pub(crate) fn get(&self, id: u64) -> Option<K> {
        let value = *self.values.get(usize::try_from(id).ok()?)?;
        (self.ids.get(&value) == Some(&id)).then_some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{Constructability, NdcState, NoEqSym, Privacy};
    use crate::lterm::{LSort, LVar, Name, NameTag};

    fn distinct<K: Copy + Eq + Hash + std::fmt::Debug>(keys: &[K]) {
        let mut table = IdentityTable::default();
        for (i, key) in keys.iter().enumerate() {
            assert_eq!(table.intern(*key), Some(i as u64));
            for (j, earlier) in keys[..=i].iter().enumerate() {
                assert_eq!(table.get(j as u64), Some(*earlier));
                assert_eq!(table.intern(*earlier), Some(j as u64));
            }
        }
        assert_eq!(table.get(keys.len() as u64), None);
        assert_eq!(table.get(u64::MAX), None);
    }

    #[test]
    fn full_variable_name_and_symbol_identities_survive_interning() {
        distinct(&[
            LVar::new("x", LSort::Msg, u64::MAX),
            LVar::new("y", LSort::Msg, u64::MAX),
            LVar::new("x", LSort::Fresh, u64::MAX),
            LVar::new("x", LSort::Msg, 0),
        ]);
        distinct(&[
            Name::new(NameTag::Pub, "same"),
            Name::new(NameTag::Fresh, "same"),
        ]);
        let f = NoEqSym::new(b"same", 1, Privacy::Public, Constructability::Constructor);
        distinct(&[
            f,
            f.with_destructor(),
            f.with_ndc(NdcState::IsNdc),
            NoEqSym::new(b"same", 2, Privacy::Public, Constructability::Constructor),
            NoEqSym::new(b"same", 1, Privacy::Private, Constructability::Constructor),
        ]);
    }

    #[test]
    fn colliding_hashes_do_not_alias_and_corrupt_reverse_maps_are_rejected() {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        struct Collision(u8);
        impl Hash for Collision {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                0_u8.hash(state);
            }
        }
        distinct(&[Collision(0), Collision(1), Collision(2)]);
        let mut table = IdentityTable::default();
        table.intern(Collision(0)).unwrap();
        table.intern(Collision(1)).unwrap();
        table.ids.insert(Collision(0), 1);
        assert_eq!(table.get(0), None);
        assert_eq!(table.intern(Collision(0)), None);
    }
}
