//! Request-local identity interning. Keys are full Rust values; hashes are
//! lookup accelerators, never semantic IDs. The reference transition and its
//! injectivity/stable-ID proofs live in the solver's
//! [IdentityTable module](https://github.com/kmilner/tamarin-algebra/blob/795e6c02146fc3d88bed8f166c1f4759cdf86545/lean/Tamarin/IdentityTable.lean).
//! Rust/C correspondence is still part of the trusted boundary.

use rustc_hash::FxHashMap;
use std::hash::Hash;

/// An identity table that finds values through a hash map.
pub(crate) type IdentityTable<K> = Table<K, 0>;

/// An identity table that finds a value by comparing it with each stored
/// value in turn while it holds at most `LINEAR` values: for a few values
/// with a cheap equality that is faster than hashing. The ids are those of
/// an [`IdentityTable`], the position of the first equal value.
pub(crate) type ShortIdentityTable<K, const LINEAR: usize> = Table<K, LINEAR>;

#[derive(Clone)]
pub(crate) struct Table<K, const LINEAR: usize> {
    /// Empty while the table holds at most `LINEAR` values.
    ids: FxHashMap<K, u64>,
    values: Vec<K>,
}

impl<K, const LINEAR: usize> Default for Table<K, LINEAR> {
    fn default() -> Self {
        Self {
            ids: FxHashMap::default(),
            values: Vec::new(),
        }
    }
}

impl<K: Copy + Eq + Hash, const LINEAR: usize> Table<K, LINEAR> {
    /// An empty table with room for `n` values.
    pub(crate) fn with_capacity(n: usize) -> Self {
        Self {
            ids: FxHashMap::default(),
            values: Vec::with_capacity(n),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.values.len()
    }

    pub(crate) fn values(&self) -> &[K] {
        &self.values
    }

    fn linear(&self) -> bool {
        self.values.len() <= LINEAR
    }

    /// IDs never truncate and remain stable for the lifetime of the request.
    pub(crate) fn intern(&mut self, value: K) -> Option<u64> {
        if self.linear() {
            // The first equal value, which is its own reverse lookup.
            if let Some(at) = self.values.iter().position(|v| *v == value) {
                return u64::try_from(at).ok();
            }
        } else if let Some(&id) = self.ids.get(&value) {
            return (self.get(id) == Some(value)).then_some(id);
        }
        let id = u64::try_from(self.values.len()).ok()?;
        self.values.push(value);
        if !self.linear() {
            if self.ids.is_empty() {
                // The table outgrew the linear search: index every value.
                for (at, v) in self.values.iter().enumerate() {
                    self.ids.insert(*v, u64::try_from(at).ok()?);
                }
            } else {
                self.ids.insert(value, id);
            }
        }
        Some(id)
    }

    pub(crate) fn id(&self, value: K) -> Option<u64> {
        if self.linear() {
            let at = self.values.iter().position(|v| *v == value)?;
            return u64::try_from(at).ok();
        }
        self.ids.get(&value).copied()
    }

    /// Check both directions before interpreting a kernel's numeric answer.
    pub(crate) fn get(&self, id: u64) -> Option<K> {
        let value = *self.values.get(usize::try_from(id).ok()?)?;
        (self.id(value) == Some(id)).then_some(value)
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
    fn a_linear_table_gives_the_ids_of_a_hashed_one_on_both_sides_of_its_bound() {
        let keys: Vec<LVar> = (0..40)
            .map(|i| LVar::new(["a", "b", "c"][i % 3], LSort::Msg, (i / 2) as u64))
            .collect();
        let mut hashed = IdentityTable::<LVar>::default();
        let mut linear = ShortIdentityTable::<LVar, 8>::default();
        for (step, key) in keys.iter().chain(keys.iter().rev()).enumerate() {
            assert_eq!(hashed.intern(*key), linear.intern(*key), "step {step}");
            assert_eq!(hashed.values(), linear.values());
            for id in 0..hashed.len() as u64 + 1 {
                assert_eq!(hashed.get(id), linear.get(id));
            }
            for probe in &keys {
                assert_eq!(hashed.id(*probe), linear.id(*probe));
            }
        }
        distinct::<LVar>(&keys[..20]);
        let mut small = ShortIdentityTable::<LVar, 8>::default();
        for (i, key) in keys[..20].iter().enumerate() {
            assert_eq!(small.intern(*key), Some(i as u64));
        }
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
