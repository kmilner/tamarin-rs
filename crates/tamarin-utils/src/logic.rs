//! Port of `Logic.Connectives` from `lib/utils/src/Logic/Connectives.hs`.
//!
//! `Conj` and `Disj` are list-newtype wrappers used to track conjunctions
//! and disjunctions of atoms. The Haskell `MonadDisj` typeclass is omitted
//! — Rust callers can construct `Disj`/`Conj` values directly.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Conj<T>(pub Vec<T>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Disj<T>(pub Vec<T>);

impl<T> Conj<T> {
    pub fn new() -> Self { Conj(Vec::new()) }
    pub fn singleton(x: T) -> Self { Conj(vec![x]) }
    pub fn into_inner(self) -> Vec<T> { self.0 }
    pub fn as_slice(&self) -> &[T] { &self.0 }
    pub fn len(&self) -> usize { self.0.len() }
    pub fn is_empty(&self) -> bool { self.0.is_empty() }
}

impl<T> Disj<T> {
    pub fn new() -> Self { Disj(Vec::new()) }
    pub fn singleton(x: T) -> Self { Disj(vec![x]) }
    pub fn into_inner(self) -> Vec<T> { self.0 }
    pub fn as_slice(&self) -> &[T] { &self.0 }
    pub fn len(&self) -> usize { self.0.len() }
    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    /// Disjoin two computations. Concatenates the alternative lists,
    /// matching the Haskell `mplus` instance.
    pub fn or(mut self, mut other: Self) -> Self {
        self.0.append(&mut other.0);
        self
    }

    /// `contradictoryBecause`: an empty disjunction (i.e. `false`).
    ///
    /// Retained as a named-constructor alias mirroring the upstream Haskell
    /// API; equivalent to [`Disj::new`].
    pub fn contradiction() -> Self { Disj(Vec::new()) }
}

impl<T> Default for Conj<T> { fn default() -> Self { Conj::new() } }
impl<T> Default for Disj<T> { fn default() -> Self { Disj::new() } }

impl<T> FromIterator<T> for Conj<T> {
    fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Self {
        Conj(it.into_iter().collect())
    }
}

impl<T> FromIterator<T> for Disj<T> {
    fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Self {
        Disj(it.into_iter().collect())
    }
}

impl<T> IntoIterator for Conj<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter { self.0.into_iter() }
}

impl<T> IntoIterator for Disj<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter { self.0.into_iter() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disj_or_concatenates() {
        let a: Disj<i32> = vec![1, 2].into_iter().collect();
        let b: Disj<i32> = vec![3].into_iter().collect();
        assert_eq!(a.or(b), Disj(vec![1, 2, 3]));
    }

    #[test]
    fn contradiction_is_empty() {
        let c: Disj<i32> = Disj::contradiction();
        assert!(c.is_empty());
    }

    #[test]
    fn conj_singleton() {
        let c = Conj::singleton(7);
        assert_eq!(c.into_inner(), vec![7]);
    }
}
