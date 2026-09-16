//! Owned traversal stacks whose remaining items retain LIFO order on unwind.

/// A Vec-backed worklist that also pops its remaining items when dropped.
/// Ordinary Vec destruction visits elements in storage order, reversing a
/// stack traversal's pending sibling order if a payload destructor panics.
pub struct DropStack<T>(Vec<T>);

impl<T> From<Vec<T>> for DropStack<T> {
    fn from(items: Vec<T>) -> Self {
        Self(items)
    }
}

impl<T> std::ops::Deref for DropStack<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> std::ops::DerefMut for DropStack<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Drop for DropStack<T> {
    fn drop(&mut self) {
        while let Some(item) = self.0.pop() {
            drop(item);
        }
    }
}
