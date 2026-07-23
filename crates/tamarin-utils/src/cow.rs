//! Copy-on-write helpers for structural rebuilds.
//!
//! A recursive rebuild — substitution, AC canonicalisation, variable renaming —
//! is very often a *no-op*: nothing under a node actually changes.  The COW
//! convention used throughout the port is for each rebuild step to return
//! `Option<T>`: `None` when its input is structurally unchanged (so the caller
//! reuses the input by clone/move, sharing `Arc`s), `Some(rebuilt)` otherwise.
//!
//! These two combinators are the shared plumbing for that convention.  The
//! per-node `match` stays at the call site (it carries the term/formula
//! structure); only the lazy bookkeeping lives here, so the subtle
//! "allocate the `Vec` lazily, cloning the unchanged prefix on the first change"
//! logic exists in exactly one place instead of being hand-copied per node type.

/// COW-map a slice: apply `f` to each element and return `None` iff `f` returned
/// `None` for *every* element (the whole slice is unchanged).  Otherwise return
/// the rebuilt `Vec`, allocated lazily on the first change: the unchanged prefix
/// is cloned once, then each element is carried as its rebuilt value (`Some`) or
/// a clone of the original (`None`), preserving positional order.
///
/// Byte-identical to an eager `xs.iter().map(|x| f(x).unwrap_or_else(|| x.clone())).collect()`
/// (modulo the elided allocation when nothing changed).
#[inline]
pub fn cow_map_vec<T: Clone>(xs: &[T], mut f: impl FnMut(&T) -> Option<T>) -> Option<Vec<T>> {
    let mut out: Option<Vec<T>> = None;
    for (i, x) in xs.iter().enumerate() {
        match f(x) {
            Some(g) => out.get_or_insert_with(|| xs[..i].to_vec()).push(g),
            None => {
                if let Some(v) = out.as_mut() {
                    v.push(x.clone());
                }
            }
        }
    }
    out
}

/// COW-combine two independently-rebuilt fields (possibly of different types):
/// `None` iff both are unchanged (`fx` and `fy` both `None`); otherwise fill
/// each unchanged side by cloning its original.  `fx`/`fy` are the already-
/// computed per-field COW results.
#[inline]
pub fn cow_pair<T: Clone, U: Clone>(x: &T, fx: Option<T>, y: &U, fy: Option<U>) -> Option<(T, U)> {
    if fx.is_none() && fy.is_none() {
        return None;
    }
    Some((
        fx.unwrap_or_else(|| x.clone()),
        fy.unwrap_or_else(|| y.clone()),
    ))
}

/// COW-map an `Arc<[T]>` (a shared slice): like [`cow_map_vec`], but rebuilds
/// into a fresh `Arc<[T]>`.  `None` when every element is unchanged, so the
/// caller reuses the original `Arc` (no allocation); `Some` carries the rebuilt
/// slice with the unchanged prefix cloned and changed elements rebuilt.
#[inline]
pub fn cow_map_arc<T: Clone>(
    xs: &std::sync::Arc<[T]>,
    f: impl FnMut(&T) -> Option<T>,
) -> Option<std::sync::Arc<[T]>> {
    cow_map_vec(&xs[..], f).map(std::sync::Arc::from)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Negate even numbers; leave odds unchanged (None).
    fn neg_even(n: &i32) -> Option<i32> {
        if n % 2 == 0 {
            Some(-n)
        } else {
            None
        }
    }

    #[test]
    fn all_unchanged_returns_none() {
        assert_eq!(cow_map_vec(&[1, 3, 5], neg_even), None);
    }

    #[test]
    fn rebuilt_matches_eager_with_prefix_and_suffix() {
        // index 1 changes; prefix [1] is cloned, suffix [5] cloned, middle rebuilt.
        let got = cow_map_vec(&[1, 4, 5], neg_even);
        let eager: Vec<i32> = [1, 4, 5]
            .iter()
            .map(|x| neg_even(x).unwrap_or(*x))
            .collect();
        assert_eq!(got, Some(eager));
        assert_eq!(got, Some(vec![1, -4, 5]));
    }

    #[test]
    fn empty_slice_is_unchanged() {
        assert_eq!(cow_map_vec::<i32>(&[], neg_even), None);
    }

    #[test]
    fn pair_both_unchanged_is_none() {
        assert_eq!(cow_pair(&1, None, &"a", None::<&str>), None);
    }

    #[test]
    fn pair_fills_unchanged_side_by_clone() {
        assert_eq!(cow_pair(&1, None, &2, Some(20)), Some((1, 20)));
        assert_eq!(cow_pair(&1, Some(10), &2, None), Some((10, 2)));
        assert_eq!(cow_pair(&1, Some(10), &2, Some(20)), Some((10, 20)));
    }

    #[test]
    fn map_arc_rebuilds_into_fresh_arc() {
        let xs: std::sync::Arc<[i32]> = std::sync::Arc::from(vec![1, 2, 3]);
        assert_eq!(cow_map_arc(&xs, neg_even).as_deref(), Some(&[1, -2, 3][..]));
        let ys: std::sync::Arc<[i32]> = std::sync::Arc::from(vec![1, 3, 5]);
        assert_eq!(cow_map_arc(&ys, neg_even), None);
    }
}
