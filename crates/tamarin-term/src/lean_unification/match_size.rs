//! Exclude a directional match without expanding shared terms or trying variable images.
use super::{residual::MAX_EXPANDED, subsort, Error, RuleTable, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lterm::{LNTerm, LSort};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;

unsafe extern "C" {
    fn tamarin_match_size_excludes(pattern: u64, subject: u64) -> u8;
}

struct Sizes {
    // The request owns these child slices throughout the query. A public caller
    // can use the same slice with different heads; include the head in its key.
    apps: FxHashMap<(FunSym, *const LNTerm, usize), (LSort, u64)>,
    remaining: usize,
}

impl Sizes {
    fn read(&mut self, table: &RuleTable, t: &LNTerm, depth: usize) -> Option<(LSort, u64)> {
        self.remaining = self.remaining.checked_sub(1)?;
        if depth > 256 {
            return None;
        }
        let (f, args) = match t {
            Term::Lit(lit) => {
                let (sort, size) = match lit {
                    Lit::Var(v) => (v.sort, 0),
                    Lit::Con(c) => (sort_of_name(c), 1),
                };
                return table.declares_sort(sort).then_some((sort, size));
            }
            Term::App(f, args) => (*f, args),
        };
        let key = (f, args.as_ptr(), args.len());
        if let Some(&known) = self.apps.get(&key) {
            return Some(known);
        }
        let (_, sort) = table.input_declaration(f, args.len())?;
        if !table.unambiguous_head(&f) || args.len() > self.remaining {
            return None;
        }
        // A flattened n-ary AC term represents n - 1 binary operators.
        // Adding shared children's counts at each occurrence gives the exact
        // expanded rigid size up to u64::MAX, independent of sharing.
        let mut size = if matches!(f, FunSym::Ac(_)) {
            u64::try_from(args.len() - 1).ok()?
        } else {
            1
        };
        for arg in args.iter() {
            let (child_sort, child_size) = self.read(table, arg, depth + 1)?;
            if !subsort(child_sort, sort) {
                return None;
            }
            size = size.saturating_add(child_size);
        }
        self.apps.insert(key, (sort, size));
        Some((sort, size))
    }
}

impl RuleTable {
    /// A substitution can only increase rigid size; B preserves it. Positive
    /// exclusion in any conjunct refutes every scoped match. Read the entire
    /// signature and all arities/sorts before accepting that certificate.
    pub(crate) fn refutes_match_size(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, Error> {
        let mut sizes = Sizes {
            apps: FxHashMap::default(),
            remaining: MAX_EXPANDED,
        };
        let mut excluded = false;
        super::initialize()?;
        for eq in eqs {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let (Some((_, left)), Some((_, right))) =
                (sizes.read(self, &eq.lhs, 0), sizes.read(self, &eq.rhs, 0))
            else {
                return Ok(false);
            };
            if !excluded {
                // SAFETY: the initialized Lean export takes only two unboxed
                // UInt64 words and returns an unboxed Bool.
                let result =
                    LEAN_THREAD.with(|_| unsafe { tamarin_match_size_excludes(left, right) });
                match result {
                    0 => {}
                    1 => excluded = true,
                    other => return Err(Error::InvalidStatus(other)),
                }
            }
        }
        Ok(excluded)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::pair;
    use crate::function_symbols::AcSym;
    use crate::lterm::{pub_term, LVar};
    use crate::maude_sig::{mset_maude_sig, pair_maude_sig};
    use crate::term::f_app_ac;
    use crate::vterm::var_term;

    #[test]
    fn an_unread_conjunct_keeps_a_provisional_refutation_from_escaping() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let a = pub_term("a");
        let x = var_term(LVar::new("x", LSort::Msg, 0));
        let wide = Term::App(
            FunSym::Ac(AcSym::Union),
            vec![a.clone(); MAX_EXPANDED].into(),
        );
        let equations = [
            Equal {
                lhs: f_app_ac(AcSym::Union, vec![a.clone(); 2]),
                rhs: a,
            },
            Equal { lhs: x, rhs: wide },
        ];
        assert!(table.refutes_match_size(&equations[..1]).unwrap());
        assert!(!table.refutes_match_size(&equations).unwrap());
    }

    #[test]
    fn reader_counts_occurrences_at_each_shared_edge_and_saturates() {
        let table = RuleTable::new(&pair_maude_sig().merge(mset_maude_sig())).unwrap();
        let x = var_term(LVar::new("x", LSort::Msg, 0));
        let doubled = |mut t: LNTerm, levels| {
            for _ in 0..levels {
                t = pair(t.clone(), t);
            }
            t
        };
        let size = |t: &LNTerm| {
            Sizes {
                apps: FxHashMap::default(),
                remaining: MAX_EXPANDED,
            }
            .read(&table, t, 0)
            .unwrap()
            .1
        };
        assert_eq!(size(&doubled(x.clone(), 16)), (1 << 16) - 1);
        assert_eq!(size(&doubled(pub_term("c"), 63)), u64::MAX);
        assert_eq!(size(&doubled(x, 71)), u64::MAX);
        let a = pub_term("a");
        let flat = f_app_ac(AcSym::Union, vec![a.clone(); 12]);
        let binary = (1..12).fold(a.clone(), |t, _| {
            Term::App(FunSym::Ac(AcSym::Union), vec![a.clone(), t].into())
        });
        assert_eq!(size(&flat), 23);
        assert_eq!(size(&binary), size(&flat));
    }
}
