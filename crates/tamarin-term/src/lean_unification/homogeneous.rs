//! Materialize column-tagged AC images using the caller's fresh variable supply.
use super::{ac_sort, Error, MatchRows, WordSlice, LEAN_THREAD};
use crate::function_symbols::AcSym;
use crate::lterm::{LNTerm, LVar};
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use std::ffi::c_void;

#[repr(C)]
pub(super) struct ProjectedAnswers {
    status: u8,
    arms: *mut c_void,
}

impl ProjectedAnswers {
    pub(super) fn into_packet(self) -> Result<Option<MatchRows>, Error> {
        match self.status {
            0 => Ok(None),
            1 => MatchRows::new(self.arms).map(Some),
            status => Err(Error::InvalidStatus(status)),
        }
    }
}

unsafe extern "C" {
    fn tamarin_lean_masked_operand_unify(
        width: u64,
        mask: u64,
        sides: *const WordSlice,
        side_count: usize,
    ) -> ProjectedAnswers;
    fn tamarin_lean_operand_unify(
        width: u64,
        sides: *const WordSlice,
        side_count: usize,
    ) -> ProjectedAnswers;
}

pub(super) enum Allocation<T> {
    Complete(T),
    Unsupported,
    Exhausted,
}

impl<T> Allocation<T> {
    pub(super) fn map<U>(self, f: impl FnOnce(T) -> U) -> Allocation<U> {
        match self {
            Self::Complete(value) => Allocation::Complete(f(value)),
            Self::Unsupported => Allocation::Unsupported,
            Self::Exhausted => Allocation::Exhausted,
        }
    }
}

#[derive(Default)]
pub(super) struct MatrixCache {
    // These are exactly the kernel arguments. The packet contains column
    // tags and ordinal witnesses only; names and symbols belong to the caller.
    packets: FxHashMap<(usize, u64, Vec<Vec<u64>>), Option<MatchRows>>,
    stored_words: usize,
}

impl MatrixCache {
    pub(super) fn images(
        &mut self,
        remaining_calls: &mut usize,
        symbol: AcSym,
        reserved: &FxHashSet<u64>,
        width: usize,
        mask: u64,
        sides: Vec<Vec<u64>>,
    ) -> Result<Allocation<Vec<Vec<LNTerm>>>, Error> {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let key = (width, mask, sides);
        if let Some(cached) = self.packets.get(&key) {
            return match cached {
                Some(packet) => decode_packet(symbol, reserved, width, packet)
                    .map(|(images, _)| Allocation::Complete(images)),
                None => Ok(Allocation::Unsupported),
            };
        }
        let Some(left) = remaining_calls.checked_sub(1) else {
            return Ok(Allocation::Exhausted);
        };
        *remaining_calls = left;
        let rows: Vec<_> = key.2.iter().map(|side| WordSlice::new(side)).collect();
        let packet = LEAN_THREAD.with(|_| {
            // SAFETY: the borrowed descriptors and their words live through
            // this call. The shim transfers one owned reference to the packet.
            unsafe {
                if mask == 0 {
                    tamarin_lean_operand_unify(width as u64, rows.as_ptr(), rows.len())
                } else {
                    tamarin_lean_masked_operand_unify(width as u64, mask, rows.as_ptr(), rows.len())
                }
            }
            .into_packet()
        })?;
        let (result, packet_words) = match &packet {
            Some(p) => {
                let (images, words) = decode_packet(symbol, reserved, width, p)?;
                (Allocation::Complete(images), words)
            }
            None => (Allocation::Unsupported, 0),
        };
        // Bound retained input, arm and row storage even if a future checked
        // executable raises its own output limit. Oversize packets still run.
        let key_words = 2 + key.2.len() + key.2.iter().map(Vec::len).sum::<usize>();
        let total = self
            .stored_words
            .saturating_add(key_words)
            .saturating_add(packet_words);
        if total <= 65_536 {
            self.stored_words = total;
            self.packets.insert(key, packet);
        }
        Ok(result)
    }
}

// Lean tags each output row with its column and numbers witnesses densely in
// order of first use. Only the choice of unused caller names happens here.
pub(super) fn decode(
    symbol: AcSym,
    reserved: &FxHashSet<u64>,
    width: usize,
    packet: MatchRows,
) -> Result<Vec<Vec<LNTerm>>, Error> {
    decode_packet(symbol, reserved, width, &packet).map(|(images, _)| images)
}

fn decode_packet(
    symbol: AcSym,
    reserved: &FxHashSet<u64>,
    width: usize,
    packet: &MatchRows,
) -> Result<(Vec<Vec<LNTerm>>, usize), Error> {
    let mut packet_words = packet.count();
    tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
    let mut words = Vec::new();
    let mut answers = Vec::new();
    let mut names = Vec::new();
    let mut free = (0..=u64::MAX).filter(|idx| !reserved.contains(idx));
    for arm in 0..packet.count() {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        if packet.rows(arm) != width {
            return Err(Error::InvalidStatus(255));
        }
        let mut bindings = vec![None; width];
        for index in 0..width {
            let length = packet.row_size(arm, index)?;
            if length < 2 {
                return Err(Error::InvalidStatus(255));
            }
            packet_words = packet_words.saturating_add(1 + length);
            words.resize(length, 0);
            if packet.copy_row(arm, index, &mut words)? != length {
                return Err(Error::InvalidStatus(255));
            }
            decode_row(symbol, &words, &mut bindings, &mut names, &mut free)?;
        }
        let arm = bindings.into_iter().collect::<Option<Vec<_>>>();
        answers.push(arm.ok_or(Error::InvalidStatus(255))?);
    }
    Ok((answers, packet_words))
}

fn decode_row(
    symbol: AcSym,
    row: &[u64],
    bindings: &mut [Option<LNTerm>],
    names: &mut Vec<LVar>,
    free: &mut impl Iterator<Item = u64>,
) -> Result<(), Error> {
    let Some((&column, ordinals)) = row.split_first() else {
        return Err(Error::InvalidStatus(255));
    };
    let binding = usize::try_from(column)
        .ok()
        .and_then(|column| bindings.get_mut(column))
        .ok_or(Error::InvalidStatus(255))?;
    if ordinals.is_empty() || binding.is_some() {
        return Err(Error::InvalidStatus(255));
    }
    let mut factors = Vec::with_capacity(ordinals.len());
    for &ordinal in ordinals {
        let index = usize::try_from(ordinal).map_err(|_| Error::InvalidStatus(255))?;
        if index == names.len() {
            let fresh = free.next().ok_or(Error::FreshVariableOverflow)?;
            names.push(LVar::new("x", ac_sort(symbol), fresh));
        }
        let name = *names.get(index).ok_or(Error::InvalidStatus(255))?;
        factors.push(Term::Lit(Lit::Var(name)));
    }
    *binding = Some(f_app_ac(symbol, factors));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::LSort;

    #[test]
    fn cached_packets_rebuild_names_and_sorts_and_reuse_deferrals() {
        super::super::initialize().unwrap();
        let mut cache = MatrixCache::default();
        let mut calls = 1;
        let sides = vec![vec![0, 0], vec![1, 1]];
        for (symbol, sort, reserved, expected) in [
            (AcSym::Union, LSort::Msg, vec![0], 1),
            (AcSym::NatPlus, LSort::Nat, vec![0, 1], 2),
        ] {
            let avoid = reserved.into_iter().collect();
            let Allocation::Complete(images) = cache
                .images(&mut calls, symbol, &avoid, 2, 0, sides.clone())
                .unwrap()
            else {
                panic!("the same numeric matrix should need just one kernel call");
            };
            let witness = Term::Lit(Lit::Var(LVar::new("x", sort, expected)));
            assert_eq!(images, [vec![witness.clone(), witness]]);
        }
        assert_eq!(calls, 0);
        let avoid = FxHashSet::default();
        assert!(matches!(
            cache
                .images(&mut calls, AcSym::Union, &avoid, 3, 0, sides)
                .unwrap(),
            Allocation::Exhausted
        ));
        let mut calls = 1;
        for _ in 0..2 {
            let tautology = vec![vec![0, 1], vec![0, 1]];
            assert!(matches!(
                cache
                    .images(&mut calls, AcSym::Union, &avoid, 2, 0, tautology)
                    .unwrap(),
                Allocation::Unsupported
            ));
        }
        assert_eq!(calls, 0);
    }

    #[test]
    fn indivisible_columns_filter_before_projection_and_separate_cache_entries() {
        super::super::initialize().unwrap();
        let mut cache = MatrixCache::default();
        let mut calls = 2;
        let avoid = FxHashSet::default();
        // Four singleton operands on each side must be paired by a bijection.
        // The unrestricted edge-cover packet is too large to materialize.
        let sides = vec![vec![0, 1, 2, 3], vec![4, 5, 6, 7]];
        for (bits, expected) in [(0, None), (255, Some(24)), (255, Some(24)), (0, None)] {
            match cache
                .images(&mut calls, AcSym::Union, &avoid, 8, bits, sides.clone())
                .unwrap()
            {
                Allocation::Unsupported => assert_eq!(expected, None),
                Allocation::Complete(arms) => {
                    assert_eq!(Some(arms.len()), expected);
                    let mut assignments = std::collections::BTreeSet::new();
                    for arm in arms {
                        let (left, right) = arm.split_at(4);
                        assert!(left.iter().all(|x| matches!(x, Term::Lit(Lit::Var(_)))));
                        let owners: Vec<_> = right
                            .iter()
                            .map(|r| left.iter().position(|l| l == r).unwrap())
                            .collect();
                        assert_eq!(
                            owners
                                .iter()
                                .copied()
                                .collect::<std::collections::BTreeSet<_>>()
                                .len(),
                            4
                        );
                        assert!(assignments.insert(owners));
                    }
                }
                Allocation::Exhausted => {
                    panic!("masked and unrestricted cache entries should both be reusable")
                }
            }
        }
        assert_eq!(calls, 0);
    }

    #[test]
    fn projected_columns_share_dense_witnesses_across_rows_and_arms() {
        let mut names = Vec::new();
        let reserved = [0, 2, u64::MAX];
        let mut free = (0..=u64::MAX).filter(|idx| !reserved.contains(idx));
        let mut arm = [None, None];
        // The column tags place these images even when their rows arrive reversed.
        decode_row(AcSym::Union, &[1, 0], &mut arm, &mut names, &mut free).unwrap();
        decode_row(AcSym::Union, &[0, 1, 0, 1], &mut arm, &mut names, &mut free).unwrap();
        let var = |idx| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, idx)));
        assert_eq!(
            arm,
            [
                Some(f_app_ac(AcSym::Union, vec![var(3), var(1), var(3)])),
                Some(var(1))
            ]
        );

        let mut second = [None, None];
        decode_row(AcSym::Union, &[0, 1], &mut second, &mut names, &mut free).unwrap();
        decode_row(AcSym::Union, &[1, 2], &mut second, &mut names, &mut free).unwrap();
        assert_eq!(second, [Some(var(3)), Some(var(4))]);

        let mut last = std::iter::once(u64::MAX);
        let mut third = [None, None];
        decode_row(AcSym::Union, &[0, 3], &mut third, &mut names, &mut last).unwrap();
        assert_eq!(third[0], Some(var(u64::MAX)));
        assert_eq!(
            decode_row(AcSym::Union, &[1, 4], &mut third, &mut names, &mut last),
            Err(Error::FreshVariableOverflow)
        );
    }

    #[test]
    fn malformed_projected_rows_fail_without_expanding_ordinal_gaps() {
        let mut names = Vec::new();
        let mut free = 0..=u64::MAX;
        let mut arm = [None, None];
        for bad in [&[][..], &[0], &[2, 0], &[0, 1], &[0, u64::MAX]] {
            assert_eq!(
                decode_row(AcSym::Union, bad, &mut arm, &mut names, &mut free),
                Err(Error::InvalidStatus(255))
            );
            assert!(names.is_empty());
        }
        decode_row(AcSym::Union, &[0, 0], &mut arm, &mut names, &mut free).unwrap();
        assert_eq!(
            decode_row(AcSym::Union, &[0, 0], &mut arm, &mut names, &mut free),
            Err(Error::InvalidStatus(255))
        );
    }

    #[test]
    fn rejected_projection_reports_an_error_and_solver_deferral_is_unsupported() {
        let result = |status| ProjectedAnswers {
            status,
            arms: std::ptr::null_mut(),
        };
        assert!(matches!(result(0).into_packet(), Ok(None)));
        assert!(matches!(
            result(255).into_packet(),
            Err(Error::InvalidStatus(255))
        ));
        assert!(matches!(
            result(1).into_packet(),
            Err(Error::InvalidStatus(255))
        ));
    }
}
