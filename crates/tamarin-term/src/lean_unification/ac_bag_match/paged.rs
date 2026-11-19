//! Collect a complete directional matching family, checking capture sorts before
//! charging the Rust terms that will be returned. The verified cursor counts
//! raw picks, including picks whose empty or ill-sorted images are discarded.
use super::*;
use crate::lean_unification::{tamarin_lean_match_release, tamarin_lean_match_row_size, MatchRows};
use crate::term::f_app_ac;
use std::ffi::c_void;

unsafe extern "C" {
    fn tamarin_lean_ac_bag_answers(rows: *const WordSlice, count: usize) -> *mut c_void;
    fn tamarin_lean_ac_bag_packet(rows: *const WordSlice, count: usize) -> *mut c_void;
    fn tamarin_lean_ac_bag_page(
        packet: *mut c_void,
        cursor: WordSlice,
        requested: u64,
    ) -> *mut c_void;
}

// The public API returns a Vec, so both the work for discarded picks and the
// storage for retained arms must fit a request. Each Lean call also caps its
// own transient words, reducing the page size when a pick is wide.
const RAW_LIMIT: u64 = 65_536;
const OUTPUT_LIMIT: usize = 262_144;
const PAGE_SIZE: u64 = 256;

struct Packet(*mut c_void);

impl Packet {
    fn new(slices: &[WordSlice]) -> Result<Self, Error> {
        // SAFETY: the shim copies both the descriptors and all occurrence IDs
        // before returning. The one owned array is released by this guard.
        let raw = unsafe { tamarin_lean_ac_bag_packet(slices.as_ptr(), slices.len()) };
        if raw.is_null() {
            Err(Error::InvalidStatus(255))
        } else {
            Ok(Self(raw))
        }
    }

    fn page(&self, cursor: &[u64], requested: u64) -> Result<Option<MatchRows>, Error> {
        // SAFETY: self keeps the packet live and the shim copies cursor. A
        // successful call transfers one new owned reply.
        let raw = unsafe { tamarin_lean_ac_bag_page(self.0, WordSlice::new(cursor), requested) };
        if raw.is_null() {
            Ok(None)
        } else {
            Ok(Some(MatchRows::new(raw)?))
        }
    }
}

impl Drop for Packet {
    fn drop(&mut self) {
        // SAFETY: this guard owns the packet reference from the shim.
        unsafe { tamarin_lean_match_release(self.0) };
    }
}

struct Output<'a, 't> {
    head: AcSym,
    vars: &'a IdentityTable<LVar>,
    factors: &'a IdentityTable<&'t LNTerm>,
    available: usize,
    arms: Substitutions,
}

impl Output<'_, '_> {
    /// Lean returns images in first-encounter key order. A strict subsort can
    /// only accept a singleton, whose sort is the frozen subject factor's sort.
    fn well_sorted(&self, reply: &MatchRows, index: usize) -> Result<bool, Error> {
        for (k, var) in self.vars.values().iter().enumerate() {
            if subsort(ac_sort(self.head), var.sort) {
                continue;
            }
            if reply.row_size(index, k)? != 1 {
                return Ok(false);
            }
            let mut id = [0];
            reply.copy_row(index, k, &mut id)?;
            let factor = self.factors.get(id[0]).ok_or(Error::InvalidStatus(255))?;
            if !subsort(sort_of_lterm(factor, sort_of_name), var.sort) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn append(&mut self, reply: &MatchRows, first: usize) -> Result<bool, Error> {
        let mut ids = Vec::new();
        for index in first..reply.count() {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            if reply.rows(index) != self.vars.len() {
                return Err(Error::InvalidStatus(255));
            }
            if !self.well_sorted(reply, index)? {
                continue;
            }
            let Some(rest) = self.available.checked_sub(1) else {
                return Ok(false);
            };
            self.available = rest;
            let mut arm = Vec::with_capacity(self.vars.len());
            for (k, &var) in self.vars.values().iter().enumerate() {
                let len = reply.row_size(index, k)?;
                // Every occurrence costs at least one node. A product also
                // allocates its own head above its frozen factors.
                let head_node = usize::from(len > 1);
                if len + head_node > self.available {
                    return Ok(false);
                }
                self.available -= head_node;
                ids.resize(len, 0);
                if reply.copy_row(index, k, &mut ids)? != len {
                    return Err(Error::InvalidStatus(255));
                }
                let terms = ids
                    .iter()
                    .map(|&id| {
                        self.factors
                            .get(id)
                            .cloned()
                            .ok_or(Error::InvalidStatus(255))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if !residual::charge_expansion(&mut self.available, &terms, None)? {
                    return Ok(false);
                }
                arm.push((var, f_app_ac(self.head, terms)));
            }
            self.arms.push(arm);
        }
        Ok(true)
    }
}

// The fixed wrapper encodes Nat as canonical little-endian limbs. Anything
// larger than one limb already exceeds this collector's u64 raw budget.
fn small_ordinal(reply: &MatchRows, field: usize) -> Result<Option<u64>, Error> {
    // SAFETY: the C accessor checks both indices. An empty ordinal represents zero.
    match unsafe { tamarin_lean_match_row_size(reply.0, 0, field) } {
        0 => Ok(Some(0)),
        1 => {
            let mut limb = [0];
            reply.copy_row(0, field, &mut limb)?;
            Ok(Some(limb[0]))
        }
        usize::MAX => Err(Error::InvalidStatus(255)),
        _ => Ok(None),
    }
}

fn collect(
    mut output: Output<'_, '_>,
    raw_limit: u64,
    requested: u64,
    mut page: impl FnMut(&[u64], u64) -> Result<Option<MatchRows>, Error>,
) -> Result<Option<Substitutions>, Error> {
    let mut start = 0u64;
    let mut known_total = None;
    loop {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let limbs = [start];
        let cursor = if start == 0 { &[][..] } else { &limbs[..] };
        let reply = page(cursor, requested)?;
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let Some(reply) = reply else { return Ok(None) };
        if reply.count() == 0 || reply.rows(0) != 3 || reply.row_size(0, 1)? != 1 {
            return Err(Error::InvalidStatus(255));
        }
        let Some(total) = small_ordinal(&reply, 2)? else {
            return Ok(None);
        };
        if total > raw_limit {
            return Ok(None);
        }
        let stop = small_ordinal(&reply, 0)?.ok_or(Error::InvalidStatus(255))?;
        let mut done = [0];
        reply.copy_row(0, 1, &mut done)?;
        let span = stop.checked_sub(start).ok_or(Error::InvalidStatus(255))?;
        if known_total.is_some_and(|previous| previous != total)
            || stop > total
            || span > requested
            || done[0] != u64::from(stop == total)
            || (span == 0 && stop != total)
            || (reply.count() - 1) as u64 > span
        {
            return Err(Error::InvalidStatus(255));
        }
        if !output.append(&reply, 1)? {
            return Ok(None);
        }
        if stop == total {
            return Ok(Some(output.arms));
        }
        start = stop;
        known_total = Some(total);
    }
}

pub(super) fn read_answers(
    head: AcSym,
    vars: &IdentityTable<LVar>,
    factors: &IdentityTable<&LNTerm>,
    slices: &[WordSlice],
) -> Result<Option<Substitutions>, Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        let mut output = Output {
            head,
            vars,
            factors,
            available: OUTPUT_LIMIT,
            arms: Vec::new(),
        };
        // SAFETY: the slices stay live while the shim copies this packet. As
        // before, the eager search may return a complete family or defer.
        let raw = unsafe { tamarin_lean_ac_bag_answers(slices.as_ptr(), slices.len()) };
        if !raw.is_null() {
            let reply = MatchRows::new(raw)?;
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            return Ok(output.append(&reply, 0)?.then_some(output.arms));
        }
        let packet = Packet::new(slices)?;
        collect(output, RAW_LIMIT, PAGE_SIZE, |cursor, n| {
            packet.page(cursor, n)
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{pub_term, LSort};
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};

    fn with_three_factors(run: impl FnOnce(&Packet, Output<'_, '_>)) {
        initialize().unwrap();
        LEAN_THREAD.with(|_| {
            let mut vars = IdentityTable::default();
            for key in ["x", "y"] {
                vars.intern(LVar::new(key, LSort::Msg, 0)).unwrap();
            }
            let atoms = ["a", "b", "c"].map(pub_term);
            let mut factors = IdentityTable::default();
            for atom in &atoms {
                factors.intern(atom).unwrap();
            }
            let input =
                Packet::new(&[WordSlice::new(&[0, 1]), WordSlice::new(&[0, 1, 2])]).unwrap();
            run(
                &input,
                Output {
                    head: AcSym::Union,
                    vars: &vars,
                    factors: &factors,
                    available: 30,
                    arms: Vec::new(),
                },
            );
        });
    }

    #[test]
    fn exact_raw_and_output_limits_include_the_boundary_and_discard_any_prefix_on_overflow() {
        // Eight raw assignments. Six are onto, each costs the arm, the three
        // atoms, and one product node. Single-pick pages also test empty
        // initial/final pages, both excluded by nonemptiness.
        for (raw, nodes, complete) in [(8, 30, true), (7, 30, false), (8, 29, false)] {
            with_three_factors(|input, mut output| {
                output.available = nodes;
                let mut calls = 0;
                let got = collect(output, raw, 1, |cursor, requested| {
                    calls += 1;
                    input.page(cursor, requested)
                })
                .unwrap();
                assert_eq!(got.map(|arms| arms.len()), complete.then_some(6));
                if raw == 7 {
                    assert_eq!(calls, 1);
                } else if nodes == 29 {
                    assert_eq!(calls, 7);
                } else {
                    assert_eq!(calls, 8);
                }
            });
        }
    }

    #[test]
    fn cancellation_after_a_nonempty_page_discards_the_partial_family() {
        with_three_factors(|input, output| {
            let token = CancellationToken::default();
            let _guard = CancellationGuard::new(Some(token.clone()));
            let mut calls = 0;
            let got = collect(output, 8, 1, |cursor, n| {
                calls += 1;
                let reply = input.page(cursor, n)?;
                if calls == 2 {
                    assert!(reply.as_ref().unwrap().count() > 1);
                }
                if calls == 3 {
                    token.request_cancel();
                }
                Ok(reply)
            });
            assert_eq!(got, Err(Error::Cancelled));
            assert_eq!(calls, 3);
        });
    }

    #[test]
    fn physical_cursor_can_resume_beyond_u64_and_finish_without_traversing_a_prefix() {
        initialize().unwrap();
        LEAN_THREAD.with(|_| {
            let ids: Vec<_> = (0..65).collect();
            let input = Packet::new(&[WordSlice::new(&[0, 1]), WordSlice::new(&ids)]).unwrap();
            // [2^65 - 2, 2^65) contains the last onto assignment and the
            // all-to-one assignment. Only the former is a matching arm.
            let page = input.page(&[u64::MAX - 1, 1], 2).unwrap().unwrap();
            assert_eq!(page.count(), 2);
            let mut words = [0; 2];
            for field in [0, 2] {
                assert_eq!(page.copy_row(0, field, &mut words).unwrap(), 2);
                assert_eq!(words, [0, 2]);
            }
            assert_eq!(page.copy_row(0, 1, &mut words).unwrap(), 1);
            assert_eq!(words[0], 1);
            let mut sizes = [page.row_size(1, 0).unwrap(), page.row_size(1, 1).unwrap()];
            sizes.sort();
            assert_eq!(sizes, [1, 64]);
        });
    }
}
