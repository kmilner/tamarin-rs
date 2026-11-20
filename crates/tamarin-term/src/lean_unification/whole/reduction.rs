//! Checked reduction over the whole active table and the original input graph.
use super::Packet;
use crate::lean_unification::{initialize, Error, MatchRows, RuleTable, WordSlice, LEAN_THREAD};
use crate::lterm::LNTerm;
use crate::maude_sig::MaudeSig;

unsafe extern "C" {
    fn tamarin_lean_checked_reduce(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        rules: WordSlice,
        root: u64,
        fallback_depth: u64,
    ) -> *mut std::ffi::c_void;
}

impl RuleTable {
    /// Observation roots precede the (left, right) roots of every active rule.
    pub(in crate::lean_unification) fn table_packet(
        &self,
        sig: &MaudeSig,
        observations: &[LNTerm],
    ) -> Result<Option<Packet>, Error> {
        let Some(rules) = self.complete_rules() else {
            return Ok(None);
        };
        Packet::with_rules(sig, observations, rules)
    }

    pub(crate) fn checked_reduction(
        &self,
        sig: &MaudeSig,
        input: &LNTerm,
    ) -> Result<Option<LNTerm>, Error> {
        let Some(packet) = self.table_packet(sig, std::slice::from_ref(input))? else {
            return Ok(None);
        };
        initialize()?;
        let rows = packet.rows();
        LEAN_THREAD.with(|_| {
            // SAFETY: the shim copies all slices, and MatchRows owns the returned array.
            let reply = MatchRows::new(unsafe {
                tamarin_lean_checked_reduce(
                    WordSlice::new(&packet.declarations),
                    rows.as_ptr(),
                    rows.len(),
                    WordSlice::new(&packet.equations[1..]),
                    packet.equations[0],
                    // Certified definition and destructor tables ignore this fallback depth.
                    32,
                )
            })?;
            let mut status = [0];
            if reply.count() != 1
                || reply.row_size(0, 0)? != 1
                || reply.copy_row(0, 0, &mut status)? != 1
            {
                return Err(Error::InvalidStatus(255));
            }
            match (status[0], reply.rows(0)) {
                (2, 1) => Ok(None),
                (1, 2) => {
                    let mut words = vec![0; reply.row_size(0, 1)?];
                    if reply.copy_row(0, 1, &mut words)? != words.len() {
                        return Err(Error::InvalidStatus(255));
                    }
                    let result = packet.read_term(&words, sig.enable_nat)?;
                    let scope = crate::lterm::frees(input);
                    if crate::lterm::frees(&result)
                        .iter()
                        .any(|v| scope.binary_search(v).is_err())
                    {
                        return Err(Error::InvalidStatus(255));
                    }
                    Ok(Some(result))
                }
                _ => Err(Error::InvalidStatus(255)),
            }
        })
    }
}

impl Packet {
    pub(super) fn with_rules<'a>(
        sig: &MaudeSig,
        observations: &[LNTerm],
        rules: impl Iterator<Item = &'a crate::rewriting::RRule<LNTerm>>,
    ) -> Result<Option<Self>, Error> {
        let Some(mut packet) = Packet::encode_total(
            sig,
            observations
                .iter()
                .chain(rules.flat_map(|r| [&r.lhs, &r.rhs])),
        )?
        else {
            return Ok(None);
        };
        // Variants quantify over substitutions using any declared operator.
        for f in sig.declared_fun_syms() {
            use crate::function_symbols::FunSym;
            let kind = match f {
                FunSym::NoEq(_) => 2,
                FunSym::C(_) => 3,
                FunSym::Ac(_) => 4,
                FunSym::List => continue,
            };
            let (arity, sort) = crate::lean_unification::declaration(f, sig.enable_nat)
                .ok_or(Error::InvalidStatus(255))?;
            packet
                .symbol(f, kind, arity, sort)
                .ok_or(Error::InvalidStatus(255))?;
        }
        Ok(Some(packet))
    }
}
