//! Checked reduction over the whole active table and the original input graph.
use super::{total, Packet};
use crate::lean_unification::{initialize, Error, MatchRows, RuleTable, WordSlice, LEAN_THREAD};
use crate::lterm::LNTerm;
use crate::maude_sig::MaudeSig;
use tamarin_utils::cancellation;

unsafe extern "C" {
    fn tamarin_lean_checked_reduce(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        rules: WordSlice,
        root: u64,
        fallback_depth: u64,
    ) -> *mut std::ffi::c_void;
    fn tamarin_lean_general_reduce(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        rules: WordSlice,
        root: u64,
        fuel: u64,
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
        evaluate(&packet, sig, input, false)
    }
}

/// Check every rewrite alternative on the submitted term against the full active
/// table. A canonical range-restricted presentation eventually gives a unique
/// normal form. Each successful stage establishes uniqueness independently.
pub fn reduction_for_convergent_theory(
    sig: &MaudeSig,
    input: &LNTerm,
) -> Result<Option<LNTerm>, Error> {
    let Some(packet) = Packet::full_table(sig, std::slice::from_ref(input))? else {
        return Ok(None);
    };
    evaluate(&packet, sig, input, true)
}

fn evaluate(
    packet: &Packet,
    sig: &MaudeSig,
    input: &LNTerm,
    reference: bool,
) -> Result<Option<LNTerm>, Error> {
    initialize()?;
    let rows = packet.rows();
    let mut fuel = if reference { 4 } else { 32 };
    LEAN_THREAD.with(|_| loop {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        // SAFETY: all slices live through the call. MatchRows owns the returned array.
        let reply = MatchRows::new(unsafe {
            let kernel = if reference {
                tamarin_lean_general_reduce
            } else {
                tamarin_lean_checked_reduce
            };
            kernel(
                WordSlice::new(&packet.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations[1..]),
                packet.equations[0],
                fuel,
            )
        })?;
        match (total::header(&reply)?, reply.rows(0)) {
            (3, 1) if reference && fuel < u64::MAX => fuel = fuel.saturating_mul(2),
            (3, 1) if reference => return Ok(None),
            (2, 1) => return Ok(None),
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
                return Ok(Some(result));
            }
            _ => return Err(Error::InvalidStatus(255)),
        }
    })
}

impl Packet {
    pub(super) fn full_table(
        sig: &MaudeSig,
        observations: &[LNTerm],
    ) -> Result<Option<Self>, Error> {
        // The algebra consumes expanded terms. encode_total checks every rule and
        // observation against the actual module declarations, including in theories
        // that also carry parser-only macro names.
        if sig.enable_diff || (sig.enable_bp && !sig.enable_dh) {
            return Ok(None);
        }
        Self::with_rules(sig, observations, sig.rrules().iter())
    }

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
