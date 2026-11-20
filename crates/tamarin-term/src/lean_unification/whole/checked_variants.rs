//! A completed frontier returns bindings for all observed variables. Rule
//! variables are local to narrowing and never become substitution keys.
use super::{total, Error, RuleTable, WordSlice, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lean_unification::{initialize, MatchRows, Outcome};
use crate::lterm::{frees, LNTerm};
use crate::maude_sig::MaudeSig;
use crate::term::Term;
use rustc_hash::FxHashSet;

// The fallback checks closure at this depth before publishing any rows.
const FRONTIER_DEPTH: u64 = 4;

unsafe extern "C" {
    fn tamarin_lean_checked_variants(
        decls: WordSlice,
        nodes: *const WordSlice,
        count: usize,
        rules: WordSlice,
        observations: WordSlice,
        fuel: u64,
    ) -> *mut std::ffi::c_void;
}

impl RuleTable {
    pub(crate) fn checked_variants(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
    ) -> Result<Outcome, Error> {
        let observations = match query {
            Term::App(FunSym::List, ts) => ts.as_ref(),
            _ => std::slice::from_ref(query),
        };
        let Some(packet) = self.table_packet(sig, observations)? else {
            return Ok(Outcome::Unsupported);
        };
        let width = observations
            .iter()
            .flat_map(frees)
            .collect::<FxHashSet<_>>()
            .len();
        let (roots, rules) = packet.equations.split_at(observations.len());
        initialize()?;
        let nodes = packet.rows();
        LEAN_THREAD.with(|_| {
            // SAFETY: all slices remain live until the shim copies them, and
            // the unique result reference is released by MatchRows.
            let reply = MatchRows::new(unsafe {
                tamarin_lean_checked_variants(
                    WordSlice::new(&packet.declarations),
                    nodes.as_ptr(),
                    nodes.len(),
                    WordSlice::new(rules),
                    WordSlice::new(roots),
                    FRONTIER_DEPTH,
                )
            })?;
            total::decode_variants(&packet, &reply, sig.enable_nat, width)
        })
    }
}
