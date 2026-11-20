//! A completed frontier returns bindings for all observed variables. Rule
//! variables are local to narrowing and never become substitution keys.
use super::{total, Error, Packet, RuleTable, WordSlice, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lean_unification::{initialize, MatchRows, Outcome, Substitutions};
use crate::lterm::{frees, LNTerm};
use crate::maude_sig::MaudeSig;
use crate::term::Term;
use rustc_hash::FxHashSet;
use tamarin_utils::cancellation;

// Per-query frontier budget. Certified destructor tables can continue to completion.
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
    fn tamarin_lean_general_variants(
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
        let observations = observations(query);
        let Some(packet) = self.table_packet(sig, observations)? else {
            return Ok(Outcome::Unsupported);
        };
        evaluate(&packet, sig, observations, Search::Checked)
    }
}

fn observations(query: &LNTerm) -> &[LNTerm] {
    match query {
        Term::App(FunSym::List, ts) => ts.as_ref(),
        _ => std::slice::from_ref(query),
    }
}

/// Run the unrestricted folding reference on the full user and builtin rule table.
/// Each returned binding row has a reachable normal variant. Termination and
/// complete coverage require a range-restricted, sort-preserving, convergent
/// finite-variant presentation modulo the declared C/AC axioms. An invalid
/// presentation may diverge. A missing result denotes an unrepresentable or
/// unsupported request or reply.
pub fn variants_for_convergent_theory(
    sig: &MaudeSig,
    query: &LNTerm,
) -> Result<Option<Substitutions>, Error> {
    let observations = observations(query);
    let Some(packet) = Packet::full_table(sig, observations)? else {
        return Ok(None);
    };
    match evaluate(&packet, sig, observations, Search::General)? {
        Outcome::Unsupported => Ok(None),
        Outcome::Complete(rows) => Ok(Some(rows)),
    }
}

enum Search {
    Checked,
    General,
}

fn evaluate(
    packet: &Packet,
    sig: &MaudeSig,
    observations: &[LNTerm],
    search: Search,
) -> Result<Outcome, Error> {
    let width = observations
        .iter()
        .flat_map(frees)
        .collect::<FxHashSet<_>>()
        .len();
    let (roots, rules) = packet.equations.split_at(observations.len());
    initialize()?;
    let nodes = packet.rows();
    let mut fuel = FRONTIER_DEPTH;
    LEAN_THREAD.with(|_| loop {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        // SAFETY: all slices remain live until the shim copies them, and
        // the unique result reference is released by MatchRows.
        let reply = MatchRows::new(unsafe {
            let decls = WordSlice::new(&packet.declarations);
            let rules = WordSlice::new(rules);
            let roots = WordSlice::new(roots);
            match search {
                Search::Checked => tamarin_lean_checked_variants(
                    decls,
                    nodes.as_ptr(),
                    nodes.len(),
                    rules,
                    roots,
                    FRONTIER_DEPTH,
                ),
                Search::General => tamarin_lean_general_variants(
                    decls,
                    nodes.as_ptr(),
                    nodes.len(),
                    rules,
                    roots,
                    fuel,
                ),
            }
        })?;
        if matches!(search, Search::General) && total::header(&reply)? == 3 {
            if reply.rows(0) != 1 {
                return Err(Error::InvalidStatus(255));
            }
            if fuel == u64::MAX {
                return Ok(Outcome::Unsupported);
            }
            fuel = fuel.saturating_mul(2);
            continue;
        }
        return total::decode_variants(packet, &reply, sig.enable_nat, width);
    })
}
