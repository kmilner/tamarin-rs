//! A completed frontier returns bindings for all observed variables. Rule
//! variables are local to narrowing and never become substitution keys.
use super::{total, Error, Packet, RuleTable, WordSlice, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lean_unification::Watch;
use crate::lean_unification::{initialize, MatchRows, Outcome, Substitutions};
use crate::lterm::{frees, LNTerm};
use crate::maude_sig::MaudeSig;
use crate::term::Term;
use rustc_hash::FxHashSet;
use tamarin_utils::cancellation;

// Initial frontier budget. A certified table can continue with staged folding.
const FRONTIER_DEPTH: u64 = 4;

// Narrowing sites of the first call of the folding proposer, and the bound
// from which no further call is made. Every call starts over, so the budget
// grows fourfold: the calls before the one that finishes cost a third of it.
// The sites do not bound the unifications at a site, so a call is also
// interruptible: it stops on cancellation and after `search` search steps.
// The families of the queries that reach this proposer in the tests need
// fewer than 4,000 sites for up to 96 variants, at roughly 0.1 ms per site.
const FOLD_WORK: u64 = 1 << 13;
const FOLD_WORK_LIMIT: u64 = 1 << 19;
// Rewrite steps along one normalization path.
const FOLD_DEPTH: u64 = 1 << 16;

use tamarin_algebra_sys::{
    tamarin_lean_checked_variants, tamarin_lean_fold_variants, tamarin_lean_general_variants,
};

impl RuleTable {
    /// The bounded narrowing search as a proposal. When it does not finish
    /// within its frontier and `certified` says that the certifier accepted
    /// the session's table, unbounded folding continues it.
    pub(crate) fn checked_variants(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        certified: impl FnOnce() -> bool,
    ) -> Result<Outcome, Error> {
        let observations = observations(query);
        let Some(packet) = self.table_packet(sig, observations)? else {
            return Ok(Outcome::Unsupported);
        };
        evaluate(&packet, sig, observations, Search::Checked, 0, certified)
    }

    /// Folding variant narrowing in Maude's order, as a proposal: the family
    /// carries no theorem and is for the certificate checker to accept. The
    /// request is unsupported when the table or a variant is outside the
    /// search or its wire format, and an error beyond `FOLD_WORK_LIMIT`
    /// narrowing sites. One call stops, with [`Error::Cancelled`] or
    /// [`Error::SearchBudget`], when the request is cancelled or the call
    /// takes more than `search` search steps (zero for no bound).
    pub(crate) fn fold_variants(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        search: u64,
    ) -> Result<Outcome, Error> {
        let observations = observations(query);
        let Some(packet) = self.table_packet(sig, observations)? else {
            return Ok(Outcome::Unsupported);
        };
        evaluate(&packet, sig, observations, Search::Fold, search, || false)
    }
}

/// Whether an AC product of the query holds a factor outside the sort of its
/// operator. Maude accepts such a product at the kind level and no
/// well-sorted theory produces one. The folding proposer is for sorted
/// queries, so such a query gets its proposal from the bounded search.
pub(crate) fn kind_level(query: &LNTerm) -> bool {
    use crate::lean_unification::{ac_sort, subsort};
    use crate::lterm::sort_of_lnterm;
    match query {
        Term::Lit(_) => false,
        Term::App(f, args) => {
            let outside = match f {
                FunSym::Ac(ac) => args
                    .iter()
                    .any(|arg| !subsort(sort_of_lnterm(arg), ac_sort(*ac))),
                _ => false,
            };
            outside || args.iter().any(kind_level)
        }
    }
}

pub(super) fn observations(query: &LNTerm) -> &[LNTerm] {
    match query {
        Term::App(FunSym::List, ts) => ts.as_ref(),
        _ => std::slice::from_ref(query),
    }
}

/// Run the unrestricted folding reference on the full user and builtin rule table.
/// Every successful binding row reconstructs a unique normal variant. Termination and
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
    match evaluate(&packet, sig, observations, Search::General, 0, || false)? {
        Outcome::Unsupported => Ok(None),
        Outcome::Complete(rows) => Ok(Some(rows)),
    }
}

enum Search {
    Checked,
    General,
    Fold,
}

fn evaluate(
    packet: &Packet,
    sig: &MaudeSig,
    observations: &[LNTerm],
    mut search: Search,
    steps: u64,
    certified: impl FnOnce() -> bool,
) -> Result<Outcome, Error> {
    let width = observations
        .iter()
        .flat_map(frees)
        .collect::<FxHashSet<_>>()
        .len();
    let (roots, rules) = packet.equations.split_at(observations.len());
    initialize()?;
    let nodes = packet.rows();
    let declarations = packet.declarations()?;
    let mut certified = Some(certified);
    let mut fuel = FRONTIER_DEPTH;
    let mut work = FOLD_WORK;
    LEAN_THREAD.with(|_| loop {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        let started = std::time::Instant::now();
        let mut watch = Watch::new("variant search", steps);
        // SAFETY: all slices and the watch remain live through the call, and
        // the unique result reference is released by MatchRows.
        let raw = unsafe {
            let decls = WordSlice::new(declarations);
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
                Search::Fold => tamarin_lean_fold_variants(
                    decls,
                    nodes.as_ptr(),
                    nodes.len(),
                    rules,
                    roots,
                    FOLD_DEPTH,
                    work,
                    watch.raw(),
                ),
            }
        };
        // A stopped call returned no reply. Only the folding proposer
        // touches the watch.
        watch.finish()?;
        let reply = MatchRows::new(raw)?;
        if matches!(search, Search::Fold) {
            if tamarin_utils::env_gate!("TAM_DBG_VARIANTS") {
                eprintln!(
                    "[variants] fold work {work}: status {} after {} ms",
                    total::header(&reply).unwrap_or(255),
                    started.elapsed().as_millis()
                );
            }
            return match total::header(&reply)? {
                3 if reply.rows(0) == 1 && work < FOLD_WORK_LIMIT => {
                    work = work.saturating_mul(4);
                    continue;
                }
                // Out of budget. The Lean searches that would follow have no
                // bound and cannot be interrupted.
                3 if reply.rows(0) == 1 => Err(Error::VariantSearchBudget { work }),
                _ => total::decode_variants(packet, &reply, sig.enable_nat, width),
            };
        }
        // Staged folding preserves unique reconstruction on a certified table.
        if matches!(search, Search::Checked)
            && total::header(&reply)? == 2
            && reply.rows(0) == 1
            && certified.take().is_some_and(|certified| certified())
        {
            search = Search::General;
            continue;
        }
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
