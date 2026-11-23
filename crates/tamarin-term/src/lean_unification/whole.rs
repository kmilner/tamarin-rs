//! Submit equations as a shared graph. Lean counts operands for homogeneous AC
//! systems and checks identity, closed clashes, and incompatible variable-image
//! sizes on the original equation roots.
mod checked_variants;
pub(crate) use checked_variants::kind_level;
pub use checked_variants::variants_for_convergent_theory;
mod packed;
pub(crate) use packed::{unpack_conjunction, Conjunction};
mod reduction;
pub use reduction::reduction_for_convergent_theory;
pub(crate) use reduction::{FamilyCheck, Reduced, ReductionTable};
mod total;
pub use total::UnifyReplies;
pub(crate) use total::{
    has_match as total_has_match, matches as total_match, unify as total_unify,
    unify_exists as total_unify_exists,
};

use super::{initialize, sort_word, Error, RuleTable, WordSlice, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lean_identity::IdentityTable;
use crate::lterm::{LNTerm, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;

// Canonicalization expands each equation's two roots, even when their numeric
// rows are shared. Charge the fully expanded size across the whole request.
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 128;

#[derive(Default, Clone)]
pub(crate) struct Packet {
    variables: IdentityTable<LVar>,
    names: IdentityTable<Name>,
    symbols: IdentityTable<FunSym>,
    declarations: Vec<u64>,
    nodes: FxHashMap<Box<[u64]>, u64>,
    equations: Vec<u64>,
    expanded: usize,
}

impl Packet {
    fn node(&mut self, row: &[u64]) -> u64 {
        if let Some(&id) = self.nodes.get(row) {
            return id;
        }
        let id = self.nodes.len() as u64;
        self.nodes.insert(row.into(), id);
        id
    }

    fn term(&mut self, table: &RuleTable, term: &LNTerm) -> Option<u64> {
        self.encode_term(
            term,
            true,
            |sort| table.declares_sort(sort),
            |f| table.declaration(f).map(|(_, arity, sort)| (arity, sort)),
        )
    }

    fn symbol(
        &mut self,
        f: FunSym,
        kind: u64,
        arity: usize,
        output: crate::lterm::LSort,
    ) -> Option<u64> {
        if let Some(id) = self.symbols.id(f) {
            return Some(id);
        }
        let id = self.symbols.intern(f)?;
        let sort = sort_word(output);
        self.declarations.extend([kind, id, arity as u64, sort]);
        self.declarations.extend(std::iter::repeat_n(sort, arity));
        Some(id)
    }

    // Children precede their parents in the graph. The bounded kernels charge
    // expanded visits, while the total reference accepts the entire query.
    fn encode_term(
        &mut self,
        term: &LNTerm,
        bounded: bool,
        declares: impl Fn(crate::lterm::LSort) -> bool,
        declaration: impl Fn(FunSym) -> Option<(usize, crate::lterm::LSort)>,
    ) -> Option<u64> {
        enum Visit<'a> {
            Term(&'a LNTerm, usize),
            Finish(u64, u64, usize),
        }
        let mut work = vec![Visit::Term(term, 0)];
        let mut values = Vec::new();
        while let Some(visit) = work.pop() {
            match visit {
                Visit::Finish(kind, symbol, count) => {
                    let start = values.len() - count;
                    let mut node = Vec::with_capacity(count + 2);
                    node.extend([kind, symbol]);
                    node.extend(values.drain(start..));
                    values.push(self.node(&node));
                }
                Visit::Term(term, depth) => {
                    self.expanded += 1;
                    if bounded && (self.expanded > MAX_NODES || depth > MAX_DEPTH) {
                        return None;
                    }
                    match term {
                        Term::Lit(lit) => {
                            let (kind, id, sort) = match lit {
                                Lit::Var(v) => (0, self.variables.intern(*v)?, v.sort),
                                Lit::Con(n) => (1, self.names.intern(*n)?, sort_of_name(n)),
                            };
                            if !declares(sort) {
                                return None;
                            }
                            values.push(self.node(&[kind, id, sort_word(sort)]));
                        }
                        Term::App(f, children) => {
                            let (arity, output) = declaration(*f)?;
                            let kind = match f {
                                FunSym::NoEq(_) if children.len() == arity => 2,
                                FunSym::C(_) if children.len() == 2 => 3,
                                FunSym::Ac(_) if children.len() >= 2 => 4,
                                _ => return None,
                            };
                            if bounded && children.len() > MAX_NODES - self.expanded {
                                return None;
                            }
                            let id = self.symbol(*f, kind, arity, output)?;
                            work.push(Visit::Finish(kind, id, children.len()));
                            work.extend(children.iter().rev().map(|t| Visit::Term(t, depth + 1)));
                        }
                    }
                }
            }
        }
        values.pop()
    }

    fn roots<'a>(
        &mut self,
        table: &RuleTable,
        equations: impl IntoIterator<Item = (&'a LNTerm, &'a LNTerm)>,
    ) -> Result<Option<Vec<u64>>, Error> {
        let mut roots = Vec::new();
        for (lhs, rhs) in equations {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let (Some(lhs), Some(rhs)) = (self.term(table, lhs), self.term(table, rhs)) else {
                return Ok(None);
            };
            roots.extend([lhs, rhs]);
        }
        Ok(Some(roots))
    }

    fn encode(table: &RuleTable, equations: &[Equal<LNTerm>]) -> Result<Option<Self>, Error> {
        let mut packet = Self::default();
        let Some(roots) = packet.roots(table, equations.iter().map(|eq| (&eq.lhs, &eq.rhs)))?
        else {
            return Ok(None);
        };
        packet.equations = roots;
        Ok(Some(packet))
    }

    // The caller has initialized Lean and holds the current thread registration.
    fn certifies_table(&self, rules: &[u64], fuel: u64) -> Result<bool, Error> {
        use tamarin_algebra_sys::tamarin_lean_certify_table;
        let nodes = self.rows();
        // SAFETY: the shim copies all words while the borrowed slices are live.
        match unsafe {
            tamarin_lean_certify_table(
                WordSlice::new(&self.declarations),
                nodes.as_ptr(),
                nodes.len(),
                WordSlice::new(rules),
                fuel,
            )
        } {
            0 => Ok(false),
            1 => Ok(true),
            status => Err(Error::InvalidStatus(status)),
        }
    }

    /// Everything the total exports read of a request, as one key: the
    /// declarations, the node rows in order and the equation roots, each
    /// behind its length.
    fn request_words(&self) -> Box<[u64]> {
        let mut rows = vec![&[][..]; self.nodes.len()];
        for (row, &id) in &self.nodes {
            rows[id as usize] = row;
        }
        let mut words = Vec::with_capacity(
            3 + self.declarations.len()
                + rows.iter().map(|r| r.len() + 1).sum::<usize>()
                + self.equations.len(),
        );
        words.push(self.declarations.len() as u64);
        words.extend(&self.declarations);
        words.push(rows.len() as u64);
        for row in rows {
            words.push(row.len() as u64);
            words.extend(row);
        }
        words.push(self.equations.len() as u64);
        words.extend(&self.equations);
        words.into_boxed_slice()
    }

    fn rows(&self) -> Vec<WordSlice> {
        let mut rows = vec![WordSlice::new(&[]); self.nodes.len()];
        for (row, &id) in &self.nodes {
            rows[id as usize] = WordSlice::new(row);
        }
        rows
    }
}

use tamarin_algebra_sys::{
    tamarin_lean_check_factors, tamarin_lean_factor_refutes, tamarin_lean_operand_refine,
    tamarin_lean_variant_overlap_agrees,
};

// The selector observes only root identity. A local table suffices even when
// substitution or decomposition has manufactured new residual roots.
pub(super) fn refine_pending(eqs: &mut Vec<Equal<LNTerm>>) -> Result<(), Error> {
    if !(2..=64).contains(&eqs.len()) {
        return Ok(());
    }
    let roots = root_ids(eqs.iter().map(|eq| (&eq.lhs, &eq.rhs)))?;
    if let Some(kept) = select_rows(eqs, &roots)? {
        *eqs = kept;
    }
    Ok(())
}

fn root_ids<'a>(pairs: impl Iterator<Item = (&'a LNTerm, &'a LNTerm)>) -> Result<Vec<u64>, Error> {
    let mut ids = IdentityTable::default();
    pairs
        .flat_map(|(left, right)| [left, right])
        .map(|t| ids.intern(t).ok_or(Error::InvalidStatus(255)))
        .collect()
}

fn select_rows(eqs: &[Equal<LNTerm>], roots: &[u64]) -> Result<Option<Vec<Equal<LNTerm>>>, Error> {
    initialize()?;
    let mut indices = vec![0; eqs.len()];
    // SAFETY: roots has two words per equation and C checks the output
    // length against that row count before writing any selected index.
    let n = LEAN_THREAD.with(|_| unsafe {
        tamarin_lean_operand_refine(roots.as_ptr(), roots.len(), indices.as_mut_ptr())
    });
    if n == eqs.len() && indices.iter().copied().eq(0..n as u64) {
        return Ok(None);
    }
    let kept = indices
        .get(..n)
        .ok_or(Error::InvalidStatus(255))?
        .iter()
        .map(|&i| {
            usize::try_from(i)
                .ok()
                .and_then(|i| eqs.get(i))
                .cloned()
                .ok_or(Error::InvalidStatus(255))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some(kept))
}

impl RuleTable {
    /// Each row has its own substitution. Earlier pairs are observations
    /// required to agree. The final pair is the proposed common output.
    pub(super) fn variant_overlap_agrees(
        &self,
        left_inputs: &[LNTerm],
        right_inputs: &[LNTerm],
        left_output: &LNTerm,
        right_output: &LNTerm,
    ) -> Result<bool, Error> {
        if left_inputs.len() != right_inputs.len() {
            return Err(Error::InvalidStatus(255));
        }
        let pairs = left_inputs
            .iter()
            .zip(right_inputs)
            .chain(std::iter::once((left_output, right_output)));
        let mut packet = Packet::default();
        let Some(roots) = packet.roots(self, pairs)? else {
            return Ok(false);
        };
        initialize()?;
        let rows = packet.rows();
        // SAFETY: the shim copies the declarations, node rows and root IDs during the call.
        let verdict = LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_variant_overlap_agrees(
                WordSlice::new(&packet.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&roots),
            )
        });
        match verdict {
            0 => Ok(false),
            1 => Ok(true),
            status => Err(Error::InvalidStatus(status)),
        }
    }

    /// Replay the clash on the pre-factoring equations. A false verdict or a
    /// graph outside the replay budget leaves the original query open.
    pub(crate) fn refutes_factor_clash(&self, equations: &[Equal<LNTerm>]) -> Result<bool, Error> {
        let Some(packet) = Packet::encode(self, equations)? else {
            return Ok(false);
        };
        initialize()?;
        let rows = packet.rows();
        // SAFETY: the shim copies the graph and its roots from these live slices.
        match LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_factor_refutes(
                WordSlice::new(&packet.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations),
            )
        }) {
            0 => Ok(false),
            1 => Ok(true),
            status => Err(Error::InvalidStatus(status)),
        }
    }

    /// The identity factor on the very same conjunction is valid by construction.
    pub(crate) fn accepts_factor(
        &self,
        original: &[Equal<LNTerm>],
        factor: &Subst<Name, LVar>,
        residual: &[Equal<LNTerm>],
    ) -> Result<bool, Error> {
        if factor.is_empty() && original == residual {
            return Ok(true);
        }
        // One packet holds the residual, the original request and the factor,
        // so the three sets of roots share a node table.
        let Some(mut packet) = Packet::encode(self, residual)? else {
            return Ok(false);
        };
        let Some(original_roots) =
            packet.roots(self, original.iter().map(|eq| (&eq.lhs, &eq.rhs)))?
        else {
            return Ok(false);
        };
        // A proposal may only refer to variables from the original request.
        // Even a reflexive residual on an unrelated variable could leak a new
        // key through the caller's substitution adapter.
        let mut original_vars = rustc_hash::FxHashSet::default();
        for e in original {
            use crate::lterm::HasFrees;
            for t in [&e.lhs, &e.rhs] {
                t.for_each_free(&mut |v| {
                    original_vars.insert(*v);
                });
            }
        }
        let mut bindings = Vec::new();
        for (&v, image) in factor.iter() {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let (Some(key), Some(value)) = (
                packet.term(self, &Term::Lit(Lit::Var(v))),
                packet.term(self, image),
            ) else {
                return Ok(false);
            };
            bindings.extend([key, value]);
        }
        if packet.variables.len() != original_vars.len() {
            return Ok(false);
        }
        initialize()?;
        let rows = packet.rows();
        // SAFETY: all three sets of roots refer to the same live node table.
        let accepted = LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_check_factors(
                WordSlice::new(&packet.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&original_roots),
                WordSlice::new(&bindings),
                WordSlice::new(&packet.equations),
            )
        });
        match accepted {
            0 => Ok(false),
            1 => Ok(true),
            status => Err(Error::InvalidStatus(status)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::AcSym;
    use crate::lterm::{pub_term, LSort};
    use crate::maude_sig::mset_maude_sig;

    #[test]
    fn factor_certificate_preserves_every_equation_and_rejects_forged_proposals() {
        use crate::term::f_app_ac;

        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let v = |name, id| LVar::new(name, LSort::Msg, id);
        let term = |v| Term::Lit(Lit::Var(v));
        let (x, y, a, b) = (v("bound", 4), v("x", 0), v("a", 2), v("b", 3));
        let alias = Equal {
            lhs: term(x),
            rhs: term(y),
        };
        let ratio = Equal {
            lhs: f_app_ac(AcSym::Union, vec![term(a); 2]),
            rhs: f_app_ac(AcSym::Union, vec![term(b); 3]),
        };
        let factor = Subst::from_list([(x, term(y))]);
        let original = [alias, ratio.clone()];
        let residual = std::slice::from_ref(&ratio);
        // A direct alias beside an independent AC equation is admitted.
        assert!(table.accepts_factor(&original, &factor, residual).unwrap());
        // Using disjoint identity tables here could make either forged proposal appear valid.
        let forged = Subst::from_list([(x, term(a))]);
        assert!(!table.accepts_factor(&original, &forged, residual).unwrap());
        assert!(!table.accepts_factor(&original, &factor, &[]).unwrap());
        let extra = [
            ratio,
            Equal {
                lhs: term(a),
                rhs: term(b),
            },
        ];
        assert!(!table.accepts_factor(&original, &factor, &extra).unwrap());
    }

    #[test]
    fn flat_ac_row_retains_all_occurrences_and_charges_shared_roots() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let query = |width| {
            let term = Term::App(FunSym::Ac(AcSym::Union), vec![pub_term("a"); width].into());
            [Equal {
                lhs: term.clone(),
                rhs: term,
            }]
        };
        // Each side uses one application and MAX_NODES / 2 - 1 leaf visits.
        let width = MAX_NODES / 2 - 1;
        let equations = query(width);
        let packet = Packet::encode(&table, &equations).unwrap().unwrap();
        assert_eq!(packet.nodes.len(), 2);
        let row = packet.nodes.keys().find(|r| r[0] == 4).unwrap();
        assert_eq!(row.len(), width + 2);
        assert!(row[2..].iter().all(|child| *child == 0));
        assert_eq!(packet.equations, [1, 1]);
        assert!(Packet::encode(&table, &query(width + 1)).unwrap().is_none());
    }
}

#[cfg(test)]
mod presentation_wire;
