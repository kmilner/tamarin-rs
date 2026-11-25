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
pub(crate) use total::Unifiers;
pub use total::UnifyReplies;
pub(crate) use total::{
    has_match as total_has_match, matches as total_match, unify as total_unify,
    unify_exists as total_unify_exists,
};

use super::{initialize, sort_word, Error, RuleTable, Theory, WordSlice, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lean_identity::{IdentityTable, ShortIdentityTable};
use crate::lterm::{LNTerm, LSort, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;
use std::sync::Arc;

// Canonicalization expands each equation's two roots, even when their numeric
// rows are shared. Charge the fully expanded size across the whole request.
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 128;

/// A request names a few variables and constants: up to this many, a table
/// finds one by comparison rather than by hashing.
pub(super) const SHORT_TABLE: usize = 16;

/// The roots of applications a request has encoded, by the address and
/// length of their argument slice and their operator's kind and id. The
/// terms of the request stay borrowed while it is encoded, so an address
/// names one slice throughout.
type Shared = FxHashMap<(usize, usize, u64, u64), u64>;

/// How the rows of a packet name operators.
#[derive(Clone)]
enum Symbols {
    /// By the fixed ids of the theory, which the `tamarin_theory_*` exports
    /// declare themselves.
    Theory(Arc<Theory>),
    /// By the order of first occurrence, with a declaration for each, for the
    /// exports that take declaration words.
    Local {
        table: IdentityTable<FunSym>,
        declarations: Vec<u64>,
    },
}

impl Default for Symbols {
    fn default() -> Self {
        Self::Local {
            table: IdentityTable::default(),
            declarations: Vec::new(),
        }
    }
}

impl Symbols {
    /// The id of `f`, declared on first use by `declaration` (arity and sort)
    /// in a local table.
    fn encode(
        &mut self,
        f: FunSym,
        width: usize,
        declaration: impl Fn(FunSym) -> Option<(usize, LSort)>,
    ) -> Option<(u64, u64)> {
        let (table, declarations) = match self {
            Self::Theory(theory) => return theory.encode(f, width),
            Self::Local {
                table,
                declarations,
            } => (table, declarations),
        };
        let (arity, output) = declaration(f)?;
        let kind = match f {
            FunSym::NoEq(_) if width == arity => 2,
            FunSym::C(_) if width == 2 => 3,
            FunSym::Ac(_) if width >= 2 => 4,
            _ => return None,
        };
        if let Some(id) = table.id(f) {
            return Some((kind, id));
        }
        let id = table.intern(f)?;
        let sort = sort_word(output);
        declarations.extend([kind, id, arity as u64, sort]);
        declarations.extend(std::iter::repeat_n(sort, arity));
        Some((kind, id))
    }

    /// The operator a reply names by `kind` and `id`, its declared arity and
    /// its sort.
    fn decode(&self, kind: u64, id: u64, nat: bool) -> Option<(FunSym, usize, LSort)> {
        match self {
            Self::Theory(theory) => theory.decode(kind, id),
            Self::Local { table, .. } => {
                let f = table.get(id)?;
                let (arity, sort) = super::declaration(f, nat)?;
                matches!(
                    (kind, f),
                    (2, FunSym::NoEq(_)) | (3, FunSym::C(_)) | (4, FunSym::Ac(_))
                )
                .then_some((f, arity, sort))
            }
        }
    }
}

#[derive(Default, Clone)]
pub(crate) struct Packet {
    variables: ShortIdentityTable<LVar, SHORT_TABLE>,
    names: ShortIdentityTable<Name, SHORT_TABLE>,
    symbols: Symbols,
    nodes: Nodes,
    equations: Vec<u64>,
    expanded: usize,
}

/// The node rows of a packet, each once, numbered in the order they were
/// added.
#[derive(Default, Clone)]
struct Nodes {
    /// The rows, one after the other.
    words: Vec<u64>,
    /// Where each row starts in `words`; it ends where the next one starts.
    starts: Vec<usize>,
    /// The hash of each row.
    hashes: Vec<u64>,
    /// The last row added with each hash, once there are more rows than a
    /// scan of `hashes` finds quickly; empty before.
    last: FxHashMap<u64, u32>,
    /// For each row, the row added before it with the same hash, kept with
    /// `last`.
    earlier: Vec<u32>,
}

/// Up to this many rows, a row is found by a scan of the hashes.
const SCANNED_ROWS: usize = 64;

impl Nodes {
    fn len(&self) -> usize {
        self.starts.len()
    }

    fn row(&self, id: usize) -> &[u64] {
        let end = self.starts.get(id + 1).copied().unwrap_or(self.words.len());
        &self.words[self.starts[id]..end]
    }

    /// The rows in the order of their numbers.
    fn rows(&self) -> impl Iterator<Item = &[u64]> {
        (0..self.len()).map(|id| self.row(id))
    }

    /// The number of `row`, which is added if it is new.
    fn intern(&mut self, row: &[u64]) -> u64 {
        use std::hash::Hasher;
        let mut hasher = rustc_hash::FxHasher::default();
        hasher.write_usize(row.len());
        for word in row {
            hasher.write_u64(*word);
        }
        let hash = hasher.finish();
        if self.len() <= SCANNED_ROWS {
            for (at, h) in self.hashes.iter().enumerate() {
                if *h == hash && self.row(at) == row {
                    return at as u64;
                }
            }
        } else {
            let mut at = self.last.get(&hash).copied().unwrap_or(u32::MAX);
            while at != u32::MAX {
                if self.row(at as usize) == row {
                    return u64::from(at);
                }
                at = self.earlier[at as usize];
            }
        }
        let id = u32::try_from(self.len()).expect("fewer than 2^32 nodes in a packet");
        self.hashes.push(hash);
        self.starts.push(self.words.len());
        self.words.extend_from_slice(row);
        if self.len() > SCANNED_ROWS {
            if self.last.is_empty() {
                // The rows outgrew the scan: chain every row by its hash.
                for (at, h) in self.hashes.iter().enumerate() {
                    let earlier = self.last.insert(*h, at as u32).unwrap_or(u32::MAX);
                    self.earlier.push(earlier);
                }
            } else {
                let earlier = self.last.insert(hash, id).unwrap_or(u32::MAX);
                self.earlier.push(earlier);
            }
        }
        u64::from(id)
    }
}

impl Packet {
    /// An empty packet whose rows name operators by the ids of `theory`.
    fn over(theory: &Arc<Theory>) -> Self {
        Self {
            symbols: Symbols::Theory(Arc::clone(theory)),
            ..Self::default()
        }
    }

    /// An empty block of rows that follows this packet: the same operators,
    /// variables and names, and node rows numbered from 0.
    fn further(&self) -> Self {
        Self {
            variables: self.variables.clone(),
            names: self.names.clone(),
            symbols: self.symbols.clone(),
            ..Self::default()
        }
    }

    /// The theory whose ids the rows use.
    fn theory(&self) -> Result<&Theory, Error> {
        match &self.symbols {
            Symbols::Theory(theory) => Ok(theory),
            Symbols::Local { .. } => Err(Error::InvalidStatus(255)),
        }
    }

    /// The declarations of a packet with local operator ids.
    fn declarations(&self) -> Result<&[u64], Error> {
        match &self.symbols {
            Symbols::Local { declarations, .. } => Ok(declarations),
            Symbols::Theory(_) => Err(Error::InvalidStatus(255)),
        }
    }

    fn node(&mut self, row: &[u64]) -> u64 {
        self.nodes.intern(row)
    }

    fn term(&mut self, table: &RuleTable, term: &LNTerm) -> Option<u64> {
        self.encode_term(
            term,
            true,
            |sort| table.declares_sort(sort),
            |f| table.declaration(f).map(|(_, arity, sort)| (arity, sort)),
        )
    }

    /// Append one term over the operators of the packet's theory and return
    /// its root.
    fn encode_theory(&mut self, term: &LNTerm) -> Option<u64> {
        self.encode_theory_sharing(term, &mut Shared::default())
    }

    /// [`Self::encode_theory`], with the roots of the applications that
    /// earlier terms of the same request encoded.
    fn encode_theory_sharing(&mut self, term: &LNTerm, shared: &mut Shared) -> Option<u64> {
        let Symbols::Theory(theory) = &self.symbols else {
            return None;
        };
        let theory = Arc::clone(theory);
        self.encode_term_sharing(
            term,
            false,
            |s| theory.declares_sort(s),
            |_| None,
            Some(shared),
        )
    }

    // Children precede their parents in the graph. The bounded kernels charge
    // expanded visits, while the total reference accepts the entire query.
    fn encode_term(
        &mut self,
        term: &LNTerm,
        bounded: bool,
        declares: impl Fn(LSort) -> bool,
        declaration: impl Fn(FunSym) -> Option<(usize, LSort)>,
    ) -> Option<u64> {
        self.encode_term_sharing(term, bounded, declares, declaration, None)
    }

    /// [`Self::encode_term`]. An application whose arguments are the very
    /// slice of one that `shared` holds, under the same operator, has the
    /// root that one got, and the rows, variables and names below it are
    /// already in the packet, so it is not walked again. Only an unbounded
    /// encoding may skip the walk, which a bounded one charges.
    fn encode_term_sharing(
        &mut self,
        term: &LNTerm,
        bounded: bool,
        declares: impl Fn(LSort) -> bool,
        declaration: impl Fn(FunSym) -> Option<(usize, LSort)>,
        mut shared: Option<&mut Shared>,
    ) -> Option<u64> {
        enum Visit<'a> {
            Term(&'a LNTerm, usize),
            Finish(u64, u64, usize, usize),
        }
        if bounded {
            shared = None;
        }
        let mut work = Vec::with_capacity(16);
        work.push(Visit::Term(term, 0));
        let mut values = Vec::with_capacity(16);
        let mut node = Vec::with_capacity(8);
        while let Some(visit) = work.pop() {
            match visit {
                Visit::Finish(kind, symbol, count, at) => {
                    let start = values.len() - count;
                    node.clear();
                    node.extend([kind, symbol]);
                    node.extend(values.drain(start..));
                    let id = self.node(&node);
                    if let Some(shared) = shared.as_deref_mut() {
                        shared.insert((at, count, kind, symbol), id);
                    }
                    values.push(id);
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
                            let width = children.len();
                            if bounded && width > MAX_NODES - self.expanded {
                                return None;
                            }
                            let (kind, id) = self.symbols.encode(*f, width, &declaration)?;
                            let at = children.as_ptr() as usize;
                            if let Some(root) = shared
                                .as_deref()
                                .and_then(|shared| shared.get(&(at, width, kind, id)))
                            {
                                values.push(*root);
                                continue;
                            }
                            work.push(Visit::Finish(kind, id, width, at));
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

    /// Everything the total exports read of a request, as one key: the
    /// theory, the node rows in order and the equation roots, each behind its
    /// length.
    fn request_words(&self) -> Result<Box<[u64]>, Error> {
        let theory = self.theory()?;
        let mut words = Vec::with_capacity(
            6 + theory.free().len()
                + self.nodes.words.len()
                + self.nodes.len()
                + self.equations.len(),
        );
        words.extend(theory.words());
        words.push(self.nodes.len() as u64);
        for row in self.nodes.rows() {
            words.push(row.len() as u64);
            words.extend(row);
        }
        words.push(self.equations.len() as u64);
        words.extend(&self.equations);
        Ok(words.into_boxed_slice())
    }

    fn rows(&self) -> Vec<WordSlice> {
        self.nodes.rows().map(WordSlice::new).collect()
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
        let declarations = packet.declarations()?;
        // SAFETY: the shim copies the declarations, node rows and root IDs during the call.
        let verdict = LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_variant_overlap_agrees(
                WordSlice::new(declarations),
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
        let declarations = packet.declarations()?;
        // SAFETY: the shim copies the graph and its roots from these live slices.
        match LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_factor_refutes(
                WordSlice::new(declarations),
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
        let declarations = packet.declarations()?;
        // SAFETY: all three sets of roots refer to the same live node table.
        let accepted = LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_check_factors(
                WordSlice::new(declarations),
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
    fn node_rows_are_numbered_by_first_occurrence_on_both_sides_of_the_scan() {
        let mut nodes = Nodes::default();
        let mut reference: FxHashMap<Vec<u64>, u64> = FxHashMap::default();
        let row = |i: u64| -> Vec<u64> { (0..(i % 5)).map(|k| (i * 7 + k) % 23).collect() };
        for step in 0..600u64 {
            let r = row((step * 13) % 211);
            let next = reference.len() as u64;
            let want = *reference.entry(r.clone()).or_insert(next);
            assert_eq!(nodes.intern(&r), want, "step {step}");
        }
        assert!(nodes.len() > SCANNED_ROWS);
        let mut by_id = vec![Vec::new(); reference.len()];
        for (r, id) in reference {
            by_id[id as usize] = r;
        }
        assert!(nodes.rows().eq(by_id.iter().map(|r| &r[..])));
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
        let row = packet.nodes.rows().find(|r| r[0] == 4).unwrap();
        assert_eq!(row.len(), width + 2);
        assert!(row[2..].iter().all(|child| *child == 0));
        assert_eq!(packet.equations, [1, 1]);
        assert!(Packet::encode(&table, &query(width + 1)).unwrap().is_none());
    }
}

#[cfg(test)]
mod presentation_wire;
