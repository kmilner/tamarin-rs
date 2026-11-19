//! Submit equations as a shared graph. Lean counts operands for homogeneous AC
//! systems and checks identity, closed clashes, and incompatible variable-image
//! sizes on the original equation roots.
use super::homogeneous::ProjectedAnswers;
use super::{ac_sort, initialize, sort_word, Error, Outcome, RuleTable, WordSlice, LEAN_THREAD};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{LNTerm, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;
use std::borrow::Cow;

// Canonicalization expands each equation's two roots, even when their numeric
// rows are shared. Charge the fully expanded size across the whole request.
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 128;

#[derive(Default)]
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
        let id = self.nodes.len() as u64; // <= MAX_NODES
        self.nodes.insert(row.into(), id);
        id
    }

    fn term(&mut self, table: &RuleTable, term: &LNTerm, depth: usize) -> Option<u64> {
        self.expanded += 1;
        if self.expanded > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        let (f, children) = match term {
            Term::Lit(lit) => {
                let (kind, id, sort) = match lit {
                    Lit::Var(v) => (0, self.variables.intern(*v)?, v.sort),
                    Lit::Con(n) => (1, self.names.intern(*n)?, sort_of_name(n)),
                };
                return table
                    .declares_sort(sort)
                    .then(|| self.node(&[kind, id, sort_word(sort)]));
            }
            Term::App(f, children) => (*f, children),
        };
        let (_, arity, output) = table.declaration(f)?;
        let kind = match f {
            FunSym::NoEq(_) if children.len() == arity => 2,
            FunSym::C(_) if children.len() == 2 => 3,
            FunSym::Ac(_) if children.len() >= 2 => 4,
            _ => return None,
        };
        if children.len() > MAX_NODES - self.expanded {
            return None;
        }
        let id = if let Some(id) = self.symbols.id(f) {
            id
        } else {
            let id = self.symbols.intern(f)?;
            let sort = sort_word(output);
            self.declarations.extend([kind, id, arity as u64, sort]);
            self.declarations.extend(std::iter::repeat_n(sort, arity));
            id
        };
        let mut row = Vec::with_capacity(children.len() + 2);
        row.extend([kind, id]);
        for child in children.iter() {
            row.push(self.term(table, child, depth + 1)?);
        }
        let next = self.nodes.len() as u64;
        Some(*self.nodes.entry(row.into_boxed_slice()).or_insert(next))
    }

    fn roots<'a>(
        &mut self,
        table: &RuleTable,
        equations: impl IntoIterator<Item = (&'a LNTerm, &'a LNTerm)>,
    ) -> Result<Option<Vec<u64>>, Error> {
        let mut roots = Vec::new();
        for (lhs, rhs) in equations {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let (Some(lhs), Some(rhs)) = (self.term(table, lhs, 0), self.term(table, rhs, 0))
            else {
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

    fn rows(&self) -> Vec<WordSlice> {
        let mut rows = vec![WordSlice::new(&[]); self.nodes.len()];
        for (row, &id) in &self.nodes {
            rows[id as usize] = WordSlice::new(row);
        }
        rows
    }
}

unsafe extern "C" {
    fn tamarin_lean_operand_refine(sides: *const u64, count: usize, indices: *mut u64) -> usize;
    fn tamarin_lean_check_factors(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        original: WordSlice,
        bindings: WordSlice,
        residual: WordSlice,
    ) -> u8;
    fn tamarin_lean_graph_homogeneous_unify(
        width: u64,
        symbol: u64,
        sort: u64,
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        roots: WordSlice,
    ) -> ProjectedAnswers;
    fn tamarin_lean_graph_ac_feasible(
        width: u64,
        symbol: u64,
        sort: u64,
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        roots: WordSlice,
    ) -> u8;
    fn tamarin_lean_variant_overlap_agrees(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        roots: WordSlice,
    ) -> u8;
    fn tamarin_lean_whole_unify(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        equations: WordSlice,
    ) -> u8;
}

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

    /// Skip rule-table initialization and graph construction for ordinary mixed
    /// terms. Nested occurrences of the same AC symbol are valid raw input.
    pub(crate) fn may_be_homogeneous(eqs: &[Equal<LNTerm>]) -> bool {
        if eqs.len() > 64 {
            return false;
        }
        let roots = || eqs.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]);
        let Some(symbol) = roots().find_map(|t| match t {
            Term::App(FunSym::Ac(symbol), _) => Some(*symbol),
            _ => None,
        }) else {
            return false;
        };
        let sort = ac_sort(symbol);
        let applicable = |t: &LNTerm| match t {
            Term::Lit(Lit::Var(v)) => v.sort == sort,
            Term::App(FunSym::Ac(f), _) => *f == symbol,
            _ => false,
        };
        roots().all(|root| {
            applicable(root)
                && match root {
                    Term::App(_, args) => args.len() <= MAX_NODES && args.iter().all(applicable),
                    Term::Lit(_) => true,
                }
        })
    }

    pub(crate) fn graph_feasible(&self, eqs: &[Equal<LNTerm>]) -> Result<Option<bool>, Error> {
        let Some(packet) = Packet::encode(self, eqs)? else {
            return Ok(None);
        };
        packet.graph_feasible()
    }

    /// Collect the scope before removing reflexive and repeated equations.
    /// Their variables remain reserved and visible in every projected answer.
    pub(super) fn ac_operand_query<'a>(
        &self,
        eqs: &'a [Equal<LNTerm>],
    ) -> Result<Option<(IdentityTable<LVar>, Cow<'a, [Equal<LNTerm>]>)>, Error> {
        let Some(packet) = Packet::encode(self, eqs)? else {
            return Ok(None);
        };
        let has_ac = packet
            .symbols
            .values()
            .iter()
            .any(|f| matches!(f, FunSym::Ac(_)));
        if !has_ac || !self.admits_terms(eqs) {
            return Ok(None);
        }
        // Up to 64 equations fit one AC matrix. The selector's candidate
        // compares unordered pairs linearly in its set of earlier rows.
        if !(2..=64).contains(&eqs.len()) {
            return Ok(Some((packet.variables, Cow::Borrowed(eqs))));
        }
        let mut selected =
            select_rows(eqs, &packet.equations)?.map_or(Cow::Borrowed(eqs), Cow::Owned);
        if selected.len() > 1 {
            let mut inner = Vec::with_capacity(selected.len());
            let mut changed = false;
            for eq in selected.iter() {
                let pair = super::residual::inner_equality(&eq.lhs, &eq.rhs)?;
                changed |= !std::ptr::eq(pair.0, &eq.lhs);
                inner.push(pair);
            }
            // Select using equivalent inner equalities but retain original
            // terms. The remaining matrix observes exactly the caller's operands.
            if changed && let Some(kept) = select_rows(&selected, &root_ids(inner.into_iter())?)? {
                selected = Cow::Owned(kept);
            }
        }
        Ok(Some((packet.variables, selected)))
    }

    pub(crate) fn whole_unify(&self, equations: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        self.try_whole_unify(equations).map(|(outcome, _)| outcome)
    }

    /// Retain a homogeneous graph after inconclusive whole-family search so a
    /// caller can try a definitive negative once other complete solvers defer.
    pub(crate) fn try_whole_unify(
        &self,
        equations: &[Equal<LNTerm>],
    ) -> Result<(Outcome, Option<Packet>), Error> {
        let Some(packet) = Packet::encode(self, equations)? else {
            return Ok((Outcome::Unsupported, None));
        };
        initialize()?;
        let shape = packet.matrix_shape();
        let outcome = packet.solve(&packet.rows(), shape)?;
        let pending = (outcome == Outcome::Unsupported && shape.is_some()).then_some(packet);
        Ok((outcome, pending))
    }

    pub(crate) fn factored_unify(
        &self,
        original: &[Equal<LNTerm>],
        factor: &Subst<Name, LVar>,
        residual: &[Equal<LNTerm>],
    ) -> Result<Outcome, Error> {
        // The residual variables form a dense prefix for the matrix solver.
        // Extending this packet reserves every variable observed in the factor
        // or the original request without renumbering any matrix column.
        let Some(mut packet) = Packet::encode(self, residual)? else {
            return Ok(Outcome::Unsupported);
        };
        let matrix = packet.matrix_shape();
        let Some(original_roots) =
            packet.roots(self, original.iter().map(|eq| (&eq.lhs, &eq.rhs)))?
        else {
            return Ok(Outcome::Unsupported);
        };
        let mut bindings = Vec::new();
        for (&v, image) in factor.iter() {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let (Some(key), Some(value)) = (
                packet.term(self, &Term::Lit(Lit::Var(v)), 0),
                packet.term(self, image, 0),
            ) else {
                return Ok(Outcome::Unsupported);
            };
            bindings.extend([key, value]);
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
            0 => Ok(Outcome::Unsupported),
            1 => match packet.solve(&rows, matrix)? {
                Outcome::Unsupported => {
                    // Residual search can introduce witnesses even if the original
                    // factor eliminated every occurrence of a caller variable.
                    self.unify_operands_avoiding(residual, packet.variables.values())
                }
                complete => Ok(complete),
            },
            status => Err(Error::InvalidStatus(status)),
        }
    }
}

impl Packet {
    /// Read feasibility from these exact equation roots. A positive verdict
    /// certifies existence and carries no substitution family.
    pub(crate) fn graph_feasible(&self) -> Result<Option<bool>, Error> {
        initialize()?;
        let rows = self.rows();
        let Some((symbol, width)) = self.matrix_shape() else {
            return self.whole_verdict(&rows);
        };
        if !(1..=MAX_NODES).contains(&width) {
            return Ok(None);
        }
        let symbol_id = self
            .symbols
            .id(FunSym::Ac(symbol))
            .ok_or(Error::InvalidStatus(255))?;
        // SAFETY: the shim copies all borrowed rows and roots before returning its tag.
        let status = LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_graph_ac_feasible(
                width as u64,
                symbol_id,
                sort_word(ac_sort(symbol)),
                WordSlice::new(&self.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&self.equations),
            )
        });
        match status {
            0 => Ok(None),
            1 => Ok(Some(false)),
            2 => Ok(Some(true)),
            status => Err(Error::InvalidStatus(status)),
        }
    }

    fn matrix_shape(&self) -> Option<(AcSym, usize)> {
        match self.symbols.values() {
            [FunSym::Ac(symbol)] if self.names.len() == 0 => Some((*symbol, self.variables.len())),
            _ => None,
        }
    }

    fn solve(&self, rows: &[WordSlice], matrix: Option<(AcSym, usize)>) -> Result<Outcome, Error> {
        if let Some((symbol, width)) = matrix {
            let symbol_id = self
                .symbols
                .id(FunSym::Ac(symbol))
                .expect("interned AC symbol");
            // SAFETY: the graph and roots remain live while C copies them into Lean arrays.
            let raw = LEAN_THREAD.with(|_| unsafe {
                tamarin_lean_graph_homogeneous_unify(
                    width as u64,
                    symbol_id,
                    sort_word(ac_sort(symbol)),
                    WordSlice::new(&self.declarations),
                    rows.as_ptr(),
                    rows.len(),
                    WordSlice::new(&self.equations),
                )
            });
            if let Some(packet) = raw.into_packet()? {
                let reserved = self.variables.values().iter().map(|v| v.idx).collect();
                let images = super::homogeneous::decode(symbol, &reserved, width, packet)?;
                let columns = &self.variables.values()[..width];
                return Ok(Outcome::Complete(
                    images
                        .into_iter()
                        .map(|arm| columns.iter().copied().zip(arm).collect())
                        .collect(),
                ));
            }
        }

        Ok(match self.whole_verdict(rows)? {
            None => Outcome::Unsupported,
            Some(false) => Outcome::Complete(vec![]),
            Some(true) => Outcome::Complete(vec![vec![]]),
        })
    }

    /// The only positive whole-query packet denotes the identity substitution.
    fn whole_verdict(&self, rows: &[WordSlice]) -> Result<Option<bool>, Error> {
        // SAFETY: all borrowed rows and roots remain live while the shim copies them.
        let status = LEAN_THREAD.with(|_| unsafe {
            tamarin_lean_whole_unify(
                WordSlice::new(&self.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&self.equations),
            )
        });
        match status {
            0 => Ok(None),
            1 => Ok(Some(false)),
            2 => Ok(Some(true)),
            status => Err(Error::InvalidStatus(status)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lterm::{pub_term, LSort},
        maude_sig::mset_maude_sig,
    };

    #[test]
    fn context_selection_keeps_the_original_equations_and_observed_siblings() {
        use crate::builtin::pair;
        use crate::maude_sig::pair_maude_sig;
        use crate::term::f_app_ac;

        let table = RuleTable::new(&mset_maude_sig().merge(pair_maude_sig())).unwrap();
        let var = |i| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)));
        let eq = |lhs, rhs| Equal { lhs, rhs };
        let sum = |xs| f_app_ac(AcSym::Union, xs);
        let context = |t| sum(vec![var(2), var(2), pair(var(3), t)]);
        let inner = eq(var(0), var(1));
        let wrapped = eq(context(var(1)), context(var(0)));
        // Neither the second differing pair argument nor a surplus AC
        // occurrence can be dropped as if it were an equal sibling.
        let differs_twice = eq(pair(var(0), var(2)), pair(var(1), var(3)));
        let surplus = eq(sum(vec![var(0), var(2), var(2)]), sum(vec![var(1), var(2)]));
        let rows = [inner, wrapped, differs_twice, surplus];
        let (vars, kept) = table.ac_operand_query(&rows).unwrap().unwrap();
        assert_eq!(vars.len(), 4);
        assert_eq!(kept.len(), 3);
        assert!(kept.contains(&rows[2]) && kept.contains(&rows[3]));
        assert!(kept.contains(&rows[0]) || kept.contains(&rows[1]));
        let reversed = [rows[1].clone(), rows[0].clone()];
        let (vars, kept) = table.ac_operand_query(&reversed).unwrap().unwrap();
        assert_eq!(vars.len(), 4);
        assert_eq!(kept.len(), 1);
        assert!(reversed.contains(&kept[0]));
    }

    #[test]
    fn graph_matrix_preserves_repeated_edges_and_column_order_across_equations() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let [z, a, x] = ["z", "a", "x"].map(|name| LVar::new(name, LSort::Msg, 17));
        let v = |key| Term::Lit(Lit::Var(key));
        let sym = FunSym::Ac(AcSym::Union);
        let plus = |left, right| Term::App(sym, vec![left, right].into());
        let twice_z = plus(v(z), v(z));
        // 2z = 3a and a + x = 2z have the single primitive ratio (3, 2, 4).
        // Both equations reference the same 2z node. The three a edges are
        // nested and all three columns have the same source variable index.
        let original = [
            Equal {
                lhs: twice_z.clone(),
                rhs: plus(v(a), plus(v(a), v(a))),
            },
            Equal {
                lhs: plus(v(a), v(x)),
                rhs: twice_z,
            },
        ];
        let Outcome::Complete(arms) = table.whole_unify(&original).unwrap() else {
            panic!("expected the primitive ratio")
        };
        let [arm] = arms.as_slice() else {
            panic!("expected one arm")
        };
        assert_eq!(
            arm.iter().map(|(key, _)| *key).collect::<Vec<_>>(),
            [z, a, x]
        );
        let Term::App(_, zs) = &arm[0].1 else {
            panic!("expected a compound image")
        };
        let Term::Lit(Lit::Var(w)) = zs[0] else {
            panic!("expected a shared witness")
        };
        assert_ne!(w.idx, z.idx);
        for ((_, image), count) in arm.iter().zip([3, 2, 4]) {
            assert_eq!(image, &Term::App(sym, vec![v(w); count].into()));
        }
    }

    #[test]
    fn factor_certificate_preserves_every_equation_and_reserves_eliminated_names() {
        use crate::lterm::HasFrees;
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
        let Outcome::Complete(arms) = table.factored_unify(&original, &factor, residual).unwrap()
        else {
            panic!("a direct alias and independent AC equation must be admitted")
        };
        let [arm] = arms.as_slice() else {
            panic!("expected one primitive ratio")
        };
        assert_eq!(arm.len(), 2);
        for (_, image) in arm {
            image.for_each_free(&mut |w| assert!(![x.idx, y.idx, a.idx, b.idx].contains(&w.idx)));
        }
        // Using disjoint identity tables here could make either forged proposal appear valid.
        let forged = Subst::from_list([(x, term(a))]);
        assert_eq!(
            table.factored_unify(&original, &forged, residual).unwrap(),
            Outcome::Unsupported
        );
        assert_eq!(
            table.factored_unify(&original, &factor, &[]).unwrap(),
            Outcome::Unsupported
        );
        let extra = [
            ratio,
            Equal {
                lhs: term(a),
                rhs: term(b),
            },
        ];
        assert_eq!(
            table.factored_unify(&original, &factor, &extra).unwrap(),
            Outcome::Unsupported
        );
    }

    #[test]
    fn checked_factor_lifts_both_graph_replies() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let x = LVar::new("bound", LSort::Msg, 0);
        let alias = Equal {
            lhs: Term::Lit(Lit::Var(x)),
            rhs: pub_term("a"),
        };
        let factor = Subst::from_list([(x, alias.rhs.clone())]);
        for (rhs, expected) in [("a", vec![vec![]]), ("b", vec![])] {
            let residual = [Equal {
                lhs: pub_term("a"),
                rhs: pub_term(rhs),
            }];
            let original = [alias.clone(), residual[0].clone()];
            assert_eq!(
                table.factored_unify(&original, &factor, &residual).unwrap(),
                Outcome::Complete(expected)
            );
        }
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
        assert!(matches!(table.whole_unify(&equations).unwrap(),
            Outcome::Complete(answers) if answers == vec![vec![]]));
        assert!(Packet::encode(&table, &query(width + 1)).unwrap().is_none());
    }
}
