//! A stable operand can be a restricted variable, a name, or a compound
//! depending on other caller variables. Abstract each distinct operand once,
//! then unify its actual term with the corresponding column in each graph
//! row. DHSignedLeaves.stable_leaf_stage justifies this simultaneous join.
use super::{signed_graph, InputDomain, JoinSearch, Row, RuleTable};
use crate::function_symbols::{inv_sym, one_sym, AcSym, FunSym};
use crate::lean_unification::{residual, subsort, Error};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::term::{f_app, Term};
use crate::vterm::Lit;
use rustc_hash::FxHashSet;

#[derive(Default)]
struct Operands {
    leaves: Vec<LNTerm>,
    formals: Vec<LVar>,
    signed: bool,
    specialized: bool,
}

impl Operands {
    fn abstract_term(
        &mut self,
        table: &RuleTable,
        t: &LNTerm,
        depth: usize,
    ) -> Result<Option<LNTerm>, Error> {
        if depth >= 256 {
            return Ok(None);
        }
        if let Term::App(head, args) = t {
            match head {
                FunSym::NoEq(f) if *f == one_sym() => {
                    return Ok(args.is_empty().then(|| t.clone()))
                }
                FunSym::NoEq(f) if *f == inv_sym() && args.len() == 1 => (),
                FunSym::Ac(AcSym::Mult) if args.len() >= 2 => (),
                _ => return self.operand(table, t),
            }
            self.signed = true;
            let mut children = Vec::with_capacity(args.len());
            for arg in args.iter() {
                let Some(child) = self.abstract_term(table, arg, depth + 1)? else {
                    return Ok(None);
                };
                children.push(child);
            }
            return Ok(Some(f_app(*head, children)));
        }
        self.operand(table, t)
    }

    fn operand(&mut self, table: &RuleTable, t: &LNTerm) -> Result<Option<LNTerm>, Error> {
        let index = match self.leaves.iter().position(|old| old == t) {
            Some(i) => i,
            None => {
                if self.leaves.len() >= signed_graph::MAX_COORDINATES
                    || !table
                        .collect(t, &mut Vec::new(), InputDomain::Sorted)
                        .is_some_and(|sort| subsort(sort, LSort::Msg))
                    || !table.stably_normal_native(t)?
                {
                    return Ok(None);
                }
                let i = self.leaves.len();
                self.specialized |= !matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg);
                self.leaves.push(t.clone());
                self.formals.push(LVar::new("x", LSort::Msg, i as u64));
                i
            }
        };
        Ok(Some(Term::Lit(Lit::Var(self.formals[index]))))
    }
}

impl RuleTable {
    pub(super) fn signed_leaf_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        terms: &[LNTerm],
    ) -> Result<Option<Vec<Row>>, Error> {
        if !self.builtin_dh {
            return Ok(None);
        }
        let mut search = JoinSearch::new();
        if !residual::charge_expansion(&mut search.graph_work, terms.iter(), None)? {
            return Ok(None);
        }
        let mut operands = Operands::default();
        let mut expressions = Vec::with_capacity(terms.len());
        for t in terms {
            let Some(e) = operands.abstract_term(self, t, 0)? else {
                return Ok(None);
            };
            expressions.push(e);
        }
        if !operands.signed || !operands.specialized {
            return Ok(None);
        }
        // Apply the known terms before subsumption. A row that requires a
        // product in a Fresh slot can fail immediately during this join.
        let Some(parent) = self.signed_graph_candidates(
            &operands.formals,
            &expressions,
            signed_graph::MAX_COORDINATES,
            &mut search,
        )?
        else {
            return Ok(None);
        };
        let children = Row {
            images: operands.leaves,
            values: keys.iter().map(|k| Term::Lit(Lit::Var(*k))).collect(),
        };
        let parent: Vec<_> = parent.into_iter().collect();
        let Some(joined) = self.join_families(&[children], &parent, original, &mut search)? else {
            return Ok(None);
        };
        let visible = joined
            .into_iter()
            .map(|r| {
                let mut images = r.values;
                let values = images.split_off(keys.len());
                Row { images, values }.rename(original)
            })
            .collect();
        self.prune_specializations(visible, &mut search.matching)
    }
}

#[cfg(test)]
impl RuleTable {
    pub(crate) fn signed_leaf_probe(
        &self,
        keys: &[LVar],
        terms: &[LNTerm],
    ) -> Result<Option<Vec<Vec<LNTerm>>>, Error> {
        let original = keys.iter().map(|k| k.idx).collect();
        Ok(self.signed_leaf_rows(keys, &original, terms)?.map(|rows| {
            rows.into_iter()
                .map(|mut r| {
                    r.images.extend(r.values);
                    r.images
                })
                .collect()
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{hash, msg_var, mult};
    use crate::lterm::pub_term;
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};

    #[test]
    fn signed_leaf_abstraction_checks_the_live_equations() {
        let mut sig = dh_maude_sig().merge(hash_maude_sig());
        let name = pub_term("a");
        sig.st_rules.insert(CtxtStRule::new(
            hash(name.clone()),
            StRhs {
                positions: vec![vec![0]],
                term: name,
            },
        ));
        let table = RuleTable::new(&sig).unwrap();
        let key = LVar::new("x", LSort::Msg, 0);
        let x = msg_var("x", 0);
        // The symbolic hash can become a redex when x is specialized to a.
        assert!(table
            .signed_leaf_probe(&[key], &[mult(x.clone(), hash(x))])
            .unwrap()
            .is_none());
    }
}
