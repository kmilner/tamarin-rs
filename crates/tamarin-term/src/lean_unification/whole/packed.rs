//! Decode the free TOP wrappers separately from the ordinary algebraic terms.
//! The Lean kernel returns the coordinates of one shared conjunction or a clash.
use super::{total, Packet};
use crate::function_symbols::FunSym;
use crate::lean_unification::{initialize, Error, MatchRows, Outcome, WordSlice, LEAN_THREAD};
use crate::lterm::LNTerm;
use crate::maude_sig::MaudeSig;
use crate::rewriting::Equal;
use crate::term::Term;
use std::borrow::Cow;
use tamarin_utils::cancellation;

use tamarin_algebra_sys::tamarin_lean_unpack_conjunction;

pub(crate) enum Conjunction<'a> {
    Rows(Cow<'a, [Equal<LNTerm>]>),
    Clash,
    Unsupported,
}

impl Conjunction<'_> {
    pub(crate) fn solve(
        self,
        solver: impl FnOnce(&[Equal<LNTerm>]) -> Result<Outcome, Error>,
    ) -> Result<Outcome, Error> {
        match self {
            Self::Rows(rows) => solver(&rows),
            Self::Clash => Ok(Outcome::Complete(Vec::new())),
            Self::Unsupported => Ok(Outcome::Unsupported),
        }
    }
}

struct Graph<'a> {
    nodes: Vec<Vec<u64>>,
    leaves: Vec<&'a LNTerm>,
}

impl<'a> Graph<'a> {
    fn node(&mut self, row: Vec<u64>) -> u64 {
        let index = self.nodes.len() as u64;
        self.nodes.push(row);
        index
    }

    fn spine(
        &mut self,
        terms: impl DoubleEndedIterator<Item = &'a LNTerm> + ExactSizeIterator,
    ) -> Result<u64, Error> {
        enum Visit<'a> {
            Term(&'a LNTerm),
            Pack(usize),
        }

        let mut work = vec![Visit::Pack(terms.len())];
        work.extend(terms.rev().map(Visit::Term));
        let mut values = Vec::new();
        while let Some(next) = work.pop() {
            cancellation::check().map_err(|_| Error::Cancelled)?;
            match next {
                Visit::Term(Term::App(FunSym::List, children)) => {
                    work.push(Visit::Pack(children.len()));
                    work.extend(children.iter().rev().map(Visit::Term));
                }
                Visit::Term(term) => {
                    let leaf = self.leaves.len() as u64;
                    self.leaves.push(term);
                    values.push(self.node(vec![leaf]));
                }
                Visit::Pack(width) => {
                    let mut tail = 0; // Node zero is nil.
                    for head in values.drain(values.len() - width..).rev() {
                        tail = self.node(vec![head, tail]);
                    }
                    values.push(tail);
                }
            }
        }
        Ok(values[0])
    }
}

pub(crate) fn unpack_conjunction<'a>(
    sig: &MaudeSig,
    equations: &'a [Equal<LNTerm>],
) -> Result<Conjunction<'a>, Error> {
    if !equations.iter().any(|e| {
        [&e.lhs, &e.rhs]
            .into_iter()
            .any(|t| matches!(t, Term::App(FunSym::List, _)))
    }) {
        return Ok(Conjunction::Rows(Cow::Borrowed(equations)));
    }
    let mut graph = Graph {
        nodes: vec![vec![]],
        leaves: Vec::new(),
    };
    let lhs = graph.spine(equations.iter().map(|e| &e.lhs))?;
    let rhs = graph.spine(equations.iter().map(|e| &e.rhs))?;
    let rows: Vec<_> = graph.nodes.iter().map(|row| WordSlice::new(row)).collect();
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim copies the rows and MatchRows owns its returned reference.
        let reply = MatchRows::new(unsafe {
            tamarin_lean_unpack_conjunction(
                rows.as_ptr(),
                rows.len(),
                graph.leaves.len() as u64,
                lhs,
                rhs,
            )
        })?;
        match total::header(&reply)? {
            2 if reply.rows(0) == 1 => {
                // A shape conflict cannot certify a malformed command. Check every
                // algebraic leaf, even in a different conjunct or an unmatched tail.
                if Packet::encode_total(sig, graph.leaves)?.is_some() {
                    Ok(Conjunction::Clash)
                } else {
                    Ok(Conjunction::Unsupported)
                }
            }
            1 => {
                let mut out = Vec::with_capacity(reply.rows(0) - 1);
                for index in 1..reply.rows(0) {
                    let mut pair = [0; 2];
                    if reply.copy_row(0, index, &mut pair)? != 2 {
                        return Err(Error::InvalidStatus(255));
                    }
                    let term = |id: u64| {
                        graph
                            .leaves
                            .get(id as usize)
                            .map(|t| (*t).clone())
                            .ok_or(Error::InvalidStatus(255))
                    };
                    out.push(Equal::new(term(pair[0])?, term(pair[1])?));
                }
                Ok(Conjunction::Rows(Cow::Owned(out)))
            }
            _ => Err(Error::InvalidStatus(255)),
        }
    })
}
