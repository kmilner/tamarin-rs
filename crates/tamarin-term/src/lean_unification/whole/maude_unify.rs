//! The port of Maude's unification algorithm (`tamarin_theory_maude_unify`)
//! on the terms of a Maude `unify` command, under Maude's ranks
//! ([`crate::maude_ranks`]), with its reply as the substitutions Maude's
//! reply parses to.
//!
//! The request is the command's terms as the Maude backend writes them: a
//! variable `xN` of a sort is the variable with identifier `N` of that sort,
//! and a name constant `p(k)` (and `f`, `c`, `n`, `t`) is the name with
//! identifier `k` of that sort. The export lists the bindings of every
//! unifier in Maude's order and numbers the unifier's own variables in the
//! order of Maude's `#1, #2, …` from the least identifier above the
//! request's variables. The reply is read here into the parsed form of a
//! Maude reply: each unifier as the bindings `xN:Sort --> term` in order,
//! with `#k` as `FreshVar(k, sort)` and every application built as the reply
//! parser builds it ([`crate::term::f_app`]), so that the Maude backend's own
//! decoding takes it from there.
use super::total::{reply_words, rows_of};
use crate::function_symbols::FunSym;
use crate::lean_unification::LEAN_THREAD;
use crate::lean_unification::{initialize, sort_word, Error, MatchRows, Theory, Watch, WordSlice};
use crate::lterm::LSort;
use crate::maude_ranks::MaudeRanks;
use crate::maude_types::{MSubst, MTerm, MaudeLit};
use crate::term::{f_app, Term};
use tamarin_algebra_sys::tamarin_lean_theory_maude_unify;
use tamarin_utils::cancellation;

/// What the port made of a request.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum PortReply {
    /// Maude's unifiers, in Maude's order, as its reply parses.
    Unifiers(Vec<MSubst>),
    /// The port ran out of fuel, or an answer did not fit in words.
    GaveUp,
    /// A term is outside the theory's operators.
    Unencodable,
}

/// The node rows of the terms of a request and the root of each term.
#[derive(Default)]
struct Rows {
    nodes: Vec<Vec<u64>>,
}

impl Rows {
    /// Append `t` in postorder and return its row, or `None` for a term
    /// outside the theory's operators.
    fn term(&mut self, theory: &Theory, t: &MTerm) -> Option<u64> {
        let row = match t {
            Term::Lit(MaudeLit::MaudeVar(id, s)) => vec![0, *id, sort_word(*s)],
            Term::Lit(MaudeLit::MaudeConst(id, s)) => vec![1, *id, sort_word(*s)],
            Term::Lit(MaudeLit::FreshVar(..)) => return None,
            Term::App(f, args) => {
                let (kind, id) = theory.encode(*f, args.len())?;
                let mut row = Vec::with_capacity(args.len() + 2);
                row.extend([kind, id]);
                for a in args.iter() {
                    row.push(self.term(theory, a)?);
                }
                row
            }
        };
        self.nodes.push(row);
        Some(self.nodes.len() as u64 - 1)
    }
}

fn sort(word: u64) -> Result<LSort, Error> {
    match word {
        0 => Ok(LSort::Pub),
        1 => Ok(LSort::Fresh),
        2 => Ok(LSort::Msg),
        3 => Ok(LSort::Node),
        4 => Ok(LSort::Nat),
        _ => Err(Error::InvalidStatus(255)),
    }
}

/// The term of a binding row's postfix tokens `[kind, id, aux]`: a variable
/// at or above `fresh` is the unifier's variable `#(id - fresh + 1)`, any
/// other the request's `x{id}`.
fn read_image(theory: &Theory, tokens: &[u64], fresh: u64) -> Result<MTerm, Error> {
    let (tokens, rest) = tokens.as_chunks::<3>();
    if !rest.is_empty() {
        return Err(Error::InvalidStatus(255));
    }
    let mut stack: Vec<MTerm> = Vec::new();
    for &[kind, id, aux] in tokens {
        let term = match kind {
            0 if id >= fresh => Term::Lit(MaudeLit::FreshVar(id - fresh + 1, sort(aux)?)),
            0 => Term::Lit(MaudeLit::MaudeVar(id, sort(aux)?)),
            1 => Term::Lit(MaudeLit::MaudeConst(id, sort(aux)?)),
            _ => {
                let (f, arity, _) = theory.decode(kind, id).ok_or(Error::InvalidStatus(255))?;
                if aux != arity as u64 {
                    return Err(Error::InvalidStatus(255));
                }
                let start = stack
                    .len()
                    .checked_sub(arity)
                    .ok_or(Error::InvalidStatus(255))?;
                let args: Vec<_> = stack.drain(start..).collect();
                match f {
                    // The reply parser keeps a free application's arguments.
                    FunSym::NoEq(_) => Term::App(f, args.into()),
                    _ => f_app(f, args),
                }
            }
        };
        stack.push(term);
    }
    match <[MTerm; 1]>::try_from(stack) {
        Ok([t]) => Ok(t),
        Err(_) => Err(Error::InvalidStatus(255)),
    }
}

/// The unifiers of the reply words: after the status row, for each unifier
/// an empty row and then a row `[N, sort, tokens…]` for each variable `xN` of
/// the request.
fn read_unifiers(theory: &Theory, words: &[u64], fresh: u64) -> Result<Vec<MSubst>, Error> {
    let mut rows = rows_of(words);
    rows.next(); // the status row
    let mut unifiers: Vec<MSubst> = Vec::new();
    for row in rows {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        let row = row.ok_or(Error::InvalidStatus(255))?;
        match row {
            [] => unifiers.push(Vec::new()),
            [id, s, tokens @ ..] => {
                let binding = ((sort(*s)?, *id), read_image(theory, tokens, fresh)?);
                unifiers
                    .last_mut()
                    .ok_or(Error::InvalidStatus(255))?
                    .push(binding);
            }
            _ => return Err(Error::InvalidStatus(255)),
        }
    }
    Ok(unifiers)
}

/// Run the port on the equations `sides` of a Maude `unify` command.
/// `fuel` bounds the port's recursion; `work` bounds the questions of the
/// call (zero for no bound), past which it is stopped like every other
/// interruptible export.
pub(crate) fn maude_unify(
    theory: &Theory,
    ranks: &MaudeRanks,
    sides: &[(MTerm, MTerm)],
    fuel: u64,
    work: u64,
) -> Result<PortReply, Error> {
    let mut rows = Rows::default();
    let mut equations = Vec::with_capacity(2 * sides.len());
    for (lhs, rhs) in sides {
        for t in [lhs, rhs] {
            let Some(root) = rows.term(theory, t) else {
                return Ok(PortReply::Unencodable);
            };
            equations.push(root);
        }
    }
    // The unifier's own variables are numbered from the least identifier
    // above the request's variables.
    let fresh = rows
        .nodes
        .iter()
        .filter(|row| row[0] == 0)
        .map(|row| row[1] + 1)
        .max()
        .unwrap_or(0);
    let rank_rows = ranks.rows(theory);
    let rank_slices: Vec<_> = rank_rows.iter().map(|r| WordSlice::new(r)).collect();
    let node_slices: Vec<_> = rows.nodes.iter().map(|r| WordSlice::new(r)).collect();
    initialize()?;
    let mut watch = Watch::new("Maude unification", work);
    let words = LEAN_THREAD.with(|_| {
        // SAFETY: the shim copies every slice, which outlives the call, and
        // writes the watch, which outlives it too. MatchRows owns the single
        // output reference and releases it on every exit.
        let raw = unsafe {
            tamarin_lean_theory_maude_unify(
                theory.flags(),
                WordSlice::new(theory.free()),
                theory.ac(),
                rank_slices.as_ptr(),
                rank_slices.len(),
                fuel,
                node_slices.as_ptr(),
                node_slices.len(),
                WordSlice::new(&equations),
                watch.raw(),
            )
        };
        // A stopped call returned no reply.
        watch.finish()?;
        reply_words(&MatchRows::new(raw)?)
    })?;
    match rows_of(&words).next() {
        Some(Some([1])) => Ok(PortReply::Unifiers(read_unifiers(theory, &words, fresh)?)),
        Some(Some([3])) => Ok(PortReply::GaveUp),
        // 0 is a malformed packet, which the rows above never are.
        Some(Some([status])) => Err(Error::InvalidStatus(*status as u8)),
        _ => Err(Error::InvalidStatus(255)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::AcSym;
    use crate::maude_sig::{minimal_maude_sig, xor_maude_sig};
    use std::sync::Arc;

    fn var(id: u64, s: LSort) -> MTerm {
        Term::Lit(MaudeLit::MaudeVar(id, s))
    }

    fn fresh(k: u64) -> MTerm {
        Term::Lit(MaudeLit::FreshVar(k, LSort::Fresh))
    }

    fn xor(args: Vec<MTerm>) -> MTerm {
        f_app(FunSym::Ac(AcSym::Xor), args)
    }

    /// A command of a captured Maude 3.5.1 session on this module, and the
    /// reply Maude printed:
    ///
    /// ```text
    /// unify in MSG : tamxor(x0:Fresh,x1:Fresh) =? tamxor(x2:Msg,x3:Msg) .
    /// Unifier 1
    /// x0:Fresh --> #1:Fresh
    /// x1:Fresh --> #2:Fresh
    /// x2:Msg --> #1:Fresh
    /// x3:Msg --> #2:Fresh
    ///
    /// Unifier 2
    /// x0:Fresh --> #1:Fresh
    /// x1:Fresh --> #2:Fresh
    /// x2:Msg --> #2:Fresh
    /// x3:Msg --> #1:Fresh
    /// ```
    #[test]
    fn the_port_reads_as_maudes_reply() {
        let sig = minimal_maude_sig(false).merge(xor_maude_sig()).refresh();
        let theory = Arc::new(Theory::new(&sig).unwrap());
        let ranks = MaudeRanks::new(&sig);
        let sides = [(
            xor(vec![var(0, LSort::Fresh), var(1, LSort::Fresh)]),
            xor(vec![var(2, LSort::Msg), var(3, LSort::Msg)]),
        )];
        let reply = maude_unify(&theory, &ranks, &sides, 1 << 20, 0).expect("the port runs");
        let binding = |id, s, k| ((s, id), fresh(k));
        let (f, m) = (LSort::Fresh, LSort::Msg);
        assert_eq!(
            reply,
            PortReply::Unifiers(vec![
                vec![
                    binding(0, f, 1),
                    binding(1, f, 2),
                    binding(2, m, 1),
                    binding(3, m, 2)
                ],
                vec![
                    binding(0, f, 1),
                    binding(1, f, 2),
                    binding(2, m, 2),
                    binding(3, m, 1)
                ],
            ])
        );
        // The parser reads Maude's own reply to the same.
        let printed = b"Unifier 1\nx0:Fresh --> #1:Fresh\nx1:Fresh --> #2:Fresh\n\
            x2:Msg --> #1:Fresh\nx3:Msg --> #2:Fresh\n\nUnifier 2\nx0:Fresh --> #1:Fresh\n\
            x1:Fresh --> #2:Fresh\nx2:Msg --> #2:Fresh\nx3:Msg --> #1:Fresh\n";
        let parsed = crate::maude_parse::parse_unify_reply_with_sig(printed, &sig).unwrap();
        assert_eq!(reply, PortReply::Unifiers(parsed));
    }

    /// Applications in an image are built as the reply parser builds them.
    #[test]
    fn images_are_built_as_the_parser_builds_them() {
        let sig = minimal_maude_sig(false).merge(xor_maude_sig()).refresh();
        let theory = Arc::new(Theory::new(&sig).unwrap());
        // x0 --> tamxor(#2:Msg, tamXCFUpair(#1:Msg, f(5)), #1:Msg) with the
        // unifier's variables from 7 on.
        let (xor_kind, xor_id) = theory.encode(FunSym::Ac(AcSym::Xor), 2).unwrap();
        let pair = crate::function_symbols::FunSym::NoEq(crate::function_symbols::pair_sym());
        let (pair_kind, pair_id) = theory.encode(pair, 2).unwrap();
        let tokens = [
            0, 8, 2, // #2
            0, 7, 2, // #1
            1, 5, 1, // f(5)
            pair_kind, pair_id, 2, xor_kind, xor_id, 2, 0, 7, 2, // #1
            xor_kind, xor_id, 2,
        ];
        let read = read_image(&theory, &tokens, 7).unwrap();
        let printed = b"Unifier 1\nx0:Msg --> tamxor(#2:Msg, tamXCFUpair(#1:Msg, f(5)), #1:Msg)\n";
        let parsed = crate::maude_parse::parse_unify_reply_with_sig(printed, &sig).unwrap();
        assert_eq!(parsed, vec![vec![((LSort::Msg, 0), read)]]);
    }

    /// A term with a wrapper outside the theory is not sent.
    #[test]
    fn a_fact_wrapper_is_unencodable() {
        let sig = minimal_maude_sig(false).merge(xor_maude_sig()).refresh();
        let theory = Arc::new(Theory::new(&sig).unwrap());
        let ranks = MaudeRanks::new(&sig);
        let list = Term::App(FunSym::List, vec![var(0, LSort::Msg)].into());
        let sides = [(list.clone(), list)];
        assert_eq!(
            maude_unify(&theory, &ranks, &sides, 1 << 20, 0),
            Ok(PortReply::Unencodable)
        );
    }
}
