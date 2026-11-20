//! Submit the original conjunction to the total mixed unifier. A binding row
//! is a postfix term over the request dictionary. Range variables share one
//! fresh namespace per answer, as required by SubstVFresh.
use super::Packet;
use crate::function_symbols::FunSym;
use crate::lean_unification::{
    declaration, initialize, sort_word, subsort, Error, MatchRows, Outcome, Substitutions,
    WordSlice, LEAN_THREAD,
};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_sig::MaudeSig;
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::{f_app, Term};
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use tamarin_utils::cancellation;

unsafe extern "C" {
    fn tamarin_lean_total_unify(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        equations: WordSlice,
    ) -> *mut std::ffi::c_void;
}

pub(crate) fn unify(sig: &MaudeSig, eqs: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
    let mut packet = Packet::default();
    let symbols = sig.declared_fun_syms();
    for eq in eqs {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        for t in [&eq.lhs, &eq.rhs] {
            let id = packet.encode_term(
                t,
                false,
                |s| sig.enable_nat || s != LSort::Nat,
                |f| {
                    symbols
                        .contains(&f)
                        .then(|| declaration(f, sig.enable_nat))
                        .flatten()
                },
            );
            let Some(id) = id else {
                return Ok(Outcome::Unsupported);
            };
            packet.equations.push(id);
        }
    }
    initialize()?;
    let rows = packet.rows();
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim consumes its own copies of all slices. MatchRows
        // owns the single output reference and releases it on every exit.
        let reply = MatchRows::new(unsafe {
            tamarin_lean_total_unify(
                WordSlice::new(&packet.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations),
            )
        })?;
        decode(&packet, &reply, sig.enable_nat).map(Outcome::Complete)
    })
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

struct Arm<'a> {
    bindings: Vec<Option<LNTerm>>,
    witnesses: FxHashMap<(u64, LSort), LVar>,
    reserved: &'a FxHashSet<u64>,
    next: std::ops::RangeInclusive<u64>,
    has_nat_witness: bool,
}
impl<'a> Arm<'a> {
    fn new(width: usize, reserved: &'a FxHashSet<u64>) -> Self {
        Self {
            bindings: vec![None; width],
            witnesses: FxHashMap::default(),
            reserved,
            next: 0..=u64::MAX,
            has_nat_witness: false,
        }
    }

    fn variable(&mut self, id: u64, s: LSort) -> Result<LNTerm, Error> {
        self.has_nat_witness |= s == LSort::Nat;
        if let Some(v) = self.witnesses.get(&(id, s)) {
            return Ok(Term::Lit(Lit::Var(*v)));
        }
        let idx = self
            .next
            .find(|i| !self.reserved.contains(i))
            .ok_or(Error::FreshVariableOverflow)?;
        let v = LVar::new("x", s, idx);
        self.witnesses.insert((id, s), v);
        Ok(Term::Lit(Lit::Var(v)))
    }

    fn binding(&mut self, packet: &Packet, words: &[u64], nat: bool) -> Result<(), Error> {
        let [key, expected, tokens @ ..] = words else {
            return Err(Error::InvalidStatus(255));
        };
        let var = packet
            .variables
            .get(*key)
            .ok_or(Error::InvalidVariable(*key))?;
        let (tokens, rest) = tokens.as_chunks::<3>();
        if sort_word(var.sort) != *expected || !rest.is_empty() {
            return Err(Error::InvalidStatus(255));
        }
        let mut stack: Vec<(LNTerm, LSort)> = Vec::new();
        for &[k, id, aux] in tokens {
            let value = match k {
                0 => {
                    let s = sort(aux)?;
                    (self.variable(id, s)?, s)
                }
                1 => {
                    let name = packet.names.get(id).ok_or(Error::InvalidAtom(id))?;
                    let s = sort_of_name(&name);
                    if sort_word(s) != aux {
                        return Err(Error::InvalidAtom(id));
                    }
                    (Term::Lit(Lit::Con(name)), s)
                }
                _ => {
                    let f = packet.symbols.get(id).ok_or(Error::InvalidStatus(255))?;
                    let (arity, s) = declaration(f, nat).ok_or(Error::InvalidStatus(255))?;
                    if aux != arity as u64
                        || !matches!(
                            (k, f),
                            (2, FunSym::NoEq(_)) | (3, FunSym::C(_)) | (4, FunSym::Ac(_))
                        )
                    {
                        return Err(Error::InvalidStatus(255));
                    }
                    let start = stack
                        .len()
                        .checked_sub(arity)
                        .ok_or(Error::InvalidStatus(255))?;
                    let children = stack
                        .drain(start..)
                        .map(|(t, actual)| {
                            if subsort(actual, s) {
                                Ok(t)
                            } else {
                                Err(Error::InvalidStatus(255))
                            }
                        })
                        .collect::<Result<_, _>>()?;
                    (f_app(f, children), s)
                }
            };
            stack.push(value);
        }
        let Some((term, actual)) = stack.pop() else {
            return Err(Error::InvalidStatus(255));
        };
        if !stack.is_empty()
            || !subsort(actual, var.sort)
            || self.bindings[*key as usize].replace(term).is_some()
        {
            return Err(Error::InvalidStatus(255));
        }
        Ok(())
    }

    fn finish(self, packet: &Packet, nat: bool, answers: &mut Substitutions) -> Result<(), Error> {
        let images = self
            .bindings
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(Error::InvalidStatus(255))?;
        if nat || !self.has_nat_witness {
            answers.push(
                packet
                    .variables
                    .values()
                    .iter()
                    .copied()
                    .zip(images)
                    .collect(),
            );
        }
        Ok(())
    }
}

fn decode(packet: &Packet, reply: &MatchRows, nat: bool) -> Result<Substitutions, Error> {
    if reply.count() != 1 || reply.row_size(0, 0)? != 1 {
        return Err(Error::InvalidStatus(255));
    }
    let mut header = [0];
    reply.copy_row(0, 0, &mut header)?;
    if header != [1] {
        return Err(Error::InvalidStatus(255));
    }
    let reserved = packet.variables.values().iter().map(|v| v.idx).collect();
    let mut answers = Vec::new();
    let mut current = None;
    let mut buf = Vec::new();
    for i in 1..reply.rows(0) {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        let size = reply.raw_row_size(0, i);
        if size == 0 {
            if let Some(arm) = current.replace(Arm::new(packet.variables.len(), &reserved)) {
                arm.finish(packet, nat, &mut answers)?;
            }
        } else {
            if size == usize::MAX {
                return Err(Error::InvalidStatus(255));
            }
            buf.resize(size, 0);
            if reply.copy_row(0, i, &mut buf)? != size {
                return Err(Error::InvalidStatus(255));
            }
            current
                .as_mut()
                .ok_or(Error::InvalidStatus(255))?
                .binding(packet, &buf, nat)?;
        }
    }
    if let Some(arm) = current {
        arm.finish(packet, nat, &mut answers)?;
    }
    Ok(answers)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binding_rows_preserve_sharing_and_reject_invalid_terms_and_domains() {
        let mut packet = Packet::default();
        let x = LVar::new("a", LSort::Msg, 0);
        let y = LVar::new("b", LSort::Msg, 0);
        packet.variables.intern(x).unwrap();
        packet.variables.intern(y).unwrap();
        packet
            .symbols
            .intern(FunSym::Ac(crate::function_symbols::AcSym::Union))
            .unwrap();
        let reserved = [0].into_iter().collect();
        let mut arm = Arm::new(2, &reserved);
        for malformed in [
            vec![0, 2, 1, 9, 0],          // unknown atom
            vec![0, 2, 4, 0, 2],          // missing children
            vec![0, 2, 0, 8, 3],          // Node in a Msg range
            vec![0, 2, 0, 8, 2, 0, 9, 2], // two roots
            vec![1, 0, 0, 8, 2],          // wrong key sort
            vec![2, 2, 0, 8, 2],          // unknown key
        ] {
            assert!(arm.binding(&packet, &malformed, false).is_err());
        }
        arm.binding(&packet, &[1, 2, 0, 8, 2], false).unwrap();
        arm.binding(&packet, &[0, 2, 0, 8, 2, 0, 8, 2, 4, 0, 2], false)
            .unwrap();
        let mut answers = Vec::new();
        arm.finish(&packet, false, &mut answers).unwrap();
        let w = answers[0][1].1.clone();
        assert!(matches!(w, Term::Lit(Lit::Var(v)) if v.idx != 0));
        assert_eq!(
            answers[0][0].1,
            f_app(
                FunSym::Ac(crate::function_symbols::AcSym::Union),
                vec![w.clone(), w]
            )
        );
        let mut incomplete = Arm::new(2, &reserved);
        incomplete
            .binding(&packet, &[0, 2, 0, 8, 4], false)
            .unwrap();
        assert!(incomplete
            .binding(&packet, &[0, 2, 0, 8, 4], false)
            .is_err());
        assert!(incomplete.finish(&packet, false, &mut answers).is_err());
    }
}
