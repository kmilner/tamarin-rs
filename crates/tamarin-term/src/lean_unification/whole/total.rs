//! Shared term graph and substitution packets for the verified references.
//! Matches retain literal input variables. Unifier and variant witnesses share
//! a fresh namespace within each returned substitution.
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
    fn tamarin_lean_total_match(
        declarations: WordSlice,
        rows: *const WordSlice,
        count: usize,
        equations: WordSlice,
        bindable: WordSlice,
    ) -> *mut std::ffi::c_void;
}

pub(crate) fn unify(sig: &MaudeSig, eqs: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
    let Some(packet) = Packet::encode_total(sig, eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]))? else {
        return Ok(Outcome::Unsupported);
    };
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
        decode(&packet, &reply, sig.enable_nat, DecodeMode::Unify).map(Outcome::Complete)
    })
}

/// Equations have (pattern, subject) orientation. Subject variables keep their caller identities.
pub(crate) fn matches(
    sig: &MaudeSig,
    eqs: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Outcome, Error> {
    let Some(packet) = Packet::encode_total(sig, eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]))? else {
        return Ok(Outcome::Unsupported);
    };
    let keys: FxHashSet<_> = eqs
        .iter()
        .flat_map(|e| crate::lterm::frees(&e.lhs))
        .filter(bindable)
        .collect();
    let ids = keys
        .iter()
        .map(|v| packet.variables.id(*v).ok_or(Error::InvalidStatus(255)))
        .collect::<Result<Vec<_>, _>>()?;
    initialize()?;
    let rows = packet.rows();
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim takes owned copies and transfers its output to MatchRows.
        let reply = MatchRows::new(unsafe {
            tamarin_lean_total_match(
                WordSlice::new(&packet.declarations),
                rows.as_ptr(),
                rows.len(),
                WordSlice::new(&packet.equations),
                WordSlice::new(&ids),
            )
        })?;
        decode(&packet, &reply, sig.enable_nat, DecodeMode::Match(&keys)).map(Outcome::Complete)
    })
}

impl Packet {
    pub(super) fn encode_total<'a>(
        sig: &MaudeSig,
        terms: impl IntoIterator<Item = &'a LNTerm>,
    ) -> Result<Option<Self>, Error> {
        let mut packet = Self::default();
        let symbols = sig.declared_fun_syms();
        for t in terms {
            cancellation::check().map_err(|_| Error::Cancelled)?;
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
            let Some(id) = id else { return Ok(None) };
            packet.equations.push(id);
        }
        Ok(Some(packet))
    }

    fn read_image(
        &self,
        tokens: &[u64],
        nat: bool,
        mut variable: impl FnMut(u64, LSort) -> Result<LNTerm, Error>,
    ) -> Result<(LNTerm, Option<LSort>), Error> {
        let (tokens, rest) = tokens.as_chunks::<3>();
        if !rest.is_empty() {
            return Err(Error::InvalidStatus(255));
        }
        let mut stack: Vec<(LNTerm, Option<LSort>)> = Vec::new();
        for &[k, id, aux] in tokens {
            let value = match k {
                0 => {
                    let s = sort(aux)?;
                    (variable(id, s)?, Some(s))
                }
                1 => {
                    let name = self.names.get(id).ok_or(Error::InvalidAtom(id))?;
                    let s = sort_of_name(&name);
                    if sort_word(s) != aux {
                        return Err(Error::InvalidAtom(id));
                    }
                    (Term::Lit(Lit::Con(name)), Some(s))
                }
                _ => {
                    let f = self.symbols.get(id).ok_or(Error::InvalidStatus(255))?;
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
                    let mut sorted = true;
                    let children = stack
                        .drain(start..)
                        .map(|(t, actual)| {
                            sorted &= actual.is_some_and(|actual| subsort(actual, s));
                            t
                        })
                        .collect();
                    (f_app(f, children), sorted.then_some(s))
                }
            };
            stack.push(value);
        }
        if stack.len() != 1 {
            return Err(Error::InvalidStatus(255));
        }
        stack.pop().ok_or(Error::InvalidStatus(255))
    }

    fn input_variable(&self, id: u64, sort: LSort) -> Result<LNTerm, Error> {
        self.variables
            .get(id)
            .filter(|v| v.sort == sort)
            .map(|v| Term::Lit(Lit::Var(v)))
            .ok_or(Error::InvalidVariable(id))
    }

    pub(super) fn read_term(&self, words: &[u64], nat: bool) -> Result<LNTerm, Error> {
        self.read_image(words, nat, |id, s| self.input_variable(id, s))
            .map(|(t, _)| t)
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

#[derive(Clone, Copy)]
enum DecodeMode<'a> {
    Unify,
    Match(&'a FxHashSet<LVar>),
    Variants(usize),
}

struct Arm<'a> {
    mode: DecodeMode<'a>,
    bindings: Vec<Option<LNTerm>>,
    witnesses: FxHashMap<(u64, LSort), LVar>,
    reserved: &'a FxHashSet<u64>,
    next: std::ops::RangeInclusive<u64>,
    has_nat_witness: bool,
}
impl<'a> Arm<'a> {
    fn new(width: usize, reserved: &'a FxHashSet<u64>, mode: DecodeMode<'a>) -> Self {
        Self {
            mode,
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
        if sort_word(var.sort) != *expected {
            return Err(Error::InvalidStatus(255));
        }
        let (term, actual) = packet.read_image(tokens, nat, |id, s| match self.mode {
            DecodeMode::Unify | DecodeMode::Variants(_) => self.variable(id, s),
            DecodeMode::Match(_) => packet.input_variable(id, s),
        })?;
        let slot = self
            .bindings
            .get_mut(*key as usize)
            .ok_or(Error::InvalidVariable(*key))?;
        if !actual.is_some_and(|s| subsort(s, var.sort)) || slot.replace(term).is_some() {
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
        let pairs = packet.variables.values().iter().copied().zip(images);
        match self.mode {
            DecodeMode::Unify if nat || !self.has_nat_witness => answers.push(pairs.collect()),
            DecodeMode::Variants(_) if nat || !self.has_nat_witness => {
                let mut bindings: Vec<_> = pairs.collect();
                bindings.sort_unstable_by_key(|(v, _)| *v);
                answers.push(bindings);
            }
            DecodeMode::Unify | DecodeMode::Variants(_) => {}
            DecodeMode::Match(keys) => {
                let mut bindings = Vec::with_capacity(keys.len());
                for (var, image) in pairs {
                    if keys.contains(&var) {
                        bindings.push((var, image));
                    } else if image != Term::Lit(Lit::Var(var)) {
                        return Err(Error::InvalidStatus(255));
                    }
                }
                bindings.sort_unstable_by_key(|(v, _)| *v);
                answers.push(bindings);
            }
        }
        Ok(())
    }
}

fn header(reply: &MatchRows) -> Result<u64, Error> {
    if reply.count() != 1 || reply.row_size(0, 0)? != 1 {
        return Err(Error::InvalidStatus(255));
    }
    let mut word = [0];
    if reply.copy_row(0, 0, &mut word)? != 1 {
        return Err(Error::InvalidStatus(255));
    }
    Ok(word[0])
}

/// Observations precede rule terms in the shared dictionary. Only observation
/// variables are reply keys. A stopped frontier has exactly one status row.
pub(super) fn decode_variants(
    packet: &Packet,
    reply: &MatchRows,
    nat: bool,
    width: usize,
) -> Result<Outcome, Error> {
    if width > packet.variables.len() {
        return Err(Error::InvalidStatus(255));
    }
    if header(reply)? == 2 && reply.rows(0) == 1 {
        return Ok(Outcome::Unsupported);
    }
    let answers = decode(packet, reply, nat, DecodeMode::Variants(width))?;
    if answers.is_empty() {
        // A certified variant packet contains at least one arm. If every arm
        // requires a sort absent from this module, leave the request unresolved.
        if !nat && reply.rows(0) > 1 {
            return Ok(Outcome::Unsupported);
        }
        return Err(Error::InvalidStatus(255));
    }
    Ok(Outcome::Complete(answers))
}

fn decode(
    packet: &Packet,
    reply: &MatchRows,
    nat: bool,
    mode: DecodeMode<'_>,
) -> Result<Substitutions, Error> {
    if header(reply)? != 1 {
        return Err(Error::InvalidStatus(255));
    }
    let width = match mode {
        DecodeMode::Variants(n) => n,
        _ => packet.variables.len(),
    };
    let reserved = packet.variables.values()[..width]
        .iter()
        .map(|v| v.idx)
        .collect();
    let mut answers = Vec::new();
    let mut current = None;
    let mut buf = Vec::new();
    for i in 1..reply.rows(0) {
        cancellation::check().map_err(|_| Error::Cancelled)?;
        let size = reply.raw_row_size(0, i);
        if size == 0 {
            if let Some(arm) = current.replace(Arm::new(width, &reserved, mode)) {
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
        let mut arm = Arm::new(2, &reserved, DecodeMode::Unify);
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
        let mut incomplete = Arm::new(2, &reserved, DecodeMode::Unify);
        incomplete
            .binding(&packet, &[0, 2, 0, 8, 4], false)
            .unwrap();
        assert!(incomplete
            .binding(&packet, &[0, 2, 0, 8, 4], false)
            .is_err());
        assert!(incomplete.finish(&packet, false, &mut answers).is_err());
    }
}
