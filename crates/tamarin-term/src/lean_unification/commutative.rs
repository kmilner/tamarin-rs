//! A binary C root contributes two simultaneous child equations per alignment.
use super::{initialize, tamarin_comm_orientations, Error, LEAN_THREAD};
use crate::function_symbols::FunSym;
use crate::lean_identity::IdentityTable;
use crate::lterm::{LNTerm, LVar, Name};
use crate::term::Term;
use crate::vterm::Lit;

pub(super) const SEARCH_LIMIT: usize = 4096;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum RigidHead {
    Name(Name),
    SubjectVariable(LVar),
    Function(FunSym),
}

pub(super) fn orientations(terms: [&LNTerm; 4]) -> Result<u8, Error> {
    orientation_mask(terms, false)
}

pub(super) fn match_orientations(terms: [&LNTerm; 4]) -> Result<u8, Error> {
    orientation_mask(terms, true)
}

fn orientation_mask([a, b, c, d]: [&LNTerm; 4], rigid_subject: bool) -> Result<u8, Error> {
    let mut table = IdentityTable::default();
    let mut head = |t: &LNTerm, subject: bool| {
        let key = match t {
            Term::Lit(Lit::Var(v)) if subject && rigid_subject => RigidHead::SubjectVariable(*v),
            Term::Lit(Lit::Var(_)) => return Ok(0),
            Term::Lit(Lit::Con(n)) => RigidHead::Name(*n),
            Term::App(f, _) => RigidHead::Function(*f),
        };
        table
            .intern(key)
            .and_then(|i| i.checked_add(1))
            .ok_or(Error::InvalidStatus(255))
    };
    // Comparing a pattern with a rigid subject can establish orientation
    // dominance only when the common term contains no bindable variable.
    let same = |pat: &LNTerm, other: &LNTerm| {
        pat == other && (!rigid_subject || crate::vterm::is_ground_vterm(pat))
    };
    let priority = if a == b || c == d {
        3
    } else if same(a, c) || same(b, d) {
        1
    } else if same(a, d) || same(b, c) {
        2
    } else {
        0
    };
    let words = [
        head(a, false)?,
        head(b, false)?,
        head(c, true)?,
        head(d, true)?,
    ];
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the verified export takes and returns native scalar words.
        let [a, b, c, d] = words;
        let mask = unsafe { tamarin_comm_orientations(a, b, c, d, priority) };
        if mask > 3 {
            Err(Error::InvalidStatus(mask))
        } else {
            Ok(mask)
        }
    })
}
