//! Stream proper AC subbags by occurrence, including repeated operands.
use crate::lean_unification::{initialize, Error, MatchRows, LEAN_THREAD};

unsafe extern "C" {
    fn tamarin_lean_ac_subgroups(size: u64) -> *mut std::ffi::c_void;
}

pub(super) struct ProperSubgroups {
    rows: MatchRows,
    next: usize,
    indices: Vec<u64>,
    selected: Vec<bool>,
}

impl ProperSubgroups {
    pub(super) fn new(width: usize) -> Result<Option<Self>, Error> {
        initialize()?;
        LEAN_THREAD.with(|_| {
            // SAFETY: this thread takes ownership of the result through MatchRows.
            let raw = unsafe { tamarin_lean_ac_subgroups(width as u64) };
            if raw.is_null() {
                return Ok(None);
            }
            let rows = MatchRows::new(raw)?;
            if rows.count() != 1 {
                return Err(Error::InvalidStatus(255));
            }
            Ok(Some(Self {
                rows,
                next: 0,
                indices: vec![0; width],
                selected: vec![false; width],
            }))
        })
    }

    pub(super) fn next(&mut self) -> Result<Option<&[bool]>, Error> {
        while self.next < self.rows.rows(0) {
            let len = self.rows.copy_row(0, self.next, &mut self.indices)?;
            self.next += 1;
            if len < 2 {
                return Err(Error::InvalidStatus(255));
            }
            self.selected.fill(false);
            for &index in &self.indices[..len] {
                let flag = self
                    .selected
                    .get_mut(index as usize)
                    .ok_or(Error::InvalidSubject(index))?;
                if *flag {
                    return Err(Error::InvalidSubject(index));
                }
                *flag = true;
            }
            if len < self.selected.len() {
                return Ok(Some(&self.selected));
            }
        }
        Ok(None)
    }
}
