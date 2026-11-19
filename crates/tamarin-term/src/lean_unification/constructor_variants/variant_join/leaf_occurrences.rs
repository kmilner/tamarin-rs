//! Necessary coordinate-wise occurrence bounds for a simultaneous B-match.
use super::Row;
use crate::lterm::LNTerm;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;

pub(super) struct Counts {
    leaves: Vec<Vec<u16>>,
    variables: u128,
    support: Vec<u32>,
}

impl Counts {
    pub(super) fn new(row: &Row) -> Option<Self> {
        let width = row.images.len() + row.values.len();
        if width > 32 {
            return None;
        }
        let mut out = Self {
            leaves: Vec::new(),
            variables: 0,
            support: Vec::new(),
        };
        let mut indices: FxHashMap<&LNTerm, usize> = FxHashMap::default();
        for (i, term) in row.iter().enumerate() {
            let mut stack = vec![term];
            while let Some(t) = stack.pop() {
                if let Term::App(_, args) = t
                    && !args.is_empty()
                {
                    stack.extend(args.iter());
                    continue;
                }
                let index = match indices.get(t) {
                    Some(&j) => j,
                    None => {
                        let j = out.leaves.len();
                        if j == 128 {
                            return None;
                        }
                        out.leaves.push(vec![0; width]);
                        out.support.push(0);
                        if matches!(t, Term::Lit(Lit::Var(_))) {
                            out.variables |= 1 << j;
                        }
                        indices.insert(t, j);
                        j
                    }
                };
                out.support[index] |= 1 << i;
                let count = &mut out.leaves[index][i];
                *count = count.saturating_add(1);
            }
        }
        Some(out)
    }

    /// Every image of a pattern variable has a leaf (variable, literal or
    /// nullary application). In each coordinate the target must contain at
    /// least as many copies of that same leaf as the pattern has of the variable.
    pub(super) fn fits(&self, target: &Self) -> bool {
        let mut witnessed = 0u128;
        for (w, subject) in target.leaves.iter().enumerate() {
            let mut source_coords = 0u32;
            let mut vars = self.variables;
            while vars != 0 {
                let v = vars.trailing_zeros() as usize;
                vars &= vars - 1;
                if self.support[v] & !target.support[w] == 0
                    && self.leaves[v].iter().zip(subject).all(|(p, s)| p <= s)
                {
                    witnessed |= 1 << v;
                    source_coords |= self.support[v];
                }
            }
            // A target variable must be supplied by an admissible capture at
            // each coordinate in which it occurs. Fixed syntax contains none.
            if target.variables & (1 << w) != 0 && target.support[w] & !source_coords != 0 {
                return false;
            }
        }
        self.variables == witnessed
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{hash, msg_var, mult, one_const};
    use crate::lterm::pub_term;

    fn counts(ts: Vec<LNTerm>) -> Counts {
        Counts::new(&Row {
            images: ts,
            values: vec![],
        })
        .unwrap()
    }

    #[test]
    fn compared_coordinates_share_variable_origins() {
        let x = msg_var("x", 0);
        let a = msg_var("a", 1);
        let b = msg_var("b", 2);
        assert!(!counts(vec![x.clone(), x.clone()]).fits(&counts(vec![a.clone(), b.clone()])));
        assert!(!counts(vec![x.clone(), one_const()]).fits(&counts(vec![a.clone(), b.clone()])));
        let value = mult(a, hash(b));
        assert!(counts(vec![x.clone(), x.clone()]).fits(&counts(vec![value.clone(), value])));
        // Fixed syntax can itself produce ground leaves.
        assert!(counts(vec![x, one_const()]).fits(&counts(vec![pub_term("c"), one_const()])));
    }
}
