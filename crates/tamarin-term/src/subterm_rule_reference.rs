// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Independent pre-refactor occurrence-search reference for small tests.
use crate::{lterm::LNTerm, positions::Position, term::Term};
/// Find every position in `haystack` where `needle` occurs.
pub fn find_subterm(haystack: &LNTerm, needle: &LNTerm) -> Vec<Position> {
    fn go(haystack: &LNTerm, needle: &LNTerm, prefix: &mut Vec<i64>, out: &mut Vec<Position>) {
        if haystack == needle {
            out.push(prefix.clone());
            return;
        }
        if let Term::App(_, args) = haystack {
            for (i, a) in args.iter().enumerate() {
                prefix.push(i as i64);
                go(a, needle, prefix, out);
                prefix.pop();
            }
        }
    }
    let mut out = Vec::new();
    let mut prefix = Vec::new();
    go(haystack, needle, &mut prefix, &mut out);
    out
}

/// `findAllSubterms l r`: positions of `r` in `l`, recursing into `r`'s
/// subterms if `r` doesn't occur. Returns `None` if no variable in `r`
/// appears in `l`.
pub fn find_all_subterms(l: &LNTerm, r: &LNTerm) -> Option<Vec<Position>> {
    use crate::vterm::Lit;
    let direct = find_subterm(l, r);
    match r {
        Term::App(_, args) => {
            if !direct.is_empty() {
                return Some(direct);
            }
            let mut out = Vec::new();
            for sub in args.iter() {
                let parts = find_all_subterms(l, sub)?;
                out.extend(parts);
            }
            Some(out)
        }
        Term::Lit(Lit::Var(_)) => {
            if direct.is_empty() {
                None
            } else {
                Some(direct)
            }
        }
        Term::Lit(Lit::Con(_)) => None,
    }
}
