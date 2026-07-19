// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, jdreier, meiersi, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Positions.hs

//! Port of `Term.Positions` from `lib/term/src/Term/Positions.hs`.
//!
//! Positions in terms, subterm access, and replacement. AC operators with
//! n-ary applications are interpreted as right-leaning binary apps:
//! `*[t1,..,tk]` ≡ `t1 * (t2 * (… * tk))`. `0` selects the head, `1` the
//! tail multiset.

use crate::function_symbols::FunSym;
use crate::term::{f_app, is_ac, is_pair, Term};
use crate::vterm::{Lit, VTerm};

/// A position in a term — list of integers.
pub type Position = Vec<i64>;

/// `t @ p`: subterm of `t` at `p`. Returns `None` for invalid positions.
pub fn at_pos<C: Ord + Clone, V: Ord + Clone>(t: &VTerm<C, V>, p: &[i64]) -> Option<VTerm<C, V>> {
    if p.is_empty() { return Some(t.clone()); }
    match t {
        Term::Lit(_) => None,
        Term::App(FunSym::Ac(s), args) => match (p[0], &args[..]) {
            (_, []) => None,
            (0, [a, ..]) => at_pos(a, &p[1..]),
            (1, [_, only]) => at_pos(only, &p[1..]),
            (1, [_, rest @ ..]) if !rest.is_empty() => {
                let tail = f_app(FunSym::Ac(*s), rest.to_vec());
                at_pos(&tail, &p[1..])
            }
            _ => None,
        },
        Term::App(_, args) => {
            let i = p[0] as usize;
            if p[0] < 0 || i >= args.len() { return None; }
            at_pos(&args[i], &p[1..])
        }
    }
}

/// `t.replace_pos(s, p)`: replace the subterm at `p` with `s`.
pub fn replace_pos<C: Ord + Clone, V: Ord + Clone>(
    t: &VTerm<C, V>,
    s: &VTerm<C, V>,
    p: &[i64],
) -> Option<VTerm<C, V>> {
    if p.is_empty() { return Some(s.clone()); }
    match t {
        Term::Lit(_) => None,
        Term::App(FunSym::Ac(sym), args) => match (p[0], &args[..]) {
            (0, [head, rest @ ..]) => {
                let new_head = replace_pos(head, s, &p[1..])?;
                let mut new_args = vec![new_head];
                new_args.extend(rest.iter().cloned());
                Some(f_app(FunSym::Ac(*sym), new_args))
            }
            (1, [head, rest @ ..]) if !rest.is_empty() => {
                let tail = f_app(FunSym::Ac(*sym), rest.to_vec());
                let new_tail = replace_pos(&tail, s, &p[1..])?;
                Some(f_app(FunSym::Ac(*sym), vec![head.clone(), new_tail]))
            }
            _ => None,
        },
        Term::App(fsym, args) => {
            let i = p[0] as usize;
            if p[0] < 0 || i >= args.len() { return None; }
            let mut new = args.to_vec();
            new[i] = replace_pos(&args[i], s, &p[1..])?;
            Some(f_app(fsym.clone(), new))
        }
    }
}

/// `find_pos t s`: all positions at which subterm `t` occurs inside `s`,
/// or `None` if `t` is not a subterm. Port of HS `findPos` (Positions.hs:63-70).
///
/// NB: this mirrors HS exactly by indexing over the **n-ary** argument list
/// (`viewTerm -> FApp _ ts`), NOT the right-leaning binary-AC encoding used
/// by [`at_pos`]. These positions feed `print_position` (the `AUTO_*` fact
/// names) and [`deepest_prot_subterm`], which use the same n-ary indexing.
/// The result order matches HS's `foldr` (highest index first, index 0 last).
pub fn find_pos<C: Ord + Clone, V: Ord + Clone>(
    t: &VTerm<C, V>,
    s: &VTerm<C, V>,
) -> Option<Vec<Position>> {
    if t == s {
        return Some(vec![vec![]]);
    }
    match s {
        Term::App(_, ts) => {
            let mut acc: Option<Vec<Position>> = None;
            // foldr over `zip [0..] ts`: process indices high→low, appending
            // each contributing index's `(x:)`-prefixed positions.
            for (x, sub) in ts.iter().enumerate().rev() {
                if let Some(ps) = find_pos(t, sub) {
                    let prefixed = ps.into_iter().map(|mut p| {
                        p.insert(0, x as i64);
                        p
                    });
                    match &mut acc {
                        None => acc = Some(prefixed.collect()),
                        Some(v) => v.extend(prefixed),
                    }
                }
            }
            acc
        }
        Term::Lit(_) => None,
    }
}

/// `deepest_prot_subterm term pos`: the deepest "protected" subterm of `term`
/// on the path to `pos` (anything but a pair or AC operator is protected).
/// Returns `None` if there is no protected subterm. Port of HS
/// `deepestProtSubterm` (Positions.hs:125-135). Uses n-ary indexing (`atMay`),
/// matching [`find_pos`]. Panics on an invalid position, like HS.
pub fn deepest_prot_subterm<C: Ord + Clone, V: Ord + Clone>(
    term: &VTerm<C, V>,
    pos: &[i64],
) -> Option<VTerm<C, V>> {
    fn f<C: Ord + Clone, V: Ord + Clone>(
        orig: &VTerm<C, V>,
        st: VTerm<C, V>,
        t: &VTerm<C, V>,
        pos: &[i64],
    ) -> Option<VTerm<C, V>> {
        match pos.split_first() {
            None => {
                if &st == orig && (is_pair(orig) || is_ac(orig)) {
                    None
                } else {
                    Some(st)
                }
            }
            Some((i, rest)) => match t {
                Term::App(_, args) => {
                    let a = args
                        .get(*i as usize)
                        .expect("deepest_prot_subterm: invalid position given");
                    let new_st = if is_pair(t) || is_ac(t) { st } else { t.clone() };
                    f(orig, new_st, a, rest)
                }
                Term::Lit(_) => panic!("deepest_prot_subterm: invalid position given"),
            },
        }
    }
    f(term, term.clone(), term, pos)
}

/// `positions t`: every position in `t` (including the empty position at
/// the root). AC nesting follows the right-leaning binary interpretation.
pub fn positions<C, V>(t: &VTerm<C, V>) -> Vec<Position> {
    fn go<C, V>(t: &VTerm<C, V>, out: &mut Vec<Position>, prefix: &mut Vec<i64>) {
        out.push(prefix.clone());
        if let Term::App(FunSym::Ac(_), args) = t {
            let len = args.len();
            for (i, a) in args.iter().enumerate() {
                let saved = prefix.len();
                prefix.extend_from_slice(&ac_position(i, len));
                go(a, out, prefix);
                prefix.truncate(saved);
            }
        } else if let Term::App(_, args) = t {
            for (i, a) in args.iter().enumerate() {
                prefix.push(i as i64);
                go(a, out, prefix);
                prefix.pop();
            }
        }
    }
    let mut out = Vec::new();
    let mut prefix = Vec::new();
    go(t, &mut out, &mut prefix);
    out
}

/// `positionsNonVar`: like `positions` but excludes positions where the
/// subterm is a variable.
pub fn positions_non_var<C, V>(t: &VTerm<C, V>) -> Vec<Position> {
    fn go<C, V>(t: &VTerm<C, V>, out: &mut Vec<Position>, prefix: &mut Vec<i64>) {
        match t {
            Term::Lit(Lit::Var(_)) => {}
            Term::Lit(Lit::Con(_)) => out.push(prefix.clone()),
            Term::App(FunSym::Ac(_), args) => {
                out.push(prefix.clone());
                let len = args.len();
                for (i, a) in args.iter().enumerate() {
                    let saved = prefix.len();
                    prefix.extend_from_slice(&ac_position(i, len));
                    go(a, out, prefix);
                    prefix.truncate(saved);
                }
            }
            Term::App(_, args) => {
                out.push(prefix.clone());
                for (i, a) in args.iter().enumerate() {
                    prefix.push(i as i64);
                    go(a, out, prefix);
                    prefix.pop();
                }
            }
        }
    }
    let mut out = Vec::new();
    let mut prefix = Vec::new();
    go(t, &mut out, &mut prefix);
    out
}

fn ac_position(i: usize, len: usize) -> Vec<i64> {
    if i == len - 1 {
        vec![1; i]
    } else {
        let mut v = vec![1; i];
        v.push(0);
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{msg_var, pair};
    use crate::lterm::LNTerm;

    #[test]
    fn at_pos_root() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let r = at_pos(&t, &[]).unwrap();
        assert_eq!(r, t);
    }

    #[test]
    fn find_pos_root_and_children() {
        let a = msg_var("a", 0);
        let b = msg_var("b", 0);
        let t: LNTerm = pair(a.clone(), b.clone());
        assert_eq!(find_pos(&t, &t), Some(vec![vec![]]));
        assert_eq!(find_pos(&a, &t), Some(vec![vec![0]]));
        assert_eq!(find_pos(&b, &t), Some(vec![vec![1]]));
        assert_eq!(find_pos(&msg_var("z", 0), &t), None);
    }

    #[test]
    fn find_pos_multiple_occurrences_hs_foldr_order() {
        // pair(a, pair(b, a)): `a` occurs at [0] and [1,1]. HS `findPos`
        // folds right, so the higher index's positions come first.
        let a = msg_var("a", 0);
        let b = msg_var("b", 0);
        let t: LNTerm = pair(a.clone(), pair(b.clone(), a.clone()));
        assert_eq!(find_pos(&a, &t), Some(vec![vec![1, 1], vec![0]]));
    }

    #[test]
    fn deepest_prot_subterm_through_pair() {
        // In pair(h(a), b), the deepest protected subterm on the path to
        // a (position [0,0]) is h(a): pairs are transparent, h is protected.
        use crate::builtin::msg_var as mv;
        use crate::function_symbols::{FunSym, NoEqSym, Privacy, Constructability};
        let h = NoEqSym::new(b"h", 1, Privacy::Public, Constructability::Constructor);
        let ha: LNTerm = Term::App(FunSym::NoEq(h), vec![mv("a", 0)].into());
        let t: LNTerm = pair(ha.clone(), mv("b", 0));
        assert_eq!(deepest_prot_subterm(&t, &[0, 0]), Some(ha));
        // No protected subterm above a top-level pair → None at the root.
        assert_eq!(deepest_prot_subterm(&t, &[]), None);
    }

    #[test]
    fn at_pos_first_child() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let r = at_pos(&t, &[0]).unwrap();
        assert_eq!(r, msg_var("x", 0));
    }

    #[test]
    fn replace_pos_at_first_child() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let new = msg_var("z", 0);
        let r = replace_pos(&t, &new, &[0]).unwrap();
        assert_eq!(r, pair(msg_var("z", 0), msg_var("y", 0)));
    }

    #[test]
    fn positions_includes_root_and_each_subterm() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let ps = positions(&t);
        assert!(ps.contains(&Vec::<i64>::new()));
        assert!(ps.contains(&vec![0i64]));
        assert!(ps.contains(&vec![1i64]));
        assert_eq!(ps.len(), 3);
    }

    #[test]
    fn positions_non_var_excludes_variables() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let ps = positions_non_var(&t);
        // Only the root is non-variable.
        assert_eq!(ps, vec![Vec::<i64>::new()]);
    }
}
