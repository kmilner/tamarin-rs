// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.Positions` from `lib/term/src/Term/Positions.hs`.
//!
//! Positions in terms, subterm access, and replacement. AC operators with
//! n-ary applications are interpreted as right-leaning binary apps:
//! `*[t1,..,tk]` ≡ `t1 * (t2 * (… * tk))`. `0` selects the head, `1` the
//! tail multiset.

use crate::function_symbols::FunSym;
use crate::term::{f_app, is_ac, is_pair, Term};
use crate::vterm::VTerm;

/// A position in a term — list of integers.
pub type Position = Vec<i64>;

/// `t @ p`: subterm of `t` at `p`. Returns `None` for invalid positions.
pub fn at_pos<C: Ord + Clone, V: Ord + Clone>(
    t: &VTerm<C, V>,
    mut p: &[i64],
) -> Option<VTerm<C, V>> {
    let mut t = t;
    let mut tail_storage;
    while let Some((&index, rest)) = p.split_first() {
        t = match t {
            Term::Lit(_) => return None,
            Term::App(FunSym::Ac(s), args) => match (index, &args[..]) {
                (_, []) => return None,
                (0, [a, ..]) => a,
                (1, [_, only]) => only,
                (1, [_, args @ ..]) if !args.is_empty() => {
                    // The smart constructor may normalize a synthetic AC tail.
                    // Own the current tail while borrowing descendants from it.
                    tail_storage = f_app(FunSym::Ac(*s), args.to_vec());
                    &tail_storage
                }
                _ => return None,
            },
            Term::App(_, args) => {
                if index < 0 {
                    return None;
                }
                args.get(index as usize)?
            }
        };
        p = rest;
    }
    Some(t.clone())
}

/// `t.replace_pos(s, p)`: replace the subterm at `p` with `s`.
pub fn replace_pos<C: Ord + Clone, V: Ord + Clone>(
    t: &VTerm<C, V>,
    s: &VTerm<C, V>,
    p: &[i64],
) -> Option<VTerm<C, V>> {
    if p.is_empty() {
        return Some(s.clone());
    }
    tamarin_utils::stack::ensure_sufficient_stack(|| match t {
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
            if p[0] < 0 || i >= args.len() {
                return None;
            }
            let mut new = args.to_vec();
            new[i] = replace_pos(&args[i], s, &p[1..])?;
            Some(f_app(*fsym, new))
        }
    })
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
    let mut out = Vec::new();
    visit_positions(s, PositionMode::ReverseNary, |node, path| {
        if node == t {
            out.push(path.to_vec());
            false
        } else {
            true
        }
    });
    (!out.is_empty()).then_some(out)
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
    let mut current = term;
    let mut protected = term.clone();
    for &index in pos {
        let Term::App(_, args) = current else {
            panic!("deepest_prot_subterm: invalid position given");
        };
        let child = args
            .get(index as usize)
            .expect("deepest_prot_subterm: invalid position given");
        if !is_pair(current) && !is_ac(current) {
            protected = current.clone();
        }
        current = child;
    }
    if &protected == term && (is_pair(term) || is_ac(term)) {
        None
    } else {
        Some(protected)
    }
}

/// `positions t`: every position in `t` (including the empty position at
/// the root). AC nesting follows the right-leaning binary interpretation.
pub fn positions<C, V>(t: &VTerm<C, V>) -> Vec<Position> {
    let mut out = Vec::new();
    visit_positions(t, PositionMode::BinaryAc, |_, path| {
        out.push(path.to_vec());
        true
    });
    out
}

#[derive(Clone, Copy)]
pub(crate) enum PositionMode {
    Nary,
    ReverseNary,
    BinaryAc,
}

/// Preorder position walk. The callback returns false to prune a matched
/// subtree. Only callers emitting a position copy the shared root-to-node path.
pub(crate) fn visit_positions<A>(
    t: &Term<A>,
    mode: PositionMode,
    mut visit: impl FnMut(&Term<A>, &[i64]) -> bool,
) {
    let mut current = t;
    let mut path = Vec::new();
    let mut pending = Vec::new();
    loop {
        if visit(current, &path)
            && let Term::App(sym, args) = current
            && !args.is_empty()
        {
            let binary_ac = matches!(mode, PositionMode::BinaryAc) && matches!(sym, FunSym::Ac(_));
            // A single child has no sibling continuation to save.
            if let [child] = &args[..] {
                if !binary_ac {
                    path.push(0);
                }
                current = child;
                continue;
            }
            pending.push((args.iter().enumerate(), path.len(), binary_ac, args.len()));
        }
        loop {
            let Some((children, depth, binary_ac, len)) = pending.last_mut() else {
                return;
            };
            let next = if matches!(mode, PositionMode::ReverseNary) {
                children.next_back()
            } else {
                children.next()
            };
            if let Some((index, child)) = next {
                path.truncate(*depth);
                if *binary_ac {
                    path.extend(std::iter::repeat_n(1, index));
                    if index + 1 != *len {
                        path.push(0);
                    }
                } else {
                    path.push(index as i64);
                }
                current = child;
                break;
            }
            pending.pop();
        }
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
        use crate::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
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

    /// The code addresses AC applications through the right-leaning binary
    /// encoding `*[t1,t2,t3] ≡ t1 * (t2 * t3)` (`atPosMay`, Positions.hs:47-59;
    /// `replacePos`, Positions.hs:76-80; `positions`, Positions.hs:109-122).
    /// `0` selects the head, and `1` selects the tail multiset.  The k-th of n
    /// arguments therefore sits at `1^k ++ [0]`.  The last one sits at `1^k`.
    /// No argument sits at `[k]`.  [`positions`], [`at_pos`] and
    /// [`replace_pos`] have to agree on this encoding, because a term's own
    /// position list is what indexes into that term.  `constant_positions`
    /// feeds these positions straight into `StRhs`, and `print_position`
    /// turns them into `AUTO_*` fact names.
    #[test]
    fn ac_positions_use_right_leaning_binary_encoding() {
        use crate::function_symbols::AcSym;
        use crate::term::f_app_ac;
        let a = msg_var("a", 0);
        let b = msg_var("b", 0);
        let c = msg_var("c", 0);
        let t: LNTerm = f_app_ac(AcSym::Mult, vec![a.clone(), b.clone(), c.clone()]);
        assert_eq!(
            positions(&t),
            vec![vec![], vec![0], vec![1, 0], vec![1, 1]],
            "the three AC arguments live at [0], [1,0], [1,1] — NOT [0], [1], [2]"
        );
        // `at_pos` reads the same encoding back.  It also reads the
        // intermediate tail multiset at [1].  That multiset is not an argument
        // of the flat term.
        assert_eq!(at_pos(&t, &[0]), Some(a.clone()));
        assert_eq!(
            at_pos(&t, &[1]),
            Some(f_app_ac(AcSym::Mult, vec![b.clone(), c.clone()]))
        );
        assert_eq!(at_pos(&t, &[1, 0]), Some(b.clone()));
        assert_eq!(at_pos(&t, &[1, 1]), Some(c));
        // DIVERGENCE (port-captured, not oracle-derived).  The AC arm in RS
        // ends in a catch-all `_ => None`.  HS `atPosMay` has no such arm.  It
        // falls through to the generic `FApp _ as (i:ps)` equation
        // (Positions.hs:55-58), so the oracle answers `Just c` here.  This
        // difference is unreachable in practice.  `positions` never emits a
        // bare index >= 2 for an AC node.
        assert_eq!(at_pos(&t, &[2]), None);
        // `replace_pos` descends the same encoding.  The AC smart constructor
        // then flattens the rebuilt tail into its parent again.
        let z = msg_var("z", 0);
        assert_eq!(
            replace_pos(&t, &z, &[1, 1]),
            Some(f_app_ac(AcSym::Mult, vec![a, b, z]))
        );
    }
}

#[cfg(test)]
#[path = "positions_reference.rs"]
mod reference;

#[cfg(test)]
mod depth_tests {
    use super::*;
    use crate::builtin::{hash, msg_var, pair};
    #[test]
    fn position_lifecycle_uses_small_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            let x = msg_var("x", 0);
            let y = msg_var("y", 0);
            let mut term = x.clone();
            for _ in 0..8192 {
                term = hash(term);
            }
            let path = vec![0; 8192];
            assert_eq!(at_pos(&term, &path), Some(x.clone()));
            assert_eq!(deepest_prot_subterm(&term, &path), Some(hash(x.clone())));
            assert_eq!(
                find_pos(&x, &pair(term.clone(), term.clone())),
                Some(vec![
                    [vec![1], path.clone()].concat(),
                    [vec![0], path.clone()].concat()
                ])
            );
            let replaced = replace_pos(&term, &y, &path).unwrap();
            assert_eq!(at_pos(&replaced, &path), Some(y));
            let invalid = [path, vec![0]].concat();
            assert!(at_pos(&term, &invalid).is_none());
            assert!(replace_pos(&term, &x, &invalid).is_none());
            assert!(std::panic::catch_unwind(|| deepest_prot_subterm(&term, &invalid)).is_err());
            // Enumerating every prefix inherently emits quadratic output.
            let mut smaller = x;
            for _ in 0..512 {
                smaller = hash(smaller);
            }
            let all = positions(&smaller);
            assert_eq!(all.len(), 513);
            assert!(all
                .iter()
                .enumerate()
                .all(|(depth, path)| path == &vec![0; depth]));
        });
    }

    #[test]
    fn synthetic_ac_tails_use_small_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            use crate::function_symbols::AcSym;
            let x = msg_var("x", 0);
            let y = msg_var("y", 0);
            let term = crate::term::f_app_ac(AcSym::Mult, vec![x.clone(); 1024]);
            let path = vec![1; 1023];
            assert_eq!(at_pos(&term, &path), Some(x));
            let replaced = replace_pos(&term, &y, &path).unwrap();
            assert_eq!(at_pos(&replaced, &path), Some(y));
            assert!(at_pos(&term, &[path, vec![1]].concat()).is_none());
        });
    }

    #[test]
    fn position_algorithms_match_independent_reference() {
        use crate::function_symbols::{AcSym, CSym};
        let x = msg_var("x", 0);
        let mut terms = vec![x.clone(), msg_var("y", 0)];
        for depth in 0..3 {
            let a = terms.last().unwrap().clone();
            for sym in [
                FunSym::NoEq(crate::builtin::hash_sym()),
                FunSym::List,
                FunSym::Ac(AcSym::Mult),
                FunSym::C(CSym::EMap),
            ] {
                // Include noncanonical arities: normalizing a synthetic AC
                // tail can change its shape, so direct slice indexing is wrong.
                for args in [
                    vec![],
                    vec![a.clone()],
                    vec![x.clone(), a.clone()],
                    vec![a.clone(), x.clone(), terms[depth].clone()],
                ] {
                    terms.push(Term::App(sym, args.into()));
                }
            }
        }
        for term in &terms {
            assert_eq!(positions(term), reference::positions(term));
            for needle in &terms {
                assert_eq!(find_pos(needle, term), reference::find_pos(needle, term));
            }
            let mut paths = positions(term);
            paths.extend([
                vec![-1],
                vec![99],
                vec![0, 99],
                vec![1],
                vec![1, 1],
                vec![1, 0, 0],
            ]);
            for path in paths {
                assert_eq!(at_pos(term, &path), reference::at_pos(term, &path));
                assert_eq!(
                    replace_pos(term, &x, &path),
                    reference::replace_pos(term, &x, &path)
                );
            }
            // n-ary paths are deliberately separate from binary AC positions.
            for needle in &terms {
                for path in find_pos(needle, term).into_iter().flatten() {
                    assert_eq!(
                        deepest_prot_subterm(term, &path),
                        reference::deepest_prot_subterm(term, &path)
                    );
                }
            }
        }
    }
}
