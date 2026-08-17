// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.SubtermRule` from `lib/term/src/Term/SubtermRule.hs`.

use crate::lterm::{frees, LNTerm};
use crate::positions::{positions, Position};
use crate::rewriting::RRule;
use crate::term::Term;

/// Right-hand side of a context subterm rewrite rule.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StRhs {
    pub positions: Vec<Position>,
    pub term: LNTerm,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CtxtStRule {
    pub lhs: LNTerm,
    pub rhs: StRhs,
}

impl CtxtStRule {
    pub fn new(lhs: LNTerm, rhs: StRhs) -> Self {
        CtxtStRule { lhs, rhs }
    }

    pub fn to_rrule(&self) -> RRule<LNTerm> {
        RRule::new(self.lhs.clone(), self.rhs.term.clone())
    }
}

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

/// `subterms args [] 1` (SubtermRule.hs:59-65, called at :69): for each top-level arg
/// `t`, find the positions where `t` occurs as a subterm of a SIBLING
/// arg, each prefixed with that sibling's top-level index.  HS visits the
/// remaining siblings (`zip [i..] ts`) before the already-processed ones
/// (`zip [0..] done`); we preserve that order.
fn subterms(args: &[LNTerm]) -> Vec<Position> {
    let mut out = Vec::new();
    for (k, t) in args.iter().enumerate() {
        // Remaining siblings first, at their true indices k+1, k+2, …
        for (off, y) in args[k + 1..].iter().enumerate() {
            let x = (k + 1 + off) as i64;
            for mut p in find_subterm(y, t) {
                let mut full = Vec::with_capacity(1 + p.len());
                full.push(x);
                full.append(&mut p);
                out.push(full);
            }
        }
        // Then the already-processed siblings, at indices 0 .. k-1.
        for (x, y) in args[..k].iter().enumerate() {
            for mut p in find_subterm(y, t) {
                let mut full = Vec::with_capacity(1 + p.len());
                full.push(x as i64);
                full.append(&mut p);
                out.push(full);
            }
        }
    }
    out
}

/// `constantPositions` (SubtermRule.hs:67-71): for an `FApp _ args` LHS,
/// the sibling-subterm positions of its args; if the LHS contains a
/// private function symbol, or no sibling-subterm is found, every
/// position of the LHS.
fn constant_positions(lhs: &LNTerm) -> Vec<Position> {
    match lhs {
        Term::App(_, args) => {
            if crate::lterm::contains_private(lhs) {
                positions(lhs)
            } else {
                let pos = subterms(args);
                if pos.is_empty() {
                    positions(lhs)
                } else {
                    pos
                }
            }
        }
        // Sole caller `rrule_to_ctxt_st_rule` rejects non-`App` LHS terms
        // before reaching here (the deliberate-divergence guard documented
        // there), so a `Lit` cannot arrive.
        _ => unreachable!("constant_positions: non-App LHS is rejected by rrule_to_ctxt_st_rule"),
    }
}

/// `rRuleToCtxtStRule`: convert an `RRule` to a `CtxtStRule` if possible.
///
/// DELIBERATE DIVERGENCE (documented upstream bug): on a ground-RHS equation
/// whose LHS is a bare literal (`equations: x = c`), HS aborts the whole run —
/// `constantPositions` (SubtermRule.hs:67-71) has only an `FApp` clause under
/// `-fno-warn-incomplete-patterns`, and the bottom is forced when the rule
/// enters the `stRules` Set (Term/Maude/Signature.hs:181-183).  For the
/// NON-ground sibling (`x = h(x)`) HS instead fails cleanly with "Not a correct
/// equation: …" (Theory/Text/Parser/Signature.hs:247-249).  The port answers
/// `None` here, routing the ground case into that same clean failure.
pub fn rrule_to_ctxt_st_rule(rule: &RRule<LNTerm>) -> Option<CtxtStRule> {
    if frees(&rule.rhs).is_empty() {
        if !matches!(rule.lhs, Term::App(_, _)) {
            return None;
        }
        // Pure right-hand-side: the positions are the LHS's constant
        // positions — HS `constantPositions` (a sibling-subterm search),
        // NOT all non-variable positions.
        return Some(CtxtStRule::new(
            rule.lhs.clone(),
            StRhs {
                positions: constant_positions(&rule.lhs),
                term: rule.rhs.clone(),
            },
        ));
    }
    let positions = find_all_subterms(&rule.lhs, &rule.rhs)?;
    // HS (SubtermRule.hs:54-57) matches `case sbtms of []:_ -> Nothing; [] ->
    // Nothing; pos -> Just`. The `[]:_` arm rejects ONLY when the empty
    // position is at the HEAD of the list; an empty position later in the
    // list does not reject. The `is_empty()` guard above covers HS's `[]` arm,
    // so `positions[0]` is in bounds here.
    if positions.is_empty() || positions[0].is_empty() {
        return None;
    }
    Some(CtxtStRule::new(
        rule.lhs.clone(),
        StRhs {
            positions,
            term: rule.rhs.clone(),
        },
    ))
}

/// `isSubtermConvergentCtxtRule`: RHS is constant or appears as a subterm
/// of LHS.
pub fn is_subterm_convergent(rule: &CtxtStRule) -> bool {
    let rhs = &rule.rhs.term;
    if frees(rhs).is_empty() {
        return true;
    }
    !find_subterm(&rule.lhs, rhs).is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{msg_var, pair};

    #[test]
    fn find_subterm_finds_all_occurrences() {
        let needle = msg_var("x", 0);
        let inner = pair(needle.clone(), msg_var("y", 0));
        let outer = pair(needle.clone(), inner);
        // The order is left-to-right and outermost-first.  The direct child at
        // [0] comes before the nested occurrence at [1,0].  HS
        // `findSubtermPrime` builds each position with a cons of the indices.
        // It then applies `reverse` at the hit.  The recorded position
        // therefore reads root→leaf.
        assert_eq!(find_subterm(&outer, &needle), vec![vec![0i64], vec![1, 0]]);
    }

    /// A ground RHS routes through `constantPositions` (SubtermRule.hs:67-71).
    /// No argument occurs inside a sibling here.  `subterms` is therefore
    /// empty, and HS falls back to `positions lhs`.  That is every position of
    /// the LHS, and it includes the variable positions.
    #[test]
    fn rrule_with_constant_rhs_falls_back_to_all_lhs_positions() {
        use crate::builtin::true_const;
        use crate::lterm::Name;
        use crate::vterm::Lit;
        let lhs = pair(msg_var("x", 0), msg_var("y", 0));
        let rhs: LNTerm = true_const::<Lit<Name, _>>();
        let rule = RRule::new(lhs, rhs);
        let ctxt = rrule_to_ctxt_st_rule(&rule).unwrap();
        assert_eq!(
            ctxt.rhs.positions,
            vec![Vec::<i64>::new(), vec![0], vec![1]],
            "no sibling-subterm found → `positions lhs`, not `positionsNonVar`"
        );
    }

    /// HS `subterms` (SubtermRule.hs:59-65, called at :69) looks at each
    /// top-level argument in turn.  For that argument it searches the siblings
    /// that it has not processed yet first (`zip [i..] ts`).  It searches the
    /// already-processed siblings only after that (`zip [0..] done`).  The two
    /// halves carry different index bases.  The order of the concatenation is
    /// the stored `StRhs` position order, which `strule_rewrites` walks.
    #[test]
    fn constant_positions_visit_remaining_siblings_before_processed_ones() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        use crate::term::f_app_no_eq;
        let h = NoEqSym::new(
            b"h".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let f = NoEqSym::new(
            b"f".to_vec(),
            3,
            Privacy::Public,
            Constructability::Constructor,
        );
        let c = NoEqSym::new(
            b"c".to_vec(),
            0,
            Privacy::Public,
            Constructability::Constructor,
        );
        let x = msg_var("x", 0);
        let hx: LNTerm = f_app_no_eq(h, vec![x.clone()]);
        // f(h(x), x, h(x)) = c
        let lhs: LNTerm = f_app_no_eq(f, vec![hx.clone(), x, hx]);
        let rule = RRule::new(lhs, f_app_no_eq(c, vec![]));
        let ctxt = rrule_to_ctxt_st_rule(&rule).unwrap();
        assert_eq!(
            ctxt.rhs.positions,
            vec![
                vec![2i64], // arg 0's h(x) inside the remaining sibling 2
                vec![2, 0], // arg 1's x inside the remaining sibling 2 …
                vec![0, 0], // … before the same x inside the processed 0
                vec![0],    // arg 2's h(x) inside the processed sibling 0
            ],
            "remaining siblings are visited before the already-processed ones"
        );
    }

    /// HS `rRuleToCtxtStRule` (SubtermRule.hs:54-57) rejects via the `[]:_`
    /// arm only when the empty position is at the HEAD of the position list.
    /// For `h(x) = f(x, h(x))`, `findAllSubterms` yields `[[0], []]`: the
    /// empty position is SECOND, so HS keeps the rule (`pos -> Just`).
    ///
    /// Verified against the real HS prover (v1.13.0): loading this equation
    /// with `--prove` accepts it (it appears in the loaded theory with a
    /// non-subterm-convergence wellformedness warning), it is NOT rejected
    /// with "Not a correct equation".
    #[test]
    fn empty_position_only_rejects_at_head() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        use crate::term::f_app_no_eq;
        let h_sym = NoEqSym::new(
            b"h".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let f_sym = NoEqSym::new(
            b"f".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        let x = msg_var("x", 0);
        let lhs: LNTerm = f_app_no_eq(h_sym, vec![x.clone()]); // h(x)
        let rhs: LNTerm = f_app_no_eq(f_sym, vec![x.clone(), lhs.clone()]); // f(x, h(x))
        let rule = RRule::new(lhs, rhs);
        let ctxt = rrule_to_ctxt_st_rule(&rule).expect("must not be rejected");
        // `x` at position [0] inside arg 0, then the whole `h(x)` from arg 1.
        assert_eq!(ctxt.rhs.positions, vec![vec![0i64], Vec::<i64>::new()]);
    }

    /// A literal LHS with a ground RHS (`equations: x = c`) is rejected as
    /// not-a-subterm-rule, which elaboration reports as "Not a correct
    /// equation" — the same clean failure both engines produce for the
    /// non-ground sibling `x = h(x)` ("Not a correct equation: RRule x h(x)"
    /// from the pinned oracle).  HS instead ABORTS on the ground case
    /// (non-exhaustive `constantPositions`, SubtermRule.hs:67-71 under
    /// `-fno-warn-incomplete-patterns`); the port deliberately diverges from
    /// that documented upstream bug.
    #[test]
    fn literal_lhs_ground_equation_is_rejected_not_crashed() {
        use crate::function_symbols::{Constructability, NoEqSym, Privacy};
        use crate::term::f_app_no_eq;
        let c_sym = NoEqSym::new(
            b"c".to_vec(),
            0,
            Privacy::Public,
            Constructability::Constructor,
        );
        let lhs = msg_var("x", 0); // literal (Var) LHS
        let rhs: LNTerm = f_app_no_eq(c_sym, vec![]); // ground RHS `c`
        let rule = RRule::new(lhs, rhs);
        assert!(rrule_to_ctxt_st_rule(&rule).is_none());
    }
}
