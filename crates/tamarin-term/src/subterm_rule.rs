// Currently GPL 3.0 until granted permission by the following authors:
//   Mathias-AURAND, beschmi, jdreier, cdumenil, meiersi
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Builtin/Signature.hs,
//   lib/term/src/Term/Maude/Signature.hs,
//   lib/term/src/Term/SubtermRule.hs

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
    pub fn new(lhs: LNTerm, rhs: StRhs) -> Self { CtxtStRule { lhs, rhs } }

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
            if !direct.is_empty() { return Some(direct); }
            let mut out = Vec::new();
            for sub in args.iter() {
                let parts = find_all_subterms(l, sub)?;
                out.extend(parts);
            }
            Some(out)
        }
        Term::Lit(Lit::Var(_)) => {
            if direct.is_empty() { None } else { Some(direct) }
        }
        Term::Lit(Lit::Con(_)) => None,
    }
}

/// `subterms args [] 1` (SubtermRule.hs:57-63, called at :67): for each top-level arg
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

/// `constantPositions` (SubtermRule.hs:56-69): for an `FApp _ args` LHS,
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
                if pos.is_empty() { positions(lhs) } else { pos }
            }
        }
        // HS `constantPositions` (SubtermRule.hs:65-69) has ONLY the
        // `FApp _ args` clause; line 2 sets `-fno-warn-incomplete-patterns`.
        // A non-FApp (Lit) LHS — e.g. a ground equation `x = c` — therefore
        // hits a non-exhaustive-pattern bottom in HS. The thunk is forced when
        // the rule is inserted into the `stRules` Set (Signature.hs:162-164,
        // via the `Ord` instance over the `[Position]` field), aborting the
        // run with:
        //   src/Term/SubtermRule.hs:(65,5)-(69,47): Non-exhaustive patterns
        //   in function constantPositions
        // We panic here to mirror that abort rather than silently accepting
        // the rule. Unreachable on real input (no equation reaching here has
        // a literal LHS in practice).
        _ => panic!(
            "src/Term/SubtermRule.hs:(65,5)-(69,47): Non-exhaustive patterns in function constantPositions"
        ),
    }
}

/// `rRuleToCtxtStRule`: convert an `RRule` to a `CtxtStRule` if possible.
pub fn rrule_to_ctxt_st_rule(rule: &RRule<LNTerm>) -> Option<CtxtStRule> {
    if frees(&rule.rhs).is_empty() {
        // Pure right-hand-side: the positions are the LHS's constant
        // positions — HS `constantPositions` (a sibling-subterm search),
        // NOT all non-variable positions.
        return Some(CtxtStRule::new(
            rule.lhs.clone(),
            StRhs { positions: constant_positions(&rule.lhs), term: rule.rhs.clone() },
        ));
    }
    let positions = find_all_subterms(&rule.lhs, &rule.rhs)?;
    // HS (SubtermRule.hs:52-55) matches `case sbtms of []:_ -> Nothing; [] ->
    // Nothing; pos -> Just`. The `[]:_` arm rejects ONLY when the empty
    // position is at the HEAD of the list; an empty position later in the
    // list does not reject. The `is_empty()` guard above covers HS's `[]` arm,
    // so `positions[0]` is in bounds here.
    if positions.is_empty() || positions[0].is_empty() { return None; }
    Some(CtxtStRule::new(
        rule.lhs.clone(),
        StRhs { positions, term: rule.rhs.clone() },
    ))
}

/// `isSubtermConvergentCtxtRule`: RHS is constant or appears as a subterm
/// of LHS.
pub fn is_subterm_convergent(rule: &CtxtStRule) -> bool {
    let rhs = &rule.rhs.term;
    if frees(rhs).is_empty() { return true; }
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
        let positions = find_subterm(&outer, &needle);
        assert_eq!(positions.len(), 2);
    }

    #[test]
    fn rrule_with_constant_rhs() {
        use crate::builtin::true_const;
        use crate::lterm::Name;
        use crate::vterm::Lit;
        let lhs = pair(msg_var("x", 0), msg_var("y", 0));
        let rhs: LNTerm = true_const::<Lit<Name, _>>();
        let rule = RRule::new(lhs, rhs);
        let ctxt = rrule_to_ctxt_st_rule(&rule).unwrap();
        assert!(!ctxt.rhs.positions.is_empty());
    }

    /// HS `rRuleToCtxtStRule` (SubtermRule.hs:52-55) rejects via the `[]:_`
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
        let lhs: LNTerm = f_app_no_eq(h_sym.clone(), vec![x.clone()]); // h(x)
        let rhs: LNTerm = f_app_no_eq(f_sym, vec![x.clone(), lhs.clone()]); // f(x, h(x))
        let rule = RRule::new(lhs, rhs);
        let ctxt = rrule_to_ctxt_st_rule(&rule).expect("must not be rejected");
        // `x` at position [0] inside arg 0, then the whole `h(x)` from arg 1.
        assert_eq!(ctxt.rhs.positions, vec![vec![0i64], Vec::<i64>::new()]);
    }

    /// HS `constantPositions` (SubtermRule.hs:65-69) has only the `FApp`
    /// clause under `-fno-warn-incomplete-patterns`; a literal LHS produces a
    /// non-exhaustive-pattern bottom. Verified against the real HS prover:
    /// loading `x = c` (with `c/0`) aborts with
    ///   src/Term/SubtermRule.hs:(65,5)-(69,47): Non-exhaustive patterns in
    ///   function constantPositions
    /// We mirror that abort with a panic.
    #[test]
    #[should_panic(expected = "Non-exhaustive patterns in function constantPositions")]
    fn literal_lhs_ground_equation_panics() {
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
        let _ = rrule_to_ctxt_st_rule(&rule);
    }
}
