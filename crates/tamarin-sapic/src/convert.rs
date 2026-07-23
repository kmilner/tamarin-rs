// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, beschmi, charlie-j, jdreier, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Basetranslation.hs,
//   lib/term/src/Term/Maude/Process.hs,
//   lib/theory/src/Theory/Sapic/Pattern.hs,
//   lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Text/Parser/Sapic.hs

//! Parser-AST → theory-AST process converter.
//!
//! Maps `tamarin_parser::ast::Process` (the surface syntax tree) into
//! `tamarin_theory::sapic::PlainProcess` (the HS-faithful `Process<ann, v>`
//! working representation):
//!
//!   - `Null`
//!   - `Action New / Event / ChOut / ChIn` (incl. named/private channels)
//!   - state (`insert` / `delete` / `lookup` / `lock` / `unlock`)
//!   - `Action Rep` (replication `!P`)
//!   - `Comb Parallel | NDC | CondEq | Cond | Let`
//!     (`P|Q`, `P+Q`, `if t1 = t2 then P else Q`, `if <formula> then`, `let`)
//!
//! There is no single HS function this mirrors: in HS the parser builds the
//! `PlainProcess` directly (`Theory.Text.Parser.Sapic.process`), whereas the
//! Rust parser produces its own `ast::Process` first.  The term/fact payloads
//! reuse the shared elaborators `term_to_sapic_term` / `fact_to_sapic_fact`
//! (elaborate.rs), so the term universe matches the protocol-rule path.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_term::lterm::{LSort, LVar};
use tamarin_theory::elaborate::{fact_to_sapic_fact, term_to_sapic_term};
use tamarin_theory::sapic::{
    PlainProcess, Process, ProcessCombinator, ProcessParsedAnnotation, SapicAction, SapicLVar,
};

/// Error returned when a SAPIC process cannot be converted (e.g. an
/// unconvertible term/fact, or a process call reached without a definition map).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvertError {
    pub message: String,
}

impl ConvertError {
    pub(crate) fn new(s: impl Into<String>) -> Self {
        ConvertError { message: s.into() }
    }
}

pub(crate) fn sort_of_hint(s: &p::SortHint) -> LSort {
    match s {
        p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => LSort::Fresh,
        p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => LSort::Pub,
        p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => LSort::Node,
        p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => LSort::Nat,
        p::SortHint::Msg | p::SortHint::Suffix(p::SuffixSort::Msg) | p::SortHint::Untagged => {
            LSort::Msg
        }
    }
}

/// `LSort` → parser `SortHint` (the inverse of [`sort_of_hint`]; always maps to
/// the plain, non-`Suffix` hint).
pub(crate) fn lsort_to_sort_hint(s: LSort) -> p::SortHint {
    match s {
        LSort::Fresh => p::SortHint::Fresh,
        LSort::Pub => p::SortHint::Pub,
        LSort::Node => p::SortHint::Node,
        LSort::Nat => p::SortHint::Nat,
        LSort::Msg => p::SortHint::Msg,
    }
}

/// `LVar` → parser `VarSpec` (name/idx/sort carried over, no SAPIC type).
pub(crate) fn lvar_to_varspec(v: &LVar) -> p::VarSpec {
    p::VarSpec {
        name: v.name.to_string(),
        idx: v.idx,
        sort: lsort_to_sort_hint(v.sort),
        typ: None,
    }
}

/// `VarSpec` → `SapicLVar` (carrying the SAPIC `name:type` annotation).
pub(crate) fn varspec_to_sapic(v: &p::VarSpec) -> SapicLVar {
    SapicLVar::new(
        LVar::new(v.name.clone(), sort_of_hint(&v.sort), v.idx),
        v.typ.clone(),
    )
}

/// Rebuild a parser-AST formula, mapping `f` over every FREE `Var` leaf.
///
/// Quantifier-bound names are tracked in a `bound` stack (respecting shadowing)
/// and their occurrences are left untouched; for a free `Var`, `f(varspec,
/// bound)` returns `Some(term)` to replace the leaf or `None` to keep it
/// unchanged.  Shared traversal behind `let_destructors::subst_cond_formula`
/// and `typing::rename_cond_formula`.
pub(crate) fn map_free_terms(
    formula: &p::Formula,
    f: &mut dyn FnMut(&p::VarSpec, &[String]) -> Option<p::Term>,
) -> p::Formula {
    fn rt(
        bound: &[String],
        f: &mut dyn FnMut(&p::VarSpec, &[String]) -> Option<p::Term>,
        t: &p::Term,
    ) -> p::Term {
        match t {
            p::Term::Var(v) => {
                if bound.iter().any(|n| n == &v.name) {
                    return t.clone();
                }
                f(v, bound).unwrap_or_else(|| t.clone())
            }
            p::Term::App(n, args) => {
                p::Term::App(n.clone(), args.iter().map(|a| rt(bound, f, a)).collect())
            }
            p::Term::Pair(items) => p::Term::Pair(items.iter().map(|a| rt(bound, f, a)).collect()),
            p::Term::AlgApp(n, a, b) => p::Term::AlgApp(
                n.clone(),
                Box::new(rt(bound, f, a)),
                Box::new(rt(bound, f, b)),
            ),
            p::Term::Diff(a, b) => {
                p::Term::Diff(Box::new(rt(bound, f, a)), Box::new(rt(bound, f, b)))
            }
            p::Term::BinOp(op, a, b) => {
                p::Term::BinOp(*op, Box::new(rt(bound, f, a)), Box::new(rt(bound, f, b)))
            }
            p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(rt(bound, f, inner))),
            other => other.clone(),
        }
    }
    fn ra(
        bound: &[String],
        f: &mut dyn FnMut(&p::VarSpec, &[String]) -> Option<p::Term>,
        a: &p::Atom,
    ) -> p::Atom {
        use p::Atom::*;
        match a {
            Eq(l, r) => Eq(rt(bound, f, l), rt(bound, f, r)),
            Less(l, r) => Less(rt(bound, f, l), rt(bound, f, r)),
            LessMset(l, r) => LessMset(rt(bound, f, l), rt(bound, f, r)),
            Subterm(l, r) => Subterm(rt(bound, f, l), rt(bound, f, r)),
            Action(fa, t) => Action(
                p::Fact {
                    persistent: fa.persistent,
                    name: fa.name.clone(),
                    args: fa.args.iter().map(|x| rt(bound, f, x)).collect(),
                    annotations: fa.annotations.clone(),
                },
                rt(bound, f, t),
            ),
            Last(t) => Last(rt(bound, f, t)),
            Pred(fa) => Pred(p::Fact {
                persistent: fa.persistent,
                name: fa.name.clone(),
                args: fa.args.iter().map(|x| rt(bound, f, x)).collect(),
                annotations: fa.annotations.clone(),
            }),
        }
    }
    fn rf(
        bound: &mut Vec<String>,
        f: &mut dyn FnMut(&p::VarSpec, &[String]) -> Option<p::Term>,
        formula: &p::Formula,
    ) -> p::Formula {
        use p::Formula::*;
        match formula {
            True => True,
            False => False,
            Atom(a) => Atom(ra(bound, f, a)),
            Not(g) => Not(Box::new(rf(bound, f, g))),
            And(a, b) => And(Box::new(rf(bound, f, a)), Box::new(rf(bound, f, b))),
            Or(a, b) => Or(Box::new(rf(bound, f, a)), Box::new(rf(bound, f, b))),
            Implies(a, b) => Implies(Box::new(rf(bound, f, a)), Box::new(rf(bound, f, b))),
            Iff(a, b) => Iff(Box::new(rf(bound, f, a)), Box::new(rf(bound, f, b))),
            Forall(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                let r = Forall(vs.clone(), Box::new(rf(bound, f, body)));
                bound.truncate(saved);
                r
            }
            Exists(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                let r = Exists(vs.clone(), Box::new(rf(bound, f, body)));
                bound.truncate(saved);
                r
            }
        }
    }
    let mut bound = Vec::new();
    rf(&mut bound, f, formula)
}

/// Visit every FREE `Var` leaf of a parser-AST formula, calling `f(varspec,
/// bound)` for each (quantifier-bound occurrences are skipped, tracking
/// shadowing via the `bound` stack).  The traversal order is the depth-first,
/// left-to-right order shared by `base_translation::formula_free_lvars` and
/// `typing::cond_formula_free_lvars`.
pub(crate) fn fold_free_vars(formula: &p::Formula, f: &mut dyn FnMut(&p::VarSpec, &[String])) {
    fn ct(bound: &[String], f: &mut dyn FnMut(&p::VarSpec, &[String]), t: &p::Term) {
        match t {
            p::Term::Var(v) if !bound.iter().any(|n| n == &v.name) => f(v, bound),
            p::Term::App(_, args) | p::Term::Pair(args) => {
                for a in args {
                    ct(bound, f, a);
                }
            }
            p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
                ct(bound, f, a);
                ct(bound, f, b);
            }
            p::Term::PatMatch(inner) => ct(bound, f, inner),
            _ => {}
        }
    }
    fn ca(bound: &[String], f: &mut dyn FnMut(&p::VarSpec, &[String]), a: &p::Atom) {
        use p::Atom::*;
        match a {
            Eq(l, r) | Less(l, r) | LessMset(l, r) | Subterm(l, r) => {
                ct(bound, f, l);
                ct(bound, f, r);
            }
            Action(fa, t) => {
                for arg in &fa.args {
                    ct(bound, f, arg);
                }
                ct(bound, f, t);
            }
            Last(t) => ct(bound, f, t),
            Pred(fa) => {
                for arg in &fa.args {
                    ct(bound, f, arg);
                }
            }
        }
    }
    fn cf(
        bound: &mut Vec<String>,
        f: &mut dyn FnMut(&p::VarSpec, &[String]),
        formula: &p::Formula,
    ) {
        use p::Formula::*;
        match formula {
            True | False => {}
            Atom(a) => ca(bound, f, a),
            Not(g) => cf(bound, f, g),
            And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
                cf(bound, f, a);
                cf(bound, f, b);
            }
            Forall(vs, body) | Exists(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                cf(bound, f, body);
                bound.truncate(saved);
            }
        }
    }
    let mut bound = Vec::new();
    cf(&mut bound, f, formula);
}

fn term(t: &p::Term) -> Result<tamarin_theory::sapic::SapicTerm, ConvertError> {
    term_to_sapic_term(t)
        .ok_or_else(|| ConvertError::new("could not convert SAPIC term (pattern term?)"))
}

/// Public alias of [`term`] for the inlining pass (process-call arguments).
pub(crate) fn convert_term(t: &p::Term) -> Result<tamarin_theory::sapic::SapicTerm, ConvertError> {
    term(t)
}

fn fact(f: &p::Fact) -> Result<tamarin_theory::sapic::SapicLNFact, ConvertError> {
    fact_to_sapic_fact(f).map_err(|e| ConvertError::new(e.message))
}

/// Public alias of [`action`] for the inlining pass.
pub(crate) fn convert_action(a: &p::SapicAction) -> Result<SapicAction<SapicLVar>, ConvertError> {
    action(a)
}

/// Public alias of [`combinator`] for the inlining pass.
pub(crate) fn convert_combinator(
    c: &p::ProcessComb,
) -> Result<ProcessCombinator<SapicLVar>, ConvertError> {
    combinator(c)
}

/// Convert a parser action into a theory `SapicAction<SapicLVar>`.
fn action(a: &p::SapicAction) -> Result<SapicAction<SapicLVar>, ConvertError> {
    match a {
        p::SapicAction::New(v) => Ok(SapicAction::New(varspec_to_sapic(v))),
        p::SapicAction::Event(f) => Ok(SapicAction::Event(fact(f)?)),
        p::SapicAction::ChOut { chan, msg } => Ok(SapicAction::ChOut {
            chan: chan.as_ref().map(term).transpose()?,
            msg: term(msg)?,
        }),
        p::SapicAction::ChIn { chan, msg } => {
            // The surface `in(c, pat)` parser stores the pattern with `=t`
            // (`PatMatch`) match markers.  HS `ChIn maybeChannel (unpattern pt)
            // (extractMatchingVariables pt)` (Parser/Sapic.hs:84-162, see line 114) unpatterns the
            // message term and splits the matched variables out into `match_vars`.
            // We reuse the same `unpattern`/`extractMatchingVariables` helper used
            // for `let` patterns.
            let (msg_unpat, match_vars) = convert_let_pattern(msg)?;
            Ok(SapicAction::ChIn {
                chan: chan.as_ref().map(term).transpose()?,
                msg: msg_unpat,
                match_vars,
            })
        }
        // Mutable state: `insert t1 v` / `delete t`.  These map to the
        // theory `SapicAction::{Insert,Delete}` (Process.hs:72-73), translated by
        // `baseTransAction` Insert/Delete (Basetranslation.hs:177-184).
        p::SapicAction::Insert(t1, t2) => Ok(SapicAction::Insert(term(t1)?, term(t2)?)),
        p::SapicAction::Delete(t) => Ok(SapicAction::Delete(term(t)?)),
        // Locks: `lock t` / `unlock t` → theory `SapicAction::{Lock,Unlock}`
        // (Process.hs:74-75), annotated by `Sapic.Locks.annotateLocks` and
        // translated by `baseTransAction` Lock/Unlock (Basetranslation.hs:185-194).
        p::SapicAction::Lock(t) => Ok(SapicAction::Lock(term(t)?)),
        p::SapicAction::Unlock(t) => Ok(SapicAction::Unlock(term(t)?)),
        // Embedded MSR rule `[l]--[a]->[r]` (optionally with `restricting φ`).
        // HS (Parser/Sapic.hs:154-160):
        //   let matchVars = foldMap (foldMap extractMatchingVariables) l
        //   let f = fmap (fmap unpattern); g = fmap (fmap unpatternVar)
        //   if validMSR S.empty (l,a,r) then MSR (f l) (f a) (f r) (g phi) matchVars
        // i.e. match-vars come from the PREMISES only; every fact row is
        // `unpattern`ed (the `=v` markers stripped) and the embedded restriction
        // formulas carry through (parser-AST, like `Cond`).
        p::SapicAction::Msr {
            prems,
            acts,
            concs,
            restrictions,
        } => {
            let mut match_vars: BTreeSet<SapicLVar> = BTreeSet::new();
            // Premises: unpattern + collect match-vars.
            let prems_c = prems
                .iter()
                .map(|f| fact_unpattern(f, Some(&mut match_vars)))
                .collect::<Result<Vec<_>, _>>()?;
            // Actions / conclusions: unpattern only (no match-var collection).
            let acts_c = acts
                .iter()
                .map(|f| fact_unpattern(f, None))
                .collect::<Result<Vec<_>, _>>()?;
            let concs_c = concs
                .iter()
                .map(|f| fact_unpattern(f, None))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SapicAction::Msr {
                prems: prems_c,
                acts: acts_c,
                concs: concs_c,
                rest: restrictions.clone(),
                match_vars,
            })
        }
    }
}

/// Convert a fact whose argument terms may carry `=v` (`PatMatch`) markers
/// (HS `fmap (fmap unpattern)` over a fact; `extractMatchingVariables` over its
/// terms).  Strips every match marker and — when `match_vars` is `Some` —
/// records each matched variable.  Mirrors `convert_let_pattern` but for a fact.
fn fact_unpattern(
    f: &p::Fact,
    mut match_vars: Option<&mut BTreeSet<SapicLVar>>,
) -> Result<tamarin_theory::sapic::SapicLNFact, ConvertError> {
    let mut sink = BTreeSet::new();
    let args: Vec<p::Term> = f
        .args
        .iter()
        .map(|t| strip_pat_match(t, match_vars.as_deref_mut().unwrap_or(&mut sink)))
        .collect();
    let f2 = p::Fact { args, ..f.clone() };
    fact(&f2)
}

/// Convert a parser combinator into a theory `ProcessCombinator<SapicLVar>`.
///
/// Mirrors the SAPIC parser's combinator construction
/// (`Theory.Text.Parser.Sapic`): `Parallel`/`Ndc` are nullary; `if t1 = t2`
/// becomes `CondEq t1 t2`; `if frml` becomes `Cond frml`; `lookup`/`let`
/// become `Lookup`/`Let`.
fn combinator(c: &p::ProcessComb) -> Result<ProcessCombinator<SapicLVar>, ConvertError> {
    match c {
        p::ProcessComb::Parallel => Ok(ProcessCombinator::Parallel),
        p::ProcessComb::Ndc => Ok(ProcessCombinator::Ndc),
        p::ProcessComb::Cond(p::Condition::Eq(t1, t2)) => {
            Ok(ProcessCombinator::CondEq(term(t1)?, term(t2)?))
        }
        // `if <formula> then .. else ..`.  HS `Cond (SapicNFormula v)`;
        // the RS `Cond` carries the un-expanded parser-AST formula directly (see
        // `ProcessCombinator::Cond` doc).  Predicate atoms inside the formula are
        // expanded later, by `lift_rule_restrictions` over the embedded
        // `_restrict` (HS `liftedExpandFormula`), so we keep it un-expanded here.
        p::ProcessComb::Cond(p::Condition::Formula(f)) => Ok(ProcessCombinator::Cond(f.clone())),
        // `lookup t as v in .. else ..`.  HS `Lookup (SapicNTerm v) v`
        // (Process.hs:95).
        p::ProcessComb::Lookup(t, v) => {
            Ok(ProcessCombinator::Lookup(term(t)?, varspec_to_sapic(v)))
        }
        // `let pat = value in P [else Q]`.  HS
        // `ProcessComb (Let (unpattern t1) t2 (extractMatchingVariables t1))`
        // (Sapic.hs:268-269).  The parser-AST pattern `pat` may contain
        // `=t` (`PatMatch`) match markers; we split them out into `match_vars`
        // and `unpattern` the rest into the `left` term.
        p::ProcessComb::Let { pat, value } => {
            let (left, match_vars) = convert_let_pattern(pat)?;
            let right = term(value)?;
            Ok(ProcessCombinator::Let {
                left,
                right,
                match_vars,
            })
        }
    }
}

/// Convert a `let` pattern term (HS `unpattern` + `extractMatchingVariables`,
/// Pattern.hs:55-96).  Returns the `unpattern`ed SAPIC term (with every `=v`
/// match marker stripped to a plain `v`) plus the set of match-marked
/// variables.  HS `extractMatchingVariables` collects every `PatternMatch v`;
/// `unpattern = fmap (fmap unpatternVar)` drops the bind/match tag.
fn convert_let_pattern(
    pat: &p::Term,
) -> Result<(tamarin_theory::sapic::SapicTerm, BTreeSet<SapicLVar>), ConvertError> {
    let mut match_vars: BTreeSet<SapicLVar> = BTreeSet::new();
    let unpatterned = strip_pat_match(pat, &mut match_vars);
    let left = term(&unpatterned)?;
    Ok((left, match_vars))
}

/// Recursively strip `PatMatch` wrappers from a pattern term, recording each
/// matched variable.  A `=v` matching a plain variable contributes `v` to the
/// match-var set and unwraps to `v`; a `=t` over a compound term unwraps the
/// inner term (its variables are still matched, mirroring HS's per-leaf
/// `PatternMatch`).  Non-pattern subterms are returned unchanged.
fn strip_pat_match(t: &p::Term, match_vars: &mut BTreeSet<SapicLVar>) -> p::Term {
    match t {
        p::Term::PatMatch(inner) => {
            // Collect every variable under the matched subterm.
            collect_pattern_vars(inner, match_vars);
            // `unpattern` the inner term (it may itself contain nested patterns).
            strip_pat_match(inner, match_vars)
        }
        p::Term::Pair(items) => p::Term::Pair(
            items
                .iter()
                .map(|x| strip_pat_match(x, match_vars))
                .collect(),
        ),
        p::Term::App(n, args) => p::Term::App(
            n.clone(),
            args.iter()
                .map(|x| strip_pat_match(x, match_vars))
                .collect(),
        ),
        p::Term::AlgApp(n, a, b) => p::Term::AlgApp(
            n.clone(),
            Box::new(strip_pat_match(a, match_vars)),
            Box::new(strip_pat_match(b, match_vars)),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(strip_pat_match(a, match_vars)),
            Box::new(strip_pat_match(b, match_vars)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(strip_pat_match(a, match_vars)),
            Box::new(strip_pat_match(b, match_vars)),
        ),
        other => other.clone(),
    }
}

/// Collect every SAPIC variable occurring in a pattern term (used to populate
/// the match-var set for a `=t` matched subterm).
fn collect_pattern_vars(t: &p::Term, out: &mut BTreeSet<SapicLVar>) {
    match t {
        p::Term::Var(v) => {
            out.insert(varspec_to_sapic(v));
        }
        p::Term::PatMatch(inner) => collect_pattern_vars(inner, out),
        p::Term::Pair(items) => items.iter().for_each(|x| collect_pattern_vars(x, out)),
        p::Term::App(_, args) => args.iter().for_each(|x| collect_pattern_vars(x, out)),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            collect_pattern_vars(a, out);
            collect_pattern_vars(b, out);
        }
        _ => {}
    }
}

/// Convert a parser process into a `PlainProcess`.  Each node carries an empty
/// [`ProcessParsedAnnotation`]; names/back-substitution are filled in by later
/// passes (`propagate_names`, `rename_unique`).
pub fn convert_process(proc: &p::Process) -> Result<PlainProcess, ConvertError> {
    let ann = ProcessParsedAnnotation::empty();
    match proc {
        p::Process::Null => Ok(Process::Null(ann)),
        p::Process::Action { action: act, body } => Ok(Process::Action(
            action(act)?,
            ann,
            Box::new(convert_process(body)?),
        )),
        p::Process::Comb { comb, left, right } => {
            let l = Box::new(convert_process(left)?);
            let r = Box::new(convert_process(right)?);
            let c = combinator(comb)?;
            Ok(Process::Comb(c, ann, l, r))
        }
        // `!P` parses to `ProcessAction Rep mempty P` in HS
        // (Theory.Text.Parser.Sapic, replication branch); mirror by emitting a
        // `Rep` action whose single child is the replicated body.
        p::Process::Replication(body) => Ok(Process::Action(
            SapicAction::Rep,
            ann,
            Box::new(convert_process(body)?),
        )),
        p::Process::Call { .. } => {
            // Process-call inlining requires the theory's process-definition
            // map; the real pipeline goes through
            // `inline::convert_process_with_defs`.  This def-less entry point
            // (used by unit tests) cannot resolve a call.
            Err(ConvertError::new(
                "process calls require convert_process_with_defs",
            ))
        }
        p::Process::AtAnnotation(inner, _) => {
            // Location annotation (`@ loc`) — drop the location and descend.
            convert_process(inner)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convert_new_event_out_chain() {
        // new x:lol; event Test(x); out(f(f(x)))
        let xspec = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: Some("lol".into()),
        };
        let xref = p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        let ffx = p::Term::App(
            "f".into(),
            vec![p::Term::App("f".into(), vec![xref.clone()])],
        );
        let inner = p::Process::Action {
            action: p::SapicAction::ChOut {
                chan: None,
                msg: ffx,
            },
            body: Box::new(p::Process::Null),
        };
        let evt = p::Process::Action {
            action: p::SapicAction::Event(p::Fact {
                persistent: false,
                name: "Test".into(),
                args: vec![xref],
                annotations: vec![],
            }),
            body: Box::new(inner),
        };
        let top = p::Process::Action {
            action: p::SapicAction::New(xspec),
            body: Box::new(evt),
        };
        let conv = convert_process(&top).unwrap();
        // Outermost is New.
        assert!(matches!(conv, Process::Action(SapicAction::New(_), _, _)));
    }

    fn event(name: &str) -> p::Process {
        p::Process::Action {
            action: p::SapicAction::Event(p::Fact {
                persistent: false,
                name: name.into(),
                args: vec![],
                annotations: vec![],
            }),
            body: Box::new(p::Process::Null),
        }
    }

    #[test]
    fn convert_parallel_and_ndc() {
        let par = p::Process::Comb {
            comb: p::ProcessComb::Parallel,
            left: Box::new(event("A")),
            right: Box::new(event("B")),
        };
        assert!(matches!(
            convert_process(&par).unwrap(),
            Process::Comb(ProcessCombinator::Parallel, _, _, _)
        ));
        let ndc = p::Process::Comb {
            comb: p::ProcessComb::Ndc,
            left: Box::new(event("A")),
            right: Box::new(event("B")),
        };
        assert!(matches!(
            convert_process(&ndc).unwrap(),
            Process::Comb(ProcessCombinator::Ndc, _, _, _)
        ));
    }

    #[test]
    fn convert_replication_becomes_rep_action() {
        let rep = p::Process::Replication(Box::new(event("A")));
        assert!(matches!(
            convert_process(&rep).unwrap(),
            Process::Action(SapicAction::Rep, _, _)
        ));
    }

    #[test]
    fn convert_condeq() {
        let a = p::Term::Var(p::VarSpec {
            name: "a".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        let cond = p::Process::Comb {
            comb: p::ProcessComb::Cond(p::Condition::Eq(a.clone(), a)),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        assert!(matches!(
            convert_process(&cond).unwrap(),
            Process::Comb(ProcessCombinator::CondEq(_, _), _, _, _)
        ));
    }

    #[test]
    fn convert_cond_formula() {
        // `if <formula> then E else 0` converts to ProcessCombinator::Cond.
        let cond = p::Process::Comb {
            comb: p::ProcessComb::Cond(p::Condition::Formula(p::Formula::True)),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        assert!(matches!(
            convert_process(&cond).unwrap(),
            Process::Comb(ProcessCombinator::Cond(_), _, _, _)
        ));
    }

    #[test]
    fn convert_lookup() {
        let lookup = p::Process::Comb {
            comb: p::ProcessComb::Lookup(
                p::Term::PubLit("x".into()),
                p::VarSpec {
                    name: "v".into(),
                    idx: 0,
                    sort: p::SortHint::Untagged,
                    typ: None,
                },
            ),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        assert!(matches!(
            convert_process(&lookup).unwrap(),
            Process::Comb(ProcessCombinator::Lookup(_, _), _, _, _)
        ));
    }

    #[test]
    fn convert_insert_delete() {
        let ins = p::Process::Action {
            action: p::SapicAction::Insert(
                p::Term::PubLit("k".into()),
                p::Term::PubLit("v".into()),
            ),
            body: Box::new(p::Process::Action {
                action: p::SapicAction::Delete(p::Term::PubLit("k".into())),
                body: Box::new(p::Process::Null),
            }),
        };
        let conv = convert_process(&ins).unwrap();
        assert!(matches!(
            conv,
            Process::Action(SapicAction::Insert(_, _), _, _)
        ));
    }
}
