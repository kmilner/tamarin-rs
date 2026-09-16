// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parser-AST → theory-AST process converter.
//!
//! Maps `tamarin_parser::ast::Process` (the surface syntax tree) into
//! `crate::sapic::PlainProcess` (the HS-faithful `Process<ann, v>`
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
use tamarin_term::maude_sig::MaudeSig;
// A variable literal of a SAPIC term and a SAPIC binder are the same reading
// of a `VarSpec`, so both come from one definition.
use crate::elaborate::{
    fact_to_sapic_fact, map_formula_terms, term_to_sapic_term, varspec_to_sapic,
};
use crate::formula::sapic_from_parser;
use crate::sapic::{
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

pub(crate) fn term(t: &p::Term, sig: &MaudeSig) -> Result<crate::sapic::SapicTerm, ConvertError> {
    term_to_sapic_term(t, sig)
        .ok_or_else(|| ConvertError::new("could not convert SAPIC term (pattern term?)"))
}

fn fact(f: &p::Fact, sig: &MaudeSig) -> Result<crate::sapic::SapicLNFact, ConvertError> {
    fact_to_sapic_fact(f, sig).map_err(|e| ConvertError::new(e.message))
}

/// Convert a parser action into a theory `SapicAction<SapicLVar>`.
pub(crate) fn action(
    a: &p::SapicAction,
    sig: &MaudeSig,
) -> Result<SapicAction<SapicLVar>, ConvertError> {
    match a {
        p::SapicAction::New(v) => Ok(SapicAction::New(varspec_to_sapic(v))),
        p::SapicAction::Event(f) => Ok(SapicAction::Event(fact(f, sig)?)),
        p::SapicAction::ChOut { chan, msg } => Ok(SapicAction::ChOut {
            chan: chan.as_ref().map(|c| term(c, sig)).transpose()?,
            msg: term(msg, sig)?,
        }),
        p::SapicAction::ChIn { chan, msg } => {
            // The surface `in(c, pat)` parser stores the pattern with `=t`
            // (`PatMatch`) match markers.  HS `ChIn maybeChannel (unpattern pt)
            // (extractMatchingVariables pt)` (Parser/Sapic.hs:84-162, see line 114) unpatterns the
            // message term and splits the matched variables out into `match_vars`.
            // We reuse the same `unpattern`/`extractMatchingVariables` helper used
            // for `let` patterns.
            let (msg_unpat, match_vars) = convert_let_pattern(msg, sig)?;
            Ok(SapicAction::ChIn {
                chan: chan.as_ref().map(|c| term(c, sig)).transpose()?,
                msg: msg_unpat,
                match_vars,
            })
        }
        // Mutable state: `insert t1 v` / `delete t`.  These map to the
        // theory `SapicAction::{Insert,Delete}` (Sapic/Process.hs:72-73), translated by
        // `baseTransAction` Insert/Delete (Basetranslation.hs:177-184).
        p::SapicAction::Insert(t1, t2) => Ok(SapicAction::Insert(term(t1, sig)?, term(t2, sig)?)),
        p::SapicAction::Delete(t) => Ok(SapicAction::Delete(term(t, sig)?)),
        // Locks: `lock t` / `unlock t` → theory `SapicAction::{Lock,Unlock}`
        // (Sapic/Process.hs:74-75), annotated by `Sapic.Locks.annotateLocks` and
        // translated by `baseTransAction` Lock/Unlock (Basetranslation.hs:185-194).
        p::SapicAction::Lock(t) => Ok(SapicAction::Lock(term(t, sig)?)),
        p::SapicAction::Unlock(t) => Ok(SapicAction::Unlock(term(t, sig)?)),
        // Embedded MSR rule `[l]--[a]->[r]` (optionally with `restricting φ`).
        // HS (Parser/Sapic.hs:154-160):
        //   let matchVars = foldMap (foldMap extractMatchingVariables) l
        //   let f = fmap (fmap unpattern); g = fmap (fmap unpatternVar)
        //   if validMSR S.empty (l,a,r) then MSR (f l) (f a) (f r) (g phi) matchVars
        // i.e. match-vars come from the PREMISES only; every fact row is
        // `unpattern`ed (the `=v` markers stripped), and the embedded
        // restriction formulas get `unpatternVar` — their `=v` markers are
        // stripped too, without contributing match-vars.  HS reads those
        // formulas with `sapicpatternvar` and strips the pattern tag
        // afterwards, so the marker goes before the locally-nameless formula
        // is built and `sapic_from_parser` never meets a `PatMatch` term.
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
                .map(|f| fact_unpattern(f, sig, Some(&mut match_vars)))
                .collect::<Result<Vec<_>, _>>()?;
            // Actions / conclusions: unpattern only (no match-var collection).
            let acts_c = acts
                .iter()
                .map(|f| fact_unpattern(f, sig, None))
                .collect::<Result<Vec<_>, _>>()?;
            let concs_c = concs
                .iter()
                .map(|f| fact_unpattern(f, sig, None))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SapicAction::Msr {
                prems: prems_c,
                acts: acts_c,
                concs: concs_c,
                rest: restrictions
                    .iter()
                    .map(|f| {
                        sapic_from_parser(&formula_unpattern(f), sig)
                            .map_err(|e| ConvertError::new(e.message))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
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
    sig: &MaudeSig,
    mut match_vars: Option<&mut BTreeSet<SapicLVar>>,
) -> Result<crate::sapic::SapicLNFact, ConvertError> {
    let mut sink = BTreeSet::new();
    let args: Vec<p::Term> = f
        .args
        .iter()
        .map(|t| strip_pat_match(t, match_vars.as_deref_mut().unwrap_or(&mut sink)))
        .collect();
    let f2 = p::Fact { args, ..f.clone() };
    fact(&f2, sig)
}

/// HS `g = fmap (fmap unpatternVar)` over an embedded restriction formula
/// (Parser/Sapic.hs:158): strip every `=v` (`PatMatch`) marker from the
/// formula's terms.  No match-vars are collected — HS takes `matchVars` from
/// the premises only.
fn formula_unpattern(f: &p::Formula) -> p::Formula {
    map_formula_terms(f, &|t| strip_pat_match(t, &mut BTreeSet::new()))
}

/// Convert a parser combinator into a theory `ProcessCombinator<SapicLVar>`.
///
/// Mirrors the SAPIC parser's combinator construction
/// (`Theory.Text.Parser.Sapic`): `Parallel`/`Ndc` are nullary; `if t1 = t2`
/// becomes `CondEq t1 t2`; `if frml` becomes `Cond frml`; `lookup`/`let`
/// become `Lookup`/`Let`.
pub(crate) fn combinator(
    c: &p::ProcessComb,
    sig: &MaudeSig,
) -> Result<ProcessCombinator<SapicLVar>, ConvertError> {
    match c {
        p::ProcessComb::Parallel => Ok(ProcessCombinator::Parallel),
        p::ProcessComb::Ndc => Ok(ProcessCombinator::Ndc),
        p::ProcessComb::Cond(p::Condition::Eq(t1, t2)) => {
            Ok(ProcessCombinator::CondEq(term(t1, sig)?, term(t2, sig)?))
        }
        // `if <formula> then .. else ..`.  HS parses the condition with
        // `standardFormula sapicvar sapicnodevar`
        // (Theory/Text/Parser/Sapic.hs:252-255), which is `sapic_from_parser`:
        // the variables carry their SAPIC type tag and a timepoint operand is
        // tagged `node`.  Predicate atoms stay sugar until the SAPIC rule
        // injection (`tamarin_sapic::apply`) expands them (HS
        // `liftedExpandFormula`).
        p::ProcessComb::Cond(p::Condition::Formula(f)) => Ok(ProcessCombinator::Cond(
            sapic_from_parser(f, sig).map_err(|e| ConvertError::new(e.message))?,
        )),
        // `lookup t as v in .. else ..`.  HS `Lookup (SapicNTerm v) v`
        // (Sapic/Process.hs:95).
        p::ProcessComb::Lookup(t, v) => Ok(ProcessCombinator::Lookup(
            term(t, sig)?,
            varspec_to_sapic(v),
        )),
        // `let pat = value in P [else Q]`.  HS
        // `ProcessComb (Let (unpattern t1) t2 (extractMatchingVariables t1))`
        // (Parser/Sapic.hs:268-269).  The parser-AST pattern `pat` may contain
        // `=t` (`PatMatch`) match markers; we split them out into `match_vars`
        // and `unpattern` the rest into the `left` term.
        p::ProcessComb::Let { pat, value } => {
            let (left, match_vars) = convert_let_pattern(pat, sig)?;
            let right = term(value, sig)?;
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
    sig: &MaudeSig,
) -> Result<(crate::sapic::SapicTerm, BTreeSet<SapicLVar>), ConvertError> {
    let mut match_vars: BTreeSet<SapicLVar> = BTreeSet::new();
    let unpatterned = strip_pat_match(pat, &mut match_vars);
    let left = term(&unpatterned, sig)?;
    Ok((left, match_vars))
}

/// Strip `PatMatch` wrappers from a pattern term, recording each
/// matched variable.  A `=v` contributes `v` to the match-var set (HS
/// `extractMatchingVariables` collects the `PatternMatch` variables,
/// Pattern.hs:92-96) and unwraps to `v`; the parser only puts the marker on a
/// variable (`pattern_var_atom`), matching HS `sapicpatternvar`.  Non-pattern
/// subterms are returned unchanged.
fn strip_pat_match(t: &p::Term, match_vars: &mut BTreeSet<SapicLVar>) -> p::Term {
    tamarin_utils::stack::ensure_sufficient_stack(|| match t {
        p::Term::PatMatch(inner) => {
            if let p::Term::Var(v) = &**inner {
                match_vars.insert(varspec_to_sapic(v));
            }
            strip_pat_match(inner, match_vars)
        }
        p::Term::Pair(args) => p::Term::Pair(
            args.iter()
                .map(|t| strip_pat_match(t, match_vars))
                .collect(),
        ),
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter()
                .map(|t| strip_pat_match(t, match_vars))
                .collect(),
        ),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            let a = Box::new(strip_pat_match(a, match_vars));
            let b = Box::new(strip_pat_match(b, match_vars));
            match t {
                p::Term::AlgApp(name, _, _) => p::Term::AlgApp(name.clone(), a, b),
                p::Term::Diff(_, _) => p::Term::Diff(a, b),
                p::Term::BinOp(op, _, _) => p::Term::BinOp(*op, a, b),
                _ => unreachable!(),
            }
        }
        _ => t.clone(),
    })
}

/// Convert a parser process into a `PlainProcess`. Nodes start with an empty
/// [`ProcessParsedAnnotation`] except that `(P) @ location` sets the root
/// node's location. Names/back-substitution are filled in by later passes
/// (`propagate_names`, `rename_unique`).
pub fn convert_process(proc: &p::Process, sig: &MaudeSig) -> Result<PlainProcess, ConvertError> {
    convert_process_with(proc, sig, &mut |_, _, _| {
        Err(ConvertError::new(
            "process calls require convert_process_with_defs",
        ))
    })
}

/// Shared iterative parser-process conversion. Process-call policy is the
/// only part that depends on the surrounding definition environment, so it is
/// supplied by the caller rather than duplicating this complete tree walk in
/// `process_inline`.
pub(crate) fn convert_process_with<F>(
    proc: &p::Process,
    sig: &MaudeSig,
    resolve_call: &mut F,
) -> Result<PlainProcess, ConvertError>
where
    F: FnMut(&str, &[p::Term], &MaudeSig) -> Result<PlainProcess, ConvertError>,
{
    enum Work<'a> {
        Visit(&'a p::Process),
        Action(SapicAction<SapicLVar>),
        Comb(&'a p::ProcessComb),
        Location(&'a p::Term),
    }
    let mut work = vec![Work::Visit(proc)];
    let mut values = Vec::new();
    while let Some(task) = work.pop() {
        let ann = ProcessParsedAnnotation::empty();
        match task {
            Work::Visit(node) => match node {
                p::Process::Null => values.push(Process::Null(ann)),
                p::Process::Action { action: act, body } => {
                    work.push(Work::Action(action(act, sig)?));
                    work.push(Work::Visit(body));
                }
                p::Process::Comb { comb, left, right } => {
                    // Preserve conversion order: both children precede the combinator.
                    work.push(Work::Comb(comb));
                    work.push(Work::Visit(right));
                    work.push(Work::Visit(left));
                }
                p::Process::Replication(body) => {
                    work.push(Work::Action(SapicAction::Rep));
                    work.push(Work::Visit(body));
                }
                p::Process::Call { name, args } => values.push(resolve_call(name, args, sig)?),
                p::Process::AtAnnotation(inner, location) => {
                    work.push(Work::Location(location));
                    work.push(Work::Visit(inner));
                }
            },
            Work::Action(act) => {
                let body = values.pop().unwrap();
                values.push(Process::Action(act, ann, Box::new(body).into()));
            }
            Work::Comb(comb) => {
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                values.push(Process::Comb(
                    combinator(comb, sig)?,
                    ann,
                    Box::new(left).into(),
                    Box::new(right).into(),
                ));
            }
            Work::Location(location) => {
                let converted = values.pop().unwrap();
                let mut ann = ann;
                ann.location = Some(term(location, sig)?);
                values.push(add_root_annotation(converted, ann));
            }
        }
    }
    Ok(values.pop().unwrap())
}

pub(crate) fn add_root_annotation(
    p: PlainProcess,
    ann_add: ProcessParsedAnnotation,
) -> PlainProcess {
    match p {
        Process::Null(a) => Process::Null(a.append(ann_add)),
        Process::Action(ac, a, body) => Process::Action(ac, a.append(ann_add), body),
        Process::Comb(c, a, l, r) => Process::Comb(c, a.append(ann_add), l, r),
    }
}

#[cfg(test)]
#[path = "process_convert_tests.rs"]
mod tests;
