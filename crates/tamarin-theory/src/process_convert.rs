// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

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
            // (extractMatchingVariables pt)` (Parser/Sapic.hs) unpatterns the
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
        // theory `SapicAction::{Insert,Delete}` (Sapic/Process.hs), translated by
        // `baseTransAction` Insert/Delete (Basetranslation.hs).
        p::SapicAction::Insert(t1, t2) => Ok(SapicAction::Insert(term(t1, sig)?, term(t2, sig)?)),
        p::SapicAction::Delete(t) => Ok(SapicAction::Delete(term(t, sig)?)),
        // Locks: `lock t` / `unlock t` → theory `SapicAction::{Lock,Unlock}`
        // (Sapic/Process.hs), annotated by `Sapic.Locks.annotateLocks` and
        // translated by `baseTransAction` Lock/Unlock (Basetranslation.hs).
        p::SapicAction::Lock(t) => Ok(SapicAction::Lock(term(t, sig)?)),
        p::SapicAction::Unlock(t) => Ok(SapicAction::Unlock(term(t, sig)?)),
        // Embedded MSR rule `[l]--[a]->[r]` (optionally with `restricting φ`).
        // HS (Parser/Sapic.hs):
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
/// (Parser/Sapic.hs): strip every `=v` (`PatMatch`) marker from the
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
        // (Theory/Text/Parser/Sapic.hs), which is `sapic_from_parser`:
        // the variables carry their SAPIC type tag and a timepoint operand is
        // tagged `node`.  Predicate atoms stay sugar until the SAPIC rule
        // injection (`tamarin_sapic::apply`) expands them (HS
        // `liftedExpandFormula`).
        p::ProcessComb::Cond(p::Condition::Formula(f)) => Ok(ProcessCombinator::Cond(
            sapic_from_parser(f, sig).map_err(|e| ConvertError::new(e.message))?,
        )),
        // `lookup t as v in .. else ..`.  HS `Lookup (SapicNTerm v) v`
        // (Sapic/Process.hs).
        p::ProcessComb::Lookup(t, v) => Ok(ProcessCombinator::Lookup(
            term(t, sig)?,
            varspec_to_sapic(v),
        )),
        // `let pat = value in P [else Q]`.  HS
        // `ProcessComb (Let (unpattern t1) t2 (extractMatchingVariables t1))`
        // (Parser/Sapic.hs).  The parser-AST pattern `pat` may contain
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
/// Pattern.hs).  Returns the `unpattern`ed SAPIC term (with every `=v`
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

/// Recursively strip `PatMatch` wrappers from a pattern term, recording each
/// matched variable.  A `=v` contributes `v` to the match-var set (HS
/// `extractMatchingVariables` collects the `PatternMatch` variables,
/// Pattern.hs) and unwraps to `v`; the parser only puts the marker on a
/// variable (`pattern_var_atom`), matching HS `sapicpatternvar`.  Non-pattern
/// subterms are returned unchanged.
fn strip_pat_match(t: &p::Term, match_vars: &mut BTreeSet<SapicLVar>) -> p::Term {
    match t {
        p::Term::PatMatch(inner) => {
            if let p::Term::Var(v) = &**inner {
                match_vars.insert(varspec_to_sapic(v));
            }
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

/// Shared recursive parser-process conversion. Process-call policy is the
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
    let ann = ProcessParsedAnnotation::empty();
    match proc {
        p::Process::Null => Ok(Process::Null(ann)),
        p::Process::Action { action: act, body } => Ok(Process::Action(
            action(act, sig)?,
            ann,
            Box::new(convert_process_with(body, sig, resolve_call)?),
        )),
        p::Process::Comb { comb, left, right } => {
            let l = Box::new(convert_process_with(left, sig, resolve_call)?);
            let r = Box::new(convert_process_with(right, sig, resolve_call)?);
            let c = combinator(comb, sig)?;
            Ok(Process::Comb(c, ann, l, r))
        }
        // `!P` parses to `ProcessAction Rep mempty P` in HS
        // (Theory.Text.Parser.Sapic, replication branch); mirror by emitting a
        // `Rep` action whose single child is the replicated body.
        p::Process::Replication(body) => Ok(Process::Action(
            SapicAction::Rep,
            ann,
            Box::new(convert_process_with(body, sig, resolve_call)?),
        )),
        p::Process::Call { name, args } => resolve_call(name, args, sig),
        p::Process::AtAnnotation(inner, location) => {
            // HS `processAddAnnotation p (mempty { location = Just m })`:
            // attach the converted location to the root of the parenthesised
            // process, preserving any annotation already present there.
            let converted = convert_process_with(inner, sig, resolve_call)?;
            let mut location_ann = ProcessParsedAnnotation::empty();
            location_ann.location = Some(term(location, sig)?);
            Ok(add_root_annotation(converted, location_ann))
        }
    }
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
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_term::lterm::LVar;
    use tamarin_term::maude_sig::pair_maude_sig;

    /// The signature a def-less conversion runs against: `minimalMaudeSig`
    /// (`pairFunSig`, Term/Maude/Signature.hs), which every theory
    /// carries.
    fn msig() -> MaudeSig {
        pair_maude_sig()
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

    // -- pattern (`=t`) splitting -------------------------------------------
    //
    // HS tags pattern variables at the leaf. The rule is `ltypedpatternlit =
    // vlit sapicpatternvar` (Parser/Sapic.hs). A `sapicpatternvar` is an
    // optional `=` in front of a single `sapicvar` (Token.hs). A
    // pattern term is therefore a `SapicNTerm PatternSapicLVar`. Every
    // variable in that term carries a `PatternBind` or `PatternMatch` tag.
    // `unpattern = fmap (fmap unpatternVar)` drops the tags
    // (Pattern.hs). `extractMatchingVariables pt = S.fromList $ foldMap
    // (foldMap isPatternMatch) pt` (Pattern.hs) collects the matched
    // ones. It is a foldMap over the complete term. The depth therefore does
    // not matter, and the result is a set.

    /// Builds `x` or `x:ty` as a parser-AST variable leaf. A bare variable is
    /// message-sorted.
    fn pvar(name: &str, typ: Option<&str>) -> p::Term {
        p::Term::Var(p::VarSpec {
            name: name.into(),
            idx: 0,
            sort: LSort::Msg,
            typ: typ.map(Into::into),
        })
    }

    /// Builds the `SapicLVar` that [`pvar`] elaborates to. A `sapicvar` keeps
    /// the `:type` annotation (Token.hs). A `PatternSapicLVar` wraps a
    /// complete `SapicLVar` (Pattern.hs). The type is therefore part of
    /// the `extractMatchingVariables` set element.
    fn svar(name: &str, typ: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, 0), typ.map(Into::into))
    }

    /// The `=t` marker.
    fn pat_match(t: p::Term) -> p::Term {
        p::Term::PatMatch(Box::new(t))
    }

    #[test]
    fn let_and_chin_patterns_split_matched_leaves_out_of_the_bound_term() {
        // HS builds `let` as `ProcessComb (Let (unpattern t1) t2
        // (extractMatchingVariables t1)) mempty p' q` (Parser/Sapic.hs).
        // HS builds `in(c,pt)` as `ChIn maybeChannel (unpattern pt)
        // (extractMatchingVariables pt)` (Parser/Sapic.hs). Both sides
        // use the same pair of Pattern.hs functions.
        //
        // `extractMatchingVariables` returns an `S.Set SapicLVar`. The two
        // `=x:ty` leaves below therefore collapse to one element, and that
        // element carries the `:ty` annotation. `y` is bound, not matched, so
        // it stays out of the set.
        let marked = p::Term::Pair(vec![
            pat_match(pvar("x", Some("ty"))),
            p::Term::Pair(vec![pvar("y", None), pat_match(pvar("x", Some("ty")))]),
        ]);
        let plain = p::Term::Pair(vec![
            pvar("x", Some("ty")),
            p::Term::Pair(vec![pvar("y", None), pvar("x", Some("ty"))]),
        ]);
        let want_vars = BTreeSet::from([svar("x", Some("ty"))]);

        let lt = p::Process::Comb {
            comb: p::ProcessComb::Let {
                pat: marked.clone(),
                value: p::Term::PubLit("v".into()),
            },
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        let Process::Comb(
            ProcessCombinator::Let {
                left,
                right,
                match_vars,
            },
            _,
            _,
            _,
        ) = convert_process(&lt, &msig()).unwrap()
        else {
            panic!("expected a Let combinator");
        };
        assert_eq!(left, term(&plain, &msig()).unwrap(), "`unpattern t1`");
        assert_eq!(match_vars, want_vars, "`extractMatchingVariables t1`");
        // The right-hand side is a `sapicterm`, not a pattern. The conversion
        // leaves it unchanged.
        assert_eq!(right, term(&p::Term::PubLit("v".into()), &msig()).unwrap());

        let chin = p::Process::Action {
            action: p::SapicAction::ChIn {
                chan: Some(p::Term::PubLit("c".into())),
                msg: marked,
            },
            body: Box::new(p::Process::Null),
        };
        let Process::Action(
            SapicAction::ChIn {
                chan,
                msg,
                match_vars,
            },
            _,
            _,
        ) = convert_process(&chin, &msig()).unwrap()
        else {
            panic!("expected a ChIn action");
        };
        assert_eq!(
            chan,
            Some(term(&p::Term::PubLit("c".into()), &msig()).unwrap())
        );
        assert_eq!(msg, term(&plain, &msig()).unwrap(), "`unpattern pt`");
        assert_eq!(match_vars, want_vars, "`extractMatchingVariables pt`");
    }
}
