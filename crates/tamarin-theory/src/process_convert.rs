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
use tamarin_term::lterm::LVar;
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

/// `LVar` → parser `VarSpec` (name/idx/sort carried over, no SAPIC type).
pub fn lvar_to_varspec(v: &LVar) -> p::VarSpec {
    p::VarSpec {
        name: v.name.to_string(),
        idx: v.idx,
        sort: v.sort,
        typ: None,
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
        // tagged `node`.  Predicate atoms stay sugar until
        // `lift_rule_restrictions` expands them (HS `liftedExpandFormula`).
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

/// Recursively strip `PatMatch` wrappers from a pattern term, recording each
/// matched variable.  A `=v` contributes `v` to the match-var set (HS
/// `extractMatchingVariables` collects the `PatternMatch` variables,
/// Pattern.hs:92-96) and unwraps to `v`; the parser only puts the marker on a
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

/// Convert a parser process into a `PlainProcess`.  Each node carries an empty
/// [`ProcessParsedAnnotation`]; names/back-substitution are filled in by later
/// passes (`propagate_names`, `rename_unique`).
pub fn convert_process(proc: &p::Process, sig: &MaudeSig) -> Result<PlainProcess, ConvertError> {
    let ann = ProcessParsedAnnotation::empty();
    match proc {
        p::Process::Null => Ok(Process::Null(ann)),
        p::Process::Action { action: act, body } => Ok(Process::Action(
            action(act, sig)?,
            ann,
            Box::new(convert_process(body, sig)?),
        )),
        p::Process::Comb { comb, left, right } => {
            let l = Box::new(convert_process(left, sig)?);
            let r = Box::new(convert_process(right, sig)?);
            let c = combinator(comb, sig)?;
            Ok(Process::Comb(c, ann, l, r))
        }
        // `!P` parses to `ProcessAction Rep mempty P` in HS
        // (Theory.Text.Parser.Sapic, replication branch); mirror by emitting a
        // `Rep` action whose single child is the replicated body.
        p::Process::Replication(body) => Ok(Process::Action(
            SapicAction::Rep,
            ann,
            Box::new(convert_process(body, sig)?),
        )),
        p::Process::Call { .. } => {
            // Process-call inlining requires the theory's process-definition
            // map; the real pipeline goes through
            // `process_inline::convert_process_with_defs`.  This def-less
            // entry point (used by unit tests) cannot resolve a call.
            Err(ConvertError::new(
                "process calls require convert_process_with_defs",
            ))
        }
        p::Process::AtAnnotation(inner, _) => {
            // Location annotation (`@ loc`) — drop the location and descend.
            convert_process(inner, sig)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_term::maude_sig::pair_maude_sig;

    /// The signature a def-less conversion runs against: `minimalMaudeSig`
    /// (`pairFunSig`, Term/Maude/Signature.hs:224-226), which every theory
    /// carries.
    fn msig() -> MaudeSig {
        pair_maude_sig()
    }

    #[test]
    fn convert_new_event_out_chain() {
        // new x:lol; event Test(x); out(f(f(x)))
        let xspec = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
            typ: Some("lol".into()),
        };
        let xref = p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: LSort::Msg,
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
        let conv = convert_process(&top, &msig()).unwrap();
        // The complete spine converts. `New` carries the SAPIC type. The
        // event fact comes next. Then comes the out with the nested `f(f(x))`
        // payload.
        let Process::Action(SapicAction::New(v), _, body) = conv else {
            panic!("expected New at the top");
        };
        assert_eq!(v.var.name, "x");
        assert_eq!(v.stype.as_deref(), Some("lol"));
        let Process::Action(SapicAction::Event(fact), _, body) = *body else {
            panic!("expected Event under the New");
        };
        assert_eq!(crate::fact::fact_tag_name(&fact.tag), "Test");
        assert_eq!(fact.terms.len(), 1);
        let Process::Action(SapicAction::ChOut { chan, msg }, _, body) = *body else {
            panic!("expected ChOut under the Event");
        };
        assert!(chan.is_none(), "`out(t)` has no explicit channel");
        // `f(f(x))` has two nested applications over the bound variable.
        use tamarin_term::vterm::{Lit, VTerm};
        let VTerm::App(_, outer) = &msg else {
            panic!("expected f(f(x)), got {msg:?}");
        };
        let VTerm::App(_, inner) = &outer[0] else {
            panic!("expected the inner f(x)");
        };
        assert!(matches!(inner[0], VTerm::Lit(Lit::Var(_))));
        assert!(matches!(*body, Process::Null(_)));
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

    /// Returns the event name that a converted `event N` child carries. The
    /// tests use it to assert that a combinator keeps its two children in the
    /// source order.
    fn child_event_name(p: &PlainProcess) -> String {
        let Process::Action(SapicAction::Event(f), _, _) = p else {
            panic!("expected an event child, got {p:?}");
        };
        crate::fact::fact_tag_name(&f.tag)
    }

    #[test]
    fn convert_parallel_and_ndc() {
        for (comb, want) in [
            (p::ProcessComb::Parallel, ProcessCombinator::Parallel),
            (p::ProcessComb::Ndc, ProcessCombinator::Ndc),
        ] {
            let src = p::Process::Comb {
                comb,
                left: Box::new(event("A")),
                right: Box::new(event("B")),
            };
            let Process::Comb(got, _, l, r) = convert_process(&src, &msig()).unwrap() else {
                panic!("expected a combinator for {want:?}");
            };
            assert_eq!(got, want);
            // The children convert. The left and right order does not change.
            assert_eq!(child_event_name(&l), "A");
            assert_eq!(child_event_name(&r), "B");
        }
    }

    #[test]
    fn convert_replication_becomes_rep_action() {
        let rep = p::Process::Replication(Box::new(event("A")));
        // `!P` becomes `Rep`. The replicated body is the only child of `Rep`.
        // The body must stay. The usual `0` must not replace it.
        let Process::Action(SapicAction::Rep, _, body) = convert_process(&rep, &msig()).unwrap()
        else {
            panic!("expected a Rep action");
        };
        let Process::Action(SapicAction::Event(f), _, _) = *body else {
            panic!("expected the replicated event as Rep's child");
        };
        assert_eq!(crate::fact::fact_tag_name(&f.tag), "A");
    }

    #[test]
    fn convert_condeq() {
        let a = p::Term::Var(p::VarSpec {
            name: "a".into(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        });
        let b = p::Term::PubLit("b".into());
        let cond = p::Process::Comb {
            comb: p::ProcessComb::Cond(p::Condition::Eq(a.clone(), b.clone())),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        let Process::Comb(ProcessCombinator::CondEq(l, r), _, then, els) =
            convert_process(&cond, &msig()).unwrap()
        else {
            panic!("expected a CondEq combinator");
        };
        // Both sides of `t1 = t2` convert, and they keep their order. The then
        // arm and the else arm stay on their own sides.
        assert_eq!(l, term(&a, &msig()).unwrap());
        assert_eq!(r, term(&b, &msig()).unwrap());
        assert_eq!(child_event_name(&then), "E");
        assert!(matches!(*els, Process::Null(_)));
    }

    #[test]
    fn convert_cond_formula() {
        // `if <formula> then E else 0` converts to ProcessCombinator::Cond,
        // whose payload is the locally-nameless SAPIC formula the condition
        // parser builds.  A predicate atom stays `SyntacticSugar::Pred` until
        // `lift_rule_restrictions` expands it.
        let frml = p::Formula::Atom(p::Atom::Pred(p::Fact {
            persistent: false,
            name: "P".into(),
            args: vec![p::Term::PubLit("c".into())],
            annotations: vec![],
        }));
        let cond = p::Process::Comb {
            comb: p::ProcessComb::Cond(p::Condition::Formula(frml.clone())),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        let Process::Comb(ProcessCombinator::Cond(got), _, then, _) =
            convert_process(&cond, &msig()).unwrap()
        else {
            panic!("expected a Cond combinator");
        };
        let want = crate::formula::ProtoFormula::Atom(crate::atom::ProtoAtom::Syntactic(
            crate::atom::SyntacticSugar::Pred(crate::fact::Fact::new(
                crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "P", 1),
                vec![tamarin_term::vterm::VTerm::Lit(
                    tamarin_term::vterm::Lit::Con(tamarin_term::lterm::Name::new(
                        tamarin_term::lterm::NameTag::Pub,
                        "c",
                    )),
                )],
            )),
        ));
        assert_eq!(got, want);
        assert_eq!(child_event_name(&then), "E");
    }

    #[test]
    fn convert_lookup() {
        let cell = p::Term::PubLit("x".into());
        let lookup = p::Process::Comb {
            comb: p::ProcessComb::Lookup(
                cell.clone(),
                p::VarSpec {
                    name: "v".into(),
                    idx: 0,
                    sort: LSort::Msg,
                    typ: Some("cellty".into()),
                },
            ),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        let Process::Comb(ProcessCombinator::Lookup(t, v), _, found, notfound) =
            convert_process(&lookup, &msig()).unwrap()
        else {
            panic!("expected a Lookup combinator");
        };
        assert_eq!(t, term(&cell, &msig()).unwrap());
        // `lookup t as v` binds `v` and keeps its SAPIC type. A bare
        // variable is message-sorted.
        assert_eq!(v.var.name, "v");
        assert_eq!(v.var.sort, LSort::Msg);
        assert_eq!(v.stype.as_deref(), Some("cellty"));
        assert_eq!(child_event_name(&found), "E");
        assert!(matches!(*notfound, Process::Null(_)));
    }

    /// A bare token naming a declared 0-arity symbol is an APPLICATION in a
    /// condition, not a free variable: HS's term parser resolves it against
    /// the signature while parsing (`nullaryApp`,
    /// Theory/Text/Parser/Term.hs:151,158-163), so `freesList` never reports
    /// it and a substitution never rewrites it.
    #[test]
    fn a_declared_nullary_symbol_in_a_condition_is_an_application_not_a_free_variable() {
        let cond = |decl: &str| {
            let thy =
                tamarin_parser::parse_theory(&format!("theory T begin\n{decl}\nend"), &[]).unwrap();
            let msig = crate::elaborate::elaborate(&thy)
                .unwrap()
                .signature
                .maude_sig;
            let f = tamarin_parser::parser::parse_formula_str("Eq(c, k)", &msig).unwrap();
            sapic_from_parser(&f, &msig).unwrap()
        };
        let names = |f: &crate::sapic::SapicFormula| -> Vec<String> {
            crate::formula::formula_frees(f)
                .iter()
                .map(|v| v.var.name.to_string())
                .collect()
        };
        // Undeclared, `c` is an ordinary variable, so both are free — this is
        // what makes the assertion below discriminating.
        assert_eq!(names(&cond("")), vec!["c".to_string(), "k".to_string()]);
        assert_eq!(
            names(&cond("functions: c/0")),
            vec!["k".to_string()],
            "a declared nullary symbol is an application, not a variable"
        );
    }

    /// A quantifier binder in a condition is a `Bound` De Bruijn index, so it
    /// is not a free variable and no substitution can reach it — HS's
    /// `Foldable BVar` yields `Free` variables only
    /// (Theory/Sapic/Term.hs:131-132#freesSapicTerm).
    #[test]
    fn a_bound_occurrence_in_a_condition_is_not_a_free_variable() {
        let msig = msig();
        let f = tamarin_parser::parser::parse_formula_str("Ex k. Eq(c, k)", &msig).unwrap();
        let got = sapic_from_parser(&f, &msig).unwrap();
        let frees: Vec<String> = crate::formula::formula_frees(&got)
            .iter()
            .map(|v| v.var.name.to_string())
            .collect();
        assert_eq!(frees, vec!["c".to_string()]);
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
        let key = term(&p::Term::PubLit("k".into()), &msig()).unwrap();
        let conv = convert_process(&ins, &msig()).unwrap();
        let Process::Action(SapicAction::Insert(k, v), _, body) = conv else {
            panic!("expected Insert at the top");
        };
        assert_eq!(k, key);
        assert_eq!(v, term(&p::Term::PubLit("v".into()), &msig()).unwrap());
        // The `delete` below it also converts. It keeps its key term.
        let Process::Action(SapicAction::Delete(dk), _, _) = *body else {
            panic!("expected Delete under the Insert");
        };
        assert_eq!(dk, key);
    }

    // -- pattern (`=t`) splitting -------------------------------------------
    //
    // HS tags pattern variables at the leaf. The rule is `ltypedpatternlit =
    // vlit sapicpatternvar` (Parser/Sapic.hs:52-53). A `sapicpatternvar` is an
    // optional `=` in front of a single `sapicvar` (Token.hs:512-519). A
    // pattern term is therefore a `SapicNTerm PatternSapicLVar`. Every
    // variable in that term carries a `PatternBind` or `PatternMatch` tag.
    // `unpattern = fmap (fmap unpatternVar)` drops the tags
    // (Pattern.hs:54-60). `extractMatchingVariables pt = S.fromList $ foldMap
    // (foldMap isPatternMatch) pt` (Pattern.hs:92-96) collects the matched
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
    /// the `:type` annotation (Token.hs:506-510). A `PatternSapicLVar` wraps a
    /// complete `SapicLVar` (Pattern.hs:42-44). The type is therefore part of
    /// the `extractMatchingVariables` set element.
    fn svar(name: &str, typ: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, 0), typ.map(Into::into))
    }

    fn pfact(name: &str, args: Vec<p::Term>) -> p::Fact {
        p::Fact {
            persistent: false,
            name: name.into(),
            args,
            annotations: vec![],
        }
    }

    /// The `=t` marker.
    fn pat_match(t: p::Term) -> p::Term {
        p::Term::PatMatch(Box::new(t))
    }

    #[test]
    fn msr_unpatterns_every_row_but_takes_match_vars_from_the_premises_only() {
        // HS (Parser/Sapic.hs:155-161):
        //   (l,a,r,phi) <- try $ genericRule sapicpatternvar (PatternBind <$> sapicnodevar)
        //   let matchVars =  foldMap (foldMap extractMatchingVariables) l
        //   let f = fmap (fmap unpattern)
        //   ... then return (MSR (f l) (f a) (f r) (g phi) matchVars, mempty)
        // The `matchVars` fold runs over `l` only. The code applies `f`
        // (unpattern) to all three rows.
        let deep = |leaf: p::Term| {
            p::Term::App("h".into(), vec![p::Term::Pair(vec![leaf, pvar("y", None)])])
        };
        let prems = vec![pfact("In", vec![deep(pat_match(pvar("x", None)))])];
        // HS never gives this code a `=` in the action rows or the conclusion
        // rows. The `validMSR` guards `(_,[]) <- freesPatternFactList a` and
        // `(_,[]) <- freesPatternFactList r` (Pattern.hs:79-89) fail the parse
        // first. The pinned oracle also rejects such a source. The half that
        // this test pins is the HS half. Whatever those rows contain, they add
        // nothing to `matchVars`.
        let acts = vec![pfact("Ev", vec![pat_match(pvar("z", None))])];
        let concs = vec![pfact("Out", vec![pat_match(pvar("w", None))])];
        let msr = p::Process::Action {
            action: p::SapicAction::Msr {
                prems,
                acts,
                concs,
                restrictions: vec![],
            },
            body: Box::new(p::Process::Null),
        };
        let Process::Action(
            SapicAction::Msr {
                prems,
                acts,
                concs,
                rest,
                match_vars,
            },
            _,
            _,
        ) = convert_process(&msr, &msig()).unwrap()
        else {
            panic!("expected an Msr action");
        };
        // The set holds the premise variables only. `z` and `w` are absent,
        // although they carry `=`.
        assert_eq!(match_vars, BTreeSet::from([svar("x", None)]));
        // The conversion unpatterns every row. A `PatMatch` that survives
        // makes `term_to_sapic_term` answer `None`, and then the conversion
        // fails. The comparison against the marker-free terms therefore pins
        // two things. It pins the removal of the markers, and it pins the rows
        // that the removal reaches.
        assert_eq!(
            prems[0].terms.to_vec(),
            vec![term(&deep(pvar("x", None)), &msig()).unwrap()],
            "the premise keeps its shape with the `=` marker removed"
        );
        assert_eq!(
            acts[0].terms.to_vec(),
            vec![term(&pvar("z", None), &msig()).unwrap()]
        );
        assert_eq!(
            concs[0].terms.to_vec(),
            vec![term(&pvar("w", None), &msig()).unwrap()]
        );
        assert!(rest.is_empty());
    }

    #[test]
    fn msr_restrict_formulas_lose_their_markers_and_add_no_match_vars() {
        // HS applies `g = fmap (fmap unpatternVar)` to the embedded
        // restriction formulas (Parser/Sapic.hs:158-160): every `=` marker
        // goes away, and `matchVars` still folds over the premises only.
        // The strip runs BEFORE the locally-nameless formula is built, and
        // the second assertion below is what pins that order — the end-to-end
        // pin is `scripts/divergence_fixtures/sapic_msr_pattern_restrict`.
        let ispec = p::VarSpec {
            name: "i".into(),
            idx: 0,
            sort: LSort::Node,
            typ: None,
        };
        // One template built twice — with the marker and without — so the
        // wrapped leaf is the only delta under test.  `=x = x` at the top and
        // a marker nested under a quantifier inside an action fact's
        // argument, so the strip provably recurses.
        let formulas = |wrap: fn(p::Term) -> p::Term| {
            vec![
                p::Formula::Atom(p::Atom::Eq(wrap(pvar("x", None)), pvar("x", None))),
                p::Formula::Forall(
                    vec![ispec.clone()],
                    Box::new(p::Formula::Atom(p::Atom::Action(
                        pfact("Ev", vec![wrap(pvar("x", None))]),
                        p::Term::Var(ispec.clone()),
                    ))),
                ),
            ]
        };
        let marked = formulas(pat_match);
        let plain = formulas(|t| t);
        let msr = p::Process::Action {
            action: p::SapicAction::Msr {
                prems: vec![pfact("In", vec![pvar("x", None)])],
                acts: vec![],
                concs: vec![pfact("Out", vec![pvar("x", None)])],
                restrictions: marked.clone(),
            },
            body: Box::new(p::Process::Null),
        };
        let Process::Action(
            SapicAction::Msr {
                rest, match_vars, ..
            },
            _,
            _,
        ) = convert_process(&msr, &msig()).unwrap()
        else {
            panic!("expected an Msr action");
        };
        let want: Vec<_> = plain
            .iter()
            .map(|f| sapic_from_parser(f, &msig()).unwrap())
            .collect();
        assert_eq!(rest, want, "both formulas come out marker-free");
        assert!(
            match_vars.is_empty(),
            "a `=` inside `_restrict` contributes no match-var"
        );
        // A marker that survives to the formula builder has no SAPIC term to
        // read it as, so leaving out the strip fails the conversion.
        for f in &marked {
            assert!(
                sapic_from_parser(f, &msig()).is_err(),
                "a `=` marker must not reach the formula builder"
            );
        }
    }

    #[test]
    fn let_and_chin_patterns_split_matched_leaves_out_of_the_bound_term() {
        // HS builds `let` as `ProcessComb (Let (unpattern t1) t2
        // (extractMatchingVariables t1)) mempty p' q` (Parser/Sapic.hs:268-269).
        // HS builds `in(c,pt)` as `ChIn maybeChannel (unpattern pt)
        // (extractMatchingVariables pt)` (Parser/Sapic.hs:113-114). Both sides
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
