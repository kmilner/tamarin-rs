// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.Warnings` (`lib/sapic/src/Sapic/Warnings.hs`).
//!
//! `checkWellformedness = concatMap (toWfErrorReport . warnProcess) . theoryProcesses`
//! (Warnings.hs:37-38) runs the SAPIC-specific wellformedness checks on every
//! `process:` of an `OpenTheory`, *after parsing but before annotation /
//! `typeTheory`* — i.e. on the `Process ProcessParsedAnnotation SapicLVar`.
//!
//! `warnProcess p = map WFBoundTwice (capturedVariables p) <> toList (checkLocks p)`
//! (Warnings.hs:17-21).  Each `WFerror` becomes a report pair
//! `("Wellformedness-error in Process", show e)` (`toWfErrorReport`,
//! Warnings.hs:24-27).
//!
//! Currently ported: the **bound-twice** check (`map WFBoundTwice
//! (capturedVariables p)`).  `checkLocks` (the sibling lock-matching check) is
//! NOT ported here — see the note on [`warn_process`].

use tamarin_parser::wf::WfError;

use tamarin_theory::sapic::{GoodAnnotation, Process, SapicLVar};

use crate::bindings::captured_variables;

/// The fixed topic HS `toWfErrorReport` attaches to every SAPIC process error
/// (Warnings.hs:24-27, see line 27).  Rendered verbatim (NOT underlined) by
/// `prettyWfErrorReport` (Wellformedness.hs:118-125).
pub const SAPIC_PROCESS_TOPIC: &str = "Wellformedness-error in Process";

/// `warnProcess` (Warnings.hs:17-21): the list of `WFerror`s for one process.
///
/// HS: `map WFBoundTwice (capturedVariables p) <> toList (checkLocks p)`.
///
/// We port the `WFBoundTwice` arm fully (`captured_variables`).  The
/// `checkLocks p` arm is **deferred**: it re-runs the lock-annotation pass
/// (`annotateLocks'`) on a `toAnProcess p` and reports `WFUnAnnotatedLock`
/// when an `unlock` has no matching enclosing `lock`, or surfaces a
/// `ProcessNotWellformed (WFLock {WFRep,WFPar})` thrown by the annotation.  No
/// in-corpus file currently exercises this warning (the lock-annotation pass
/// `crate::locks::annotate_locks` is the analogous machinery, run later in the
/// pipeline; only its `Rep`/`Par` *hard error* path is wired up).  Porting it
/// would require an `annotateLocks'`-style pass that returns the unmatched-
/// unlock predicate rather than throwing — left out to avoid emitting spurious
/// lock warnings.
pub fn warn_process<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<WfError> {
    captured_variables(p)
        .iter()
        .map(|v| {
            // `show (WFBoundTwice v) = "Variable bound twice: " ++ show v ++ "."`
            // (Sapic/Exceptions.hs:117-118).
            let body = format!("Variable bound twice: {}.", show_sapic_lvar(v));
            // `toWfErrorReport` (Warnings.hs:24-27) pairs each error with the
            // topic; `prettyWfErrorReport` (Wellformedness.hs:118-125) renders
            // a topic GROUP as `text topic $-$ nest 2 (vcat (intersperse "")
            // bodies)` — the topic header ONCE, then each body 2-space-indented
            // and separated by a blank line.  We emit ONE `WfError` per error
            // (so `wf_report.len()` matches HS `length report` for the trailing
            // `N wellformedness check failed` summary); the message is the bare
            // 2-space-indented body.  The header is printed once by
            // `format_wf_block`'s headerless path (keyed on this topic).
            WfError::new(SAPIC_PROCESS_TOPIC, format!("  {body}"))
        })
        .collect()
}

/// `Sapic.checkWellformedness` (Warnings.hs:37-38) for a single process:
/// `toWfErrorReport . warnProcess`.  The caller concatenates the result over
/// every `theoryProcesses` (here: the single top-level process).
pub fn check_wellformedness<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<WfError> {
    warn_process(p)
}

/// `show (SapicLVar v stype)` (Theory/Sapic/Term.hs:108-110):
/// `show v ++ maybe "" (":" ++)` — the HS-faithful `Show LVar`
/// (LTerm.hs:526-533) with the optional `:type` suffix.
fn show_sapic_lvar(v: &SapicLVar) -> String {
    let base = show_lvar(&v.var);
    match &v.stype {
        Some(t) => format!("{base}:{t}"),
        None => base,
    }
}

/// `show (LVar v s i)` (Term/LTerm.hs:526-533):
/// `sortPrefix s ++ body`, where `body = show i` if the name is empty,
/// `v` if `i == 0`, else `v ++ "." ++ show i`.
fn show_lvar(v: &tamarin_term::lterm::LVar) -> String {
    let pre = tamarin_term::lterm::sort_prefix(v.sort);
    if v.name.is_empty() {
        format!("{pre}{}", v.idx)
    } else if v.idx == 0 {
        format!("{pre}{}", v.name)
    } else {
        format!("{pre}{}.{}", v.name, v.idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_theory::sapic::{Process, ProcessParsedAnnotation, SapicAction};

    fn msg_var(name: &str) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, LSort::Msg, 0))
    }

    fn null() -> Process<ProcessParsedAnnotation, SapicLVar> {
        Process::null(ProcessParsedAnnotation::empty())
    }

    fn new_action(
        v: SapicLVar,
        body: Process<ProcessParsedAnnotation, SapicLVar>,
    ) -> Process<ProcessParsedAnnotation, SapicLVar> {
        Process::Action(
            SapicAction::New(v),
            ProcessParsedAnnotation::empty(),
            Box::new(body),
        )
    }

    #[test]
    fn bound_twice_emits_one_warning() {
        // `new x; new x` — x captured once.  This is the `boundonce2.spthy`
        // case: HS emits exactly one `Variable bound twice: x.` warning.
        let x = msg_var("x");
        let p = new_action(x.clone(), new_action(x, null()));
        let rep = check_wellformedness(&p);
        assert_eq!(rep.len(), 1);
        assert_eq!(rep[0].topic, SAPIC_PROCESS_TOPIC);
        // The header is added once by the report formatter; the per-error
        // message is the bare 2-space-indented body.
        assert_eq!(rep[0].message, "  Variable bound twice: x.");
    }

    #[test]
    fn distinct_sequential_binders_are_fine() {
        // `new x; new y` — no capture.
        let p = new_action(msg_var("x"), new_action(msg_var("y"), null()));
        assert!(check_wellformedness(&p).is_empty());
    }

    /// Every branch of HS `Show (SapicLVar)` / `Show LVar`
    /// (Theory/Sapic/Term.hs:108-110, Term/LTerm.hs:526-533), since the result
    /// is spliced verbatim into the `Variable bound twice: …` report body.
    #[test]
    fn show_sapic_lvar_matches_hs_show() {
        let show = |name: &str, sort, idx, ty: Option<&str>| {
            show_sapic_lvar(&SapicLVar::new(
                LVar::new(name, sort, idx),
                ty.map(str::to_string),
            ))
        };
        for (label, got, want) in [
            (
                "msg sort has no prefix",
                show("x", LSort::Msg, 0, None),
                "x",
            ),
            ("fresh prefix", show("k", LSort::Fresh, 0, None), "~k"),
            ("pub prefix", show("a", LSort::Pub, 0, None), "$a"),
            ("node prefix", show("i", LSort::Node, 0, None), "#i"),
            ("nat prefix", show("n", LSort::Nat, 0, None), "%n"),
            // `i /= 0` appends `.i`; an EMPTY name renders the index alone.
            ("nonzero index", show("x", LSort::Msg, 2, None), "x.2"),
            ("indexed fresh", show("k", LSort::Fresh, 1, None), "~k.1"),
            (
                "empty name is the index",
                show("", LSort::Msg, 7, None),
                "7",
            ),
            (
                "type suffix",
                show("m", LSort::Msg, 0, Some("bitstring")),
                "m:bitstring",
            ),
            (
                "prefix, index and type together",
                show("m", LSort::Fresh, 3, Some("lol")),
                "~m.3:lol",
            ),
        ] {
            assert_eq!(got, want, "{label}");
        }
    }
}
