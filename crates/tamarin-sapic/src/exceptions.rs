// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The wellformedness errors of `Sapic.Exceptions`
//! (lib/sapic/src/Sapic/Exceptions.hs) and their `Show` texts, which reach
//! the user verbatim: an uncaught exception prints as `tamarin-prover: <show>`.

use std::collections::BTreeSet;
use std::fmt;

use tamarin_term::function_symbols::{
    plain_show_bytes, show_acfct_sym, show_constructability, show_ndc_state, show_privacy,
    UserDefinedSym,
};
use tamarin_term::lterm::{LVar, Name};
use tamarin_term::term::{show_term, ShowLit};
use tamarin_term::vterm::Lit;
use tamarin_theory::pretty_hpj::Doc;
use tamarin_theory::pretty_sapic::{pretty_sapic_no_loc, render_sapic};
use tamarin_theory::sapic::{Process, SapicLVar, SapicTerm, SapicType};

/// HS `WFLockTag` (Sapic/Exceptions.hs).
#[derive(Debug, Clone, Copy)]
pub(crate) enum WfLockTag {
    Rep,
    Par,
}

/// HS `SapicFunType = ([SapicType], SapicType)`.
pub(crate) type SapicFunType = (Vec<SapicType>, SapicType);

/// HS `WFerror` (Sapic/Exceptions.hs), restricted to the variants the port
/// raises.
#[derive(Debug, Clone)]
pub(crate) enum WfError {
    Lock(WfLockTag),
    Unbound(BTreeSet<LVar>),
    Reliable,
    BoundTwice(SapicLVar),
    /// `TypingError t at tt`: term, actual type, expected type.
    Typing(SapicTerm, SapicType, SapicType),
    FunctionMerge(UserDefinedSym, SapicFunType, SapicFunType),
}

/// HS `show` at `Maybe String`.
fn show_sapic_type(t: &SapicType) -> String {
    match t {
        Some(s) => format!("Just {s:?}"),
        None => "Nothing".to_string(),
    }
}

/// HS `prettySapicFunType` (Theory/Sapic/Term.hs).
fn pretty_sapic_fun_type((ins, out): &SapicFunType) -> String {
    let ins: Vec<String> = ins.iter().map(show_sapic_type).collect();
    format!("{} -> {}", ins.join(" * "), show_sapic_type(out))
}

/// Derived `Show UserDefinedSym` (Term/Term/FunctionSymbols.hs).
fn show_user_defined_sym(sym: &UserDefinedSym) -> String {
    match sym {
        UserDefinedSym::NoEqUser(s) => format!(
            "NoEqUser (\"{}\",({},{},{},{}))",
            plain_show_bytes(s.name),
            s.arity,
            show_privacy(s.privacy),
            show_constructability(s.constructability),
            show_ndc_state(s.ndc)
        ),
        UserDefinedSym::AcFctUser(s) => format!("ACfctUser {}", show_acfct_sym(s)),
    }
}

/// A `SapicTerm` literal under HS `Show (Lit Name SapicLVar)`: `Show Name`,
/// or `Show SapicLVar` (Theory/Sapic/Term.hs), the variable then `:type`.
/// Its order is the literal's, so re-wrapping a term keeps its AC order.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SapicLit(Lit<Name, SapicLVar>);

impl ShowLit for SapicLit {
    fn show_into(&self, out: &mut String) {
        match &self.0 {
            Lit::Con(n) => Lit::<Name, LVar>::Con(*n).show_into(out),
            Lit::Var(v) => {
                Lit::<Name, LVar>::Var(v.var).show_into(out);
                if let Some(t) = &v.stype {
                    out.push(':');
                    out.push_str(t);
                }
            }
        }
    }
}

/// HS `show` at `SapicTerm` (Term/Term/Raw.hs).
fn show_sapic_term(t: &SapicTerm) -> String {
    show_term(&tamarin_term::term::map_lits(t, &mut |l| {
        SapicLit(l.clone())
    }))
}

impl fmt::Display for WfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WfError::Unbound(vars) => {
                let vars: Vec<String> = vars.iter().map(|v| v.to_string()).collect();
                write!(f, "The variable(s) {} are not bound.", vars.join(", "))
            }
            WfError::Reliable => f.write_str(
                "If reliable channels are activated, processes should only contain \
                 in('r',m), out('r',m), in('c',m) or out('c',m) for communication.",
            ),
            WfError::Lock(tag) => {
                let tag = match tag {
                    WfLockTag::Rep => "replication",
                    WfLockTag::Par => "a parallel",
                };
                write!(
                    f,
                    "Process contains lock that extends over {tag} which is not allowed."
                )
            }
            WfError::BoundTwice(v) => write!(f, "Variable bound twice: {v}."),
            WfError::Typing(t, at, tt) => write!(
                f,
                "Typing error: expected term {} to have {} but actual type is {}.",
                show_sapic_term(t),
                show_sapic_type(tt),
                show_sapic_type(at)
            ),
            WfError::FunctionMerge(fs, t1, t2) => write!(
                f,
                "Typing error: function types for function{} are compatible. \
                 Expected type {} but actual type is {}.",
                show_user_defined_sym(fs),
                pretty_sapic_fun_type(t1),
                pretty_sapic_fun_type(t2)
            ),
        }
    }
}

/// HS `show (ProcessNotWellformed e (Just p))` (Sapic/Exceptions.hs):
/// `"Process not well-formed: " ++ render (text (show e) $-$ nest 2
/// (prettySapicNoLoc p))`.
pub(crate) fn process_not_wellformed<Ann>(e: &WfError, p: &Process<Ann, SapicLVar>) -> String {
    let doc = Doc::text(e.to_string()).above_g(pretty_sapic_no_loc(p).nest(2));
    format!("Process not well-formed: {}", render_sapic(doc))
}
