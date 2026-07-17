// Currently GPL 3.0 until granted permission by the following authors:
//   Benedikt Schmidt, Jannik Dreier, Robert Künnemann, Philip Lukert, and
//   other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Maude/Parser.hs

//! Port of `Term.Maude.Parser`'s pretty-printing portion (Maude module
//! emission and term formatting). The parsing portion lives in
//! [`crate::maude_parse`].
//!
//! This module produces:
//! - `pp_theory(&MaudeSig) -> String`: a `fmod MSG is … endfm` module that
//!   declares the term algebra, AC operators, and rewriting rules.
//! - `pp_mterm(&Term<MaudeLit>) -> Vec<u8>`: a Maude-syntax rendering of a
//!   term used in queries.

use crate::function_symbols::{
    AcSym, CSym, Constructability, FunSym, NoEqSym, Privacy,
    EMAP_SYM_STRING, MULT_SYM_STRING, MUN_SYM_STRING,
    NAT_PLUS_SYM_STRING, XOR_SYM_STRING,
};
use crate::lterm::LSort;
use crate::maude_sig::MaudeSig;
use crate::maude_types::MaudeLit;
use crate::rewriting::RRule;
use crate::term::Term;

// =============================================================================
// Sort / symbol formatting
// =============================================================================

/// `ppLSort`: long-form sort name as it appears in the Maude module.
pub fn pp_lsort(s: LSort) -> &'static str {
    match s {
        LSort::Pub => "Pub",
        LSort::Fresh => "Fresh",
        LSort::Msg => "Msg",
        LSort::Nat => "TamNat",
        LSort::Node => "Node",
    }
}

/// `ppLSortSym`: single-letter constant constructor for each sort.
pub fn pp_lsort_sym(s: LSort) -> &'static str {
    match s {
        LSort::Fresh => "f",
        LSort::Pub => "p",
        LSort::Msg => "c",
        LSort::Node => "n",
        LSort::Nat => "t",
    }
}

pub fn parse_lsort_sym(s: &str) -> Option<LSort> {
    match s {
        "f" => Some(LSort::Fresh),
        "p" => Some(LSort::Pub),
        "c" => Some(LSort::Msg),
        "n" => Some(LSort::Node),
        "t" => Some(LSort::Nat),
        _ => None,
    }
}

/// Prefix every user-defined function symbol with `tam` so it never clashes
/// with Maude's own syntax (e.g. `true`, `not`, `if`).
pub const FUN_SYM_PREFIX: &str = "tam";

/// Encode privacy / constructability into a 2-char prefix that follows
/// `tam` for each NoEq symbol.
pub fn fun_sym_encode_attr(p: Privacy, c: Constructability) -> &'static str {
    match (p, c) {
        (Privacy::Private, Constructability::Destructor) => "PD",
        (Privacy::Private, Constructability::Constructor) => "PC",
        (Privacy::Public,  Constructability::Destructor)  => "XD",
        (Privacy::Public,  Constructability::Constructor) => "XC",
    }
}

/// Decode a Maude-prefixed identifier back into the original `(name, p, c)`.
/// `prefix == "tam<PC|PD|XC|XD>"` followed by the user-given name.
pub fn fun_sym_decode(s: &[u8]) -> (Vec<u8>, Privacy, Constructability) {
    let prefix_len = FUN_SYM_PREFIX.len();
    if s.len() < prefix_len + 2 {
        return (s.to_vec(), Privacy::Public, Constructability::Constructor);
    }
    let attr = &s[prefix_len..prefix_len + 2];
    let ident = s[prefix_len + 2..].to_vec();
    let (priv_, constr) = match attr {
        b"PD" => (Privacy::Private, Constructability::Destructor),
        b"PC" => (Privacy::Private, Constructability::Constructor),
        b"XD" => (Privacy::Public,  Constructability::Destructor),
        _      => (Privacy::Public,  Constructability::Constructor),
    };
    (ident, priv_, constr)
}

/// Replace `-` with `_` (inverse of the identifier `_` -> `-` mapping
/// applied when emitting Maude names).
pub fn replace_minus(s: &[u8]) -> Vec<u8> {
    s.iter().map(|c| if *c == b'-' { b'_' } else { *c }).collect()
}

/// AC operator's Maude name (with `tam` prefix).
pub fn pp_maude_ac_sym(o: AcSym) -> Vec<u8> {
    let mut v = Vec::new();
    pp_maude_ac_sym_into(o, &mut v);
    v
}

/// Append an AC operator's Maude name directly into `buf`.
fn pp_maude_ac_sym_into(o: AcSym, buf: &mut Vec<u8>) {
    buf.extend_from_slice(FUN_SYM_PREFIX.as_bytes());
    let s: &[u8] = match o {
        AcSym::Mult => MULT_SYM_STRING,
        AcSym::Union => MUN_SYM_STRING,
        AcSym::Xor => XOR_SYM_STRING,
        AcSym::NatPlus => NAT_PLUS_SYM_STRING,
    };
    buf.extend_from_slice(s);
}

/// Append a free symbol's Maude name directly into `buf`.
fn pp_maude_no_eq_sym_into(sym: &NoEqSym, buf: &mut Vec<u8>) {
    buf.extend_from_slice(FUN_SYM_PREFIX.as_bytes());
    buf.extend_from_slice(fun_sym_encode_attr(sym.privacy, sym.constructability).as_bytes());
    // `replaceUnderscore`: map `_` -> `-`, pushed straight into `buf`.
    buf.extend(sym.name.iter().map(|c| if *c == b'_' { b'-' } else { *c }));
}

/// Append a C-symbol's Maude name directly into `buf`.
fn pp_maude_c_sym_into(c: CSym, buf: &mut Vec<u8>) {
    match c {
        CSym::EMap => {
            buf.extend_from_slice(FUN_SYM_PREFIX.as_bytes());
            buf.extend_from_slice(EMAP_SYM_STRING);
        }
    }
}

// =============================================================================
// Term pretty printing
// =============================================================================

/// Render a Maude term as bytes.
pub fn pp_mterm(t: &Term<MaudeLit>) -> Vec<u8> {
    let mut buf = Vec::new();
    pp_mterm_into(t, &mut buf);
    buf
}

/// Render a `list(...)`-headed Maude term directly from a borrowed slice
/// of elements, avoiding the `Vec`+`Arc` allocation a `Term::App(List, ..)`
/// would require.  Byte-identical to `pp_mterm(&Term::App(FunSym::List, items))`.
pub fn pp_mterm_list(items: &[Term<MaudeLit>]) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(b"list(");
    pp_list(items, &mut buf);
    buf.push(b')');
    buf
}

fn pp_mterm_into(t: &Term<MaudeLit>, buf: &mut Vec<u8>) {
    match t {
        Term::Lit(MaudeLit::MaudeVar(i, sort)) => {
            buf.push(b'x');
            buf.extend(i.to_string().as_bytes());
            buf.push(b':');
            buf.extend(pp_lsort(*sort).as_bytes());
        }
        Term::Lit(MaudeLit::MaudeConst(i, sort)) => {
            buf.extend(pp_lsort_sym(*sort).as_bytes());
            buf.push(b'(');
            buf.extend(i.to_string().as_bytes());
            buf.push(b')');
        }
        Term::Lit(MaudeLit::FreshVar(_, _)) => {
            // Should not appear in queries we send. Match Haskell's panic.
            panic!("pp_mterm: FreshVar must not appear in outgoing terms");
        }
        Term::App(sym, args) => {
            match sym {
                FunSym::NoEq(s) => {
                    pp_maude_no_eq_sym_into(s, buf);
                    if !args.is_empty() { pp_args(args, buf); }
                }
                FunSym::C(c) => {
                    pp_maude_c_sym_into(*c, buf);
                    pp_args(args, buf);
                }
                FunSym::Ac(op) => {
                    pp_maude_ac_sym_into(*op, buf);
                    pp_args(args, buf);
                }
                FunSym::List => {
                    buf.extend_from_slice(b"list(");
                    pp_list(args, buf);
                    buf.push(b')');
                }
            }
        }
    }
}

fn pp_args(args: &[Term<MaudeLit>], buf: &mut Vec<u8>) {
    buf.push(b'(');
    for (i, a) in args.iter().enumerate() {
        if i > 0 { buf.push(b','); }
        pp_mterm_into(a, buf);
    }
    buf.push(b')');
}

fn pp_list(args: &[Term<MaudeLit>], buf: &mut Vec<u8>) {
    if args.is_empty() {
        buf.extend_from_slice(b"nil");
        return;
    }
    buf.extend_from_slice(b"cons(");
    pp_mterm_into(&args[0], buf);
    buf.push(b',');
    pp_list(&args[1..], buf);
    buf.push(b')');
}

// =============================================================================
// Theory module emission
// =============================================================================

/// Generate the Maude functional module describing the term algebra,
/// AC operators, and rewriting rules for the given signature.
pub fn pp_theory(msig: &MaudeSig) -> String {
    let mut out = String::new();
    out.push_str("fmod MSG is\n");
    out.push_str("  protecting NAT .\n");
    if msig.enable_nat {
        out.push_str("  sort Pub Fresh Msg Node TamNat TOP .\n");
    } else {
        out.push_str("  sort Pub Fresh Msg Node TOP .\n");
    }
    out.push_str("  subsort Pub < Msg .\n");
    out.push_str("  subsort Fresh < Msg .\n");
    if msig.enable_nat {
        out.push_str("  subsort TamNat < Msg .\n");
    }
    out.push_str("  subsort Msg < TOP .\n");
    out.push_str("  subsort Node < TOP .\n");
    // Constants.
    out.push_str("  op f : Nat -> Fresh .\n");
    out.push_str("  op p : Nat -> Pub .\n");
    out.push_str("  op c : Nat -> Msg .\n");
    out.push_str("  op n : Nat -> Node .\n");
    if msig.enable_nat {
        out.push_str("  op t : Nat -> TamNat .\n");
    }
    // List encoding.
    out.push_str("  op list : TOP -> TOP .\n");
    out.push_str("  op cons : TOP TOP -> TOP .\n");
    out.push_str("  op nil  : -> TOP .\n");
    if msig.enable_mset {
        op_ac(&mut out, "mun", "Msg Msg -> Msg");
    }
    if msig.enable_dh {
        op_eq(&mut out, "one", "-> Msg");
        // HS `theoryOpEq "DH-neutral  : -> Msg"` (Parser.hs:209) has TWO
        // spaces before the colon; the trailing space on the name reproduces
        // that so `format!("{} : {}")` yields `DH-neutral  : -> Msg`.
        op_eq(&mut out, "DH-neutral ", "-> Msg");
        op_eq(&mut out, "exp", "Msg Msg -> Msg");
        op_ac(&mut out, "mult", "Msg Msg -> Msg");
        op_eq(&mut out, "inv", "Msg -> Msg");
    }
    if msig.enable_bp {
        op_eq(&mut out, "pmult", "Msg Msg -> Msg");
        op_c(&mut out, "em", "Msg Msg -> Msg");
    }
    if msig.enable_xor {
        op_eq(&mut out, "zero", "-> Msg");
        op_ac(&mut out, "xor", "Msg Msg -> Msg");
    }
    if msig.enable_nat {
        op_eq(&mut out, "tone", "-> TamNat");
        op_ac(&mut out, "tplus", "TamNat TamNat -> TamNat");
    }
    // User-defined free symbols.  `st_fun_syms` is a `BTreeSet`, so
    // iterating it directly already yields the symbols deduplicated and
    // in `NoEqSym`-`Ord` order.
    for sym in &msig.st_fun_syms {
        let args = "Msg ".repeat(sym.arity);
        // Match HS `theoryFunSym` (Parser.hs:247) byte-for-byte:
        // `replaceUnderscore s <> " : " <> (concat $ replicate ar "Msg ") <> " -> Msg"`.
        // `args` already ends in a trailing space (or is empty), and the
        // literal " -> Msg" has a leading space, so there are two spaces
        // before `->` for arity>0 (and `name :  -> Msg` for arity 0).
        // Emit the op line piecewise so the `replaceUnderscore` name bytes go
        // straight into `out` without a `format!`/`String::from_utf8_lossy`
        // round-trip; the resulting bytes are identical to the `op(..)` helper.
        out.push_str("  op ");
        out.push_str(FUN_SYM_PREFIX);
        out.push_str(fun_sym_encode_attr(sym.privacy, sym.constructability));
        // `replaceUnderscore`: map `_` -> `-` (names are ASCII).
        for b in sym.name.iter() {
            out.push(if *b == b'_' { '-' } else { *b as char });
        }
        out.push_str(" : ");
        out.push_str(&args);
        out.push_str(" -> Msg");
        out.push_str(" .\n");
    }
    // Rewrite rules.
    for rule in msig.rrules() {
        emit_rrule(&mut out, &rule);
    }
    out.push_str("endfm\n");
    out
}

fn op_eq(out: &mut String, name: &str, sort: &str) {
    op(out, Privacy::Public, Constructability::Constructor,
       &format!("{} : {}", name, sort));
}

fn op_ac(out: &mut String, name: &str, sort: &str) {
    out.push_str("  op ");
    out.push_str(FUN_SYM_PREFIX);
    out.push_str(name);
    out.push_str(" : ");
    out.push_str(sort);
    out.push_str(" [comm assoc] .\n");
}

fn op_c(out: &mut String, name: &str, sort: &str) {
    out.push_str("  op ");
    out.push_str(FUN_SYM_PREFIX);
    out.push_str(name);
    out.push_str(" : ");
    out.push_str(sort);
    out.push_str(" [comm] .\n");
}

fn op(out: &mut String, p: Privacy, c: Constructability, fsort: &str) {
    out.push_str("  op ");
    out.push_str(FUN_SYM_PREFIX);
    out.push_str(fun_sym_encode_attr(p, c));
    out.push_str(fsort);
    out.push_str(" .\n");
}

fn emit_rrule(out: &mut String, rule: &RRule<crate::lterm::LNTerm>) {
    use crate::maude_types::lterm_to_mterm_global;
    // Convert LNTerm rule sides to MTerm. The same conversion context
    // is used for both sides so variables are shared.
    let mut ctx = crate::maude_types::ConvCtx::new();
    let lm = lterm_to_mterm_global(&rule.lhs, &mut ctx);
    let rm = lterm_to_mterm_global(&rule.rhs, &mut ctx);
    out.push_str("  eq ");
    out.push_str(&String::from_utf8_lossy(&pp_mterm(&lm)));
    out.push_str(" = ");
    out.push_str(&String::from_utf8_lossy(&pp_mterm(&rm)));
    out.push_str(" [variant] .\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::maude_sig::{dh_maude_sig, pair_maude_sig};

    #[test]
    fn dh_neutral_op_has_two_spaces_before_colon() {
        // HS `theoryOpEq "DH-neutral  : -> Msg"` (Parser.hs:209) emits TWO
        // spaces before the colon; the emitted module must match byte-for-byte.
        let s = pp_theory(&dh_maude_sig());
        assert!(s.contains("op tamXCDH-neutral  : -> Msg ."));
        // Guard against accidentally emitting only a single space.
        assert!(!s.contains("op tamXCDH-neutral : -> Msg ."));
    }

    #[test]
    fn theory_for_pair_is_well_formed() {
        let s = pp_theory(&pair_maude_sig());
        assert!(s.starts_with("fmod MSG is\n"));
        assert!(s.contains("op f : Nat -> Fresh ."));
        assert!(s.ends_with("endfm\n"));
    }

    #[test]
    fn ac_sym_names() {
        assert_eq!(pp_maude_ac_sym(AcSym::Mult), b"tammult".to_vec());
        assert_eq!(pp_maude_ac_sym(AcSym::Xor), b"tamxor".to_vec());
    }
}
