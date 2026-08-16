// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
    AcState, AcSym, CSym, Constructability, FunSym, NdcState, NoEqSym, Privacy, EMAP_SYM_STRING,
    MULT_SYM_STRING, MUN_SYM_STRING, NAT_PLUS_SYM_STRING, XOR_SYM_STRING,
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

/// Number of attribute characters between the `tam` prefix and the user-given
/// name: `fun_sym_encode_attr` emits exactly this many, `fun_sym_decode`
/// splits at the same width, and `maude_parse::is_ac_fct_ident` classifies on
/// it (HS `funSymDecode`'s `BC.splitAt 4`, Maude/Parser.hs:92-105).
pub(crate) const ATTR_BLOCK_LEN: usize = 4;

/// Encode privacy / constructability / AC-ness / NDC state into the
/// `ATTR_BLOCK_LEN`-char prefix that follows `tam` for each user-defined
/// symbol.
///
/// HS `funSymEncodeAttr` (Maude/Parser.hs:76-88) concatenates one char per
/// attribute: `Private`->`P` / `Public`->`X`, `Constructor`->`C` /
/// `Destructor`->`D`, `IsAC`->`A` / `NotAC`->`F`, and `IsNDC`->`N` /
/// `NotNDC`->`U` / `IsNDCDiff`->`D` / `IsNDCBoth`->`B`.  All 32
/// concatenations are spelled out so the encoding stays a `&'static str`:
/// the Maude-emission path appends it per printed term, so it must not
/// allocate.
pub fn fun_sym_encode_attr(
    p: Privacy,
    c: Constructability,
    ac: AcState,
    ndc: NdcState,
) -> &'static str {
    use crate::function_symbols::AcState::{IsAc, NotAc};
    use crate::function_symbols::Constructability::{Constructor, Destructor};
    use crate::function_symbols::NdcState::{IsNdc, IsNdcBoth, IsNdcDiff, NotNdc};
    use crate::function_symbols::Privacy::{Private, Public};
    match (p, c, ac, ndc) {
        (Private, Destructor, IsAc, IsNdc) => "PDAN",
        (Private, Destructor, IsAc, NotNdc) => "PDAU",
        (Private, Destructor, IsAc, IsNdcDiff) => "PDAD",
        (Private, Destructor, IsAc, IsNdcBoth) => "PDAB",
        (Private, Destructor, NotAc, IsNdc) => "PDFN",
        (Private, Destructor, NotAc, NotNdc) => "PDFU",
        (Private, Destructor, NotAc, IsNdcDiff) => "PDFD",
        (Private, Destructor, NotAc, IsNdcBoth) => "PDFB",
        (Private, Constructor, IsAc, IsNdc) => "PCAN",
        (Private, Constructor, IsAc, NotNdc) => "PCAU",
        (Private, Constructor, IsAc, IsNdcDiff) => "PCAD",
        (Private, Constructor, IsAc, IsNdcBoth) => "PCAB",
        (Private, Constructor, NotAc, IsNdc) => "PCFN",
        (Private, Constructor, NotAc, NotNdc) => "PCFU",
        (Private, Constructor, NotAc, IsNdcDiff) => "PCFD",
        (Private, Constructor, NotAc, IsNdcBoth) => "PCFB",
        (Public, Destructor, IsAc, IsNdc) => "XDAN",
        (Public, Destructor, IsAc, NotNdc) => "XDAU",
        (Public, Destructor, IsAc, IsNdcDiff) => "XDAD",
        (Public, Destructor, IsAc, IsNdcBoth) => "XDAB",
        (Public, Destructor, NotAc, IsNdc) => "XDFN",
        (Public, Destructor, NotAc, NotNdc) => "XDFU",
        (Public, Destructor, NotAc, IsNdcDiff) => "XDFD",
        (Public, Destructor, NotAc, IsNdcBoth) => "XDFB",
        (Public, Constructor, IsAc, IsNdc) => "XCAN",
        (Public, Constructor, IsAc, NotNdc) => "XCAU",
        (Public, Constructor, IsAc, IsNdcDiff) => "XCAD",
        (Public, Constructor, IsAc, IsNdcBoth) => "XCAB",
        (Public, Constructor, NotAc, IsNdc) => "XCFN",
        (Public, Constructor, NotAc, NotNdc) => "XCFU",
        (Public, Constructor, NotAc, IsNdcDiff) => "XCFD",
        (Public, Constructor, NotAc, IsNdcBoth) => "XCFB",
    }
}

/// Decode a Maude-prefixed identifier back into the original
/// `(name, p, c, ndc)`.  `prefix == "tam"` plus the attribute chars
/// (see [`fun_sym_encode_attr`]) followed by the user-given name.
///
/// HS `funSymDecode` (Maude/Parser.hs:92-105) reads the privacy from char 0, the
/// constructability from char 1 and the NDC state from char 3 — char 2 (the
/// AC state) is not decoded, because the caller already knows from the
/// identifier's shape which of `fAppNoEq`/`fAppACfct` it is building.
pub fn fun_sym_decode(s: &[u8]) -> (Vec<u8>, Privacy, Constructability, NdcState) {
    let prefix_len = FUN_SYM_PREFIX.len();
    if s.len() < prefix_len + ATTR_BLOCK_LEN {
        return (
            s.to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
    }
    let attr = &s[prefix_len..prefix_len + ATTR_BLOCK_LEN];
    let ident = s[prefix_len + ATTR_BLOCK_LEN..].to_vec();
    let priv_ = if attr[0] == b'P' {
        Privacy::Private
    } else {
        Privacy::Public
    };
    let constr = if attr[1] == b'D' {
        Constructability::Destructor
    } else {
        Constructability::Constructor
    };
    let ndc = match attr[3] {
        b'U' => NdcState::NotNdc,
        b'D' => NdcState::IsNdcDiff,
        b'B' => NdcState::IsNdcBoth,
        _ => NdcState::IsNdc,
    };
    (ident, priv_, constr, ndc)
}

/// Replace `-` with `_` (inverse of the identifier `_` -> `-` mapping
/// applied when emitting Maude names).
pub fn replace_minus(s: &[u8]) -> Vec<u8> {
    s.iter()
        .map(|c| if *c == b'-' { b'_' } else { *c })
        .collect()
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
    match o {
        AcSym::Mult => buf.extend_from_slice(MULT_SYM_STRING),
        AcSym::Union => buf.extend_from_slice(MUN_SYM_STRING),
        AcSym::Xor => buf.extend_from_slice(XOR_SYM_STRING),
        AcSym::NatPlus => buf.extend_from_slice(NAT_PLUS_SYM_STRING),
        // A user-defined AC symbol carries its attributes just like a free
        // symbol does; the `A` in the AC slot is what tells the parser to
        // rebuild an AC application rather than a free one.
        AcSym::AcFct(sym) => {
            buf.extend_from_slice(
                fun_sym_encode_attr(sym.privacy, sym.constructability, AcState::IsAc, sym.ndc)
                    .as_bytes(),
            );
            // `replaceUnderscore`: map `_` -> `-`, pushed straight into `buf`.
            buf.extend(sym.name.iter().map(|c| if *c == b'_' { b'-' } else { *c }));
        }
    }
}

/// Append a free symbol's Maude name directly into `buf`.
fn pp_maude_no_eq_sym_into(sym: &NoEqSym, buf: &mut Vec<u8>) {
    buf.extend_from_slice(FUN_SYM_PREFIX.as_bytes());
    buf.extend_from_slice(
        fun_sym_encode_attr(sym.privacy, sym.constructability, AcState::NotAc, sym.ndc).as_bytes(),
    );
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
        Term::App(sym, args) => match sym {
            FunSym::NoEq(s) => {
                pp_maude_no_eq_sym_into(s, buf);
                if !args.is_empty() {
                    pp_args(args, buf);
                }
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
        },
    }
}

fn pp_args(args: &[Term<MaudeLit>], buf: &mut Vec<u8>) {
    buf.push(b'(');
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            buf.push(b',');
        }
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
        // HS `theoryOpEq "DH-neutral  : -> Msg"` (Maude/Parser.hs:223) has TWO
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
        // Match HS `theoryFunSym` (Maude/Parser.hs:264-265) byte-for-byte:
        // `replaceUnderscore s <> " : " <> (concat $ replicate ar "Msg ") <> " -> Msg"`.
        // `args` already ends in a trailing space (or is empty), and the
        // literal " -> Msg" has a leading space, so there are two spaces
        // before `->` for arity>0 (and `name :  -> Msg` for arity 0).
        op_user_head(
            &mut out,
            sym.privacy,
            sym.constructability,
            AcState::NotAc,
            sym.ndc,
            sym.name,
        );
        out.push_str(" : ");
        out.push_str(&args);
        out.push_str(" -> Msg");
        out.push_str(" .\n");
    }
    // User-defined AC symbols, declared `[comm assoc]` so Maude solves modulo
    // AC for them.  `st_ac_fun_syms` is a `BTreeSet`, so iterating it directly
    // yields `AcFctSym`-`Ord` order (HS `S.toList $ stACFunSyms msig`).
    for sym in &msig.st_ac_fun_syms {
        // Match HS `theoryACFunSym` (Maude/Parser.hs:266-267) byte-for-byte:
        // `replaceUnderscore s <> " : " <> (concat $ replicate 2 "Msg ") <> "-> Msg"
        //  <> " [comm assoc]"`.  Unlike `theoryFunSym` above, the sort part has
        // no extra space before `->`, so the line reads
        // `name : Msg Msg -> Msg [comm assoc] .`.
        op_user_head(
            &mut out,
            sym.privacy,
            sym.constructability,
            AcState::IsAc,
            sym.ndc,
            sym.name,
        );
        out.push_str(" : Msg Msg -> Msg [comm assoc] .\n");
    }
    // Rewrite rules.
    for rule in msig.rrules() {
        emit_rrule(&mut out, &rule);
    }
    out.push_str("endfm\n");
    out
}

/// Emit the `  op tam<attrs><name>` head shared by the user-defined free and
/// AC declarations — HS `theoryOp` and `theoryOpACUser` (Maude/Parser.hs:257-260)
/// are the same `"  op " <> funSymPrefix <> attrs <> fsort <> " ."` string.
/// The caller appends the `fsort` tail and the trailing ` .\n`.
///
/// Written piecewise so the `replaceUnderscore` name bytes (`_` -> `-`; names
/// are ASCII) go straight into `out` without a `format!` /
/// `String::from_utf8_lossy` round-trip; the bytes are identical to what the
/// `op(..)` helper produces.
fn op_user_head(
    out: &mut String,
    p: Privacy,
    c: Constructability,
    ac: AcState,
    ndc: NdcState,
    name: &[u8],
) {
    out.push_str("  op ");
    out.push_str(FUN_SYM_PREFIX);
    out.push_str(fun_sym_encode_attr(p, c, ac, ndc));
    for b in name {
        out.push(if *b == b'_' { '-' } else { *b as char });
    }
}

fn op_eq(out: &mut String, name: &str, sort: &str) {
    // HS `theoryOpEq = theoryOp (Just (Public,Constructor,NotAC,NotNDC))`
    // (Maude/Parser.hs:261).
    op(
        out,
        Privacy::Public,
        Constructability::Constructor,
        AcState::NotAc,
        NdcState::NotNdc,
        &format!("{} : {}", name, sort),
    );
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

fn op(out: &mut String, p: Privacy, c: Constructability, ac: AcState, ndc: NdcState, fsort: &str) {
    out.push_str("  op ");
    out.push_str(FUN_SYM_PREFIX);
    out.push_str(fun_sym_encode_attr(p, c, ac, ndc));
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
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, pair_maude_sig};

    #[test]
    fn dh_neutral_op_has_two_spaces_before_colon() {
        // HS `theoryOpEq "DH-neutral  : -> Msg"` (Maude/Parser.hs:223) emits TWO
        // spaces before the colon; the emitted module must match byte-for-byte.
        let s = pp_theory(&dh_maude_sig());
        assert!(s.contains("op tamXCFUDH-neutral  : -> Msg ."));
    }

    /// The whole module the port ships to Maude for the pairing signature,
    /// byte for byte.  Every line is HS `ppTheory`'s (Maude/Parser.hs:176-253):
    /// the fixed preamble, the `enable_nat`-gated sort/subsort/`op t` lines
    /// left out, `op nil  : -> TOP .`'s two spaces, the `stFunSyms` block in
    /// `BTreeSet` order with `theoryFunSym`'s trailing `"Msg "` meeting the
    /// leading space of `" -> Msg"`, then `theoryRule` per rewrite rule with
    /// both sides numbered from ONE shared conversion context (`x0`/`x1`
    /// recur across the rule's two sides, and restart per rule).
    #[test]
    fn theory_for_pair_is_the_pinned_module() {
        assert_eq!(
            pp_theory(&pair_maude_sig()),
            "fmod MSG is\n\
             \x20 protecting NAT .\n\
             \x20 sort Pub Fresh Msg Node TOP .\n\
             \x20 subsort Pub < Msg .\n\
             \x20 subsort Fresh < Msg .\n\
             \x20 subsort Msg < TOP .\n\
             \x20 subsort Node < TOP .\n\
             \x20 op f : Nat -> Fresh .\n\
             \x20 op p : Nat -> Pub .\n\
             \x20 op c : Nat -> Msg .\n\
             \x20 op n : Nat -> Node .\n\
             \x20 op list : TOP -> TOP .\n\
             \x20 op cons : TOP TOP -> TOP .\n\
             \x20 op nil  : -> TOP .\n\
             \x20 op tamXCFUfst : Msg  -> Msg .\n\
             \x20 op tamXCFUpair : Msg Msg  -> Msg .\n\
             \x20 op tamXCFUsnd : Msg  -> Msg .\n\
             \x20 eq tamXCFUfst(tamXCFUpair(x0:Msg,x1:Msg)) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUsnd(tamXCFUpair(x0:Msg,x1:Msg)) = x1:Msg [variant] .\n\
             endfm\n"
        );
    }

    /// The DH module the port ships to Maude, byte for byte, as captured from
    /// the pinned oracle: `DEBUG_MAUDE=1 tamarin-prover dh.spthy` tees the
    /// module Maude is fed to `/tmp/maude.input` (Maude/Process.hs:116-126),
    /// and `dh.spthy` declares `builtins: diffie-hellman` only, so its
    /// signature is HS `dhMaudeSig <> pairMaudeSig` (Maude/Signature.hs:201) --
    /// what the merge below builds.
    ///
    /// This pins what a rule COUNT cannot: the five DH `op` lines in HS source
    /// order (Maude/Parser.hs:222-226), `mult` among them carrying
    /// `[comm assoc]` and NO attribute letters (`theoryOpAC = theoryOp
    /// Nothing`, Maude/Parser.hs:262) where the other four carry `XCFU`; and
    /// all 15 rewrite rules -- the 13 of `dhRules` (Builtin/Rules.hs:47-61)
    /// plus the two pairing rules -- in `Set`-sorted order, each rendered by
    /// `ppMaude` with AC arguments flattened into a single `tammult(..)`
    /// application and both sides numbered from ONE per-rule conversion
    /// context.  Reordering, retyping or renaming any single DH rule moves or
    /// rewrites a line here.
    #[test]
    fn theory_for_dh_is_the_oracle_module() {
        assert_eq!(
            pp_theory(&dh_maude_sig().merge(pair_maude_sig())),
            "fmod MSG is\n\
             \x20 protecting NAT .\n\
             \x20 sort Pub Fresh Msg Node TOP .\n\
             \x20 subsort Pub < Msg .\n\
             \x20 subsort Fresh < Msg .\n\
             \x20 subsort Msg < TOP .\n\
             \x20 subsort Node < TOP .\n\
             \x20 op f : Nat -> Fresh .\n\
             \x20 op p : Nat -> Pub .\n\
             \x20 op c : Nat -> Msg .\n\
             \x20 op n : Nat -> Node .\n\
             \x20 op list : TOP -> TOP .\n\
             \x20 op cons : TOP TOP -> TOP .\n\
             \x20 op nil  : -> TOP .\n\
             \x20 op tamXCFUone : -> Msg .\n\
             \x20 op tamXCFUDH-neutral  : -> Msg .\n\
             \x20 op tamXCFUexp : Msg Msg -> Msg .\n\
             \x20 op tammult : Msg Msg -> Msg [comm assoc] .\n\
             \x20 op tamXCFUinv : Msg -> Msg .\n\
             \x20 op tamXCFUfst : Msg  -> Msg .\n\
             \x20 op tamXCFUpair : Msg Msg  -> Msg .\n\
             \x20 op tamXCFUsnd : Msg  -> Msg .\n\
             \x20 eq tamXCFUexp(x0:Msg,tamXCFUone) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUexp(tamXCFUDH-neutral,x0:Msg) = tamXCFUDH-neutral [variant] .\n\
             \x20 eq tamXCFUexp(tamXCFUexp(x0:Msg,x1:Msg),x2:Msg) = tamXCFUexp(x0:Msg,tammult(x1:Msg,x2:Msg)) [variant] .\n\
             \x20 eq tamXCFUfst(tamXCFUpair(x0:Msg,x1:Msg)) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUinv(tamXCFUinv(x0:Msg)) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUinv(tamXCFUone) = tamXCFUone [variant] .\n\
             \x20 eq tamXCFUinv(tammult(x0:Msg,tamXCFUinv(x1:Msg))) = tammult(x1:Msg,tamXCFUinv(x0:Msg)) [variant] .\n\
             \x20 eq tamXCFUsnd(tamXCFUpair(x0:Msg,x1:Msg)) = x1:Msg [variant] .\n\
             \x20 eq tammult(x0:Msg,x1:Msg,tamXCFUinv(x0:Msg)) = x1:Msg [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUinv(x0:Msg)) = tamXCFUone [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUone) = x0:Msg [variant] .\n\
             \x20 eq tammult(x0:Msg,x1:Msg,tamXCFUinv(tammult(x0:Msg,x2:Msg))) = tammult(x1:Msg,tamXCFUinv(x2:Msg)) [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUinv(tammult(x0:Msg,x1:Msg))) = tamXCFUinv(x1:Msg) [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUinv(x1:Msg),tamXCFUinv(x2:Msg)) = tammult(x0:Msg,tamXCFUinv(tammult(x1:Msg,x2:Msg))) [variant] .\n\
             \x20 eq tammult(tamXCFUinv(x0:Msg),tamXCFUinv(x1:Msg)) = tamXCFUinv(tammult(x0:Msg,x1:Msg)) [variant] .\n\
             endfm\n"
        );
    }

    /// The same oracle capture for a `builtins: bilinear-pairing` theory: HS
    /// `bpMaudeSig <> pairMaudeSig`.  `maudeSig` forces `enableDH` on whenever
    /// `enableBP` is set (Maude/Signature.hs:112), so this is the DH module
    /// plus the two BP `op` lines -- `pmult` a plain `theoryOpEq`, `em` a
    /// `theoryOpC` carrying `[comm]` and no attribute letters
    /// (Maude/Parser.hs:231-232) -- and the three `bpRules`
    /// (Builtin/Rules.hs:71-78) sorted in among the DH ones.
    #[test]
    fn theory_for_bp_is_the_oracle_module() {
        assert_eq!(
            pp_theory(&bp_maude_sig().merge(pair_maude_sig())),
            "fmod MSG is\n\
             \x20 protecting NAT .\n\
             \x20 sort Pub Fresh Msg Node TOP .\n\
             \x20 subsort Pub < Msg .\n\
             \x20 subsort Fresh < Msg .\n\
             \x20 subsort Msg < TOP .\n\
             \x20 subsort Node < TOP .\n\
             \x20 op f : Nat -> Fresh .\n\
             \x20 op p : Nat -> Pub .\n\
             \x20 op c : Nat -> Msg .\n\
             \x20 op n : Nat -> Node .\n\
             \x20 op list : TOP -> TOP .\n\
             \x20 op cons : TOP TOP -> TOP .\n\
             \x20 op nil  : -> TOP .\n\
             \x20 op tamXCFUone : -> Msg .\n\
             \x20 op tamXCFUDH-neutral  : -> Msg .\n\
             \x20 op tamXCFUexp : Msg Msg -> Msg .\n\
             \x20 op tammult : Msg Msg -> Msg [comm assoc] .\n\
             \x20 op tamXCFUinv : Msg -> Msg .\n\
             \x20 op tamXCFUpmult : Msg Msg -> Msg .\n\
             \x20 op tamem : Msg Msg -> Msg [comm] .\n\
             \x20 op tamXCFUfst : Msg  -> Msg .\n\
             \x20 op tamXCFUpair : Msg Msg  -> Msg .\n\
             \x20 op tamXCFUsnd : Msg  -> Msg .\n\
             \x20 eq tamXCFUexp(x0:Msg,tamXCFUone) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUexp(tamXCFUDH-neutral,x0:Msg) = tamXCFUDH-neutral [variant] .\n\
             \x20 eq tamXCFUexp(tamXCFUexp(x0:Msg,x1:Msg),x2:Msg) = tamXCFUexp(x0:Msg,tammult(x1:Msg,x2:Msg)) [variant] .\n\
             \x20 eq tamXCFUfst(tamXCFUpair(x0:Msg,x1:Msg)) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUinv(tamXCFUinv(x0:Msg)) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUinv(tamXCFUone) = tamXCFUone [variant] .\n\
             \x20 eq tamXCFUinv(tammult(x0:Msg,tamXCFUinv(x1:Msg))) = tammult(x1:Msg,tamXCFUinv(x0:Msg)) [variant] .\n\
             \x20 eq tamXCFUpmult(x0:Msg,tamXCFUpmult(x1:Msg,x2:Msg)) = tamXCFUpmult(tammult(x0:Msg,x1:Msg),x2:Msg) [variant] .\n\
             \x20 eq tamXCFUpmult(tamXCFUone,x0:Msg) = x0:Msg [variant] .\n\
             \x20 eq tamXCFUsnd(tamXCFUpair(x0:Msg,x1:Msg)) = x1:Msg [variant] .\n\
             \x20 eq tammult(x0:Msg,x1:Msg,tamXCFUinv(x0:Msg)) = x1:Msg [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUinv(x0:Msg)) = tamXCFUone [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUone) = x0:Msg [variant] .\n\
             \x20 eq tammult(x0:Msg,x1:Msg,tamXCFUinv(tammult(x0:Msg,x2:Msg))) = tammult(x1:Msg,tamXCFUinv(x2:Msg)) [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUinv(tammult(x0:Msg,x1:Msg))) = tamXCFUinv(x1:Msg) [variant] .\n\
             \x20 eq tammult(x0:Msg,tamXCFUinv(x1:Msg),tamXCFUinv(x2:Msg)) = tammult(x0:Msg,tamXCFUinv(tammult(x1:Msg,x2:Msg))) [variant] .\n\
             \x20 eq tammult(tamXCFUinv(x0:Msg),tamXCFUinv(x1:Msg)) = tamXCFUinv(tammult(x0:Msg,x1:Msg)) [variant] .\n\
             \x20 eq tamem(x0:Msg,tamXCFUpmult(x1:Msg,x2:Msg)) = tamXCFUexp(tamem(x0:Msg,x2:Msg),x1:Msg) [variant] .\n\
             endfm\n"
        );
    }

    /// `enable_nat` adds the `TamNat` sort to the `sort` line, a `subsort`
    /// and an `op t` constant, and the `tone`/`tplus` operators — the four
    /// `enableNat` guards of HS `ppTheory` (Maude/Parser.hs:181-186, 190-193,
    /// 204-207, 240-244).
    #[test]
    fn nat_theory_adds_the_tamnat_lines() {
        let s = pp_theory(&crate::maude_sig::nat_maude_sig());
        assert!(s.contains("  sort Pub Fresh Msg Node TamNat TOP .\n"));
        assert!(s.contains("  subsort Fresh < Msg .\n  subsort TamNat < Msg .\n"));
        assert!(s.contains("  op n : Nat -> Node .\n  op t : Nat -> TamNat .\n"));
        assert!(s.contains("  op tamXCFUtone : -> TamNat .\n"));
        assert!(s.contains("  op tamtplus : TamNat TamNat -> TamNat [comm assoc] .\n"));
        // Without it, none of those lines appear.
        let plain = pp_theory(&pair_maude_sig());
        assert!(!plain.contains("TamNat"));
    }

    /// The four builtin AC operators' Maude names.  Each must equal the name
    /// `pp_theory` declares the operator with (`op_ac`'s own literal), or a
    /// query would be headed by an operator the module never declared;
    /// `maude_parse::build_app` matches replies against the same constants.
    #[test]
    fn ac_sym_names() {
        assert_eq!(pp_maude_ac_sym(AcSym::Mult), b"tammult".to_vec());
        assert_eq!(pp_maude_ac_sym(AcSym::Xor), b"tamxor".to_vec());
        assert_eq!(pp_maude_ac_sym(AcSym::Union), b"tammun".to_vec());
        assert_eq!(pp_maude_ac_sym(AcSym::NatPlus), b"tamtplus".to_vec());
        for (op, sig) in [
            (AcSym::Mult, dh_maude_sig()),
            (AcSym::Xor, crate::maude_sig::xor_maude_sig()),
            (AcSym::Union, crate::maude_sig::mset_maude_sig()),
            (AcSym::NatPlus, crate::maude_sig::nat_maude_sig()),
        ] {
            let decl = format!(
                "  op {} : ",
                String::from_utf8(pp_maude_ac_sym(op)).unwrap()
            );
            assert!(pp_theory(&sig).contains(&decl), "no `{decl}` declaration");
        }
    }

    /// The absolute letters of the attribute block (HS `funSymEncodeAttr`,
    /// Maude/Parser.hs:76-88) — what actually goes on the wire.
    /// `every_attribute_quadruple_round_trips_through_decode` pins encode
    /// only against its own decode, so a letter renamed on BOTH sides
    /// survives it; these two spellings anchor the alphabet.
    #[test]
    fn encode_attr_spells_the_haskell_letters() {
        assert_eq!(
            fun_sym_encode_attr(
                Privacy::Public,
                Constructability::Constructor,
                AcState::NotAc,
                NdcState::NotNdc
            ),
            "XCFU"
        );
        assert_eq!(
            fun_sym_encode_attr(
                Privacy::Private,
                Constructability::Destructor,
                AcState::IsAc,
                NdcState::IsNdcBoth
            ),
            "PDAB"
        );
    }

    /// Every one of the 32 attribute quadruples `fun_sym_encode_attr` spells
    /// out survives a `tam` + attributes + name identifier being handed back
    /// to `fun_sym_decode`, and the 32 encodings are pairwise distinct.
    ///
    /// The encoding is four independent injective maps concatenated, so
    /// distinctness is a table invariant; together with the round trip it
    /// pins each of the 32 arms against a transposed letter, which otherwise
    /// only surfaces when Maude echoes a symbol back carrying the wrong
    /// privacy / constructability / NDC flags.  The AC slot is not part of
    /// the decoded triple — HS `funSymDecode` reads chars 0/1/3 only
    /// (Maude/Parser.hs:92-105), because the caller already knows from the
    /// identifier's shape which symbol kind it is rebuilding.
    #[test]
    fn every_attribute_quadruple_round_trips_through_decode() {
        let mut seen: std::collections::BTreeSet<&'static str> = Default::default();
        for p in [Privacy::Private, Privacy::Public] {
            for c in [Constructability::Constructor, Constructability::Destructor] {
                for ac in [AcState::IsAc, AcState::NotAc] {
                    for ndc in [
                        NdcState::IsNdc,
                        NdcState::NotNdc,
                        NdcState::IsNdcDiff,
                        NdcState::IsNdcBoth,
                    ] {
                        let attr = fun_sym_encode_attr(p, c, ac, ndc);
                        assert_eq!(attr.len(), ATTR_BLOCK_LEN, "{attr:?} is not 4 chars");
                        assert!(seen.insert(attr), "{attr:?} encodes two quadruples");
                        let mut ident = FUN_SYM_PREFIX.as_bytes().to_vec();
                        ident.extend_from_slice(attr.as_bytes());
                        ident.extend_from_slice(b"x");
                        assert_eq!(
                            fun_sym_decode(&ident),
                            (b"x".to_vec(), p, c, ndc),
                            "attribute block {attr:?} for {p:?}/{c:?}/{ac:?}/{ndc:?}"
                        );
                    }
                }
            }
        }
        assert_eq!(seen.len(), 32);
    }

    /// A user-defined AC symbol is declared `[comm assoc]`, with a single
    /// space before `->` (unlike the free-symbol declarations, which carry a
    /// trailing space in the argument list AND a leading one before `->`).
    #[test]
    fn ac_user_fun_sym_op_line() {
        use crate::function_symbols::AcFctSym;
        let f = AcFctSym::new(
            b"my_op".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        let sig = MaudeSig {
            st_ac_fun_syms: [f].into_iter().collect(),
            ..MaudeSig::default()
        }
        .refresh();
        let s = pp_theory(&sig);
        assert!(
            s.contains("  op tamXCAUmy-op : Msg Msg -> Msg [comm assoc] .\n"),
            "got: {}",
            s
        );
        assert_eq!(pp_maude_ac_sym(AcSym::AcFct(f)), b"tamXCAUmy-op".to_vec());
    }
}
