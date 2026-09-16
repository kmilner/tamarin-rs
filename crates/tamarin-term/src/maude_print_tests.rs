// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::maude_sig::{bp_maude_sig, dh_maude_sig, pair_maude_sig};

fn reference(t: &Term<MaudeLit>, buf: &mut Vec<u8>) {
    match t {
        Term::Lit(MaudeLit::MaudeVar(i, sort)) => {
            buf.push(b'x');
            push_u64(*i, buf);
            buf.push(b':');
            buf.extend(pp_lsort(*sort).as_bytes());
        }
        Term::Lit(MaudeLit::MaudeConst(i, sort)) => {
            buf.extend(pp_lsort_sym(*sort).as_bytes());
            buf.push(b'(');
            push_u64(*i, buf);
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
                    reference_args(args, buf);
                }
            }
            FunSym::C(c) => {
                pp_maude_c_sym_into(*c, buf);
                reference_args(args, buf);
            }
            FunSym::Ac(op) => {
                pp_maude_ac_sym_into(*op, buf);
                reference_args(args, buf);
            }
            FunSym::List => {
                buf.extend_from_slice(b"list(");
                reference_list(args, buf);
                buf.push(b')');
            }
        },
    }
}

fn reference_args(args: &[Term<MaudeLit>], buf: &mut Vec<u8>) {
    buf.push(b'(');
    for (i, arg) in args.iter().enumerate() {
        if i != 0 {
            buf.push(b',');
        }
        reference(arg, buf);
    }
    buf.push(b')');
}
fn reference_list(args: &[Term<MaudeLit>], buf: &mut Vec<u8>) {
    for arg in args {
        buf.extend_from_slice(b"cons(");
        reference(arg, buf);
        buf.push(b',');
    }
    buf.extend_from_slice(b"nil");
    buf.extend(std::iter::repeat_n(b')', args.len()));
}
#[test]
fn maude_writer_matches_reference_wire_format() {
    let mut terms = vec![
        Term::Lit(MaudeLit::MaudeVar(u64::MAX, LSort::Msg)),
        Term::Lit(MaudeLit::MaudeConst(17, LSort::Nat)),
    ];
    for depth in 0..4 {
        let left = terms.last().unwrap().clone();
        for sym in [
            FunSym::NoEq(crate::builtin::hash_sym()),
            FunSym::C(CSym::EMap),
            FunSym::Ac(AcSym::Mult),
            FunSym::List,
        ] {
            for args in [
                vec![],
                vec![left.clone()],
                vec![left.clone(), terms[depth].clone()],
            ] {
                let term = Term::App(sym, args.into());
                let mut expected = Vec::new();
                reference(&term, &mut expected);
                assert_eq!(pp_mterm(&term), expected);
                terms.push(term);
            }
        }
    }
}
#[test]
fn nested_maude_terms_and_borrowed_lists_use_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut term = Term::Lit(MaudeLit::MaudeVar(0, LSort::Msg));
        for depth in 0..8192 {
            let sym = if depth % 2 == 0 {
                FunSym::NoEq(crate::builtin::hash_sym())
            } else {
                FunSym::List
            };
            term = Term::App(sym, vec![term].into());
        }
        let wire = pp_mterm(&term);
        assert_eq!(
            wire.iter().filter(|&&b| b == b'(').count(),
            wire.iter().filter(|&&b| b == b')').count()
        );
        assert!(String::from_utf8(wire).unwrap().contains("x0:Msg"));
        let list = pp_mterm_list(std::slice::from_ref(&term));
        assert_eq!(list, pp_mterm(&Term::App(FunSym::List, vec![term].into())));
    });
}

#[test]
fn term_writer_handles_full_width_ids_and_lists() {
    let items = [
        Term::Lit(MaudeLit::MaudeVar(u64::MAX, LSort::Msg)),
        Term::Lit(MaudeLit::MaudeConst(0, LSort::Fresh)),
    ];
    let mut appended = b"prefix:".to_vec();
    pp_mterm_list_into(&items, &mut appended);
    assert_eq!(
        appended,
        b"prefix:list(cons(x18446744073709551615:Msg,cons(f(0),nil)))"
    );
    assert_eq!(pp_mterm_list(&items), &appended[b"prefix:".len()..]);
}

#[test]
fn dh_neutral_op_has_two_spaces_before_colon() {
    // HS `theoryOpEq "DH-neutral  : -> Msg"` (Maude/Parser.hs:223) emits TWO
    // spaces before the colon; the emitted module must match byte-for-byte.
    let s = pp_theory(&dh_maude_sig());
    assert!(s.contains("op tamXCFUDH-neutral  : -> Msg ."));
}

/// The complete module that the port sends to Maude for the pairing
/// signature, byte for byte.  HS `ppTheory` (Maude/Parser.hs:176-253)
/// supplies every line.  The module starts with the fixed preamble.  It
/// leaves out the sort, subsort and `op t` lines that `enable_nat` gates.
/// The line `op nil  : -> TOP .` keeps its two spaces.  The `stFunSyms`
/// block comes next, in `BTreeSet` order.  In that block the trailing
/// `"Msg "` of `theoryFunSym` meets the leading space of `" -> Msg"`.
/// Then comes one `theoryRule` line for each rewrite rule.  A single
/// shared conversion context numbers both sides of a rule, so `x0` and
/// `x1` occur again on the second side.  The context restarts for each
/// rule.
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

/// The DH module that the port sends to Maude, byte for byte, as captured
/// from the pinned oracle.  `DEBUG_MAUDE=1 tamarin-prover dh.spthy` writes
/// a copy of the module that Maude reads to `/tmp/maude.input`
/// (Maude/Process.hs:116-126).  `dh.spthy` declares only
/// `builtins: diffie-hellman`.  Its signature is therefore HS
/// `dhMaudeSig <> pairMaudeSig` (Maude/Signature.hs:201), which is what
/// the merge below builds.
///
/// A count of the rules cannot check the details that follow.  The module
/// holds five DH `op` lines in HS source order (Maude/Parser.hs:222-226).
/// Among those five, `mult` carries `[comm assoc]` and no attribute
/// letters (`theoryOpAC = theoryOp Nothing`, Maude/Parser.hs:262).  The
/// other four carry `XCFU`.  The module also holds all 15 rewrite rules in
/// `Set`-sorted order.  They are the 13 rules of `dhRules`
/// (Builtin/Rules.hs:47-61) plus the two pairing rules.  `ppMaude` renders
/// each rule.  It flattens AC arguments into a single `tammult(..)`
/// application.  One conversion context per rule numbers both sides of
/// that rule.  A change to the order, the type or the name of any single
/// DH rule moves a line here or rewrites it.
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

/// The same oracle capture for a `builtins: bilinear-pairing` theory.  Its
/// signature is HS `bpMaudeSig <> pairMaudeSig`.  `maudeSig` sets
/// `enableDH` whenever `enableBP` is set (Maude/Signature.hs:112).  This
/// module is therefore the DH module plus two additions.  The first
/// addition is the two BP `op` lines.  `pmult` is a plain `theoryOpEq`.
/// `em` is a `theoryOpC` that carries `[comm]` and no attribute letters
/// (Maude/Parser.hs:231-232).  The second addition is the three `bpRules`
/// (Builtin/Rules.hs:71-78), sorted in among the DH rules.
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

/// `enable_nat` adds these items to the module.  It adds the `TamNat` sort
/// to the `sort` line.  It adds a `subsort` line and an `op t` constant.
/// It also adds the `tone` and `tplus` operators.  These lines come from
/// the four `enableNat` guards of HS `ppTheory`
/// (Maude/Parser.hs:181-186, 190-193, 204-207, 240-244).
#[test]
fn nat_theory_adds_the_tamnat_lines() {
    let s = pp_theory(&crate::maude_sig::nat_maude_sig());
    assert!(s.contains("  sort Pub Fresh Msg Node TamNat TOP .\n"));
    assert!(s.contains("  subsort Fresh < Msg .\n  subsort TamNat < Msg .\n"));
    assert!(s.contains("  op n : Nat -> Node .\n  op t : Nat -> TamNat .\n"));
    assert!(s.contains("  op tamXCFUtone : -> TamNat .\n"));
    assert!(s.contains("  op tamtplus : TamNat TamNat -> TamNat [comm assoc] .\n"));
    // Without `enable_nat`, none of these lines appear.
    let plain = pp_theory(&pair_maude_sig());
    assert!(!plain.contains("TamNat"));
}

/// The Maude names of the four builtin AC operators.  Each name must be
/// the same name that `pp_theory` declares the operator with, which is
/// the literal in `op_ac`.  If the two names differ, an operator that the
/// module never declares heads a query.  `maude_parse::build_app` matches
/// replies against the same constants.
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

/// The exact letters of the attribute block (HS `funSymEncodeAttr`,
/// Maude/Parser.hs:76-88).  These letters are the ones the port sends to
/// Maude.  The test `every_attribute_quadruple_round_trips_through_decode`
/// compares the encoder only against its own decoder.  A letter renamed on
/// both the encode side and the decode side still passes that test.  These
/// two spellings fix the alphabet.
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
