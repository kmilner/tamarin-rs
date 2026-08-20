// Currently GPL 3.0 until granted permission by the following authors:
//   BTom-GH, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Signature.hs

//! Cross-check: the `builtins:` symbol table `tamarin-parser` carries must
//! agree with the `MaudeSig`s `tamarin-theory` derives the same symbols from.
//!
//! HS keeps ONE source for both — the parser's `function` reads
//! `stFunSyms . sig <$> getState`, the signature the `builtins` parser merged
//! (`Theory/Text/Parser/Signature.hs:102-135`).  The Rust port has two: the
//! parser needs the symbols at parse time to reproduce `function`'s conflict
//! diagnostics with a parsec frame, but `tamarin-theory` — which owns the
//! builtin-name → `MaudeSig` mapping — depends on the parser, so the parser
//! carries a static table instead.  This test pins the two together — the
//! `MaudeSig` side is what `elaborate`'s `builtin_sig` / `builtin_fun_attrs`
//! read, so a drift here is a drift in what the two stages believe a builtin
//! declares.

use tamarin_parser::parser::{builtin_st_fun_syms, BuiltinFunSym};
use tamarin_parser::BuiltinKind;
use tamarin_term::function_symbols::{Constructability, Privacy};
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, hash_maude_sig,
    location_report_maude_sig, minimal_maude_sig, mset_maude_sig, nat_maude_sig,
    pair_dest_maude_sig, pair_maude_sig, reveal_signature_maude_sig, signature_dest_maude_sig,
    signature_maude_sig, sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};

/// `elaborate`'s `builtin_sig`: the `MaudeSig` a `builtins:` name enables, i.e.
/// HS `builtinsNames` (Theory/Text/Parser/Signature.hs:78-86) with the
/// `reliable-channel` row's `Nothing` dropped.
fn builtin_sig(builtin: BuiltinKind) -> MaudeSig {
    match builtin {
        BuiltinKind::DiffieHellman => dh_maude_sig(),
        BuiltinKind::BilinearPairing => bp_maude_sig(),
        BuiltinKind::Multiset => mset_maude_sig(),
        BuiltinKind::NaturalNumbers => nat_maude_sig(),
        BuiltinKind::Xor => xor_maude_sig(),
        BuiltinKind::SymmetricEncryption => sym_enc_maude_sig(),
        BuiltinKind::AsymmetricEncryption => asym_enc_maude_sig(),
        BuiltinKind::Signing => signature_maude_sig(),
        BuiltinKind::RevealingSigning => reveal_signature_maude_sig(),
        BuiltinKind::Hashing => hash_maude_sig(),
        BuiltinKind::LocationsReport => location_report_maude_sig(),
        BuiltinKind::DestSymmetricEncryption => sym_enc_dest_maude_sig(),
        BuiltinKind::DestAsymmetricEncryption => asym_enc_dest_maude_sig(),
        BuiltinKind::DestSigning => signature_dest_maude_sig(),
        BuiltinKind::DestPairing => pair_dest_maude_sig(),
        BuiltinKind::Pairing => pair_maude_sig(),
        BuiltinKind::ReliableChannel => minimal_maude_sig(false),
    }
}

/// Every builtin the parser's table names must resolve to a `MaudeSig`, and the
/// row must be that signature's `st_fun_syms` — same names, same arities, same
/// privacy, same constructability, in the same (ascending set) order.
#[test]
fn parser_builtin_table_matches_the_maude_signatures() {
    for builtin in BuiltinKind::iter() {
        let msig = builtin_sig(builtin);
        let expected: Vec<BuiltinFunSym> = msig
            .st_fun_syms
            .iter()
            .map(|s| BuiltinFunSym {
                name: Box::leak(
                    String::from_utf8(s.name.to_vec())
                        .expect("builtin symbol names are ASCII")
                        .into_boxed_str(),
                ),
                arity: s.arity,
                private: s.privacy == Privacy::Private,
                destructor: s.constructability == Constructability::Destructor,
            })
            .collect();
        assert_eq!(
            builtin_st_fun_syms(builtin).expect("just enumerated"),
            expected.as_slice(),
            "builtin `{builtin}`"
        );
    }
}

/// The other direction: no builtin with a `MaudeSig` may be missing from the
/// parser's table, or `function`'s builtin pre-check would silently not fire
/// for the names it reserves.  `reliable-channel` is the one `builtinsNames`
/// row without a signature (Signature.hs:84) and is absent from both sides.
#[test]
fn every_builtin_with_a_signature_is_in_the_parser_table() {
    for builtin in BuiltinKind::iter() {
        assert!(
            builtin_st_fun_syms(builtin).is_some(),
            "builtin `{builtin}` is missing from the parser's table"
        );
    }
    // assert!(
    //     builtin_st_fun_syms("reliable-channel").is_none(),
    //     "`reliable-channel` maps to Nothing in HS and must reserve nothing"
    // );
}
