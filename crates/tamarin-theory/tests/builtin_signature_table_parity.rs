// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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

use tamarin_parser::parser::{builtin_st_fun_sym_names, builtin_st_fun_syms, BuiltinFunSym};
use tamarin_term::function_symbols::{Constructability, Privacy};
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, hash_maude_sig,
    location_report_maude_sig, mset_maude_sig, nat_maude_sig, pair_dest_maude_sig,
    reveal_signature_maude_sig, signature_dest_maude_sig, signature_maude_sig,
    sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};

/// `elaborate`'s `builtin_sig`: the `MaudeSig` a `builtins:` name enables, i.e.
/// HS `builtinsNames` (Theory/Text/Parser/Signature.hs:78-86) with the
/// `reliable-channel` row's `Nothing` dropped.
fn builtin_sig(name: &str) -> Option<MaudeSig> {
    Some(match name {
        "diffie-hellman" => dh_maude_sig(),
        "bilinear-pairing" => bp_maude_sig(),
        "multiset" => mset_maude_sig(),
        "natural-numbers" => nat_maude_sig(),
        "xor" => xor_maude_sig(),
        "symmetric-encryption" => sym_enc_maude_sig(),
        "asymmetric-encryption" => asym_enc_maude_sig(),
        "signing" => signature_maude_sig(),
        "revealing-signing" => reveal_signature_maude_sig(),
        "hashing" => hash_maude_sig(),
        "locations-report" => location_report_maude_sig(),
        "dest-symmetric-encryption" => sym_enc_dest_maude_sig(),
        "dest-asymmetric-encryption" => asym_enc_dest_maude_sig(),
        "dest-signing" => signature_dest_maude_sig(),
        "dest-pairing" => pair_dest_maude_sig(),
        _ => return None,
    })
}

/// The `builtinsNames` rows that carry a signature
/// (Theory/Text/Parser/Signature.hs:78-86), in the
/// order that list is walked.
const BUILTINS_WITH_SIGNATURE: [&str; 15] = [
    "locations-report",
    "diffie-hellman",
    "bilinear-pairing",
    "multiset",
    "xor",
    "symmetric-encryption",
    "asymmetric-encryption",
    "signing",
    "dest-pairing",
    "dest-symmetric-encryption",
    "dest-asymmetric-encryption",
    "dest-signing",
    "revealing-signing",
    "hashing",
    "natural-numbers",
];

/// Every builtin the parser's table names must resolve to a `MaudeSig`, and the
/// row must be that signature's `st_fun_syms` — same names, same arities, same
/// privacy, same constructability, in the same (ascending set) order.
#[test]
fn parser_builtin_table_matches_the_maude_signatures() {
    for name in builtin_st_fun_sym_names() {
        let msig = builtin_sig(name)
            .unwrap_or_else(|| panic!("parser table names `{name}`, which has no MaudeSig"));
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
            builtin_st_fun_syms(name).expect("just enumerated"),
            expected.as_slice(),
            "builtin `{name}`"
        );
    }
}

/// The other direction: no builtin with a `MaudeSig` may be missing from the
/// parser's table, or `function`'s builtin pre-check would silently not fire
/// for the names it reserves.  `reliable-channel` is the one `builtinsNames`
/// row without a signature (Theory/Text/Parser/Signature.hs:84) and is absent
/// from both sides.
#[test]
fn every_builtin_with_a_signature_is_in_the_parser_table() {
    for name in BUILTINS_WITH_SIGNATURE {
        assert!(
            builtin_st_fun_syms(name).is_some(),
            "builtin `{name}` is missing from the parser's table"
        );
    }
    assert!(
        builtin_st_fun_syms("reliable-channel").is_none(),
        "`reliable-channel` maps to Nothing in HS and must reserve nothing"
    );
}

/// `builtinReservedNames` (Theory/Text/Parser/Signature.hs:174-181) is built
/// by walking
/// `builtinsNames` in order, and `function`'s `conflictingBuiltins`
/// (Theory/Text/Parser/Signature.hs:203) renders that walk's result — so the
/// parser table's ROW
/// order is load-bearing for the error text, not just its contents.
#[test]
fn parser_builtin_table_is_in_builtins_names_order() {
    let order: Vec<&str> = builtin_st_fun_sym_names().collect();
    assert_eq!(order, BUILTINS_WITH_SIGNATURE);
}
