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
//! carries a static table instead.  This test pins the two together against
//! `elaborate::builtin_sig` itself — the function `elaborate`'s signature fold
//! and `builtin_fun_attrs` read — so a drift here is a drift in what the two
//! stages believe a builtin declares.

use tamarin_parser::parser::{builtin_st_fun_sym_kinds, builtin_st_fun_syms, BuiltinFunSym};
use tamarin_parser::BuiltinKind;
use tamarin_term::function_symbols::{
    fst_dest_sym, fst_sym, snd_dest_sym, snd_sym, Constructability, Privacy,
};
use tamarin_term::maude_sig::minimal_maude_sig;
use tamarin_theory::elaborate::builtin_sig;

/// The `builtinsNames` rows that carry a signature
/// (Theory/Text/Parser/Signature.hs:78-86), in the
/// order that list is walked.
const BUILTINS_WITH_SIGNATURE: [BuiltinKind; 15] = [
    BuiltinKind::LocationsReport,
    BuiltinKind::DiffieHellman,
    BuiltinKind::BilinearPairing,
    BuiltinKind::Multiset,
    BuiltinKind::Xor,
    BuiltinKind::SymmetricEncryption,
    BuiltinKind::AsymmetricEncryption,
    BuiltinKind::Signing,
    BuiltinKind::DestPairing,
    BuiltinKind::DestSymmetricEncryption,
    BuiltinKind::DestAsymmetricEncryption,
    BuiltinKind::DestSigning,
    BuiltinKind::RevealingSigning,
    BuiltinKind::Hashing,
    BuiltinKind::NaturalNumbers,
];

/// Every builtin with a `MaudeSig` must have a parser-table row, and the row
/// must be that signature's `st_fun_syms` — same names, same arities, same
/// privacy, same constructability, in the same (ascending set) order.
#[test]
fn parser_builtin_table_matches_the_maude_signatures() {
    let mut compared = 0;
    for builtin in BuiltinKind::iter() {
        let Some(msig) = builtin_sig(builtin) else {
            continue; // covered by `reliable_channel_reserves_no_symbols`
        };
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
            builtin_st_fun_syms(builtin).unwrap_or_else(|| panic!(
                "builtin `{builtin}` is missing from the parser's table"
            )),
            expected.as_slice(),
            "builtin `{builtin}`"
        );
        compared += 1;
    }
    // `BuiltinKind::iter()` is a hand-written list, so a variant dropped from
    // it would make the loop above silently skip that builtin rather than
    // fail.  Pin the number of rows actually compared.
    assert_eq!(
        compared,
        BUILTINS_WITH_SIGNATURE.len(),
        "`BuiltinKind::iter()` no longer yields every signature-carrying builtin"
    );
}

/// `reliable-channel` is the one `builtinsNames` row without a signature
/// (Theory/Text/Parser/Signature.hs:84).  It must therefore reserve nothing.
/// A row for it makes `function`'s builtin pre-check fire on names that HS
/// leaves free.  [`parser_builtin_table_matches_the_maude_signatures`] checks
/// the other direction, that no builtin with a signature is missing from the
/// table.
#[test]
fn reliable_channel_reserves_no_symbols() {
    assert!(
        builtin_st_fun_syms(BuiltinKind::ReliableChannel).is_none(),
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
    let order: Vec<BuiltinKind> = builtin_st_fun_sym_kinds().collect();
    assert_eq!(order, BUILTINS_WITH_SIGNATURE);
}

/// `reliable-channel`'s `None` must stay a no-op in the signature fold, not a
/// merge of some neutral-looking signature.
///
/// `MaudeSig::merge` is asymmetric in its right operand for the `fst`/`snd`
/// constructor-vs-destructor pair (HS `unionExceptPairSym`,
/// Term/Maude/Signature.hs:143-150): whichever variant the right operand
/// carries wins.  `minimal_maude_sig` — the signature every theory starts from
/// — carries the CONSTRUCTOR `fst`/`snd`, so merging it for `reliable-channel`
/// would evict `dest-pairing`'s destructors whenever `reliable-channel`
/// follows `dest-pairing` in the `builtins:` list.
///
/// Both orders are legal HS input and both keep the destructors there, so
/// fold `builtin_sig` the way `elaborate_items` does and pin the outcome.
#[test]
fn reliable_channel_does_not_evict_dest_pairing_destructors() {
    for order in [
        [BuiltinKind::DestPairing, BuiltinKind::ReliableChannel],
        [BuiltinKind::ReliableChannel, BuiltinKind::DestPairing],
    ] {
        let mut sig = minimal_maude_sig(false);
        for builtin in order {
            if let Some(s) = builtin_sig(builtin) {
                sig = sig.merge(s);
            }
        }
        let syms = &sig.st_fun_syms;
        assert!(
            syms.contains(&fst_dest_sym()) && syms.contains(&snd_dest_sym()),
            "`builtins: {}, {}` lost the destructor `fst`/`snd`",
            order[0],
            order[1]
        );
        assert!(
            !syms.contains(&fst_sym()) && !syms.contains(&snd_sym()),
            "`builtins: {}, {}` kept the constructor `fst`/`snd`",
            order[0],
            order[1]
        );
    }
}
