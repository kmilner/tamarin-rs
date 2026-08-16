// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

#[test]
fn predefined_arities() {
    assert_eq!(pair_sym().arity, 2);
    assert_eq!(inv_sym().arity, 1);
    assert_eq!(one_sym().arity, 0);
    assert_eq!(diff_sym().privacy, Privacy::Private);
    assert_eq!(pair_sym().privacy, Privacy::Public);
}

#[test]
fn destructors_flip_constructability() {
    assert_eq!(fst_sym().constructability, Constructability::Constructor);
    assert_eq!(
        fst_dest_sym().constructability,
        Constructability::Destructor
    );
    // Same name though.
    assert_eq!(fst_sym().name, fst_dest_sym().name);
}

#[test]
fn signature_membership() {
    let dh = dh_fun_sig();
    assert!(dh.contains(&FunSym::Ac(AcSym::Mult)));
    assert!(dh.contains(&FunSym::NoEq(exp_sym())));
    assert!(!dh.contains(&FunSym::Ac(AcSym::Xor)));
}

/// `plainstring (show sym)` is the Haskell string literal's escaped body:
/// ordinary symbol names pass through, and the `\&` separator appears only
/// where the literal would otherwise re-lex (a numeric escape before a
/// digit, `\SO` before `H`).
#[test]
fn plain_show_bytes_matches_haskell_string_literal_body() {
    assert_eq!(plain_show_bytes(b"aenc"), "aenc");
    assert_eq!(plain_show_bytes(b"_exp"), "_exp");
    assert_eq!(plain_show_bytes(b"a\"b\\c"), "a\\\"b\\\\c");
    assert_eq!(plain_show_bytes(&[0xc3, b'7']), "\\195\\&7");
    assert_eq!(plain_show_bytes(&[0xc3, b'x']), "\\195x");
    assert_eq!(plain_show_bytes(&[0x0e, b'H']), "\\SO\\&H");
    assert_eq!(plain_show_bytes(&[0x0e, b'I']), "\\SOI");
}

/// Every variant's derived-`Show` spelling, which is GHC's constructor
/// name — not the Rust one (`IsNdc` renders as `IsNDC`).  Pinned per
/// variant, not just at the tuples `show_acfct_sym` composes them into.
#[test]
fn attribute_shows_match_the_haskell_constructor_names() {
    assert_eq!(show_privacy(Privacy::Private), "Private");
    assert_eq!(show_privacy(Privacy::Public), "Public");
    assert_eq!(
        show_constructability(Constructability::Constructor),
        "Constructor"
    );
    assert_eq!(
        show_constructability(Constructability::Destructor),
        "Destructor"
    );
    assert_eq!(show_ndc_state(NdcState::IsNdc), "IsNDC");
    assert_eq!(show_ndc_state(NdcState::NotNdc), "NotNDC");
    assert_eq!(show_ndc_state(NdcState::IsNdcDiff), "IsNDCDiff");
    assert_eq!(show_ndc_state(NdcState::IsNdcBoth), "IsNDCBoth");
}

/// Derived `Show` of the `ACfctSym` tuple.
#[test]
fn show_acfct_sym_matches_derived_show() {
    let s = AcFctSym::new(
        b"add".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    assert_eq!(show_acfct_sym(&s), "(\"add\",(Public,Constructor,NotNDC))");
    let d = AcFctSym::new(
        b"add".to_vec(),
        Privacy::Private,
        Constructability::Destructor,
        NdcState::IsNdcBoth,
    );
    assert_eq!(
        show_acfct_sym(&d),
        "(\"add\",(Private,Destructor,IsNDCBoth))"
    );
}

#[test]
fn implicit_sig_includes_pair_and_inv() {
    let s = implicit_fun_sig();
    assert!(s.contains(&FunSym::NoEq(pair_sym())));
    assert!(s.contains(&FunSym::NoEq(inv_sym())));
    assert!(s.contains(&FunSym::Ac(AcSym::Mult)));
    assert!(s.contains(&FunSym::Ac(AcSym::Union)));
}

// =========================================================================
// Haskell-faithfulness invariants for FunctionSymbols enum orders.
//
// FunSym sets appear as BTreeSet<FunSym> (function signatures), and
// their iteration order is the basis for several deterministic
// serializations (cf. MaudeSig).  Drift here silently changes
// Maude-bridge command order and term canonicalization.
// =========================================================================

/// FunctionSymbols.hs:138:
///     data ACSym = Union | Mult | Xor | NatPlus | ACfct ACfctSym
#[test]
fn ac_sym_ord_matches_haskell_declaration() {
    assert!(AcSym::Union < AcSym::Mult);
    assert!(AcSym::Mult < AcSym::Xor);
    assert!(AcSym::Xor < AcSym::NatPlus);
    let user = AcSym::AcFct(AcFctSym::new(
        b"f".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    ));
    assert!(AcSym::NatPlus < user);
}

/// The hand-written `AcFctSym` `Ord` orders on the HS tuple's field chain
/// `(name, (privacy, constructability, ndc))`: the name dominates, and the
/// tail decides between equal names.  This order reaches the emitted Maude
/// module (`st_ac_fun_syms` is a `BTreeSet`) and term canonicalization
/// through `AcSym`/`FunSym`.
#[test]
fn ac_fct_sym_ord_follows_the_haskell_tuple_field_chain() {
    let sym = |name: &str, p, c, ndc| AcFctSym::new(name.as_bytes().to_vec(), p, c, ndc);
    let base = sym(
        "f",
        Privacy::Private,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    // Two separately built symbols with the same fields: the interned name
    // makes the `Eq`/`Ord` pointer fast-path fire, and it must agree with
    // the byte comparison it replaces.
    let same = sym(
        "f",
        Privacy::Private,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    assert_eq!(base, same);
    assert_eq!(base.cmp(&same), std::cmp::Ordering::Equal);
    // Each field breaks the tie only once every field before it is equal.
    assert!(
        base < sym(
            "f",
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc
        )
    );
    assert!(
        base < sym(
            "f",
            Privacy::Private,
            Constructability::Destructor,
            NdcState::IsNdc
        )
    );
    assert!(
        base < sym(
            "f",
            Privacy::Private,
            Constructability::Constructor,
            NdcState::NotNdc
        )
    );
    // The name dominates: the greatest tail under "f" still sorts before
    // the smallest tail under "g".
    assert!(
        sym(
            "f",
            Privacy::Public,
            Constructability::Destructor,
            NdcState::IsNdcBoth
        ) < sym(
            "g",
            Privacy::Private,
            Constructability::Constructor,
            NdcState::IsNdc
        )
    );
}

/// `Hash` feeds the same field sequence as `Eq`/`Ord` — the name, then the
/// remaining fields in declared order — so it agrees with those fields
/// hashed by hand into the same hasher.
#[test]
fn interned_name_sym_hash_feeds_the_declared_field_sequence() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    fn hash_of(value: impl Hash) -> u64 {
        let mut state = DefaultHasher::new();
        value.hash(&mut state);
        state.finish()
    }
    let no_eq = NoEqSym::new(
        b"f".to_vec(),
        2,
        Privacy::Private,
        Constructability::Destructor,
    )
    .with_ndc(NdcState::IsNdcDiff);
    let mut state = DefaultHasher::new();
    no_eq.name.hash(&mut state);
    no_eq.arity.hash(&mut state);
    no_eq.privacy.hash(&mut state);
    no_eq.constructability.hash(&mut state);
    no_eq.ndc.hash(&mut state);
    assert_eq!(hash_of(no_eq), state.finish());

    let ac = AcFctSym::new(
        b"f".to_vec(),
        Privacy::Private,
        Constructability::Destructor,
        NdcState::IsNdcDiff,
    );
    let mut state = DefaultHasher::new();
    ac.name.hash(&mut state);
    ac.privacy.hash(&mut state);
    ac.constructability.hash(&mut state);
    ac.ndc.hash(&mut state);
    assert_eq!(hash_of(ac), state.finish());
}

/// The `NoEqSym` `Ord` orders on the HS tuple's field chain
/// `(name, (arity, privacy, constructability, ndc))`: the name dominates,
/// and the tail decides between equal names — `arity` first, so it outranks
/// privacy.  This order reaches the emitted Maude module (`st_fun_syms` is
/// a `BTreeSet`) and term canonicalization through `FunSym`.
#[test]
fn no_eq_sym_ord_follows_the_haskell_tuple_field_chain() {
    let sym = |name: &str, arity, p, c, ndc| {
        NoEqSym::new(name.as_bytes().to_vec(), arity, p, c).with_ndc(ndc)
    };
    let base = sym(
        "f",
        1,
        Privacy::Private,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    // Two separately built symbols with the same fields: the interned name
    // makes the `Eq`/`Ord` pointer fast-path fire, and it must agree with
    // the byte comparison it replaces.
    let same = sym(
        "f",
        1,
        Privacy::Private,
        Constructability::Constructor,
        NdcState::IsNdc,
    );
    assert_eq!(base, same);
    assert_eq!(base.cmp(&same), std::cmp::Ordering::Equal);
    // Each field breaks the tie only once every field before it is equal.
    assert!(
        base < sym(
            "f",
            2,
            Privacy::Private,
            Constructability::Constructor,
            NdcState::IsNdc
        )
    );
    assert!(
        base < sym(
            "f",
            1,
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc
        )
    );
    assert!(
        base < sym(
            "f",
            1,
            Privacy::Private,
            Constructability::Destructor,
            NdcState::IsNdc
        )
    );
    assert!(
        base < sym(
            "f",
            1,
            Privacy::Private,
            Constructability::Constructor,
            NdcState::NotNdc
        )
    );
    // Arity outranks privacy: the greater arity wins even though its
    // privacy sorts first.
    assert!(
        sym(
            "f",
            1,
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc
        ) < sym(
            "f",
            2,
            Privacy::Private,
            Constructability::Constructor,
            NdcState::IsNdc
        )
    );
    // The name dominates: the greatest tail under "f" still sorts before
    // the smallest tail under "g".
    assert!(
        sym(
            "f",
            usize::MAX,
            Privacy::Public,
            Constructability::Destructor,
            NdcState::IsNdcBoth
        ) < sym(
            "g",
            0,
            Privacy::Private,
            Constructability::Constructor,
            NdcState::IsNdc
        )
    );
    // `BTreeSet<NoEqSym>` iterates name-major, then by the remaining fields
    // in declared order.
    let set: std::collections::BTreeSet<NoEqSym> = [
        sym(
            "g",
            0,
            Privacy::Private,
            Constructability::Constructor,
            NdcState::IsNdc,
        ),
        sym(
            "f",
            1,
            Privacy::Private,
            Constructability::Constructor,
            NdcState::NotNdc,
        ),
        sym(
            "f",
            1,
            Privacy::Private,
            Constructability::Destructor,
            NdcState::IsNdc,
        ),
        sym(
            "f",
            1,
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc,
        ),
        base,
        sym(
            "f",
            0,
            Privacy::Public,
            Constructability::Destructor,
            NdcState::IsNdcBoth,
        ),
    ]
    .into_iter()
    .collect();
    let order: Vec<(String, usize, Privacy, Constructability, NdcState)> = set
        .iter()
        .map(|s| {
            (
                String::from_utf8_lossy(s.name).into_owned(),
                s.arity,
                s.privacy,
                s.constructability,
                s.ndc,
            )
        })
        .collect();
    assert_eq!(
        order,
        vec![
            (
                "f".to_string(),
                0,
                Privacy::Public,
                Constructability::Destructor,
                NdcState::IsNdcBoth
            ),
            (
                "f".to_string(),
                1,
                Privacy::Private,
                Constructability::Constructor,
                NdcState::IsNdc
            ),
            (
                "f".to_string(),
                1,
                Privacy::Private,
                Constructability::Constructor,
                NdcState::NotNdc
            ),
            (
                "f".to_string(),
                1,
                Privacy::Private,
                Constructability::Destructor,
                NdcState::IsNdc
            ),
            (
                "f".to_string(),
                1,
                Privacy::Public,
                Constructability::Constructor,
                NdcState::IsNdc
            ),
            (
                "g".to_string(),
                0,
                Privacy::Private,
                Constructability::Constructor,
                NdcState::IsNdc
            ),
        ]
    );
}

/// FunctionSymbols.hs:125:
///     data NDCstate = IsNDC | NotNDC | IsNDCDiff | IsNDCBoth
#[test]
fn ndc_state_ord_matches_haskell_declaration() {
    assert!(NdcState::IsNdc < NdcState::NotNdc);
    assert!(NdcState::NotNdc < NdcState::IsNdcDiff);
    assert!(NdcState::IsNdcDiff < NdcState::IsNdcBoth);
}

/// FunctionSymbols.hs:111:
///     data Privacy = Private | Public
#[test]
fn privacy_ord_matches_haskell_declaration() {
    assert!(
        Privacy::Private < Privacy::Public,
        "Private MUST sort before Public — used in unifiabilty queries"
    );
}

/// FunctionSymbols.hs:116:
///     data Constructability = Constructor | Destructor
#[test]
fn constructability_ord_matches_haskell_declaration() {
    assert!(Constructability::Constructor < Constructability::Destructor);
}

/// FunctionSymbols.hs:150-153:
///     data FunSym = NoEq NoEqSym | AC ACSym | C CSym | List
///
/// `NoEq` comes FIRST.  This ordering matters because `BTreeSet<FunSym>`
/// signatures iterate in it when constructing Maude bridge commands.  If
/// `List` or `C` came before `NoEq`, Maude would see declarations in an
/// inconsistent order vs Haskell.
#[test]
fn fun_sym_ord_matches_haskell_declaration() {
    let no_eq = FunSym::NoEq(pair_sym());
    let ac = FunSym::Ac(AcSym::Mult);
    let c = FunSym::C(CSym::EMap);
    let list = FunSym::List;
    assert!(no_eq < ac, "NoEq < AC (Haskell decl order)");
    assert!(ac < c, "AC < C");
    assert!(c < list, "C < List");
    assert!(no_eq < list, "transitive: NoEq < List");
}
