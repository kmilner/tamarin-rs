// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parity for the legal-name set of the `builtins:` declaration.
//!
//! HS `builtins` (Theory/Text/Parser/Signature.hs:88-95) is
//! `symbol "builtins" *> colon *> commaSep1 builtinTheory`, and
//! `builtinTheory = asum $ map (try . extendSig) builtinsNames`
//! (Theory/Text/Parser/Signature.hs:142): every entry matches through
//! `symbol name`, so a name outside `builtinsNames`
//! (Theory/Text/Parser/Signature.hs:78-86) matches nothing and the whole
//! alternation fails with the sixteen names as its `expecting` set.  The port
//! reports that as [`ParseError::UnknownItem`] in the
//! [`ParseContext::Builtin`] context, whose `expected()` is the same sixteen
//! names ranked by edit distance and cut to the closest three.
//!
//! WHICH names are accepted, and where a rejection is reported, is pinned to
//! the Haskell oracle (Git revision ef3f0468): every name in
//! [`BUILTINS_NAMES`] loads `theory BN begin builtins: <name> end` at exit 0
//! there, and every rejected name below is the oracle's own `(line, column)`
//! except where a comment marks a deliberate divergence.

use tamarin_parser::ast::BuiltinKind;
use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError, TheoryItem};

/// `builtinsNames` (Theory/Text/Parser/Signature.hs:78-86) in row order —
/// `locations-report` and `reliable-channel` ahead of the `builtinsDiffNames`
/// rows (Theory/Text/Parser/Signature.hs:60-75).  This is byte-for-byte the
/// oracle's `expecting` list for `builtins: pairing`.
const BUILTINS_NAMES: [&str; 16] = [
    "locations-report",
    "reliable-channel",
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

/// A theory whose single item is `builtins: <list>`, with the list starting at
/// line 2 column 11.
fn builtins_theory(list: &str) -> String {
    format!("theory BN begin\nbuiltins: {list}\nend\n")
}

/// The kinds of `src`'s single `builtins:` item, in source order.
#[track_caller]
fn kinds(src: &str) -> Vec<BuiltinKind> {
    let thy = parse_theory(src, &[]).unwrap_or_else(|e| panic!("{src:?} rejected: {e:?}"));
    let Some(TheoryItem::Builtins(entries)) = thy
        .items
        .iter()
        .find(|i| matches!(i, TheoryItem::Builtins(_)))
    else {
        panic!("no builtins item in {src:?}");
    };
    entries.iter().map(|b| b.kind).collect()
}

/// The `(unknown_item, (line, col), expected)` of the builtin-context
/// [`ParseError::UnknownItem`] `src` fails with.
#[track_caller]
fn unknown(src: &str) -> (String, (u32, u32), Vec<String>) {
    let e = parse_theory(src, &[]).expect_err("the probes below must all fail to parse");
    let ParseError::UnknownItem {
        item_kind: ParseContext::Builtin,
        unknown_item,
        at,
    } = &e
    else {
        panic!("expected the builtin-context unknown-item variant, got {e:?}");
    };
    (
        unknown_item.clone(),
        (at.line, at.col),
        e.expected()
            .expect("an unknown builtin carries suggestions"),
    )
}

/// [`BuiltinKind::iter`] enumerates the legal names in `builtinsNames` row
/// order, which is the order the oracle prints them in.
#[test]
fn the_name_table_is_in_builtins_names_order() {
    assert_eq!(
        BuiltinKind::iter().map(|b| b.as_str()).collect::<Vec<_>>(),
        BUILTINS_NAMES
    );
}

/// Each of the sixteen names parses on its own, and round-trips through
/// [`BuiltinKind::from_str`] and [`BuiltinKind::as_str`].
#[test]
fn every_legal_name_is_accepted() {
    for name in BUILTINS_NAMES {
        let kind = BuiltinKind::from_str(name).unwrap_or_else(|| panic!("{name} has no kind"));
        assert_eq!(kind.as_str(), name);
        assert_eq!(kinds(&builtins_theory(name)), [kind], "case {name}");
    }
}

/// `reliable-channel` is legal even though it merges no signature — its
/// `builtinsNames` row maps to `Nothing`
/// (Theory/Text/Parser/Signature.hs:84).  `pairing` is NOT a name: the pairing
/// symbols are seeded (`pairMaudeSig`, Token.hs:260-261) and only
/// `dest-pairing` names a row.  The oracle loads the first and rejects the
/// second at line 2 column 11.
#[test]
fn reliable_channel_is_legal_and_pairing_is_not() {
    assert_eq!(
        kinds(&builtins_theory("reliable-channel")),
        [BuiltinKind::ReliableChannel]
    );
    assert_eq!(BuiltinKind::from_str("pairing"), None);
    let (found, at, _) = unknown(&builtins_theory("pairing"));
    assert_eq!(found, "pairing");
    assert_eq!(at, (2, 11));
}

/// A name outside the table is rejected at its first character — the oracle's
/// own position for every case below.  None of these shares a prefix with a
/// legal name, so the oracle's `symbol` alternation also stops at column 11.
#[test]
fn an_unknown_name_is_rejected_at_its_first_character() {
    for name in [
        "foobar",
        "pairing",
        "hash",
        "dh",
        "sign",
        "XOR",
        "location-report",
        "locations_report",
        "reliable_channel",
        "natural-number",
        "dest-pariing",
        "dest-x",
    ] {
        let (found, at, _) = unknown(&builtins_theory(name));
        assert_eq!(found, name, "case {name}");
        assert_eq!(at, (2, 11), "case {name}");
    }

    // A dangling hyphen is not part of the name: `hyphen_identifier` joins a
    // `-` only when another identifier follows, so the reported token stops
    // before it.  The oracle also reports column 11 here.
    let (found, at, _) = unknown(&builtins_theory("dest-"));
    assert_eq!(found, "dest");
    assert_eq!(at, (2, 11));
}

/// The suggestions are the closest three legal names — never a name the
/// parser would then reject.
#[test]
fn the_suggestions_are_always_legal_names() {
    for name in ["foobar", "hash", "dest-pariing", "natural-number"] {
        let (_, _, expected) = unknown(&builtins_theory(name));
        assert_eq!(expected.len(), 3, "case {name}");
        for suggestion in &expected {
            assert!(
                BUILTINS_NAMES.contains(&suggestion.as_str()),
                "case {name}: `{suggestion}` is not a legal builtin name"
            );
            assert_eq!(
                kinds(&builtins_theory(suggestion)).len(),
                1,
                "case {name}: `{suggestion}` is suggested but rejected"
            );
        }
    }
    // A one-edit typo puts the intended name first.
    let (_, _, expected) = unknown(&builtins_theory("dest-pariing"));
    assert_eq!(expected[0], "dest-pairing");
}

/// A comma-separated list keeps every entry, in source order, and repeats are
/// not collapsed — the oracle loads each of these at exit 0.
#[test]
fn a_comma_separated_list_keeps_every_entry() {
    assert_eq!(
        kinds(&builtins_theory("hashing, xor")),
        [BuiltinKind::Hashing, BuiltinKind::Xor]
    );
    assert_eq!(
        kinds(&builtins_theory(
            "diffie-hellman, xor, multiset, natural-numbers"
        )),
        [
            BuiltinKind::DiffieHellman,
            BuiltinKind::Xor,
            BuiltinKind::Multiset,
            BuiltinKind::NaturalNumbers,
        ]
    );
    assert_eq!(
        kinds(&builtins_theory("hashing, hashing")),
        [BuiltinKind::Hashing, BuiltinKind::Hashing]
    );
    // A later unknown entry is rejected with the same variant.
    let (found, _, _) = unknown(&builtins_theory("hashing, foobar"));
    assert_eq!(found, "foobar");
}

/// The first entry's [`Location`](tamarin_parser::Location) spans exactly its
/// name — the span the conflict diagnostics of `tests/macro_conflicts.rs` and
/// `tests/function_decl_parity.rs` label as the first declaration.
#[test]
fn the_first_entrys_location_spans_exactly_the_name() {
    for list in ["hashing", "hashing, xor", "dest-asymmetric-encryption"] {
        let src = builtins_theory(list);
        let thy = parse_theory(&src, &[]).expect("parse");
        let Some(TheoryItem::Builtins(entries)) = thy
            .items
            .iter()
            .find(|i| matches!(i, TheoryItem::Builtins(_)))
        else {
            panic!("no builtins item in {src:?}");
        };
        let first = &entries[0];
        let at = first.location;
        assert_eq!((at.line, at.col), (2, 11), "case {list}");
        assert_eq!(&src[at.start..at.end], first.kind.as_str(), "case {list}");
    }
}

/// An empty list is rejected at the token that follows the colon — the
/// oracle's own position, since `commaSep1` needs one element.
#[test]
fn an_empty_list_is_rejected_at_the_following_token() {
    let (_, at, _) = unknown("theory BN begin\nbuiltins:\nend\n");
    assert_eq!(at, (3, 1));
}

/// DELIBERATE DIVERGENCE, the same one `function_decl_parity.rs` pins for the
/// theory's closing `end`: HS `symbol name` (Token.hs:272-273) is a plain
/// `string` with no word boundary, so it PREFIX-matches and leaves the
/// remainder for the next parser.  The oracle stops `signing-dest` after
/// `signing` and reports line 2 column 18, stops `diffie-hellman-x` after
/// `diffie-hellman` and reports line 2 column 25, and ACCEPTS
/// `builtins: signingend` at exit 0 — reading it as `signing` followed by the
/// theory's `end`.  This port lexes the whole word and rejects it as one
/// unknown name, so a typo cannot silently enable a builtin or truncate a
/// theory.
#[test]
fn a_name_that_merely_prefixes_a_legal_one_is_rejected_whole() {
    for name in ["signing-dest", "diffie-hellman-x", "signingend", "xorend"] {
        let (found, at, _) = unknown(&builtins_theory(name));
        assert_eq!(found, name, "case {name}");
        assert_eq!(at, (2, 11), "case {name}");
    }
}
