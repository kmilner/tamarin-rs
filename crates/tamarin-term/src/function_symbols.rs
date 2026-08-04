// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, jdreier, meiersi, PhilipLukertWork, charlie-j, rsasse,
//   rkunnema, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term.hs,
//   lib/term/src/Term/Term/FunctionSymbols.hs

//! Port of `Term.Term.FunctionSymbols` from
//! `lib/term/src/Term/Term/FunctionSymbols.hs`.
//!
//! Function-symbol enums and the predefined operator signatures used by
//! Diffie-Hellman, XOR, multiset, bilinear pairing, and natural-number
//! reasoning.

use std::collections::BTreeSet;

// HS bundles the four attribute enums below into `FctAttr`
// (FunctionSymbols.hs:128); tamarin-parser carries the surface-shaped copy.

/// A function symbol can be either private (unknown to the adversary) or public.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Privacy {
    Private,
    Public,
}

/// A function symbol can be a constructor or a destructor (which only
/// applies if it reduces).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constructability {
    Constructor,
    Destructor,
}

/// A function symbol can be AC or not (parser attribute carrier).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AcState {
    IsAc,
    NotAc,
}

/// NDC ("no deconstruction chain") property of a function symbol: held for
/// the trace intruder rules (`IsNdc`), the diff-mode intruder rules
/// (`IsNdcDiff`), both, or neither.
///
/// Variant order mirrors the Haskell declaration
/// `IsNDC | NotNDC | IsNDCDiff | IsNDCBoth` — the derived `Ord` participates
/// in symbol ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NdcState {
    IsNdc,
    NotNdc,
    IsNdcDiff,
    IsNdcBoth,
}

impl NdcState {
    /// Does the state include the NDC property for the trace intruder rules?
    pub fn has_ndc(self) -> bool {
        matches!(self, NdcState::IsNdc | NdcState::IsNdcBoth)
    }
    /// Does the state include the NDC property for the diff-mode intruder rules?
    pub fn has_ndc_diff(self) -> bool {
        matches!(self, NdcState::IsNdcDiff | NdcState::IsNdcBoth)
    }
    /// Combine two NDC states, keeping the properties asserted by either one.
    pub fn join(self, other: NdcState) -> NdcState {
        match (
            self.has_ndc() || other.has_ndc(),
            self.has_ndc_diff() || other.has_ndc_diff(),
        ) {
            (true, true) => NdcState::IsNdcBoth,
            (true, false) => NdcState::IsNdc,
            (false, true) => NdcState::IsNdcDiff,
            (false, false) => NdcState::NotNdc,
        }
    }
}

/// Free (no-equation) function symbol — name plus arity, privacy,
/// constructability, and NDC property. Mirrors the Haskell tuple
/// `(ByteString, (Int, Privacy, Constructability, NDCstate))`.
#[derive(Clone, Copy)]
pub struct NoEqSym {
    /// Interned into a global pool and held as a `&'static [u8]`, so a clone
    /// is a pointer copy — no heap allocation (unlike owned `Vec`) and no
    /// atomic refcount (unlike `Arc`, whose refcount was a contention point
    /// under the parallel proof search) — and equal names share one copy.
    /// Raw-bytes (`ByteString`) semantics of HS `NoEqSym` are preserved:
    /// `&[u8]` derefs to its contents, so `Eq`/`Ord`/`Hash` stay content-based.
    pub name: &'static [u8],
    pub arity: usize,
    pub privacy: Privacy,
    pub constructability: Constructability,
    pub ndc: NdcState,
}

// Render the name as a (lossy) string rather than a raw byte array, so debug
// output is readable (e.g. `name: "MAC"` not `name: [77, 65, 67]`).
impl std::fmt::Debug for NoEqSym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NoEqSym")
            .field("name", &String::from_utf8_lossy(self.name))
            .field("arity", &self.arity)
            .field("privacy", &self.privacy)
            .field("constructability", &self.constructability)
            .field("ndc", &self.ndc)
            .finish()
    }
}

// `Eq`/`Hash`/`Ord` for a symbol struct whose first field is an interned name,
// generated from the field list in comparison order — the HS tuple's order,
// which all three impls read off.  That order is load-bearing: `AcSym` and
// `FunSym` derive their `Ord` from these, and `BTreeSet` iteration order
// reaches the emitted Maude module text and the pretty-printed signature.
//
// The name comparison carries a pointer fast-path.  `name` is interned
// (`intern_bytes`), so equal content ⇒ equal pointer; therefore an `as_ptr()`
// match is true exactly on the common same-symbol path and lets us skip the
// byte `memcmp` that dominated `FunSig::contains` and term comparison in the
// proof search.  Correctness does NOT depend on the interning invariant: equal
// data pointers always imply equal content (same allocation), and on a pointer
// MISmatch we fall back to the full byte comparison — so the boolean/total-order
// is identical to a derived, content-based one.
//
// `Hash` is generated here rather than `derive`d so that it sits alongside the
// manual `PartialEq`/`Ord` without tripping `clippy::derived_hash_with_manual_eq`
// (a correctness lint: a derived `Hash` next to a hand-written `Eq` risks the
// `a == b ⇒ hash(a) == hash(b)` invariant being violated).  Here both are
// content-based — the `Eq`/`Ord` pointer fast-path only ever returns early when
// the contents are provably equal — so the invariant holds.
//
// Each impl destructures `self` without `..`, so a new struct field fails to
// compile until it is added to the invocation's field list below, which then
// forces the same decision for equality, hashing, and ordering at once.
macro_rules! interned_name_sym_impls {
    ($ty:ident { $name:ident, $($tail:ident),+ $(,)? }) => {
        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let $ty { $name, $($tail),+ } = self;
                (std::ptr::eq($name.as_ptr(), other.$name.as_ptr()) || *$name == other.$name)
                    $(&& *$tail == other.$tail)+
            }
        }
        impl Eq for $ty {}
        impl std::hash::Hash for $ty {
            #[inline]
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                let $ty { $name, $($tail),+ } = self;
                $name.hash(state);
                $($tail.hash(state);)+
            }
        }
        impl Ord for $ty {
            #[inline]
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                let $ty { $name, $($tail),+ } = self;
                // Only the name compare gains the ptr fast-path.
                let name_ord = if std::ptr::eq($name.as_ptr(), other.$name.as_ptr()) {
                    std::cmp::Ordering::Equal
                } else {
                    $name.cmp(&other.$name)
                };
                name_ord$(.then_with(|| $tail.cmp(&other.$tail)))+
            }
        }
        impl PartialOrd for $ty {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
    };
}

interned_name_sym_impls!(NoEqSym {
    name,
    arity,
    privacy,
    constructability,
    ndc
});

impl NoEqSym {
    pub fn new(
        name: impl Into<Vec<u8>>,
        arity: usize,
        privacy: Privacy,
        c: Constructability,
    ) -> Self {
        NoEqSym {
            name: crate::intern::intern_bytes(&name.into()),
            arity,
            privacy,
            constructability: c,
            ndc: NdcState::NotNdc,
        }
    }
    pub fn with_destructor(mut self) -> Self {
        self.constructability = Constructability::Destructor;
        self
    }
    pub fn with_ndc(mut self, ndc: NdcState) -> Self {
        self.ndc = ndc;
        self
    }
}

/// User-defined AC function symbol — name plus privacy, constructability,
/// and NDC property (arity is always 2). Mirrors the Haskell tuple
/// `(ByteString, (Privacy, Constructability, NDCstate))`; the field order is
/// that tuple's, which `Ord` reads off.
#[derive(Clone, Copy)]
pub struct AcFctSym {
    /// Interned like `NoEqSym::name` (see there for the rationale).
    pub name: &'static [u8],
    pub privacy: Privacy,
    pub constructability: Constructability,
    pub ndc: NdcState,
}

impl std::fmt::Debug for AcFctSym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AcFctSym")
            .field("name", &String::from_utf8_lossy(self.name))
            .field("privacy", &self.privacy)
            .field("constructability", &self.constructability)
            .field("ndc", &self.ndc)
            .finish()
    }
}

interned_name_sym_impls!(AcFctSym {
    name,
    privacy,
    constructability,
    ndc
});

impl AcFctSym {
    pub fn new(
        name: impl Into<Vec<u8>>,
        privacy: Privacy,
        c: Constructability,
        ndc: NdcState,
    ) -> Self {
        AcFctSym {
            name: crate::intern::intern_bytes(&name.into()),
            privacy,
            constructability: c,
            ndc,
        }
    }
    pub fn with_ndc(mut self, ndc: NdcState) -> Self {
        self.ndc = ndc;
        self
    }
}

/// Haskell `showLitChar` over a single `ByteString` byte (each byte is
/// unpacked to the `Char` with the same code point).
pub fn hs_show_lit_byte(b: u8, out: &mut String) {
    match b {
        b'"' => out.push_str("\\\""),
        b'\\' => out.push_str("\\\\"),
        0x20..=0x7e => out.push(b as char),
        0x7f => out.push_str("\\DEL"),
        // ASCII control mnemonics, in code-point order (`asciiTab`), with the
        // `\a \b \f \n \r \t \v` shortcuts GHC prints for the seven that have
        // one.
        _ if b < 0x20 => {
            const CTRL: [&str; 32] = [
                "\\NUL", "\\SOH", "\\STX", "\\ETX", "\\EOT", "\\ENQ", "\\ACK", "\\a", "\\b", "\\t",
                "\\n", "\\v", "\\f", "\\r", "\\SO", "\\SI", "\\DLE", "\\DC1", "\\DC2", "\\DC3",
                "\\DC4", "\\NAK", "\\SYN", "\\ETB", "\\CAN", "\\EM", "\\SUB", "\\ESC", "\\FS",
                "\\GS", "\\RS", "\\US",
            ];
            out.push_str(CTRL[b as usize]);
        }
        // Above DEL: `'\\' : show (ord c)`, i.e. a decimal escape.
        _ => {
            out.push('\\');
            out.push_str(&b.to_string());
        }
    }
}

/// `plainstring $ show s` for a symbol-name `ByteString`.
///
/// `show` renders the byte string as a Haskell string literal and
/// `plainstring` strips the surrounding quotes again, leaving the
/// literal's escaped BODY.  Symbol names produced by the parser are
/// alphanumeric, so the escaping is inert in practice; it is reproduced for
/// faithfulness.
pub fn plain_show_bytes(name: &[u8]) -> String {
    let mut out = String::with_capacity(name.len());
    for (i, &b) in name.iter().enumerate() {
        let before = out.len();
        hs_show_lit_byte(b, &mut out);
        // GHC `showLitString`'s `\&` separator: a numeric escape followed by a
        // digit, and `\SO` followed by `H`, would otherwise re-lex as a single
        // token.  Both following characters are ASCII, so the next INPUT byte
        // is also the next OUTPUT character.
        let escape = &out[before..];
        let ambiguous = match name.get(i + 1) {
            Some(n) if n.is_ascii_digit() => {
                escape.len() > 1 && escape.as_bytes()[1..].iter().all(u8::is_ascii_digit)
            }
            Some(b'H') => escape == "\\SO",
            _ => false,
        };
        if ambiguous {
            out.push_str("\\&");
        }
    }
    out
}

// -- Derived `Show` of the attribute enums -------------------------------------
//
// The Rust variant names follow Rust's naming convention, so `{:?}` would
// print `IsNdc` where GHC prints `IsNDC`; these three functions spell the
// GHC constructor names.

/// Derived `Show` of `Privacy` (FunctionSymbols.hs:111-112).
pub fn show_privacy(privacy: Privacy) -> &'static str {
    match privacy {
        Privacy::Private => "Private",
        Privacy::Public => "Public",
    }
}

/// Derived `Show` of `Constructability` (FunctionSymbols.hs:116-117).
pub fn show_constructability(constructability: Constructability) -> &'static str {
    match constructability {
        Constructability::Constructor => "Constructor",
        Constructability::Destructor => "Destructor",
    }
}

/// Derived `Show` of `NDCstate` (FunctionSymbols.hs:125-126).
pub fn show_ndc_state(ndc: NdcState) -> &'static str {
    match ndc {
        NdcState::IsNdc => "IsNDC",
        NdcState::NotNdc => "NotNDC",
        NdcState::IsNdcDiff => "IsNDCDiff",
        NdcState::IsNdcBoth => "IsNDCBoth",
    }
}

/// Derived `Show` of the `ACfctSym` tuple
/// `(ByteString, (Privacy, Constructability, NDCstate))`:
/// `("name",(Public,Constructor,NotNDC))` — no spaces after the commas, and
/// the `ByteString` name as a string literal's escaped body.
pub fn show_acfct_sym(sym: &AcFctSym) -> String {
    format!(
        "(\"{}\",({},{},{}))",
        plain_show_bytes(sym.name),
        show_privacy(sym.privacy),
        show_constructability(sym.constructability),
        show_ndc_state(sym.ndc)
    )
}

/// AC (associative-commutative) function symbols.
///
/// Variant order mirrors the Haskell declaration
/// `Union | Mult | Xor | NatPlus | ACfct ACfctSym`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AcSym {
    Union,
    Mult,
    Xor,
    NatPlus,
    AcFct(AcFctSym),
}

/// Commutative (but not associative) function symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CSym {
    EMap,
}

/// A user-defined function symbol: free or AC.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UserDefinedSym {
    NoEqUser(NoEqSym),
    AcFctUser(AcFctSym),
}

impl UserDefinedSym {
    pub fn name(&self) -> &'static [u8] {
        match self {
            UserDefinedSym::NoEqUser(s) => s.name,
            UserDefinedSym::AcFctUser(s) => s.name,
        }
    }
}

/// Top-level function-symbol classification.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum FunSym {
    NoEq(NoEqSym),
    Ac(AcSym),
    C(CSym),
    /// `LIST`: free n-ary symbol of TOP sort.
    List,
}

impl FunSym {
    pub fn is_ac(&self) -> bool {
        matches!(self, FunSym::Ac(_))
    }
    pub fn is_c(&self) -> bool {
        matches!(self, FunSym::C(_))
    }
    pub fn is_list(&self) -> bool {
        matches!(self, FunSym::List)
    }

    /// NDC state of the symbol, or `None` for the variants that carry no NDC
    /// field: the built-in AC operators, `C`, and `LIST`.  Kept in step with
    /// [`FunSym::set_ndc`], which writes back to exactly the two variants that
    /// do carry one.
    fn ndc_state(&self) -> Option<NdcState> {
        match self {
            FunSym::NoEq(s) => Some(s.ndc),
            FunSym::Ac(AcSym::AcFct(s)) => Some(s.ndc),
            _ => None,
        }
    }

    /// HS `isNDCFunSym`: NDC property (trace mode) of the symbol.
    pub fn is_ndc_fun_sym(&self) -> bool {
        self.ndc_state().is_some_and(NdcState::has_ndc)
    }

    /// HS `isNDCDiffFunSym`: NDC property (diff mode) of the symbol.
    pub fn is_ndc_diff_fun_sym(&self) -> bool {
        self.ndc_state().is_some_and(NdcState::has_ndc_diff)
    }

    /// HS `setNDC`: overwrite the NDC state (no-op on non-user symbols).
    pub fn set_ndc(self, ndc: NdcState) -> FunSym {
        match self {
            FunSym::NoEq(s) => FunSym::NoEq(s.with_ndc(ndc)),
            FunSym::Ac(AcSym::AcFct(s)) => FunSym::Ac(AcSym::AcFct(s.with_ndc(ndc))),
            other => other,
        }
    }

    /// HS `addNDC`: join the given NDC state onto the existing one.
    pub fn add_ndc(self, ndc: NdcState) -> FunSym {
        match self.ndc_state() {
            Some(old) => self.set_ndc(ndc.join(old)),
            None => self,
        }
    }
}

/// Function signature.
pub type FunSig = BTreeSet<FunSym>;
/// Free function signature.
pub type NoEqFunSig = BTreeSet<NoEqSym>;
/// User-defined AC function signature.
pub type AcFctFunSig = BTreeSet<AcFctSym>;
/// User-defined function signature.
pub type UserDefinedSig = BTreeSet<UserDefinedSym>;

// =============================================================================
// Symbol-name string constants (matching the Haskell `*SymString` family).
// =============================================================================

pub const DIFF_SYM_STRING: &[u8] = b"diff";
pub const MUN_SYM_STRING: &[u8] = b"mun";
pub const EXP_SYM_STRING: &[u8] = b"exp";
pub const INV_SYM_STRING: &[u8] = b"inv";
pub const ONE_SYM_STRING: &[u8] = b"one";
pub const FST_SYM_STRING: &[u8] = b"fst";
pub const SND_SYM_STRING: &[u8] = b"snd";
pub const DH_NEUTRAL_SYM_STRING: &[u8] = b"DH_neutral";
pub const MULT_SYM_STRING: &[u8] = b"mult";
pub const ZERO_SYM_STRING: &[u8] = b"zero";
pub const XOR_SYM_STRING: &[u8] = b"xor";
pub const NAT_PLUS_SYM_STRING: &[u8] = b"tplus";
pub const NAT_ONE_SYM_STRING: &[u8] = b"tone";
pub const UNION_SYM_STRING: &[u8] = b"union";
pub const EMAP_SYM_STRING: &[u8] = b"em";
pub const PMULT_SYM_STRING: &[u8] = b"pmult";
/// Display name of [`FunSym::List`].  HS has no `listSymString`:
/// `showFunSymName`'s `List` arm spells the literal (Term.hs:296).
pub const LIST_SYM_STRING: &[u8] = b"List";

// -- Predefined NoEq symbols --------------------------------------------------

fn pub_ctor(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
}
fn priv_ctor(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Private, Constructability::Constructor)
}

pub fn pair_sym() -> NoEqSym {
    pub_ctor(b"pair", 2)
}
pub fn diff_sym() -> NoEqSym {
    priv_ctor(DIFF_SYM_STRING, 2)
}
pub fn exp_sym() -> NoEqSym {
    pub_ctor(EXP_SYM_STRING, 2)
}
pub fn inv_sym() -> NoEqSym {
    pub_ctor(INV_SYM_STRING, 1)
}
pub fn one_sym() -> NoEqSym {
    pub_ctor(ONE_SYM_STRING, 0)
}
pub fn dh_neutral_sym() -> NoEqSym {
    pub_ctor(DH_NEUTRAL_SYM_STRING, 0)
}
pub fn fst_sym() -> NoEqSym {
    pub_ctor(FST_SYM_STRING, 1)
}
pub fn snd_sym() -> NoEqSym {
    pub_ctor(SND_SYM_STRING, 1)
}
pub fn pmult_sym() -> NoEqSym {
    pub_ctor(PMULT_SYM_STRING, 2)
}
pub fn zero_sym() -> NoEqSym {
    pub_ctor(ZERO_SYM_STRING, 0)
}
pub fn nat_one_sym() -> NoEqSym {
    pub_ctor(NAT_ONE_SYM_STRING, 0)
}

pub fn fst_dest_sym() -> NoEqSym {
    fst_sym().with_destructor()
}
pub fn snd_dest_sym() -> NoEqSym {
    snd_sym().with_destructor()
}

// -- Predefined signatures ----------------------------------------------------

pub fn dh_fun_sig() -> FunSig {
    [
        FunSym::Ac(AcSym::Mult),
        FunSym::NoEq(exp_sym()),
        FunSym::NoEq(one_sym()),
        FunSym::NoEq(inv_sym()),
        FunSym::NoEq(dh_neutral_sym()),
    ]
    .into_iter()
    .collect()
}

pub fn xor_fun_sig() -> FunSig {
    [FunSym::Ac(AcSym::Xor), FunSym::NoEq(zero_sym())]
        .into_iter()
        .collect()
}

pub fn bp_fun_sig() -> FunSig {
    [FunSym::NoEq(pmult_sym()), FunSym::C(CSym::EMap)]
        .into_iter()
        .collect()
}

pub fn mset_fun_sig() -> FunSig {
    [FunSym::Ac(AcSym::Union)].into_iter().collect()
}

pub fn pair_fun_sig() -> NoEqFunSig {
    [pair_sym(), fst_sym(), snd_sym()].into_iter().collect()
}

pub fn pair_fun_dest_sig() -> NoEqFunSig {
    [pair_sym(), fst_dest_sym(), snd_dest_sym()]
        .into_iter()
        .collect()
}

pub fn dh_reducible_fun_sig() -> FunSig {
    [FunSym::NoEq(exp_sym()), FunSym::NoEq(inv_sym())]
        .into_iter()
        .collect()
}

pub fn bp_reducible_fun_sig() -> FunSig {
    [FunSym::NoEq(pmult_sym()), FunSym::C(CSym::EMap)]
        .into_iter()
        .collect()
}

pub fn xor_reducible_fun_sig() -> FunSig {
    [FunSym::Ac(AcSym::Xor)].into_iter().collect()
}

pub fn implicit_fun_sig() -> FunSig {
    [
        FunSym::NoEq(inv_sym()),
        FunSym::NoEq(pair_sym()),
        FunSym::Ac(AcSym::Mult),
        FunSym::Ac(AcSym::Union),
    ]
    .into_iter()
    .collect()
}

pub fn nat_fun_sig() -> FunSig {
    [FunSym::NoEq(nat_one_sym()), FunSym::Ac(AcSym::NatPlus)]
        .into_iter()
        .collect()
}

#[cfg(test)]
mod tests {
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

    /// FunctionSymbols.hs:
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

    /// FunctionSymbols.hs:
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
    /// `NoEq` comes FIRST.  This ordering matters because BTreeSet<FunSym>
    /// signatures iterate in this order when constructing Maude bridge
    /// commands.  If `List` or `C` came before `NoEq`, Maude would see
    /// declarations in an inconsistent order vs Haskell.
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

    /// Sanity-check: BTreeSet<FunSym> iterates in declaration order.
    /// This is the contract the Maude bridge relies on for
    /// deterministic signature emission.
    #[test]
    fn fun_sym_btreeset_iterates_in_declaration_order() {
        let mut s: std::collections::BTreeSet<FunSym> = Default::default();
        s.insert(FunSym::List);
        s.insert(FunSym::C(CSym::EMap));
        s.insert(FunSym::Ac(AcSym::Union));
        s.insert(FunSym::NoEq(pair_sym()));
        let kinds: Vec<&str> = s
            .iter()
            .map(|f| match f {
                FunSym::NoEq(_) => "NoEq",
                FunSym::Ac(_) => "AC",
                FunSym::C(_) => "C",
                FunSym::List => "List",
            })
            .collect();
        assert_eq!(
            kinds,
            vec!["NoEq", "AC", "C", "List"],
            "BTreeSet<FunSym> must iterate in Haskell decl order"
        );
    }
}
