// Currently GPL 3.0 until granted permission by the following authors:
//   Benedikt Schmidt, Philip Lukert, Charlie Jacomme, Jannik Dreier, Robert
//   Künnemann, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term/FunctionSymbols.hs

//! Port of `Term.Term.FunctionSymbols` from
//! `lib/term/src/Term/Term/FunctionSymbols.hs`.
//!
//! Function-symbol enums and the predefined operator signatures used by
//! Diffie-Hellman, XOR, multiset, bilinear pairing, and natural-number
//! reasoning.

use std::collections::BTreeSet;

/// AC (associative-commutative) function symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AcSym {
    Union,
    Mult,
    Xor,
    NatPlus,
}

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

/// Free (no-equation) function symbol — name plus arity, privacy, and
/// constructability. Mirrors the Haskell tuple
/// `(ByteString, (Int, Privacy, Constructability))`.
#[derive(Clone)]
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
            .finish()
    }
}

// Hand-written `Eq`/`Ord` with an interned-name pointer fast-path.  `name` is
// interned (`intern_bytes`), so equal content ⇒ equal pointer; therefore an
// `as_ptr()` match is true exactly on the common same-symbol path and lets us
// skip the byte `memcmp` that dominated `FunSig::contains` and term comparison
// in the proof search.  Correctness does NOT depend on the interning
// invariant: equal data pointers always imply equal content (same allocation),
// and on a pointer MISmatch we fall back to the full byte comparison — so the
// boolean/total-order is identical to a derived, content-based one.
impl PartialEq for NoEqSym {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Destructure without `..` so a new field forces an equality decision
        // here and in the sibling Hash/Ord impls; all four fields participate.
        let NoEqSym { name, arity, privacy, constructability } = self;
        let NoEqSym {
            name: other_name,
            arity: other_arity,
            privacy: other_privacy,
            constructability: other_constructability,
        } = other;
        (std::ptr::eq(name.as_ptr(), other_name.as_ptr()) || name == other_name)
            && arity == other_arity
            && privacy == other_privacy
            && constructability == other_constructability
    }
}
impl Eq for NoEqSym {}
// Hand-written `Hash` (rather than `derive`d) so it sits alongside the manual
// `PartialEq`/`Ord` above without tripping `clippy::derived_hash_with_manual_eq`
// (a correctness lint: a derived `Hash` next to a hand-written `Eq` risks the
// `a == b ⇒ hash(a) == hash(b)` invariant being violated).  Here both are
// content-based — the `Eq`/`Ord` pointer fast-path only ever returns early when
// the contents are provably equal — so the invariant holds.  The field order matches
// Eq/Ord's (name, arity, privacy, constructability).
impl std::hash::Hash for NoEqSym {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Destructure without `..` so a new field forces a hash decision here,
        // keeping this in step with Eq/Ord; all four fields are hashed.
        let NoEqSym { name, arity, privacy, constructability } = self;
        name.hash(state);
        arity.hash(state);
        privacy.hash(state);
        constructability.hash(state);
    }
}
impl Ord for NoEqSym {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Field order: name, arity, privacy, constructability (consistent with
        // Eq/Hash).  Only the name compare gains the ptr fast-path.  Destructure
        // without `..` so a new field forces an ordering decision here.
        let NoEqSym { name, arity, privacy, constructability } = self;
        let NoEqSym {
            name: other_name,
            arity: other_arity,
            privacy: other_privacy,
            constructability: other_constructability,
        } = other;
        let name_ord = if std::ptr::eq(name.as_ptr(), other_name.as_ptr()) {
            std::cmp::Ordering::Equal
        } else {
            name.cmp(other_name)
        };
        name_ord
            .then_with(|| arity.cmp(other_arity))
            .then_with(|| privacy.cmp(other_privacy))
            .then_with(|| constructability.cmp(other_constructability))
    }
}
impl PartialOrd for NoEqSym {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl NoEqSym {
    pub fn new(name: impl Into<Vec<u8>>, arity: usize, privacy: Privacy, c: Constructability) -> Self {
        NoEqSym { name: crate::intern::intern_bytes(&name.into()), arity, privacy, constructability: c }
    }
    pub fn with_destructor(mut self) -> Self {
        self.constructability = Constructability::Destructor;
        self
    }
}

/// Commutative (but not associative) function symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CSym {
    EMap,
}

/// Top-level function-symbol classification.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FunSym {
    NoEq(NoEqSym),
    Ac(AcSym),
    C(CSym),
    /// `LIST`: free n-ary symbol of TOP sort.
    List,
}

impl FunSym {
    pub fn is_ac(&self) -> bool { matches!(self, FunSym::Ac(_)) }
    pub fn is_c(&self) -> bool { matches!(self, FunSym::C(_)) }
    pub fn is_list(&self) -> bool { matches!(self, FunSym::List) }
}

/// Function signature.
pub type FunSig = BTreeSet<FunSym>;
/// Free function signature.
pub type NoEqFunSig = BTreeSet<NoEqSym>;

// =============================================================================
// Symbol-name string constants (matching the Haskell `*SymString` family).
// =============================================================================

pub const DIFF_SYM_STRING: &[u8]     = b"diff";
pub const MUN_SYM_STRING: &[u8]      = b"mun";
pub const EXP_SYM_STRING: &[u8]      = b"exp";
pub const INV_SYM_STRING: &[u8]      = b"inv";
pub const ONE_SYM_STRING: &[u8]      = b"one";
pub const FST_SYM_STRING: &[u8]      = b"fst";
pub const SND_SYM_STRING: &[u8]      = b"snd";
pub const DH_NEUTRAL_SYM_STRING: &[u8] = b"DH_neutral";
pub const MULT_SYM_STRING: &[u8]     = b"mult";
pub const ZERO_SYM_STRING: &[u8]     = b"zero";
pub const XOR_SYM_STRING: &[u8]      = b"xor";
pub const NAT_PLUS_SYM_STRING: &[u8] = b"tplus";
pub const NAT_ONE_SYM_STRING: &[u8]  = b"tone";
pub const UNION_SYM_STRING: &[u8]    = b"union";
pub const EMAP_SYM_STRING: &[u8]     = b"em";
pub const PMULT_SYM_STRING: &[u8]    = b"pmult";

// -- Predefined NoEq symbols --------------------------------------------------

fn pub_ctor(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
}
fn priv_ctor(name: &[u8], arity: usize) -> NoEqSym {
    NoEqSym::new(name, arity, Privacy::Private, Constructability::Constructor)
}

pub fn pair_sym() -> NoEqSym       { pub_ctor(b"pair", 2) }
pub fn diff_sym() -> NoEqSym       { priv_ctor(DIFF_SYM_STRING, 2) }
pub fn exp_sym() -> NoEqSym        { pub_ctor(EXP_SYM_STRING, 2) }
pub fn inv_sym() -> NoEqSym        { pub_ctor(INV_SYM_STRING, 1) }
pub fn one_sym() -> NoEqSym        { pub_ctor(ONE_SYM_STRING, 0) }
pub fn dh_neutral_sym() -> NoEqSym { pub_ctor(DH_NEUTRAL_SYM_STRING, 0) }
pub fn fst_sym() -> NoEqSym        { pub_ctor(FST_SYM_STRING, 1) }
pub fn snd_sym() -> NoEqSym        { pub_ctor(SND_SYM_STRING, 1) }
pub fn pmult_sym() -> NoEqSym      { pub_ctor(PMULT_SYM_STRING, 2) }
pub fn zero_sym() -> NoEqSym       { pub_ctor(ZERO_SYM_STRING, 0) }
pub fn nat_one_sym() -> NoEqSym    { pub_ctor(NAT_ONE_SYM_STRING, 0) }

pub fn fst_dest_sym() -> NoEqSym { fst_sym().with_destructor() }
pub fn snd_dest_sym() -> NoEqSym { snd_sym().with_destructor() }

// -- Predefined signatures ----------------------------------------------------

pub fn dh_fun_sig() -> FunSig {
    [
        FunSym::Ac(AcSym::Mult),
        FunSym::NoEq(exp_sym()),
        FunSym::NoEq(one_sym()),
        FunSym::NoEq(inv_sym()),
        FunSym::NoEq(dh_neutral_sym()),
    ].into_iter().collect()
}

pub fn xor_fun_sig() -> FunSig {
    [FunSym::Ac(AcSym::Xor), FunSym::NoEq(zero_sym())].into_iter().collect()
}

pub fn bp_fun_sig() -> FunSig {
    [FunSym::NoEq(pmult_sym()), FunSym::C(CSym::EMap)].into_iter().collect()
}

pub fn mset_fun_sig() -> FunSig {
    [FunSym::Ac(AcSym::Union)].into_iter().collect()
}

pub fn pair_fun_sig() -> NoEqFunSig {
    [pair_sym(), fst_sym(), snd_sym()].into_iter().collect()
}

pub fn pair_fun_dest_sig() -> NoEqFunSig {
    [pair_sym(), fst_dest_sym(), snd_dest_sym()].into_iter().collect()
}

pub fn dh_reducible_fun_sig() -> FunSig {
    [FunSym::NoEq(exp_sym()), FunSym::NoEq(inv_sym())].into_iter().collect()
}

pub fn bp_reducible_fun_sig() -> FunSig {
    [FunSym::NoEq(pmult_sym()), FunSym::C(CSym::EMap)].into_iter().collect()
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
    ].into_iter().collect()
}

pub fn nat_fun_sig() -> FunSig {
    [FunSym::NoEq(nat_one_sym()), FunSym::Ac(AcSym::NatPlus)].into_iter().collect()
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
        assert_eq!(fst_dest_sym().constructability, Constructability::Destructor);
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

    /// FunctionSymbols.hs:93:
    ///     data ACSym = Union | Mult | Xor | NatPlus
    #[test]
    fn ac_sym_ord_matches_haskell_declaration() {
        assert!(AcSym::Union < AcSym::Mult);
        assert!(AcSym::Mult  < AcSym::Xor);
        assert!(AcSym::Xor   < AcSym::NatPlus);
    }

    /// FunctionSymbols.hs:97:
    ///     data Privacy = Private | Public
    #[test]
    fn privacy_ord_matches_haskell_declaration() {
        assert!(Privacy::Private < Privacy::Public,
                "Private MUST sort before Public — used in unifiabilty queries");
    }

    /// FunctionSymbols.hs:102:
    ///     data Constructability = Constructor | Destructor
    #[test]
    fn constructability_ord_matches_haskell_declaration() {
        assert!(Constructability::Constructor < Constructability::Destructor);
    }

    /// FunctionSymbols.hs:113-116:
    ///     data FunSym = NoEq NoEqSym | AC ACSym | C CSym | List
    ///
    /// `NoEq` comes FIRST.  This ordering matters because BTreeSet<FunSym>
    /// signatures iterate in this order when constructing Maude bridge
    /// commands.  If `List` or `C` came before `NoEq`, Maude would see
    /// declarations in an inconsistent order vs Haskell.
    #[test]
    fn fun_sym_ord_matches_haskell_declaration() {
        let no_eq = FunSym::NoEq(pair_sym());
        let ac    = FunSym::Ac(AcSym::Mult);
        let c     = FunSym::C(CSym::EMap);
        let list  = FunSym::List;
        assert!(no_eq < ac,   "NoEq < AC (Haskell decl order)");
        assert!(ac    < c,    "AC < C");
        assert!(c     < list, "C < List");
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
        let kinds: Vec<&str> = s.iter().map(|f| match f {
            FunSym::NoEq(_) => "NoEq",
            FunSym::Ac(_) => "AC",
            FunSym::C(_) => "C",
            FunSym::List => "List",
        }).collect();
        assert_eq!(kinds, vec!["NoEq", "AC", "C", "List"],
                   "BTreeSet<FunSym> must iterate in Haskell decl order");
    }
}
