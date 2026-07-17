// Currently GPL 3.0 until granted permission by the following authors:
//   Kevin Morio
// Ported from upstream tamarin-prover sources:
//   lib/export/src/ProVerifHeader.hs

//! Port of `ProVerifHeader` from `lib/export/src/ProVerifHeader.hs`.
//!
//! Header declarations emitted at the top of a ProVerif export. They must
//! be ordered (by variant) and de-duplicated.

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProVerifHeader {
    /// Type declaration.
    Type(String),
    /// Symbol declaration: `(symkind, name, type, attrs)`.
    Sym(String, String, String, Vec<String>),
    /// Function declaration: `(symkind, name, arity, types, attrs)`.
    Fun(String, String, usize, String, Vec<String>),
    /// Event declaration: `(name, type)`, rendered as `event <name><type>.`.
    HEvent(String, String),
    /// Table declaration: `(name, type)`, rendered as `table <name><type>.`.
    Table(String, String),
    /// Equation: `(eqtype, quantif, equation, pub_priv)`.
    Eq(String, String, String, String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordering_groups_by_variant() {
        let mut hs = [ProVerifHeader::Sym("k".into(), "n".into(), "t".into(), vec![]),
            ProVerifHeader::Type("nat".into()),
            ProVerifHeader::Type("bitstring".into())];
        hs.sort();
        // Type variants come before Sym in derived Ord.
        assert!(matches!(hs[0], ProVerifHeader::Type(_)));
        assert!(matches!(hs[1], ProVerifHeader::Type(_)));
        assert!(matches!(hs[2], ProVerifHeader::Sym(_, _, _, _)));
    }

    #[test]
    fn equality_compares_all_fields() {
        let a = ProVerifHeader::Fun("k".into(), "f".into(), 2, "t".into(), vec!["a".into()]);
        let b = ProVerifHeader::Fun("k".into(), "f".into(), 2, "t".into(), vec!["a".into()]);
        let c = ProVerifHeader::Fun("k".into(), "f".into(), 3, "t".into(), vec!["a".into()]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
}
