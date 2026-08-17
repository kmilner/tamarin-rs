// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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

    /// The derived `Ord` exists for the declaration order of the six
    /// constructors.  `attribHeaders` sorts by that order, and so does the
    /// `S.toList` that feeds the header block in the output.  A different
    /// order of the enum therefore changes the order of the ProVerif output,
    /// and nothing reports an error.  The test sorts a shuffled set with one
    /// member of each variant.  That check covers the complete sequence of
    /// discriminants, not one pair alone.
    #[test]
    fn ordering_follows_upstream_declaration_order() {
        let mut hs = [
            ProVerifHeader::Eq("e".into(), "q".into(), "u".into(), "p".into()),
            ProVerifHeader::Table("t".into(), "ty".into()),
            ProVerifHeader::Sym("k".into(), "n".into(), "t".into(), vec![]),
            ProVerifHeader::HEvent("ev".into(), "ty".into()),
            ProVerifHeader::Type("nat".into()),
            ProVerifHeader::Fun("k".into(), "f".into(), 2, "t".into(), vec![]),
        ];
        hs.sort();
        let variants: Vec<&str> = hs
            .iter()
            .map(|h| match h {
                ProVerifHeader::Type(_) => "Type",
                ProVerifHeader::Sym(..) => "Sym",
                ProVerifHeader::Fun(..) => "Fun",
                ProVerifHeader::HEvent(..) => "HEvent",
                ProVerifHeader::Table(..) => "Table",
                ProVerifHeader::Eq(..) => "Eq",
            })
            .collect();
        assert_eq!(
            variants,
            ["Type", "Sym", "Fun", "HEvent", "Table", "Eq"],
            "ProVerifHeader.hs:4-11 declaration order"
        );
        // Inside one variant the fields break the tie from left to right.
        // The arity of `Fun` (field 3) therefore outranks its type string
        // (field 4).
        let mut funs = [
            ProVerifHeader::Fun("k".into(), "f".into(), 2, "zz".into(), vec![]),
            ProVerifHeader::Fun("k".into(), "f".into(), 1, "aa".into(), vec![]),
        ];
        funs.sort();
        assert!(matches!(funs[0], ProVerifHeader::Fun(_, _, 1, _, _)));
    }
}
