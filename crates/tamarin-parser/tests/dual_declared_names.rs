// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Declaration-side parity for DUAL-DECLARED names — one name that is both a
//! `NoEq` funsym and a user-declared `[AC]` symbol.
//!
//! HS `function`'s conflict check (Parser/Signature.hs:212-217) looks the name
//! up in `stFunSyms` only, and an `[AC]` declaration registers under
//! `stACFunSyms` (`addFunSym (ACfctUser …)`, Parser/Signature.hs:221), so the two declarations
//! never collide directly: `f/2 [AC], f/2` and `f/2, f/2 [AC]` are BOTH
//! accepted (the compared options tuple `(k,priv,destr,ndc)` carries no AC
//! flag).  Only a NoEq declaration whose tuple DIFFERS from the `[AC]`
//! declaration's requested tuple conflicts — and only in the NoEq-first
//! order, where `stFunSyms` already holds it.
//!
//! WHICH theories are rejected (and which load) is pinned to the Haskell
//! oracle (Git revision ef3f0468).  The positions are the port's own: they
//! point at the two declarations.

use tamarin_parser::parser::ParseContext;
use tamarin_parser::{parse_theory, ParseError, TheoryItem};

/// The two `f` declarations of a parsed dual theory, `(ac, arity)` per decl
/// in source order.
fn f_decls(src: &str) -> Vec<(bool, usize)> {
    let thy = parse_theory(src, &[]).expect("parse");
    let mut out = Vec::new();
    for it in &thy.items {
        if let TheoryItem::Functions(decls) = it {
            for d in decls {
                if d.name == "f" {
                    out.push((d.ac, d.arg_types.len()));
                }
            }
        }
    }
    out
}

/// Both declaration orders are accepted and keep both symbols.
#[test]
fn both_declaration_orders_are_accepted() {
    assert_eq!(
        f_decls("theory T begin\n\nfunctions: f/2 [AC], f/2\n\nend\n"),
        [(true, 2), (false, 2)]
    );
    assert_eq!(
        f_decls("theory T begin\n\nfunctions: f/2, f/2 [AC]\n\nend\n"),
        [(false, 2), (true, 2)]
    );
    // A NoEq declaration at a DIFFERENT arity after the `[AC]` one is also
    // accepted — `stFunSyms` holds nothing under `f` when it is checked.
    assert_eq!(
        f_decls("theory T begin\n\nfunctions: f/2 [AC], f/3\n\nend\n"),
        [(true, 2), (false, 3)]
    );
}

/// The NoEq-first order at a different arity DOES conflict: the `[AC]`
/// declaration's requested tuple is compared against the `stFunSyms` entry
/// (Parser/Signature.hs:212-215; oracle probe `p_orderconf`).  The port
/// reports [`ParseError::ConflictingDeclarations`] with both declaration
/// sites.
#[test]
fn a_noeq_first_arity_mismatch_conflicts() {
    let e = parse_theory("theory T begin\n\nfunctions: f/3, f/2 [AC]\n\nend\n", &[])
        .expect_err("the NoEq-first order conflicts");
    let ParseError::ConflictingDeclarations {
        name,
        context: ParseContext::Function,
        first_at,
        second_at,
    } = e
    else {
        panic!("expected the conflict variant, got {e:?}");
    };
    assert_eq!(name, "f");
    let first_at = first_at.expect("the NoEq declaration has a site");
    assert_eq!((first_at.line, first_at.col), (3, 12));
    assert_eq!((second_at.line, second_at.col), (3, 17));
}

/// The AST keeps the two spellings of a dual name apart: prefix is a plain
/// `App` (which the readers resolve NoEq-first, HS `lookupArity`,
/// Parser/Term.hs:62-71), infix is `BinOp::AcFct` (always the AC symbol, HS
/// `acterm`, Parser/Term.hs:165-172).  The oracle renders the two differently in one
/// rule — `A( ('a' f 'b') ), B( f('a', 'b') )` (probe `p_infix`) — which is
/// only representable with distinct nodes.
#[test]
fn infix_and_prefix_spellings_parse_to_distinct_nodes() {
    use tamarin_parser::ast::{BinOp, Term};
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2\n\n\
               rule R:\n\
               \x20 [ ] --[ A('a' f 'b'), B(f('a','b')) ]-> [ ]\n\n\
               end\n";
    let thy = parse_theory(src, &[]).expect("parse");
    let rule = thy
        .items
        .iter()
        .find_map(|it| match it {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("one rule");
    match &rule.actions[0].args[0] {
        Term::BinOp(BinOp::AcFct("f"), _, _) => {}
        other => panic!("expected the infix spelling as BinOp::AcFct, got {other:?}"),
    }
    match &rule.actions[1].args[0] {
        Term::App(name, args) if name == "f" && args.len() == 2 => {}
        other => panic!("expected the prefix spelling as App, got {other:?}"),
    }
}
