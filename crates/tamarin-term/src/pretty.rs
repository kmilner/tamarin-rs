// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, beschmi, jdreier, PhilipLukertWork, rsasse, charlie-j,
//   rkunnema, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Term.hs

//! Port of `prettyLNTerm`/`prettyTerm` from
//! `lib/term/src/Term/Term.hs` (lines 267-297) and the `Show LVar` /
//! `Show Name` instances from `lib/term/src/Term/LTerm.hs`.
//!
//! Produces the same surface syntax Tamarin's interactive UI uses:
//!
//! - AC operators render in infix form: `Mult` => `*`, `Xor` => `⊕`
//!   (the single character U+2295, matching the Haskell side's `\8853`),
//!   `Union` => `++`, `NatPlus` => `%+`.
//! - `pair`-trees flatten into `<a,b,c>` notation.
//! - `exp(a,b)` renders as `a^b`, `diff(a,b)` stays as `diff(a, b)`.
//! - The `%1` constant (`tone`) prints as `%1`.
//! - Constants print as `'name'` (matching Haskell's
//!   `Name PubName "alice"` => `'alice'`).
//! - Variables print as `~k`, `$pk`, `#i`, `%n`, etc., with `.idx`
//!   suffix when `idx > 0`.
//!
//! Two entry points are exposed:
//! - [`pretty_lnterm`] returns a `String` (port of `prettyLNTerm`).
//! - `impl Display for LNTerm` (technically on `Term<Lit<Name, LVar>>`).

use std::fmt;

use crate::function_symbols::{
    diff_sym, exp_sym, nat_one_sym, pair_sym, AcSym, CSym, FunSym, EMAP_SYM_STRING,
};
use crate::lterm::{sort_prefix, LSort, LVar, Name, NameTag};
use crate::term::Term;
use crate::vterm::Lit;

/// Pretty-print an `LNTerm` to a `String`.
///
/// Port of `prettyLNTerm` from `Term.LTerm` (`LTerm.hs`)
/// which delegates to `prettyTerm (text . show)`.
pub fn pretty_lnterm<T: PrettyTerm + ?Sized>(t: &T) -> String {
    let mut s = String::new();
    t.pretty_into(&mut s);
    s
}

/// Trait for terms that know how to render themselves in the
/// Haskell-faithful pretty form.  Avoids a free-standing
/// generic-on-`Lit` function so [`Display`] can be implemented on
/// `Term<Lit<Name, LVar>>` directly.
pub trait PrettyTerm {
    fn pretty_into(&self, out: &mut String);
}

// ---------------------------------------------------------------------
// Term<Lit<Name, LVar>> = LNTerm
// ---------------------------------------------------------------------

impl PrettyTerm for Term<Lit<Name, LVar>> {
    fn pretty_into(&self, out: &mut String) {
        pp_term_lnterm(self, out);
    }
}

fn pp_term_lnterm(t: &Term<Lit<Name, LVar>>, out: &mut String) {
    match t {
        Term::Lit(l) => pp_lit_lnterm(l, out),
        Term::App(FunSym::Ac(o), ts) => {
            // Haskell: `ppTerms (ppACOp o) 1 "(" ")" ts` — parenthesised
            // infix list joined by the AC operator symbol.
            out.push('(');
            for (i, child) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(ac_op_symbol(*o));
                }
                pp_term_lnterm(child, out);
            }
            out.push(')');
        }
        // Haskell `prettyTerm` matches full `NoEqSym` equality (incl.
        // privacy/constructability), e.g. `s == expSym` — not just the
        // name+arity (Term.hs:274-277).
        Term::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && *sym == exp_sym() => {
            pp_term_lnterm(&ts[0], out);
            out.push('^');
            pp_term_lnterm(&ts[1], out);
        }
        Term::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && *sym == diff_sym() => {
            out.push_str("diff(");
            pp_term_lnterm(&ts[0], out);
            out.push_str(", ");
            pp_term_lnterm(&ts[1], out);
            out.push(')');
        }
        Term::App(FunSym::NoEq(sym), ts) if ts.is_empty() && *sym == nat_one_sym() => {
            out.push_str("%1");
        }
        Term::App(FunSym::NoEq(sym), _) if *sym == pair_sym() => {
            // Flatten right-associated pair trees.
            let mut flat: Vec<&Term<Lit<Name, LVar>>> = Vec::new();
            collect_pair_tail(t, &mut flat);
            out.push('<');
            for (i, c) in flat.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                pp_term_lnterm(c, out);
            }
            out.push('>');
        }
        Term::App(FunSym::NoEq(sym), ts) => {
            out.push_str(&String::from_utf8_lossy(sym.name));
            if !ts.is_empty() {
                out.push('(');
                for (i, c) in ts.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    pp_term_lnterm(c, out);
                }
                out.push(')');
            }
        }
        Term::App(FunSym::C(CSym::EMap), ts) => {
            out.push_str(&String::from_utf8_lossy(EMAP_SYM_STRING));
            out.push('(');
            for (i, c) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                pp_term_lnterm(c, out);
            }
            out.push(')');
        }
        Term::App(FunSym::List, ts) => {
            // `LIST(...)` — matches Haskell `ppFun "LIST" ts`
            out.push_str("LIST(");
            for (i, c) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                pp_term_lnterm(c, out);
            }
            out.push(')');
        }
    }
}

fn collect_pair_tail<'a>(
    t: &'a Term<Lit<Name, LVar>>,
    out: &mut Vec<&'a Term<Lit<Name, LVar>>>,
) {
    if let Term::App(FunSym::NoEq(sym), args) = t {
        if *sym == pair_sym() && args.len() == 2 {
            collect_pair_tail(&args[0], out);
            collect_pair_tail(&args[1], out);
            return;
        }
    }
    out.push(t);
}

fn pp_lit_lnterm(l: &Lit<Name, LVar>, out: &mut String) {
    match l {
        Lit::Var(v) => pp_lvar(v, out),
        Lit::Con(n) => pp_name(n, out),
    }
}

/// Mirror of Haskell `instance Show LVar` (LTerm.hs:525-532).
pub fn pp_lvar(v: &LVar, out: &mut String) {
    out.push_str(sort_prefix(v.sort));
    if v.name.is_empty() {
        out.push_str(&v.idx.to_string());
    } else if v.idx == 0 {
        out.push_str(v.name);
    } else {
        out.push_str(v.name);
        out.push('.');
        out.push_str(&v.idx.to_string());
    }
}

/// Mirror of Haskell `instance Show Name` (LTerm.hs:231-235).
pub fn pp_name(n: &Name, out: &mut String) {
    let body = format!("'{}'", n.id.0);
    match n.tag {
        NameTag::Fresh => {
            out.push('~');
            out.push_str(&body);
        }
        NameTag::Pub => out.push_str(&body),
        NameTag::Node => {
            out.push('#');
            out.push_str(&body);
        }
        NameTag::Nat => {
            out.push('%');
            out.push_str(&body);
        }
    }
}

pub fn ac_op_symbol(op: AcSym) -> &'static str {
    // Haskell `ppACOp` (Term.hs:283-286).
    //   Mult => "*"; Xor => "⊕"; Union => "++"; NatPlus => "%+"
    // We use the unicode char for Xor since the rest of the UI
    // already passes UTF-8 around and the JS frontend renders it.
    match op {
        AcSym::Mult => "*",
        AcSym::Xor => "\u{2295}",
        AcSym::Union => "++",
        AcSym::NatPlus => "%+",
    }
}

// ---------------------------------------------------------------------
// Display impls — `format!("{}", &term)` just works.
// ---------------------------------------------------------------------

impl fmt::Display for Term<Lit<Name, LVar>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        pp_term_lnterm(self, &mut buf);
        f.write_str(&buf)
    }
}

impl fmt::Display for Lit<Name, LVar> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        pp_lit_lnterm(self, &mut buf);
        f.write_str(&buf)
    }
}

impl fmt::Display for LVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        pp_lvar(self, &mut buf);
        f.write_str(&buf)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        pp_name(self, &mut buf);
        f.write_str(&buf)
    }
}

// Convenience: `LSort` display matches Haskell's `sortSuffix`
// (`Term.LTerm` lines 198-203), NOT the derived `Show LSort`
// (which yields constructor names like `LSortMsg`).
impl fmt::Display for LSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            LSort::Msg => "msg",
            LSort::Fresh => "fresh",
            LSort::Pub => "pub",
            LSort::Node => "node",
            LSort::Nat => "nat",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{
        exp_sym, inv_sym, nat_one_sym, pair_sym, NoEqSym, Privacy, Constructability,
    };
    use crate::lterm::{fresh_term, pub_term, NameTag};
    use crate::term::{f_app_ac, f_app_no_eq, lit};

    fn var(name: &str, sort: LSort) -> Term<Lit<Name, LVar>> {
        lit(Lit::Var(LVar::new(name, sort, 0)))
    }
    fn var_idx(name: &str, sort: LSort, idx: u64) -> Term<Lit<Name, LVar>> {
        lit(Lit::Var(LVar::new(name, sort, idx)))
    }

    #[test]
    fn pretty_msg_var() {
        let t = var("x", LSort::Msg);
        assert_eq!(pretty_lnterm(&t), "x");
    }

    #[test]
    fn pretty_fresh_var_with_index() {
        let t = var_idx("k", LSort::Fresh, 3);
        assert_eq!(pretty_lnterm(&t), "~k.3");
    }

    #[test]
    fn pretty_pub_var_idx0() {
        let t = var("pk", LSort::Pub);
        assert_eq!(pretty_lnterm(&t), "$pk");
    }

    #[test]
    fn pretty_pub_const_unquoted_outer() {
        // Haskell renders `'alice'` with surrounding quotes
        let t: Term<Lit<Name, LVar>> = pub_term("alice");
        assert_eq!(pretty_lnterm(&t), "'alice'");
    }

    #[test]
    fn pretty_fresh_const() {
        let t: Term<Lit<Name, LVar>> = fresh_term("kAB");
        assert_eq!(pretty_lnterm(&t), "~'kAB'");
    }

    #[test]
    fn pretty_pair_flat() {
        // <a, b, c> from right-associated nested pairs
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let c = var("c", LSort::Msg);
        let inner = f_app_no_eq(pair_sym(), vec![b, c]);
        let outer = f_app_no_eq(pair_sym(), vec![a, inner]);
        assert_eq!(pretty_lnterm(&outer), "<a, b, c>");
    }

    #[test]
    fn pretty_xor_infix() {
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let t = f_app_ac(crate::function_symbols::AcSym::Xor, vec![a, b]);
        // AC-normalised order: alphabetic — a, b
        let rendered = pretty_lnterm(&t);
        assert!(rendered.starts_with('(') && rendered.ends_with(')'),
            "got {}", rendered);
        assert!(rendered.contains("\u{2295}"));
    }

    #[test]
    fn pretty_mult_infix() {
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let t = f_app_ac(crate::function_symbols::AcSym::Mult, vec![a, b]);
        let rendered = pretty_lnterm(&t);
        assert!(rendered.starts_with('(') && rendered.ends_with(')'));
        assert!(rendered.contains('*'));
    }

    #[test]
    fn pretty_exp_caret() {
        let g = var("g", LSort::Msg);
        let x = var("x", LSort::Msg);
        let t = f_app_no_eq(exp_sym(), vec![g, x]);
        assert_eq!(pretty_lnterm(&t), "g^x");
    }

    #[test]
    fn pretty_inv_normal_function() {
        let g = var("g", LSort::Msg);
        let t = f_app_no_eq(inv_sym(), vec![g]);
        assert_eq!(pretty_lnterm(&t), "inv(g)");
    }

    #[test]
    fn pretty_nat_one() {
        let t: Term<Lit<Name, LVar>> = f_app_no_eq(nat_one_sym(), vec![]);
        assert_eq!(pretty_lnterm(&t), "%1");
    }

    #[test]
    fn pretty_user_function() {
        // senc(k, m)
        let senc = NoEqSym::new(b"senc".to_vec(), 2, Privacy::Public,
            Constructability::Constructor);
        let k = var("k", LSort::Msg);
        let m = var("m", LSort::Msg);
        let t = f_app_no_eq(senc, vec![k, m]);
        assert_eq!(pretty_lnterm(&t), "senc(k, m)");
    }

    #[test]
    fn display_trait_works() {
        let t = var("x", LSort::Msg);
        assert_eq!(format!("{}", t), "x");
    }

    #[test]
    fn display_for_lvar() {
        let v = LVar::new("foo", LSort::Pub, 0);
        assert_eq!(format!("{}", v), "$foo");
        let v2 = LVar::new("foo", LSort::Pub, 4);
        assert_eq!(format!("{}", v2), "$foo.4");
    }

    #[test]
    fn display_for_name() {
        let n = Name::new(NameTag::Fresh, "kAB");
        assert_eq!(format!("{}", n), "~'kAB'");
        let n2 = Name::new(NameTag::Pub, "alice");
        assert_eq!(format!("{}", n2), "'alice'");
    }

    #[test]
    fn pretty_empty_pub_name_var() {
        // Anonymous var prints just the index.
        let v = LVar::new("", LSort::Msg, 7);
        let t: Term<Lit<Name, LVar>> = lit(Lit::Var(v));
        assert_eq!(pretty_lnterm(&t), "7");
    }
}
