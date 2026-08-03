// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, beschmi, jdreier, PhilipLukertWork, rsasse, charlie-j, and
//   other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Term.hs

//! Port of `prettyLNTerm`/`prettyTerm` from
//! `lib/term/src/Term/Term.hs` (lines 298-327) and the `Show LVar` /
//! `Show Name` instances from `lib/term/src/Term/LTerm.hs`.
//!
//! Produces the same surface syntax Tamarin's interactive UI uses:
//!
//! - AC operators render in infix form: `Mult` => `*`, `Xor` => `⊕`
//!   (the single character U+2295, matching the Haskell side's `\8853`),
//!   `Union` => `++`, `NatPlus` => `%+`.
//! - A user-defined AC symbol `f` renders infix with its name surrounded
//!   by spaces (`(a f b)`), or as the bare name when applied to no
//!   arguments.
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

use std::cell::RefCell;
use std::fmt;

use tamarin_utils::FastMap;

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
        // Haskell `prettyTerm` matches the user-defined AC symbols BEFORE the
        // builtin AC operators, and prints a nullary application as the bare
        // symbol name (`FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)`).
        // Non-nullary ones fall through to the generic AC arm below, whose
        // separator `ac_op_symbol` renders as `" f "`.
        Term::App(FunSym::Ac(AcSym::AcFct(sym)), ts) if ts.is_empty() => {
            out.push_str(&String::from_utf8_lossy(sym.name));
        }
        Term::App(FunSym::Ac(o), ts) => {
            // Haskell: `ppTerms <op> 1 "(" ")" ts` — parenthesised
            // infix list joined by the AC operator symbol.  The separator
            // only ever appears BETWEEN operands, so a 1-element `ts` never
            // resolves one.
            let op = if ts.len() > 1 { ac_op_symbol(*o) } else { "" };
            out.push('(');
            for (i, child) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(op);
                }
                pp_term_lnterm(child, out);
            }
            out.push(')');
        }
        // Haskell `prettyTerm` matches full `NoEqSym` equality (incl.
        // privacy/constructability), e.g. `s == expSym` — not just the
        // name+arity (Term.hs:310-313).
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

/// HS `split` (Term.hs:323-324): `split (viewTerm2 -> FPair t1 t2) = t1 :
/// split t2; split t = [t]`.  ONLY the RIGHT spine of a pair is flattened —
/// `pair(t1, t2)` yields `t1` then recurses into `t2`.  A LEFT-nested pair
/// such as `pair(pair(a,b), c)` therefore renders as `<<a, b>, c>` (the left
/// child is printed by the recursive term printer, NOT flattened here).
fn collect_pair_tail<'a>(t: &'a Term<Lit<Name, LVar>>, out: &mut Vec<&'a Term<Lit<Name, LVar>>>) {
    if let Term::App(FunSym::NoEq(sym), args) = t {
        if *sym == pair_sym() && args.len() == 2 {
            out.push(&args[0]);
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

/// Mirror of Haskell `instance Show Name` (LTerm.hs:235-240).
pub fn pp_name(n: &Name, out: &mut String) {
    match n.tag {
        NameTag::Fresh => out.push('~'),
        NameTag::Pub => {}
        NameTag::Node => out.push('#'),
        NameTag::Nat => out.push('%'),
        // `show (Name AbbrevName n) = show n` (LTerm.hs:240) — the bare name
        // id, with neither a sigil nor the quotes the other four tags carry.
        NameTag::Abbrev => {
            out.push_str(n.id.0);
            return;
        }
    }
    out.push('\'');
    out.push_str(n.id.0);
    out.push('\'');
}

pub fn ac_op_symbol(op: AcSym) -> &'static str {
    // Haskell `prettyTerm`'s AC arms (Term.hs:304-309).
    //   Mult => "*"; Xor => "⊕"; Union => "++"; NatPlus => "%+"
    // We use the unicode char for Xor since the rest of the UI
    // already passes UTF-8 around and the JS frontend renders it.
    match op {
        AcSym::Mult => "*",
        AcSym::Xor => "\u{2295}",
        AcSym::Union => "++",
        AcSym::NatPlus => "%+",
        AcSym::AcFct(sym) => ac_fct_op_symbol_interned(sym.name),
    }
}

thread_local! {
    /// Per-thread cache of user-defined AC separators, keyed on the IDENTITY
    /// of the symbol's interned name.  `AcFctSym::new` draws `name` from the
    /// byte intern pool, so the pointer is valid for the whole process and
    /// equal names share one address; `(ptr, len)` therefore names exactly
    /// one immutable byte string, and a hit returns the same `&'static str`
    /// the interning path below would.  Bounded per worker thread by the
    /// theory's user-defined AC signature.
    static AC_FCT_OP_L1: RefCell<FastMap<(usize, usize), &'static str>> =
        RefCell::new(FastMap::default());
}

/// [`ac_fct_op_symbol`] for a symbol name that is already interned: the
/// separator comes out of the per-thread cache, so rendering a user-AC
/// application allocates nothing.
fn ac_fct_op_symbol_interned(name: &'static [u8]) -> &'static str {
    let key = (name.as_ptr() as usize, name.len());
    if let Some(sep) = AC_FCT_OP_L1.with(|c| c.borrow().get(&key).copied()) {
        return sep;
    }
    let sep = ac_fct_op_symbol(&String::from_utf8_lossy(name));
    AC_FCT_OP_L1.with(|c| c.borrow_mut().insert(key, sep));
    sep
}

/// The infix separator of a user-defined AC symbol: Haskell
/// `ppTerms (" " ++ BC.unpack f ++ " ") 1 "(" ")" ts` (Term.hs:305) surrounds
/// the symbol name by spaces, so the spaces are part of the separator (unlike
/// the builtin ops).  Interned so it can be handed out as `&'static str` like
/// the fixed ones; the pool is bounded by the theory's user-defined AC names.
/// This is the by-content entry point (the parser-AST printer holds names as
/// `String`s); [`ac_op_symbol`] reaches the same strings by symbol identity.
pub fn ac_fct_op_symbol(name: &str) -> &'static str {
    crate::intern::intern_str(&format!(" {} ", name))
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
// (`Term.LTerm` lines 202-207), NOT the derived `Show LSort`
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
        exp_sym, inv_sym, nat_one_sym, pair_sym, Constructability, NoEqSym, Privacy,
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
    fn pretty_pair_left_nested_not_flattened() {
        // HS `split` unrolls only the RIGHT spine: pair(pair(a,b), c)
        // renders `<<a, b>, c>`, keeping the render round-trippable
        // (`<a, b, c>` would re-parse as the right-nested pair(a, pair(b,c))).
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let c = var("c", LSort::Msg);
        let inner = f_app_no_eq(pair_sym(), vec![a, b]);
        let outer = f_app_no_eq(pair_sym(), vec![inner, c]);
        assert_eq!(pretty_lnterm(&outer), "<<a, b>, c>");
    }

    #[test]
    fn pretty_xor_infix() {
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let t = f_app_ac(crate::function_symbols::AcSym::Xor, vec![a, b]);
        // AC-normalised order: alphabetic — a, b
        let rendered = pretty_lnterm(&t);
        assert!(
            rendered.starts_with('(') && rendered.ends_with(')'),
            "got {}",
            rendered
        );
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
        let senc = NoEqSym::new(
            b"senc".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        let k = var("k", LSort::Msg);
        let m = var("m", LSort::Msg);
        let t = f_app_no_eq(senc, vec![k, m]);
        assert_eq!(pretty_lnterm(&t), "senc(k, m)");
    }

    #[test]
    fn pretty_user_ac_infix_and_nullary() {
        use crate::function_symbols::{AcFctSym, AcSym, NdcState};
        let f = AcFctSym::new(
            b"f".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let t = f_app_ac(AcSym::AcFct(f), vec![a, b]);
        assert_eq!(pretty_lnterm(&t), "(a f b)");
        // HS `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term.hs:304):
        // the bare name, no parens.  `f_app_ac` rejects an empty argument list
        // (HS `fAppAC` errors likewise), so the arm is reachable only by direct
        // construction.
        let nullary: Term<Lit<Name, LVar>> = Term::App(FunSym::Ac(AcSym::AcFct(f)), vec![].into());
        assert_eq!(pretty_lnterm(&nullary), "f");
    }

    #[test]
    fn ac_fct_separator_shared_across_attributes() {
        use crate::function_symbols::{AcFctSym, AcSym, NdcState};
        let plain = AcFctSym::new(
            b"op".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        // Same name, every other field different: the separator depends on the
        // name alone, so both resolve to the one interned string.
        let decorated = AcFctSym::new(
            b"op".to_vec(),
            Privacy::Private,
            Constructability::Destructor,
            NdcState::IsNdc,
        );
        let a = ac_op_symbol(AcSym::AcFct(plain));
        let b = ac_op_symbol(AcSym::AcFct(decorated));
        assert_eq!(a, " op ");
        assert_eq!(a.as_ptr(), b.as_ptr());
        // A name of which `op` is a prefix gets its own separator.
        let longer = AcFctSym::new(
            b"opq".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        assert_eq!(ac_op_symbol(AcSym::AcFct(longer)), " opq ");
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
