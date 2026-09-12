// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! The entry points are:
//! - [`pretty_term`], the `Doc` printer parameterised over the printer of the
//!   term's literals, and [`pretty_nterm`] at `NTerm v = VTerm Name v`;
//! - [`pretty_lnterm`], the same flat syntax written iteratively to a `String`;
//! - `impl Display for LNTerm` (technically on `Term<Lit<Name, LVar>>`).

use std::fmt;
use std::fmt::Write as _;
use std::sync::{OnceLock, RwLock};

use tamarin_utils::pretty_hpj::{fcat, fsep, parens, punctuate, Doc};
#[cfg(test)]
use tamarin_utils::pretty_hpj::{HtmlDocGuard, FLAT_WIDTH};
use tamarin_utils::FastMap;

use crate::function_symbols::{
    diff_sym, exp_sym, nat_one_sym, pair_sym, AcSym, CSym, FunSym, EMAP_SYM_STRING,
};
use crate::lterm::{sort_prefix, BVar, LNTerm, LSort, LVar, Name, NameTag};
use crate::term::{ShowLit, Term};
use crate::vterm::{Lit, VTerm};

/// Mirror of Haskell `instance Show LVar` (LTerm.hs:550-557).
pub fn pp_lvar(v: &LVar, out: &mut String) {
    out.push_str(sort_prefix(v.sort));
    if v.name.is_empty() {
        let _ = write!(out, "{}", v.idx);
    } else if v.idx == 0 {
        out.push_str(v.name);
    } else {
        out.push_str(v.name);
        out.push('.');
        let _ = write!(out, "{}", v.idx);
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
    // Haskell `prettyTerm`'s AC arms (Term/Term.hs:304-309).
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

/// One process-wide cache of user-defined AC separators, keyed on the IDENTITY
/// of the symbol's interned name.  `AcFctSym::new` draws `name` from the byte
/// intern pool, so the pointer is valid for the whole process and equal names
/// share one address; `(ptr, len)` therefore names exactly one immutable byte
/// string.  Every entry is a canonical `&'static str` from the string intern
/// pool, determined by the key's content alone, so all threads see the one
/// separator per name whether they hit or miss.  Bounded by the theory's
/// user-defined AC signature.
fn ac_fct_op_cache() -> &'static RwLock<FastMap<(usize, usize), &'static str>> {
    static C: OnceLock<RwLock<FastMap<(usize, usize), &'static str>>> = OnceLock::new();
    C.get_or_init(|| RwLock::new(FastMap::default()))
}

/// [`ac_fct_op_symbol`] for a symbol name that is already interned: a hit is a
/// read-locked lookup on the `(ptr, len)` key, so rendering a user-AC
/// application allocates nothing.
fn ac_fct_op_symbol_interned(name: &'static [u8]) -> &'static str {
    let key = (name.as_ptr() as usize, name.len());
    if let Some(&sep) = ac_fct_op_cache().read().unwrap().get(&key) {
        return sep;
    }
    // Resolved before the write lock is taken: `ac_fct_op_symbol` locks the
    // intern pool, and holding both at once would nest the two locks.  A
    // concurrent miss on the same key resolves to the same canonical pointer,
    // so the losing insert overwrites the entry with an identical value.
    let sep = ac_fct_op_symbol(&String::from_utf8_lossy(name));
    ac_fct_op_cache().write().unwrap().insert(key, sep);
    sep
}

/// The infix separator of a user-defined AC symbol: Haskell
/// `ppTerms (" " ++ BC.unpack f ++ " ") 1 "(" ")" ts` (Term/Term.hs:305) surrounds
/// the symbol name by spaces, so the spaces are part of the separator (unlike
/// the builtin ops).  Interned so it can be handed out as `&'static str` like
/// the fixed ones; the pool is bounded by the theory's user-defined AC names.
/// This is the by-content entry point (the parser-AST printer holds names as
/// `String`s); [`ac_op_symbol`] reaches the same strings by symbol identity.
pub fn ac_fct_op_symbol(name: &str) -> &'static str {
    crate::intern::intern_str(&format!(" {} ", name))
}

// ---------------------------------------------------------------------
// `prettyTerm` — the Doc printer (Term/Term.hs:299-327).
// ---------------------------------------------------------------------

/// HS `prettyTerm :: (Document d, Show l) => (l -> d) -> Term l -> d`
/// (Term/Term.hs:299-317), parameterised over the printer of the term's
/// literals.  The arms keep HS's order: a nullary user-`[AC]` symbol before
/// the generic AC arm, and `exp`/`diff`/`%1`/`pair` before the generic `NoEq`
/// arms.  Each of those four guards compares the whole `NoEqSym`, as HS's
/// `s == expSym` does, so a symbol that only shares the name renders through
/// the generic arm.
pub fn pretty_term<L>(pp_lit: &dyn Fn(&L) -> Doc, t: &Term<L>) -> Doc {
    enum Frame<'a, L> {
        Visit(&'a Term<L>),
        Finish(&'a FunSym, &'a [Term<L>], usize),
    }
    // Leaf printers need neither a worklist nor an operand vector.
    match t {
        Term::Lit(literal) => return pp_lit(literal),
        Term::App(symbol, args) if args.is_empty() => {
            return pretty_app(symbol, args, Vec::new());
        }
        _ => {}
    }
    let mut pending = vec![Frame::Visit(t)];
    let mut docs = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Visit(Term::Lit(literal)) => docs.push(pp_lit(literal)),
            Frame::Visit(term @ Term::App(symbol, args)) => {
                pending.push(Frame::Finish(symbol, args, docs.len()));
                if matches!(symbol, FunSym::NoEq(sym) if *sym == pair_sym()) && args.len() == 2 {
                    let mut flat = Vec::new();
                    split_pair(term, &mut flat);
                    pending.extend(flat.into_iter().rev().map(Frame::Visit));
                } else {
                    pending.extend(args.iter().rev().map(Frame::Visit));
                }
            }
            Frame::Finish(symbol, args, start) => {
                let children = docs.split_off(start);
                docs.push(pretty_app(symbol, args, children));
            }
        }
    }
    docs.pop().unwrap()
}

// Build a parent only after its children have been printed in source order.
// Child Docs retain exactly the same nesting, separators and alternatives as
// the recursive printer; the worklist changes only term traversal.
fn pretty_app<L>(symbol: &FunSym, ts: &[Term<L>], mut docs: Vec<Doc>) -> Doc {
    match symbol {
        // `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term/Term.hs:304).
        FunSym::Ac(AcSym::AcFct(sym)) if ts.is_empty() => {
            Doc::text(String::from_utf8_lossy(sym.name))
        }
        FunSym::Ac(o @ AcSym::AcFct(_)) => {
            let docs = ts.iter().zip(docs).map(|(term, doc)| {
                // User AC operators bind more tightly than exponentiation.
                if matches!(term, Term::App(FunSym::NoEq(sym), args) if *sym == exp_sym() && args.len() == 2) {
                    parens(doc)
                } else {
                    doc
                }
            }).collect();
            pp_docs(ac_op_symbol(*o), 1, "(", ")", docs)
        }
        FunSym::Ac(o) => pp_docs(ac_op_symbol(*o), 1, "(", ")", docs),
        FunSym::NoEq(sym) if ts.len() == 2 && *sym == exp_sym() => {
            let right = docs.pop().unwrap();
            docs.pop().unwrap().beside(Doc::text("^")).beside(right)
        }
        // All `<>` (Term/Term.hs:311): a diff comma never breaks.
        FunSym::NoEq(sym) if ts.len() == 2 && *sym == diff_sym() => {
            let right = docs.pop().unwrap();
            Doc::text("diff")
                .beside(Doc::text("("))
                .beside(docs.pop().unwrap())
                .beside(Doc::text(", "))
                .beside(right)
                .beside(Doc::text(")"))
        }
        FunSym::NoEq(sym) if ts.is_empty() && *sym == nat_one_sym() => Doc::text("%1"),
        // `split` (Term/Term.hs:323-324) flattens only binary pairs.
        FunSym::NoEq(sym) if ts.len() == 2 && *sym == pair_sym() => {
            pp_docs(", ", 1, "<", ">", docs)
        }
        FunSym::NoEq(sym) if ts.is_empty() => Doc::text(String::from_utf8_lossy(sym.name)),
        FunSym::NoEq(sym) => pp_fun(&String::from_utf8_lossy(sym.name), docs),
        FunSym::C(CSym::EMap) => pp_fun(&String::from_utf8_lossy(EMAP_SYM_STRING), docs),
        FunSym::List => pp_fun("LIST", docs),
    }
}

/// HS `prettyNTerm = prettyTerm (text . show)` (LTerm.hs:930-931) over
/// `NTerm v = VTerm Name v` (LTerm.hs:227), whose literal printer is
/// `Show (Lit c v)` (VTerm.hs:98-100).
pub fn pretty_nterm<V: fmt::Display>(t: &VTerm<Name, V>) -> Doc {
    pretty_term(&|l: &Lit<Name, V>| Doc::text(l.to_string()), t)
}

/// HS `prettyLNTerm = prettyNTerm` (LTerm.hs:934-935), laid out on a
/// single line. Write the flat syntax directly: constructing a HughesPJ
/// document here would allocate layout alternatives which can never be used.
/// The explicit worklist also keeps native stack use independent of term depth.
/// Output is plain text even inside an HTML rendering context.
pub fn pretty_lnterm(t: &LNTerm) -> String {
    enum Frame<'a> {
        Term(&'a LNTerm),
        Text(&'static str),
        Args(&'a [LNTerm], &'static str, bool),
        PairTail(&'a LNTerm),
        FunArgs(&'a [LNTerm]),
    }
    let mut out = String::new();
    let mut pending = Vec::new();
    let mut next = Some(Frame::Term(t));
    while let Some(frame) = next.take().or_else(|| pending.pop()) {
        let t = match frame {
            Frame::Text(text) => {
                out.push_str(text);
                continue;
            }
            Frame::FunArgs(args) => {
                if let Some((first, rest)) = args.split_first() {
                    if !rest.is_empty() {
                        pending.push(Frame::FunArgs(rest));
                        // fsep discards an empty final Doc after punctuate:
                        // the preceding comma remains, but its space does not.
                        let separator = if rest.len() == 1 && flat_term_is_empty(&rest[0]) {
                            ","
                        } else {
                            ", "
                        };
                        pending.push(Frame::Text(separator));
                    }
                    next = Some(Frame::Term(first));
                }
                continue;
            }
            Frame::Args(args, separator, user_ac) => {
                if let Some((first, rest)) = args.split_first() {
                    if !rest.is_empty() {
                        pending.push(Frame::Args(rest, separator, user_ac));
                        pending.push(Frame::Text(separator));
                    }
                    if user_ac
                        && matches!(first, Term::App(FunSym::NoEq(sym), args)
                            if *sym == exp_sym() && args.len() == 2)
                    {
                        out.push('(');
                        pending.push(Frame::Text(")"));
                    }
                    next = Some(Frame::Term(first));
                }
                continue;
            }
            Frame::PairTail(term) => {
                if let Term::App(FunSym::NoEq(sym), args) = term
                    && *sym == pair_sym()
                    && args.len() == 2
                {
                    pending.push(Frame::PairTail(&args[1]));
                    pending.push(Frame::Text(", "));
                    next = Some(Frame::Term(&args[0]));
                } else {
                    next = Some(Frame::Term(term));
                }
                continue;
            }
            Frame::Term(term) => term,
        };
        match t {
            Term::Lit(literal) => literal.show_into(&mut out),
            Term::App(FunSym::Ac(AcSym::AcFct(sym)), args) if args.is_empty() => {
                out.push_str(&String::from_utf8_lossy(sym.name));
            }
            Term::App(FunSym::Ac(op), args) => {
                out.push('(');
                pending.push(Frame::Text(")"));
                next = Some(Frame::Args(
                    args,
                    ac_op_symbol(*op),
                    matches!(op, AcSym::AcFct(_)),
                ));
            }
            Term::App(FunSym::NoEq(sym), args) if *sym == exp_sym() && args.len() == 2 => {
                pending.push(Frame::Term(&args[1]));
                pending.push(Frame::Text("^"));
                next = Some(Frame::Term(&args[0]));
            }
            Term::App(FunSym::NoEq(sym), args) if *sym == diff_sym() && args.len() == 2 => {
                out.push_str("diff(");
                pending.push(Frame::Text(")"));
                next = Some(Frame::Args(args, ", ", false));
            }
            Term::App(FunSym::NoEq(sym), args) if *sym == nat_one_sym() && args.is_empty() => {
                out.push_str("%1");
            }
            Term::App(FunSym::NoEq(sym), args) if *sym == pair_sym() && args.len() == 2 => {
                out.push('<');
                pending.push(Frame::Text(">"));
                next = Some(Frame::PairTail(t));
            }
            Term::App(FunSym::NoEq(sym), args) if args.is_empty() => {
                out.push_str(&String::from_utf8_lossy(sym.name));
            }
            Term::App(symbol, args) => {
                let name = match symbol {
                    FunSym::NoEq(sym) => String::from_utf8_lossy(sym.name),
                    FunSym::C(CSym::EMap) => String::from_utf8_lossy(EMAP_SYM_STRING),
                    FunSym::List => "LIST".into(),
                    FunSym::Ac(_) => unreachable!(),
                };
                out.push_str(&name);
                out.push('(');
                pending.push(Frame::Text(")"));
                next = Some(Frame::FunArgs(args));
            }
        }
    }
    out
}

// These are the only term forms whose flat document is Empty; every
// non-nullary application contributes punctuation, even with an empty name.
fn flat_term_is_empty(term: &LNTerm) -> bool {
    match term {
        Term::Lit(Lit::Con(name)) => name.tag == NameTag::Abbrev && name.id.0.is_empty(),
        Term::App(FunSym::NoEq(sym), args) => args.is_empty() && sym.name.is_empty(),
        Term::App(FunSym::Ac(AcSym::AcFct(sym)), args) => args.is_empty() && sym.name.is_empty(),
        _ => false,
    }
}

/// HS `ppTerms sepa n lead finish ts` (Term/Term.hs:319-321):
/// `fcat . (text lead :) . (++[text finish]) . map (nest n)
///       . punctuate (text sepa) . map ppTerm`.
fn pp_docs(sepa: &str, n: isize, lead: &str, finish: &str, docs: Vec<Doc>) -> Doc {
    let items = punctuate(Doc::text(sepa), docs);
    let mut all: Vec<Doc> = Vec::with_capacity(items.len() + 2);
    all.push(Doc::text(lead));
    for d in items {
        all.push(d.nest(n));
    }
    all.push(Doc::text(finish));
    fcat(all)
}

/// HS `ppFun f ts` (Term/Term.hs:326-327):
/// `text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"`.
fn pp_fun(f: &str, docs: Vec<Doc>) -> Doc {
    Doc::text(format!("{}(", f))
        .beside(fsep(punctuate(Doc::char(','), docs)))
        .beside(Doc::text(")"))
}

/// HS `split` (Term/Term.hs:323-324): `split (viewTerm2 -> FPair t1 t2) = t1 :
/// split t2; split t = [t]`.  `FPair` (Term/Term/Raw.hs:194) needs exactly two
/// arguments and full `NoEqSym` equality with `pairSym`, and only the RIGHT
/// child continues the spine, so `pair(pair(a, b), c)` keeps its left child
/// nested.
fn split_pair<'a, L>(mut t: &'a Term<L>, out: &mut Vec<&'a Term<L>>) {
    while let Term::App(FunSym::NoEq(sym), ts) = t {
        if ts.len() != 2 || *sym != pair_sym() {
            break;
        }
        out.push(&ts[0]);
        t = &ts[1];
    }
    out.push(t);
}

// ---------------------------------------------------------------------
// `ShowLit` impls — the literal half of HS `Show (Term a)`.
// ---------------------------------------------------------------------

/// HS `instance (Show v, Show c) => Show (Lit c v)` (Term/VTerm.hs:98-100) at
/// `Lit Name LVar`, the literal of an `LNTerm`.  Both sides are the same
/// `Show` instances the pretty-printer reuses for its leaves: `Show LVar`
/// (LTerm.hs:550-557) and `Show Name` (LTerm.hs:235-240).
impl ShowLit for Lit<Name, LVar> {
    fn show_into(&self, out: &mut String) {
        match self {
            Lit::Var(v) => pp_lvar(v, out),
            Lit::Con(n) => pp_name(n, out),
        }
    }
}

/// The same instance at `Lit Name (BVar LVar)`, the literal of a `BLTerm`.
/// Its variable side is the derived `Show (BVar v)` (LTerm.hs:476-478):
/// `Bound <i>` for a De Bruijn index, `Free <v>` for a free variable.  Neither
/// payload takes parentheses — a De Bruijn index is never negative, and
/// `Show LVar` is hand-written, so it ignores the precedence the derived
/// instance passes it.
impl ShowLit for Lit<Name, BVar<LVar>> {
    fn show_into(&self, out: &mut String) {
        match self {
            Lit::Var(BVar::Bound(i)) => {
                out.push_str("Bound ");
                let _ = write!(out, "{}", i);
            }
            Lit::Var(BVar::Free(v)) => {
                out.push_str("Free ");
                pp_lvar(v, out);
            }
            Lit::Con(n) => pp_name(n, out),
        }
    }
}

// ---------------------------------------------------------------------
// Display impls — `format!("{}", &term)` just works.
// ---------------------------------------------------------------------

impl fmt::Display for Term<Lit<Name, LVar>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&pretty_lnterm(self))
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
    use crate::term::{f_app_ac, f_app_c, f_app_no_eq, lit, show_term};

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

    /// The four builtin AC operators render as HS `ppTerms <op> 1 "(" ")"`
    /// (Term/Term.hs:304-309).  This gives one pair of parentheses around the
    /// complete application.  The operator appears between the operands only.
    /// There are no spaces, and no separator at the start or at the end.  The
    /// arguments come out in AC-sorted order (`a` before `b`), whatever order
    /// the caller passes them in.
    #[test]
    fn pretty_builtin_ac_ops_render_infix() {
        use crate::function_symbols::AcSym;
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        for (op, expected) in [
            (AcSym::Mult, "(a*b)"),
            (AcSym::Xor, "(a\u{2295}b)"),
            (AcSym::Union, "(a++b)"),
            (AcSym::NatPlus, "(a%+b)"),
        ] {
            let t = f_app_ac(op, vec![b.clone(), a.clone()]);
            assert_eq!(pretty_lnterm(&t), expected, "{op:?}");
        }
        // With three operands the separator appears twice, and never at the
        // edges.
        let c = var("c", LSort::Msg);
        let t = f_app_ac(AcSym::Mult, vec![c, b, a]);
        assert_eq!(pretty_lnterm(&t), "(a*b*c)");
    }

    #[test]
    fn pretty_exp_caret() {
        let g = var("g", LSort::Msg);
        let x = var("x", LSort::Msg);
        let t = f_app_no_eq(exp_sym(), vec![g, x]);
        assert_eq!(pretty_lnterm(&t), "g^x");
    }

    #[test]
    fn pretty_user_ac_parenthesizes_exponent_arguments() {
        let g = var("g", LSort::Msg);
        let x = var("x", LSort::Msg);
        let rest = var("rest", LSort::Msg);
        let exponent = f_app_no_eq(exp_sym(), vec![g, x]);
        let t = f_app_ac(user_ac(b"add"), vec![rest, exponent]);
        assert_eq!(pretty_lnterm(&t), "(rest add (g^x))");
    }

    /// `diff(a, b)` keeps its prefix spelling, with a space after the comma.
    /// See the module doc above, and HS `prettyTerm`'s own `s == diffSym`
    /// case.  The guard on the dedicated arm compares the complete `NoEqSym`,
    /// so a public `diff/2` is a different symbol.  That symbol falls through
    /// to the generic `NoEq` arm, which spells a 2-ary application the same
    /// way.  Both assertions therefore check the one spelling.  They do not
    /// check a difference between the two arms.
    #[test]
    fn pretty_diff_renders_prefix_with_spaced_args() {
        let x = var("x", LSort::Msg);
        let y = var("y", LSort::Msg);
        let t = f_app_no_eq(diff_sym(), vec![x.clone(), y.clone()]);
        assert_eq!(pretty_lnterm(&t), "diff(x, y)");
        let public_diff = NoEqSym::new(
            b"diff".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        assert_ne!(public_diff, diff_sym());
        let generic = f_app_no_eq(public_diff, vec![x, y]);
        assert_eq!(pretty_lnterm(&generic), "diff(x, y)");
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
        // HS `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term/Term.hs:304):
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

    /// The separator cache is shared by every thread: a symbol first rendered
    /// on one thread yields the identical `&'static str` — same pointer, same
    /// bytes — on all the others.
    ///
    /// Bytes from the oracle on a theory declaring `f/2 [AC]`, `op/2 [AC]`,
    /// `opq/2 [AC]` and a rule emitting `f(~a,~b)`, `op(~a,~b)`, `opq(~a,~b)`;
    /// it renders them `(~a f ~b)`, `(~a op ~b)`, `(~a opq ~b)` (HS
    /// `ppTerms (" " ++ BC.unpack f ++ " ") 1 "(" ")" ts`, Term/Term.hs:305).
    #[test]
    fn ac_fct_separator_shared_across_threads() {
        use crate::function_symbols::{AcFctSym, AcSym, NdcState};
        let syms: Vec<AcSym> = [&b"f"[..], b"op", b"opq"]
            .iter()
            .map(|n| {
                AcSym::AcFct(AcFctSym::new(
                    n.to_vec(),
                    Privacy::Public,
                    Constructability::Constructor,
                    NdcState::NotNdc,
                ))
            })
            .collect();
        let a = var("a", LSort::Fresh);
        let b = var("b", LSort::Fresh);
        let render = |syms: &[AcSym]| -> Vec<(String, usize)> {
            syms.iter()
                .map(|o| {
                    let t = f_app_ac(*o, vec![a.clone(), b.clone()]);
                    (pretty_lnterm(&t), ac_op_symbol(*o).as_ptr() as usize)
                })
                .collect()
        };
        let expected = ["(~a f ~b)", "(~a op ~b)", "(~a opq ~b)"];

        let first = render(&syms);
        let rendered: Vec<&str> = first.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(rendered, expected);

        // Warm on this thread, then read from four others at once.
        let others: Vec<Vec<(String, usize)>> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..4)
                .map(|_| {
                    let syms = syms.clone();
                    s.spawn(move || render(&syms))
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        for other in &others {
            assert_eq!(other, &first);
        }
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

    /// One sigil per `NameTag`, from HS `instance Show Name`
    /// (LTerm.hs:235-240).  Four of the tags print a quoted form with their
    /// own prefix character, and the prefix of `Pub` is empty.  `Abbrev`
    /// prints the bare id with no sigil and no quotes.
    #[test]
    fn display_for_name() {
        for (tag, expected) in [
            (NameTag::Fresh, "~'kAB'"),
            (NameTag::Pub, "'kAB'"),
            (NameTag::Node, "#'kAB'"),
            (NameTag::Nat, "%'kAB'"),
            (NameTag::Abbrev, "kAB"),
        ] {
            assert_eq!(format!("{}", Name::new(tag, "kAB")), expected, "{tag:?}");
        }
    }

    /// `Display for LSort` carries the spelling of HS `sortSuffix` for every
    /// sort.  It does not carry the constructor names of the derived
    /// `Show LSort`.
    #[test]
    fn lsort_display_matches_sort_suffix() {
        for s in [
            LSort::Pub,
            LSort::Fresh,
            LSort::Msg,
            LSort::Node,
            LSort::Nat,
        ] {
            assert_eq!(s.to_string(), crate::lterm::sort_suffix(s));
        }
    }

    #[test]
    fn pretty_empty_pub_name_var() {
        // Anonymous var prints just the index.
        let v = LVar::new("", LSort::Msg, 7);
        let t: Term<Lit<Name, LVar>> = lit(Lit::Var(v));
        assert_eq!(pretty_lnterm(&t), "7");
    }

    // =====================================================================
    // The `ShowLit` impls, through `show_term`.
    // =====================================================================

    /// The `BLTerm` literal type: `Lit Name (BVar LVar)`.
    type BLit = Lit<Name, BVar<LVar>>;

    fn bound(i: u64) -> Term<BLit> {
        lit(Lit::Var(BVar::Bound(i)))
    }

    /// `show (Bound i)` is the derived `Show (BVar v)` (LTerm.hs:476-478):
    /// the constructor name, a space, the index, no parentheses.  The whole
    /// offender spelling of a wellformedness report is built from this arm —
    /// the string here is the one pinned in
    /// `scripts/divergence_fixtures/expected/formula_terms_offenders.wf.hs.txt`.
    #[test]
    fn show_writes_a_bound_variable_as_the_derived_constructor() {
        assert_eq!(show_term(&bound(1)), "Bound 1");
        let aaa = NoEqSym::new(
            b"aaa".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        let offender: Term<BLit> = f_app_ac(
            AcSym::Mult,
            vec![
                f_app_c(CSym::EMap, vec![bound(1), bound(2)]),
                f_app_no_eq(aaa, vec![bound(2), bound(1)]),
            ],
        );
        assert_eq!(
            show_term(&offender),
            "Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))"
        );
    }

    /// `show (Free v)` is the same derived instance; `Show LVar` is
    /// hand-written (LTerm.hs:550-557), so its sort prefix follows the
    /// constructor name with no parentheses around it.
    #[test]
    fn show_writes_a_free_variable_as_the_derived_constructor() {
        let x: Term<BLit> = lit(Lit::Var(BVar::Free(LVar::new("x", LSort::Fresh, 0))));
        assert_eq!(show_term(&x), "Free ~x");
        let y: Term<BLit> = lit(Lit::Var(BVar::Free(LVar::new("y", LSort::Node, 4))));
        assert_eq!(show_term(&y), "Free #y.4");
        // At `Lit Name LVar` there is no `BVar` wrapper, so the same variable
        // shows as the bare `Show LVar`.
        let z: Term<Lit<Name, LVar>> = var("z", LSort::Msg);
        assert_eq!(show_term(&z), "z");
    }

    /// `show Name` (LTerm.hs:235-240) quotes the name id and prefixes the
    /// tag's sigil; the abbreviation tag carries neither.
    #[test]
    fn show_writes_a_name_with_its_tag_sigil() {
        for (tag, expected) in [
            (NameTag::Pub, "'n'"),
            (NameTag::Fresh, "~'n'"),
            (NameTag::Node, "#'n'"),
            (NameTag::Nat, "%'n'"),
            (NameTag::Abbrev, "n"),
        ] {
            let c: Term<Lit<Name, LVar>> = lit(Lit::Con(Name::new(tag, "n")));
            assert_eq!(show_term(&c), expected);
            let b: Term<BLit> = lit(Lit::Con(Name::new(tag, "n")));
            assert_eq!(show_term(&b), expected);
        }
    }

    // =====================================================================
    // `pretty_term` / `pretty_nterm`, the Doc printer.
    // =====================================================================

    /// The Doc of `t` laid out on one line: no width is ever exceeded, so no
    /// `fcat`/`fsep` ever breaks.
    fn flat(t: &Term<Lit<Name, LVar>>) -> String {
        pretty_nterm(t).render_with(FLAT_WIDTH, FLAT_WIDTH)
    }

    /// A user-declared AC symbol, whose separator is its name in spaces.
    fn user_ac(name: &[u8]) -> AcSym {
        use crate::function_symbols::{AcFctSym, NdcState};
        AcSym::AcFct(AcFctSym::new(
            name.to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        ))
    }

    fn user_fun(name: &[u8], arity: usize) -> NoEqSym {
        NoEqSym::new(
            name.to_vec(),
            arity,
            Privacy::Public,
            Constructability::Constructor,
        )
    }

    /// One term of every arm of the battery above, each with the spelling the
    /// battery pins for it.
    fn shape_rows() -> Vec<(Term<Lit<Name, LVar>>, &'static str)> {
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let c = var("c", LSort::Msg);
        let mut rows = vec![
            (var("x", LSort::Msg), "x"),
            (var_idx("k", LSort::Fresh, 3), "~k.3"),
            (var("pk", LSort::Pub), "$pk"),
            (lit(Lit::Var(LVar::new("", LSort::Msg, 7))), "7"),
            (pub_term("alice"), "'alice'"),
            (fresh_term("kAB"), "~'kAB'"),
            (
                f_app_no_eq(
                    pair_sym(),
                    vec![
                        a.clone(),
                        f_app_no_eq(pair_sym(), vec![b.clone(), c.clone()]),
                    ],
                ),
                "<a, b, c>",
            ),
            (
                f_app_no_eq(
                    pair_sym(),
                    vec![
                        f_app_no_eq(pair_sym(), vec![a.clone(), b.clone()]),
                        c.clone(),
                    ],
                ),
                "<<a, b>, c>",
            ),
            (f_app_ac(AcSym::Mult, vec![b.clone(), a.clone()]), "(a*b)"),
            (
                f_app_ac(AcSym::Xor, vec![b.clone(), a.clone()]),
                "(a\u{2295}b)",
            ),
            (f_app_ac(AcSym::Union, vec![b.clone(), a.clone()]), "(a++b)"),
            (
                f_app_ac(AcSym::NatPlus, vec![b.clone(), a.clone()]),
                "(a%+b)",
            ),
            (
                f_app_ac(AcSym::Mult, vec![c.clone(), b.clone(), a.clone()]),
                "(a*b*c)",
            ),
            (
                f_app_ac(user_ac(b"f"), vec![a.clone(), b.clone()]),
                "(a f b)",
            ),
            (Term::App(FunSym::Ac(user_ac(b"f")), vec![].into()), "f"),
            (
                f_app_no_eq(exp_sym(), vec![var("g", LSort::Msg), var("x", LSort::Msg)]),
                "g^x",
            ),
            (
                f_app_no_eq(diff_sym(), vec![var("x", LSort::Msg), var("y", LSort::Msg)]),
                "diff(x, y)",
            ),
            (
                f_app_no_eq(
                    user_fun(b"diff", 2),
                    vec![var("x", LSort::Msg), var("y", LSort::Msg)],
                ),
                "diff(x, y)",
            ),
            (f_app_no_eq(inv_sym(), vec![var("g", LSort::Msg)]), "inv(g)"),
            (f_app_no_eq(nat_one_sym(), vec![]), "%1"),
            (
                f_app_no_eq(
                    user_fun(b"senc", 2),
                    vec![var("k", LSort::Msg), var("m", LSort::Msg)],
                ),
                "senc(k, m)",
            ),
            (f_app_c(CSym::EMap, vec![a.clone(), b.clone()]), "em(a, b)"),
            (
                crate::term::f_app_list(vec![a.clone(), b.clone()]),
                "LIST(a, b)",
            ),
        ];
        for (tag, expected) in [
            (NameTag::Fresh, "~'kAB'"),
            (NameTag::Pub, "'kAB'"),
            (NameTag::Node, "#'kAB'"),
            (NameTag::Nat, "%'kAB'"),
            (NameTag::Abbrev, "kAB"),
        ] {
            rows.push((lit(Lit::Con(Name::new(tag, "kAB"))), expected));
        }
        rows
    }

    /// Every shape of the battery, laid out on one line, spells what the
    /// `String` printer spells.
    #[test]
    fn pretty_nterm_flat_equals_pretty_lnterm() {
        for (t, expected) in shape_rows() {
            assert_eq!(flat(&t), expected, "{t:?}");
            assert_eq!(flat(&t), pretty_lnterm(&t), "{t:?}");
        }
    }

    #[test]
    fn malformed_pairs_use_function_notation() {
        // Raw/smart constructors can supply an arity other than two. Such a
        // node must not be flattened into a list containing itself forever.
        for (arity, expected) in [(0, "pair"), (1, "pair(x)"), (3, "pair(x, x, x)")] {
            let term = f_app_no_eq(pair_sym(), vec![var("x", LSort::Msg); arity]);
            assert_eq!(pretty_nterm(&term).render(), expected);
            assert_eq!(pretty_lnterm(&term), expected);
        }
    }

    #[test]
    fn flat_writer_matches_document_for_composed_shapes() {
        let mut rows: Vec<_> = shape_rows().into_iter().map(|(term, _)| term).collect();
        rows.push(lit(Lit::Con(Name::new(NameTag::Abbrev, ""))));
        rows.push(f_app_no_eq(user_fun(b"", 0), vec![]));
        rows.push(pub_term("λ\n\t<&>"));
        for left in &rows {
            for right in &rows {
                for symbol in [
                    FunSym::NoEq(user_fun(b"f", 2)),
                    FunSym::NoEq(pair_sym()),
                    FunSym::NoEq(exp_sym()),
                    FunSym::NoEq(diff_sym()),
                    FunSym::Ac(user_ac(b"add")),
                    FunSym::List,
                ] {
                    let term = crate::term::f_app(symbol, vec![left.clone(), right.clone()]);
                    assert_eq!(pretty_lnterm(&term), flat(&term), "{term:?}");
                }
            }
        }
    }

    #[test]
    fn flat_writer_uses_bounded_stack_for_deep_terms() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = var("x", LSort::Msg);
                for _ in 0..100_000 {
                    term = f_app_no_eq(user_fun(b"f", 1), vec![term]);
                }
                assert_eq!(
                    pretty_lnterm(&term),
                    "f(".repeat(100_000) + "x" + &")".repeat(100_000)
                );
                drop(term);

                let mut term = var("x", LSort::Msg);
                for _ in 0..100_000 {
                    term = f_app_no_eq(pair_sym(), vec![var("x", LSort::Msg), term]);
                }
                assert_eq!(
                    pretty_lnterm(&term),
                    "<".to_owned() + &"x, ".repeat(100_000) + "x>"
                );
                drop(term);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// The literal printer of `prettyNTerm` is `show`, so a name carries the
    /// sigil of its tag (LTerm.hs:235-240) — `#` for a node name, which the
    /// Maude skolems of a node-sorted variable carry (`maude_proc`).
    #[test]
    fn pretty_nterm_prints_a_node_name_with_its_sigil() {
        let n: Term<Lit<Name, LVar>> = lit(Lit::Con(Name::new(NameTag::Node, "n")));
        assert_eq!(flat(&n), "#'n'");
        let inside = f_app_no_eq(user_fun(b"senc", 2), vec![n, var("m", LSort::Msg)]);
        assert_eq!(flat(&inside), "senc(#'n', m)");
    }

    /// HS's `diff` arm is a chain of `<>` (Term/Term.hs:311), so the comma
    /// between the operands is not a break point however far the application
    /// overruns the line.  The generic `ppFun` arm (Term/Term.hs:326-327)
    /// joins its arguments with `fsep`, so the same operands break there.
    #[test]
    fn pretty_nterm_diff_never_breaks() {
        let wide = |c: char| -> Term<Lit<Name, LVar>> { pub_term(c.to_string().repeat(60)) };
        let d = f_app_no_eq(diff_sym(), vec![wide('a'), wide('b')]);
        let rendered = pretty_nterm(&d).render_with(110, 73);
        assert!(rendered.len() > 110, "{rendered}");
        assert!(!rendered.contains('\n'), "{rendered}");
        assert_eq!(rendered, flat(&d));
        let f = f_app_no_eq(user_fun(b"senc", 2), vec![wide('a'), wide('b')]);
        assert!(pretty_nterm(&f).render_with(110, 73).contains('\n'));
    }

    /// HS `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)`
    /// (Term/Term.hs:304): the bare name, with neither parentheses nor the
    /// spaced separator the infix arm uses.
    #[test]
    fn pretty_nterm_nullary_user_ac_is_the_bare_name() {
        let f = user_ac(b"f");
        let nullary: Term<Lit<Name, LVar>> = Term::App(FunSym::Ac(f), vec![].into());
        assert_eq!(flat(&nullary), "f");
        assert_eq!(
            flat(&f_app_ac(
                f,
                vec![var("a", LSort::Msg), var("b", LSort::Msg)]
            )),
            "(a f b)"
        );
    }

    /// A pair term keeps its raw `<`/`>` under an enclosing HTML render: the
    /// escaping belongs to the `Doc` a caller wraps the string in, HS's
    /// `Document (HtmlDoc d)` instance (Html.hs:102-104).
    #[test]
    fn pretty_lnterm_stays_plain_under_an_html_render() {
        let p = f_app_no_eq(pair_sym(), vec![var("a", LSort::Msg), var("b", LSort::Msg)]);
        let _html = HtmlDocGuard::enable();
        assert_eq!(pretty_lnterm(&p), "<a, b>");
        assert_eq!(
            Doc::text(pretty_lnterm(&p)).render_with(FLAT_WIDTH, FLAT_WIDTH),
            "&lt;a, b&gt;"
        );
    }

    /// HS `split` walks the RIGHT spine only (Term/Term.hs:323-324), so a
    /// left-nested pair keeps its inner brackets.
    #[test]
    fn pretty_nterm_left_nested_pair_is_not_flattened() {
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let c = var("c", LSort::Msg);
        let left = f_app_no_eq(
            pair_sym(),
            vec![
                f_app_no_eq(pair_sym(), vec![a.clone(), b.clone()]),
                c.clone(),
            ],
        );
        assert_eq!(flat(&left), "<<a, b>, c>");
        let right = f_app_no_eq(pair_sym(), vec![a, f_app_no_eq(pair_sym(), vec![b, c])]);
        assert_eq!(flat(&right), "<a, b, c>");
    }

    /// `prettyProtoAtom` writes its timepoint positions with `text (show v)`
    /// (Atom.hs:216,223,224), not with `ppT`.  The two agree on a literal —
    /// `show (LIT l) = show l` (Term/Term/Raw.hs:227-232, see line 230) —
    /// which is the shape every constructed timepoint has; on an application
    /// they part, `show` keeping the prefix form the pretty-printer rewrites.
    #[test]
    fn show_term_is_the_prefix_form() {
        for (t, _) in shape_rows() {
            if matches!(t, Term::Lit(_)) {
                assert_eq!(show_term(&t), flat(&t), "{t:?}");
            }
        }
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let p = f_app_no_eq(pair_sym(), vec![a.clone(), b.clone()]);
        assert_eq!(show_term(&p), "pair(a,b)");
        assert_eq!(flat(&p), "<a, b>");
        let e = f_app_no_eq(exp_sym(), vec![a.clone(), b.clone()]);
        assert_eq!(show_term(&e), "exp(a,b)");
        assert_eq!(flat(&e), "a^b");
        let m = f_app_ac(AcSym::Mult, vec![a, b]);
        assert_eq!(show_term(&m), "Mult(a,b)");
        assert_eq!(flat(&m), "(a*b)");
    }
}
