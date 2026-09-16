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
    match t {
        Term::Lit(literal) => pp_lit(literal),
        Term::App(symbol, args) if args.is_empty() => pretty_app(symbol, args, Vec::new()),
        Term::App(symbol, args) => tamarin_utils::stack::ensure_sufficient_stack(|| {
            let docs =
                if matches!(symbol, FunSym::NoEq(sym) if *sym == pair_sym()) && args.len() == 2 {
                    let mut flat = Vec::new();
                    split_pair(t, &mut flat);
                    flat.into_iter().map(|t| pretty_term(pp_lit, t)).collect()
                } else {
                    args.iter().map(|t| pretty_term(pp_lit, t)).collect()
                };
            pretty_app(symbol, args, docs)
        }),
    }
}

// Build a parent only after its children have been printed in source order.
// Child Docs retain exactly the same nesting, separators and alternatives as
// the recursive printer.
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
#[path = "pretty_tests.rs"]
mod tests;
