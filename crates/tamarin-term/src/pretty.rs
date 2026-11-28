// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `prettyLNTerm`/`prettyTerm` from
//! `lib/term/src/Term/Term.hs` and the `Show LVar` /
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
//! - [`pretty_lnterm`], that `Doc` laid out on a single line as a `String`;
//! - `impl Display for LNTerm` (technically on `Term<Lit<Name, LVar>>`).

use std::borrow::Cow;
use std::fmt;
use std::fmt::Write as _;

use tamarin_utils::pretty_hpj::{fcat, fsep, parens, punctuate, Doc, HtmlDocGuard, FLAT_WIDTH};

use crate::function_symbols::{AcSym, CSym, FunSym, EMAP_SYM_STRING};
use crate::lterm::{sort_prefix, sort_suffix, BVar, LNTerm, LSort, LVar, Name, NameTag};
use crate::term::{ShowLit, Term};
use crate::vterm::{Lit, VTerm};

/// Mirror of Haskell `instance Show LVar` (LTerm.hs).
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

/// Mirror of Haskell `instance Show Name` (LTerm.hs).
pub fn pp_name(n: &Name, out: &mut String) {
    match n.tag {
        NameTag::Fresh => out.push('~'),
        NameTag::Pub => {}
        NameTag::Node => out.push('#'),
        NameTag::Nat => out.push('%'),
        // `show (Name AbbrevName n) = show n` (LTerm.hs) — the bare name
        // id, with neither a sigil nor the quotes the other four tags carry.
        NameTag::Abbrev => {
            out.push_str(n.id.0);
            return;
        }
        // A skolem exists only inside one guarded match and HS never prints
        // its `SkConst`; show the frozen variable.
        NameTag::Skolem { idx, .. } => {
            let _ = write!(out, "sk({}.{})", n.id.0, idx);
            return;
        }
    }
    out.push('\'');
    out.push_str(n.id.0);
    out.push('\'');
}

pub fn ac_op_symbol(op: AcSym) -> Cow<'static, str> {
    // Haskell `prettyTerm`'s AC arms (Term/Term.hs).
    //   Mult => "*"; Xor => "⊕"; Union => "++"; NatPlus => "%+"
    // We use the unicode char for Xor since the rest of the UI
    // already passes UTF-8 around and the JS frontend renders it.
    match op {
        AcSym::Mult => Cow::Borrowed("*"),
        AcSym::Xor => Cow::Borrowed("\u{2295}"),
        AcSym::Union => Cow::Borrowed("++"),
        AcSym::NatPlus => Cow::Borrowed("%+"),
        // `ppTerms (" " ++ BC.unpack f ++ " ") 1 "(" ")" ts` (Term/Term.hs)
        // surrounds the user-defined AC symbol's name by spaces, so the
        // spaces are part of the separator (unlike the builtin ops).
        AcSym::AcFct(sym) => Cow::Owned(format!(" {} ", String::from_utf8_lossy(sym.name))),
    }
}

// ---------------------------------------------------------------------
// `prettyTerm` — the Doc printer (Term/Term.hs).
// ---------------------------------------------------------------------

/// HS `prettyTerm :: (Document d, Show l) => (l -> d) -> Term l -> d`
/// (Term/Term.hs), parameterised over the printer of the term's
/// literals.  The arms keep HS's order: a nullary user-`[AC]` symbol before
/// the generic AC arm, and `exp`/`diff`/`%1`/`pair` before the generic `NoEq`
/// arms.  Each of those four guards compares the whole `NoEqSym`, as HS's
/// `s == expSym` does, so a symbol that only shares the name renders through
/// the generic arm.
pub fn pretty_term<L>(pp_lit: &dyn Fn(&L) -> Doc, t: &Term<L>) -> Doc {
    match t {
        Term::Lit(l) => pp_lit(l),
        // `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term/Term.hs).
        Term::App(FunSym::Ac(AcSym::AcFct(sym)), ts) if ts.is_empty() => {
            Doc::text(String::from_utf8_lossy(sym.name))
        }
        Term::App(FunSym::Ac(o @ AcSym::AcFct(_)), ts) => {
            pp_user_ac_terms(pp_lit, &ac_op_symbol(*o), ts)
        }
        Term::App(FunSym::Ac(o), ts) => {
            pp_terms(pp_lit, &ac_op_symbol(*o), 1, "(", ")", ts.iter().collect())
        }
        Term::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && sym.is_exp_sym() => {
            pretty_term(pp_lit, &ts[0])
                .beside(Doc::text("^"))
                .beside(pretty_term(pp_lit, &ts[1]))
        }
        // All `<>` (Term/Term.hs), so a `diff` application never breaks at
        // its comma the way the generic `ppFun` arm does.
        Term::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && sym.is_diff_sym() => Doc::text("diff")
            .beside(Doc::text("("))
            .beside(pretty_term(pp_lit, &ts[0]))
            .beside(Doc::text(", "))
            .beside(pretty_term(pp_lit, &ts[1]))
            .beside(Doc::text(")")),
        t if crate::term::is_nat_one(t) => Doc::text("%1"),
        // The arm carries no arity guard (Term/Term.hs); the arity check
        // lives in `split`, which stops on anything else.
        Term::App(FunSym::NoEq(sym), _) if sym.is_pair_sym() => {
            let mut flat: Vec<&Term<L>> = Vec::new();
            split_pair(t, &mut flat);
            pp_terms(pp_lit, ", ", 1, "<", ">", flat)
        }
        Term::App(FunSym::NoEq(sym), ts) if ts.is_empty() => {
            Doc::text(String::from_utf8_lossy(sym.name))
        }
        Term::App(FunSym::NoEq(sym), ts) => pp_fun(pp_lit, &String::from_utf8_lossy(sym.name), ts),
        Term::App(FunSym::C(CSym::EMap), ts) => {
            pp_fun(pp_lit, &String::from_utf8_lossy(EMAP_SYM_STRING), ts)
        }
        Term::App(FunSym::List, ts) => pp_fun(pp_lit, "LIST", ts),
    }
}

/// HS `prettyNTerm = prettyTerm (text . show)` (LTerm.hs) over
/// `NTerm v = VTerm Name v` (LTerm.hs), whose literal printer is
/// `Show (Lit c v)` (VTerm.hs).
pub fn pretty_nterm<V: fmt::Display>(t: &VTerm<Name, V>) -> Doc {
    pretty_term(&|l: &Lit<Name, V>| Doc::text(l.to_string()), t)
}

/// HS `prettyLNTerm = prettyNTerm` (LTerm.hs) laid out on a single
/// line: [`FLAT_WIDTH`] leaves no `fcat` or `fsep` of the `Doc` a reason to
/// break.  HS has no `String` twin — the flat form is what the port's map and
/// sort keys, its abbreviation table and its debug messages compare.
///
/// The `Doc` is built and rendered in plain mode whatever the caller's
/// rendering context: the callers that put the string back into a `Doc::text`
/// take their escaping from that `Doc`, which is where HS's
/// `Document (HtmlDoc d)` instance applies it (Html.hs), and the rest
/// write to a plain-text channel.
pub fn pretty_lnterm(t: &LNTerm) -> String {
    let _plain = HtmlDocGuard::disable();
    pretty_nterm(t).render_with(FLAT_WIDTH, FLAT_WIDTH)
}

/// HS `ppTerms sepa n lead finish ts` (Term/Term.hs):
/// `fcat . (text lead :) . (++[text finish]) . map (nest n)
///       . punctuate (text sepa) . map ppTerm`.
fn pp_terms<L>(
    pp_lit: &dyn Fn(&L) -> Doc,
    sepa: &str,
    n: isize,
    lead: &str,
    finish: &str,
    ts: Vec<&Term<L>>,
) -> Doc {
    let docs: Vec<Doc> = ts.into_iter().map(|t| pretty_term(pp_lit, t)).collect();
    pp_docs(sepa, n, lead, finish, docs)
}

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

/// User-defined AC operators bind more tightly than exponentiation in the
/// parser. Parenthesise a direct exponent argument so pretty-printed terms
/// reparse with the same tree (tamarin-prover#919).
fn pp_user_ac_terms<L>(pp_lit: &dyn Fn(&L) -> Doc, separator: &str, terms: &[Term<L>]) -> Doc {
    let docs = terms
        .iter()
        .map(|term| {
            let doc = pretty_term(pp_lit, term);
            if matches!(term, Term::App(FunSym::NoEq(sym), args) if sym.is_exp_sym() && args.len() == 2)
            {
                parens(doc)
            } else {
                doc
            }
        })
        .collect();
    pp_docs(separator, 1, "(", ")", docs)
}

/// HS `ppFun f ts` (Term/Term.hs):
/// `text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"`.
fn pp_fun<L>(pp_lit: &dyn Fn(&L) -> Doc, f: &str, ts: &[Term<L>]) -> Doc {
    let docs: Vec<Doc> = ts.iter().map(|t| pretty_term(pp_lit, t)).collect();
    Doc::text(format!("{}(", f))
        .beside(fsep(punctuate(Doc::char(','), docs)))
        .beside(Doc::text(")"))
}

/// HS `split` (Term/Term.hs): `split (viewTerm2 -> FPair t1 t2) = t1 :
/// split t2; split t = [t]`.  `FPair` (Term/Term/Raw.hs) needs exactly two
/// arguments and full `NoEqSym` equality with `pairSym`, and only the RIGHT
/// child continues the spine, so `pair(pair(a, b), c)` keeps its left child
/// nested.
fn split_pair<'a, L>(t: &'a Term<L>, out: &mut Vec<&'a Term<L>>) {
    match t {
        Term::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && sym.is_pair_sym() => {
            out.push(&ts[0]);
            split_pair(&ts[1], out);
        }
        _ => out.push(t),
    }
}

// ---------------------------------------------------------------------
// `ShowLit` impls — the literal half of HS `Show (Term a)`.
// ---------------------------------------------------------------------

/// HS `instance (Show v, Show c) => Show (Lit c v)` (Term/VTerm.hs) at
/// `Lit Name LVar`, the literal of an `LNTerm`.  Both sides are the same
/// `Show` instances the pretty-printer reuses for its leaves: `Show LVar`
/// (LTerm.hs) and `Show Name` (LTerm.hs).
impl ShowLit for Lit<Name, LVar> {
    fn show_into(&self, out: &mut String) {
        match self {
            Lit::Var(v) => pp_lvar(v, out),
            Lit::Con(n) => pp_name(n, out),
        }
    }
}

/// The same instance at `Lit Name (BVar LVar)`, the literal of a `BLTerm`.
/// Its variable side is the derived `Show (BVar v)` (LTerm.hs):
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
// (`Term.LTerm`), NOT the derived `Show LSort`
// (which yields constructor names like `LSortMsg`).
impl fmt::Display for LSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(sort_suffix(*self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{
        diff_sym, exp_sym, inv_sym, nat_one_sym, pair_sym, AcFctSym, Constructability, NdcState,
        NoEqSym, Privacy,
    };
    use crate::lterm::{fresh_term, pub_term, NameTag};
    use crate::term::{f_app_ac, f_app_c, f_app_list, f_app_no_eq, lit, show_term};

    type T = Term<Lit<Name, LVar>>;

    fn var(name: &str, sort: LSort) -> T {
        var_idx(name, sort, 0)
    }
    fn var_idx(name: &str, sort: LSort, idx: u64) -> T {
        lit(Lit::Var(LVar::new(name, sort, idx)))
    }

    /// The Doc of `t` laid out on one line: no width is ever exceeded, so no
    /// `fcat`/`fsep` ever breaks.
    fn flat(t: &T) -> String {
        pretty_nterm(t).render_with(FLAT_WIDTH, FLAT_WIDTH)
    }

    fn ac_fct(name: &[u8], privacy: Privacy, ctor: Constructability, ndc: NdcState) -> AcSym {
        AcSym::AcFct(AcFctSym::new(name.to_vec(), privacy, ctor, ndc))
    }

    /// A user-declared AC symbol, whose separator is its name in spaces.
    fn user_ac(name: &[u8]) -> AcSym {
        ac_fct(
            name,
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        )
    }

    fn user_fun(name: &[u8], arity: usize) -> NoEqSym {
        NoEqSym::new(
            name.to_vec(),
            arity,
            Privacy::Public,
            Constructability::Constructor,
        )
    }

    fn app(name: &str, args: Vec<T>) -> T {
        f_app_no_eq(user_fun(name.as_bytes(), args.len()), args)
    }

    /// `<a, b, c>`: HS `fAppPair` is arity 2 (Term/Term.hs), so a tuple is
    /// the right-nested chain `prettyTerm`'s `split` walks back out.
    fn tuple(items: Vec<T>) -> T {
        let mut it = items.into_iter().rev();
        let mut acc = it.next().expect("a tuple has at least one element");
        for prev in it {
            acc = f_app_no_eq(pair_sym(), vec![prev, acc]);
        }
        acc
    }

    /// The term-show table: one term per arm of `prettyTerm` (Term/Term.hs)
    /// and of the derived-style `Show (Term a)` (Term/Term/Raw.hs), with the
    /// flat pretty spelling and the `show` spelling of each.
    ///
    /// - pretty: builtin AC ops are infix with no spaces and AC-sorted
    ///   operands; a user AC symbol's separator is its name in spaces,
    ///   whatever its attributes; a user-AC operand that is an `exp` is
    ///   parenthesised (tamarin-prover#919); `split` unrolls only the RIGHT
    ///   pair spine; `diff` keeps its prefix spelling whether or not the
    ///   symbol is the builtin one.
    /// - show: `intercalate ","` with no space; an AC head shows its derived
    ///   `ACSym` constructor name and a user AC symbol its own name; the
    ///   nullary arms write the bare name; `pair`/`exp` stay prefix.
    fn shape_rows() -> Vec<(T, &'static str, &'static str)> {
        let a = var("a", LSort::Msg);
        let b = var("b", LSort::Msg);
        let c = var("c", LSort::Msg);
        let (x, y) = (var("x", LSort::Msg), var("y", LSort::Msg));
        let (fa, fb) = (var("a", LSort::Fresh), var("b", LSort::Fresh));
        let g_x = f_app_no_eq(exp_sym(), vec![var("g", LSort::Msg), x.clone()]);
        let h_xy = app("h", vec![x.clone(), y.clone()]);
        let pair_ab = f_app_no_eq(pair_sym(), vec![pub_term("a"), pub_term("b")]);
        let mut rows = vec![
            (x.clone(), "x", "x"),
            (var_idx("k", LSort::Fresh, 3), "~k.3", "~k.3"),
            (var("pk", LSort::Pub), "$pk", "$pk"),
            (var_idx("foo", LSort::Pub, 4), "$foo.4", "$foo.4"),
            (var_idx("", LSort::Msg, 7), "7", "7"),
            (pub_term("alice"), "'alice'", "'alice'"),
            (fresh_term("kAB"), "~'kAB'", "~'kAB'"),
            (
                tuple(vec![a.clone(), b.clone(), c.clone()]),
                "<a, b, c>",
                "pair(a,pair(b,c))",
            ),
            (
                f_app_no_eq(
                    pair_sym(),
                    vec![tuple(vec![a.clone(), b.clone()]), c.clone()],
                ),
                "<<a, b>, c>",
                "pair(pair(a,b),c)",
            ),
            (pair_ab.clone(), "<'a', 'b'>", "pair('a','b')"),
            (
                f_app_ac(AcSym::Mult, vec![b.clone(), a.clone()]),
                "(a*b)",
                "Mult(a,b)",
            ),
            (
                f_app_ac(AcSym::Xor, vec![b.clone(), a.clone()]),
                "(a\u{2295}b)",
                "Xor(a,b)",
            ),
            (
                f_app_ac(AcSym::Union, vec![b.clone(), a.clone()]),
                "(a++b)",
                "Union(a,b)",
            ),
            (
                f_app_ac(AcSym::NatPlus, vec![b.clone(), a.clone()]),
                "(a%+b)",
                "NatPlus(a,b)",
            ),
            (
                f_app_ac(AcSym::Mult, vec![c.clone(), b.clone(), a.clone()]),
                "(a*b*c)",
                "Mult(a,b,c)",
            ),
            (
                f_app_ac(user_ac(b"f"), vec![a.clone(), b.clone()]),
                "(a f b)",
                "f(a,b)",
            ),
            (
                f_app_ac(user_ac(b"f"), vec![fa.clone(), fb.clone()]),
                "(~a f ~b)",
                "f(~a,~b)",
            ),
            (
                f_app_ac(user_ac(b"op"), vec![fa.clone(), fb.clone()]),
                "(~a op ~b)",
                "op(~a,~b)",
            ),
            (
                f_app_ac(user_ac(b"opq"), vec![fa.clone(), fb.clone()]),
                "(~a opq ~b)",
                "opq(~a,~b)",
            ),
            (
                f_app_ac(
                    ac_fct(
                        b"op",
                        Privacy::Private,
                        Constructability::Destructor,
                        NdcState::IsNdc,
                    ),
                    vec![fa, fb],
                ),
                "(~a op ~b)",
                "op(~a,~b)",
            ),
            (
                f_app_ac(user_ac(b"xorr"), vec![x.clone(), y.clone()]),
                "(x xorr y)",
                "xorr(x,y)",
            ),
            (
                f_app_ac(user_ac(b"add"), vec![var("rest", LSort::Msg), g_x.clone()]),
                "(rest add (g^x))",
                "add(rest,exp(g,x))",
            ),
            // `f_app_ac` rejects an empty argument list (HS `fAppAC` errors
            // likewise), so the nullary arm is reachable only by direct
            // construction.
            (
                Term::App(FunSym::Ac(user_ac(b"f")), vec![].into()),
                "f",
                "f",
            ),
            (g_x, "g^x", "exp(g,x)"),
            (
                f_app_no_eq(exp_sym(), vec![pair_ab, pub_term("c")]),
                "<'a', 'b'>^'c'",
                "exp(pair('a','b'),'c')",
            ),
            (
                f_app_no_eq(diff_sym(), vec![x.clone(), y.clone()]),
                "diff(x, y)",
                "diff(x,y)",
            ),
            (
                app("diff", vec![x.clone(), y.clone()]),
                "diff(x, y)",
                "diff(x,y)",
            ),
            (
                f_app_no_eq(inv_sym(), vec![var("g", LSort::Msg)]),
                "inv(g)",
                "inv(g)",
            ),
            (f_app_no_eq(nat_one_sym(), vec![]), "%1", "tone"),
            (app("g", vec![]), "g", "g"),
            (
                app("senc", vec![var("k", LSort::Msg), var("m", LSort::Msg)]),
                "senc(k, m)",
                "senc(k,m)",
            ),
            (
                app(
                    "senc",
                    vec![
                        lit(Lit::Con(Name::new(NameTag::Node, "n"))),
                        var("m", LSort::Msg),
                    ],
                ),
                "senc(#'n', m)",
                "senc(#'n',m)",
            ),
            (h_xy.clone(), "h(x, y)", "h(x,y)"),
            (
                app("k", vec![h_xy, x.clone(), f_app_list(vec![y.clone()])]),
                "k(h(x, y), x, LIST(y))",
                "k(h(x,y),x,LIST(y))",
            ),
            (
                f_app_c(CSym::EMap, vec![b.clone(), a.clone()]),
                "em(a, b)",
                "em(a,b)",
            ),
            (f_app_list(vec![a, b]), "LIST(a, b)", "LIST(a,b)"),
        ];
        for (tag, expected) in [
            (NameTag::Fresh, "~'kAB'"),
            (NameTag::Pub, "'kAB'"),
            (NameTag::Node, "#'kAB'"),
            (NameTag::Nat, "%'kAB'"),
            (NameTag::Abbrev, "kAB"),
        ] {
            rows.push((lit(Lit::Con(Name::new(tag, "kAB"))), expected, expected));
        }
        rows
    }

    /// Every shape row spells its pretty form flat, through the `String`
    /// printer and through `Display`, and its `show` form through
    /// `show_term`.  A literal row's pretty form is also the `Display` of the
    /// `LVar` or `Name` it holds.
    #[test]
    fn every_shape_row_prints_its_pretty_and_show_forms() {
        for (t, pretty, show) in shape_rows() {
            assert_eq!(flat(&t), pretty, "{t:?}");
            assert_eq!(pretty_lnterm(&t), pretty, "{t:?}");
            assert_eq!(t.to_string(), pretty, "{t:?}");
            assert_eq!(show_term(&t), show, "{t:?}");
            match &t {
                Term::Lit(Lit::Var(v)) => assert_eq!(v.to_string(), pretty),
                Term::Lit(Lit::Con(n)) => assert_eq!(n.to_string(), pretty),
                Term::App(..) => {}
            }
        }
    }

    /// The `BLTerm` literal type: `Lit Name (BVar LVar)`.
    type BLit = Lit<Name, BVar<LVar>>;

    fn bound(i: u64) -> Term<BLit> {
        lit(Lit::Var(BVar::Bound(i)))
    }

    /// The `show` form at `Lit Name (BVar LVar)`.  The variable side is the
    /// derived `Show (BVar v)` (LTerm.hs): constructor name, a space, then
    /// the payload with no parentheses (`Show LVar` is hand-written and
    /// ignores the precedence).  The `Mult(…)` row is the offender spelling
    /// a wellformedness report prints.
    #[test]
    fn every_bound_literal_row_shows_the_derived_constructor() {
        let free = |name: &str, sort, idx| lit(Lit::Var(BVar::Free(LVar::new(name, sort, idx))));
        let mut rows: Vec<(Term<BLit>, &str)> = vec![
            (bound(1), "Bound 1"),
            (free("x", LSort::Fresh, 0), "Free ~x"),
            (free("y", LSort::Node, 4), "Free #y.4"),
            (
                f_app_ac(
                    AcSym::Mult,
                    vec![
                        f_app_c(CSym::EMap, vec![bound(1), bound(2)]),
                        f_app_no_eq(user_fun(b"aaa", 2), vec![bound(2), bound(1)]),
                    ],
                ),
                "Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))",
            ),
        ];
        for (tag, expected) in [
            (NameTag::Pub, "'n'"),
            (NameTag::Fresh, "~'n'"),
            (NameTag::Node, "#'n'"),
            (NameTag::Nat, "%'n'"),
            (NameTag::Abbrev, "n"),
        ] {
            rows.push((lit(Lit::Con(Name::new(tag, "n"))), expected));
        }
        for (t, expected) in rows {
            assert_eq!(show_term(&t), expected, "{t:?}");
        }
    }

    /// Where a wrapped term is laid out: page width and ribbon, the column
    /// the term starts at (`get1`'s `sl`), the `nest` it sits under, and
    /// whether it renders as HTML (HS `HtmlDoc` measures escaped widths).
    struct Layout {
        width: usize,
        ribbon: usize,
        start_col: usize,
        nest: isize,
        html: bool,
    }

    fn render_wrapped(t: &T, at: &Layout) -> String {
        let _mode = if at.html {
            HtmlDocGuard::enable()
        } else {
            HtmlDocGuard::disable()
        };
        let doc = pretty_nterm(t).nest(at.nest);
        if at.start_col == 0 {
            doc.render_with(at.width, at.ribbon)
        } else {
            doc.render_at(at.width, at.ribbon, at.start_col)
        }
    }

    /// The UM_three_pass `/main/cases/raw/0/0` substitution term, as the web
    /// pane's `prettyEqStore` lays it out under `equations:`/`subst:`.
    fn um3_subst_term() -> T {
        let pube = |s: &str| pub_term(s);
        let a5 = || var_idx("A", LSort::Pub, 5);
        let b5 = || var_idx("B", LSort::Pub, 5);
        let y5 = || var_idx("Y", LSort::Msg, 5);
        let exp = |l: T, r: T| f_app_no_eq(exp_sym(), vec![l, r]);
        let g_ex5 = || exp(pube("g"), var_idx("ex", LSort::Fresh, 5));
        let g_eax5 = || {
            exp(
                pube("g"),
                f_app_ac(
                    AcSym::Mult,
                    vec![
                        var_idx("ea", LSort::Fresh, 5),
                        var_idx("x", LSort::Fresh, 5),
                    ],
                ),
            )
        };
        let h_arg = || {
            tuple(vec![
                var_idx("z", LSort::Msg, 5),
                g_eax5(),
                a5(),
                b5(),
                g_ex5(),
                y5(),
            ])
        };
        let mac = |snd: T| {
            app(
                "MAC",
                vec![app("first", vec![app("h", vec![h_arg()])]), snd],
            )
        };
        let t1 = tuple(vec![pube("1"), g_ex5()]);
        let t2 = tuple(vec![
            pube("2"),
            y5(),
            mac(tuple(vec![pube("I"), a5(), b5(), g_ex5(), y5()])),
        ]);
        let t3 = tuple(vec![
            pube("3"),
            mac(tuple(vec![pube("R"), b5(), a5(), y5(), g_ex5()])),
        ]);
        tuple(vec![
            pube("UM3"),
            a5(),
            b5(),
            f_app_ac(AcSym::Union, vec![t1, t2, t3]),
        ])
    }

    /// The UM3 term's bytes from HS's cached web response for
    /// `examples/ake/dh/UM_three_pass.spthy` (`&nbsp;` read as a space,
    /// `<br/>` as a newline), without the ` <~ {t.1}` tail of its line.
    const UM3_WEB: &str = "    &lt;&#39;UM3&#39;, $A.5, $B.5, \n     \
(&lt;&#39;1&#39;, &#39;g&#39;^~ex.5&gt;++\n      \
&lt;&#39;2&#39;, Y.5, \n       \
MAC(first(h(&lt;z.5, &#39;g&#39;^(~ea.5*~x.5), $A.5, $B.5, \n                    \
&#39;g&#39;^~ex.5, Y.5&gt;)),\n           \
&lt;&#39;I&#39;, $A.5, $B.5, &#39;g&#39;^~ex.5, Y.5&gt;)\n      \
&gt;++\n      \
&lt;&#39;3&#39;, \n       \
MAC(first(h(&lt;z.5, &#39;g&#39;^(~ea.5*~x.5), $A.5, $B.5, \n                    \
&#39;g&#39;^~ex.5, Y.5&gt;)),\n           \
&lt;&#39;R&#39;, $B.5, $A.5, Y.5, &#39;g&#39;^~ex.5&gt;)\n      \
&gt;\n     \
)\n    \
&gt;";

    /// Wrapped layouts: the break points of `fcat`/`fsep`/`punctuate` inside
    /// `prettyTerm`.  The `exp` row keeps `'g'^(` on its first line (`^` is
    /// `<>`, never a break) while the AC exponent's operands break at `nest
    /// 1`.
    #[test]
    fn every_wrap_row_breaks_where_hs_breaks() {
        let lf = |n: &str| var(n, LSort::Fresh);
        let hmac = app(
            "hmac",
            vec![
                f_app_no_eq(
                    exp_sym(),
                    vec![
                        pub_term("g"),
                        f_app_ac(
                            AcSym::Mult,
                            vec![lf("longFreshPrivKeyOne"), lf("longFreshPrivKeyTwo")],
                        ),
                    ],
                ),
                lf("longSaltArgumentName"),
            ],
        );
        let cli = |start_col| Layout {
            width: 110,
            ribbon: 73,
            start_col,
            nest: 0,
            html: false,
        };
        let web = Layout {
            width: 100,
            ribbon: 67,
            start_col: 0,
            nest: 4,
            html: true,
        };
        let rows: Vec<(T, Layout, &str)> = vec![
            (
                hmac,
                cli(30),
                "hmac('g'^(~longFreshPrivKeyOne*\n                                        ~longFreshPrivKeyTwo),\n                                   ~longSaltArgumentName)",
            ),
            (um3_subst_term(), web, UM3_WEB),
        ];
        for (t, at, expected) in rows {
            assert_eq!(render_wrapped(&t, &at), expected, "{t:?}");
        }
    }

    /// HS's `diff` arm is a chain of `<>` (Term/Term.hs), so the comma
    /// between the operands is not a break point however far the application
    /// overruns the line.  The generic `ppFun` arm (Term/Term.hs)
    /// joins its arguments with `fsep`, so the same operands break there.
    #[test]
    fn pretty_nterm_diff_never_breaks() {
        let wide = |c: char| -> T { pub_term(c.to_string().repeat(60)) };
        let d = f_app_no_eq(diff_sym(), vec![wide('a'), wide('b')]);
        let rendered = pretty_nterm(&d).render_with(110, 73);
        assert!(rendered.len() > 110, "{rendered}");
        assert!(!rendered.contains('\n'), "{rendered}");
        assert_eq!(rendered, flat(&d));
        let f = f_app_no_eq(user_fun(b"senc", 2), vec![wide('a'), wide('b')]);
        assert!(pretty_nterm(&f).render_with(110, 73).contains('\n'));
    }

    /// A pair term keeps its raw `<`/`>` under an enclosing HTML render: the
    /// escaping belongs to the `Doc` a caller wraps the string in, HS's
    /// `Document (HtmlDoc d)` instance (Html.hs).
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
}
