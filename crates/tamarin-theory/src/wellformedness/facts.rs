// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HS `factReports` (Wellformedness.hs:579-583): the wellformedness checks
//! over a theory's facts — reserved names, reserved `KU`/`KD`/`K` usage,
//! `Fr` arguments, the special `In`/`Out`/`Fr` tags, and the arity /
//! multiplicity / capitalization clash groups.
//!
//! The checks read the parser AST, so this module carries its own port of
//! HS's term printer and term ordering: `prettyTerm` / `prettyLNFact`
//! (Term/Term.hs:298-327, Theory/Model/Fact.hs:567-582) as [`WfDoc`]
//! skeletons, `fAppAC`'s flatten-and-sort (Term/Term/Raw.hs:118-131), the
//! derived `Ord (Term a)` those two need, and the De Bruijn `show` form HS
//! prints a lemma-formula fact with.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_parser::ast;
use tamarin_parser::ast::*;
use tamarin_term::lterm::{sort_prefix, LSort};

use super::{
    numbered_index_width, render_var, rule_facts, theory_lemmas, theory_rules, underline_topic,
    WfError, WfReport,
};
use crate::pretty_hpj::{self as hpj, Doc};

/// The layout skeleton of one `prettyTerm` / `prettyLNFact` rendering
/// (Term/Term.hs:298-327, Theory/Model/Fact.hs:567-572).
///
/// HS builds these as HughesPJ `Doc`s, so a fact that overruns the render
/// ribbon breaks at its OWN `sep`/`fsep`/`fcat` points — `prettyLNFact` drops
/// its closing `)` onto the next line and refills the argument list at a
/// deeper indent.  [`cell_doc`] maps each variant onto the HughesPJ
/// combinator HS used, for the entries whose body the layout engine lays out;
/// [`WfDoc::write_flat`] takes every break point horizontally, which is the
/// body the single-line entries carry.
enum WfDoc {
    /// HS `text s` — a leaf with no internal break point.
    Text(String),
    /// HS `<>` — juxtaposition; the parts keep their own break points.
    Beside(Vec<WfDoc>),
    /// HS `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm
    /// ts)) <> text ")"` (Term/Term.hs:326-327).
    Fun(String, Vec<WfDoc>),
    /// HS `ppTerms sepa 1 lead finish ts` (Term/Term.hs:319-321) — the `fcat`
    /// of `text lead`, the `nest 1`'d and `sepa`-punctuated operands, and
    /// `text finish`: pairs (`<`, `, `, `>`) and AC chains (`(`, the operator,
    /// `)`).
    Terms {
        lead: String,
        sep: String,
        finish: String,
        items: Vec<WfDoc>,
    },
    /// HS `ppFact n ts = nestShort' (n ++ "(") ")" (fsep (punctuate comma (map
    /// ppTerm ts)))` (Theory/Model/Fact.hs:572), i.e. `sep [text lead $$ nest
    /// (length lead + 1) body, text ")"]` (Text/PrettyPrint/Class.hs:218-223).
    Fact { lead: String, args: Vec<WfDoc> },
}

impl WfDoc {
    /// Render with every break point taken horizontally — the layout HughesPJ
    /// picks while the doc fits the ribbon.
    fn write_flat(&self, out: &mut String) {
        match self {
            WfDoc::Text(s) => out.push_str(s),
            WfDoc::Beside(parts) => {
                for p in parts {
                    p.write_flat(out);
                }
            }
            WfDoc::Fun(name, args) => {
                out.push_str(name);
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        // `punctuate comma` + the space `fsep` joins with.
                        out.push_str(", ");
                    }
                    a.write_flat(out);
                }
                out.push(')');
            }
            WfDoc::Terms {
                lead,
                sep,
                finish,
                items,
            } => {
                out.push_str(lead);
                for (i, it) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(sep);
                    }
                    it.write_flat(out);
                }
                out.push_str(finish);
            }
            WfDoc::Fact { lead, args } => {
                // `nestShort'`'s two spaces: `$$` overlaps the nested body onto
                // the lead's line one column past it, and the enclosing `sep`
                // joins that with the closing `)`.  An argument-less fact keeps
                // only the `sep` space (`text lead $$ nest n emptyDoc` is just
                // the lead), so it renders `A( )`.
                out.push_str(lead);
                if !args.is_empty() {
                    out.push(' ');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        a.write_flat(out);
                    }
                }
                out.push_str(" )");
            }
        }
    }
}

/// One [`WfDoc`] skeleton as the HughesPJ `Doc` HS's `prettyTerm` /
/// `prettyFact` build for it (Term/Term.hs:298-327,
/// Theory/Model/Fact.hs:567-574).
fn cell_doc(d: &WfDoc) -> Doc {
    match d {
        WfDoc::Text(s) => Doc::text(s),
        // HS `<>` chain = `hcat` (HughesPJ.hs:496).
        WfDoc::Beside(parts) => hpj::hcat(parts.iter().map(cell_doc).collect()),
        WfDoc::Fun(name, args) => {
            let refs: Vec<&WfDoc> = args.iter().collect();
            hpj::fun_app_doc(name, &refs, cell_doc)
        }
        WfDoc::Terms {
            lead,
            sep,
            finish,
            items,
        } => {
            let refs: Vec<&WfDoc> = items.iter().collect();
            hpj::fcat_bracketed(lead, sep, finish, &refs, cell_doc)
        }
        WfDoc::Fact { lead, args } => {
            let body = hpj::fsep(hpj::punctuate(
                Doc::char(','),
                args.iter().map(cell_doc).collect(),
            ));
            hpj::nest_short_doc(lead, ")", body)
        }
    }
}

/// HS `prettyLNFact = prettyFact prettyNTerm` (Theory/Model/Fact.hs:581-582):
/// the fact's
/// `ppFact` skeleton `[!]Name(` … `)` over `prettyTerm`'d arguments.
fn wf_fact_doc(fa: &Fact, ac: &AcSyms) -> WfDoc {
    let mut lead = String::new();
    if fa.persistent {
        lead.push('!');
    }
    lead.push_str(&fa.name);
    lead.push('(');
    WfDoc::Fact {
        lead,
        args: fa.args.iter().map(|a| wf_term_doc(a, ac)).collect(),
    }
}

/// [`wf_fact_doc`] laid out flat: `!Name( arg, arg, ... )` for persistent,
/// `Name( arg, arg, ... )` for linear.
fn pp_wf_fact(fa: &Fact, ac: &AcSyms) -> String {
    let mut out = String::new();
    wf_fact_doc(fa, ac).write_flat(&mut out);
    out
}

/// HS `prettyTerm`'s `split` (Term/Term.hs:323-324): the operand list a
/// pair-headed term renders between `<` and `>`.  `split` recurses on the
/// RIGHT child while that child is itself `pairSym`-headed
/// (`FPair`, Term/Term/Raw.hs:194), so `pair(a, pair(b, c))` yields
/// `[a, b, c]` while the left-nested `pair(pair(a, b), c)` yields
/// `[pair(a, b), c]`.  A non-pair `t` yields `[t]`.
///
/// Both parser spellings feed the same spine: `Pair` holds `<a, b, c>` flat
/// where HS nests it `pair(a, pair(b, c))`, so every element but the last is
/// an operand and the last continues the spine; `App("pair", [a, b])` is the
/// source form `pair(a, b)`, which HS parses to that same `pairSym` FAPP
/// (`naryOpApp`, Theory/Text/Parser/Term.hs:88-105, see line 104).
fn pair_split<'a>(t: &'a Term, out: &mut Vec<&'a Term>) {
    match t {
        Term::Pair(items) => {
            if let Some((last, init)) = items.split_last() {
                out.extend(init.iter());
                pair_split(last, out);
            }
        }
        Term::App(name, args) if name == "pair" && args.len() == 2 => {
            out.push(&args[0]);
            pair_split(&args[1], out);
        }
        _ => out.push(t),
    }
}

/// HS `prettyTerm`'s pair arm `ppTerms ", " 1 "<" ">" (split t)`
/// (Term/Term.hs:313), for a `t` that is `pairSym`-headed.
fn wf_pair_doc(t: &Term, ac: &AcSyms) -> WfDoc {
    let mut items: Vec<&Term> = Vec::new();
    pair_split(t, &mut items);
    WfDoc::Terms {
        lead: "<".to_string(),
        sep: ", ".to_string(),
        finish: ">".to_string(),
        items: items.iter().map(|it| wf_term_doc(it, ac)).collect(),
    }
}

/// HS `prettyTerm`'s AC arms (Term/Term.hs:304-309): the flattened, sorted
/// operand list of an `FAPP (AC …)` rendered inside `(` `)` with `sepa`
/// between operands (`ppTerms sepa 1 "(" ")" ts`).
fn wf_ac_chain_doc(t: &Term, sepa: &str, ac: &AcSyms) -> WfDoc {
    let head = wf_funsym_key(t, ac);
    let mut flat: Vec<&Term> = Vec::new();
    flatten_ac(head, t, &mut flat, ac);
    flat.sort_by(|a, b| cmp_wf_term(a, b, ac));
    WfDoc::Terms {
        lead: "(".to_string(),
        sep: sepa.to_string(),
        finish: ")".to_string(),
        items: flat.iter().map(|a| wf_term_doc(a, ac)).collect(),
    }
}

/// HS `prettyTerm` (Term/Term.hs:298-327) over a parser-AST term: the
/// skeleton whose break points HS's `fsep`/`fcat` own.
fn wf_term_doc(t: &Term, ac: &AcSyms) -> WfDoc {
    use Term::*;
    let t = ac_collapse(t, ac);
    // HS `prettyTerm` matches `FApp (AC (ACfct (f, _))) ts` BEFORE any
    // builtin-symbol arm (Term/Term.hs:304-305), and the separator is the
    // symbol name with a space on each side — the same string
    // `ast::BinOp::AcFct`'s `separator` builds for the infix spelling.
    if let Some(name) = ac_app_name(t, ac) {
        return wf_ac_chain_doc(t, &format!(" {name} "), ac);
    }
    // The leaves HS renders with a single `text` — no break point inside.
    let leaf = |s: String| WfDoc::Text(s);
    match t {
        Var(v) => {
            let mut s = String::new();
            s.push_str(sort_prefix(v.sort));
            s.push_str(&v.name);
            if v.idx > 0 {
                s.push('.');
                s.push_str(&v.idx.to_string());
            }
            leaf(s)
        }
        PubLit(s) => leaf(format!("'{s}'")),
        FreshLit(s) => leaf(format!("~'{s}'")),
        NatLit(s) => leaf(format!("%'{s}'")),
        Number(n) => leaf(n.to_string()),
        // HS `prettyTerm` renders the nullary builtins via `text (BC.unpack f)`
        // except natOneSym ("%1"): oneSym → "one", dhNeutralSym → "DH_neutral"
        // (FunctionSymbols.hs:255,257,267; Term/Term.hs:312,314).
        NumberOne => leaf("one".to_string()),
        NatOne => leaf("%1".to_string()),
        DhNeutral => leaf("DH_neutral".to_string()),
        Pair(_) => wf_pair_doc(t, ac),
        App(name, args) if name == "pair" && args.len() == 2 => wf_pair_doc(t, ac),
        // `em` is HS's sole `C` symbol (`CSym = EMap`,
        // FunctionSymbols.hs:142-143), and `fAppC nacsym as = FAPP (C nacsym)
        // (sort as)` (Term/Term/Raw.hs:132-134, see line 134) sorts its
        // arguments at construction, so `prettyTerm` never sees the written
        // order.
        App(name, args) if name == "em" && args.len() == 2 => {
            let mut sorted: Vec<&Term> = args.iter().collect();
            sorted.sort_by(|a, b| cmp_wf_term(a, b, ac));
            WfDoc::Fun(
                name.clone(),
                sorted.iter().map(|a| wf_term_doc(a, ac)).collect(),
            )
        }
        // HS checks `s == natOneSym` BEFORE the generic nullary arm:
        // `FApp (NoEq s) [] | s == natOneSym -> text "%1"` (Term/Term.hs:312).
        App(name, args) if args.is_empty() && name == "tone" => leaf("%1".to_string()),
        // HS `FApp (NoEq (f,_)) [] -> text f` (Term/Term.hs:314) — a nullary
        // symbol
        // has no `ppFun` parentheses at all.
        App(name, args) if args.is_empty() => leaf(name.clone()),
        App(name, args) => WfDoc::Fun(
            name.clone(),
            args.iter().map(|a| wf_term_doc(a, ac)).collect(),
        ),
        // HS canonicalises `aenc{m}pk` as `aenc(m, pk)`.
        AlgApp(name, l, r) => {
            WfDoc::Fun(name.clone(), vec![wf_term_doc(l, ac), wf_term_doc(r, ac)])
        }
        // HS `prettyTerm`'s diff arm (Term/Term.hs:311) joins with `<>`, not the
        // breakable `fsep` `ppFun` uses.
        Diff(l, r) => WfDoc::Beside(vec![
            WfDoc::Text("diff(".to_string()),
            wf_term_doc(l, ac),
            WfDoc::Text(", ".to_string()),
            wf_term_doc(r, ac),
            WfDoc::Text(")".to_string()),
        ]),
        BinOp(op, l, r) => {
            let sym = op.separator();
            // HS builds AC operators (Mult/Union/Xor/NatPlus and the
            // user-declared `[AC]` symbols) via `fAppAC`, which flattens the
            // chain, sorts the operands (Ord LTerm), and renders them
            // parenthesised by `prettyTerm` (e.g. `(%x%+%1%+%1)`).
            // Exp is NOT AC: rendered binary with `<>`, no surrounding parens.
            if is_ac_binop(op) {
                wf_ac_chain_doc(t, &sym, ac)
            } else {
                WfDoc::Beside(vec![
                    wf_term_doc(l, ac),
                    WfDoc::Text(sym.into_owned()),
                    wf_term_doc(r, ac),
                ])
            }
        }
        PatMatch(inner) => {
            WfDoc::Beside(vec![WfDoc::Text("=".to_string()), wf_term_doc(inner, ac)])
        }
    }
}

/// The names whose PREFIX application denotes a user-declared `[AC]` symbol.
///
/// HS carries this information in the signature: `functions: add/2 [AC]`
/// registers an `ACfctUser` symbol
/// (Theory/Text/Parser/Signature.hs:219-222, see line 221), and `lookupArity`
/// resolves a prefix application by a list lookup over
/// `S.toList (userDefinedFunSyms maudeSig)` in which every `NoEqUser` sorts
/// before every `ACfctUser` (Theory/Text/Parser/Term.hs:62-72,
/// Term/Term/FunctionSymbols.hs:146-147).  A name that is ALSO a `NoEq`
/// symbol of the full signature therefore resolves to the `NoEq` symbol and
/// is NOT in this set; only the remaining `[AC]` names build
/// `FAPP (AC (ACfct …))` from the prefix spelling.  (The INFIX spelling is
/// always the AC symbol — HS `acterm`, Theory/Text/Parser/Term.hs:165-172 —
/// which the AST
/// records as [`BinOp::AcFct`], classified by shape, not via this set.)
/// The parser AST has no signature, so the wellformedness printers
/// reconstruct the set from the theory's own `functions:` and `builtins:`
/// declarations — the same declarations HS reads.
type AcSyms = BTreeSet<String>;

/// The `[AC]`-attributed function symbols declared by `thy` (HS
/// `stACFunSyms . sig`, Theory/Text/Parser/Term.hs:165-174), minus the names
/// that are also `NoEq` symbols of the full signature — see [`AcSyms`].  The
/// `NoEq` side is the non-`[AC]` `functions:` declarations, each enabled
/// builtin's contribution ([`tamarin_parser::parser::builtin_noeq_sym_names`]), and
/// the always-present pair signature (`minimalMaudeSig` is `pairFunSig` —
/// `pair`/`fst`/`snd` — Term/Maude/Signature.hs:224-226).
fn user_ac_fun_names(thy: &Theory) -> AcSyms {
    let mut ac = AcSyms::new();
    let mut noeq: BTreeSet<&str> = ["pair", "fst", "snd"].into_iter().collect();
    for it in &thy.items {
        match it {
            TheoryItem::Functions(decls) => {
                for d in decls {
                    if d.ac {
                        ac.insert(d.name.clone());
                    } else {
                        noeq.insert(d.name.as_str());
                    }
                }
            }
            TheoryItem::Builtins(names) => {
                for n in names {
                    noeq.extend(tamarin_parser::parser::builtin_noeq_sym_names(n));
                }
            }
            _ => {}
        }
    }
    ac.retain(|n| !noeq.contains(n.as_str()));
    ac
}

/// The symbol name when `t` is an application of a user-declared `[AC]`
/// symbol, i.e. HS's `FAPP (AC (ACfct …)) ts`.
///
/// HS `naryOpApp` (Theory/Text/Parser/Term.hs:88-105, see line 105) builds
/// `fAppAC (ACfct …) ts` for an `IsAC` symbol, and its arity check is guarded
/// on `NotAC` (line 98), so `add(p, q, r)` is a legal ternary AC application.
/// One-argument applications are excluded because [`ac_collapse`] has already
/// replaced them by their argument.
fn ac_app_name<'a>(t: &'a Term, ac: &AcSyms) -> Option<&'a str> {
    match t {
        Term::App(n, args) if args.len() >= 2 && ac.contains(n.as_str()) => Some(n.as_str()),
        _ => None,
    }
}

/// HS `fAppAC _ [a] = a` (Term/Term/Raw.hs:118-129, see line 121): a
/// one-argument AC application IS its argument, so `add(x)` is the term `x`
/// and carries no `add` node at all.
fn ac_collapse<'a>(t: &'a Term, ac: &AcSyms) -> &'a Term {
    let mut t = t;
    while let Term::App(n, args) = t {
        if args.len() == 1 && ac.contains(n.as_str()) {
            t = &args[0];
        } else {
            break;
        }
    }
    t
}

/// The direct operands of an AC-headed term — the `ts` of HS's
/// `FAPP (AC …) ts`, before [`flatten_ac`] merges same-head nesting.
fn ac_operands(t: &Term) -> Vec<&Term> {
    match t {
        Term::BinOp(_, l, r) => vec![l, r],
        Term::App(_, args) => args.iter().collect(),
        _ => Vec::new(),
    }
}

/// Flatten an AC chain headed by the [`wf_funsym_key`] `head` into its operand
/// list, mirroring HS `fAppAC`'s flatten-then-sort (Term/Term/Raw.hs:118-129).
/// Both AC spellings feed the same spine: the builtin operators parse to
/// `BinOp` and a user `[AC]` symbol to `App`, and HS's `fAppAC` hoists the
/// arguments of every same-head child whichever way it was written.
fn flatten_ac<'a>(head: (u8, &str, usize), t: &'a Term, out: &mut Vec<&'a Term>, ac: &AcSyms) {
    let t = ac_collapse(t, ac);
    if wf_funsym_key(t, ac) == head {
        for child in ac_operands(t) {
            flatten_ac(head, child, out, ac);
        }
    } else {
        out.push(t);
    }
}

/// HS `Ord LTerm` for the subset of parser terms we render here.
///
/// HS-faithful class order (Term/Term/Raw.hs:72-74, VTerm.hs:56-57):
/// `LIT _ < FAPP _ _`, and within `LIT`, `Con < Var`, with constant Names
/// ordered by NameTag (Fresh < Pub < Nat, LTerm.hs:218-220).  The nullary
/// builtins `1`/`%1`/`DH-neutral` are `fAppNoEq … []` so they live in the
/// FAPP class.
///
/// Two FAPP terms compare by their `FunSym` first and only then by the
/// argument list, exactly as the derived `Ord (Term a)` does — so the FAPP
/// order is NAME-based, not Rust-variant-based (HS sorts `exp(a,b)` before
/// `pair(a,b)` because `"exp" < "pair"`).  [`wf_funsym_key`] carries that key.
fn cmp_wf_term(a: &Term, b: &Term, ac: &AcSyms) -> std::cmp::Ordering {
    let a = ac_collapse(a, ac);
    let b = ac_collapse(b, ac);
    let (ca, sa) = wf_term_class(a, ac);
    let (cb, sb) = wf_term_class(b, ac);
    if ca != cb {
        return ca.cmp(&cb);
    }
    if ca == 1 {
        // FAPP class: `compare fsym` then `compare ts` (Term/Term/Raw.hs:72-74,
        // see line 74).
        let ka = wf_funsym_key(a, ac);
        let kb = wf_funsym_key(b, ac);
        let key =
            ka.0.cmp(&kb.0)
                .then_with(|| ka.1.cmp(kb.1))
                .then_with(|| ka.2.cmp(&kb.2));
        if key != std::cmp::Ordering::Equal {
            return key;
        }
        // Same FunSym.  An AC head stores its arguments flattened and sorted
        // (HS `fAppAC`, Term/Term/Raw.hs:118-131, see line 122), so its operand
        // list is the sorted multiset rather than the parser's binary tree.
        if ka.0 == 1 {
            let mut fa: Vec<&Term> = Vec::new();
            let mut fb: Vec<&Term> = Vec::new();
            flatten_ac(ka, a, &mut fa, ac);
            flatten_ac(kb, b, &mut fb, ac);
            fa.sort_by(|x, y| cmp_wf_term(x, y, ac));
            fb.sort_by(|x, y| cmp_wf_term(x, y, ac));
            return cmp_term_lists(&fa, &fb, ac);
        }
        return cmp_term_lists(&hs_fapp_args(a, ac), &hs_fapp_args(b, ac), ac);
    }
    if sa != sb {
        return sa.cmp(&sb);
    }
    use Term::*;
    // LIT class only — the FAPP variants have already returned above.
    // `wf_term_class` gives each LIT variant a unique sub-tag, so the early
    // return above leaves `a` and `b` the same variant and each `let … else`
    // binding of `b` is infallible.  A new `Term` variant must still declare
    // itself in `wf_term_class`, `wf_funsym_key` and `hs_fapp_args`, none of
    // which has a wildcard arm.
    match a {
        Var(v1) => {
            let Var(v2) = b else {
                unreachable!("term class matched Var")
            };
            // HS Ord LVar = (idx, sort, name) (LTerm.hs:545-548).
            v1.idx
                .cmp(&v2.idx)
                .then_with(|| v1.sort.cmp(&v2.sort))
                .then_with(|| v1.name.cmp(&v2.name))
        }
        PubLit(s1) => {
            let PubLit(s2) = b else {
                unreachable!("term class matched PubLit")
            };
            s1.cmp(s2)
        }
        FreshLit(s1) => {
            let FreshLit(s2) = b else {
                unreachable!("term class matched FreshLit")
            };
            s1.cmp(s2)
        }
        NatLit(s1) => {
            let NatLit(s2) = b else {
                unreachable!("term class matched NatLit")
            };
            s1.cmp(s2)
        }
        Number(n1) => {
            let Number(n2) = b else {
                unreachable!("term class matched Number")
            };
            n1.cmp(n2)
        }
        _ => std::cmp::Ordering::Equal,
    }
}

/// `(class, sub_tag)` for a parser term: class 0 is HS's `LIT`, class 1 its
/// `FAPP` (`LIT _ < FAPP _ _`, Term/Term/Raw.hs:72-74).  The sub-tag orders
/// the LIT class only — `Con < Var` (VTerm.hs:56-57) and, among constants, by
/// `NameTag` (Fresh < Pub < Nat, LTerm.hs:218-220).  FAPP terms are ordered by
/// [`wf_funsym_key`], so their sub-tag is never consulted.
fn wf_term_class(t: &Term, ac: &AcSyms) -> (u8, u8) {
    use Term::*;
    match ac_collapse(t, ac) {
        FreshLit(_) => (0, 0),
        PubLit(_) => (0, 1),
        NatLit(_) => (0, 2),
        Number(_) => (0, 3),
        Var(_) => (0, 4),
        NumberOne | NatOne | DhNeutral | App(..) | AlgApp(..) | Pair(_) | Diff(..) | BinOp(..)
        | PatMatch(_) => (1, 0),
    }
}

/// HS `FunSym` ordering key `(outer, name, arity)` for a FAPP-class parser
/// term, mirroring [`crate::guarded::funsym_key`] over the same shapes.
///
/// `outer` is the derived `Ord FunSym` constructor order `NoEq(0) < AC(1) <
/// C(2) < List(3)` (FunctionSymbols.hs:150-154).  Within `NoEq`, `Ord NoEqSym`
/// compares `(name, arity)` first (FunctionSymbols.hs:132) — so the parser's
/// dedicated variants key by the HS symbol name they stand for (`pair`, `exp`,
/// `diff`, `one`, `tone`, `DH_neutral`; FunctionSymbols.hs:222,224,226,229,236,247).
/// The builtin AC operators carry no name; their `ACSym` order `Union < Mult <
/// Xor < NatPlus < ACfct` (FunctionSymbols.hs:138-139) rides in the arity slot,
/// and a user `ACfct` carries the name that `Ord ACfctSym` compares first
/// (FunctionSymbols.hs:135).
///
/// A parser `App` is classified by name+arity because the AST carries no
/// signature: `em/2` is HS's sole `C` symbol (`CSym = EMap`,
/// FunctionSymbols.hs:142-143), and `LIST` never has source syntax.  An `App`
/// of a user-declared `[AC]` name is the `ACfct` case, which HS's `Ord`
/// reaches through `AC`, not `NoEq` — it is tested first because HS resolves
/// the name against the signature before any builtin-symbol identity holds.
fn wf_funsym_key<'a>(t: &'a Term, ac: &AcSyms) -> (u8, &'a str, usize) {
    use Term::*;
    let t = ac_collapse(t, ac);
    if let Some(n) = ac_app_name(t, ac) {
        return (1, n, 4);
    }
    match t {
        Pair(_) => (0, "pair", 2),
        BinOp(ast::BinOp::Exp, _, _) => (0, "exp", 2),
        Diff(..) => (0, "diff", 2),
        NumberOne => (0, "one", 0),
        NatOne => (0, "tone", 0),
        DhNeutral => (0, "DH_neutral", 0),
        App(n, args) if n == "em" && args.len() == 2 => (2, "", 0),
        App(n, args) => (0, n.as_str(), args.len()),
        AlgApp(n, _, _) => (0, n.as_str(), 2),
        BinOp(o, _, _) => binop_rank(o),
        // `=t` is SAPIC pattern-match syntax with no HS term counterpart.
        PatMatch(_) => (255, "", 0),
        // LIT-class terms never reach here.
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) => (254, "", 0),
    }
}

/// The positional argument list HS's `Term` carries for a FAPP-class parser
/// term.  `Pair` is the only variant whose parser shape differs from HS's: the
/// AST holds `<a, b, c>` flat, while HS builds the right-nested
/// `pair(a, pair(b, c))` that `prettyTerm`'s `split` walks back out
/// (Term/Term.hs:313,323-324), so the tail is re-nested here.
fn hs_fapp_args(t: &Term, ac: &AcSyms) -> Vec<Term> {
    use Term::*;
    match ac_collapse(t, ac) {
        App(_, x) => x.clone(),
        Pair(x) if x.len() > 2 => vec![x[0].clone(), Pair(x[1..].to_vec())],
        Pair(x) => x.clone(),
        AlgApp(_, l, r) | Diff(l, r) | BinOp(_, l, r) => vec![(**l).clone(), (**r).clone()],
        PatMatch(x) => vec![(**x).clone()],
        NumberOne | NatOne | DhNeutral => Vec::new(),
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) => Vec::new(),
    }
}

/// Which `BinOp`s are AC?  Mult, Union, Xor, NatPlus and the user-declared
/// `[AC]` symbols are the `ACSym` constructors (FunctionSymbols.hs:138-139);
/// `Exp` is the `NoEq` symbol `exp` (FunctionSymbols.hs:251).
fn is_ac_binop(o: &BinOp) -> bool {
    matches!(
        o,
        BinOp::Mult | BinOp::Union | BinOp::Xor | BinOp::NatPlus | BinOp::AcFct(_)
    )
}

/// [`wf_funsym_key`] for a `BinOp` head, split out because
/// `binop_rank_matches_funsym_key_order` pins it against
/// [`crate::guarded::funsym_key`], which is the source of truth for this
/// order over internal terms.
fn binop_rank(o: &BinOp) -> (u8, &str, usize) {
    match o {
        BinOp::Exp => (0, "exp", 2),
        BinOp::Union => (1, "", 0),
        BinOp::Mult => (1, "", 1),
        BinOp::Xor => (1, "", 2),
        BinOp::NatPlus => (1, "", 3),
        BinOp::AcFct(n) => (1, n, 4),
    }
}

/// Lexicographic comparison of two operand lists by [`cmp_wf_term`], with the
/// shorter list ordering first on a common prefix (matching Haskell's derived
/// `Ord [a]`).  Generic over the element type so the positional argument lists
/// (`Term`) and the flattened AC chains (`&Term`) share one body.
fn cmp_term_lists<T: std::borrow::Borrow<Term>>(
    a: &[T],
    b: &[T],
    ac: &AcSyms,
) -> std::cmp::Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        let o = cmp_wf_term(x.borrow(), y.borrow(), ac);
        if o != std::cmp::Ordering::Equal {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

// =============================================================================
// The factReports group
// =============================================================================

/// Port of HS `factReports` (Wellformedness.hs:579-583), in HS's member
/// order.  Its last member, `factLhsOccurNoRhs`, reads the elaborated rules
/// and lives in [`super::rules`].
pub fn fact_reports(_elab: &crate::theory::Theory, parsed: &Theory) -> WfReport {
    let mut report = reserved_report(parsed);
    report.extend(reserved_fact_name_rules(parsed));
    report.extend(fresh_fact_arguments(parsed));
    report.extend(special_facts_usage(parsed));
    report.extend(fact_usage(parsed));
    report
}

// =============================================================================
// Reserved fact names — Tamarin reserves 'fr', 'ku', 'kd', 'out', 'in'
// =============================================================================

/// HS `reservedFactName`'s list (Wellformedness.hs:621-623): a `ProtoFact`
/// whose lowercased tag name is one of these is reserved.
const RESERVED_FACT_NAMES: &[&str] = &["fr", "ku", "kd", "out", "in"];

fn reserved_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for f in rule_facts(r) {
            // HS matches on the `ProtoFact _ name _` pattern, so the special
            // fact tags never reach the name test.
            if !is_proto_fact_name(&f.name) {
                continue;
            }
            let lower = f.name.to_lowercase();
            if RESERVED_FACT_NAMES.contains(&lower.as_str()) {
                out.push(WfError::new(
                    "Reserved names",
                    format!(
                        "Rule '{}' contains a fact with reserved name `{}`",
                        r.name, f.name
                    ),
                ));
            }
        }
    }
    // HS's `theoryFacts` also feeds this check the Action-atom facts of every
    // lemma formula (Wellformedness.hs:602-605); this scan reads rule facts.
    out
}

// =============================================================================
// Reserved KU/KD/K-log usage
// =============================================================================

// HS `reservedFactNameRules'` (Wellformedness.hs:530-541) flags facts whose
// tag is `KUFact`/`KDFact` or which satisfy `isKLogFact` (a `ProtoFact "K"`,
// Theory/Model/Fact.hs:348-350).  `Ded(..)` parses to tag `DedFact`
// (`dedLogFact`, Theory/Model/Fact.hs:305-308), which
// is in NONE of those sets, so it must NOT appear here.
const KLOG_NAMES: &[&str] = &["KU", "KD", "K"];

fn reserved_fact_name_rules(thy: &Theory) -> WfReport {
    // HS builds the report as a plain `Doc`: `prettyWfErrorReport`'s text
    // never passes through the escaping `Document (HtmlDoc d)` instance
    // (Html.hs:102-105), so a pair term inside a fact keeps its raw `<`/`>`
    // on the web routes, which render under an active `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let bad_lhs: Vec<&Fact> = r
            .premises
            .iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        let bad_acts: Vec<&Fact> = r
            .actions
            .iter()
            .filter(|f| {
                KLOG_NAMES.contains(&f.name.as_str())
                    || matches!(f.name.as_str(), "In" | "Out" | "Fr")
            })
            .collect();
        let bad_rhs: Vec<&Fact> = r
            .conclusions
            .iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        for (msg, fs) in [
            ("on left-hand-side", bad_lhs),
            ("on the middle", bad_acts),
            ("on the right-hand-side", bad_rhs),
        ] {
            if !fs.is_empty() {
                // HS `reservedFactNameRules'` (Wellformedness.hs:530-550):
                //   (underlineTopic "Reserved names",
                //      text ("Rule " ++ quote (showRuleCaseName ru))
                //      <-> text ("contains facts with reserved names"++msg) $-$
                //      nest 2 (fsep $ punctuate comma $ map prettyLNFact fas))
                // grouped/nested by `prettyWfErrorReport` (text topic $-$
                // nest 2 body): the rule line gets 2-space indent, the fact
                // line 4-space (2 from ppTopic + 2 from the inner nest 2).
                let facts: Vec<Doc> = fs.iter().map(|f| cell_doc(&wf_fact_doc(f, &ac))).collect();
                // Headerless body (no trailing newline); `format_wf_block`
                // emits the single "Reserved names" header for the group and
                // joins per-rule/side bodies with the 2-space blank separator.
                out.push(WfError::filled(
                    "Reserved names",
                    format!(
                        "Rule `{}' contains facts with reserved names {}:",
                        r.name, msg
                    ),
                    facts,
                ));
            }
        }
    }
    out
}

// =============================================================================
// Special facts misuse
// =============================================================================

fn special_facts_usage(thy: &Theory) -> WfReport {
    // Plain mode for the same reason as the `reserved_fact_name_rules`
    // sibling: the fill's cells are built and laid out here.
    let _plain = hpj::HtmlDocGuard::disable();
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        // HS `specialFactsUsage'` (Wellformedness.hs:553-566) reads
        // `get rPrems`/`get rConcs` on the closed `ProtoRuleE`.
        let lhs_bad: Vec<&Fact> = r.premises.iter().filter(|f| f.name == "Out").collect();
        let rhs_bad: Vec<&Fact> = r
            .conclusions
            .iter()
            .filter(|f| f.name == "Fr" || f.name == "In")
            .collect();
        for (msg, fs) in [
            ("on left-hand-side", lhs_bad),
            ("on right-hand-side", rhs_bad),
        ] {
            if !fs.is_empty() {
                // HS `specialFactsUsage'` (Wellformedness.hs:553-566):
                //   (underlineTopic "Special facts",
                //      text ("rule " ++ quote (showRuleCaseName ru)) <-> text msg
                //      $-$ nest 2 (fsep $ punctuate comma $ map prettyLNFact fas))
                // grouped/nested by `prettyWfErrorReport` exactly like the
                // "Reserved names" sibling.  Note HS uses lowercase `"rule "`
                // here (vs capital `"Rule "` for reserved names).
                let facts: Vec<Doc> = fs.iter().map(|f| cell_doc(&wf_fact_doc(f, &ac))).collect();
                // Headerless body (no trailing newline); `format_wf_block`
                // emits the single "Special facts" header for the group and
                // joins per-rule/side bodies with the 2-space blank separator.
                out.push(WfError::filled(
                    "Special facts",
                    format!("rule `{}' uses disallowed facts {}:", r.name, msg),
                    facts,
                ));
            }
        }
    }
    out
}

// =============================================================================
// Fr facts must use a fresh- or msg-variable
// =============================================================================

fn fresh_fact_arguments(thy: &Theory) -> WfReport {
    let ac = user_ac_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for f in &r.premises {
            if f.name != "Fr" {
                continue;
            }
            if f.args.len() != 1 {
                continue;
            }
            let arg = &f.args[0];
            // The argument must be a single variable of fresh- or
            // message-sort. Anything else (constants, function
            // applications, public/node vars) triggers the warning.
            let ok = match arg {
                Term::Var(v) => matches!(v.sort, LSort::Fresh | LSort::Msg),
                _ => false,
            };
            if !ok {
                // HS `freshFactArguments'` (Wellformedness.hs:569-576, see
                // line 576) renders the WHOLE fact with `prettyLNFact`, so the
                // argument carries `prettyLVar`'s `.idx` suffix and
                // `prettyTerm`'s AC canonicalisation.
                out.push(WfError::new(
                    "Fr facts must only use a fresh- or a msg-variable",
                    format!("rule `{}' fact: {}", r.name, pp_wf_fact(f, &ac)),
                ));
            }
        }
    }
    out
}

// =============================================================================
// Fact arity / multiplicity / capitalization clashes
// =============================================================================

#[derive(Debug, Clone)]
struct FactObservation {
    /// HS `origin`: `Rule \`X'` or `Lemma \`X'` (Wellformedness.hs:579-734, see line 580,605).
    origin: String,
    name: String,
    arity: usize,
    persistent: bool,
    /// Pre-rendered fact body for the detail line: `prettyLNFact` for rule
    /// facts, the Haskell `show` form for lemma-formula facts (HS
    /// `theoryFacts`'s LemmaItem branch uses `text (show fa)`,
    /// Wellformedness.hs:605-607).
    pp: String,
}

fn collect_fact_observations(thy: &Theory) -> Vec<FactObservation> {
    let ac = user_ac_fun_names(thy);
    // HS `theoryFacts` (Wellformedness.hs:597-607): rule facts (E rules) then
    // lemma-formula facts.  (AC-rule facts only differ for non-trivial-variant
    // rules and never introduce a new arity/cap clash, so we omit them.)
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for f in rule_facts(r) {
            // HS `theoryFacts` groups facts by `factTagName` with no builtin
            // filter; a user-written `K(..)` is a `ProtoFact "K"`
            // (`isKLogFact`/`isProtoFact`) whose tag-name is "K", so it MUST be
            // included in the capitalization/arity/multiplicity clash grouping.
            // We exclude only the genuine special tags (Fr/In/Out/KU/KD/Ded/Term)
            // via `is_proto_fact_name`, matching the sibling check.
            if !is_proto_fact_name(&f.name) {
                continue;
            }
            out.push(FactObservation {
                origin: format!("Rule `{}'", r.name),
                name: f.name.clone(),
                arity: f.args.len(),
                persistent: f.persistent,
                pp: pp_wf_fact(f, &ac),
            });
        }
    }
    out.extend(lemma_fact_observations(thy, &ac));
    out
}

/// HS `theoryFacts`'s LemmaItem branch (Wellformedness.hs:602-605):
///   `(,) ("Lemma " ++ quote (get lName l)) $ do
///        fa <- formulaFacts (get lFormula l); return (text (show fa), factInfo fa)`
/// i.e. every Action-atom fact in the lemma formula, rendered as the Haskell
/// `show` of `Fact (VTerm Name (BVar LVar))` — `Fact {factTag = ProtoFact
/// Linear "X" n, factAnnotations = fromList [], factTerms = [Bound i, ...]}`.
fn lemma_fact_observations(thy: &Theory, ac: &AcSyms) -> Vec<FactObservation> {
    let mut out = Vec::new();
    for l in theory_lemmas(thy) {
        let mut facts: Vec<(Fact, Vec<String>)> = Vec::new();
        collect_formula_facts(&l.formula, &mut Vec::new(), ac, &mut facts);
        for (fa, dbterms) in facts {
            // HS show of the Fact: see `show_debruijn_fact`.
            let pp = show_debruijn_fact(&fa, &dbterms);
            out.push(FactObservation {
                origin: format!("Lemma `{}'", l.name),
                name: fa.name.clone(),
                arity: fa.args.len(),
                persistent: fa.persistent,
                pp,
            });
        }
    }
    out
}

/// Walk a formula left-to-right (HS `foldFormula` order), collecting the fact
/// of every `Action` atom together with its argument terms rendered in De
/// Bruijn form (`Bound n` / `Free ...`).  `binders` is the enclosing
/// quantifier stack (outermost first); the innermost binder has index 0.
fn collect_formula_facts<'a>(
    f: &'a Formula,
    binders: &mut Vec<&'a VarSpec>,
    ac: &AcSyms,
    out: &mut Vec<(Fact, Vec<String>)>,
) {
    match f {
        Formula::Atom(Atom::Action(fa, _)) => {
            let terms = fa
                .args
                .iter()
                .map(|t| show_debruijn_term(t, binders, ac))
                .collect();
            out.push((fa.clone(), terms));
        }
        Formula::Atom(_) | Formula::True | Formula::False => {}
        Formula::Not(a) => collect_formula_facts(a, binders, ac, out),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
            collect_formula_facts(a, binders, ac, out);
            collect_formula_facts(b, binders, ac, out);
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            let n = vars.len();
            for v in vars {
                binders.push(v);
            }
            collect_formula_facts(body, binders, ac, out);
            for _ in 0..n {
                binders.pop();
            }
        }
    }
}

/// The De Bruijn index of the innermost binder `v` refers to, or `None` when
/// `v` is free.
///
/// HS binds a use to its binder by full `LVar` equality — name AND sort AND
/// idx (`quantify x = … | v == x = Bound i`,
/// Theory/Model/Formula.hs:347-351;
/// `Eq LVar`, LTerm.hs:541-542).
fn db_index(v: &VarSpec, binders: &[&VarSpec]) -> Option<usize> {
    binders.iter().enumerate().rev().find_map(|(pos, b)| {
        (b.name == v.name && b.sort == v.sort && b.idx == v.idx).then(|| binders.len() - 1 - pos)
    })
}

/// [`wf_term_class`] refined for the De Bruijn form: a variable use is a
/// `BVar`, and `Bound _ < Free _` (LTerm.hs:476-478) splits the single `Var`
/// sub-tag in two.
fn db_term_class(t: &Term, binders: &[&VarSpec], ac: &AcSyms) -> (u8, u8) {
    match ac_collapse(t, ac) {
        Term::Var(v) if db_index(v, binders).is_none() => (0, 5),
        other => wf_term_class(other, ac),
    }
}

/// [`cmp_wf_term`] over terms whose variables have been resolved to De
/// Bruijn form.
///
/// The lemma-formula terms HS sorts are `VTerm Name (BVar LVar)`, not
/// `LNTerm`: `quantify` rewrites a free variable to `Bound i` through
/// `mapLits` (Theory/Model/Formula.hs:288-291,347-351), which rebuilds every
/// node with
/// `fApp` and so re-sorts it, and the outermost binder's pass runs last over
/// the fully-bound term.  So the operand order is the one `Bound _ < Free _`
/// induces, NOT the `LVar` order [`cmp_wf_term`] uses.
fn cmp_db_term(a: &Term, b: &Term, binders: &[&VarSpec], ac: &AcSyms) -> std::cmp::Ordering {
    let a = ac_collapse(a, ac);
    let b = ac_collapse(b, ac);
    let (ca, sa) = db_term_class(a, binders, ac);
    let (cb, sb) = db_term_class(b, binders, ac);
    if ca != cb {
        return ca.cmp(&cb);
    }
    if ca == 1 {
        // FAPP class: `compare fsym` then `compare ts` (Term/Term/Raw.hs:72-74).
        let ka = wf_funsym_key(a, ac);
        let kb = wf_funsym_key(b, ac);
        let key =
            ka.0.cmp(&kb.0)
                .then_with(|| ka.1.cmp(kb.1))
                .then_with(|| ka.2.cmp(&kb.2));
        if key != std::cmp::Ordering::Equal {
            return key;
        }
        let xa = db_fapp_args(a, binders, ac);
        let xb = db_fapp_args(b, binders, ac);
        for (x, y) in xa.iter().zip(xb.iter()) {
            let o = cmp_db_term(x, y, binders, ac);
            if o != std::cmp::Ordering::Equal {
                return o;
            }
        }
        return xa.len().cmp(&xb.len());
    }
    if sa != sb {
        return sa.cmp(&sb);
    }
    if sa == 4 {
        // Both bound: `Bound Integer` compares by index.
        if let (Term::Var(v1), Term::Var(v2)) = (a, b) {
            return db_index(v1, binders).cmp(&db_index(v2, binders));
        }
    }
    // Free variables and the constant literals order exactly as they do
    // outside a formula.
    cmp_wf_term(a, b, ac)
}

/// The argument list HS's `Term` carries for a FAPP-class term of a lemma
/// formula: [`hs_fapp_args`], canonicalised the way the smart constructors
/// do it (Term/Term/Raw.hs:118-134) — an `AC` head flattens its same-head
/// children and sorts, a `C` head (`em`) only sorts.
fn db_fapp_args(t: &Term, binders: &[&VarSpec], ac: &AcSyms) -> Vec<Term> {
    let t = ac_collapse(t, ac);
    let key = wf_funsym_key(t, ac);
    match key.0 {
        1 => {
            let mut flat: Vec<&Term> = Vec::new();
            flatten_ac(key, t, &mut flat, ac);
            let mut args: Vec<Term> = flat.into_iter().cloned().collect();
            args.sort_by(|x, y| cmp_db_term(x, y, binders, ac));
            args
        }
        2 => {
            let mut args = hs_fapp_args(t, ac);
            args.sort_by(|x, y| cmp_db_term(x, y, binders, ac));
            args
        }
        _ => hs_fapp_args(t, ac),
    }
}

/// The head name HS's `Show (Term a)` prints for a FAPP-class parser term
/// (Term/Term/Raw.hs:227-237).  It is [`wf_funsym_key`]'s name everywhere a
/// `FunSym` carries one; the builtin `ACSym`s print their derived
/// constructor name instead, and the sole `CSym` prints `emapSymString`
/// (FunctionSymbols.hs:242).
fn show_debruijn_head<'a>(t: &'a Term, ac: &AcSyms) -> &'a str {
    use ast::BinOp as B;
    match t {
        Term::BinOp(B::Mult, _, _) => "Mult",
        Term::BinOp(B::Union, _, _) => "Union",
        Term::BinOp(B::Xor, _, _) => "Xor",
        Term::BinOp(B::NatPlus, _, _) => "NatPlus",
        Term::App(n, args) if n == "em" && args.len() == 2 => "em",
        _ => wf_funsym_key(t, ac).1,
    }
}

/// HS `show` of a `VTerm Name (BVar LVar)` (Term Show: `Lit l -> show l`,
/// `FApp s as -> s(...)`, Term/Term/Raw.hs:227-237; Lit Show: `Var v -> show v`,
/// `Con n -> show n`, VTerm.hs:98-100; BVar `Bound i`/`Free v` derived).
fn show_debruijn_term(t: &Term, binders: &[&VarSpec], ac: &AcSyms) -> String {
    let t = ac_collapse(t, ac);
    match t {
        Term::Var(v) => match db_index(v, binders) {
            Some(i) => format!("Bound {}", i),
            None => format!("Free {}", render_var(v)),
        },
        Term::PubLit(s) => format!("'{}'", s),
        Term::FreshLit(s) => format!("~'{}'", s),
        Term::NatLit(s) => format!("%'{}'", s),
        Term::Number(n) => n.to_string(),
        // `=t` is SAPIC pattern-match syntax with no HS term counterpart.
        Term::PatMatch(inner) => show_debruijn_term(inner, binders, ac),
        // Every remaining variant is a FAPP: `s`, or `s ++ "(" ++
        // intercalate "," (map show as) ++ ")"`.  `db_fapp_args` supplies the
        // operand list HS's term carries — right-nested for `<a, b, c>`
        // (`tupleterm`'s `chainr1`, Theory/Text/Parser/Term.hs:211-212),
        // flattened and sorted under an AC head, sorted under `em`.
        _ => {
            let head = show_debruijn_head(t, ac);
            let args = db_fapp_args(t, binders, ac);
            if args.is_empty() {
                return head.to_string();
            }
            let args_s: Vec<String> = args
                .iter()
                .map(|a| show_debruijn_term(a, binders, ac))
                .collect();
            format!("{}({})", head, args_s.join(","))
        }
    }
}

/// HS `show (Fact {...})` (derived Show, Theory/Model/Fact.hs:157-163):
/// `Fact {factTag = ProtoFact <Mult> "<name>" <arity>, factAnnotations =
/// fromList [], factTerms = [<terms>]}`.
fn show_debruijn_fact(fa: &Fact, dbterms: &[String]) -> String {
    let mult = if fa.persistent {
        "Persistent"
    } else {
        "Linear"
    };
    format!(
        "Fact {{factTag = ProtoFact {} {:?} {}, factAnnotations = fromList [], factTerms = [{}]}}",
        mult,
        fa.name,
        fa.args.len(),
        dbterms.join(",")
    )
}

fn fact_usage(thy: &Theory) -> WfReport {
    let observations = collect_fact_observations(thy);
    let mut groups: BTreeMap<String, Vec<&FactObservation>> = BTreeMap::new();
    for obs in &observations {
        groups.entry(obs.name.to_lowercase()).or_default().push(obs);
    }
    let mut out = Vec::new();

    // HS emits one block per issue type when ANY clash group exhibits
    // it.  Collect first, then emit.
    let mut cap_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    let mut arity_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    let mut mult_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    for (_, group) in groups.iter().filter(|(_, g)| g.len() >= 2) {
        let cap_set: BTreeSet<&str> = group.iter().map(|o| o.name.as_str()).collect();
        let arity_set: BTreeSet<usize> = group.iter().map(|o| o.arity).collect();
        let mult_set: BTreeSet<bool> = group.iter().map(|o| o.persistent).collect();
        if cap_set.len() > 1 {
            cap_groups.push(group);
        }
        if arity_set.len() > 1 {
            arity_groups.push(group);
        }
        if mult_set.len() > 1 {
            mult_groups.push(group);
        }
    }

    if !cap_groups.is_empty() {
        let msg = "Fact names are case-sensitive, different capitalizations are \
                  considered as different facts, i.e., Fact() is different from FAct(). \n\
                  Check the capitalization of your fact names.";
        out.push(format_fact_clash_block(
            "Fact capitalization issues",
            msg,
            &cap_groups,
            |o| format!("capitalization {:?}", o.name),
        ));
    }
    if !arity_groups.is_empty() {
        let msg = "Same fact is used with different arities, \
                  i.e., Fact('A','B') is different from Fact('A'). \n\
                  Check the arguments of your facts.";
        out.push(format_fact_clash_block(
            "Fact arity issues",
            msg,
            &arity_groups,
            |o| format!("arity {}", o.arity),
        ));
    }
    if !mult_groups.is_empty() {
        let msg = "Same fact is used with different multiplicities, \
                  i.e., !Fact() (Persistent fact) exists along with Fact() (Linear) in your rules. \n\
                  Check the multiplicity (persistence) of your facts.";
        out.push(format_fact_clash_block(
            "Fact multiplicity issues",
            msg,
            &mult_groups,
            |o| {
                format!(
                    "multiplicity (persistence) {}",
                    if o.persistent { "Persistent" } else { "Linear" }
                )
            },
        ));
    }
    out
}

/// Emit one HS-style WfError block: title + underline + intro msg +
/// per-clash numbered detail.  Layout matches the byte output of HS's
/// `formatMultipIssue` / `formatArityIssue` / `formatCapIssue`
/// (Wellformedness.hs:660-674).
fn format_fact_clash_block<F>(
    title: &str,
    intro: &str,
    groups: &[&Vec<&FactObservation>],
    detail: F,
) -> WfError
where
    F: Fn(&FactObservation) -> String,
{
    let mut s = String::new();
    s.push_str(&underline_topic(title));
    s.push('\n');
    s.push_str(intro);
    s.push('\n');
    s.push_str("  \n"); // trailing 2-space line from HS `text ""`
                        // HS body = `text "\n" $-$ vcat (map formatCapIssue groups)`: the leading
                        // blank line (`text "\n"`) appears ONCE before the first group; each group
                        // ends with its own trailing `  \n` (from `$-$ text ""`), which is the only
                        // separator between groups.  So push the leading blank only for group 0.
    for (gi, group) in groups.iter().enumerate() {
        if gi == 0 {
            s.push('\n');
        }
        let name = group[0].name.to_lowercase();
        s.push_str(&format!("  Fact `{}':\n", name));
        s.push('\n');
        let w = numbered_index_width(group.len());
        for (i, obs) in group.iter().enumerate() {
            if i > 0 {
                s.push_str("    \n"); // 4-space trailing line
            }
            s.push_str(&format!(
                "    {:>w$}. {}, {}\n",
                i + 1,
                obs.origin,
                detail(obs),
                w = w,
            ));
            // HS `text(origin..) $-$ nest 2 ppFa` under `numbered'`: the
            // continuation `ppFa` aligns past the `flushRight w (show i) ++
            // ". "` prefix, so its indent grows with the index width:
            //   4 (outer nest) + w (flushRight) + 2 (". ") + 2 (nest 2) = 8 + w.
            // (Probed: width 1 => 9 spaces, width 2 => 10 spaces.)
            s.push_str(&format!("{}{}\n", " ".repeat(8 + w), obs.pp));
        }
        s.push_str("  \n"); // 2-space trailing line after the group
    }
    WfError::new(title, s)
}

// =============================================================================
// Proto-fact classification
// =============================================================================

/// `isProtoFact` for parser facts: every user fact (including the
/// reserved-named `K`, which HS parses as `ProtoFact "K"`) EXCEPT the
/// truly-special fact tags (`Fr`/`In`/`Out`/`KU`/`KD`/`Ded`/`Term`).
/// Mirrors HS `isProtoFact` (Theory/Model/Fact.hs:338-341) — note `K` is a
/// ProtoFact (`isKLogFact = isProtoFact && name=="K"`,
/// Theory/Model/Fact.hs:348-350).
fn is_proto_fact_name(name: &str) -> bool {
    !matches!(name, "Fr" | "In" | "Out" | "KU" | "KD" | "Ded" | "Term")
}

#[cfg(test)]
#[path = "facts_tests.rs"]
mod tests;
