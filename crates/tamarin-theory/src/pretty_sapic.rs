// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of the SAPIC process pretty-printers from
//! `lib/theory/src/Theory/Sapic/{Term,Process}.hs` and
//! `lib/theory/src/Theory/Model/Fact.hs`, used for the open theory's
//! `process:` blocks, the `process="..."` rule attribute and the
//! SAPIC-generated rule names.
//!
//! WRAPPING.  The `process="..."` attribute value is NOT a single
//! `text` — `prettySapicAction'` (Theory/Sapic/Process.hs:450-469) builds it by string
//! concatenation of literals (`"out("`, `"new "`, …) with the result of
//! `render` applied SEPARATELY to each embedded term/fact/pattern `Doc`.  That
//! inner `render` is `Text.PrettyPrint.Class.render = P.render`
//! (`lib/utils/src/Text/PrettyPrint/Class.hs:77-78`), i.e. the HughesPJ
//! DEFAULT `style = Style { lineLength = 100, ribbonsPerLine = 1.5 }`, giving
//! ribbon `round(100 / 1.5) = 67`.  This is DIFFERENT from the theory display
//! width (110 / 73) used everywhere else (`pretty_hpj::{LINE_LENGTH,RIBBON}`).
//! A long term such as `<aenc(shared_key.1, pk(skV.1)),
//! report(aenc(shared_key.1, pk(skV.1)))>` (70 cols > 67) therefore wraps
//! INSIDE the rendered term, with continuation lines indented by the `nest 1`
//! that `ppTerms`/pairs apply (Term/Term.hs:319-321).  Each `render` starts at
//! column 0 (the surrounding literals do not shift the wrap column), so we
//! render each sub-Doc standalone via [`render_sapic`].
//!
//! HS references:
//!   - `prettySapicTerm = prettyTerm (text . show)` (Theory/Sapic/Term.hs:168-169), where
//!     `show :: SapicLVar` is `show v ++ ":" ++ t` for typed vars
//!     (Theory/Sapic/Term.hs:108-110).
//!   - `prettyTerm` term Doc structure (Term/Term.hs:299-327): pairs via
//!     `ppTerms ", " 1 "<" ">"` (fcat + `nest 1`), AC ops via `ppTerms` over
//!     the operator's own separator (Term/Term.hs:304-309), functions via `ppFun =
//!     text(f++"(") <> fsep (punctuate comma args) <> ")"`.
//!   - `prettySapicFact = prettyFact prettySapicTerm` (Theory/Sapic/Term.hs:171-172); a
//!     fact renders as `Name( a, b )` via `nestShort' (n++"(") ")" . fsep .
//!     punctuate comma` (Theory/Model/Fact.hs:567-573, Text/PrettyPrint/Class.hs:221-223).
//!   - `prettySapicAction'` (Theory/Sapic/Process.hs:450-469).
//!   - `prettySapicTopLevel'` (Theory/Sapic/Process.hs:514-524).
//!
//! Scope: every `SapicAction` and `ProcessCombinator` variant, but only the
//! TOP node of a process — `prettySapic'`'s recursive `$-$`/`nest` layout
//! (Theory/Sapic/Process.hs:485-512) is not ported here; `pretty_theory::open_process_doc`
//! walks the tree and calls [`pretty_sapic_top_level`] per node.

use tamarin_term::function_symbols::{diff_sym, exp_sym, nat_one_sym, pair_sym, EMAP_SYM_STRING};
use tamarin_term::function_symbols::{AcSym, CSym, FunSym};
use tamarin_term::vterm::{Lit, VTerm};

use crate::pretty_hpj::{self as hpj, Doc};
use crate::sapic::{PlainProcess, Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm};

/// HughesPJ DEFAULT `lineLength` (`Text.PrettyPrint.HughesPJ.style`,
/// pretty-1.1.3.6 HughesPJ.hs:939).  The inner `render` calls in
/// `prettySapicAction'` use the bare `P.render` (Text/PrettyPrint/Class.hs:77-78), so they
/// render at this width, NOT the tamarin theory width (110).
const SAPIC_LINE_LENGTH: usize = 100;
/// HughesPJ DEFAULT ribbon = `round(lineLength / ribbonsPerLine)` =
/// `round(100 / 1.5) = 67`.
const SAPIC_RIBBON: usize = 67;

/// Render a SAPIC sub-Doc the way HS's inner `render` does: standalone,
/// starting at column 0, at the HughesPJ default width 100 / ribbon 67.
/// Continuation lines carry the `nest`-driven indent verbatim — matching
/// HS, which then string-concatenates the result with the surrounding action
/// literals.
fn render_sapic(d: Doc) -> String {
    d.render_with(SAPIC_LINE_LENGTH, SAPIC_RIBBON)
}

/// `show :: SapicLVar` (Theory/Sapic/Term.hs:108-110): `show lvar (++ ":" ++ type)`.
/// Also the typed-overlay process-def formal printer in `pretty_theory`, over
/// the post-`typeTheoryEnv` `SapicLVar`s (whose indices are the
/// `renameUnique` fresh ones, e.g. `c.1`).
pub(crate) fn show_sapic_lvar(v: &SapicLVar) -> String {
    let mut s = String::new();
    tamarin_term::pretty::pp_lvar(&v.var, &mut s);
    if let Some(t) = &v.stype {
        s.push(':');
        s.push_str(t);
    }
    s
}

/// `render (prettySapicTerm t)` over a `SapicTerm` — HS `prettyTerm (text .
/// show)` (Term/Term.hs:299-327) built as a HughesPJ `Doc` then rendered standalone
/// at the default width (100 / 67), so long terms WRAP exactly as HS's inner
/// `render` does.
pub(crate) fn pretty_sapic_term(t: &SapicTerm) -> String {
    render_sapic(sapic_term_to_doc(t, None))
}

/// `prettyTerm (text . show) t` as a `Doc`.  Structurally identical to
/// `pretty_formula::term_to_doc` (the parser-AST renderer that the rule body
/// uses), only over `SapicTerm = VTerm`: pairs → `pair_doc` (fcat + `nest 1`),
/// AC ops → `ac_op_doc`, functions → `fun_doc` (`text(f++"(") <> fsep(args)
/// <> ")"`).  `match_vars`, when `Some`, marks pattern-match variables with a
/// leading `=` (HS `prettyPattern' = prettySapicTerm . unextractMatchingVariables`,
/// Theory/Sapic/Process.hs:443-444).
fn sapic_term_to_doc(
    t: &SapicTerm,
    match_vars: Option<&std::collections::BTreeSet<SapicLVar>>,
) -> Doc {
    match t {
        VTerm::Lit(Lit::Var(v)) => {
            // `unextractMatchingVariables`: `v ∈ vs` → `PatternMatch v` (`=v`).
            let mut s = String::new();
            if let Some(mv) = match_vars {
                if mv.contains(v) {
                    s.push('=');
                }
            }
            s.push_str(&show_sapic_lvar(v));
            Doc::text(s)
        }
        VTerm::Lit(Lit::Con(n)) => {
            let mut s = String::new();
            tamarin_term::pretty::pp_name(n, &mut s);
            Doc::text(s)
        }
        // HS `prettyTerm` matches the user-defined AC symbols BEFORE the
        // builtin AC operators and prints a nullary application as the bare
        // symbol name (`FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)`,
        // Term/Term.hs:304).  Non-nullary ones fall through to the generic AC arm
        // below, whose separator renders as `" f "`.
        VTerm::App(FunSym::Ac(AcSym::AcFct(sym)), ts) if ts.is_empty() => {
            Doc::text(String::from_utf8_lossy(sym.name))
        }
        VTerm::App(FunSym::Ac(o), ts) => {
            // HS `FApp (AC o) ts -> ppTerms <op> 1 "(" ")" ts` (Term/Term.hs:305-309).
            let refs: Vec<&SapicTerm> = ts.iter().collect();
            ac_op_doc(tamarin_term::pretty::ac_op_symbol(*o), &refs, match_vars)
        }
        VTerm::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && *sym == exp_sym() => {
            // HS `... | s == expSym -> ppTerm t1 <> "^" <> ppTerm t2` (flat).
            sapic_term_to_doc(&ts[0], match_vars)
                .beside(Doc::text("^"))
                .beside(sapic_term_to_doc(&ts[1], match_vars))
        }
        VTerm::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && *sym == diff_sym() => {
            // HS `... | s == diffSym -> "diff" <> "(" <> ppTerm t1 <> ", " <>
            // ppTerm t2 <> ")"` (all `<>`, never breaks at the comma).
            Doc::text("diff(")
                .beside(sapic_term_to_doc(&ts[0], match_vars))
                .beside(Doc::text(", "))
                .beside(sapic_term_to_doc(&ts[1], match_vars))
                .beside(Doc::text(")"))
        }
        VTerm::App(FunSym::NoEq(sym), ts) if ts.is_empty() && *sym == nat_one_sym() => {
            Doc::text("%1")
        }
        VTerm::App(FunSym::NoEq(sym), _) if *sym == pair_sym() => {
            let mut flat: Vec<&SapicTerm> = Vec::new();
            collect_pair_tail(t, &mut flat);
            pair_doc(&flat, match_vars)
        }
        VTerm::App(FunSym::NoEq(sym), ts) => {
            let name = String::from_utf8_lossy(sym.name).into_owned();
            if ts.is_empty() {
                // HS `FApp (NoEq (f,_)) [] -> text f`.
                Doc::text(name)
            } else {
                let refs: Vec<&SapicTerm> = ts.iter().collect();
                fun_doc(&name, &refs, match_vars)
            }
        }
        VTerm::App(FunSym::C(CSym::EMap), ts) => {
            let name = String::from_utf8_lossy(EMAP_SYM_STRING).into_owned();
            let refs: Vec<&SapicTerm> = ts.iter().collect();
            fun_doc(&name, &refs, match_vars)
        }
        VTerm::App(FunSym::List, ts) => {
            let refs: Vec<&SapicTerm> = ts.iter().collect();
            fun_doc("LIST", &refs, match_vars)
        }
    }
}

/// HS `ppTerms ", " 1 "<" ">" flat` (Term/Term.hs:319-321): a fcat of `<`,
/// each element `nest 1`'d and comma-suffixed (except the last), and `>`.
fn pair_doc(
    flat: &[&SapicTerm],
    match_vars: Option<&std::collections::BTreeSet<SapicLVar>>,
) -> Doc {
    hpj::fcat_bracketed("<", ", ", ">", flat, |t| sapic_term_to_doc(t, match_vars))
}

/// HS `ppTerms <op> 1 "(" ")" ts` (Term/Term.hs:305-309, 319-321): like
/// `pair_doc` with `(`/`)` lead/finish and the AC-op symbol as separator (the
/// builtin ops carry no surrounding spaces; a user-defined AC name does).
fn ac_op_doc(
    sym: &str,
    flat: &[&SapicTerm],
    match_vars: Option<&std::collections::BTreeSet<SapicLVar>>,
) -> Doc {
    hpj::fcat_bracketed("(", sym, ")", flat, |t| sapic_term_to_doc(t, match_vars))
}

/// HS `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts))
/// <> text ")"` (Term/Term.hs:326-327).  The args are joined by a breakable
/// `fsep` over a bare `,` (no following space — HS `comma = text ","`).
fn fun_doc(
    name: &str,
    args: &[&SapicTerm],
    match_vars: Option<&std::collections::BTreeSet<SapicLVar>>,
) -> Doc {
    hpj::fun_app_doc(name, args, |a| sapic_term_to_doc(a, match_vars))
}

/// `render (prettyPattern' vs t)` (Theory/Sapic/Process.hs:443-444): render a `ChIn`/`let`
/// pattern term as a `Doc` (prefixing every variable in the match-var set `vs`
/// with `=`) then render standalone at 100 / 67, so a long pattern wraps the
/// same way HS's inner `render` does.
fn pretty_pattern(t: &SapicTerm, match_vars: &std::collections::BTreeSet<SapicLVar>) -> String {
    render_sapic(sapic_term_to_doc(t, Some(match_vars)))
}

/// HS `split` (Term/Term.hs:323-324): `split (viewTerm2 -> FPair t1 t2) = t1 :
/// split t2; split t = [t]`.  ONLY the RIGHT spine of a pair is flattened —
/// `pair(t1, t2)` yields `t1` then recurses into `t2`.  A LEFT-nested pair such
/// as `pair(pair(a,b), c)` therefore renders as `<<a, b>, c>` (the left child is
/// printed by the recursive `ppTerm`, NOT flattened here).
fn collect_pair_tail<'a>(t: &'a SapicTerm, out: &mut Vec<&'a SapicTerm>) {
    if let VTerm::App(FunSym::NoEq(sym), args) = t {
        if sym.name == b"pair" && args.len() == 2 {
            out.push(&args[0]);
            collect_pair_tail(&args[1], out);
            return;
        }
    }
    out.push(t);
}

/// `render (prettySapicFact a)` = `render (prettyFact prettySapicTerm a)`
/// (Theory/Sapic/Term.hs:171-172, Theory/Model/Fact.hs:567-573).  Built as a `Doc` via `nestShort'
/// (n++"(") ")" . fsep . punctuate comma` (Text/PrettyPrint/Class.hs:221-223) then rendered
/// standalone at 100 / 67.  On one line this is `Name( a, b )` — the leading
/// and trailing spaces come from `nestShort'`'s `sep [lead $$ nest k body,
/// finish]` overlap; an empty arg list renders `Name( )`.  A wide event fact
/// wraps the same way HS's inner `render` does.
fn pretty_sapic_fact(f: &crate::sapic::SapicLNFact) -> String {
    render_sapic(sapic_fact_to_doc(f))
}

/// HS `prettyFact prettySapicTerm` (Theory/Model/Fact.hs:567-573): `ppFact (showFactTag
/// tag) ts = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map
/// prettySapicTerm ts`.  (SAPIC event facts never carry annotations, so the
/// `<> ppAnn` suffix — empty for `S.null ann` — is omitted here, matching the
/// committed gate.)
fn sapic_fact_to_doc(f: &crate::sapic::SapicLNFact) -> Doc {
    sapic_fact_to_doc_pat(f, None)
}

/// `prettyFact` over a fact whose terms carry pattern markers: `match_vars`,
/// when `Some`, is the `unextractMatchingVariables` set applied to every term
/// (HS `rulePrinter`'s `l' = fmap (fmap (unextractMatchingVariables mv)) l`,
/// Print.hs:45).
fn sapic_fact_to_doc_pat(
    f: &crate::sapic::SapicLNFact,
    match_vars: Option<&std::collections::BTreeSet<SapicLVar>>,
) -> Doc {
    let name = crate::fact::show_fact_tag(&f.tag);
    let lead = format!("{name}(");
    let arg_docs: Vec<Doc> = f
        .terms
        .iter()
        .map(|t| sapic_term_to_doc(t, match_vars))
        .collect();
    let body = hpj::fsep(hpj::punctuate(Doc::char(','), arg_docs));
    hpj::nest_short_doc(&lead, ")", body)
}

/// Which MSR rule printer `prettySapic'` / `prettySapicTopLevel'` is
/// instantiated with.  HS takes it as a parameter because its two callers
/// disagree about the premise rendering.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MsrPrinter {
    /// `Theory.Sapic.Print.rulePrinter` (Print.hs:34-46): re-applies
    /// `unextractMatchingVariables mv` to the PREMISES, so each match variable
    /// prints with a leading `=`; the actions and conclusions get `mempty`, so
    /// they stay unmarked.  Used by `prettySapic` / `prettySapicTopLevel`,
    /// i.e. the `process:` / `let` / `equivLemma` blocks of an open theory.
    Sapic,
    /// `prettyRuleAttribute`'s local `ppProcess.f l a r rest _`
    /// (Theory/Model/Rule.hs:1324-1327): DISCARDS the match-var set, rendering the premises
    /// as plain facts.  Used for the `process="..."` rule attribute.
    Attribute,
}

/// The embedded-MSR rule printer.  Both HS instantiations go through
/// `prettyRuleRestrGen` (Model/Rule.hs:1366-1383), which builds
/// `[ prems ] --[ acts (+ _restrict(..)) ]-> [ concls ]`; with no actions and
/// no restrictions the arrow collapses to `-->`.  They differ only in the fact
/// printer: [`MsrPrinter::Sapic`] marks the premises' match variables with `=`,
/// [`MsrPrinter::Attribute`] does not.
fn render_msr(
    prems: &[crate::sapic::SapicLNFact],
    acts: &[crate::sapic::SapicLNFact],
    concls: &[crate::sapic::SapicLNFact],
    rest: &[tamarin_parser::ast::Formula],
    match_vars: &std::collections::BTreeSet<SapicLVar>,
    printer: MsrPrinter,
) -> String {
    let prem_mv = match printer {
        MsrPrinter::Sapic => Some(match_vars),
        MsrPrinter::Attribute => None,
    };

    // `ppFactsList list = fsep [ "[", fsep (punctuate "," (map ppFact list)), "]" ]`.
    let pp_facts_list = |facts: &[crate::sapic::SapicLNFact],
                         mv: Option<&std::collections::BTreeSet<SapicLVar>>|
     -> Doc {
        let inner: Vec<Doc> = facts.iter().map(|f| sapic_fact_to_doc_pat(f, mv)).collect();
        hpj::fsep(vec![
            Doc::char('['),
            hpj::fsep(hpj::punctuate(Doc::char(','), inner)),
            Doc::char(']'),
        ])
    };

    // The action/restriction row.
    let arrow_row = if acts.is_empty() && rest.is_empty() {
        Doc::text("-->")
    } else {
        // map ppFact acts ++ map ppRestr' restr
        let mut items: Vec<Doc> = acts.iter().map(sapic_fact_to_doc).collect();
        for phi in rest {
            // `ppRestr' fact = "_restrict(" <> ppRestr fact <> ")"`,
            // `ppRestr = prettySyntacticLNFormula . toLFormula` — the flat
            // single-line formula renderer (matches `Cond`'s formula path).
            // HS's payload is a formula over signature-built `SapicTerm`s, so
            // `fAppAC`/`fAppC` flattened and sorted every AC/C application at
            // parse time and `prettyTerm` prints AC nodes infix; the RS payload
            // is the parser AST in written order, so canonicalise first — same
            // treatment `ProcessCombinator::Cond` gets, and this render feeds
            // both the `process="..."` attribute and the SAPIC-derived rule
            // names, which must agree.
            let canonical = crate::elaborate::canonicalize_ac_in_formula(phi);
            let inner = crate::pretty_formula::pretty_formula(&canonical);
            items.push(Doc::text(format!("_restrict({inner})")));
        }
        hpj::fsep(vec![
            Doc::text("--["),
            hpj::fsep(hpj::punctuate(Doc::char(','), items)),
            Doc::text("]->"),
        ])
    };

    let doc = hpj::sep(vec![
        pp_facts_list(prems, prem_mv).nest(1),
        arrow_row,
        pp_facts_list(concls, None).nest(1),
    ]);
    render_sapic(doc)
}

/// `prettySapicAction'` (Theory/Sapic/Process.hs:450-469), linear subset.
fn pretty_sapic_action(a: &SapicAction<SapicLVar>, printer: MsrPrinter) -> String {
    match a {
        SapicAction::New(v) => format!("new {}", show_sapic_lvar(v)),
        SapicAction::Rep => "!".to_string(),
        SapicAction::Event(fa) => format!("event {}", pretty_sapic_fact(fa)),
        SapicAction::ChOut { chan: None, msg } => {
            format!("out({})", pretty_sapic_term(msg))
        }
        SapicAction::ChOut { chan: Some(c), msg } => {
            format!("out({},{})", pretty_sapic_term(c), pretty_sapic_term(msg))
        }
        SapicAction::ChIn {
            chan: None,
            msg,
            match_vars,
        } => {
            format!("in({})", pretty_pattern(msg, match_vars))
        }
        SapicAction::ChIn {
            chan: Some(c),
            msg,
            match_vars,
        } => {
            format!(
                "in({},{})",
                pretty_sapic_term(c),
                pretty_pattern(msg, match_vars)
            )
        }
        SapicAction::Insert(a, b) => {
            format!("insert {},{}", pretty_sapic_term(a), pretty_sapic_term(b))
        }
        SapicAction::Delete(t) => format!("delete {}", pretty_sapic_term(t)),
        SapicAction::Lock(t) => format!("lock {}", pretty_sapic_term(t)),
        SapicAction::Unlock(t) => format!("unlock {}", pretty_sapic_term(t)),
        SapicAction::ProcessCall(s, ts) => {
            // HS `prettySapicAction' _ (ProcessCall s ts) = s ++ "(" ++ p ts
            // ++ ")"` where `p pts = render $ fsep (punctuate comma (map
            // prettySapicTerm pts))` (Theory/Sapic/Process.hs:469-471).  The args render
            // standalone via a breakable `fsep` over a bare `,`.
            let arg_docs: Vec<Doc> = ts.iter().map(|t| sapic_term_to_doc(t, None)).collect();
            let body = render_sapic(hpj::fsep(hpj::punctuate(Doc::char(','), arg_docs)));
            format!("{}({})", s, body)
        }
        // HS `prettySapicAction' prettyRule' (MSR p a c r mv) = prettyRule' p a c r mv`
        // (Theory/Sapic/Process.hs:450-471, see line 468); `prettyRule'` is the caller-supplied
        // printer selected by `printer`.
        SapicAction::Msr {
            prems,
            acts,
            concs,
            rest,
            match_vars,
        } => render_msr(prems, acts, concs, rest, match_vars, printer),
    }
}

/// `prettySapicComb` (Theory/Sapic/Process.hs:473-485), only the cases reachable here.
fn pretty_sapic_comb(c: &ProcessCombinator<SapicLVar>) -> String {
    match c {
        ProcessCombinator::Parallel => "|".to_string(),
        ProcessCombinator::Ndc => "+".to_string(),
        // HS `prettySapicComb (CondEq t t') = "if "++ p t ++ "=" ++ p t'`.
        ProcessCombinator::CondEq(t, t2) => {
            format!("if {}={}", pretty_sapic_term(t), pretty_sapic_term(t2))
        }
        // HS `prettySapicComb (Cond a) = "if "++ render (prettySyntacticSapicFormula a)`
        // (Theory/Sapic/Process.hs:473-483, see line 476).  `prettySyntacticSapicFormula = prettySyntacticLNFormula
        // . toLFormula` (Theory/Sapic/Term.hs:174-175); `toLFormula` just drops the SAPIC type
        // tags (`SapicLVar → LVar`), keeping the syntactic structure (predicates
        // intact, formula un-expanded).  The RS `Cond` carries the un-expanded
        // parser-AST formula whose `VarSpec`s render WITHOUT type tags, so
        // `pretty_formula` (the flat, single-line renderer) matches
        // `render . prettySyntacticSapicFormula`.
        //
        // HS's payload is a formula over `SapicTerm`s built by the signature-aware
        // term parser, so every AC application was flattened + sorted by `fAppAC`
        // and every `C` application sorted by `fAppC` at parse time
        // (`naryOpApp`, Theory/Text/Parser/Term.hs:88-105; Term/Term/Raw.hs:118-133),
        // and `prettyTerm` then prints the AC node infix (Term/Term.hs:305).  The
        // parser AST keeps the written order instead, so canonicalise here to
        // reach the same operand order and the same infix spelling — this render
        // feeds BOTH the `process="..."` attribute and the SAPIC-derived rule
        // names, which must agree.
        ProcessCombinator::Cond(f) => {
            let canonical = crate::elaborate::canonicalize_ac_in_formula(f);
            format!("if {}", crate::pretty_formula::pretty_formula(&canonical))
        }
        // HS `prettySapicComb (Lookup t v) = "lookup "++ p t ++ " as " ++ show v`
        // (Theory/Sapic/Process.hs:473-483, see line 482).  `show v` on an (untyped) `SapicLVar` is just the
        // LVar display name (`x.1`); a typed var would append `:type`, but
        // lookup binders are never typed by inference (`typeWithVar`).
        ProcessCombinator::Lookup(t, v) => {
            format!("lookup {} as {}", pretty_sapic_term(t), show_sapic_lvar(v))
        }
        // HS `prettySapicComb (Let t t' vs) = "let "++ p' t ++ "=" ++ p t'`
        // where `p = render . prettySapicTerm` and `p' = render . prettyPattern' vs`
        // (Theory/Sapic/Process.hs:479-481).  `prettyPattern' vs = prettySapicTerm .
        // unextractMatchingVariables vs` renders the LEFT pattern with its match
        // vars `=`-prefixed; the RIGHT is a plain term.
        ProcessCombinator::Let {
            left,
            right,
            match_vars,
        } => {
            format!(
                "let {}={}",
                pretty_pattern(left, match_vars),
                pretty_sapic_term(right)
            )
        }
    }
}

/// `prettySapicTopLevel' prettyRule'` (Theory/Sapic/Process.hs:514-524).  Only inspects the
/// TOP node.
fn pretty_sapic_top_level_with(p: &PlainProcess, printer: MsrPrinter) -> String {
    match p {
        Process::Null(_) => "0".to_string(),
        Process::Comb(c, _, _, _) => pretty_sapic_comb(c),
        Process::Action(SapicAction::Rep, _, _) => pretty_sapic_action(&SapicAction::Rep, printer),
        Process::Action(a, _, _) => format!("{};", pretty_sapic_action(a, printer)),
    }
}

/// `prettySapicTopLevel = prettySapicTopLevel' rulePrinter` (Print.hs:56):
/// the `process:` / `let` / `equivLemma` block printer and the source of the
/// SAPIC-generated rule names.
pub fn pretty_sapic_top_level(p: &PlainProcess) -> String {
    pretty_sapic_top_level_with(p, MsrPrinter::Sapic)
}

/// `prettySapicTopLevel' f` with `prettyRuleAttribute`'s local `f`
/// (Theory/Model/Rule.hs:1324-1327): the `process="..."` rule-attribute value.
pub fn pretty_sapic_top_level_attr(p: &PlainProcess) -> String {
    pretty_sapic_top_level_with(p, MsrPrinter::Attribute)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sapic::ProcessParsedAnnotation;
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::f_app_no_eq;

    fn sv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(String::from))
    }

    #[test]
    fn new_top_level() {
        let p = Process::Action(
            SapicAction::New(sv("x", 1, Some("lol"))),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        assert_eq!(pretty_sapic_top_level(&p), "new x.1:lol;");
    }

    #[test]
    fn out_ffx_top_level() {
        let f = NoEqSym::new(
            b"f".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let x = VTerm::Lit(Lit::Var(sv("x", 1, Some("lol"))));
        let ffx = f_app_no_eq(f, vec![f_app_no_eq(f, vec![x])]);
        let p = Process::Action(
            SapicAction::ChOut {
                chan: None,
                msg: ffx,
            },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        assert_eq!(pretty_sapic_top_level(&p), "out(f(f(x.1:lol)));");
    }

    #[test]
    fn event_top_level_has_spaces() {
        let x = VTerm::Lit(Lit::Var(sv("x", 1, Some("lol"))));
        let fact = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Test", 1),
            vec![x],
        );
        let p = Process::Action(
            SapicAction::Event(fact),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        assert_eq!(pretty_sapic_top_level(&p), "event Test( x.1:lol );");
    }

    #[test]
    fn user_ac_term_infix_and_nullary() {
        use tamarin_term::function_symbols::{AcFctSym, AcSym, NdcState};
        let f = AcFctSym::new(
            b"f".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        let x = VTerm::Lit(Lit::Var(sv("x", 1, None)));
        let y = VTerm::Lit(Lit::Var(sv("y", 1, None)));
        let applied = tamarin_term::term::f_app_ac(AcSym::AcFct(f), vec![x, y]);
        assert_eq!(
            render_sapic(sapic_term_to_doc(&applied, None)),
            "(x.1 f y.1)"
        );
        // HS `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term/Term.hs:304):
        // the bare name, no parens.  `f_app_ac` rejects an empty argument list
        // (HS `fAppAC` errors likewise, Raw.hs:120), so no theory text reaches
        // this arm — it is here to keep the printer the shape of `prettyTerm`.
        let nullary: SapicTerm = VTerm::App(FunSym::Ac(AcSym::AcFct(f)), vec![].into());
        assert_eq!(render_sapic(sapic_term_to_doc(&nullary, None)), "f");
    }

    #[test]
    fn null_top_level() {
        let p: PlainProcess = Process::Null(ProcessParsedAnnotation::empty());
        assert_eq!(pretty_sapic_top_level(&p), "0");
    }

    /// `if <formula>` renders its user-`[AC]` applications the way HS's
    /// signature-built `SapicTerm`s do: flattened, sorted, infix.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `functions: add/2 [AC]` + `predicates: Eq(a, b) <=> a = b` +
    /// `in(k); if Eq(<'g'^k, add(k,'a')>, k) then out('yes') else out('no')`:
    ///   `process="if Eq( <'g'^k.1, ('a' add k.1)>, k.1 )"`
    /// and for `if Eq(add(k, add('a','b')), k)`:
    ///   `process="if Eq( ('a' add 'b' add k.1), k.1 )"`.
    #[test]
    fn cond_renders_user_ac_flattened_sorted_and_infix() {
        use tamarin_parser::ast as p;

        let k = p::Term::Var(p::VarSpec {
            typ: None,
            name: "k".into(),
            sort: LSort::Msg,
            idx: 1,
        });
        let eq_cond = |args: Vec<p::Term>| {
            let f = p::Formula::Atom(p::Atom::Pred(p::Fact {
                persistent: false,
                name: "Eq".into(),
                args,
                annotations: Vec::new(),
            }));
            let proc: PlainProcess = Process::Comb(
                ProcessCombinator::Cond(f),
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())),
            );
            pretty_sapic_top_level(&proc)
        };

        let add = |a: p::Term, b: p::Term| {
            p::Term::BinOp(
                p::BinOp::AcFct(tamarin_term::intern::intern_str("add")),
                Box::new(a),
                Box::new(b),
            )
        };

        // `<'g'^k.1, add(k.1, 'a')>` with `add` an ordinary function symbol:
        // the application stays prefix, which is what makes the AC
        // assertions below discriminating.
        let pair_with = |second: p::Term| {
            vec![
                p::Term::Pair(vec![
                    p::Term::BinOp(
                        p::BinOp::Exp,
                        Box::new(p::Term::PubLit("g".into())),
                        Box::new(k.clone()),
                    ),
                    second,
                ]),
                k.clone(),
            ]
        };
        assert_eq!(
            eq_cond(pair_with(p::Term::App(
                "add".into(),
                vec![k.clone(), p::Term::PubLit("a".into())],
            ))),
            "if Eq( <'g'^k.1, add(k.1, 'a')>, k.1 )"
        );

        // The `[AC]` symbol's node, in the non-canonical operand order the
        // source spelling `add(k, 'a')` gives it.
        assert_eq!(
            eq_cond(pair_with(add(k.clone(), p::Term::PubLit("a".into())))),
            "if Eq( <'g'^k.1, ('a' add k.1)>, k.1 )"
        );
        // A nested chain flattens to three operands under one AC node.
        let m2 = vec![
            add(
                k.clone(),
                add(p::Term::PubLit("a".into()), p::Term::PubLit("b".into())),
            ),
            k.clone(),
        ];
        assert_eq!(eq_cond(m2), "if Eq( ('a' add 'b' add k.1), k.1 )");
    }

    /// An MSR's embedded `_restrict(...)` renders its user-`[AC]` applications
    /// the same way `if <formula>` does — the render feeds both the
    /// `process="..."` attribute and the SAPIC-derived rule/restriction names.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `builtins: xor` + `functions: add/2 [AC]` +
    /// `in(k); [ ] --[ Ev(add(k,'a')), _restrict(add(k,'a') = k) ]-> [ ]; out('y')`:
    ///   `process=" [ ] --[ Ev( ('a' add k.1) ), _restrict(('a' add k.1) = k.1) ]-> [ ];"`
    #[test]
    fn msr_restriction_renders_user_ac_flattened_sorted_and_infix() {
        use tamarin_parser::ast as p;

        let k = p::Term::Var(p::VarSpec {
            typ: None,
            name: "k".into(),
            sort: LSort::Msg,
            idx: 1,
        });
        let restr = |head: p::Term| p::Formula::Atom(p::Atom::Eq(head, k.clone()));
        let add_prefix = p::Term::App("add".into(), vec![k.clone(), p::Term::PubLit("a".into())]);
        let add_ac = p::Term::BinOp(
            p::BinOp::AcFct(tamarin_term::intern::intern_str("add")),
            Box::new(k.clone()),
            Box::new(p::Term::PubLit("a".into())),
        );
        let ev = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Ev", 1),
            vec![tamarin_term::term::f_app_ac(
                tamarin_term::function_symbols::AcSym::AcFct(
                    tamarin_term::function_symbols::AcFctSym::new(
                        b"add".to_vec(),
                        Privacy::Public,
                        Constructability::Constructor,
                        tamarin_term::function_symbols::NdcState::NotNdc,
                    ),
                ),
                vec![
                    VTerm::Lit(Lit::Var(sv("k", 1, None))),
                    VTerm::Lit(Lit::Con(tamarin_term::lterm::Name::new(
                        tamarin_term::lterm::NameTag::Pub,
                        "a",
                    ))),
                ],
            )],
        );
        let msr = |rest: Vec<p::Formula>| {
            let proc: PlainProcess = Process::Action(
                SapicAction::Msr {
                    prems: Vec::new(),
                    acts: vec![ev.clone()],
                    concs: Vec::new(),
                    rest,
                    match_vars: std::collections::BTreeSet::new(),
                },
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())),
            );
            pretty_sapic_top_level(&proc)
        };

        // With `add` an ordinary function symbol the application stays
        // prefix — this is what makes the AC assertion below discriminating.
        assert_eq!(
            msr(vec![restr(add_prefix)]),
            " [ ] --[ Ev( ('a' add k.1) ), _restrict(add(k.1, 'a') = k.1) ]-> [ ];"
        );
        assert_eq!(
            msr(vec![restr(add_ac)]),
            " [ ] --[ Ev( ('a' add k.1) ), _restrict(('a' add k.1) = k.1) ]-> [ ];"
        );
    }
}
