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
//!   - `prettySapicTerm = prettyTerm (text . show)` (Theory/Sapic/Term.hs:168-169):
//!     the shared `prettyTerm` (Term/Term.hs:299-327,
//!     [`tamarin_term::pretty::pretty_term`]) at the literal printer
//!     `Show (Lit c v)` (Term/VTerm.hs:98-100), whose variable half is
//!     `show v ++ ":" ++ t` for typed vars (Theory/Sapic/Term.hs:108-110).
//!     Pairs go through `ppTerms ", " 1 "<" ">"` (fcat + `nest 1`,
//!     Term/Term.hs:319-321), so a wrapped term carries that indent.
//!   - `prettySapicFact = prettyFact prettySapicTerm` (Theory/Sapic/Term.hs:171-172,
//!     [`crate::fact::pretty_fact`]); a fact renders as `Name( a, b )` via
//!     `nestShort' (n++"(") ")" . fsep . punctuate comma`
//!     (Theory/Model/Fact.hs:566-574, Text/PrettyPrint/Class.hs:221-223).
//!   - `prettySapicAction'` (Theory/Sapic/Process.hs:450-469).
//!   - `prettySapicTopLevel'` (Theory/Sapic/Process.hs:514-524).
//!
//! Scope: every `SapicAction` and `ProcessCombinator` variant, but only the
//! TOP node of a process — `prettySapic'`'s recursive `$-$`/`nest` layout
//! (Theory/Sapic/Process.hs:485-512) is not ported here; `pretty_theory::open_process_doc`
//! walks the tree and calls [`pretty_sapic_top_level`] per node.

use std::collections::BTreeSet;

use tamarin_term::lterm::Name;
use tamarin_term::pretty::{pretty_nterm, pretty_term};
use tamarin_term::vterm::Lit;

use crate::fact::pretty_fact;
use crate::pretty_hpj::{self as hpj, Doc};
use crate::sapic::{
    PlainProcess, Process, ProcessCombinator, SapicAction, SapicLNFact, SapicLVar, SapicTerm,
};

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
pub(crate) fn render_sapic(d: Doc) -> String {
    d.render_with(SAPIC_LINE_LENGTH, SAPIC_RIBBON)
}

/// `render (prettySapicTerm t)` over a `SapicTerm` — HS `prettyTerm (text .
/// show)` (Theory/Sapic/Term.hs:168-169), the same body as `prettyNTerm`
/// (Term/LTerm.hs:930-931) at `v = SapicLVar`, built as a HughesPJ `Doc` then
/// rendered standalone at the default width (100 / 67), so long terms WRAP
/// exactly as HS's inner `render` does.
pub(crate) fn pretty_sapic_term(t: &SapicTerm) -> String {
    render_sapic(pretty_nterm(t))
}

/// `prettyPattern' vs t` (Theory/Sapic/Process.hs:443-444) as a `Doc`:
/// `prettySapicTerm . unextractMatchingVariables vs`.
/// `unextractMatchingVariables` (Theory/Sapic/Pattern.hs:99-102) retags every
/// variable of the term, and the tag is read only by
/// `Show PatternSapicLVar` (Theory/Sapic/Pattern.hs:46-48), which spells a
/// matched variable `"=" ++ show v` and a bound one `show v`.  The retagging
/// therefore lives entirely in the literal printer handed to `prettyTerm`.
fn pattern_term_doc(t: &SapicTerm, match_vars: &BTreeSet<SapicLVar>) -> Doc {
    pretty_term(
        &|l: &Lit<Name, SapicLVar>| match l {
            Lit::Var(v) if match_vars.contains(v) => Doc::text(format!("={v}")),
            _ => Doc::text(l.to_string()),
        },
        t,
    )
}

/// `render (prettyPattern' vs t)` (Theory/Sapic/Process.hs:443-444): a
/// `ChIn`/`let` pattern rendered standalone at 100 / 67, so a long pattern
/// wraps the same way HS's inner `render` does.
fn pretty_pattern(t: &SapicTerm, match_vars: &BTreeSet<SapicLVar>) -> String {
    render_sapic(pattern_term_doc(t, match_vars))
}

/// `prettySapicFact` (Theory/Sapic/Term.hs:171-172) = `prettyFact
/// prettySapicTerm`.  `match_vars`, when `Some`, is the
/// `unextractMatchingVariables` set applied to every term of the fact (HS
/// `rulePrinter`'s `l' = fmap (fmap (unextractMatchingVariables mv)) l` for
/// the premises, Print.hs:45); `None` is its `toPat`, which passes `mempty`
/// for the actions and conclusions (Print.hs:46) and so marks nothing.
fn sapic_fact_doc(f: &SapicLNFact, match_vars: Option<&BTreeSet<SapicLVar>>) -> Doc {
    match match_vars {
        Some(vs) => pretty_fact(&|t: &SapicTerm| pattern_term_doc(t, vs), f),
        None => pretty_fact(&|t: &SapicTerm| pretty_nterm(t), f),
    }
}

/// `render (prettySapicFact a)` (Theory/Sapic/Term.hs:171-172): the fact Doc
/// rendered standalone at 100 / 67.  On one line this is `Name( a, b )` — the
/// leading and trailing spaces come from `nestShort'`'s
/// `sep [lead $$ nest k body, finish]` overlap
/// (Text/PrettyPrint/Class.hs:218-223); an empty argument list renders
/// `Name( )`.  A wide event fact wraps the same way HS's inner `render` does.
fn pretty_sapic_fact(f: &SapicLNFact) -> String {
    render_sapic(sapic_fact_doc(f, None))
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
    prems: &[SapicLNFact],
    acts: &[SapicLNFact],
    concls: &[SapicLNFact],
    rest: &[crate::sapic::SapicFormula],
    match_vars: &BTreeSet<SapicLVar>,
    printer: MsrPrinter,
) -> String {
    let prem_mv = match printer {
        MsrPrinter::Sapic => Some(match_vars),
        MsrPrinter::Attribute => None,
    };

    // `ppFactsList list = fsep [ "[", fsep (punctuate "," (map ppFact list)), "]" ]`.
    let pp_facts_list = |facts: &[SapicLNFact], mv: Option<&BTreeSet<SapicLVar>>| -> Doc {
        let inner: Vec<Doc> = facts.iter().map(|f| sapic_fact_doc(f, mv)).collect();
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
        let mut items: Vec<Doc> = acts.iter().map(|f| sapic_fact_doc(f, None)).collect();
        for phi in rest {
            // `ppRestr' fact = operator_ "_restrict(" <> ppRestr fact <>
            // operator_ ")"` (Theory/Model/Rule.hs:1382#ppRestr') with
            // `ppRes = prettySyntacticLNFormula . toLFormula`
            // (Theory/Sapic/Print.hs:41-44#rulePrinter).  The formula is a Doc
            // inside that composition, so a break it takes indents by the ten
            // columns of the opening operator and the whole item takes part in
            // the rule's layout, which the caller closes with `render_sapic`.
            items.push(
                hpj::operator_("_restrict(")
                    .beside(crate::pretty_formula::syntactic_lnformula_doc(
                        &crate::sapic::to_lformula(phi),
                    ))
                    .beside(hpj::operator_(")")),
            );
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
        SapicAction::New(v) => format!("new {v}"),
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
            let arg_docs: Vec<Doc> = ts.iter().map(pretty_nterm).collect();
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
        // (Theory/Sapic/Process.hs:473-483, see line 476).
        // `prettySyntacticSapicFormula = prettySyntacticLNFormula . toLFormula`
        // (Theory/Sapic/Term.hs:174-175) drops the SAPIC type tags and keeps
        // the syntactic structure (predicates intact, formula un-expanded).
        // The `render` is the inner one this module's header documents, so the
        // formula wraps at the HughesPJ default width — and the same string
        // feeds BOTH the `process="..."` attribute and the SAPIC-derived rule
        // names, which the `filter isAlpha` of `stripNonAlphanumerical`
        // (Sapic/Facts.hs:401) leaves unaffected by the break.
        ProcessCombinator::Cond(f) => {
            format!(
                "if {}",
                render_sapic(crate::pretty_formula::syntactic_lnformula_doc(
                    &crate::sapic::to_lformula(f)
                ))
            )
        }
        // HS `prettySapicComb (Lookup t v) = "lookup "++ p t ++ " as " ++ show v`
        // (Theory/Sapic/Process.hs:473-483, see line 482).  `show v` on an (untyped) `SapicLVar` is just the
        // LVar display name (`x.1`); a typed var would append `:type`, but
        // lookup binders are never typed by inference (`typeWithVar`).
        ProcessCombinator::Lookup(t, v) => {
            format!("lookup {} as {v}", pretty_sapic_term(t))
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
///
/// Every `Doc` this module builds and hands to [`render_sapic`] is built and
/// laid out in plain mode, whatever the caller's rendering context.  HS's
/// inner `render` is the plain `P.render` on a plain `Doc`
/// (Text/PrettyPrint/Class.hs:77-78), so the process text carries raw `<`,
/// `>` and `'` at their visible widths; the callers put that string back into
/// a `Doc::text`, which is where `Document (HtmlDoc d)` (Html.hs:102-104)
/// escapes it — once.
fn pretty_sapic_top_level_with(p: &PlainProcess, printer: MsrPrinter) -> String {
    let _plain = hpj::HtmlDocGuard::disable();
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
    use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::f_app_no_eq;
    use tamarin_term::vterm::VTerm;

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
        assert_eq!(pretty_sapic_term(&applied), "(x.1 f y.1)");
        // HS `FApp (AC (ACfct (f, _))) [] -> text (BC.unpack f)` (Term/Term.hs:304):
        // the bare name, no parens.  `f_app_ac` rejects an empty argument list
        // (HS `fAppAC` errors likewise, Raw.hs:120), so no theory text reaches
        // this arm — it is here to keep the printer the shape of `prettyTerm`.
        let nullary: SapicTerm = VTerm::App(FunSym::Ac(AcSym::AcFct(f)), vec![].into());
        assert_eq!(pretty_sapic_term(&nullary), "f");
    }

    #[test]
    fn null_top_level() {
        let p: PlainProcess = Process::Null(ProcessParsedAnnotation::empty());
        assert_eq!(pretty_sapic_top_level(&p), "0");
    }

    /// The Maude signature of a one-line theory, for building a condition
    /// from source text the way the SAPIC parser does.
    fn sig_of(decl: &str) -> tamarin_term::maude_sig::MaudeSig {
        let thy =
            tamarin_parser::parse_theory(&format!("theory T begin\n{decl}\nend"), &[]).unwrap();
        crate::elaborate::elaborate(&thy).unwrap().signature
    }

    /// `if <formula>` as the process printer renders it, with `formula` read
    /// against the signature `decl` declares.
    fn cond_render(src: &str, decl: &str) -> String {
        let sig = sig_of(decl);
        let f = tamarin_parser::parser::parse_formula_str(src, &sig).unwrap();
        let proc: PlainProcess = Process::Comb(
            ProcessCombinator::Cond(crate::formula::sapic_from_parser(&f, &sig).unwrap()),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        pretty_sapic_top_level(&proc)
    }

    /// A conditional renders its formula STANDALONE, so a conjunction wider
    /// than the HughesPJ default page breaks and the second conjunct starts a
    /// new line at column 0.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1` +
    /// `predicates: Longer(xxxxxxxxxx, yyyyyyyyyy) <=> xxxxxxxxxx = yyyyyyyyyy` +
    /// `in(<xxxxxxxxxx, yyyyyyyyyy, zzzzzzzzzz>); if Longer(aaaaaaaaaa(xxxxxxxxxx), bbbbbbbbbb(yyyyyyyyyy)) & Longer(cccccccccc(zzzzzzzzzz), aaaaaaaaaa(yyyyyyyyyy)) then …`
    /// (fixture `sapic_cond_wrap`).
    #[test]
    fn cond_wraps_at_the_hughespj_default_width() {
        let got = cond_render(
            "Longer(aaaaaaaaaa(xxxxxxxxxx.1), bbbbbbbbbb(yyyyyyyyyy.1)) \
             & Longer(cccccccccc(zzzzzzzzzz.1), aaaaaaaaaa(yyyyyyyyyy.1))",
            "functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1",
        );
        assert_eq!(
            got,
            "if (Longer( aaaaaaaaaa(xxxxxxxxxx.1), bbbbbbbbbb(yyyyyyyyyy.1) )) ∧\n\
             (Longer( cccccccccc(zzzzzzzzzz.1), aaaaaaaaaa(yyyyyyyyyy.1) ))"
        );
        // The derived rule name is `filter isAlpha` over the same string
        // (Sapic/Facts.hs:401#stripNonAlphanumerical), so the break leaves it
        // untouched.
        let name: String = got.chars().filter(|c| c.is_alphabetic()).collect();
        assert_eq!(
            name,
            "ifLongeraaaaaaaaaaxxxxxxxxxxbbbbbbbbbbyyyyyyyyyyLongercccccccccczzzzzzzzzzaaaaaaaaaayyyyyyyyyy"
        );
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
        // `^` is a term operator only under `builtins: diffie-hellman`
        // (Theory/Text/Parser/Term.hs:179-185).
        // With `add` an ordinary function symbol the application stays
        // prefix, which is what makes the AC assertions below discriminating.
        assert_eq!(
            cond_render(
                "Eq(<'g'^k.1, add(k.1,'a')>, k.1)",
                "builtins: diffie-hellman\nfunctions: add/2"
            ),
            "if Eq( <'g'^k.1, add(k.1, 'a')>, k.1 )"
        );
        assert_eq!(
            cond_render(
                "Eq(<'g'^k.1, add(k.1,'a')>, k.1)",
                "builtins: diffie-hellman\nfunctions: add/2 [AC]"
            ),
            "if Eq( <'g'^k.1, ('a' add k.1)>, k.1 )"
        );
        // A nested chain flattens to three operands under one AC node.
        assert_eq!(
            cond_render("Eq(add(k.1, add('a','b')), k.1)", "functions: add/2 [AC]"),
            "if Eq( ('a' add 'b' add k.1), k.1 )"
        );
    }

    /// An embedded MSR as the process printer renders it: one `Ev(<arg>)`
    /// action and one `_restrict(<restr>)`, both read against the signature
    /// `decl` declares.
    fn msr_render(arg: &str, restr: &str, decl: &str) -> String {
        use tamarin_parser::ast::{Atom, Formula};

        let sig = sig_of(decl);
        // The action's argument comes back out of an action atom, the formula
        // entry point's way of reading one term with `sig`'s symbols.
        let action =
            tamarin_parser::parser::parse_formula_str(&format!("Ev({arg}) @ #i"), &sig).unwrap();
        let t = match &action {
            Formula::Atom(Atom::Action(fact, _)) => fact.args[0].clone(),
            other => panic!("expected an action atom, got {other:?}"),
        };
        let f = tamarin_parser::parser::parse_formula_str(restr, &sig).unwrap();
        let ev = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Ev", 1),
            vec![crate::elaborate::term_to_sapic_term(&t, &sig).unwrap()],
        );
        let proc: PlainProcess = Process::Action(
            SapicAction::Msr {
                prems: Vec::new(),
                acts: vec![ev],
                concs: Vec::new(),
                rest: vec![crate::formula::sapic_from_parser(&f, &sig).unwrap()],
                match_vars: std::collections::BTreeSet::new(),
            },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        pretty_sapic_top_level(&proc)
    }

    /// An MSR's embedded `_restrict(...)` renders its user-`[AC]` applications
    /// the way HS's signature-built `SapicTerm`s do: flattened, sorted, infix.
    /// The render feeds both the `process="..."` attribute and the
    /// SAPIC-derived rule/restriction names.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `in(k); [ ] --[ Ev(add(k,'a')), _restrict(add(k,'a') = k) ]-> [ ]; out('y')`
    /// with `functions: add/2 [AC]`:
    ///   `process=" [ ] --[ Ev( ('a' add k.1) ), _restrict(('a' add k.1) = k.1) ]-> [ ];"`
    /// and with `functions: add/2`:
    ///   `process=" [ ] --[ Ev( add(k.1, 'a') ), _restrict(add(k.1, 'a') = k.1) ]-> [ ];"`
    #[test]
    fn msr_restriction_renders_user_ac_flattened_sorted_and_infix() {
        // With `add` an ordinary function symbol the application stays
        // prefix, which is what makes the AC assertion below discriminating.
        assert_eq!(
            msr_render("add(k.1,'a')", "add(k.1,'a') = k.1", "functions: add/2"),
            " [ ] --[ Ev( add(k.1, 'a') ), _restrict(add(k.1, 'a') = k.1) ]-> [ ];"
        );
        assert_eq!(
            msr_render(
                "add(k.1,'a')",
                "add(k.1,'a') = k.1",
                "functions: add/2 [AC]"
            ),
            " [ ] --[ Ev( ('a' add k.1) ), _restrict(('a' add k.1) = k.1) ]-> [ ];"
        );
    }

    /// `prettyFact`'s annotation suffix (Theory/Model/Fact.hs:573-574) reaches
    /// the embedded MSR through `rulePrinter`'s `ppFact = prettyFact $
    /// prettyTerm $ text . show` (Print.hs:43), so an annotated fact carries
    /// its `[…]` into the `process="…"` attribute — and, through
    /// `filter isAlpha` (Sapic/Facts.hs:401#stripNonAlphanumerical), into the
    /// derived rule name.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `in('c', x); [ St(x)[+] ] --[ Ev(x)[no_precomp] ]-> [ Out(x) ]`:
    ///   `rule (modulo E) StxEvxnoprecompOutx_0_1[…, process=" [ St( x.2 )[+] ] --[ Ev( x.2 )[no_precomp] ]-> [ Out( x.2 ) ];", …]`
    #[test]
    fn msr_facts_carry_their_annotations() {
        use crate::fact::{Fact, FactAnnotation, FactTag, Multiplicity};

        let x: SapicTerm = VTerm::Lit(Lit::Var(sv("x", 2, None)));
        let annotated = |name: &'static str, a: FactAnnotation| {
            Fact::new(
                FactTag::Proto(Multiplicity::Linear, name, 1),
                vec![x.clone()],
            )
            .annotate(a)
        };
        let proc: PlainProcess = Process::Action(
            SapicAction::Msr {
                prems: vec![annotated("St", FactAnnotation::SolveFirst)],
                acts: vec![annotated("Ev", FactAnnotation::NoSources)],
                concs: vec![Fact::new(FactTag::Out, vec![x])],
                rest: Vec::new(),
                match_vars: std::collections::BTreeSet::new(),
            },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        let got = pretty_sapic_top_level(&proc);
        assert_eq!(
            got,
            " [ St( x.2 )[+] ] --[ Ev( x.2 )[no_precomp] ]-> [ Out( x.2 ) ];"
        );
        let name: String = got.chars().filter(|c| c.is_alphabetic()).collect();
        assert_eq!(name, "StxEvxnoprecompOutx");
    }

    /// The restriction item is the Doc composition `_restrict(` <> formula <>
    /// `)`, so a break the formula takes indents by the ten columns of the
    /// opening operator and the whole item lays out inside the rule.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1` +
    /// `in(<xxxxxxxxxx, yyyyyyyyyy, zzzzzzzzzz>); [ ] --[ Ev(xxxxxxxxxx), _restrict( aaaaaaaaaa(xxxxxxxxxx) = bbbbbbbbbb(yyyyyyyyyy) & cccccccccc(zzzzzzzzzz) = aaaaaaaaaa(yyyyyyyyyy) ) ]-> [ ]; out('a')`
    /// (fixture `sapic_msr_restrict_wrap`).
    #[test]
    fn msr_restrict_wraps_under_the_restrict_paren() {
        let got = msr_render(
            "xxxxxxxxxx.1",
            "aaaaaaaaaa(xxxxxxxxxx.1) = bbbbbbbbbb(yyyyyyyyyy.1) \
             & cccccccccc(zzzzzzzzzz.1) = aaaaaaaaaa(yyyyyyyyyy.1)",
            "functions: aaaaaaaaaa/1, bbbbbbbbbb/1, cccccccccc/1",
        );
        assert_eq!(
            got,
            " [ ]\n\
             --[\n\
             Ev( xxxxxxxxxx.1 ),\n\
             _restrict((aaaaaaaaaa(xxxxxxxxxx.1) = bbbbbbbbbb(yyyyyyyyyy.1)) \u{2227}\n\
             \x20         (cccccccccc(zzzzzzzzzz.1) = aaaaaaaaaa(yyyyyyyyyy.1)))\n\
             ]->\n\
             \x20[ ];"
        );
        // The derived rule name is `filter isAlpha` over the same string
        // (Sapic/Facts.hs:401#stripNonAlphanumerical), so the breaks leave it
        // untouched.
        let name: String = got.chars().filter(|c| c.is_alphabetic()).collect();
        assert_eq!(
            name,
            "Evxxxxxxxxxxrestrictaaaaaaaaaaxxxxxxxxxxbbbbbbbbbbyyyyyyyyyycccccccccczzzzzzzzzzaaaaaaaaaayyyyyyyyyy"
        );
    }

    /// The `process="..."` rule attribute and the `process:` block are plain
    /// text inside the page's `Doc`: an interactive-server page render holds
    /// an [`hpj::HtmlDocGuard`], and the process text must still reach that
    /// `Doc` unescaped and measured at its visible width, so the page escapes
    /// each metacharacter exactly once.
    #[test]
    fn top_level_attr_is_plain_text_under_html_mode() {
        use tamarin_term::function_symbols::pair_sym;
        use tamarin_term::lterm::{Name, NameTag};
        let msg = f_app_no_eq(
            pair_sym(),
            vec![
                VTerm::Lit(Lit::Con(Name::new(NameTag::Pub, "p"))),
                VTerm::Lit(Lit::Var(sv("x", 1, None))),
            ],
        );
        let p: PlainProcess = Process::Action(
            SapicAction::ChOut { chan: None, msg },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        let _html = hpj::HtmlDocGuard::enable();
        let attr = pretty_sapic_top_level_attr(&p);
        assert_eq!(attr, "out(<'p', x.1>);");
        assert_eq!(
            Doc::text(format!("process=\"{attr}\"")).render_with(200, 200),
            "process=&quot;out(&lt;&#39;p&#39;, x.1&gt;);&quot;"
        );
    }
}
