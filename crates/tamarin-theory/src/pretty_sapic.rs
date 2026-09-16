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

/// The action/combinator text consumed by the reparsable open-process
/// printer. Unlike [`pretty_sapic_top_level`], actions carry no sequencing
/// semicolon because that printer decides whether a continuation needs one.
pub(crate) fn pretty_sapic_open_node(p: &PlainProcess) -> String {
    let _plain = hpj::HtmlDocGuard::disable();
    match p {
        Process::Null(_) => "0".to_string(),
        Process::Comb(c, _, _, _) => pretty_sapic_comb(c),
        Process::Action(a, _, _) => pretty_sapic_action(a, MsrPrinter::Sapic),
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
#[path = "pretty_sapic_tests.rs"]
mod tests;
