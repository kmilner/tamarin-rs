// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HughesPJ layout of the wellformedness report's paragraph fills.
//!
//! HS builds every such body as ONE `Doc` and lets the layout engine break it:
//! `text info $-$ nest 2 (fsep $ punctuate comma cells)` — `unboundCheck`
//! (Wellformedness.hs:497-498), `reservedFactNameRules'`
//! (Wellformedness.hs:546) and `specialFactsUsage'` (Wellformedness.hs:563),
//! whose cells are `prettyLNFact` (Theory/Model/Fact.hs:567-574) or
//! `prettyLVar`
//! (`prettyVarList`, TheoryObject.hs:858-859) documents.  So a cell that
//! overruns the ribbon does not merely get a line of its own: it breaks at its
//! OWN `sep`/`fsep`/`fcat` points, dropping `prettyLNFact`'s closing `)` onto
//! the next line and refilling the argument list at the `nestShort'` indent
//! (Text/PrettyPrint/Class.hs:218-223).
//!
//! The checks themselves live in `tamarin-parser`, which cannot reach this
//! engine, so they carry their cells over as
//! [`WfDoc`](tamarin_parser::wf::WfDoc) skeletons in
//! [`WfError::fill`](tamarin_parser::wf::WfError::fill) and this module lays
//! the body out.
//!
//! Width: the report is baked into the theory by `addComment`, which renders
//! with HughesPJ's DEFAULT style — `lineLength = 100`, `ribbonsPerLine = 1.5`,
//! so `ribbonLen = round (100 / 1.5) = 67` (TheoryObject.hs:717-718) — not the
//! console's 110/73.  See [`crate::mult_restricted`], which renders its own
//! entry bodies at the same width for the same reason.

use tamarin_parser::wf::{WfDoc, WfFill};

use crate::pretty_hpj::{self as hpj, Doc};

/// `lineLength` of the style HughesPJ's `render` uses, reached from HS through
/// `addComment`'s `render` (TheoryObject.hs:717-718).
const WF_LINE_LENGTH: usize = 100;
/// `ribbonLen = round (100 / 1.5) = 67` for [`WF_LINE_LENGTH`].
const WF_RIBBON: usize = 67;

/// Lay out one filled body — HS `text info $-$ nest 2 (fsep $ punctuate comma
/// cells)` inside the `nest 2` `prettyWfErrorReport` wraps every body of a
/// topic group in (Wellformedness.hs:118-125).
///
/// The result is the entry's complete headerless body, with no trailing
/// newline: what [`WfError::message`](tamarin_parser::wf::WfError::message)
/// holds for the checks that need no layout engine.
pub fn fill_body(fill: &WfFill) -> String {
    // HS builds the report as a plain `Doc`: `prettyWfErrorReport`'s text
    // never passes through the escaping `Document (HtmlDoc d)` instance
    // (Html.hs:102-105), so a pair term inside a fact keeps its raw `<`/`>`
    // on the web routes too — which render this under an active
    // `HtmlDocGuard`.
    let _plain = hpj::HtmlDocGuard::disable();
    match fill {
        WfFill::Paragraph { info, cells } => {
            let cells: Vec<Doc> = cells.iter().map(cell_doc).collect();
            // HS `fsep $ punctuate comma cells` with `comma = char ','`
            // (Text/PrettyPrint/Class.hs:121).
            let list = hpj::fsep(hpj::punctuate(Doc::char(','), cells));
            // `above_g` is HughesPJ's `$+$`, which HS's `$-$` maps to
            // (Text/PrettyPrint/Class.hs:180); `info` is a single `text` (its
            // `<->` join cannot break), so it keeps its trailing spaces on the
            // line above the fill.
            Doc::text(info)
                .above_g(list.nest(2))
                .nest(2)
                .render_with(WF_LINE_LENGTH, WF_RIBBON)
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
