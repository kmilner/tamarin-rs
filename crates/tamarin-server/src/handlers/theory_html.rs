// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, arcz, cascremers, felixlinker, beschmi, rsasse, jdreier,
//   BTom-GH, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term/Raw.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/utils/src/Text/PrettyPrint/Html.hs, src/Web/Hamlet.hs,
//   src/Web/Handler.hs, src/Web/Theory.hs, src/Web/Types.hs

//! HTML rendering for theory pages.
//!
//! This mirrors a *minimal* slice of Haskell's `Web.Theory` + `Web.Hamlet`
//! pretty printing — enough to surface the lemmas, restrictions and
//! rules in the UI, and to wire `Autoprove` links the frontend
//! recognises.

use crate::handlers::path_parse::{encode_sub_path, url_path_escape, SourceKind, TheoryPath};
use crate::handlers::root::html_escape;
use crate::state::TheoryEntry;

use tamarin_theory::constraint::solver::proof_method::{ProofMethod, Result as MethodResult};
use tamarin_theory::constraint::solver::search::{proof_status, ProofNode, ProofStatus};
use tamarin_theory::theory::{LemmaAttr, TraceQuantifier};

/// Full overview/framing page (the one served at `/thy/trace/<idx>/overview/...`).
pub fn overview_page(entry: &TheoryEntry, path: &TheoryPath) -> String {
    let header_html = header(entry);
    let proof_state = proof_state(entry);
    let main_view = path_html(entry, path);
    // Byte-faithful port of HS `defaultLayout'` (Web/Types.hs:686-723)
    // wrapping `overviewTpl` (Web/Hamlet.hs:290-317): a `$newline never`
    // single-line frame (the only embedded newlines come from the
    // postprocessed `{proof_state}` west pane and the `{main_view}` centre
    // pane).  Verbatim hamlet quirks: unquoted URL attrs, doubled
    // `</script></script>` close tags, class-before-id attribute ordering,
    // the ` </div></div></div>` pane closers and the doubled `</a>` in the
    // context menu.  Volatile substitutions: `{name}` (title), and — inside
    // `{header}` — the `{version}` field.
    format!(
        r##"<!DOCTYPE html>
<html><head><title>Theory: {name}</title><link rel="stylesheet" href="/static/css/intdot-style.css"><link rel="stylesheet" href="/static/css/tamarin-prover-ui.css"><link rel="stylesheet" href="/static/css/jquery-contextmenu.css"><link rel="stylesheet" href="/static/css/smoothness/jquery-ui.css"><script src="/static/js/jquery.js"></script></script><script src="/static/js/jquery-ui.js"></script></script><script src="/static/js/jquery-layout.js"></script></script><script src="/static/js/jquery-cookie.js"></script></script><script src="/static/js/jquery-superfish.js"></script></script><script src="/static/js/jquery-contextmenu.js"></script></script><script src="/static/js/tamarin-prover-ui.js"></script></script><script type="module" src="/static/js/intdot-graph.es.js"></script></script><script type="module" src="/static/js/intdot-staticgraph.es.js"></script></script><script type="module" src="/static/js/intdot-dynamicgraph.es.js"></script></script></head><body><p class="loading">Analyzing, please wait...  <a id=cancel href='#'>Cancel</a></p><div class="ui-layout-north">{header}</div><div class="ui-layout-west"><h1 class="pane-head">Proof scripts</h1><div class="scroll-wrapper" id="proof-wrapper"><div class="monospace" id="proof">{proof_state} </div></div></div><div class="ui-layout-east"><h1 class="pane-head">&nbsp;Debug information</h1><div class="scroll-wrapper" id="debug-wrapper"><div id="ui-debug-display"></div></div></div><div class="ui-layout-center"><h1 class="pane-head" id="main-title">Visualization display</h1><div class="scroll-wrapper" id="main-wrapper" tabindex="0"><div id="ui-main-display">{main_view} </div></div></div><div id="dialog"></div><div id="confirm-dialog"></div><ul id="contextMenu"><li class="autoprove"><a href="#autoprove">Autoprove</a></a></li></ul></body></html>"##,
        name = html_escape(&entry.name),
        header = header_html,
        proof_state = proof_state,
        main_view = main_view,
    )
}

fn header(entry: &TheoryEntry) -> String {
    // Byte-faithful port of HS `headerTpl` (Web/Hamlet.hs:166-198): the
    // Reload-file and Append-modified-lemmas `<li>`s are gated on
    // `isLocalOrigin origin`.  Attributes are rendered exactly as hamlet
    // writes them: `@{RootR}` URL interpolations are unquoted (`href=/`,
    // `target=_blank`, `href=/thy/...`), the `#id`/`.class` shorthands are
    // quoted (`id="header-info"`), and literal `id=abbrv-toggle` attrs stay
    // unquoted.  No "(Rust port)" suffix — HS renders `Running … Tamarin … 1.13.0`.
    let is_local = matches!(entry.origin, crate::state::TheoryOrigin::Local(_));
    let idx = entry.idx;
    let filename = html_escape(&format!("{}.spthy", entry.name));
    let reload_form = if is_local {
        format!(
            "<li><form class=\"ajax-form ajax-form-full reload-confirm\" method=\"POST\" action=\"/thy/trace/{idx}/reload\"><button class=\"nav-button\" type=\"submit\">Reload file</button></form></li>")
    } else {
        String::new()
    };
    let append_form = if is_local {
        format!(
            "<li><form class=\"ajax-form\" method=\"POST\" action=\"/thy/trace/{idx}/get_and_append/{filename}\"><button class=\"link-button\" type=\"submit\">Append modified lemmas to file</button></form></li>")
    } else {
        String::new()
    };
    format!(
        "<div class=\"layout-pane-north\"><div id=\"header-info\">Running <a href=/><span class=\"tamarin\">Tamarin</span></a> {version}</div></div>\
<div id=\"header-links\"><ul id=\"navigation\">\
<li><a href=/>Index</a></li>\
{reload_form}\
<li><a href=\"#\">Actions</a><ul>\
<li><a target=_blank href=/thy/trace/{idx}/source>Show source</a></li>\
<li><a href=/thy/trace/{idx}/download/{filename}>Download source</a></li>\
{append_form}\
</ul></li>\
<li><a href=\"#\">Options</a><ul class=\"list-with-toggles\">\
<li><a id=abbrv-toggle href=\"#\">Abbreviate terms</a></li>\
<li><a id=agent-toggle href=\"#\">Clustering by role</a></li>\
<li><a id=auto-toggle href=\"#\">Show annotation auto-sources</a></li>\
<li><a id=lvl0-toggle href=\"#\">Graph simplification off</a></li>\
<li><a id=lvl1-toggle href=\"#\">Graph simplification L1</a></li>\
<li><a id=lvl2-toggle href=\"#\">Graph simplification L2</a></li>\
<li><a id=lvl3-toggle href=\"#\">Graph simplification L3</a></li>\
</ul></li></ul></div>",
        version = env!("CARGO_PKG_VERSION"),
        idx = idx,
        filename = filename,
        reload_form = reload_form,
        append_form = append_form,
    )
}

/// Left-pane proof-state tree.  Faithful port of Haskell's `theoryIndex`
/// (`src/Web/Theory.hs:369-416`) → `lemmaIndex` (`src/Web/Theory.hs:296-329`)
/// → `proofIndex` (`src/Web/Theory.hs:223-257`) → `prettyProofWith`
/// (`Theory/Proof.hs:1078-1096`).  The frame is
///
/// ```text
/// theory <help-link>Name</help-link> begin
/// <Message theory>  <Multiset rewriting rules … (N)>  <Tactic(s)>
/// <Raw sources (N cases, …)>  <Refined sources (N cases, …)>
/// add lemma
/// <lemma_1 index>  …  <lemma_k index>
/// end
/// ```
///
/// Blank-line separators (`text ""`) are emitted as `<br>` and collapsed by
/// the parity normalizer; only element structure / link targets / visible
/// text are compared.
fn proof_state(entry: &TheoryEntry) -> String {
    use tamarin_theory::pretty_hpj::{self as hpj, postprocess_html, HtmlDocGuard};
    let typed = &entry.typed_theory;
    let idx = entry.idx;
    // HS renders the whole `theoryIndex` through the `HtmlDoc Doc` transformer
    // + `renderHtmlDoc`: every keyword is an `hl_keyword` span, every formula
    // operator an `hl_operator` span, text is entity-escaped and the result is
    // postprocessed once (leading spaces → `&nbsp;`, each line → `<br/>`).
    // Build the `foldr1 ($-$)` element list (Web/Theory.hs:372-392) as a
    // `\n`-separated string under the guard, then postprocess.
    let _html = HtmlDocGuard::enable();
    let kw = |s: &str| hpj::keyword_(s).render();
    // Elements of `theoryIndex`, each an entry in the top-level `foldr1 ($-$)`.
    // `text ""` blanks are rendered as empty entries (postprocess emits `<br/>`).
    let mut elems: Vec<String> = Vec::new();
    // `kwTheoryHeader $ linkToPath … ["help"] (text name)` =
    // `keyword_ "theory" <-> <a class="internal-link help" …>NAME</a> <-> keyword_ "begin"`.
    elems.push(format!(
        "{theory} <a class=\"internal-link help\" href=\"/thy/trace/{idx}/main/help\">{name}</a> {begin}",
        theory = kw("theory"), begin = kw("begin"),
        idx = idx, name = html_escape(&entry.name)));
    elems.push(String::new());
    // `overview n info p = linkToPath … [] (bold n <-> info)`; `bold = withTag
    // "strong" [] . text`.  Message / Tactic pass `text ""` as info (a trailing
    // space); rules / sources pass their `(N …)` annotation.
    elems.push(format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/message\"><strong>Message theory</strong> </a>",
        idx = idx));
    elems.push(String::new());
    // `ruleLinkMsg = "Multiset rewriting rules" ++ (if null restrictions then ""
    // else " and restrictions")`; `rulesInfo = parens (length crProtocol)`.
    let has_restr = typed.restrictions().next().is_some();
    let rule_msg = if has_restr {
        "Multiset rewriting rules and restrictions"
    } else {
        "Multiset rewriting rules"
    };
    elems.push(format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/rules\"><strong>{msg}</strong> ({n})</a>",
        idx = idx, msg = html_escape(rule_msg), n = proto_rule_count(entry)));
    elems.push(String::new());
    elems.push(format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/tactic\"><strong>Tactic(s)</strong> </a>",
        idx = idx));
    elems.push(String::new());
    // `reqCasesLink name k = overview name (casesInfo k) (TheorySource k 0 0)`.
    // Note HS's "Refined sources " carries a trailing space inside `bold`.
    let (raw_n, raw_ch) = source_case_counts(entry, false);
    elems.push(format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/cases/raw/0/0\"><strong>Raw sources</strong> {info}</a>",
        idx = idx, info = html_escape(&cases_info(raw_n, raw_ch))));
    elems.push(String::new());
    let (ref_n, ref_ch) = source_case_counts(entry, true);
    elems.push(format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/cases/refined/0/0\"><strong>Refined sources </strong> {info}</a>",
        idx = idx, info = html_escape(&cases_info(ref_n, ref_ch))));
    elems.push(String::new());
    // `add lemma` for the very first slot (`TheoryAdd "<first>"`).
    elems.push(format!(
        "<a class=\"internal-link add\" href=\"/thy/trace/{idx}/main/add/%3Cfirst%3E\">add lemma</a>",
        idx = idx));
    elems.push(String::new());
    // `vcat $ intersperse (text "") lemmas` — one multi-line block per lemma,
    // blank line between blocks.
    let mut lemma_blocks: Vec<String> = Vec::new();
    for l in typed.lemmas() {
        let mut block = String::new();
        lemma_index(&mut block, entry, l);
        lemma_blocks.push(block);
    }
    elems.push(lemma_blocks.join("\n\n"));
    elems.push(String::new());
    // `kwEnd`.
    elems.push(kw("end"));
    // `foldr1 ($-$)` = join by newline; then postprocess once.
    postprocess_html(&elems.join("\n"))
}

/// HS `length (getClassifiedRules thy)._crProtocol` — the count shown in the
/// `Multiset rewriting rules … (N)` link.  Equal to the number of rules the
/// `main/rules` page renders (`extraACRules ++ protoRules`), i.e.
/// `web_proto_rules.len()` plus the ISend/IRecv-style intruder members of
/// `crProtocol` (`ctx.intruder_rules` minus construction/destruction rules).
fn proto_rule_count(entry: &TheoryEntry) -> usize {
    let proto =
        tamarin_theory::pretty_theory::web_proto_rules(&entry.parser_theory, &entry.typed_theory)
            .len();
    let extra = entry.proof_state.as_ref().map_or(0, |ps| {
        let ctx = ps.ctx.lock();
        ctx.intruder_rules
            .iter()
            .filter(|ir| !is_constr_intr(&ir.info) && !is_destr_intr(&ir.info))
            .count()
    });
    proto + extra
}

/// HS `casesInfo` rendering: `(N cases, deconstructions complete)` or
/// `(N cases, K partial deconstructions left)`.
fn cases_info(n_cases: usize, n_chains: usize) -> String {
    let chain_info = if n_chains == 0 {
        "deconstructions complete".to_string()
    } else {
        format!("{} partial deconstructions left", n_chains)
    };
    format!("({} cases, {})", n_cases, chain_info)
}

/// HS `lemmaIndex` (`src/Web/Theory.hs:296-329`): the lemma header
/// (`lemma Name [attrs]: <tq> "<formula>"`), the `edit lemma`/`delete lemma`
/// links, the `proofIndex` tree, then a trailing `add lemma`.  The header +
/// edit/delete are wrapped by HS in `markStatus (root color)` — a `hl_*` span
/// the normalizer unwraps, so we emit them plain.
fn lemma_index(
    out: &mut String,
    entry: &TheoryEntry,
    l: &tamarin_theory::theory::Lemma<tamarin_theory::theory::ProofSkeleton>,
) {
    let idx = entry.idx;
    let tq = match l.trace_quantifier {
        TraceQuantifier::AllTraces => "all-traces",
        TraceQuantifier::ExistsTrace => "exists-trace",
    };
    let attrs = render_attrs(&l.attributes, &entry.typed_theory.in_file);
    // HS renders the quantifier + formula as `nest 2 (sep [tq, doubleQuotes
    // (prettyLNFormula f)])` (Web/Theory.hs:301-306) through the
    // HtmlDoc/HughesPJ engine: (1) AC argument lists (`++`/`*`/xor) are
    // stored AC-canonically (fAppAC flatten+sort, Term/Raw.hs:117-129);
    // (2) layout runs at the web width 100/67 (renderHtmlDoc,
    // Text/PrettyPrint/Html.hs:151-153); (3) fill widths are measured on
    // entity-ESCAPED text (Html.hs:102-105).  `pretty_formula` alone kept
    // source operand order and never wrapped, so `++`-operand order and
    // the fcat break-spaces inside tuples/AC chains diverged (the alethea
    // overview family).
    let canon = tamarin_theory::elaborate::canonicalize_ac_in_formula(&l.formula);
    // `nest 2 (sep [prettyTraceQuantifier tq, doubleQuotes (prettyLNFormula f)])`
    // — rendered under the active `HtmlDocGuard` (proof_state's), so operators
    // become `hl_operator` spans and the formula text is entity-escaped, while
    // the line-wrapping still measures escaped fill-widths at WEB_LINE_LENGTH/
    // WEB_RIBBON (the widths lib.rs installs) exactly as HS `renderHtmlDoc`.
    let formula_hdr = tamarin_theory::pretty_formula::lemma_header_line(tq, &canon);
    let n_url = url_path_escape(&l.name);
    use tamarin_theory::pretty_hpj as hpj;
    // HS `lemmaIndex` (Web/Theory.hs:301-321), a single Doc joined by `$-$`
    // (newline).  For a freshly-loaded (Unmarked) lemma `markStatus` is the
    // identity, so no wrapping colour span:
    //   kwLemma <-> prettyLemmaName l <> colon           -- "lemma NAME:"
    //   $-$ nest 2 (sep [tq, doubleQuotes formula])      -- the tq + formula
    //   $-$ (editLink <-> " or " <-> deleteLink)         -- note TWO spaces
    //   $-$ proofIndex $-$ text "" $-$ addLink
    // `bold`/name text is entity-escaped; `<->` contributes a single space, so
    // `editLink <-> " or " <-> deleteLink` renders `…edit</a>  or  <a…` (two
    // spaces around "or").
    out.push_str(&format!(
        "{lemma} {name}{attrs}:\n",
        lemma = hpj::keyword_("lemma").render(),
        name = html_escape(&l.name),
        attrs = html_escape(&attrs)
    ));
    out.push_str(&formula_hdr);
    out.push('\n');
    out.push_str(&format!(
        "<a class=\"internal-link edit\" href=\"/thy/trace/{idx}/main/edit/{n_url}\">edit lemma</a>  or  \
         <a class=\"internal-link delete\" href=\"/thy/trace/{idx}/main/delete/{n_url}\">delete lemma</a>\n",
        idx = idx, n_url = n_url));
    // `proofIndex l._lName tidx renderUrl mkRoute annPrf` — the annotated
    // proof tree, rendered by `prettyProofWith ppStep ppCase . insertPaths`.
    let live_root = entry
        .proof_state
        .as_ref()
        .and_then(|ps| ps.get_root(&l.name));
    match live_root {
        Some(root) => {
            let cx = PpCtx {
                idx,
                lemma: &l.name,
                tq: l.trace_quantifier,
            };
            let path: Vec<String> = Vec::new();
            pp_prf(out, &cx, &path, &root, 0);
        }
        None => {
            // No live proof state yet (lazily built): the lemma's root is a
            // fresh `Sorry Nothing`.  HS `proofIndex` of such a proof is
            // `ppCases (Sorry) [] = kwBy <> " " <> stepLink ["sorry-step"]`
            // (an `Unmarked`, unannotated-free `Sorry` step gets no
            // `remove-step`); the method text is `keyword_ "sorry"`.
            out.push_str(&format!(
                "{by} <a class=\"internal-link proof-step sorry-step\" \
                 href=\"/thy/trace/{idx}/main/proof/{n_url}\">{sorry}</a>",
                by = hpj::keyword_("by").render(),
                sorry = hpj::keyword_("sorry").render(),
                idx = idx,
                n_url = n_url
            ));
        }
    }
    // `$-$ text "" $-$ addLink`.
    out.push_str("\n\n");
    out.push_str(&format!(
        "<a class=\"internal-link add\" href=\"/thy/trace/{idx}/main/add/{n_url}\">add lemma</a>",
        idx = idx,
        n_url = n_url
    ));
}

/// Addressing context threaded through the `proofIndex` recursion.
struct PpCtx<'a> {
    idx: usize,
    lemma: &'a str,
    tq: TraceQuantifier,
}

/// HS `ProofStepColor` after `annotateLemmaProof` — the per-step highlight.
#[derive(Clone, Copy, PartialEq)]
enum StepColor {
    Unmarked,
    Green,
    Red,
    Yellow,
}

/// HS `annotateLemmaProof.interpret` (`src/Web/Theory.hs:2183-2192`): map the
/// aggregate subtree [`ProofStatus`] + trace quantifier to a highlight colour.
fn interpret_color(tq: TraceQuantifier, status: ProofStatus) -> StepColor {
    use ProofStatus::*;
    match status {
        Incomplete | Undetermined => StepColor::Unmarked,
        Unfinishable | Invalidated => StepColor::Yellow,
        TraceFound => match tq {
            TraceQuantifier::AllTraces => StepColor::Red,
            TraceQuantifier::ExistsTrace => StepColor::Green,
        },
        Complete => match tq {
            TraceQuantifier::AllTraces => StepColor::Green,
            TraceQuantifier::ExistsTrace => StepColor::Red,
        },
    }
}

/// HS `markStatus (fst psInfo)` (`src/Web/Theory.hs:2170-2175`): the span
/// `prettyCase` wraps each structural keyword (`by`/`next`/`qed`/`case <name>`)
/// in, keyed on the node's `(Maybe System, ProofStepColor)`:
///   (Nothing, _)       -> hl_superfluous   (unannotated / replayed verbatim)
///   (Just _, Green)    -> hl_good
///   (Just _, Red)      -> hl_bad
///   (Just _, Yellow)   -> hl_medium
///   (Just _, Unmarked) -> id               (no wrapping span)
/// Returns the (open, close) tag pair; `("","")` for the identity case.
fn mark_wrap(cx: &PpCtx, node: &ProofNode) -> (&'static str, &'static str) {
    if !node.annotated {
        return ("<span class=\"hl_superfluous\">", "</span>");
    }
    match interpret_color(cx.tq, proof_status(node)) {
        StepColor::Unmarked => ("", ""),
        StepColor::Green => ("<span class=\"hl_good\">", "</span>"),
        StepColor::Red => ("<span class=\"hl_bad\">", "</span>"),
        StepColor::Yellow => ("<span class=\"hl_medium\">", "</span>"),
    }
}

/// HS `prettyProofWith.ppPrf` / `ppCases` (`Theory/Proof.hs:1080-1096`):
/// dispatch on the node's children shape.  `depth` counts the named-case
/// `nest 2` levels the subtree sits under (HS `ppCase`), which shifts the
/// method text's wrap budget — see `pp_step`.
fn pp_prf(out: &mut String, cx: &PpCtx, path: &[String], node: &ProofNode, depth: usize) {
    use tamarin_theory::pretty_hpj as hpj;
    // Nest indent for `next`/`qed` at this level (HS `nest 2` per named case).
    let ind = "  ".repeat(depth);
    let children = &node.children;
    if children.is_empty() {
        // `ppCases ps@(Finished Solved) [] = prettyStep ps` (SOLVED leaf,
        // no `by`); every other leaf is `prettyCase ps (kwBy<>" ") <> step`.
        let by = !matches!(node.method, ProofMethod::Finished(MethodResult::Solved));
        pp_step(out, cx, path, node, depth, by);
    } else if children.len() == 1 && children.contains_key("") {
        // `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf` — single
        // unnamed continuation, no `case` label (same nest level).
        pp_step(out, cx, path, node, depth, false);
        out.push('\n');
        let mut child_path = path.to_vec();
        child_path.push(String::new());
        pp_prf(out, cx, &child_path, &children[""], depth);
    } else {
        // `ppCases ps cases = prettyStep ps $-$
        //    (vcat $ intersperse (prettyCase ps kwNext) $ map ppCase cases)
        //    $-$ prettyCase ps kwQED`.  `next`/`qed` sit at THIS nest level;
        // each case body is one `nest 2` deeper (see `pp_case`).
        pp_step(out, cx, path, node, depth, false);
        // `prettyCase ps kwNext` / `prettyCase ps kwQED` wrap the keyword in
        // `markStatus ps` (this node's colour span).
        let (mo, mc) = mark_wrap(cx, node);
        for (i, (name, child)) in children.iter().enumerate() {
            out.push('\n');
            if i > 0 {
                out.push_str(&format!(
                    "{}{}{}{}\n",
                    ind,
                    mo,
                    hpj::keyword_("next").render(),
                    mc
                ));
            }
            pp_case(out, cx, path, name, child, depth);
        }
        out.push('\n');
        out.push_str(&format!(
            "{}{}{}{}",
            ind,
            mo,
            hpj::keyword_("qed").render(),
            mc
        ));
    }
}

/// HS `prettyProofWith.ppCase` (`Theory/Proof.hs:1094-1096`):
/// `nest 2 $ (prettyCase (root prf) (kwCase <-> name)) $-$ ppPrf prf`.  The
/// `case <name>` keyword is wrapped by HS in `markStatus`, a `hl_*` span the
/// normalizer unwraps, so we emit it plain.  Each named case adds one
/// `nest 2` level for the whole subtree.
fn pp_case(
    out: &mut String,
    cx: &PpCtx,
    path: &[String],
    name: &str,
    child: &ProofNode,
    depth: usize,
) {
    use tamarin_theory::pretty_hpj as hpj;
    // `nest 2 $ (kwCase <-> name) $-$ ppPrf prf` — the case header and its whole
    // subtree sit one `nest 2` deeper than this node.  `kwCase` is an
    // `hl_keyword` span; the case name is entity-escaped.
    let ind = "  ".repeat(depth + 1);
    // `prettyCase (root prf) (kwCase <-> name)` wraps the case header in
    // `markStatus (root prf)` — the CHILD node's colour span.
    let (mo, mc) = mark_wrap(cx, child);
    out.push_str(&format!(
        "{}{}{} {}{}\n",
        ind,
        mo,
        hpj::keyword_("case").render(),
        html_escape(name),
        mc
    ));
    let mut child_path = path.to_vec();
    child_path.push(name.to_string());
    pp_prf(out, cx, &child_path, child, depth + 1);
}

/// HS `proofIndex.ppStep` (`src/Web/Theory.hs:232-257`): a coloured
/// `proof-step` link carrying the pretty method, plus (unless the method is
/// `Sorry`) an empty `remove-step` link at the same path.  An unannotated
/// step (HS `psInfo == Nothing`) renders as a plain `hl_superfluous` span
/// instead of the proof-step link — but the `remove-step` link is appended
/// OUTSIDE that case split (`<>`, Web/Theory.hs:242-244), so it is emitted
/// for unannotated non-`Sorry` steps too.
///
/// The method text is `prettyProofMethod` laid out INSIDE the tree Doc
/// (`prettyProofWith`) by HS: at `nest (2*depth)` (one `nest 2` per named
/// case), with the leaf's `by ` prefix beside it, at the HtmlDoc width
/// (100/67, entity fill-widths).  Reproduce that layout exactly by
/// rendering `nest (2·depth) ("by "? <> method)` under the entity guard,
/// then stripping the indent/`by ` back off the first line (the `<a>`
/// wraps only the method text; continuation-line whitespace is
/// canonicalized by the gate, break positions are what must match).
fn pp_step(
    out: &mut String,
    cx: &PpCtx,
    path: &[String],
    node: &ProofNode,
    depth: usize,
    by_prefix: bool,
) {
    use tamarin_theory::pretty_hpj::{self as hpj, Doc, WEB_LINE_LENGTH, WEB_RIBBON};
    // Render `("by "? <> prettyProofMethod)` at `nest (2*depth)` under the
    // ACTIVE `HtmlDocGuard` (proof_state's), so the method carries its `hl_*`
    // spans and the wrap budget accounts for the `by ` offset exactly as HS.
    // The `by ` is a plain `Doc::text` here purely to size the budget; it is
    // stripped back off and re-emitted as `keyword_ "by"` OUTSIDE the link.
    let rendered = {
        let mut doc = tamarin_theory::pretty_theory::pretty_proof_method_doc(&node.method);
        if by_prefix {
            doc = Doc::text("by ").beside(doc);
        }
        doc.nest((2 * depth) as isize)
            .render_with(WEB_LINE_LENGTH, WEB_RIBBON)
    };
    // Strip the first line's nest indent (and the sizing `by `) so the `<a>`
    // wraps only the method text; continuation lines keep their absolute
    // indentation (→ `&nbsp;` via postprocess).  The stripped text ALREADY
    // carries `hl_*` spans — do NOT entity-escape it again.
    let mut label: &str = rendered.trim_start_matches(' ');
    if by_prefix {
        label = label.strip_prefix("by ").unwrap_or(label);
    }
    // Leading indent for this line (HS `nest 2` per named case).  The `by `
    // prefix is HS `prettyCase ps (kwBy <> text " ")` = `markStatus ps` wrapping
    // `keyword_ "by"` PLUS its trailing space (Theory/Proof.hs:1080-1101, see line 1084).
    let ind = "  ".repeat(depth);
    out.push_str(&ind);
    if by_prefix {
        let (mo, mc) = mark_wrap(cx, node);
        out.push_str(&format!("{}{} {}", mo, hpj::keyword_("by").render(), mc));
    }
    let url = format!(
        "/thy/trace/{idx}/main/proof/{lemma}{path}",
        idx = cx.idx,
        lemma = url_path_escape(cx.lemma),
        path = encode_sub_path(path)
    );
    if !node.annotated {
        // `superfluousStep = withTag "span" [("class","hl_superfluous")] ppMethod`.
        // HS appends `removeStep` regardless of the annotation branch
        // (Web/Theory.hs:242-244) — only a `Sorry` method skips it.  Seen on
        // noise secrecy_4_passiveINpsk1_proof.spthy: the kept-verbatim
        // (unannotated) subtrees under drifted nested split_case steps carry
        // one empty remove-step anchor per node in HS's /overview/help.
        out.push_str(&format!("<span class=\"hl_superfluous\">{}</span>", label));
        if !matches!(node.method, ProofMethod::Sorry(_)) {
            out.push_str(&format!(
                "<a class=\"internal-link remove-step\" href=\"{url}\"></a>",
                url = url
            ));
        }
        return;
    }
    let color = interpret_color(cx.tq, proof_status(node));
    let cls = match color {
        StepColor::Unmarked => "sorry-step",
        StepColor::Green => "hl_good",
        StepColor::Red => "hl_bad",
        StepColor::Yellow => "hl_medium",
    };
    out.push_str(&format!(
        "<a class=\"internal-link proof-step {cls}\" href=\"{url}\">{label}</a>",
        cls = cls,
        url = url,
        label = label
    ));
    // `invalidatedStep`: an `Invalidated` step also gets a `verify it` link.
    if color == StepColor::Yellow && matches!(node.method, ProofMethod::Invalidated) {
        out.push_str(&format!(
            " <a class=\"internal-link hl_medium\" href=\"/thy/trace/{idx}/verify/proof/{lemma}\">verify it</a>",
            idx = cx.idx, lemma = url_path_escape(cx.lemma)));
    }
    // `<> case psMethod step of Sorry _ -> emptyDoc; _ -> removeStep`.
    if !matches!(node.method, ProofMethod::Sorry(_)) {
        out.push_str(&format!(
            "<a class=\"internal-link remove-step\" href=\"{url}\"></a>",
            url = url
        ));
    }
}

fn render_attrs(attrs: &[LemmaAttr], in_file: &str) -> String {
    if attrs.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = attrs
        .iter()
        .map(|a| match a {
            LemmaAttr::Sources => "sources".into(),
            LemmaAttr::Reuse => "reuse".into(),
            LemmaAttr::DiffReuse => "diff_reuse".into(),
            LemmaAttr::UseInduction => "use_induction".into(),
            LemmaAttr::HideLemma(s) => format!("hide_lemma={}", s),
            // HS prints the STORED ranking value, whose oracle name was resolved
            // at parse time; RS keeps the raw source string, so it must be
            // re-rendered with the oracle name expanded — the same
            // `pretty_goal_rankings` the batch printer's `lemma_attr_docs` uses
            // (`heuristic=O` alone would drop the oracle file name).
            LemmaAttr::Heuristic(s) => format!(
                "heuristic={}",
                tamarin_theory::pretty_theory::pretty_goal_rankings(s, in_file)
            ),
            LemmaAttr::Output(xs) => format!("output={}", xs.join(",")),
            LemmaAttr::Left => "left".into(),
            LemmaAttr::Right => "right".into(),
            LemmaAttr::Hint(s) => s.clone(),
        })
        .collect();
    format!(" [{}]", parts.join(", "))
}

/// Main pane: render the content for a given path.
pub fn path_html(entry: &TheoryEntry, path: &TheoryPath) -> String {
    let typed = &entry.typed_theory;
    match path {
        TheoryPath::Help => help_html(entry),
        TheoryPath::Rules => rules_html(entry),
        TheoryPath::Message => message_html(entry),
        TheoryPath::Tactic => {
            // HS `tacticSnippet` (Web/Theory.hs:934-940) =
            //   ppSection "Tactic(s)" (prettyTactic <$> _thyTactic)
            // ppSection h s = withTag "h2" [] (text h) $$ withTag "p"
            //   [("class","monospace rules")] (vcat (intersperse (text "") s))
            // rendered through the `HtmlDoc Doc` transformer + postprocess.  A
            // literal '<' inside a tactic (e.g. regex lookbehind `(?<!'g'^)`)
            // is entity-escaped by `Doc::text` under the guard.
            let _html = tamarin_theory::pretty_hpj::HtmlDocGuard::enable();
            // `vcat (intersperse (text "") s)` = tactics joined by a blank line.
            let body = typed
                .tactic
                .iter()
                .map(|t| t.render())
                .collect::<Vec<_>>()
                .join("\n\n");
            assemble_pane(vec![Some(section_fragment(
                "Tactic(s)",
                "monospace rules",
                &body,
            ))])
        }
        // HS renders `text "this is a mistake"` for the bare lemma path
        // (`htmlThyPath` `TheoryLemma _`, Web/Theory.hs:1005-1144, see line 1068) — the UI never
        // navigates here (it uses the proof path); mirror it verbatim.
        TheoryPath::Lemma(_) => "this is a mistake".into(),
        TheoryPath::Proof { lemma, sub } => proof_html(entry, lemma, sub),
        TheoryPath::Method { lemma, sub, .. } => proof_html(entry, lemma, sub),
        TheoryPath::Source { kind, .. } => sources_html(entry, kind),
        // HS `htmlThyPath` arms `TheoryEdit`/`TheoryAdd`/`TheoryDelete`
        // (`src/Web/Theory.hs:1025-1133`).
        TheoryPath::Edit(name) => edit_lemma_html(entry, name),
        TheoryPath::Add(name) => add_lemma_html(name),
        TheoryPath::Delete(name) => delete_lemma_html(name),
    }
}

/// HS `htmlThyPath (TheoryEdit name)` (`src/Web/Theory.hs:1025-1065`).  The
/// textarea holds the lemma's `_lPlaintext` (HS `getLemmaPlaintext`,
/// `src/Web/Handler.hs:178-187`); a missing lemma falls back to the same
/// "Enter your new Lemma" default as Add.  `rows = 2 + (#newlines in plaintext)`
/// (HS `textHeight`).
fn edit_lemma_html(entry: &TheoryEntry, name: &str) -> String {
    let plaintext = entry
        .typed_theory
        .lookup_lemma(name)
        .map(|l| l.plaintext.clone())
        .unwrap_or_else(|| "Enter your new Lemma".to_string());
    let rows = 2 + plaintext.matches('\n').count();
    let esc_name = html_escape(name);
    format!(
        "<form method=\"post\" action=\"../../edit/edit/{action}\">\
<div contenteditable=\"true\">\
<label for=\"lemmaTextArea\"> Edit Lemma {name}</label>\n\
<textarea name=\"lemma-text\" id=\"lemmaTextArea\" rows=\"{rows}\">{plaintext}</textarea>\n\
</div>\n\
<button type=\"submit\">Submit</button>\n\
<p></p>\n\
<h3> Introduction to Lemma Edit:</h3>\n\
{noscript}\n\
<p><ul class=\"wrap-text\">\
<li>Modifying the lemma in the box above and clicking the submit button will attempt to modify the lemma in the current theory.\n<br>&zwnj;</br>\n</li>\n\
<li>Failures in parsing the lemma or verifying its well-formedness will result in an error, and the lemma will NOT be modified.\nHowever, your changes will be kept on this page until you leave this right panel.\n<br>&zwnj;</br>\n</li>\n\
<li>Editing a lemma will NOT modify the file it was loaded from, but clicking on \"Append modified lemmas to file\" in the Actions menu adds all modified lemmas as a comment at the end of the file on disk they were loaded from.\n<br>&zwnj;</br>\n</li>\n\
<li>Clicking on \"Download source\" in the Actions menu will download the modified version of the theory (including the modified lemmas), but not modify the file on disk.\n<br>&zwnj;</br>\n</li>\n\
<li>Modifying a reuse lemma will invalidate all subsequent proofs.\n<br>&zwnj;</br>\n</li>\n\
<li>Modifying a sources lemma is not supported and will result in an error.</li>\n\
</ul>\n{wrap_style}\n</p>\n</form>\n",
        action = esc_name,
        name = esc_name,
        rows = rows,
        plaintext = html_escape(&plaintext),
        noscript = NOSCRIPT_WARNING,
        wrap_style = WRAP_TEXT_STYLE,
    )
}

/// HS `htmlThyPath (TheoryAdd name)` (`src/Web/Theory.hs:1103-1133`).  The
/// textarea is always the literal "Enter your new Lemma" (HS passes
/// `lname = Nothing` for Add, so `getLemmaPlaintext` returns the default).
fn add_lemma_html(name: &str) -> String {
    let esc_name = html_escape(name);
    format!(
        "<form method=\"post\" action=\"../../edit/add/{action}\">\
<div contenteditable=\"true\">\
<label for=\"lemmaTextArea\">LemmaText</label>\n\
<textarea name=\"lemma-text\" id=\"lemmaTextArea\">Enter your new Lemma</textarea>\n\
</div>\n\
<button type=\"submit\">Submit</button>\n\
<p></p>\n\
<h3> Introduction to Adding Lemmas:</h3>\n\
{noscript}\n\
<p><ul class=\"wrap-text\">\
<li>Adds the lemma in the current position in the theory, but will throw an error if a lemma with the same name exists, the parsing fails, or the lemma isn't well-formed.\n<br>&zwnj;</br>\n</li>\n\
<li>Adding a lemma will NOT modify the loaded source file, but clicking on \"Append modified lemmas to file\" in the Actions menu appends all added lemmas as a comment at the end of the current theory file.\n<br>&zwnj;</br>\n</li>\n\
<li>Clicking on \"Download source\" in the Actions menu will download the modified version of the theory (including the added lemmas).</li>\n\
</ul>\n{wrap_style}\n</p>\n</form>\n",
        action = esc_name,
        noscript = NOSCRIPT_WARNING,
        wrap_style = WRAP_TEXT_STYLE,
    )
}

/// HS `htmlThyPath (TheoryDelete name)` (`src/Web/Theory.hs:1070-1101`).
fn delete_lemma_html(name: &str) -> String {
    let esc_name = html_escape(name);
    format!(
        "<p> Do you want to delete lemma {name}?</p>\n\
<form method=\"post\" action=\"../../edit/delete/{action}\">\
<button type=\"submit\">Yes</button>\n\
<p></p>\n\
<h3> Introduction to Lemma Delete:</h3>\n\
{noscript}\n\
<p><ul class=\"wrap-text\">\
<li>Clicking on the button above will delete the lemma from the loaded theory.\n<br>&zwnj;</br>\n</li>\n\
<li>Deleting a lemma will NOT modify the file it was loaded from, but clicking on \"Download source\" in the Actions menu will download the modified version of the theory (so without the deleted lemmas).\n<br>&zwnj;</br>\n</li>\n\
<li>Deleting a reuse lemma will invalidate all subsequent proofs.\n<br>&zwnj;</br>\n</li>\n\
<li>Deleting a source lemma is not supported and will result in an error.</li>\n\
{wrap_style}\n</ul>\n</p>\n</form>\n",
        name = esc_name,
        action = esc_name,
        noscript = NOSCRIPT_WARNING,
        wrap_style = WRAP_TEXT_STYLE,
    )
}

/// HS's shared `<noscript>` JavaScript-required warning (the `<span
/// class="tamarin">Tamarin</span>` Hamlet-emits a stray extra `</span>` the
/// parity normalizer drops; we emit a single well-formed span).
const NOSCRIPT_WARNING: &str =
    "<noscript><div class=\"warning\">Warning: JavaScript must be enabled for the\n\
<span class=\"tamarin\">Tamarin</span>\nprover GUI to function properly.</div>\n</noscript>";

/// HS's shared `.wrap-text li` inline `<style>` block.
const WRAP_TEXT_STYLE: &str =
    "<style>.wrap-text li {white-space: normal;\nword-wrap: break-word;}</style>";

/// HS `helpHtml` (`src/Web/Theory.hs:1187-1285`): the static Quick-introduction
/// and keyboard-shortcut help page, prefixed by the `Theory: NAME (Loaded at TIME
/// from ORIGIN) ERRORS` env line.  The env line's `(Loaded at ...)` parenthetical
/// is stripped by the parity normalizer (`norm_env`) on both sides, so its
/// timestamp/origin need not be byte-identical to HS.  `errorsHtml` is the
/// wellformedness banner (`<div class="wf-warning">…</div>` when the theory has
/// warnings, empty otherwise), populated from the stored `wf_report` at load.
fn help_html(entry: &TheoryEntry) -> String {
    // HS `show info.origin` — e.g. `Local "/path/Foo.spthy"`.
    let origin = match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => format!("Local \"{}\"", p.display()),
        crate::state::TheoryOrigin::Upload(n) => format!("Upload \"{}\"", n),
        crate::state::TheoryOrigin::Interactive => "Interactive".to_string(),
    };
    let time = entry.loaded_at.format("%H:%M:%S").to_string();
    // HS `helpHtml` (Web/Theory.hs:1187-1285) is a `$newline never` Hamlet
    // template returned directly as `Html` (NOT through `renderHtmlDoc`), so it
    // emits a single line with no `<br/>`.  The env line carries the theory
    // name + load time/origin + wellformedness banner; the rest is a fixed
    // static block reproduced byte-for-byte from HS (including the stray extra
    // `</span>` after the Tamarin span that HS's Hamlet emits).
    let env_line = format!(
        "<p>Theory: {name} (Loaded at {time} from {origin}) {errors}</p>",
        name = html_escape(&entry.name),
        time = html_escape(&time),
        origin = html_escape(&origin),
        errors = entry.errors_html,
    );
    format!("{env_line}{HELP_STATIC}")
}

/// The static remainder of HS `helpHtml` (everything after the env-line `</p>`),
/// reproduced byte-for-byte from the HS interactive server (`$newline never`
/// Hamlet, so a single line with the stray `</span>` quirk after the Tamarin
/// span).
const HELP_STATIC: &str = r#"<div id="help"><h3>Quick introduction</h3><noscript><div class="warning">Warning: JavaScript must be enabled for the<span class="tamarin">Tamarin</span></span>prover GUI to function properly.</div></noscript><p><em>Left pane: Proof scripts display.</em><ul><li>When a theory is initially loaded, there will be a line at the end of each theorem stating <tt>"by sorry // not yet proven"</tt>.  Click on <tt>sorry</tt> to inspect the proof state.</li><li>Right-click to show further options, such as autoprove.</li></ul></p><p><em>Right pane: Visualization.</em><ul><li>Visualization and information display relating to the currently selected item.</li></ul></p></div><h3>Keyboard shortcuts</h3><p><div id="shortcuts"><table><tr><td><span class="keys">j/k</span></td><td>Jump to the next/previous proof path within the currently focused lemma.</td></tr><tr><td><span class="keys">J/K</span></td><td>Jump to the next/previous open constraint within the currently focused lemma, or to the next/previous lemma if there are no more <tt>sorry</tt> steps in the proof of the current lemma.</td></tr><tr><td><span class="keys">1-9</span></td><td>Apply the proof method with the given number as shown in the applicable proof method section in the main view.</td></tr><tr><td><span class="keys">a/A</span></td><td>Apply the autoprove method to the focused proof step. <span class="keys">a</span> stops after finding a solution, and <span class="keys">A</span> searches for all solutions. Needs to have a <tt>sorry</tt> selected to work.</td></tr><tr><td><span class="keys">b/B</span></td><td>Apply a bounded-depth version of the autoprove method to the focused proof step. <span class="keys">b</span> stops after finding a solution, and <span class="keys">B</span> searches for all solutions. Needs to have a <tt>sorry</tt> selected to work.</td></tr><tr><td><span class="keys">s/S</span></td><td>Apply the autoprove method to all lemmas. <span class="keys">s</span> stops after finding a solution, and <span class="keys">S</span> searches for all solutions.</td></tr><tr><td><span class="keys">?</span></td><td>Display this help message.</td></tr></table></div></p>"#;

/// Render the proof tree pane for a lemma at a given sub-path.
/// If a live [`ProofState`] is already built, use the actual tree;
/// otherwise fall back to the lemma's static info plus a build hint.
pub fn proof_html(entry: &TheoryEntry, lemma: &str, sub: &[String]) -> String {
    // HS `htmlThyPath` for `TheoryProof l p` (Web/Theory.hs:1019-1023):
    //   pp $ fromMaybe (text "No such lemma or proof path.") $ do
    //     lemma <- lookupLemma l thy
    //     subProofSnippet ... l p (getProofContext lemma thy)
    //       <$> resolveProofPath thy l p
    // → renders ONLY the sub-proof snippet at the resolved path; a missing
    //   lemma or unresolvable proof path yields the single fallback string.
    //   No lemma header, no formula echo, no whole-tree dump.
    if entry.typed_theory.lookup_lemma(lemma).is_none() {
        return "No such lemma or proof path.".into();
    }
    if let Some(ps) = &entry.proof_state {
        if let Some(root) = ps.get_root(lemma) {
            if let Some(n) = crate::handlers::proof_tree::navigate_at(&root, sub) {
                // `write_applicable_methods` execs every candidate method —
                // solver code that resolves user fun symbols via
                // thread-locals; install them for this render (tokio
                // workers start empty — see `ProofState::user_funs`).
                let _user_funs_guard = ps.install_user_funs();
                // Install this lemma's per-lemma `use_induction`/`heuristic`
                // into the shared ctx before ranking (HS `getProofContext`);
                // otherwise the Applicable Proof Methods order + ranking name
                // default to `AvoidInduction`/`Smart` and diverge from HS.
                let mut ctx_guard = ps.ctx.lock();
                ps.install_lemma_settings(&mut ctx_guard, lemma);
                return crate::handlers::proof_tree::render_sub_proof_snippet(
                    entry.idx, lemma, sub, n, &ctx_guard,
                );
            }
        }
    }
    "No such lemma or proof path.".into()
}

// ---------------------------------------------------------------------
// Main-pane content: message / rules / source-case snippets.
//
// These mirror HS `Web.Theory` `messageSnippet` (920-931), `rulesSnippet`
// (887-917) and `htmlSource`/`reqCasesSnippet` (820-879).  All TEXT content is
// produced by the byte-faithful `--prove` printers (`pretty_theory`,
// `pretty_formula`, `pretty_system`) so it stays consistent with the CLI; this
// module only adds the surrounding HTML tags HS's `withTag`/`ppSection` emit.
// ---------------------------------------------------------------------

use tamarin_theory::rule::{IntrRuleAC, IntrRuleACInfo};

/// HS `isConstrRule` for the message-page classification (Model/Rule.hs:684-691):
/// `_crConstruct` = ConstrRule | FreshConstr | PubConstr | NatConstr | Coerce.
fn is_constr_intr(info: &IntrRuleACInfo) -> bool {
    matches!(
        info,
        IntrRuleACInfo::ConstrRule(_)
            | IntrRuleACInfo::FreshConstr
            | IntrRuleACInfo::PubConstr
            | IntrRuleACInfo::NatConstr
            | IntrRuleACInfo::Coerce
    )
}

/// HS `isDestrRule` (Model/Rule.hs:671-675): `_crDestruct` = DestrRule | IEquality.
fn is_destr_intr(info: &IntrRuleACInfo) -> bool {
    matches!(
        info,
        IntrRuleACInfo::DestrRule(..) | IntrRuleACInfo::IEquality
    )
}

/// HS `ppSection header s = withTag "h2" [] (text header) $$ withTag "p"
/// [("class","monospace rules")] body` (Web/Theory.hs:928-931), rendered
/// through the `HtmlDoc` transformer.  Returns the pane fragment BEFORE
/// `postprocessHtmlDoc` (the caller `vcat`-joins fragments with `\n` and
/// postprocesses once): `<h2>HEADER</h2>` on its own line (from `$$`), then the
/// zero-width `<p …>` open glued before `body`'s first line and `</p>` after
/// its last (`withTag`).  `body` is already escaped + span-marked (rendered
/// under [`HtmlDocGuard`]); `header` is `text header` so it is entity-escaped
/// too.
fn section_fragment(header: &str, class: &str, body: &str) -> String {
    format!(
        "<h2>{}</h2>\n<p class=\"{}\">{}</p>",
        tamarin_theory::pretty_hpj::escape_html_entities(header),
        class,
        body,
    )
}

/// HS `ppWithHeader` (Web/Theory.hs:912-917): like [`section_fragment`] but the
/// whole section is `emptyDoc` (omitted from the `vcat`) when `body` is empty
/// (`caseEmptyDoc emptyDoc … body`).
fn with_header_fragment(header: &str, class: &str, body: &str) -> Option<String> {
    if body.is_empty() {
        None
    } else {
        Some(section_fragment(header, class, body))
    }
}

/// `vcat` the pane fragments (HS `messageSnippet`/`rulesSnippet` top-level
/// `vcat`) then `postprocessHtmlDoc` once (leading spaces → `&nbsp;`, `<br/>`
/// per line).  `None` fragments are HS `emptyDoc` and vanish (`emptyDoc $$ x =
/// x`); an empty `String` fragment is HS `text ""` (a real blank line, e.g. the
/// absent-macros slot).
fn assemble_pane(fragments: Vec<Option<String>>) -> String {
    let pieces: Vec<String> = fragments.into_iter().flatten().collect();
    tamarin_theory::pretty_hpj::postprocess_html(&pieces.join("\n"))
}

/// HS `messageSnippet` (Web/Theory.hs:920-931): Signature +
/// Construction/Deconstruction rule sections.
fn message_html(entry: &TheoryEntry) -> String {
    // HS renders `messageSnippet` through the `HtmlDoc Doc` transformer (same
    // `pp = renderHtmlDoc` dispatch as `rulesSnippet`, Web/Theory.hs:1014-1015):
    // every `text`/`char` is entity-escaped + measured escaped, keywords/
    // operators become `hl_*` spans, and the whole doc is postprocessed
    // (`<br/>`/`&nbsp;`).  Enable HtmlDoc mode for the pane build.
    let _html = tamarin_theory::pretty_hpj::HtmlDocGuard::enable();
    // `prettySignatureWithMaude thy._thySignature` — the same signature block
    // the theory body prints.
    let sig_block =
        tamarin_theory::pretty_theory::web_signature_block(&entry.typed_theory.signature.maude_sig);
    // `getClassifiedRules thy`'s `_crConstruct` / `_crDestruct`.  RS stores
    // proto rules separately, so `ctx.intruder_rules` is exactly HS's
    // `intrRulesAC`; an order-preserving filter reproduces the classification.
    let mut construct: Vec<IntrRuleAC> = Vec::new();
    let mut destruct: Vec<IntrRuleAC> = Vec::new();
    if let Some(ps) = &entry.proof_state {
        let ctx = ps.ctx.lock();
        for ir in &ctx.intruder_rules {
            if is_constr_intr(&ir.info) {
                construct.push(ir.clone());
            } else if is_destr_intr(&ir.info) {
                destruct.push(ir.clone());
            }
        }
    }
    // `map prettyRuleAC` joined by one blank line == `pretty_intruder_variants`
    // (HS `vcat (intersperse (text "") s)`).
    let construct_block = tamarin_theory::pretty_formula::pretty_intruder_variants(&construct);
    let destruct_block = tamarin_theory::pretty_formula::pretty_intruder_variants(&destruct);
    // HS `messageSnippet = vcat [ppSection "Signature" …, ppSection
    // "Construction Rules" …, ppSection "Deconstruction Rules" …]`.  `ppSection`
    // is ALWAYS emitted (even with an empty body), unlike `ppWithHeader`.
    assemble_pane(vec![
        Some(section_fragment("Signature", "monospace rules", &sig_block)),
        Some(section_fragment(
            "Construction Rules",
            "monospace rules",
            &construct_block,
        )),
        Some(section_fragment(
            "Deconstruction Rules",
            "monospace rules",
            &destruct_block,
        )),
    ])
}

/// HS `showInjFact` (Web/Theory.hs:906-910): `showFactTag tag ++ "(" ++
/// intercalate "," ("id":positions) ++ ")"`.
fn show_inj_fact(
    tag: &tamarin_theory::fact::FactTag,
    behaviours: &[Vec<tamarin_theory::tools::injective_fact_instances::MonotonicBehaviour>],
) -> String {
    use tamarin_theory::fact::{FactTag, Multiplicity};
    let name = tamarin_theory::fact::fact_tag_name(tag);
    let head = match tag {
        FactTag::Proto(Multiplicity::Persistent, _, _) => format!("!{}", name),
        _ => name.to_string(),
    };
    let mut parts: Vec<String> = vec!["id".to_string()];
    for bb in behaviours {
        if bb.len() == 1 {
            parts.push(bb[0].to_string());
        } else {
            let inner: Vec<String> = bb.iter().map(|b| b.to_string()).collect();
            parts.push(format!("({})", inner.join(",")));
        }
    }
    format!("{}({})", head, parts.join(","))
}

/// HS `rulesSnippet` (Web/Theory.hs:887-917).
fn rules_html(entry: &TheoryEntry) -> String {
    // HS renders `rulesSnippet` through the `HtmlDoc Doc` transformer
    // (`HtmlDocument d => ClosedTheory -> d`, Web/Theory.hs:887-917, laid out by
    // `renderHtmlDoc`): every `text`/`char` is entity-escaped + measured
    // escaped, keywords/operators/comments become `hl_*` spans, and the whole
    // doc is postprocessed.  The batch `--prove` theory printer calls the SAME
    // renderers WITHOUT the guard and is unaffected (thread-local).
    let _html = tamarin_theory::pretty_hpj::HtmlDocGuard::enable();
    use tamarin_theory::pretty_hpj::{escape_html_entities, multi_comment_};
    // HS `rulesSnippet`'s FIRST slot: `if null (theoryMacros thy) then text
    // empty else ppWithHeader "Macros" (prettyMacros ...)` — a `text ""` blank
    // line when there are no macros, else the macros section.
    let macros_block = tamarin_theory::pretty_theory::web_macros(&entry.parser_theory);
    let proto_rules =
        tamarin_theory::pretty_theory::web_proto_rules(&entry.parser_theory, &entry.typed_theory);
    let mut inj_body = String::from("None");
    let mut extra_ac: Vec<String> = Vec::new();
    if let Some(ps) = &entry.proof_state {
        let ctx = ps.ctx.lock();
        // `getInjectiveFactInsts thy` — already computed on the context.
        if !ctx.injective_fact_insts.is_empty() {
            let items: Vec<String> = ctx
                .injective_fact_insts
                .iter()
                .map(|(tag, behaviours)| show_inj_fact(tag, behaviours))
                .collect();
            inj_body = items.join(", ");
        }
        // `extraACRules` = `_crProtocol` not already in `theoryRules` (ISend,
        // IRecv).  HS `prettyIntruderRuleAC r = prettyRuleAC r $--$ nest 2
        // (multiComment_ ["has exactly the trivial AC variant"]) $--$ text ""`
        // (Web/Theory.hs:887-917, see line 911): body, blank line, indent-2 comment, blank line,
        // trailing empty line.  Rendered as a string that is `vcat`-joined
        // (`\n`) with the other rules below.
        let comment = multi_comment_(&["has exactly the trivial AC variant"]).render();
        for ir in &ctx.intruder_rules {
            if is_constr_intr(&ir.info) || is_destr_intr(&ir.info) {
                continue;
            }
            let body =
                tamarin_theory::pretty_formula::pretty_intruder_variants(std::slice::from_ref(ir));
            extra_ac.push(format!("{body}\n\n  {comment}\n\n"));
        }
    }
    // `vcat (map prettyIntruderRuleAC extraACRules ++ map prettyClosedProtoRule
    // protoRules)` — `vcat` = `$$`, i.e. join with a single `\n`.  Each
    // rule string already carries its own internal blank lines (intruder rules
    // end with a trailing blank; proto rules end at the comment), so the
    // resulting blank-line structure matches HS byte-for-byte.
    let mut msr_parts = extra_ac;
    msr_parts.extend(proto_rules);
    let msr_body = msr_parts.join("\n");
    // `vsep $ map prettyRestriction` (Web/Theory.hs:887-917, see line 895) = `foldr ($--$)` =
    // blank line between restrictions.
    let restr_body =
        tamarin_theory::pretty_theory::web_restrictions(&entry.parser_theory, &entry.typed_theory)
            .join("\n\n");

    // HS `rulesSnippet` order: Macros slot → Fact Symbols → MSR → Restrictions.
    let macros_slot = match &macros_block {
        // HS `ppWithHeader "Macros"` — omitted iff the body is empty.
        Some(m) => with_header_fragment("Macros", "monospace rules", m),
        // HS `text empty` — a real blank line.
        None => Some(String::new()),
    };
    assemble_pane(vec![
        macros_slot,
        with_header_fragment(
            "Fact Symbols with Injective Instances",
            "monospace rules",
            &escape_html_entities(&inj_body),
        ),
        with_header_fragment("Multiset Rewriting Rules", "monospace rules", &msr_body),
        with_header_fragment(
            "Restrictions of the Set of Traces",
            "monospace rules",
            &restr_body,
        ),
    ])
}

/// HS `reqCasesSnippet` + `htmlSource` (Web/Theory.hs:820-879): the raw/refined
/// source-case listing.  The `src_idx`/`case_idx` URL fields are ignored (HS
/// `TheorySource kind _ _` renders the whole `getSource kind thy` list); they
/// only address the per-case interactive graph.
fn sources_html(entry: &TheoryEntry, kind: &SourceKind) -> String {
    // HS renders `reqCasesSnippet = vcat (htmlSource <$> …)` through the
    // `HtmlDoc Doc` transformer + `renderHtmlDoc` (Web/Theory.hs:1005-1144, see line 1016): the
    // goal headers, per-case sequents (`pretty_non_graph_system`) and all
    // structural tags are entity-escaped + span-marked and postprocessed once.
    let _html = tamarin_theory::pretty_hpj::HtmlDocGuard::enable();
    let (kind_str, want_refined) = match kind {
        SourceKind::Raw => ("raw", false),
        SourceKind::Refined => ("refined", true),
    };
    let source_lists = compute_source_lists(entry, want_refined);
    // `vcat` the per-source blocks (join with `\n`), then `postprocessHtmlDoc`.
    let blocks: Vec<String> = source_lists
        .iter()
        .enumerate()
        .map(|(j, (goal, cases))| render_html_source(entry.idx, kind_str, j + 1, goal, cases))
        .collect();
    tamarin_theory::pretty_hpj::postprocess_html(&blocks.join("\n"))
}

/// Compute `getSource kind thy` — the raw or refined source list, as
/// `(goal, cases)` pairs.  Shared by `sources_html` (the page) and
/// `source_case_counts` (the theory-index `(N cases, …)` annotation) so both
/// stay consistent.  Returns empty when the proof state is not yet built.
fn compute_source_lists(
    entry: &TheoryEntry,
    want_refined: bool,
) -> Vec<(
    tamarin_theory::constraint::constraints::Goal,
    Vec<(String, tamarin_theory::constraint::system::System)>,
)> {
    use tamarin_theory::constraint::system::SourceKind as SysSourceKind;
    let Some(ps) = &entry.proof_state else {
        return Vec::new();
    };
    // Saturation (`s.cases(&ctx)` → `ensure_saturated`) and
    // `refine_with_source_asms` run solver code; `formula_to_guarded` on
    // the `[sources]`-lemma formulas resolves user fun symbols.  All via
    // thread-locals — install them (see `ProofState::user_funs`).
    let _user_funs_guard = ps.install_user_funs();
    let ctx = ps.ctx.lock();
    // Refined sources fold in the `[sources]`-lemma typing assumptions
    // (HS `refineWithSourceAsms`, Rule.hs:157).  With no such lemma the refine
    // is a plain relabel to `RefinedSource` (Sources.hs:617-618).
    let typ_asms: Vec<tamarin_theory::guarded::Guarded> = if want_refined {
        entry
            .typed_theory
            .lemmas()
            .filter(|l| {
                matches!(l.trace_quantifier, TraceQuantifier::AllTraces)
                    && l.attributes.iter().any(|a| matches!(a, LemmaAttr::Sources))
            })
            .filter_map(|l| tamarin_theory::guarded::formula_to_guarded(&l.formula).ok())
            .collect()
    } else {
        Vec::new()
    };

    // `getSource kind thy`: raw = `ctx.full_sources` (precomputed + saturated);
    // refined = raw with `refineWithSourceAsms` applied (or relabeled).
    if want_refined && !typ_asms.is_empty() {
        let cloned: Vec<_> = ctx
            .full_sources
            .iter()
            .map(|s| {
                let _ = s.cases(&ctx);
                s.clone()
            })
            .collect();
        let refined = tamarin_theory::constraint::solver::sources::refine_with_source_asms(
            cloned, &typ_asms, &ctx,
        );
        refined
            .iter()
            .map(|s| (s.goal.clone(), s.cases_or_empty()))
            .collect()
    } else {
        ctx.full_sources
            .iter()
            .map(|s| {
                let mut cases = s.cases(&ctx);
                if want_refined {
                    for (_, sys) in cases.iter_mut() {
                        sys.source_kind = Some(SysSourceKind::RefinedSources);
                    }
                }
                (s.goal.clone(), cases)
            })
            .collect()
    }
}

/// HS `casesInfo kind` (Web/Theory.hs:399-406): `(nCases, chainInfo)` where
/// `nCases = length (getSource kind thy)` and `nChains = sum $ map (sum .
/// unsolvedChainConstraints)`.  Rendered as `(N cases, deconstructions
/// complete)` or `(N cases, K partial deconstructions left)`.
fn source_case_counts(entry: &TheoryEntry, want_refined: bool) -> (usize, usize) {
    let source_lists = compute_source_lists(entry, want_refined);
    let n_cases = source_lists.len();
    let n_chains: usize = source_lists
        .iter()
        .flat_map(|(_, cases)| cases.iter())
        .map(|(_, sys)| {
            tamarin_theory::constraint::solver::sources::unsolved_chain_constraints(sys)
        })
        .sum();
    (n_cases, n_chains)
}

/// HS `htmlSource` (Web/Theory.hs:820-845) for a single [`Source`] — returns
/// the pre-`postprocessHtmlDoc` fragment (the caller `vcat`-joins with `\n`
/// then postprocesses once).  Must be called under an [`HtmlDocGuard`] so the
/// goal + sequent render escaped + span-marked.
fn render_html_source(
    idx: usize,
    kind: &str,
    j: usize,
    goal: &tamarin_theory::constraint::constraints::Goal,
    cases: &[(String, tamarin_theory::constraint::system::System)],
) -> String {
    use tamarin_theory::pretty_hpj::escape_html_entities;
    let n_cases = cases.len();
    // `withTag "p" [] ppPrem` — the per-case premise paragraph, built as ONE
    // Doc so the goal wraps (continuation `&nbsp;`/`<br/>`) exactly as HS.
    let prem_p = tamarin_theory::pretty_theory::web_pretty_source_prem(goal);
    // `withTag "h2" [] ppHeader`, `ppHeader = hsep [text "Sources of" <-> ppPrem,
    // parens (nCases <-> "cases")]` — the whole header is ONE Doc so the goal
    // wraps at the width WITH the `Sources of ` prefix offset.
    let header = format!(
        "<h2>{}</h2>",
        tamarin_theory::pretty_theory::web_pretty_source_header(goal, n_cases)
    );
    if cases.is_empty() {
        // HS `withTag "h2" [] ppHeader $-$ withTag "h3" [] (text "No cases.")`.
        return format!("{header}\n<h3>No cases.</h3>");
    }
    // `vcat (h2 : concatMap ppCase cases)` — each `ppCase` is [h3, static-graph,
    // p-prem, p-cases]; all joined with `\n`.
    let mut parts: Vec<String> = vec![header];
    for (i, (name, sys)) in cases.iter().enumerate() {
        let ii = i + 1;
        // `isPartial = not (null (unsolvedChains se))`.
        let is_partial =
            tamarin_theory::constraint::solver::sources::unsolved_chain_constraints(sys) != 0;
        let partial = if is_partial {
            "(partial deconstructions)"
        } else {
            ""
        };
        // HS `fsep [text "Source", int i, text "of", nCases, text " / named ",
        // doubleQuotes (text name), partial]` — `fsep` single-spaces, and the
        // ` / named ` text keeps its own surrounding spaces (→ double spaces),
        // and the trailing (possibly empty) `partial` element is preceded by an
        // `fsep` space (→ trailing space even when not partial).
        parts.push(format!(
            "<h3>Source {i} of {n}  / named  &quot;{name}&quot; {partial}</h3>",
            i = ii,
            n = n_cases,
            name = escape_html_entities(name),
            partial = partial,
        ));
        // `refDotInteractiveStaticPath = withTag "static-graph"
        // [("graphSrc", srcPath)] (text "")` — note the capital-S `graphSrc`.
        parts.push(format!(
            "<static-graph graphSrc=\"/thy/trace/{idx}/intdot/cases/{kind}/{j}/{i}\"></static-graph>",
            idx = idx, kind = kind, j = j, i = ii,
        ));
        // `withTag "p" [] ppPrem`.
        parts.push(prem_p.clone());
        // `wrapP (prettyNonGraphSystem se)`, `wrapP = withTag "p"
        // [("class","monospace cases")]`.  The sequent renders under the guard.
        parts.push(format!(
            "<p class=\"monospace cases\">{}</p>",
            tamarin_theory::pretty_system::pretty_non_graph_system(sys)
        ));
    }
    parts.join("\n")
}
