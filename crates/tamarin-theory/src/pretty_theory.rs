// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Theory pretty-printer.  Port of Haskell's `prettyClosedTheory`
//! (ClosedTheory.hs:382-418) — top-level renderer for `--prove` output.
//!
//! Goal: byte-identical output to Haskell on the analyzed theory body.
//! The output layout:
//!
//! ```text
//! theory <name>
//!
//! begin
//!
//! // Function signature and definition of the equational theory E
//!
//! builtins: ...     (if any)
//! functions: ...
//! equations: ...
//!
//! rule (modulo E) <name>:
//!    [ <prems> ] --[ <acts> ]-> [ <concs> ]
//!
//!   /* has exactly the trivial AC variant */
//!
//! restriction <name>:
//!   "<formula>"
//!
//! lemma <name> [attrs]:
//!   <quant> "<formula>"
//! /*
//! guarded formula characterizing ...:
//! "<gformula>"
//! */
//! <proof body>
//!
//! /* All wellformedness checks were successful. */ (or warning block)
//!
//! /*
//! Generated from:
//! Tamarin version ...
//! Maude version ...
//! Git revision: ...
//! Compiled at: ...
//! */
//!
//! end
//! ```
//!
//! Each top-level item is separated by a blank line (HS uses `vsep`).
//!
//! HS's `prettyTheory` (TheoryObject.hs:747-783) is one function taking five
//! injected printers; here its ITEM half is [`pretty_theory_items`] and its
//! header/footer half is spelled out once in [`pretty_closed_theory`] and once
//! in `open_theory_blocks`.  The two assemblies differ in `ppSig`/`ppCache`
//! and in the trailing wellformedness / `Generated from:` / `end` handling,
//! and each is about thirty lines, so they stay apart.

use crate::constraint::solver::goals::GoalRanking;
use crate::pretty_formula as pf;
use crate::theory::{Theory, TheoryItem, TranslationElement};
use tamarin_term::pretty::pretty_nterm;

/// Build info passed in from the prover binary so the Generated-from
/// block reflects compile-time facts.
#[derive(Debug, Clone)]
pub struct BuildInfo {
    pub tamarin_version: String,
    pub maude_version: String,
    pub git_revision: String,
    pub git_branch: String,
    pub compiled_at: String,
}

/// Per-lemma proof result produced by the prover.  When `proof_body`
/// is `None` (e.g. when the user did not pass `--prove`), the lemma's
/// stored skeleton (`by sorry`) is rendered instead.
#[derive(Debug, Clone)]
pub struct ProvedLemma {
    pub name: String,
    /// Pre-rendered HS-faithful proof body (lines of text, no leading
    /// blank line, no trailing blank line).  See `pretty_proof_body`.
    pub proof_body: Option<String>,
}

// =============================================================================
// Heuristic / GoalRanking rendering
// =============================================================================

/// Compute the default oracle name for a theory file.
///
/// Mirrors HS `defaultOracleNames` (System.hs:550-560) exactly: take the
/// prefix before the first dot in the complete input path, then the final
/// slash-delimited group (including its leading slash), and probe that name
/// from the process CWD. This intentionally preserves upstream's surprising
/// behavior for paths containing directories or multiple dots.
pub(crate) fn oracle_name_for_theory(in_file: &str) -> String {
    let candidate = oracle_candidate_for_theory(in_file);
    if std::path::Path::new(&candidate).is_file() {
        candidate
    } else {
        "oracle".to_string()
    }
}

fn oracle_candidate_for_theory(in_file: &str) -> String {
    // `head (groupBy (\_ b -> b /= '.') inFile)` always keeps the first
    // character, even when it is itself a dot.  Only a later dot terminates
    // the group (`.foo.spthy` -> `.foo`, `./foo.spthy` -> `./foo`).
    let before_dot = in_file
        .char_indices()
        .skip(1)
        .find(|(_, ch)| *ch == '.')
        .map_or(in_file, |(i, _)| &in_file[..i]);
    let final_group = before_dot
        .rfind('/')
        .map_or(before_dot, |slash| &before_dot[slash..]);
    format!("{final_group}.oracle")
}

/// Render one `GoalRanking` as the heuristic token that names it, mirroring
/// HS `prettyGoalRanking` (System.hs:709-714): an oracle ranking as its
/// letter plus the quoted relative oracle path, a tactic ranking as its
/// braced name, every other ranking as the single letter
/// `goalRankingIdentifiers` maps to it (System.hs:584-597).
fn pretty_goal_ranking(r: &GoalRanking) -> String {
    match r {
        GoalRanking::Smart(false) => "s".to_string(),
        GoalRanking::Smart(true) => "S".to_string(),
        GoalRanking::Inj(false) => "i".to_string(),
        GoalRanking::Inj(true) => "I".to_string(),
        GoalRanking::Sapic => "p".to_string(),
        GoalRanking::SapicPKCS11 => "P".to_string(),
        GoalRanking::GoalNr => "C".to_string(),
        GoalRanking::UsefulGoalNr => "c".to_string(),
        GoalRanking::Oracle { oracle_path, .. } => format!("o \"{}\"", oracle_path),
        GoalRanking::OracleSmart { oracle_path, .. } => format!("O \"{}\"", oracle_path),
        GoalRanking::Tactic { tactic, .. } => format!("{{{}}}", tactic.name),
    }
}

/// HS `prettyGoalRankings rs = unwords (map prettyGoalRanking rs)`
/// (System.hs:706-707).
pub fn pretty_goal_rankings(rankings: &[GoalRanking]) -> String {
    rankings
        .iter()
        .map(pretty_goal_ranking)
        .collect::<Vec<_>>()
        .join(" ")
}

/// Render the verbatim text of a `heuristic=` lemma attribute in HS style.
///
/// HS stores that attribute as the `[GoalRanking ProofContext]` its parser
/// built (`LemmaHeuristic`, lib/theory/src/Lemma.hs:103); the port keeps the
/// source text, so it is parsed here — with the theory's `in_file` for the
/// default oracle name — and rendered through [`pretty_goal_rankings`].  A
/// `{name}` ranking prints its name whether or not the theory declares that
/// tactic, so the tactic list is not needed.
pub fn pretty_heuristic_str(raw: &str, in_file: &str) -> String {
    pretty_goal_rankings(
        &crate::constraint::solver::goals::parse_heuristic_str_with_tactics(raw, in_file, &[]),
    )
}

// =============================================================================

/// Render the analyzed theory in HS's `prettyClosedTheory` shape
/// (ClosedTheory.hs:381-418#prettyClosedTheory).
pub fn pretty_closed_theory(
    thy: &Theory,
    proved: &[ProvedLemma],
    wf_block: &str,
    build: &BuildInfo,
) -> String {
    let in_file = thy.in_file.as_str();
    // `ppCache` for a closed theory is `ppInjectiveFactInsts`, the "looping
    // facts with injective instances" comment (ClosedTheory.hs:413-418).  The
    // header's blocks are `vsep`-separated, which this route writes as the
    // "\n\n" join plus the trailing newline every following block is written
    // against.
    let mut out = theory_header_blocks(thy, &render_injective_fact_insts(thy)).join("\n\n");
    out.push('\n');

    // HS `prettyClosedTheory` (ClosedTheory.hs:383-402) renders the merged
    // rule items through `prettyOpenProtoRuleAsClosedRule` when some of them
    // carries an AC rule of its own, and the closed items through
    // `prettyClosedProtoRule` otherwise.
    let proof_bodies: tamarin_utils::FastMap<&str, &str> = proved
        .iter()
        .filter_map(|p| Some((p.name.as_str(), p.proof_body.as_deref()?)))
        .collect();
    let proof = |lem: &crate::theory::Lemma| match proof_bodies.get(lem.name.as_str()) {
        Some(b) => (*b).to_string(),
        None => "by sorry".to_string(),
    };
    // HS `emptyString` (lib/theory/src/Pretty.hs:24-25) as `ppSap`
    // (ClosedTheory.hs:390, :398).
    let translation = |_: &TranslationElement| String::new();
    let blocks = if crate::theory::contains_open_rule_variants(&thy.items) {
        let merged = crate::theory::merge_open_proto_rules(&thy.items);
        pretty_theory_items(
            &merged,
            &ItemPrinters {
                rule: &|r| crate::rule::pretty_open_proto_rule_as_closed_rule(r).render(),
                proof: &proof,
                translation: &translation,
                in_file,
                open_formulas: false,
            },
        )
    } else {
        pretty_theory_items(
            &crate::theory::close_proto_rules(&thy.items),
            &ItemPrinters {
                rule: &|r: &crate::theory::ClosedProtoRule| {
                    crate::rule::pretty_closed_proto_rule(&r.rule_ac, &r.rule_e).render()
                },
                proof: &proof,
                translation: &translation,
                in_file,
                open_formulas: false,
            },
        )
    };
    for b in blocks {
        out.push('\n');
        out.push_str(&b);
        out.push('\n');
    }

    // Wellformedness block (already preformatted: either the "all
    // successful" line or the WARNING /* ... */ block).
    out.push('\n');
    out.push_str(wf_block);
    out.push('\n');

    // Generated-from block.
    out.push('\n');
    out.push_str(&render_generated_from(build));
    out.push('\n');

    // end
    out.push_str("\nend\n");

    out
}

// =============================================================================
// The theory item fold (HS `prettyTheory`, TheoryObject.hs:747-783)
// =============================================================================

/// The printers HS's `prettyTheory` (TheoryObject.hs:747-783) injects that
/// reach a theory ITEM.  `ppSig` and `ppCache` are applied to the header, so
/// they stay with the two header assemblies.
///
/// HS applies `ppPrf` to the lemma's own proof; RS's closed print takes the
/// proof body from the prover's result list instead, so the slot is handed
/// the whole lemma.
pub struct ItemPrinters<'a, R> {
    /// HS `ppRule`.
    pub rule: &'a (dyn Fn(&R) -> String + Sync),
    /// HS `ppPrf`, the body `prettyLemma` puts under the lemma
    /// (lib/theory/src/Lemma.hs:116-141, see line 130).
    pub proof: &'a (dyn Fn(&crate::theory::Lemma) -> String + Sync),
    /// HS `ppSap`.
    pub translation: &'a (dyn Fn(&TranslationElement) -> String + Sync),
    /// The theory's file name, which a `heuristic=` lemma attribute needs to
    /// resolve a bare `o`/`O` ranking's default oracle (`defaultOracleNames`,
    /// System.hs:551-561).
    pub in_file: &'a str,
    /// Render the pre-macro formula without an `expanded formula` block.
    pub open_formulas: bool,
}

/// HS `parMap rdeepseq ppItem (filter (not . isConfigBlock) (thyItems thy))`
/// (TheoryObject.hs:767): one rendered block per item, in source order.  HS's
/// `vsep` is `foldr ($--$) emptyDoc` over those blocks and `$--$` drops an
/// empty operand (Theory/Text/Pretty.hs:83-84), so an item that renders
/// nothing contributes no block and no blank line.
pub fn pretty_theory_items<R: Sync>(
    items: &[TheoryItem<R>],
    pp: &ItemPrinters<'_, R>,
) -> Vec<String> {
    use rayon::prelude::*;
    items
        .par_iter()
        .map(|item| pretty_theory_item(item, pp))
        .filter(|b| !b.is_empty())
        .collect()
}

/// HS `ppItem = foldTheoryItem ppRule prettyRestriction (prettyLemma ppPrf)
/// (uncurry prettyFormalComment) prettyConfigBlock prettyPredicate
/// prettyMacros ppSap` (TheoryObject.hs:772-781).  The config blocks are
/// printed before `begin` (TheoryObject.hs:759), so the item stream skips
/// them.
fn pretty_theory_item<R>(item: &TheoryItem<R>, pp: &ItemPrinters<'_, R>) -> String {
    match item {
        TheoryItem::Rule(r) => (pp.rule)(r),
        TheoryItem::Restriction(r) => {
            if pp.open_formulas {
                let formula = r.original_formula.as_ref().unwrap_or(&r.formula);
                pretty_restriction_view(r, formula, None)
            } else {
                pretty_restriction(r)
            }
        }
        TheoryItem::Lemma(l) => {
            let proof = (pp.proof)(l);
            if pp.open_formulas {
                let formula = l.original_formula.as_ref().unwrap_or(&l.formula);
                pretty_lemma_formulas(l, formula, formula, &proof, pp.in_file)
            } else {
                pretty_lemma(l, &proof, pp.in_file)
            }
        }
        TheoryItem::Text(fc) => pretty_formal_comment(fc),
        TheoryItem::ConfigBlock(_) => String::new(),
        TheoryItem::Predicate(pr) => pretty_predicate(pr),
        TheoryItem::Macros(ms) => pretty_macros(ms),
        TheoryItem::Translation(t) => (pp.translation)(t),
    }
}

/// HS `prettyFormalComment` (lib/theory/src/Pretty.hs:19-21):
///
/// ```haskell
/// prettyFormalComment ""     body = multiComment_ [body]
/// prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"
/// ```
///
/// A user `section{* .. *}` / `text{* .. *}` item always carries a non-empty
/// header; the empty one only arises from a machine-injected comment
/// (`addComment`).
fn pretty_formal_comment(fc: &crate::theory::FormalComment) -> String {
    let (header, body) = fc;
    if header.is_empty() {
        format!("/*\n{}\n*/", body)
    } else {
        format!("{}{{*{}*}}", header, body)
    }
}

// =============================================================================
// Open theory — port of HS `prettyOpenTheory` (OpenTheory.hs:869-877) =
// `prettyTheory prettySignaturePure (const emptyDoc) prettyOpenProtoRule
// prettyProof prettyTranslationElement` (TheoryObject.hs:747-783).
// Differences from the closed print:
//   - the signature is the PARSE-time pure signature (same `prettyMaudeSig`
//     renderer — for a theory that has not been closed the two signatures
//     have equal content);
//   - `ppCache = const emptyDoc`: no "looping facts with injective instances"
//     comment and no intruder-rule section;
//   - rules render as `prettyOpenProtoRule` — the E rule and the manual
//     `variants (modulo AC)` blocks, with no loop breakers and no computed
//     variants (OpenTheory.hs:814-824);
//   - lemmas carry their stored proof skeleton (`prettyProof`), `by sorry`
//     when none was written;
//   - lemma and restriction rendering borrows their pre-macro formula for the
//     quoted formula, guarded characterization and safety test, and writes no
//     `expanded formula:` block;
//   - `TranslationItem`s render via `prettyTranslationElement`
//     (TheoryObject.hs:785-841): `builtin  <name>`, `function: …` typing
//     lines, `process:`/`let` blocks, `export:`, accountability lemmas and
//     `test` case tests;
//   - `--parse-only` prints no wellformedness block and no `Generated from:`
//     footer (Batch.hs:91-95 prints the doc alone), while the `-m` prints add
//     both.
// =============================================================================

/// HS `prettyOpenTheory` (OpenTheory.hs:869-877) as `--parse-only` emits it
/// (Batch.hs:91-95 `putStrLn . renderDoc`): the returned string carries NO
/// trailing newline, the caller's `println!` supplies `putStrLn`'s.
pub fn pretty_open_theory(thy: &Theory) -> String {
    let in_file = thy.in_file.as_str();
    let translation = |el: &TranslationElement| pretty_translation_element(el, in_file);
    let mut blocks = open_theory_blocks(thy, in_file, &translation);
    blocks.push("end".to_string());
    blocks.join("\n\n")
}

/// [`pretty_open_theory`] followed by the two trailing comment `TextItem`s
/// `withVersionAndReport` appends (TheoryLoader.hs:636-660): the
/// wellformedness block (`reportToDoc` — pass the pre-rendered
/// [`format_wf_block`] string) and the `Generated from:` version block.
/// `prettyOpenTheoryByModule`'s `spthy` and `spthytyped` arms
/// (TheoryLoader.hs:783-801) both land here; they differ only in the theory
/// VALUE, which `tamarin_sapic::type_theory::type_theory_env` has rewritten
/// for `spthytyped`.
pub fn pretty_open_theory_by_module(thy: &Theory, wf_block: &str, build: &BuildInfo) -> String {
    let in_file = thy.in_file.as_str();
    let translation = |el: &TranslationElement| pretty_translation_element(el, in_file);
    let mut blocks = open_theory_blocks(thy, in_file, &translation);
    blocks.push(wf_block.to_string());
    blocks.push(render_generated_from(build));
    blocks.push("end".to_string());
    blocks.join("\n\n")
}

/// HS `prettyOpenTranslatedTheory` (OpenTheory.hs:891-899) with the same two
/// trailing comment items: `prettyOpenTheoryByModule`'s `msr` arm, which is
/// `prettyOpenTranslatedTheory . removeTranslationItems`
/// (TheoryLoader.hs:786,789). `ppSap` is `emptyString`
/// (lib/theory/src/Pretty.hs:24-25), so translation items render nothing.
pub fn pretty_open_translated_theory_by_module(
    thy: &Theory,
    wf_block: &str,
    build: &BuildInfo,
) -> String {
    let in_file = thy.in_file.as_str();
    let translation = |_: &TranslationElement| String::new();
    let mut blocks = open_theory_blocks(thy, in_file, &translation);
    blocks.push(wf_block.to_string());
    blocks.push(render_generated_from(build));
    blocks.push("end".to_string());
    blocks.join("\n\n")
}

/// The header blocks of HS's one `prettyTheory` (TheoryObject.hs:757-765):
/// `vsep` over the theory name, the `configuration:` items, `begin`, the
/// equational-theory line comment, `ppSig`, the tactics, the `heuristic:` line
/// and `ppCache`, in that order.  `vsep = foldr ($--$) emptyDoc` skips empty
/// docs and puts exactly one blank line between the rest, so an entry that
/// would render empty is left out here and the caller joins with "\n\n".
/// `cache` is HS's `ppCache` applied to the theory's rule cache; an empty
/// string is HS's `const emptyDoc`.
fn theory_header_blocks<R>(thy: &Theory<R>, cache: &str) -> Vec<String> {
    let mut blocks: Vec<String> = Vec::new();
    blocks.push(format!("theory {}", thy.name));
    for item in &thy.items {
        if let TheoryItem::ConfigBlock(cfg) = item {
            // `prettyConfigBlock cb = text "configuration: " <> doubleQuotes
            // (text cb)` (TheoryObject.hs:921-922), filtered BEFORE `begin`
            // (line 759).
            blocks.push(format!("configuration: \"{}\"", cfg));
        }
    }
    blocks.push("begin".to_string());
    blocks.push("// Function signature and definition of the equational theory E".to_string());
    // `ppSig` = `prettySignaturePure = prettyMaudeSig . sigpMaudeSig`
    // (Theory/Model/Signature.hs:173-175): the `builtins:`/`functions:`/
    // `equations:` lines, single-newline separated, so the trailing newline
    // comes off and the vsep glue supplies the blank line.
    let sig_block = render_signature(&thy.signature);
    let sig_trimmed = sig_block.trim_end_matches('\n');
    if !sig_trimmed.is_empty() {
        blocks.push(sig_trimmed.to_string());
    }
    // `vcat $ map prettyTactic thyT` (TheoryObject.hs:763) — single-newline
    // joined tactic blocks; then the `heuristic:` line (line 764).  Both are
    // hoisted header fields in HS (never item-positioned), which `elaborate`
    // mirrors by collecting the parser's Tactic/Heuristic items.
    if !thy.tactic.is_empty() {
        let tblocks: Vec<String> = thy.tactic.iter().map(crate::tactic::render).collect();
        blocks.push(tblocks.join("\n"));
    }
    if !thy.heuristic.is_empty() {
        blocks.push(format!(
            "heuristic: {}",
            pretty_goal_rankings(&thy.heuristic)
        ));
    }
    if !cache.is_empty() {
        blocks.push(cache.to_string());
    }
    blocks
}

/// Shared block list of the open print: everything from `theory <name>` up to
/// (but not including) the final `end`, one `vsep` block per entry.
fn open_theory_blocks(
    thy: &Theory,
    in_file: &str,
    translation: &(dyn Fn(&TranslationElement) -> String + Sync),
) -> Vec<String> {
    // `ppCache = const emptyDoc` (OpenTheory.hs:872) — the open print has no
    // cache block.
    let mut blocks = theory_header_blocks(thy, "");
    blocks.extend(pretty_theory_items(
        &thy.items,
        &ItemPrinters {
            rule: &|r| crate::rule::pretty_open_proto_rule(r).render(),
            proof: &open_proof_body,
            translation,
            in_file,
            open_formulas: true,
        },
    ));
    blocks
}

/// HS `prettyProof` over a lemma's stored `ProofSkeleton`: a lemma written
/// without a proof carries the one-node `unproven ()` skeleton
/// (Theory/ProofSkeleton.hs:59-61), whose `Sorry Nothing` step prints
/// `by sorry`.
fn open_proof_body(lem: &crate::theory::Lemma) -> String {
    match &lem.proof {
        Some(tree) => {
            let mut body = String::new();
            pp_proof(tree, &mut body, 0);
            body
        }
        None => "by sorry".to_string(),
    }
}

/// HS `prettyTranslationElement` (TheoryObject.hs:785-841).  `in_file`
/// resolves a bare `o`/`O` ranking inside an accountability lemma's
/// `heuristic=` attribute (`defaultOracleNames`, System.hs:551-561).
fn pretty_translation_element(el: &TranslationElement, in_file: &str) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    match el {
        // `text "process" <> colon $-$ (nest 2 $ prettyProcess p)` (`:786`).
        TranslationElement::Process(pr) => Doc::text("process:")
            .above_g(open_process_doc(pr).nest(2))
            .render(),
        // `text "diffEquivLemma" <> colon $-$ (nest 2 $ prettyProcess p)` (`:787`).
        TranslationElement::DiffEquivLemma(pr) => Doc::text("diffEquivLemma:")
            .above_g(open_process_doc(pr).nest(2))
            .render(),
        // `text "equivLemma" <> colon $-$ (nest 2 p1) $$ (nest 2 p2)` (`:788`).
        TranslationElement::EquivLemma(p1, p2) => Doc::text("equivLemma:")
            .above_g(open_process_doc(p1).nest(2))
            .above(open_process_doc(p2).nest(2))
            .render(),
        // `text "let " <-> name <-> vars? <-> text "=" <-> nest 2 (prettyProcess body)`
        // (`:791-799`) — `text "let "` keeps its own trailing space, so `<->`
        // yields the oracle's `let  P …` double space.  `show` on a
        // `SapicLVar` is the LVar display plus an optional `:type` suffix
        // (Theory/Sapic/Term.hs:108-110).
        TranslationElement::ProcessDef(pd) => {
            let mut d = Doc::text("let ").beside_sp(Doc::text(pd.name.clone()));
            if let Some(vs) = &pd.vars {
                let shown: Vec<String> = vs.iter().map(ToString::to_string).collect();
                d = d.beside_sp(Doc::text(format!("({})", shown.join(","))));
            }
            d.beside_sp(Doc::text("="))
                .beside_sp(open_process_doc(&pd.body).nest(2))
                .render()
        }
        // `(text "builtin ") <-> (text s)` (`:843`) = two spaces.
        TranslationElement::SignatureBuiltin(name) => format!("builtin  {}", name),
        // The two `FunctionTypingInfo` cases (`:800-838`).
        TranslationElement::FunctionTypingInfo(fti) => pretty_function_typing_info(fti).render(),
        // `(text "export: ") <-> tag <-> nest 2 (doubleQuotes body)`
        // (`:839-842`) — all flat text chunks, so the layout is a plain
        // concatenation with `<->`'s single spaces (`export:  tag "body"`,
        // double space after the colon from `"export: "`'s own trailing
        // space).  The body is emitted verbatim (embedded newlines stay at
        // column 0 — HughesPJ cannot re-indent inside one `text` chunk).
        TranslationElement::ExportInfo { tag, body } => {
            format!("export:  {} \"{}\"", tag, body)
        }
        // `prettyAccLemma` (Items/AccLemmaItem.hs:47-57):
        //   kwLemma <-> name[attrs] <> colon $-$ nest 2 (
        //     text (intercalate ", " caseIdents) <-> "accounts for" $-$
        //     sep [doubleQuotes (prettySyntacticLNFormula aFormula)])
        // The `Pred` sugar survives: `liftedAddAccLemma` adds the lemma
        // verbatim (Theory/Text/Parser.hs:153-157).
        TranslationElement::AccLemma(al) => {
            let kw = Doc::text("lemma");
            let name_doc = Doc::text(al.name.clone());
            let header = if al.attributes.is_empty() {
                kw.beside_sp(name_doc).beside(Doc::text(":"))
            } else {
                let attr_docs = lemma_attr_docs(&al.attributes, in_file);
                let attrs_fsep = hpj::fsep(hpj::punctuate(Doc::text(","), attr_docs));
                let brackets = Doc::text("[").beside(attrs_fsep).beside(Doc::text("]"));
                kw.beside_sp(name_doc)
                    .beside_sp(brackets)
                    .beside(Doc::text(":"))
            };
            let mut out = header.render();
            out.push_str("\n  ");
            out.push_str(&al.case_test_idents.join(", "));
            out.push_str(" accounts for\n");
            out.push_str(&pf::doublequoted_nested_doc(
                pf::syntactic_lnformula_doc(&al.formula),
                2,
            ));
            out
        }
        // `prettyCaseTest` (Items/CaseTestItem.hs:39-45):
        //   text "test" <-> name <> colon $-$ nest 2 (sep [doubleQuotes f]).
        TranslationElement::CaseTest(ct) => {
            format!(
                "test {}:\n{}",
                ct.name,
                pf::doublequoted_nested_doc(pf::syntactic_lnformula_doc(&ct.formula), 2)
            )
        }
    }
}

/// HS `prettySapic'` (Theory/Sapic/Process.hs:485-502) as a Doc:
///
/// ```haskell
/// prettySapic' ppRR p
///     | (ProcessNull _) <- p = text "0"
///     | (ProcessComb c _ pl pr) <- p = r pl <-> text (prettySapicComb c) <-> r pr
///     | (ProcessAction Rep _ p') <- p = ppAct Rep <> parens (r p')
///     | (ProcessAction a@ProcessCall {} _ _ ) <- p = ppAct a
///     | (ProcessAction a _ (ProcessNull _)) <- p = ppAct a
///     | (ProcessAction a _ p'@ProcessComb {}) <- p = ppAct a <> semi $-$ nest 1 (parens (r p'))
///     | (ProcessAction a _ p') <- p = ppAct a <> semi $-$ r p'
/// ```
///
/// The action/combinator TEXT comes from [`crate::pretty_sapic::pretty_sapic_top_level`]
/// (the byte-faithful `prettySapicTopLevel'` port, which appends `";"` to a
/// non-`!` action — stripped here, since `prettySapic'` adds `semi` itself
/// only on the continuation cases).  This reproduces upstream's layout
/// verbatim, including the surprising `then-branch if-cond else-branch`
/// operand order of `ProcessComb` (oracle-verified).
///
/// `prettyProcess = prettySapic = prettySapic' rulePrinter`
/// (TheoryObject.hs:851-852, Print.hs:52-53), so an embedded MSR renders its
/// premises through `unextractMatchingVariables mv` — every pattern-match
/// variable keeps its `=` marker.  This is the printer that
/// [`crate::pretty_sapic::pretty_sapic_top_level`] selects; the
/// `process="..."` rule attribute uses the other one.
fn open_process_doc(pr: &crate::sapic::PlainProcess) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{parens, Doc};
    use crate::sapic::{Process, SapicAction};
    // `prettySapicTopLevel'` text for this node, without the trailing `;` it
    // appends to non-`!` actions (no action string otherwise ends in ';').
    let node_text = |p: &crate::sapic::PlainProcess| -> String {
        let s = crate::pretty_sapic::pretty_sapic_top_level(p);
        s.strip_suffix(';').map(str::to_string).unwrap_or(s)
    };
    match pr {
        Process::Null(_) => Doc::text("0"),
        Process::Comb(_, _, pl, pr2) => open_process_doc(pl)
            .beside_sp(Doc::text(node_text(pr)))
            .beside_sp(open_process_doc(pr2)),
        Process::Action(SapicAction::Rep, _, p2) => {
            Doc::text("!").beside(parens(open_process_doc(p2)))
        }
        // A `ProcessCall`'s continuation is NEVER printed (Theory/Sapic/Process.hs:496).
        Process::Action(SapicAction::ProcessCall(_, _), _, _) => Doc::text(node_text(pr)),
        Process::Action(_, _, p2) => match p2.as_ref() {
            Process::Null(_) => Doc::text(node_text(pr)),
            Process::Comb(_, _, _, _) => Doc::text(format!("{};", node_text(pr)))
                .above_g(parens(open_process_doc(p2)).nest(1)),
            _ => Doc::text(format!("{};", node_text(pr))).above_g(open_process_doc(p2)),
        },
    }
}

// =============================================================================
// Interactive-web snippet reuse (Web/Theory.hs `messageSnippet` /
// `rulesSnippet` / `htmlSource`).  These re-expose the byte-faithful
// `--prove` printers so the web handler (`tamarin-server`) renders the same
// text the CLI does — the web handler only adds the surrounding HTML tags.
// =============================================================================

/// HS `prettySignatureWithMaude sig = prettyMaudeSig (mhMaudeSig …)`
/// (Signature.hs) — the same signature block the theory body prints
/// (`render_signature`).  Used by the web message page's "Signature" section.
pub fn web_signature_block(sig: &tamarin_term::maude_sig::MaudeSig) -> String {
    // `render_signature` appends a trailing `\n` after each block for the
    // `--prove` theory-body layout (where more theory items follow).  HS's
    // `prettySignatureWithMaude` is one self-contained Doc with no trailing
    // blank, and `messageSnippet` wraps just that Doc: strip the trailing
    // newline so `</p>` glues directly after the last signature line.
    render_signature(sig).trim_end_matches('\n').to_string()
}

/// HS `ppPrem = nest 2 (doubleQuotes (prettyGoal th._cdGoal))`
/// (Web/Theory.hs:820-845, see line 830).  `doubleQuotes d = char '"' <> d <> char '"'` (the
/// quotes entity-escape to `&quot;` under the active HtmlDoc guard); the
/// `nest 2` indents wrapped continuation lines.  Rendered as ONE Doc so a long
/// source goal wraps exactly as HS `renderHtmlDoc` (the per-case `<p>` prem).
fn web_source_prem_doc(g: &crate::constraint::constraints::Goal) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    Doc::text("\"")
        .beside(solve_goal_to_doc(g))
        .beside(Doc::text("\""))
        .nest(2)
}

/// HS per-case `withTag "p" [] ppPrem` premise (Web/Theory.hs:820-845, see line 837): the whole
/// `<p>` is built as ONE Doc via `with_tag`, so the `nest 2` indents only
/// WRAPPED continuation lines — the `<p>` tag is zero-width and the prem sits
/// BESIDE it, so line 1 carries no leading indent (a standalone `.render()`
/// WOULD emit the nest on line 1, which HS does not).  Returns `<p>…</p>`.
pub fn web_pretty_source_prem(g: &crate::constraint::constraints::Goal) -> String {
    crate::pretty_hpj::with_tag("p", &[], web_source_prem_doc(g)).render()
}

/// HS `ppHeader = hsep [text "Sources of" <-> ppPrem, parens (nCases <->
/// text "cases")]` (Web/Theory.hs:832-834).  Built and rendered as ONE Doc so
/// the goal wraps at the web width WITH the `Sources of ` prefix offset — the
/// `<h2>` source header (`n_cases` is the number of cases).
pub fn web_pretty_source_header(
    g: &crate::constraint::constraints::Goal,
    n_cases: usize,
) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    let left = Doc::text("Sources of").beside_sp(web_source_prem_doc(g));
    let right = hpj::parens(Doc::text(n_cases.to_string()).beside_sp(Doc::text("cases")));
    hpj::hsep(vec![left, right]).render()
}

/// HS `rulesSnippet`'s `map prettyClosedProtoRule protoRules`
/// (Web/Theory.hs:892-904, see line 900) — one rendered rule string per
/// closed protocol rule, in source order, for the interactive `main/rules`
/// page.
pub fn web_proto_rules(thy: &Theory) -> Vec<String> {
    thy.rules()
        .flat_map(|r| {
            crate::theory::closed_rules_ac(r)
                .into_iter()
                .map(|ac| crate::rule::pretty_closed_proto_rule(&ac, r.rule_e()).render())
                .collect::<Vec<_>>()
        })
        .collect()
}

/// HS `rulesSnippet`'s `vsep $ map prettyRestriction $ theoryRestrictions thy`
/// (Web/Theory.hs:892-904, see line 901) — one rendered restriction string
/// per restriction, in source order.
pub fn web_restrictions(thy: &Theory) -> Vec<String> {
    thy.restrictions().map(pretty_restriction).collect()
}

/// HS `rulesSnippet`'s first `ppWithHeader "Macros"`
/// (Web/Theory.hs:892-904, see line 895-897): the `macros:` block, or nothing
/// at all when the theory declares none.
pub fn web_macros(thy: &Theory) -> Option<String> {
    let macros: Vec<crate::theory::LNMacro> = thy.macros().cloned().collect();
    if macros.is_empty() {
        None
    } else {
        Some(pretty_macros(&macros))
    }
}

/// Render HS `ppInjectiveFactInsts` (ClosedTheory.hs:413-418):
///
/// ```text
/// /*
/// looping facts with injective instances:
///   T1/n1, T2/n2, ...
/// */
/// ```
///
/// HS:
/// ```haskell
/// multiComment $ sep
///   [ text "looping facts with injective instances:"
///   , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]
/// ```
/// where `multiComment d = comment $ fsep [text "/*", d, text "*/"]`
/// (Theory/Text/Pretty.hs:102-103) and `fsepList pp = fsep . punctuate comma . map pp`
/// (Theory/Text/Pretty.hs:88-89).
///
/// Emits the empty string when no fact tags are injective.  Computes
/// the set on demand from the elaborated rules + reducible function
/// symbols — the same call `ProofContext::new` makes through `new_impl`
/// (`constraint/solver/context.rs`).
fn render_injective_fact_insts(elab: &Theory) -> String {
    use crate::fact::{FactTag, Multiplicity};
    use crate::pretty_hpj::{self as hpj, punctuate, Doc};
    let proto_rules: Vec<&crate::rule::ProtoRuleE> = elab.rules().map(|r| &r.rule).collect();
    let mut tags = crate::tools::injective_fact_instances::simple_injective_fact_instances(
        &proto_rules,
        &elab.signature.reducible_fun_syms_fast,
    );
    // HS `closeRuleCache` (CloseRule.hs:417-420): union the FORCED injective facts
    // (`setforcedInjectiveFacts {L_PureState, L_CellLocked}`,
    // lib/sapic/src/Sapic.hs:84) when
    // the state-channel optimisation is on.
    if elab.options.state_channel_opt() {
        tags = crate::tools::injective_fact_instances::union_forced_injective_fact_instances(
            tags,
            &crate::tools::injective_fact_instances::pure_state_forced_fact_tags(),
        );
    }
    if tags.is_empty() {
        return String::new();
    }
    // HS `showFactTagArity` (Theory/Model/Fact.hs:556-557): persistent `!`-prefix + name
    // + `/` + arity.
    let label = |tag: &FactTag| -> String {
        let prefix = match tag {
            FactTag::Proto(Multiplicity::Persistent, _, _) => "!",
            _ => "",
        };
        format!(
            "{}{}/{}",
            prefix,
            crate::fact::fact_tag_name(tag),
            crate::fact::fact_tag_arity(tag)
        )
    };
    let tag_docs: Vec<Doc> = tags.iter().map(|(t, _)| Doc::text(label(t))).collect();
    // fsepList (text . showFactTagArity) (map fst tags)
    let list_doc = hpj::fsep(punctuate(Doc::text(","), tag_docs));
    // sep [text "looping facts...", nest 2 list_doc]
    let inner = hpj::sep(vec![
        Doc::text("looping facts with injective instances:"),
        list_doc.nest(2),
    ]);
    // multiComment inner = comment $ fsep [text "/*", inner, text "*/"]
    let doc = hpj::fsep(vec![Doc::text("/*"), inner, Doc::text("*/")]);
    doc.render()
}

// =============================================================================
// Signature
// =============================================================================

pub(crate) fn render_signature(sig: &tamarin_term::maude_sig::MaudeSig) -> String {
    let mut out = String::new();

    // builtins: ...  (only if any enabled)
    let mut builtins: Vec<&str> = Vec::new();
    if sig.enable_dh {
        builtins.push("diffie-hellman");
    }
    if sig.enable_bp {
        builtins.push("bilinear-pairing");
    }
    if sig.enable_mset {
        builtins.push("multiset");
    }
    if sig.enable_nat {
        builtins.push("natural-numbers");
    }
    if sig.enable_xor {
        builtins.push("xor");
    }
    if !builtins.is_empty() {
        // HS renders builtins via the same `ppNonEmptyList'` as functions:
        // `(keyword_ "builtins:" <->) . fsep . punctuate comma`
        // (Term/Maude/Signature.hs:252-263, see lines 261,263) — so the list wraps through
        // the HughesPJ engine, not a flat join.
        out.push_str(&wrap_with_lead("builtins:", &builtins));
        out.push('\n');
    }

    // functions: ...
    let funs = render_fun_syms(sig);
    if !funs.is_empty() {
        out.push_str(&wrap_with_lead("functions:", &funs));
        out.push('\n');
    }

    // equations: ...
    let eqs = render_equations(sig);
    if !eqs.is_empty() {
        let key = if sig.eq_convergent {
            "equations [convergent]:"
        } else {
            "equations:"
        };
        // HS uses `sep [hdr, nest 2 (punctuate comma ds)]` for the
        // equations list — yields `hdr\n    eq1,\n    eq2,...` when
        // multiple equations.
        out.push_str(&sep_block_with_lead(key, &eqs));
        out.push('\n');
    }

    out
}

/// Render the function symbol list: HS `prettyMaudeSigExcept` with an empty
/// exclusion set, i.e. the NoEq symbols in `S.toList` (BTreeSet) order
/// followed by the user-defined AC symbols, each with its space-prefixed
/// attribute list (`h/1 [destructor]`) and NDC attributes.
fn render_fun_syms(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<String> {
    sig.pretty_fun_syms_except(&std::collections::BTreeSet::new())
}

/// HS `prettyTranslationElement`, the two `FunctionTypingInfo` cases
/// (TheoryObject.hs:800-819 for a user-defined AC symbol, 820-838 for a free
/// one): the `function: f(t1, t2): t` typing line of a SAPIC theory, followed by
/// the symbol's attributes.
///
/// Intentionally retained: faithful mirror of those two cases, exercised only
/// by the unit tests below.  RS never produces
/// `TranslationElement::FunctionTypingInfo`.  In HS these items only reach a
/// printer through the OPEN theory (`typeTheoryEnv`
/// rebuilds them from the typing environment, Typing.hs:204-226, see line 210);
/// `removeTranslationItems` strips every translation item before a theory is
/// closed, so `--prove` output never carries them.  This is the faithful printer
/// for whenever open-theory rendering is ported.
///
/// SPACING.  HS glues the parts with `<->` = HughesPJ `<+>`, whose `text ""`
/// is a zero-width run rather than `empty`, so an ABSENT attribute still
/// contributes its separating space: a public constructor with no NDC state
/// renders `function: f (Any) : Any` plus three trailing spaces.  The
/// attribute strings themselves also carry a LEADING space in HS, which is why
/// a present `[private]` ends up two spaces from the out type.  `Doc::text_hs`
/// is the constructor that keeps an empty run present.
pub fn pretty_function_typing_info(fti: &crate::theory::SapicFunSym) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{fsep, parens, punctuate, Doc};
    use tamarin_term::function_symbols::{Constructability, NdcState, Privacy, UserDefinedSym};

    // HS `printType = maybe (text defaultSapicTypeS) text`.
    fn print_type(t: &crate::sapic::SapicType) -> Doc {
        match t {
            Some(ty) => Doc::text(ty),
            None => Doc::text(crate::sapic::DEFAULT_SAPIC_TYPE),
        }
    }
    fn show_priv(p: Privacy) -> &'static str {
        match p {
            Privacy::Private => " [private]",
            Privacy::Public => "",
        }
    }
    fn show_const(c: Constructability) -> &'static str {
        match c {
            Constructability::Constructor => "",
            Constructability::Destructor => " [destructor]",
        }
    }
    fn show_ndc(n: NdcState) -> &'static str {
        match n {
            NdcState::NotNdc => "",
            NdcState::IsNdc => " [NDC]",
            NdcState::IsNdcDiff => " [NDC-Diff]",
            NdcState::IsNdcBoth => " [NDC,NDC-Diff]",
        }
    }

    let (privacy, constructability, ndc, is_ac) = match fti.sym {
        UserDefinedSym::NoEqUser(s) => (s.privacy, s.constructability, s.ndc, false),
        UserDefinedSym::AcFctUser(s) => (s.privacy, s.constructability, s.ndc, true),
    };
    let name = String::from_utf8_lossy(fti.sym.name());
    let args: Vec<Doc> = fti.arg_types.iter().map(print_type).collect();
    let mut d = Doc::text("function:")
        .beside_sp(Doc::text(name))
        .beside_sp(parens(fsep(punctuate(Doc::text(","), args))))
        .beside_sp(Doc::text(":"))
        .beside_sp(print_type(&fti.out_type));
    // The AC marker sits between the out type and the privacy attribute.
    if is_ac {
        d = d.beside_sp(Doc::text_hs(" [AC]"));
    }
    d = d.beside_sp(Doc::text_hs(show_priv(privacy)));
    d = d.beside_sp(Doc::text_hs(show_const(constructability)));
    d.beside_sp(Doc::text_hs(show_ndc(ndc)))
}

#[cfg(test)]
mod open_item_tests {
    use super::*;
    use crate::sapic::{Process, ProcessParsedAnnotation};
    use crate::theory::{ProcessDef, SapicFunSym, Theory, TheoryItem, TranslationElement};
    use tamarin_term::function_symbols::{Constructability, NdcState, NoEqSym, Privacy};

    fn null_proc() -> crate::sapic::PlainProcess {
        Process::Null(ProcessParsedAnnotation::empty())
    }

    fn typing_info(name: &'static str) -> SapicFunSym {
        SapicFunSym {
            sym: tamarin_term::function_symbols::UserDefinedSym::NoEqUser(NoEqSym {
                name: name.as_bytes(),
                arity: 1,
                privacy: Privacy::Public,
                constructability: Constructability::Constructor,
                ndc: NdcState::NotNdc,
            }),
            arg_types: vec![None],
            out_type: None,
        }
    }

    fn theory_with(items: Vec<TheoryItem>) -> Theory {
        let mut thy = Theory::new("T", tamarin_term::maude_sig::minimal_maude_sig(false));
        thy.items = items;
        thy
    }

    /// `msr`: `prettyOpenTranslatedTheory` prints every translation item
    /// through `emptyString` (OpenTheory.hs:891-899); every other item is kept
    /// and rendered.
    #[test]
    fn the_translated_theory_prints_no_translation_item() {
        let thy = theory_with(vec![
            TheoryItem::Translation(TranslationElement::SignatureBuiltin("multiset".to_string())),
            TheoryItem::Translation(TranslationElement::FunctionTypingInfo(typing_info("h"))),
            TheoryItem::Translation(TranslationElement::Process(null_proc())),
            TheoryItem::Translation(TranslationElement::ProcessDef(ProcessDef {
                name: "P".to_string(),
                vars: None,
                body: null_proc(),
            })),
            TheoryItem::Translation(TranslationElement::EquivLemma(null_proc(), null_proc())),
            TheoryItem::Translation(TranslationElement::DiffEquivLemma(null_proc())),
            TheoryItem::Translation(TranslationElement::ExportInfo {
                tag: "queries".to_string(),
                body: "q".to_string(),
            }),
            TheoryItem::Text((String::new(), "keep".to_string())),
        ]);
        let blocks = open_theory_blocks(&thy, "f.spthy", &|_: &TranslationElement| String::new());
        assert_eq!(
            blocks.last().map(String::as_str),
            Some("/*\nkeep\n*/"),
            "only the formal comment survives: {blocks:?}"
        );
    }

    /// `prettyTranslationElement` (TheoryObject.hs:785-843) on the item kinds
    /// whose text is a plain concatenation.
    #[test]
    fn translation_elements_render_their_headers() {
        assert_eq!(
            pretty_translation_element(
                &TranslationElement::SignatureBuiltin("multiset".to_string()),
                "f.spthy"
            ),
            "builtin  multiset"
        );
        assert_eq!(
            pretty_translation_element(
                &TranslationElement::ExportInfo {
                    tag: "queries".to_string(),
                    body: "q".to_string(),
                },
                "f.spthy"
            ),
            "export:  queries \"q\""
        );
        assert_eq!(
            pretty_translation_element(&TranslationElement::Process(null_proc()), "f.spthy"),
            "process:\n  0"
        );
        assert_eq!(
            pretty_translation_element(
                &TranslationElement::ProcessDef(ProcessDef {
                    name: "P".to_string(),
                    vars: Some(Vec::new()),
                    body: null_proc(),
                }),
                "f.spthy"
            ),
            "let  P () = 0"
        );
    }
}

#[cfg(test)]
mod function_typing_info_tests {
    use crate::theory::SapicFunSym;
    use tamarin_term::function_symbols::{
        AcFctSym, Constructability, NdcState, NoEqSym, Privacy, UserDefinedSym,
    };

    fn render(sym: UserDefinedSym, arg_types: Vec<Option<String>>) -> String {
        super::pretty_function_typing_info(&SapicFunSym {
            sym,
            arg_types,
            out_type: None,
        })
        .render()
    }

    /// A public constructor with no NDC state: the three absent attributes
    /// still contribute their `<+>` separator, so the line carries three
    /// trailing spaces.
    #[test]
    fn free_symbol_absent_attributes_keep_their_spaces() {
        let sym = NoEqSym::new(
            b"f".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        assert_eq!(
            render(UserDefinedSym::NoEqUser(sym), vec![None, None]),
            "function: f (Any, Any) : Any   "
        );
    }

    /// Declared argument types print verbatim, and each present attribute
    /// carries its own leading space on top of the separator.
    #[test]
    fn free_symbol_with_types_and_every_attribute() {
        let sym = NoEqSym::new(
            b"h".to_vec(),
            1,
            Privacy::Private,
            Constructability::Destructor,
        )
        .with_ndc(NdcState::IsNdcBoth);
        assert_eq!(
            render(UserDefinedSym::NoEqUser(sym), vec![Some("Key".to_string())]),
            "function: h (Key) : Any  [private]  [destructor]  [NDC,NDC-Diff]"
        );
    }

    /// The `[AC]` marker sits between the out type and the privacy attribute.
    #[test]
    fn user_ac_symbol_carries_the_ac_marker() {
        let sym = AcFctSym::new(
            b"g".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::IsNdc,
        );
        assert_eq!(
            render(UserDefinedSym::AcFctUser(sym), vec![None, None]),
            "function: g (Any, Any) : Any  [AC]    [NDC]"
        );
    }
}

/// Render the equation list.  Each `CtxtStRule` has an LHS term and an
/// RHS term (after reading positions/term out of `StRhs`).  HS renders
/// `prettyCtxtStRule $ S.toList (stRules sig)` (Term/Maude/Signature.hs:252-259, see line 258),
/// i.e. equations in `S.toList` order.  `CtxtStRule` derives structural `Ord`,
/// so we emit them in the `st_rules` `BTreeSet` iteration order, which mirrors
/// HS's `S.toList` exactly.  We must NOT re-sort by the rendered pretty-string,
/// since that diverges from the structural (term-tree) order (e.g. AC products
/// pretty-print with a leading `(`, `exp` as infix `a^b`).
///
/// Each side is returned as a HughesPJ `Doc` (not a flat string) so that wide
/// function applications wrap at the ribbon width exactly as HS
/// `prettyCtxtStRule`/`prettyLNTerm` (SubtermRule.hs:123-126, Term/Term.hs:326-327)
/// — the `ppFun f ts = text (f++"(") <> fsep (punctuate comma …) <> ")"` `fsep`
/// breaks at argument boundaries when the term overruns.  Each side is the
/// `LNTerm` printed by [`pretty_nterm`], HS `prettyLNTerm = prettyNTerm`
/// (LTerm.hs:930-935#prettyNTerm).
fn render_equations(
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<(crate::pretty_hpj::Doc, crate::pretty_hpj::Doc)> {
    let mut items = Vec::new();
    for r in &sig.st_rules {
        items.push((pretty_nterm(&r.lhs), pretty_nterm(&r.rhs.term)));
    }
    items
}

/// Format the `/* WARNING: ... */` or `/* All wellformedness checks
/// were successful. */` block that goes BETWEEN the source body and
/// the analysis summary.  Mirrors HS's `prettyWfErrorReport`
/// (Wellformedness.hs:118-125).
///
/// Each `WfError.message` is expected to carry the FULL HS-style block
/// for its topic: `Title\n=====\n\n<intro>\n<body>` — pre-formatted with
/// the exact bytes HS emits, including trailing spaces from HS's
/// `text ""` markers.  Consecutive `WfError`s with the same topic are
/// merged into one block (the per-clash bodies concatenated).  Topic
/// groups are separated by blank lines.
///
/// Shared by the `--prove` CLI (`run.rs`) and the interactive web server
/// (`source`/`message` routes) so both render the wellformedness comment
/// byte-identically.  The empty-report case returns exactly
/// `"/* All wellformedness checks were successful. */"`, so no-warning
/// theories stay byte-for-byte unchanged on both paths.
pub fn format_wf_block(report: &[crate::wellformedness::WfError]) -> String {
    if report.is_empty() {
        return "/* All wellformedness checks were successful. */".to_string();
    }
    let mut out = String::new();
    out.push_str("/*\nWARNING: the following wellformedness checks failed!\n\n");
    out.push_str(&render_wf_error_report(report));
    // Trim trailing blank lines but keep a single newline before `*/`.
    while out.ends_with("\n\n") {
        out.pop();
    }
    out.push_str("*/");
    out
}

/// Bare `prettyWfErrorReport` rendering (Wellformedness.hs:118-125) —
/// the grouped topic blocks WITHOUT the `/* WARNING ... */` comment
/// wrapper.  Shared by `format_wf_block` (batch theory output) and the
/// interactive server's `ppInteractive` console echo of the report at
/// theory-load time (Web/Dispatch.hs:149-209, see line 187,200-209).
pub fn render_wf_error_report(report: &[crate::wellformedness::WfError]) -> String {
    let mut out = String::new();
    // HS `groupOn fst = groupBy ((==) `on` fst)` (Extension/Prelude.hs:96-97)
    // splits the report into runs of CONSECUTIVE same-topic entries, so a topic
    // that reappears after an intervening one opens a SECOND group carrying its
    // own header.  Grouping every entry of a topic together instead would merge
    // those runs and drop the repeat.
    let mut groups: Vec<(&str, Vec<&str>)> = Vec::new();
    for e in report {
        match groups.last_mut() {
            Some((topic, msgs)) if *topic == e.topic => msgs.push(&e.message),
            _ => groups.push((&e.topic, vec![&e.message])),
        }
    }
    for (i, (topic, msgs)) in groups.iter().enumerate() {
        let topic = *topic;
        if i > 0 {
            out.push('\n');
        }
        // HS `prettyWfErrorReport` (Wellformedness.hs:118-125) groups by
        // topic and renders each group as
        //   `text topic $-$ (nest 2 . vcat . intersperse (text "") $ bodies)`
        // — the underlineTopic header ONCE per group, then the 2-space-nested
        // bodies separated by a 2-space blank line.  Most RS checks already
        // pre-render the FULL block (header + indent) into a per-topic
        // message, and the default path below concatenates those (dropping
        // the header copies past the first, which HS never repeats).
        //
        // Some checks emit one HEADER-LESS body per offending rule (so the
        // summary's `length rep` WARNING count stays HS-faithful,
        // Batch.hs:87-316, see line 245), all sharing one topic.  These are assembled HS-style
        // (`prettyWfErrorReport`, Wellformedness.hs:118-125): the topic header
        // (+ any "reasons" preamble that HS folds into the topic string) ONCE,
        // then the per-rule bodies joined by the `intersperse (text "")`
        // 2-space blank separator.  Other topics keep baking their full block
        // into each message (default path below).
        if let Some((preamble, nest_bodies)) = wf_headerless_preamble(topic) {
            out.push_str(&preamble);
            let bodies: Vec<String> = msgs
                .iter()
                .map(|m| {
                    if nest_bodies {
                        nest_wf_body(m)
                    } else {
                        (*m).to_string()
                    }
                })
                .collect();
            out.push_str(&bodies.join("\n  \n"));
            out.push('\n');
        } else {
            // The bodies here bake the header in, one copy per entry, so a
            // multi-entry group sheds every copy but the first and falls back
            // on the group's own `intersperse (text "")` separator.
            let header = crate::wellformedness::underline_topic(topic);
            for (j, m) in msgs.iter().enumerate() {
                let mut body: &str = m;
                if j > 0 {
                    match body.strip_prefix(header.as_str()) {
                        // Shed the repeated header AND the blank line that
                        // `ppTopic`'s `$-$` puts between it and the body.
                        Some(rest) => {
                            out.push_str("  \n");
                            body = rest.strip_prefix('\n').unwrap_or(rest);
                        }
                        None => out.push('\n'),
                    }
                }
                out.push_str(body);
                if !body.ends_with('\n') {
                    out.push('\n');
                }
            }
        }
    }
    out
}

/// For the WF topics whose checks emit one header-less body per finding,
/// return the byte-exact preamble that `prettyWfErrorReport` prints ONCE
/// before the group's bodies: the `underlineTopic` header, plus the blank
/// line HS's `$-$`/topic-string folds in, plus (for the sort-clash topic)
/// the "Possible reasons" paragraph that HS appends to the topic string
/// (Wellformedness.hs:258-273).  Returns `None` for the topics that bake
/// their full block into each message (default path).
///
/// The `bool` says whether the bodies ALSO arrive without the `nest 2`
/// indent that `ppTopic` applies to every body of a group
/// (Wellformedness.hs:118-125, see line 125) — `true` means the renderer
/// supplies it.
fn wf_headerless_preamble(topic: &str) -> Option<(String, bool)> {
    use crate::wellformedness::underline_topic;
    match topic {
        // SAPIC-process wellformedness errors (HS `toWfErrorReport`,
        // Warnings.hs:23-26).  Unlike the other topics, HS does NOT underline
        // this one — `prettyWfErrorReport` renders it as a bare `text topic`
        // (Wellformedness.hs:118-125, see line 124).  So the per-error bodies (each
        // `"  Variable bound twice: x."`) sit directly under a plain header.
        "Wellformedness-error in Process" => Some((format!("{topic}\n"), false)),
        // These five bake the `nest 2` into their own bytes — the `Doc` fills
        // via `WfError::filled`, `multRestrictedReport'`
        // (Wellformedness.hs:1047-1064) via `crate::wellformedness::mult`.
        // Their bodies wrap at `sep`/`fsep` points that depend on the absolute
        // column, so the indent has to be inside the Doc the HughesPJ engine
        // lays out, not applied to the rendered lines afterwards.
        "Unbound variables"
        | "Reserved names"
        | "Special facts"
        | "Nat Sorts"
        | "Multiplication restriction of rules"
        | "Fresh public constants" => Some((format!("{}\n", underline_topic(topic)), false)),
        // HS `freshFactArguments'` (Wellformedness.hs:569-576, see line 574)
        // and `lemmaAttributeReport` (Wellformedness.hs:924-932, see lines
        // 930-931) pair the underlined topic with a body that carries neither
        // the header nor the `nest 2` indent, so both come from here.
        "Fr facts must only use a fresh- or a msg-variable" | "Lemma annotations" => {
            Some((format!("{}\n", underline_topic(topic)), true))
        }
        "Variable with mismatching sorts or capitalization" => Some((
            format!(
                "{}\nPossible reasons:\n\
                 1. Identifiers are case sensitive, i.e.,\
                 'x' and 'X' are considered to be different.\n\
                 2. The same holds for sorts:, \
                 i.e., '$x', 'x', and '~x' are considered to be different.\n\n",
                underline_topic(topic)
            ),
            false,
        )),
        _ => None,
    }
}

/// Apply `prettyWfErrorReport`'s per-group `nest 2` to a body that arrives
/// without it: HS `nest` shifts EVERY line of the nested Doc, blank lines
/// included (Wellformedness.hs:118-125, see line 125).
fn nest_wf_body(body: &str) -> String {
    body.lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// HS `ppNonEmptyList' name pp xs = (keyword_ name <->) . fsep $
/// punctuate comma (map pp xs)` (Term/Maude/Signature.hs:261-263).
/// `<->` is HughesPJ `<+>` (beside-with-space), and `fsep` is the
/// fill-paragraph combinator, so the wrap decisions must come from the
/// ported HughesPJ Doc engine (LINE_LENGTH=110, RIBBON=73) — not a
/// hand-rolled greedy fill at a guessed width.  Route through `pretty_hpj`.
fn wrap_with_lead<S: AsRef<str>>(lead: &str, items: &[S]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() {
        return String::new();
    }
    let docs: Vec<Doc> = items.iter().map(Doc::text).collect();
    let body = hpj::fsep(hpj::punctuate(Doc::char(','), docs));
    // HS `ppNonEmptyList' name = (keyword_ name <->) . fsep`
    // (Term/Maude/Signature.hs:252-263, see line 261) — the `builtins:`/`functions:` lead is a
    // keyword.  `keyword_` is the identity in plain mode, so `--prove` is
    // unchanged.
    hpj::keyword_(lead).beside_sp(body).render()
}

/// HS `equations:` layout (Term/Maude/Signature.hs:256-258):
///   `P.sep ( keyword_ "equations:" : map (P.nest 2) ds )`
/// where `ds = P.punctuate P.comma (map prettyCtxtStRule rules)` — i.e. the
/// comma is appended to the END of each equation doc (all but the last), and
/// each resulting doc is `nest 2`'d, then `sep`-joined.
///
/// Each equation doc is itself (SubtermRule.hs:123-126):
///   `prettyCtxtStRule r = sep [ nest 2 (prettyLNTerm lhs)
///                             , operator_ "=" <-> prettyLNTerm rhs ]`
/// — so the LHS carries an *inner* `nest 2`.  When the outer `sep` breaks and
/// lays each equation on its own line at indent 2, the inner `nest 2` adds a
/// further 2, yielding the 4-space indent HS emits.  Reproducing that requires
/// the structured doc, not a pre-joined `lhs = rhs` string.  Route through the
/// ported HughesPJ engine so the break decision and indentation are HS-exact.
///
/// `items` carries the LHS/RHS as already-built term `Doc`s (HS `prettyLNTerm`)
/// so the inner function-application `fsep` wrapping survives — passing flat
/// strings would defeat the engine and emit over-long single lines for wide
/// equations (e.g. BP `idverify(idsign(…), m, IBPub(…))`).
fn sep_block_with_lead(
    lead: &str,
    items: &[(crate::pretty_hpj::Doc, crate::pretty_hpj::Doc)],
) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() {
        return String::new();
    }
    let n = items.len();
    let mut docs: Vec<Doc> = Vec::with_capacity(n + 1);
    // HS `keyword_ "equations:"` / `keyword_ "equations [convergent]:"`
    // (Term/Maude/Signature.hs:256-257).  Identity in plain mode.
    docs.push(hpj::keyword_(lead));
    for (i, (lhs, rhs)) in items.iter().enumerate() {
        // prettyCtxtStRule: sep [ nest 2 lhs, operator_ "=" <-> rhs ]
        let lhs_doc = lhs.clone().nest(2);
        let eq_doc = hpj::operator_("=").beside_sp(rhs.clone());
        let mut d = hpj::sep(vec![lhs_doc, eq_doc]);
        if i + 1 < n {
            d = d.beside(Doc::char(','));
        }
        docs.push(d.nest(2));
    }
    hpj::sep(docs).render()
}

/// HughesPJ default-`style` line length used by the oracle/tactic
/// ranking path.  HS `render = P.render` (`Text.PrettyPrint.Class`
/// re-exports `P.render` from HughesPJ — Text/PrettyPrint/Class.hs:77-78), and `P.render`
/// uses HughesPJ's default `style { lineLength = 100 }`.  This is
/// DISTINCT from the `--prove` DISPLAY width (`pretty_hpj::LINE_LENGTH`
/// = 110, set by `defaultStyle { lineLength = lineWidth }` in
/// Console.hs:242-243,398-399).
const ORACLE_LINE_LENGTH: usize = 100;

/// HughesPJ default-`style` ribbon length used by the oracle/tactic
/// path: `ribbonsPerLine = 1.5` → `round(100/1.5) = round(66.67) = 67`.
/// DISTINCT from the display ribbon `pretty_hpj::RIBBON` = 73.
const ORACLE_RIBBON: usize = 67;

// =============================================================================
// Lemma
// =============================================================================

/// HS `prettyLemma ppPrf` (lib/theory/src/Lemma.hs:116-141): the `lemma
/// <name> [attrs]:` header, the `<quant> "<formula>"` line, the `/* guarded
/// formula … */` comment block and the injected proof body.  The header line
/// quotes `fromMaybe expandedFormula ogFormula` (`:121`) and the guarded
/// block converts `_lFormula` (`:125`).
fn pretty_lemma(lem: &crate::theory::Lemma, proof: &str, in_file: &str) -> String {
    let original = lem.original_formula.as_ref().unwrap_or(&lem.formula);
    pretty_lemma_formulas(lem, original, &lem.formula, proof, in_file)
}

fn pretty_lemma_formulas(
    lem: &crate::theory::Lemma,
    displayed: &crate::formula::LNFormula,
    guarded: &crate::formula::LNFormula,
    proof: &str,
    in_file: &str,
) -> String {
    let mut out = lemma_head(
        &lem.name,
        lemma_attr_docs(&lem.attributes, in_file),
        trace_quantifier_keyword(lem.trace_quantifier),
        pf::lnformula_doc(displayed),
        &render_guarded_block(lem.trace_quantifier, guarded),
    );
    out.push('\n');
    out.push_str(proof);
    out
}

/// Everything of HS `prettyLemma` (lib/theory/src/Lemma.hs:116-141) BEFORE the
/// proof body: the `lemma <name> [attrs]:` header, the `<quant> "<formula>"`
/// line, and the `/* guarded formula ... */` comment block.  `formula_doc` is
/// the quoted formula of the quantifier line and `guarded_block` the comment,
/// both built by [`pretty_lemma`] from the lemma it holds.
fn lemma_head(
    name: &str,
    attr_docs: Vec<crate::pretty_hpj::Doc>,
    quant: &str,
    formula_doc: crate::pretty_hpj::Doc,
    guarded_block: &str,
) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    let mut out = String::new();
    // HS `prettyLemmaName` (lib/theory/src/Lemma.hs:91-95):
    //   `text name <-> brackets (fsep (punctuate comma attrs))`
    // The whole header line is:
    //   `kwLemma <-> prettyLemmaName lem <> colon`
    // Rendered via HughesPJ so `fsep` wraps the attributes list when the
    // line is long (e.g. `[heuristic={…}, use_induction,\n<col>reuse]`).
    let kw = Doc::text("lemma");
    let name_doc = Doc::text(name);
    let header_doc = if attr_docs.is_empty() {
        kw.beside_sp(name_doc).beside(Doc::text(":"))
    } else {
        // `brackets (fsep (punctuate comma attrs))` — no space after `[`
        // (beside, not beside_sp) so fsep's continuation aligns with the
        // first attr character (i.e. right after `[`).
        let attrs_fsep = hpj::fsep(hpj::punctuate(Doc::text(","), attr_docs));
        let brackets = Doc::text("[").beside(attrs_fsep).beside(Doc::text("]"));
        kw.beside_sp(name_doc)
            .beside_sp(brackets)
            .beside(Doc::text(":"))
    };
    out.push_str(&header_doc.render());
    out.push('\n');

    // Lemma body shape from HS `prettyLemma` (lib/theory/src/Lemma.hs:119-122):
    //   `nest 2 $ sep [ prettyTraceQuantifier, doubleQuotes (prettyLNFormula f) ]`
    // Routed through the HS-faithful Doc engine so the quant-vs-formula
    // `sep` wrap, the formula's internal `sep`/`nest` wrapping, and the
    // continuation indents are byte-identical to HS.  The `nest 2` indent
    // is included in the rendered output (HS renders it at theory col 0).
    out.push_str(&pf::lemma_header_line_doc(quant, formula_doc));
    out.push('\n');

    // /* guarded formula characterizing ... */
    out.push_str(guarded_block);
    out
}

/// HS `prettyLemmaAttribute` (lib/theory/src/Lemma.hs:97-106) over the
/// theory's own attribute type.
fn lemma_attr_docs(
    attrs: &[crate::theory::LemmaAttr],
    in_file: &str,
) -> Vec<crate::pretty_hpj::Doc> {
    use crate::pretty_hpj::Doc;
    use crate::theory::LemmaAttr::*;
    let mut out = Vec::new();
    for a in attrs {
        let s: String = match a {
            Sources => "sources".into(),
            Reuse => "reuse".into(),
            DiffReuse => "diff_reuse".into(),
            UseInduction => "use_induction".into(),
            HideLemma(s) => format!("hide_lemma={}", s),
            // HS `text ("heuristic=" ++ prettyGoalRankings h)` (`:103`),
            // space-separated and with the oracle name expanded.
            Heuristic(s) => format!("heuristic={}", pretty_heuristic_str(s, in_file)),
            Output(modules) => format!("output=[{}]", modules.join(",")),
            Left => "left".into(),
            Right => "right".into(),
        };
        out.push(Doc::text(s));
    }
    out
}

/// HS `prettyTraceQuantifier` (lib/theory/src/Lemma.hs:179-181).
fn trace_quantifier_keyword(q: crate::theory::TraceQuantifier) -> &'static str {
    match q {
        crate::theory::TraceQuantifier::AllTraces => "all-traces",
        crate::theory::TraceQuantifier::ExistsTrace => "exists-trace",
    }
}

/// HS `ppLNFormulaGuarded` (lib/theory/src/Lemma.hs:131-141) over the
/// ELABORATED lemma's `_lFormula`.
fn render_guarded_block(
    trace_quantifier: crate::theory::TraceQuantifier,
    formula: &crate::formula::LNFormula,
) -> String {
    guarded_block_comment(
        matches!(
            trace_quantifier,
            crate::theory::TraceQuantifier::ExistsTrace
        ),
        crate::guarded::formula_to_guarded(formula),
        || crate::pretty_formula::lnformula_doc(formula),
    )
}

/// The `/* guarded formula characterizing ... */` comment of HS
/// `ppLNFormulaGuarded` (lib/theory/src/Lemma.hs:131-141) around an already
/// converted formula.  `full_doc` builds the quoted whole formula of the
/// failure branch, which the success branch never needs.
fn guarded_block_comment(
    exists_trace: bool,
    gf: Result<crate::guarded::Guarded, crate::guarded::GuardError>,
    full_doc: impl FnOnce() -> crate::pretty_hpj::Doc,
) -> String {
    let header = if exists_trace {
        "guarded formula characterizing all satisfying traces:"
    } else {
        "guarded formula characterizing all counter-examples:"
    };
    let gf = match gf {
        Ok(g) => g,
        Err(e) => {
            // HS lib/theory/src/Lemma.hs:132-134: `multiComment (text "conversion to
            // guarded formula failed:" $$ nest 2 err)` where `err` is the
            // full `ppError` doc (Guarded.hs:471-566, see line 479): the error text, the
            // quoted failing sub-formula (Guarded.hs:508-514/561-563 both
            // include `ppFormula f0`), then "in the formula" + the quoted
            // formula passed to `formulaToGuarded` (nest 2 . doubleQuotes).
            // `nest 2 err` (lib/theory/src/Lemma.hs:132-134) over the thrown
            // message Doc.
            let mut block = String::from("/*\nconversion to guarded formula failed:\n");
            block.push_str(&e.message_doc().nest(2).render());
            block.push('\n');
            // Both formulas are `ppFormula = nest 2 . doubleQuotes .
            // prettyLNFormula` (Guarded.hs:476-477) inside `nest 2 err`
            // (lib/theory/src/Lemma.hs:132-134), so each is a `Doc` laid out
            // at nesting 4 and wraps at the page width.
            let full = full_doc();
            let sub = e
                .subject_formula
                .as_ref()
                .map(crate::pretty_formula::lnformula_doc)
                .unwrap_or_else(|| full.clone());
            block.push_str(&pf::doublequoted_nested_doc(sub, 4));
            block.push_str("\n  in the formula\n");
            block.push_str(&pf::doublequoted_nested_doc(full, 4));
            block.push_str("\n*/");
            return block;
        }
    };
    // For all-traces lemmas, HS prints the negated guarded formula
    // (`gnot gf`).  The result is the "counter-example" form.
    //
    // The guarded block is rendered inside `multiComment` at col 0 with
    // the formula wrapped in `doubleQuotes` (HS lib/theory/src/Lemma.hs:116-141, see line 138/141:
    // `doubleQuotes (prettyGuarded gf)`).  `pretty_guarded_doublequoted`
    // models the `"` as a real `Doc` `beside`, so HughesPJ's column-shift
    // puts continuation lines at the formula's start column (1) — exactly
    // like HS's `"\"" <> prettyGuarded <> "\""`.
    let to_render = if exists_trace {
        gf
    } else {
        crate::guarded::gnot(&gf)
    };
    let quoted = pf::pretty_guarded_doublequoted(&to_render);
    format!("/*\n{}\n{}\n*/", header, quoted)
}

// =============================================================================
// Restriction
// =============================================================================

/// HS `prettyRestriction` (TheoryObject.hs:889-901).  `_rstrFormula` is the
/// macro- and predicate-expanded formula and `_rstrOriginalFormula` the
/// pre-macro one, so the body shows `fromMaybe expandedFormula ogFormula`
/// (`:893`), the safety predicate runs on `_rstrFormula` (`:901`) and the
/// `expanded formula:` comment shows `_rstrFormula` (`:895-898`) under a
/// `case ogFormula of Just _` guard.  The closed theory's restrictions carry
/// an original formula (elaboration and the SAPIC injection both fill it) and
/// print the block; the open view sets it to `None` and prints none.
///
/// The restriction carries no attribute list: HS's restriction parser accepts
/// none (`restriction`, Theory/Text/Parser/Restriction.hs:77-81) and only the
/// diff parser does (`diffRestriction`, `:95-100`).
fn pretty_restriction(r: &crate::restriction::Restriction) -> String {
    let original = r.original_formula.as_ref().unwrap_or(&r.formula);
    let expanded = r.original_formula.as_ref().map(|_| &r.formula);
    pretty_restriction_view(r, original, expanded)
}

fn pretty_restriction_view(
    r: &crate::restriction::Restriction,
    displayed: &crate::formula::LNFormula,
    expanded: Option<&crate::formula::LNFormula>,
) -> String {
    use crate::pretty_hpj::{
        escape_html_entities, hl_close, hl_open, html_mode, keyword_, line_comment_, Hl,
    };
    let mut out = String::new();
    // HS `kwRestriction <-> text name <> colon` (TheoryObject.hs:891-892):
    // `restriction` is a keyword; the name is `text` (entity-escaped in HtmlDoc
    // mode).  `keyword_`/escaping are identities in plain mode.
    out.push_str(&keyword_("restriction").render());
    out.push(' ');
    if html_mode() {
        out.push_str(&escape_html_entities(&r.name));
    } else {
        out.push_str(&r.name);
    }
    out.push_str(":\n");
    out.push_str(&pf::doublequoted_nested_doc(
        pf::lnformula_doc(displayed),
        2,
    ));
    // `nest 2 (if safety then lineComment_ "safety formula" else emptyDoc)`
    // (TheoryObject.hs:894).
    if is_safety_formula(expanded.unwrap_or(displayed)) {
        out.push_str("\n  ");
        out.push_str(&line_comment_("safety formula").render());
    }
    // `nest 2 (multiComment (text "expanded formula:" $-$ doubleQuotes
    // (prettyLNFormula expandedFormula)))` (TheoryObject.hs:896-897).
    // `multiComment = comment (…)` wraps the whole `/* … */` in an
    // `hl_comment` span; the inner formula still carries its own operator spans.
    if let Some(expanded) = expanded {
        out.push_str("\n\n  ");
        out.push_str(&hl_open(Hl::Comment));
        out.push_str("/*\n  expanded formula:\n");
        out.push_str(&pf::doublequoted_nested_doc(pf::lnformula_doc(expanded), 2));
        out.push_str("\n  */");
        out.push_str(&hl_close(Hl::Comment));
    }
    out
}

/// HS `prettyPredicate` (TheoryObject.hs:845-849):
///
/// ```haskell
/// prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
///   factstr    = render $ prettyFact prettyLVar (pFact p)
///   formulastr = render $ prettyLNFormula      (pFormula p)
/// ```
///
/// `kwPredicate <> colon` is `predicate:` (no space), `<->` adds one space,
/// then the combined `<fact><=><formula>` text (no spaces around `<=>`).
///
/// `render` is HughesPJ's default style: `lineLength = 100` and
/// `ribbonsPerLine = 1.5`, so `fullRender` rounds the ribbon to 67
/// (HughesPJ.hs:940, :1010) — NOT the 110/73 the console's `renderDoc`
/// installs for the surrounding theory echo.  The fact and the formula are
/// rendered INDEPENDENTLY at that style from column 0, then concatenated as
/// plain text.
fn pretty_predicate(pr: &crate::predicate::Predicate) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    // HS `prettyLVar = text . show` over the formal args, so each carries its
    // sort sigil (`#i` for a temporal arg).
    let pp_var = |v: &tamarin_term::lterm::LVar| Doc::text(v.to_string());
    let factstr = crate::fact::pretty_fact(&pp_var, &pr.fact)
        .render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON);
    let formulastr =
        pf::lnformula_doc(&pr.formula).render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON);
    format!("predicate: {}<=>{}", factstr, formulastr)
}

/// HS `prettyMacros` / `prettyMacro` (TheoryObject.hs:862-884).
///
/// HS: `prettyMacros m = keyword_ "macros:" $$ nest 4 (vcat [macros...])`
/// HS: `prettyMacro (op, args, out) =
///       vcat [ppNonEmptyList (\ds -> sep (map (nest 4) ds)) text [op++"("]
///             <-> prettyVarList args <-> text ") = " <-> prettyTerm show out]`
///
/// `ppNonEmptyList hdr pp [x] = hdr [pp x] = sep [nest 4 (text x)]`
/// = `nest 4 (text (name++"("))`.
///
/// With `keyword_ "macros:" $$ nest 4 (nest 4 "name(" <+> args <+> ") = " <+> body)`:
/// the double-nest (8 total) combined with `keyword_`'s 7-char width makes
/// `nil_above_nest` inline the content (k = -7+8 = 1 > 0), putting everything
/// on ONE line: `macros: name( args ) =  body`.
///
/// For multiple macros, each is nested 4 levels inside the outer `nest 4`,
/// giving 8-space indent on subsequent lines.  An empty list renders nothing
/// (`prettyMacros [] = emptyDoc`, TheoryObject.hs:863).
fn pretty_macros(macros: &[crate::theory::LNMacro]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if macros.is_empty() {
        return String::new();
    }
    let last_idx = macros.len() - 1;
    let macro_docs: Vec<Doc> = macros
        .iter()
        .enumerate()
        .map(|(i, m)| {
            // HS: `ppNonEmptyList (\ds -> sep (map (nest 4) ds)) text [op++"("]`
            // = `sep [nest 4 (text (op ++ "("))]` = `nest 4 (text (op ++ "("))`.
            let name_open = Doc::text(format!("{}(", String::from_utf8_lossy(&m.name))).nest(4);
            // HS `prettyVarList = fsep . punctuate comma . map prettyLVar`
            // (TheoryObject.hs:858-859).
            let args: Vec<Doc> = m.params.iter().map(|v| Doc::text(v.to_string())).collect();
            // HS `prettyTerm (text . show) out`.
            let body = tamarin_term::pretty::pretty_nterm(&m.body);
            // Build: `nest 4 "name(" <+> args <+> ") = " <+> body`
            // HS <-> = HughesPJ <+> (beside with space = beside_sp).
            let mut doc = name_open;
            if !args.is_empty() {
                doc = doc.beside_sp(hpj::fsep(hpj::punctuate(Doc::char(','), args)));
            }
            doc = doc.beside_sp(Doc::text(") = "));
            doc = doc.beside_sp(body);
            // HS: last macro has no trailing comma
            if i < last_idx {
                doc.beside(Doc::text(","))
            } else {
                doc
            }
        })
        .collect();

    // HS: `keyword_ "macros:" $$ nest 4 (vcat macro_docs)`
    let body = hpj::vcat(macro_docs).nest(4);
    Doc::text("macros:").above(body).render()
}

/// HS `isSafetyFormula . formulaToGuarded_` (Guarded.hs:156-164 / 466-467) over
/// a restriction's formula.
///
/// `isSafetyFormula gf0 = null (frees [gf0]) && noExistential gf0`
/// (Guarded.hs:157-158): the guarded formula must be CLOSED *and* free of
/// existential quantifiers.  `crate::guarded::is_safety_formula` is that exact
/// predicate; this wrapper supplies the `LNFormula → LNGuarded` step.
/// HS's `formulaToGuarded_` `error`s out when the formula is not guardable
/// (`either (error . render) id`, Guarded.hs:467) and takes the whole run down;
/// an unguardable restriction here yields `false` (no annotation) instead.
fn is_safety_formula(f: &crate::formula::LNFormula) -> bool {
    match crate::guarded::formula_to_guarded(f) {
        Ok(g) => crate::guarded::is_safety_formula(&g),
        Err(_) => false,
    }
}

// =============================================================================
// Proof body
// =============================================================================

/// Render a proof tree in HS's `prettyProofWith` shape:
///
/// - `Finished Solved` with no children → `SOLVED // trace found`
/// - No children otherwise               → `by <step>` (e.g. `by contradiction`)
/// - One unnamed child                   → `<step>\n<recurse>`
/// - Multiple children                   → `<step>\n  case A\n  ...\nnext\n  case B\n  ...\nqed`
///
/// Mirrors `Theory.Proof.prettyProofWith` (Theory/Proof.hs:1054-1075).
pub fn pretty_proof_body(node: &crate::constraint::solver::search::ProofNode) -> String {
    let mut out = String::new();
    pp_proof(node, &mut out, 0);
    out
}

/// The two proof trees the proof body prints: the tree the solver searched
/// and the tree a lemma's stored skeleton elaborated into.  HS prints both
/// with `prettyProofWith` over a `Proof a = LTree CaseName (ProofStep a)`
/// (Theory/Proof.hs:1054-1075).
trait ProofBody {
    fn method(&self) -> &crate::constraint::solver::proof_method::ProofMethod;

    /// False for a step whose constraint system is HS's `Nothing`, which
    /// prints `/* unannotated */` (ProofSkeleton.hs:80-84).
    fn annotated(&self) -> bool;

    /// The child cases in the name order HS's `M.toList` gives.
    fn cases(&self) -> Vec<(&String, &Self)>;
}

impl ProofBody for crate::constraint::solver::search::ProofNode {
    fn method(&self) -> &crate::constraint::solver::proof_method::ProofMethod {
        &self.method
    }

    fn annotated(&self) -> bool {
        self.annotated
    }

    fn cases(&self) -> Vec<(&String, &Self)> {
        self.children.iter().collect()
    }
}

impl ProofBody for crate::theory::ProofTree {
    fn method(&self) -> &crate::constraint::solver::proof_method::ProofMethod {
        &self.method
    }

    /// HS echoes a stored skeleton with `prettyProof`, whose step printer is
    /// `prettyProofMethod . psMethod` and has no annotation branch
    /// (Theory/Proof.hs:1051-1052), so no step carries `/* unannotated */`.
    fn annotated(&self) -> bool {
        true
    }

    /// `cases` keeps source order; the parser stored them in an `M.fromList`
    /// (Theory/Text/Parser/Proof.hs:113), so they print sorted by name.
    fn cases(&self) -> Vec<(&String, &Self)> {
        let mut cases: Vec<(&String, &Self)> = self.cases.iter().map(|(n, c)| (n, c)).collect();
        cases.sort_by_key(|(n, _)| *n);
        cases
    }
}

fn pp_proof<T: ProofBody>(node: &T, out: &mut String, depth: usize) {
    use crate::constraint::solver::proof_method::{ProofMethod, Result as MR};
    // The step's first char lands at col `depth*2` (proof body uses
    // 2-space indent per nesting level).
    //
    // HS `prettyIncrementalProof` (ProofSkeleton.hs:80-84) renders each
    // step as `sep [prettyProofMethod, if Nothing then "/* unannotated
    // */" else empty]`.  A step whose constraint system could not be
    // re-attached during the close-time `checkProof` replay
    // (`annotated == false`) gets the `/* unannotated */` comment beside
    // its method.  Fully-searched / successfully-replayed steps stay
    // `Just System` (annotated == true) and render without it.
    // HS `prettyIncrementalProof.ppStep` (ProofSkeleton.hs:80-84) wraps
    // every step as `sep [prettyProofMethod, comment-or-empty]`, where
    // `comment = multiComment_ ["unannotated"]` iff `psInfo == Nothing`
    // (`annotated == false`).  `sep` lays method+comment inline when they
    // fit the ribbon, else drops the comment to its OWN line at the
    // step's base indent (`depth*2`).  We build the method as a Doc and
    // run it through the same HughesPJ engine so the break is
    // byte-identical to HS.
    let base = depth * 2;
    let annotated = node.annotated();
    let cases = node.cases();

    match (node.method(), cases.as_slice()) {
        (ProofMethod::Finished(MR::Solved), []) => {
            let doc = pp_step_doc(node.method(), "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
        }
        (_, []) => {
            // No children: `by <step>` form.  HS `ppCases ps [] =
            // prettyCase ps (kwBy <> text " ") <> prettyStep ps` (non-diff
            // `prettyProofWith`, Theory/Proof.hs:1065-1066) — `<>` is beside, so the
            // `prettyStep` Doc is laid
            // out BESIDE `by `.  For a `SolveGoal` step the goal can wrap, and
            // HughesPJ counts the `by ` (3 cols) toward the ribbon when
            // deciding the `fsep`/`sep` break — so we must render `by ` as
            // line CONTENT, not as part of the indent (cf. the live string path;
            // the NAXOS/KAS2 `Match( a,` / `<…>` divergence).  The `by `
            // prefix is laid out by `step_line_with_unann` BESIDE the WHOLE
            // `sep [method, comment]` (HS `prettyCase ps (kwBy<>" ") <>
            // prettyStep ps`), so a dropped `/* unannotated */` aligns at
            // `base + len("by ")` (= +3), not `base`.  `beside` still shifts
            // the method's own wrapped continuation columns by the prefix
            // width and counts it toward the ribbon, so the method lines
            // stay byte-identical to HS.
            let doc = pp_step_doc(node.method(), "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, "by "));
        }
        (_, [(label, child)]) if label.is_empty() => {
            let doc = pp_step_doc(node.method(), "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
            out.push('\n');
            // HS `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf`
            // (non-diff `prettyProofWith`, Theory/Proof.hs:1054-1075, see line 1067).
            // `$-$` is "above" — the child is rendered
            // at the SAME indent column as the parent step.  In our output
            // model the caller writes the indent before calling pp_proof, so
            // we reproduce that here: write the same `depth`-level indent
            // before recursing into the child.
            out.push_str(&"  ".repeat(depth));
            pp_proof(*child, out, depth);
        }
        (_, multi) => {
            let doc = pp_step_doc(node.method(), "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
            for (i, (name, child)) in multi.iter().enumerate() {
                if i > 0 {
                    // HS Theory/Proof.hs:1054-1075, see line 1070 (non-diff
                    // `prettyProofWith`): `intersperse (prettyCase ps kwNext)`
                    // — `next` is a sibling of `solve`/`qed`, so it sits at
                    // the parent's indent (`depth*2`), not column 0.
                    out.push('\n');
                    out.push_str(&"  ".repeat(depth));
                    out.push_str("next");
                }
                out.push('\n');
                let pad = "  ".repeat(depth + 1);
                out.push_str(&pad);
                out.push_str("case ");
                out.push_str(name);
                out.push('\n');
                out.push_str(&pad);
                pp_proof(*child, out, depth + 1);
            }
            out.push('\n');
            out.push_str(&"  ".repeat(depth));
            out.push_str("qed");
        }
    }
}

/// Render a `ProofMethod` to a flat string exactly as HS `prettyProofMethod`
/// (ProofMethod.hs:1173-1186) — the SAME renderer the `--prove` proof tree
/// uses, so `solve( <goal> )` carries the faithful fact spacing (`!KU( ~ltk )`),
/// LVar dots (`#vk.2`), and contradiction reasons.  Used by the interactive
/// web UI's applicable-methods list + proof snippet (`tamarin-server`), which
/// must match `--prove`'s method text.  Rendered at the process display width
/// (100 for the web); the semantic web gate normalises any wrapping away.
pub fn pretty_proof_method_inline(
    m: &crate::constraint::solver::proof_method::ProofMethod,
) -> String {
    pp_step_doc(m, "").render()
}

/// HS `prettyProofMethod m` as a Doc (ProofMethod.hs:1170-1186), for
/// callers that lay the method out INSIDE a larger Doc context — the web
/// "Applicable Proof Methods" list (`Web/Theory.hs:513-611, see line 546` `numbered' $
/// zipWith prettyPM [1..] pms`), where the `N. ` prefix beside-shift and
/// the trailing `// expl` line comment both participate in the HughesPJ
/// fill decisions.
pub fn pretty_proof_method_doc(
    m: &crate::constraint::solver::proof_method::ProofMethod,
) -> crate::pretty_hpj::Doc {
    pp_step_doc(m, "")
}

/// Build the proof-step method as a `pretty_hpj::Doc` so it can be
/// combined with the `/* unannotated */` comment via `sep`, per HS
/// `prettyIncrementalProof.ppStep`, ProofSkeleton.hs:80-84.
///
/// `prefix` is the leaf-step keyword (`"by "` for childless steps, `""`
/// otherwise); it is laid out BESIDE the method as line content (NOT
/// folded into the indent) so HughesPJ counts its columns toward the
/// ribbon, identical to `step_line_with_unann`/`pp_proof`'s string path.
fn pp_step_doc(
    m: &crate::constraint::solver::proof_method::ProofMethod,
    prefix: &str,
) -> crate::pretty_hpj::Doc {
    use crate::constraint::solver::proof_method::{ProofMethod as PM, Result as MR};
    use crate::pretty_hpj::Doc;
    // `solve( <goal> )` builds its own goal Doc; everything else is a
    // flat string with no internal wrapping, so `Doc::text` of the
    // string form is faithful.
    let body = match m {
        // HS `SolveGoal goal -> keyword_ "solve(" <-> prettyGoal goal <->
        // keyword_ ")"` (ProofMethod.hs:1181).  The `solve(` / `)` delimiters
        // are `hl_keyword` spans (identity in plain mode, so batch bytes are
        // unchanged); the unannotated-replay overview index
        // (`hl_superfluous` steps) needs these spans to match HS.
        PM::SolveGoal(g) => crate::pretty_hpj::keyword_("solve(")
            .beside_sp(solve_goal_to_doc(g))
            .beside_sp(crate::pretty_hpj::keyword_(")")),
        // HS `prettyProofMethod` (ProofMethod.hs:1183-1186):
        //   Finished (Contradictory reason) ->
        //     sep [ keyword_ "contradiction"
        //         , maybe emptyDoc (closedComment . prettyContradiction) reason ]
        // `closedComment d = comment $ fsep [text "/*", d, text "*/"]`
        // (Theory/Text/Pretty.hs:108-109).  Build this as a real Doc so HughesPJ's
        // `sep`/`fsep` break the comment (and its `/*`…`*/` delimiters)
        // onto their own lines at deep proof-tree indentation, identical
        // to HS.
        PM::Finished(MR::Contradictory(reason)) => {
            // HS `sep [keyword_ "contradiction", maybe emptyDoc (closedComment
            // . prettyContradiction) reason]` (ProofMethod.hs:1184-1186).
            let contra = crate::pretty_hpj::keyword_("contradiction");
            match reason {
                None => contra,
                Some(c) => {
                    // `closedComment d = comment (fsep [text "/*", d, text "*/"])`.
                    let inner = crate::pretty_hpj::comment(crate::pretty_hpj::fsep(vec![
                        Doc::text("/*"),
                        Doc::text(pp_contradiction(c)),
                        Doc::text("*/"),
                    ]));
                    crate::pretty_hpj::sep(vec![contra, inner])
                }
            }
        }
        // HS `prettyProofMethod` leaf keywords/comments (ProofMethod.hs:1175-1182).
        // Built as all-`beside` chains (no `fsep`) so plain-mode layout
        // matches HS exactly (the highlight combinators are the identity
        // there); HtmlDoc mode adds `hl_*` spans.
        PM::Simplify => crate::pretty_hpj::keyword_("simplify"),
        PM::Induction => crate::pretty_hpj::keyword_("induction"),
        PM::Finished(MR::Solved) => crate::pretty_hpj::keyword_("SOLVED")
            .beside_sp(crate::pretty_hpj::line_comment_("trace found")),
        PM::Finished(MR::Unfinishable) => crate::pretty_hpj::keyword_("UNFINISHABLE").beside_sp(
            crate::pretty_hpj::line_comment_("reducible operator in subterm"),
        ),
        PM::Invalidated => crate::pretty_hpj::line_comment_(
            "proof may have been invalidated by editing a reuse lemma above. You should ",
        ),
        // HS `Sorry reason -> fsep [keyword_ "sorry", maybe emptyDoc
        // closedComment_ reason]` (ProofMethod.hs:1179-1180).  `keyword_` is
        // identity in plain mode, so `sorry` / `sorry /* reason */`
        // matches HS exactly (verified against the `--prove` baseline); HtmlDoc
        // mode adds the `hl_keyword`/`hl_comment`
        // spans the overview `#proof` index needs.  `fsep [x, emptyDoc] = x`.
        PM::Sorry(reason) => match reason {
            None => crate::pretty_hpj::keyword_("sorry"),
            Some(r) => crate::pretty_hpj::fsep(vec![
                crate::pretty_hpj::keyword_("sorry"),
                crate::pretty_hpj::closed_comment_(r),
            ]),
        },
    };
    if prefix.is_empty() {
        body
    } else {
        Doc::text(prefix).beside(body)
    }
}

/// Render a `Goal` for the oracle/tactic ranking path.  This is HS's
/// `render $ prettyGoal g` from `ProofMethod.hs:604-622,700-702, see line 606,701`
/// (oracle stdin)
/// and `Tactics.hs` `pg = concat . lines . render $ prettyGoal agoal`
/// (tactic regex string).  All consumers (goals.rs oracle stdin /
/// `apply_ranking_fn` / `tactic_pg`) immediately apply `concat . lines`
/// to drop the newlines, so the byte-for-byte requirement is on each
/// line's internal text (leading indent spaces survive the `concat`).
///
/// Width: the oracle/tactic path uses plain `render = P.render`
/// (`Theory.Text.Pretty` re-exports `Text.PrettyPrint.Class.render`,
/// which is `P.render` from HughesPJ — Text/PrettyPrint/Class.hs:77-78).  `P.render`
/// uses HughesPJ's DEFAULT `style`: `lineLength = 100`,
/// `ribbonsPerLine = 1.5` → `ribbon = round(100/1.5) = 67`.  This is
/// DISTINCT from the `--prove` display path, which uses
/// `renderStyle (defaultStyle { lineLength = lineWidth })`
/// (Console.hs:242-243,398-399),
/// i.e. width 110 / ribbon 73 (`pretty_hpj::LINE_LENGTH`/`RIBBON`).
/// We build the goal via the same `solve_goal_to_doc` builder the
/// display path uses, then render it at the oracle width.
pub(crate) fn render_goal_for_oracle(g: &crate::constraint::constraints::Goal) -> String {
    // HS oracle stdin line = `show i ++": "++ (concat . lines . render $
    // prettyGoal g)` (ProofMethod.hs:598-623, see line 607).  HS `render` is HughesPJ's plain
    // `render` (= `fullRender`/`display` from line column 0), which APPLIES a
    // top-level `nest` to the FIRST line — so e.g. `prettyGoal (DisjG ..)` =
    // `fsep (map (nest 1 . parens . prettyGuarded) gfs)` renders with a LEADING
    // SPACE (`" (#a < #b)  ∥ .."`).  Use `render_with` (HughesPJ `lay`, indent
    // 0) here, NOT `render_at` (`lay2`, continuation mode) — `lay2` discards a
    // leading `Nest`, dropping that space and feeding the oracle a DIFFERENT
    // goal string than HS, which can change the oracle's ranking decisions.
    // (The `--prove` display path renders the disjunction AFTER a `solve( `
    // prefix, so the nest is never at the doc start there and both lay/lay2
    // agree — this divergence is oracle-stdin-specific.)
    //
    // ALWAYS plain: HS builds this string with the plain `render $
    // prettyGoal` regardless of the caller's rendering context
    // (ProofMethod.hs:598-623, see line 607).  The web proof-pane ranks while its
    // `HtmlDocGuard::enable()` is active — without forcing plain mode the
    // oracle receives `<span class=…>`/`&lt;`-laden goal strings its
    // regexes cannot match (dmn `*_min` panes ranked in bare goal-nr
    // order while HS's oracle reordered).
    let _plain = crate::pretty_hpj::HtmlDocGuard::disable();
    solve_goal_to_doc(g).render_with(ORACLE_LINE_LENGTH, ORACLE_RIBBON)
}

/// Build a `pretty_hpj::Doc` for a non-DisjG `Goal`, mirroring HS
/// `prettyGoal` (Constraints.hs:273-287).  `<->` = `<+>` (beside-with-
/// space).  Facts go through `prettyLNFact`'s `nestShort'` wrapping
/// ([`crate::fact::pretty_lnfact`]); terms through `prettyLNTerm`
/// ([`tamarin_term::pretty::pretty_nterm`]); node-ids / node-conc /
/// node-prem are atomic strings (HS `prettyNodeId` is `text . show`).  The
/// non-empty DisjG case is rendered by the `disj_goal_to_doc` arm below.
pub(crate) fn solve_goal_to_doc(
    g: &crate::constraint::constraints::Goal,
) -> crate::pretty_hpj::Doc {
    use crate::constraint::constraints::Goal;
    use crate::pretty_hpj::Doc;
    use crate::rule::PremIdx;
    match g {
        // `prettyGoal (ActionG i fa) = prettyNAtom (Action (varTerm i) fa)`
        // = `prettyFact fa <-> opAction <-> text (show i)` (Atom.hs:216-217),
        // `opAction = "@"` (Theory/Text/Pretty.hs:170).
        Goal::Action(i, fa) => {
            let nid = render_node_id(i);
            crate::fact::pretty_lnfact(fa)
                .beside_sp(crate::pretty_hpj::operator_("@"))
                .beside_sp(Doc::text(nid))
        }
        // `prettyGoal (ChainG c p) =
        //    prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p`.
        Goal::Chain(c, p) => Doc::text(render_node_conc(c))
            .beside_sp(crate::pretty_hpj::operator_("~~>"))
            .beside_sp(Doc::text(render_node_prem(p))),
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i`.
        Goal::Premise((i, PremIdx(v)), fa) => {
            let sub = goal_subscript(*v);
            let nid = render_node_id(i);
            crate::fact::pretty_lnfact(fa)
                .beside_sp(Doc::text(format!("\u{25B6}{}", sub)))
                .beside_sp(Doc::text(nid))
        }
        // `prettyGoal (SplitG x) = text "splitEqs" <> parens (text (show ...))`
        // `<>` = no space → `splitEqs(N)`.
        Goal::Split(id) => Doc::text(format!("splitEqs({})", id.0)),
        // `prettyGoal (DisjG (Disj [])) = text "Disj" <-> operator_ "(⊥)"`.
        Goal::Disj(d) if d.0.is_empty() => {
            Doc::text("Disj").beside_sp(crate::pretty_hpj::operator_("(\u{22A5})"))
        }
        // Non-empty DisjG renders via the Doc form (`disj_goal_to_doc`).
        Goal::Disj(d) => pf::disj_goal_to_doc(&d.0),
        // `prettyGoal (SubtermG (l,r)) =
        //    prettyLNTerm l <-> operator_ "⊏" <-> prettyLNTerm r`.
        Goal::Subterm((l, r)) => tamarin_term::pretty::pretty_nterm(l)
            .beside_sp(crate::pretty_hpj::operator_("\u{228F}"))
            .beside_sp(tamarin_term::pretty::pretty_nterm(r)),
    }
}

/// Render a `NodeId` (`LVar` of Node sort).  HS `prettyNodeId`
/// (LTerm.hs:926-927) is `text . show`; `Display for LVar` is that `show`.
fn render_node_id(nid: &crate::constraint::constraints::NodeId) -> String {
    nid.to_string()
}

/// Render a `NodeConc`.  Mirrors HS `prettyNodeConc`
/// (Constraints.hs:256-257): `parens (prettyNodeId v <> comma <-> int i)`.
/// `<>` joins with no space; `<->` adds a space — `(#i, 0)`.
fn render_node_conc(c: &crate::constraint::constraints::NodeConc) -> String {
    format!("({}, {})", render_node_id(&c.0), (c.1).0)
}

/// Render a `NodePrem`.  Mirrors HS `prettyNodePrem`
/// (Constraints.hs:260-261): same layout as `prettyNodeConc`.
fn render_node_prem(p: &crate::constraint::constraints::NodePrem) -> String {
    format!("({}, {})", render_node_id(&p.0), (p.1).0)
}

/// Unicode-subscript digits for a non-negative integer.  Mirrors HS
/// `subscript` used by `prettyGoal (PremiseG …)` in Constraints.hs:273-288.
fn goal_subscript(n: usize) -> String {
    tamarin_utils::unicode::subscript(&n.to_string())
}

fn pp_contradiction(c: &crate::constraint::solver::contradictions::Contradiction) -> String {
    use crate::constraint::solver::contradictions::Contradiction as C;
    // HS `prettyContradiction` (Contradictions.hs:487-506).
    match c {
        C::Cyclic => "cyclic".to_string(),
        // HS: `SubtermCyclic -> text "contradictory subterm store"`
        C::SubtermCyclic => "contradictory subterm store".to_string(),
        C::IncompatibleEqs => "incompatible equalities".to_string(),
        C::NonNormalTerms => "non-normal terms".to_string(),
        // HS: `ForbiddenExp -> text "non-normal exponentiation rule instance"`
        C::ForbiddenExp => "non-normal exponentiation rule instance".to_string(),
        // HS: `ForbiddenBP -> text "non-normal bilinear pairing rule instance"`
        C::ForbiddenBP => "non-normal bilinear pairing rule instance".to_string(),
        // HS: `ForbiddenKD -> text "forbidden KD-fact"`
        C::ForbiddenKD => "forbidden KD-fact".to_string(),
        C::ForbiddenChain => "forbidden chain".to_string(),
        C::ForbiddenACConstrChain => "forbidden AC constructor chain".to_string(),
        C::ImpossibleChain => "impossible chain".to_string(),
        // HS: `NonInjectiveFactInstance cex -> text $ "non-injective facts " ++ show cex`
        // where `cex :: (NodeId, NodeId, NodeId)`.  HS `Show` for a
        // tuple yields `(a,b,c)` (no spaces after commas), with each
        // component rendered by `Show LVar` (LTerm.hs:550-557) — which
        // is `Display for LVar`.
        C::NonInjectiveFactInstance(a, b, c) => format!("non-injective facts ({a},{b},{c})"),
        C::FormulasFalse => "from formulas".to_string(),
        // HS: `SuperfluousLearn m v ->
        //        doubleQuotes (prettyLNTerm m) <->
        //        text "derived before and after" <->
        //        doubleQuotes (prettyNodeId v)`
        // → `"<m>" derived before and after "<v>"`.
        C::SuperfluousLearn(m, v) => format!(
            "\"{}\" derived before and after \"{}\"",
            tamarin_term::pretty::pretty_lnterm(m),
            render_node_id(v)
        ),
        // HS: `NodeAfterLast (i,j) ->
        //        text $ "node " ++ show j ++ " after last node " ++ show i`
        // Note HS reverses the order: `j` first in the message, then `i`.
        C::NodeAfterLast(i, j) => {
            format!("node {j} after last node {i}")
        }
    }
}

// =============================================================================
// Generated-from
// =============================================================================

fn render_generated_from(build: &BuildInfo) -> String {
    format!(
        "/*\nGenerated from:\nTamarin version {}\nMaude version {}\nGit revision: {}, branch: {}\nCompiled at: {}\n*/",
        build.tamarin_version,
        build.maude_version,
        build.git_revision,
        build.git_branch,
        build.compiled_at,
    )
}

#[cfg(test)]
mod oracle_goal_tests {
    use super::*;
    use crate::constraint::constraints::{Disj, Goal};
    use crate::fact::{Fact, FactTag, LNFact, Multiplicity};
    use crate::rule::{ConcIdx, PremIdx};
    use crate::tools::equation_store::SplitId;
    use tamarin_term::function_symbols::{
        diff_sym, exp_sym, nat_one_sym, pair_sym, AcFctSym, AcSym, Constructability, FunSym,
        NdcState, Privacy,
    };
    use tamarin_term::intern::intern_str;
    use tamarin_term::lterm::{pub_term, LNTerm, LSort, LVar};
    use tamarin_term::term::{f_app_ac, f_app_no_eq, unsafe_f_app, Term};
    use tamarin_term::vterm::Lit;

    fn fresh(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Fresh, 0)))
    }

    fn msg(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
    }

    /// HS's oracle string is `concat . lines . render $ prettyGoal g`
    /// (ProofMethod.hs:606).
    fn collapse(s: &str) -> String {
        s.lines().collect::<Vec<_>>().concat()
    }

    /// The term shapes HS `prettyTerm` gives an arm of its own
    /// (Term/Term.hs:304-317): a builtin AC operator, a `pair` chain, `exp`,
    /// `diff`, a user-`[AC]` symbol nullary and binary, and `%1`.
    fn shape_terms() -> Vec<(&'static str, LNTerm)> {
        let user_ac = AcFctSym::new(
            b"add".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        vec![
            ("mult", f_app_ac(AcSym::Mult, vec![fresh("a"), fresh("b")])),
            ("xor", f_app_ac(AcSym::Xor, vec![fresh("a"), fresh("b")])),
            (
                "pair",
                f_app_no_eq(
                    pair_sym(),
                    vec![msg("x"), f_app_no_eq(pair_sym(), vec![msg("y"), msg("z")])],
                ),
            ),
            (
                "exp",
                f_app_no_eq(exp_sym(), vec![pub_term("g"), fresh("a")]),
            ),
            ("diff", f_app_no_eq(diff_sym(), vec![msg("x"), msg("y")])),
            (
                "nullary_user_ac",
                unsafe_f_app(FunSym::Ac(AcSym::AcFct(user_ac)), vec![]),
            ),
            (
                "binary_user_ac",
                f_app_ac(AcSym::AcFct(user_ac), vec![msg("x"), msg("y")]),
            ),
            ("nat_one", f_app_no_eq(nat_one_sym(), vec![])),
        ]
    }

    fn ev_fact(t: LNTerm) -> LNFact {
        Fact::new(
            FactTag::Proto(Multiplicity::Linear, intern_str("Ev"), 1),
            vec![t],
        )
    }

    fn st_fact(t: LNTerm) -> LNFact {
        Fact::new(
            FactTag::Proto(Multiplicity::Persistent, intern_str("St"), 1),
            vec![t],
        )
    }

    /// The oracle/tactic ranking string is HS's `concat . lines . render`,
    /// where `render = P.render` uses HughesPJ's default `style`
    /// (lineLength = 100, ribbon = 67) — NOT the `--prove` DISPLAY width
    /// (110 / 73, used by `renderStyle (defaultStyle { lineLength = lineWidth })`
    /// in Console.hs:242-243,398-399).
    ///
    /// Authentic ground truth (captured from the v1.13.0 HS prover with an
    /// oracle that echoes stdin, on a crafted theory whose premise goal is
    /// 69 columns wide):
    ///
    /// ```text
    /// 0: !KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb) ▶₀ #l
    /// ```
    ///
    /// Note the absence of a space before the closing `)`: at ribbon 67 the
    /// fact's `nestShort'` (Theory/Model/Fact.hs:567-574, see line 572) wraps,
    /// pushing `)` onto its own
    /// line at column 0, and `concat . lines` then joins it directly to the
    /// preceding `~msgbbbbbbbbbbbbbbbbbbbb`.  At the DISPLAY ribbon 73 the same
    /// goal stays inline (`... ~msgbbbbbbbbbbbbbbbbbbbb )`, with the space).
    /// That single byte distinguishes the two widths, so it pins the oracle
    /// path to 100/67.
    #[test]
    fn premise_goal_wraps_at_oracle_ribbon_67() {
        // !KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb ) ▶₀ #l
        let fa: LNFact = Fact::new(
            FactTag::Proto(Multiplicity::Persistent, "KeyStore0", 2),
            vec![
                fresh("keyaaaaaaaaaaaaaaaaaaaa"),
                fresh("msgbbbbbbbbbbbbbbbbbbbb"),
            ],
        );
        let node = LVar::new("l", LSort::Node, 0);
        let goal = Goal::Premise((node, PremIdx(0)), fa);

        // HS: `concat . lines . render $ prettyGoal g`.
        let rendered = render_goal_for_oracle(&goal);
        let collapsed: String = rendered.lines().collect::<Vec<_>>().concat();

        assert_eq!(
            collapsed,
            "!KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb) \u{25B6}\u{2080} #l",
            "oracle goal string must match HS `render` at default ribbon 67 \
             (wrapped fact: no space before `)`)",
        );

        // The SAME goal at the DISPLAY width (110 / 73) stays inline, keeping
        // the space before `)`.  This guards against silently swapping the
        // oracle width back to the display width.
        let display: String = solve_goal_to_doc(&goal)
            .render_at(crate::pretty_hpj::LINE_LENGTH, crate::pretty_hpj::RIBBON, 0)
            .lines()
            .collect::<Vec<_>>()
            .concat();
        assert_eq!(
            display,
            "!KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb ) \u{25B6}\u{2080} #l",
            "display width must keep the fact inline (space before `)`); the two \
             expectations differ by exactly that byte, which is what makes this \
             pair discriminating",
        );
    }

    /// Regression: a disjunction goal sent to the oracle MUST carry the
    /// leading space HS produces.  HS `prettyGoal (DisjG (Disj gfs))` =
    /// `fsep (map (nest 1 . parens . prettyGuarded) gfs)` (Constraints.hs:
    /// 276-277), and HS `render` (HughesPJ `lay`, from column 0) APPLIES the
    /// top-level `nest 1` to the FIRST line — so the oracle stdin line is
    /// `" (#a < #b)  ∥ (#b < #a)"` (leading space).  `render_goal_for_oracle`
    /// must use `render_with`/`lay`, NOT `render_at`/`lay2` (which drops a
    /// leading `Nest`); the latter fed the oracle a string differing from HS
    /// by one space, perturbing oracle ranking decisions on oracle-driven
    /// proofs (e.g. csf19-wrapping gcm).  Ground truth captured from the
    /// v1.13.0 HS prover with an echoing oracle.
    #[test]
    fn disj_goal_for_oracle_has_leading_space() {
        use crate::atom::ProtoAtom;
        use crate::constraint::constraints::{Disj, Goal};
        use crate::formula::BLNTerm;
        use crate::guarded::Guarded;
        use tamarin_term::lterm::{BVar, LSort, LVar};
        use tamarin_term::vterm::var_term;

        let tp = |n: &str| -> BLNTerm { var_term(BVar::Free(LVar::new(n, LSort::Node, 0))) };
        // `#a < #b` ∥ `#b < #a`
        let d1 = Guarded::Atom(ProtoAtom::Less(tp("a"), tp("b")));
        let d2 = Guarded::Atom(ProtoAtom::Less(tp("b"), tp("a")));
        let goal = Goal::Disj(Disj::new(vec![d1, d2]));

        let rendered = render_goal_for_oracle(&goal);
        let collapsed: String = rendered.lines().collect::<Vec<_>>().concat();
        // HS `nest 1` leading space + `"  ∥"` separator (two spaces + ∥).
        assert_eq!(
            collapsed, " (#a < #b)  \u{2225} (#b < #a)",
            "oracle disjunction goal must keep HS's leading `nest 1` space; \
             losing it is the render_at/lay2 regression",
        );
    }

    /// The `Action`, `Premise` and `Subterm` arms at the oracle width, once
    /// per term shape.  These strings are the external ranking program's
    /// stdin, so one byte of drift here reorders goals and changes which
    /// proof the solver finds — not just what it prints.
    #[test]
    fn the_term_goal_arms_render_each_shape_at_the_oracle_width() {
        let expected: Vec<(&str, &str, &str, &str)> = vec![
            (
                "mult",
                "Ev( (~a*~b) ) @ #i",
                "!St( (~a*~b) ) \u{25B6}\u{2082} #i",
                "(~a*~b) \u{228F} w",
            ),
            (
                "xor",
                "Ev( (~a\u{2295}~b) ) @ #i",
                "!St( (~a\u{2295}~b) ) \u{25B6}\u{2082} #i",
                "(~a\u{2295}~b) \u{228F} w",
            ),
            (
                "pair",
                "Ev( <x, y, z> ) @ #i",
                "!St( <x, y, z> ) \u{25B6}\u{2082} #i",
                "<x, y, z> \u{228F} w",
            ),
            (
                "exp",
                "Ev( 'g'^~a ) @ #i",
                "!St( 'g'^~a ) \u{25B6}\u{2082} #i",
                "'g'^~a \u{228F} w",
            ),
            (
                "diff",
                "Ev( diff(x, y) ) @ #i",
                "!St( diff(x, y) ) \u{25B6}\u{2082} #i",
                "diff(x, y) \u{228F} w",
            ),
            (
                "nullary_user_ac",
                "Ev( add ) @ #i",
                "!St( add ) \u{25B6}\u{2082} #i",
                "add \u{228F} w",
            ),
            (
                "binary_user_ac",
                "Ev( (x add y) ) @ #i",
                "!St( (x add y) ) \u{25B6}\u{2082} #i",
                "(x add y) \u{228F} w",
            ),
            (
                "nat_one",
                "Ev( %1 ) @ #i",
                "!St( %1 ) \u{25B6}\u{2082} #i",
                "%1 \u{228F} w",
            ),
        ];
        let node = LVar::new("i", LSort::Node, 0);
        let shapes = shape_terms();
        assert_eq!(shapes.len(), expected.len());
        for ((label, t), (elabel, action, premise, subterm)) in shapes.into_iter().zip(expected) {
            assert_eq!(label, elabel);
            let g = Goal::Action(node, ev_fact(t.clone()));
            assert_eq!(collapse(&render_goal_for_oracle(&g)), action, "{label}");
            let g = Goal::Premise((node, PremIdx(2)), st_fact(t.clone()));
            assert_eq!(collapse(&render_goal_for_oracle(&g)), premise, "{label}");
            let g = Goal::Subterm((t, msg("w")));
            assert_eq!(collapse(&render_goal_for_oracle(&g)), subterm, "{label}");
        }
    }

    /// The three arms with no term in them: `prettyNodeConc`/`prettyNodePrem`
    /// (Constraints.hs:255-261), `splitEqs` and the empty disjunction
    /// (Constraints.hs:281,285-286).
    #[test]
    fn the_termless_goal_arms_render_at_the_oracle_width() {
        let chain = Goal::Chain(
            (LVar::new("i", LSort::Node, 0), ConcIdx(1)),
            (LVar::new("j", LSort::Node, 3), PremIdx(0)),
        );
        assert_eq!(
            collapse(&render_goal_for_oracle(&chain)),
            "(#i, 1) ~~> (#j.3, 0)"
        );
        assert_eq!(
            collapse(&render_goal_for_oracle(&Goal::Split(SplitId(7)))),
            "splitEqs(7)"
        );
        assert_eq!(
            collapse(&render_goal_for_oracle(&Goal::Disj(Disj::new(vec![])))),
            "Disj (\u{22A5})"
        );
    }

    /// A fact holding all eight shapes runs past the oracle ribbon, so
    /// `prettyFact`'s `nestShort'` (Theory/Model/Fact.hs:572) breaks the
    /// argument list and indents the continuation by the lead's width plus
    /// one.  `concat . lines` joins the two lines, leaving that indent inside
    /// the string the oracle reads — six spaces after the comma.
    #[test]
    fn a_wide_action_goal_keeps_the_nest_short_indent_in_the_oracle_string() {
        let wide: LNFact = Fact::new(
            FactTag::Proto(Multiplicity::Linear, intern_str("Wide"), 8),
            shape_terms().into_iter().map(|(_, t)| t).collect(),
        );
        let g = Goal::Action(LVar::new("i", LSort::Node, 0), wide);
        assert_eq!(
            collapse(&render_goal_for_oracle(&g)),
            "Wide( (~a*~b), (~a\u{2295}~b), <x, y, z>, 'g'^~a, diff(x, y), add,\
             \u{20}     (x add y), %1) @ #i"
        );
    }
}

#[cfg(test)]
mod manual_rule_variants_tests {
    use super::*;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
    use crate::theory::{
        contains_manual_rule_variants, contains_open_rule_variants, merge_open_proto_rules,
        OpenProtoRule,
    };

    type Item = TheoryItem<OpenProtoRule>;

    /// A rule item whose AC half carries `action_names` on top of the E half —
    /// the shape `addActionClosedProtoRule` leaves behind, which adds the
    /// `AUTO_*` actions to `cprRuleAC` alone (lib/theory/src/Rule.hs:95-99).
    fn elab_rule(name: &str, action_names: &[&str]) -> Item {
        let e: ProtoRuleE = Rule::new(ProtoRuleEInfo::standard(name), vec![], vec![], vec![]);
        let mut opr = OpenProtoRule::new(e.clone());
        if !action_names.is_empty() {
            opr.rule.actions = action_names
                .iter()
                .map(|a| proto_fact(Multiplicity::Linear, a, vec![]))
                .collect();
            opr.rule_e = Some(Box::new(e));
        }
        TheoryItem::Rule(opr)
    }

    fn gate(items: &[Item]) -> bool {
        let old = contains_manual_rule_variants(&merge_open_proto_rules(items));
        assert_eq!(contains_open_rule_variants(items), old);
        old
    }

    /// `containsManualRuleVariants` (OpenTheory.hs:584-589) is the OR over the
    /// merged items' AC lists, and an `AUTO_*` action separates a rule's AC
    /// half from its E half by action count, so `equalUpToTerms` keeps it
    /// (lib/theory/src/Rule.hs:52-59).  Partial evaluation refines one rule
    /// into several of the SAME name and auto-sources annotates them by name,
    /// so every member of a same-name group opens the gate alike.
    #[test]
    fn an_auto_action_opens_the_gate() {
        let auto_out = "AUTO_OUT_TERM_1_0_0__Recv";
        assert!(gate(&[
            elab_rule("Send", &[auto_out]),
            elab_rule("Send", &[auto_out]),
            elab_rule("Recv", &["AUTO_IN_TERM_1_0_0__Recv"]),
        ]));
        // The gate is an OR over the rules.  The mixed theory above still
        // fires if the discriminant loses one of the two prefixes.  Each
        // prefix therefore gets a single-rule theory of its own.
        for auto in [auto_out, "AUTO_IN_TERM_1_0_0__Recv"] {
            assert!(
                gate(&[elab_rule("R", &[auto])]),
                "{auto} alone must open the gate",
            );
        }
    }

    /// A theory whose rules' AC halves say what their E halves say leaves the
    /// gate off, duplicated names included.
    #[test]
    fn matching_ac_and_e_halves_leave_the_gate_off() {
        assert!(!gate(&[
            elab_rule("Send", &[]),
            elab_rule("Send", &[]),
            elab_rule("Recv", &[]),
        ]));
    }
}

#[cfg(test)]
mod ac_variants_block_tests {
    use crate::fact::{in_fact, out_fact, proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule, RuleAttributes};
    use crate::theory::OpenProtoRule;
    use tamarin_term::function_symbols::{zero_sym, AcSym, FunSym};
    use tamarin_term::lterm::{LNTerm, LSort, LVar};
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    use tamarin_term::term::{f_app_ac, f_app_no_eq, Term};
    use tamarin_term::vterm::var_term;

    /// A message-sort variable at index 0 — how the abstracted AC rule
    /// spells the variables its variant substitutions bind.
    fn msg(name: &str) -> LVar {
        LVar::new(name, LSort::Msg, 0)
    }

    fn term(v: LVar) -> LNTerm {
        var_term(v)
    }

    /// The `nest 2 (multiComment (prettyProtoRuleAC ruAC))` block
    /// `prettyClosedProtoRule` puts under a rule whose AC form differs from
    /// its E form (ClosedTheory.hs:349-353).
    fn ac_block(o: &OpenProtoRule) -> String {
        let acs = crate::theory::closed_rules_ac(o);
        crate::pretty_hpj::multi_comment(crate::rule::pretty_proto_rule_ac(&acs[0]))
            .nest(2)
            .render()
    }

    /// `features/xor/basicfunctionality/xor0.spthy`'s `receive` rule as the
    /// closing pipeline leaves it: one abstracted variable in the body, and
    /// the two substitutions Maude's narrowing returns for it.
    fn xor0_receive() -> OpenProtoRule {
        let z = msg("z");
        let mut info = ProtoRuleEInfo::standard("receive");
        info.attributes.ignore_deriv_checks = true;
        let mut open = OpenProtoRule::new(Rule::new(
            info,
            vec![in_fact(term(z))],
            vec![],
            vec![proto_fact(Multiplicity::Linear, "Response", vec![term(z)])],
        ));
        let a = LVar::new("a", LSort::Fresh, 4);
        let b = LVar::new("b", LSort::Fresh, 4);
        open.variant_substs = vec![
            LNSubstVFresh::from_list([(z, f_app_no_eq(zero_sym(), vec![]))]),
            LNSubstVFresh::from_list([(z, f_app_ac(AcSym::Xor, vec![term(a), term(b)]))]),
        ];
        open
    }

    /// `sapic/fast/basic/typing.spthy`'s `outxloly_0_11121111111` rule: a
    /// multiset union in a conclusion, and an attribute list long enough
    /// that the header's `fsep` wraps.
    fn typing_outxloly() -> OpenProtoRule {
        let vars: Vec<LVar> = ["a", "n", "x", "y"].into_iter().map(msg).collect();
        let args: Vec<LNTerm> = vars.iter().map(|v| term(*v)).collect();
        let union = f_app_ac(AcSym::Union, vec![term(vars[2]), term(vars[3])]);
        let mut info = ProtoRuleEInfo::standard("outxloly_0_11121111111");
        info.attributes = RuleAttributes {
            color: tamarin_utils::color::hex_to_rgb("6c8040"),
            process: None,
            ignore_deriv_checks: false,
            is_sapic_rule: true,
            role: Some("P".to_string()),
        };
        OpenProtoRule::new(Rule::new(
            info,
            vec![proto_fact(
                Multiplicity::Linear,
                "State_11121111111",
                args.clone(),
            )],
            vec![
                proto_fact(Multiplicity::Linear, "State_111211111111", args),
                out_fact(union),
            ],
            vec![],
        ))
    }

    /// The block prints the internal rule's AC arguments in the order the
    /// rule holds them.  Both expectations are the bytes the Haskell oracle
    /// at the submodule pin prints for the named corpus rule.
    #[test]
    fn the_ac_block_keeps_the_internal_ac_order() {
        assert_eq!(
            ac_block(&xor0_receive()),
            concat!(
                "  /*\n",
                "  rule (modulo AC) receive[no_derivcheck]:\n",
                "     [ In( z ) ] --[ Response( z ) ]-> [ ]\n",
                "    variants (modulo AC)\n",
                "    1. z     = zero\n",
                "    \n",
                "    2. z     = (~a.4\u{2295}~b.4)\n",
                "  */",
            ),
        );
        assert_eq!(
            ac_block(&typing_outxloly()),
            concat!(
                "  /*\n",
                "  rule (modulo AC) outxloly_0_11121111111[color=#6c8040, issapicrule,\n",
                "                                          role='P']:\n",
                "     [ State_11121111111( a, n, x, y ) ]\n",
                "    -->\n",
                "     [ State_111211111111( a, n, x, y ), Out( (x++y) ) ]\n",
                "  */",
            ),
        );
    }

    /// HS sorts an AC argument list at construction (`fAppAC`,
    /// Term/Term/Raw.hs:118-129#fAppAC) and `prettyFact`
    /// (Theory/Model/Fact.hs:566-574#prettyFact) prints what it is handed,
    /// so a body holding the two operands the other way round prints them
    /// that way round.
    #[test]
    fn the_ac_block_does_not_re_sort_the_ac_arguments() {
        let mut rule = typing_outxloly();
        let x = term(msg("x"));
        let y = term(msg("y"));
        let reversed = Term::App(FunSym::Ac(AcSym::Union), vec![y, x].into());
        *rule.rule.conclusions.last_mut().expect("Out conclusion") = out_fact(reversed);
        let block = ac_block(&rule);
        assert!(block.contains("Out( (y++x) )"), "{block}");
    }
}

#[cfg(test)]
mod stored_proof_reparse_tests {
    use super::*;

    /// A stored `solve( ... )` step is echoed from the `Goal` the proof
    /// parser read, so its layout is the printer's and not the file's, and
    /// the goal grammar reads a user `[AC]` symbol's INFIX spelling only when
    /// the theory declares the symbol — HS's `acterm` takes the same set from
    /// the signature in parser state (Theory/Text/Parser/Term.hs:166-172).
    #[test]
    fn a_stored_goal_is_echoed_from_its_parsed_value() {
        let src = |decl: &str| {
            format!(
                "theory T begin\n{decl}\nlemma L: exists-trace \"T\"\n\
                 simplify\nsolve( !KU( (x add\n         y) ) @ #i )\n  by sorry\nend"
            )
        };
        let thy = tamarin_parser::parser::parse_theory(&src("functions: add/2 [AC]"), &[]).unwrap();
        let echo = pretty_open_theory(&crate::elaborate::elaborate(&thy).unwrap());
        assert!(
            echo.contains("solve( !KU( (x add y) ) @ #i )"),
            "the stored wrapping must not survive the echo: {echo}"
        );

        // Without the declaration the infix spelling is not a term, so the
        // goal grammar rejects it, so the stored proof makes the entire
        // theory invalid just as it does in Haskell.
        assert!(tamarin_parser::parser::parse_theory(&src("functions: add/2"), &[]).is_err());
    }
}

#[cfg(test)]
mod predicate_echo_tests {
    use super::*;

    /// HS `prettyPredicate` (TheoryObject.hs:845-849) lays the predicate's
    /// fact and formula out with `render`, HughesPJ's default style, and
    /// embeds the two as one `text`.  That style is 100 columns with 1.5
    /// ribbons per line, which `fullRender` rounds to a ribbon of 67
    /// (HughesPJ.hs:940, :1010), while the theory echo around the predicate
    /// item is laid out by the console's `renderDoc` at 110/73.  So a
    /// predicate formula breaks where 67 columns of ribbon run out, not
    /// where 73 do: `Between`'s inner conjunction is 68 columns wide and
    /// breaks, and its second operand starts a line of its own.
    ///
    /// Expected string: the pinned oracle's bytes for this theory.
    #[test]
    fn predicate_formula_wraps_at_the_default_style() {
        const SRC: &str = "theory P4PredWidth\n\
begin\n\
rule R:\n  [ In( x ) ] --[ Ev( x ) ]-> [ ]\n\
predicate: Between(x, y, z) <=> \
(Ex #i #j #k. Ev(x) @ #i & Ev(y) @ #j & Ev(z) @ #k & #i < #j & #j < #k)\n\
end\n";
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let elaborated = crate::elaborate::elaborate(&parsed).expect("theory elaborates");
        let predicate = elaborated.predicates().next().expect("predicate item");
        assert_eq!(
            pretty_predicate(predicate),
            concat!(
                "predicate: Between( x, y, z )<=>\u{2203} #i #j #k.\n",
                " ((((Ev( x ) @ #i) \u{2227} (Ev( y ) @ #j)) \u{2227} (Ev( z ) @ #k)) \u{2227}\n",
                "  (#i < #j)) \u{2227}\n",
                " (#j < #k)",
            )
        );
    }
}

#[cfg(test)]
mod closed_restriction_tests {
    use super::*;

    /// The fixture theory of `scripts/divergence_fixtures/s3_macro_lemma_header.spthy`,
    /// cut to its restrictions: `MacroRestriction` calls a macro and a
    /// predicate, `PlainRestriction` neither.
    const SRC: &str = "theory S3MacroLemmaHeader\n\
begin\n\
predicates:\n  IsPairOf(m, a, b) <=> m = <a, b>\n\
macros:\n  tag(x) = <'t', x>, wrap(x, y) = tag(<x, y>)\n\
rule A:\n  [ In( <x, y> ) ] --[ A( wrap(x, y) ) ]-> [ Out( tag(x) ) ]\n\
restriction PlainRestriction:\n  \"All m #i. A( m ) @ #i ==> not( m = 'no' )\"\n\
restriction MacroRestriction:\n  \"All m x y #i. A( m ) @ #i & IsPairOf(m, x, y) ==> m = wrap(x, y)\"\n\
end\n";

    /// HS `prettyRestriction` quotes `fromMaybe expandedFormula ogFormula`
    /// above the block and `expandedFormula` inside it
    /// (TheoryObject.hs:893, :895-898), and `applyMacroInRestriction` fills
    /// `ogFormula` with the pre-macro formula
    /// (Theory/Model/Restriction.hs:164-166).  So the macro call `wrap(x, y)`
    /// stands on top and its expansion `<'t', x, y>` in the block, while the
    /// predicate atom `IsPairOf(m, x, y)` is inlined in both — parse-time
    /// expansion, which `liftedAddRestriction` runs over the stored formula
    /// and its original alike (Theory/Text/Parser.hs:129-139).
    ///
    /// Expected strings are the pinned oracle's bytes for the fixture
    /// (`scripts/divergence_fixtures/expected/s3_macro_lemma_header.theory.hs.txt`).
    #[test]
    fn closed_restriction_prints_the_original_on_top_and_the_expanded_in_the_block() {
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let elaborated = crate::elaborate::elaborate(&parsed).expect("theory elaborates");
        let rendered = web_restrictions(&elaborated);
        assert_eq!(
            rendered,
            vec![
                "restriction PlainRestriction:\n  \
                 \"∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))\"\n  \
                 // safety formula\n\n  \
                 /*\n  expanded formula:\n  \
                 \"∀ m #i. (A( m ) @ #i) ⇒ (¬(m = 'no'))\"\n  */",
                "restriction MacroRestriction:\n  \
                 \"∀ m x y #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ⇒ (m = wrap(x, y))\"\n  \
                 // safety formula\n\n  \
                 /*\n  expanded formula:\n  \
                 \"∀ m x y #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ⇒ (m = <'t', x, y>)\"\n  */",
            ]
        );
    }
}

#[cfg(test)]
mod restriction_attribute_tests {
    use super::*;

    /// HS's restriction parser accepts no attribute list at all —
    /// `restriction varp nodep = Restriction <$> (symbol "restriction" *>
    /// identifier <* colon) <*> doubleQuoted (standardFormula varp nodep)
    /// <*> pure Nothing` (Theory/Text/Parser/Restriction.hs:77-81) — and only
    /// `diffRestriction` (`:95-100`) does, so `prettyRestriction`
    /// (TheoryObject.hs:889-901) has no attribute to print.  RS's parser is
    /// lenient here and reads `[left]`/`[right]` in a non-diff theory; neither
    /// print carries it through.
    #[test]
    fn restriction_attributes_are_not_printed() {
        const SRC: &str = "theory RestrictionAttrs\n\
begin\n\
rule A:\n  [ In( x ) ] --[ A( x ) ]-> [ ]\n\
restriction Sided [left]:\n  \"All x #i. A( x ) @ #i ==> not( x = 'no' )\"\n\
end\n";
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let elaborated = crate::elaborate::elaborate(&parsed).expect("theory elaborates");
        let closed = web_restrictions(&elaborated);
        assert_eq!(closed.len(), 1);
        assert!(
            closed[0].starts_with("restriction Sided:\n"),
            "closed print: {}",
            closed[0]
        );
        let open = pretty_open_theory(&elaborated);
        assert!(open.contains("restriction Sided:\n"), "open print: {open}");
        assert!(!open.contains("[left]"), "open print: {open}");
    }
}

#[cfg(test)]
mod closed_lemma_tests {
    use super::*;

    /// The fixture theory of `scripts/divergence_fixtures/s3_macro_lemma_header.spthy`,
    /// cut to its lemmas: `MacroLemma` calls a macro and a predicate,
    /// `PlainLemma` neither.
    const SRC: &str = "theory S3MacroLemmaHeader\n\
begin\n\
predicates:\n  IsPairOf(m, a, b) <=> m = <a, b>\n\
macros:\n  tag(x) = <'t', x>, wrap(x, y) = tag(<x, y>)\n\
rule A:\n  [ In( <x, y> ) ] --[ A( wrap(x, y) ) ]-> [ Out( tag(x) ) ]\n\
rule B:\n  [ In( z ) ] --[ B( z ) ]-> [ ]\n\
lemma PlainLemma:\n  all-traces\n  \"All z #i. B( z ) @ #i ==> Ex #j. A( z ) @ #j\"\n\
lemma MacroLemma:\n  exists-trace\n  \"Ex x y m #i. A( m ) @ #i & IsPairOf(m, x, y) & m = wrap(x, y)\"\n\
end\n";

    /// HS `prettyLemma` quotes `fromMaybe expandedFormula ogFormula` on the
    /// header line and converts `expandedFormula` for the guarded block
    /// (lib/theory/src/Lemma.hs:121, :125), and `applyMacroInLemma` fills
    /// `ogFormula` with the pre-macro formula (lib/theory/src/Lemma.hs:83-88).
    /// So the macro call `wrap(x, y)` stands in the header and its expansion
    /// `<'t', x, y>` in the block, while the predicate atom `IsPairOf(m, x, y)`
    /// is inlined in both — parse-time expansion, which `liftedAddLemma` runs
    /// over the stored formula and its original alike
    /// (Theory/Text/Parser.hs:141-152).
    ///
    /// Expected strings are the pinned oracle's bytes for the fixture
    /// (`scripts/divergence_fixtures/expected/s3_macro_lemma_header.theory.hs.txt`).
    #[test]
    fn closed_lemma_header_uses_the_original_and_the_guarded_block_the_expanded() {
        let parsed = tamarin_parser::parse_theory(SRC, &[]).expect("theory parses");
        let elaborated = crate::elaborate::elaborate(&parsed).expect("theory elaborates");
        let rendered: Vec<String> = elaborated
            .lemmas()
            .map(|l| pretty_lemma(l, "by sorry", ""))
            .collect();
        assert_eq!(
            rendered,
            vec![
                "lemma PlainLemma:\n  \
                 all-traces \"∀ z #i. (B( z ) @ #i) ⇒ (∃ #j. A( z ) @ #j)\"\n\
                 /*\nguarded formula characterizing all counter-examples:\n\
                 \"∃ z #i. (B( z ) @ #i) ∧ ∀ #j. (A( z ) @ #j) ⇒ ⊥\"\n*/\nby sorry",
                "lemma MacroLemma:\n  exists-trace\n  \
                 \"∃ x y m #i. ((A( m ) @ #i) ∧ (m = <x, y>)) ∧ (m = wrap(x, y))\"\n\
                 /*\nguarded formula characterizing all satisfying traces:\n\
                 \"∃ x y m #i. (A( m ) @ #i) ∧ (m = <x, y>) ∧ (m = <'t', x, y>)\"\n*/\nby sorry",
            ]
        );
    }
}

#[cfg(test)]
mod heuristic_header_tests {
    use super::*;

    #[test]
    fn default_oracle_name_matches_haskell_path_splitting() {
        assert_eq!(oracle_candidate_for_theory("thy.spthy"), "thy.oracle");
        assert_eq!(oracle_candidate_for_theory("a.b.spthy"), "a.oracle");
        assert_eq!(oracle_candidate_for_theory("dir/thy.spthy"), "/thy.oracle");
        assert_eq!(oracle_candidate_for_theory("./thy.spthy"), "/thy.oracle");
        assert_eq!(oracle_candidate_for_theory(".thy.spthy"), ".thy.oracle");
        assert_eq!(
            oracle_candidate_for_theory("dir.v2/foo.spthy"),
            "dir.oracle"
        );
        assert_eq!(oracle_name_for_theory("missing.spthy"), "oracle");
    }

    /// The `heuristic:` header prints the theory's stored rankings (HS `text
    /// "heuristic: " <> text (prettyGoalRankings thyH)`,
    /// TheoryObject.hs:756-768, see line 764): a letter run spells its
    /// rankings out one per token, an oracle ranking adds its quoted path —
    /// the theory file's default oracle name when the source names none — and
    /// a tactic ranking prints the name between its braces, whether or not the
    /// theory declares a tactic of that name.  The `tactic:` block sits after
    /// the header, so the header's `{rank}` resolves against a declaration
    /// the parser has not reached yet.
    #[test]
    fn the_header_prints_the_stored_rankings() {
        let src = "theory T\nbegin\n\n\
                   heuristic: sop {rank} O \"./my-oracle\" {.}\n\n\
                   tactic: rank\npresort: C\nprio:\n    regex \"Out\"\n\n\
                   lemma L: exists-trace \"T\"\n\nend";
        let parsed = tamarin_parser::parser::parse_theory(src, &[]).expect("theory parses");
        let thy = crate::elaborate::elaborate_with_in_file(&parsed, "f.spthy")
            .expect("theory elaborates");
        assert!(
            pretty_open_theory(&thy)
                .contains("heuristic: s o \"oracle\" p {rank} O \"./my-oracle\" {.}"),
            "{}",
            pretty_open_theory(&thy)
        );
    }
}
