// Currently GPL 3.0 until granted permission by the following authors:
//   kevinmorio, arcz, meiersi, rkunnema, yavivanov, jdreier, Nynko,
//   cascremers, felixlinker, Azurios-git, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Warnings.hs,
//   lib/theory/src/Theory/Text/Parser.hs,
//   lib/utils/src/Text/PrettyPrint/Html.hs,
//   src/Main/Mode/Interactive.hs, src/Main/TheoryLoader.hs,
//   src/Web/Dispatch.hs, src/Web/Handler.hs

//! Parse + elaborate a `.spthy` file into a [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tamarin_parser::parse_theory;
use tamarin_parser::wf::{
    after_public_names_topics, insert_wf_before, WfError, WF_AFTER_CHECK_GUARDED,
    WF_AFTER_CHECK_TERMS, WF_AFTER_FACT_LHS, WF_TOPIC_ORDER,
};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::elaborate::elaborate;

use crate::state::{TheoryEntry, TheoryOrigin};

#[derive(Debug)]
pub enum LoadError {
    Io(String),
    Parse(String),
    Elaborate(String),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io(s) => write!(f, "IO error: {}", s),
            // `Parse` already holds the fully-rendered parsec frame (HS `show
            // err` = `show (ParserError e) = show e`, TheoryLoader.hs:396-398, see line 397), so
            // it is emitted verbatim — no `parse error:` prefix, which HS never
            // prints.  This is what lands inside the eager-load dashed block
            // (Dispatch.hs:191-198 `show err`) and after the web upload's
            // "Theory loading failed:\n" banner (Handler.hs:785-817, see line 803).
            LoadError::Parse(s) => write!(f, "{}", s),
            LoadError::Elaborate(s) => write!(f, "elaboration error: {}", s),
        }
    }
}
impl std::error::Error for LoadError {}

/// Read the file, parse it, elaborate it, and return a [`TheoryEntry`].
///
/// `entry.idx` is left as `0`; [`TheoryStore::insert`] assigns the
/// real index.
pub fn load_from_path(
    path: &Path,
    maude_path: &str,
    derivcheck_timeout: u32,
) -> Result<TheoryEntry, LoadError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| LoadError::Io(format!("{}: {}", path.display(), e)))?;
    load_from_source(
        &src, TheoryOrigin::Local(PathBuf::from(path)), maude_path, derivcheck_timeout)
}

/// Parse + elaborate from a string (for the upload path), then "close"
/// the theory by pre-computing each protocol rule's AC-variants via
/// Maude (HS `closeTheory`), so the source / rules / overview renderers
/// can emit the `variants (modulo AC)` blocks byte-for-byte.  Variant
/// computation is best-effort: if Maude can't be started the theory is
/// still usable (rules just render without their variants block).
pub fn load_from_source(
    src: &str,
    origin: TheoryOrigin,
    maude_path: &str,
    derivcheck_timeout: u32,
) -> Result<TheoryEntry, LoadError> {
    // Inject the parsec `SourcePos` name (the path HS prints in the frame
    // header) from the origin: a local file's on-disk path, or the uploaded
    // filename — the same value HS passes as `inFile`/`filename` to
    // `parseString` (Dispatch.hs:149-209, see line 167 `thLoad srcThy path`; Handler.hs:785-817, see line 800
    // `loadAndCloseTheory srcContent filename`).  `LoadError::Parse` then holds
    // the byte-for-byte parsec frame.
    let source_name = origin.label();
    let mut parser_theory = parse_theory(src, &[])
        .map_err(|e| LoadError::Parse(e.with_source(source_name).to_string()))?;

    // HS `liftedAddProtoRule` (Theory/Text/Parser.hs:166-193) expands each
    // rule's `_restrict(φ)` into a fresh `Restr_<rule>_<i>` restriction
    // (inserted before the rule) and rewrites the rule's actions DURING
    // parsing.  RS captures `_restrict` into `Rule.embedded_restrictions`
    // at parse time; run the lifting pass here, immediately after parse and
    // BEFORE the wellformedness clone / elaboration / SAPIC translation —
    // the exact position the CLI uses (run.rs:507) — so the transformed
    // parser theory drives every web renderer (rules / source / message /
    // graphs / sequents).
    tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parser_theory)
        .map_err(|e| LoadError::Parse(format!(
            "_restrict expansion failed: {}", e.message)))?;

    // HS lifecycle markers, stderr via `traceM`: "Theory loaded" right
    // after parsing (TheoryLoader.hs:401-424, see line 409; `liftedAddProtoRule` runs
    // during parsing, so post-lift here is the same point).
    eprintln!("[Theory {}] Theory loaded", parser_theory.name);

    // Wellformedness report — computed by the SAME pipeline `--prove` runs
    // (`run.rs`'s `checkWellformedness`, mirroring HS `TheoryLoader.hs`), so the
    // interactive web UI surfaces exactly the warnings HS does.  HS runs
    // `checkWellformedness` at theory load (before any proving), so running it
    // here — including the Maude-backed derivation check in the block below — is
    // faithful.  The result feeds two renderings: the `/* WARNING: ... */`
    // comment in the source/message routes (`format_wf_block`) and the
    // `<div class="wf-warning">` header banner in help/overview (`errors_html`).
    //
    // Static checks run on the PRE-translation parsed theory (HS runs
    // `check_theory` BEFORE the SAPIC `translate` pass, run.rs:517-528).  HS
    // `thyProtoRules` applies `applyMacroInRule` to every rule before the
    // checks, so clone + macro-expand first.
    let parsed_for_wf = tamarin_theory::macro_expand::macro_expanded_clone(&parser_theory);
    let mut wf_report = tamarin_parser::wf::check_theory(&parsed_for_wf);
    // Strip the STATIC "Message Derivation Checks" entry — the dynamic,
    // Maude-backed check in the maude block below replaces it (run.rs:527-528).
    wf_report.retain(|e| e.topic != "Message Derivation Checks");

    // "Theory translated" at the START of translation (TheoryLoader.hs:448-460, see line 454
    // prints before `processOpenTheory` runs); RS's `elaborate` is that
    // translation step.
    eprintln!("[Theory {}] Theory translated", parser_theory.name);
    let mut typed = elaborate(&parser_theory)
        .map_err(|e| LoadError::Elaborate(e.message))?;
    // Oracle path resolution base (HS Parser.hs:230-393, see line 304 sets `inFile` at load;
    // `heuristic: o "./oracle-…"` then resolves against the theory's own
    // directory, `hs_take_directory`).  Local files carry their on-disk
    // path; uploads keep the bare filename (dir "." — as in HS, where an
    // uploaded theory has no on-disk home).
    typed.in_file = origin.label();
    let maude_sig = typed.signature.maude_sig.clone();

    // Subterm-convergence check on the signature's subterm-rule set
    // (run.rs:577-580): replace `check_theory`'s AST-level placeholder with the
    // signature-driven, width-wrapped version now that the MaudeSig exists.
    wf_report.retain(|e| e.topic != "Subterm Convergence Warning");
    wf_report.extend(
        tamarin_theory::pretty_theory::subterm_convergence_report_wf(&maude_sig),
    );

    // Formula terms (run.rs:601-616): needs the elaborated MaudeSig
    // (reducible/irreducible funsym classification), so it runs here rather than
    // inside `check_theory`.  Insert BEFORE the guardedness / lemma-annotation
    // topics to match HS `formulaReports` order (8b before 8c/9).
    {
        let term_errors = tamarin_theory::check_terms::check_terms_wf(
            &parsed_for_wf, &maude_sig);
        insert_wf_before(&mut wf_report, term_errors,
            &WF_TOPIC_ORDER[WF_AFTER_CHECK_TERMS..]);
    }

    // Formula guardedness (run.rs:638-656): each lemma/restriction formula that
    // cannot be converted to a guarded formula.  Runs on the PRE-translation
    // parser theory (HS `formulaReports`), before the SAPIC pass below.
    {
        let guard_errors = tamarin_theory::elaborate::check_guarded_wf(&parser_theory);
        insert_wf_before(&mut wf_report, guard_errors,
            &WF_TOPIC_ORDER[WF_AFTER_CHECK_GUARDED..]);
    }

    // SAPIC `process:` translation — mirror `run.rs`'s CLI-side pass
    // (run.rs:658-696) so the web load path renders SAPIC theories exactly
    // like `--prove`.  Runs ONLY for `is_sapic` theories (exactly one
    // top-level `process:`); `apply_sapic` returns `Ok(vec![])` when
    // `!typed.is_sapic`, so it is safe to call unconditionally and leaves
    // non-process theories byte-unchanged.  It injects the generated MSR
    // rules + `single_session` restriction + `heuristic: p` into BOTH
    // `parser_theory` (which drives the web rules / source / message
    // renderers) and `typed` (for AC-variant pre-computation), so it MUST run
    // before `populate_rule_variants` below.  `user_set_heuristic` is true iff
    // a `heuristic:` item already populated `typed.heuristic` (HS
    // `addHeuristic` returns `Nothing` in that case).
    //
    // Install the user/builtin function-symbol flag sets
    // (`USER_PRIVATE_FUNS` / `USER_DESTRUCTOR_FUNS` / …) for the duration of
    // BOTH the SAPIC translation AND the variant pre-computation below.  These
    // thread-locals drive `term_to_lnterm`'s symbol resolution (privacy /
    // constructability); `elaborate()` sets them only for its own scope, so
    // without re-installing them here the SAPIC-injected rules' builtin
    // symbols (`rep` private, `check_rep` / `get_rep` destructors from
    // `locations-report`) re-elaborate with the default public-constructor
    // flags, serialising as `tamXC..` — which Maude rejects, leaving the rule
    // with "no variants".  The guard must therefore stay alive across the
    // `populate_rule_variants` call in the maude block below (it does: this
    // binding lives to the end of the function).
    let _sapic_funs_guard =
        tamarin_theory::elaborate::set_user_funs_for_theory(&parser_theory);
    // HS `Acc.checkWellformedness t` (translateTheory, TheoryLoader.hs:448-460, see line 455)
    // runs on the PRE-translation theory — before `apply_sapic` injects the
    // SAPIC-generated rules (mirrors run.rs's CLI-side placement).
    let acc_wf = tamarin_accountability::check_wellformedness(&parser_theory);
    let user_set_heuristic = !typed.heuristic.is_empty();
    // HS `Sapic.checkWellformedness` (Warnings.hs) is part of `preReport`, which
    // is PREPENDED to the rest of the report (run.rs:685-695).  A hard
    // translation error still propagates as `LoadError::Elaborate`.
    let sapic_wf = tamarin_sapic::apply::apply_sapic(
        &mut parser_theory, &mut typed, user_set_heuristic,
    ).map_err(|e| LoadError::Elaborate(e.message))?;
    // Accountability translation (HS `Sapic.translate >=> Acc.translate`,
    // TheoryLoader.hs:428-443, see line 430): expands each `… accounts for` lemma into its
    // verification-condition lemmas + case-test predicates, injecting into
    // BOTH `parser_theory` (web renderers) and `typed` (lemma list, proof
    // state).  Without this the web UI has no pages for the VC sub-lemmas
    // batch `--prove` proves.  No-op for theories without accountability
    // lemmas / case tests.
    tamarin_accountability::translate(&mut parser_theory, &mut typed)
        .map_err(|e| LoadError::Elaborate(e.to_string()))?;
    // `preReport` order (run.rs:922-927): SAPIC warnings, then the
    // accountability RP check, then the rest.
    if !sapic_wf.is_empty() || !acc_wf.is_empty() {
        let mut new_report = sapic_wf;
        new_report.extend(acc_wf);
        new_report.extend(std::mem::take(&mut wf_report));
        wf_report = new_report;
    }

    // HS re-runs the full `checkWellformedness` on the TRANSLATED theory
    // (run.rs:698-731): re-run `factLhsOccurNoRhs` on the post-translation
    // parsed theory so SAPIC-only premise facts (e.g. a `Message(c,m)` consumed
    // by an `in(c,m)` with no producing `out`) are surfaced.  No-op for
    // non-SAPIC theories (pre- and post-translation rule sets are equal).
    if typed.is_sapic {
        let post_thy = tamarin_theory::macro_expand::macro_expanded_clone(&parser_theory);
        let topic = "Facts occur in the left-hand-side but not in any right-hand-side ";
        wf_report.retain(|e| e.topic != topic);
        let lhs_rhs = tamarin_parser::wf::fact_lhs_occur_no_rhs(&post_thy);
        insert_wf_before(&mut wf_report, lhs_rhs,
            &WF_TOPIC_ORDER[WF_AFTER_FACT_LHS..]);
        // HS `publicNamesReport` runs on the TRANSLATED rules — the
        // parser-level report cannot see the source process a generated
        // rule carries as its `process=` attribute (run.rs:950-973, e.g.
        // CentralizedMonitor's `rule "Init":  name 'C', 'c'`).  Same
        // replace + splice as the batch path; the boundary list is
        // WF_TOPIC_ORDER minus "Unbound variables" (unboundReport runs
        // BEFORE publicNames in HS, so it must not act as a boundary),
        // headed by the variable-sorts topic.
        let caps_topic = "Public constants with mismatching capitalization";
        wf_report.retain(|e| e.topic != caps_topic);
        let public_names =
            tamarin_theory::elaborate::sapic_public_names_report(&typed);
        insert_wf_before(&mut wf_report, public_names, &after_public_names_topics());
    }

    if let Ok(maude) = MaudeHandle::start(maude_path, typed.signature.maude_sig.clone()) {
        tamarin_theory::tools::rule_variants::populate_rule_variants(&mut typed, &maude, None);
        // Annotate per-rule loop breakers on the stored theory so the web
        // rules / source / message renderers emit HS's `// loop breaker: [<n>]`
        // comments — HS `prettyClosedProtoRule` reads them from the
        // `ProtoRuleACInfo` baked into every closed rule.  Our prover computes
        // them inside `ProofContext::new` on a local copy; mirror `run.rs`'s
        // CLI-side pass here on the load path (identical writeback in source
        // order) so the byte-faithful `web_proto_rules` printer has them.
        use tamarin_theory::theory::{OpenProtoRule, TheoryItem};
        let mut rules: Vec<OpenProtoRule> = typed.items.iter().filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r.clone()),
            _ => None,
        }).collect();
        tamarin_theory::constraint::solver::context::annotate_loop_breakers(&mut rules, &maude);
        let mut iter = rules.into_iter();
        for item in typed.items.iter_mut() {
            if let TheoryItem::Rule(opr) = item {
                if let Some(updated) = iter.next() {
                    opr.loop_breakers = updated.loop_breakers;
                }
            }
        }

        // Dynamic Message Derivation Checks (run.rs:974-995): HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout` (HS
        // interactive default 5s).  The budget comes from ServerConfig
        // (CLI flag on the interactive path, 5s default otherwise) —
        // matching HS interactive, which honors the flag
        // (Main/Mode/Interactive.hs:39-63, see line 62).  Needs the Maude handle; runs on
        // the POST-translation parser theory (`parser_theory`, matching
        // run.rs's `&parsed` at that point).
        // HS brackets the check with stderr markers via `traceM`
        // (TheoryLoader.hs:463-533, see line 485,498) — emitted for every close (initial
        // load, upload, reload), and only when derivChecks != 0
        // (TheoryLoader.hs:482-483 skips the whole block on EQ).
        if derivcheck_timeout > 0 {
            eprintln!("[Theory {}] Derivation checks started", typed.name);
        }
        let extra = tamarin_theory::deriv_check::check_message_derivation(
            &parser_theory, &maude, derivcheck_timeout,
        );
        wf_report.extend(extra);
        if derivcheck_timeout > 0 {
            eprintln!("[Theory {}] Derivation checks ended", typed.name);
        }
    }

    // HS `makeWfErrorsHtml` (src/Web/Handler.hs:463-469) — the header-banner
    // rendering of the same report; empty string when the report is empty.
    let errors_html = make_wf_errors_html(&wf_report);

    // "Theory closed" at the end of `closeTheory` (TheoryLoader.hs:569-615, see line 596).
    eprintln!("[Theory {}] Theory closed", typed.name);

    Ok(TheoryEntry {
        idx: 0,
        name: typed.name.clone(),
        parser_theory: Arc::new(parser_theory),
        typed_theory: Arc::new(typed),
        origin,
        loaded_at: Local::now(),
        primary: true,
        wf_report,
        errors_html,
        proof_state: None,
    })
}

/// Build the HS `makeWfErrorsHtml` banner (`src/Web/Handler.hs:463-469`): wrap
/// the wellformedness report in a `<div class="wf-warning">`, prefixed by the
/// literal `WARNING: ...<br /><br />` line and followed by the report body
/// rendered exactly as HS's `renderHtmlDoc (htmlDoc $ prettyWfErrorReport
/// report)` — each source line HTML-escaped, its leading spaces turned into
/// `&nbsp;`, and a `<br/>` appended (HS `postprocessHtmlDoc`,
/// Text/PrettyPrint/Html.hs:157-162).  Empty report ⇒ empty string
/// (HS `makeWfErrorsHtml [] = ""`).
///
/// `format_wf_block` is reused as the single source of truth for the report
/// body: strip its `/* ... */` framing to recover the same
/// `prettyWfErrorReport` text HS feeds to `renderHtmlDoc`, then re-render it
/// HS-web-style.  Line-wrap width may differ from HS's web render, but the
/// parity gate compares structure/text (whitespace-collapsed), so only the
/// word tokens must match — which they do (the body is byte-identical to the
/// `--prove` `/* */` block, itself HS-byte-faithful).
fn make_wf_errors_html(report: &[WfError]) -> String {
    if report.is_empty() {
        return String::new();
    }
    let block = tamarin_theory::pretty_theory::format_wf_block(report);
    // `format_wf_block` frames the body as
    //   "/*\nWARNING: the following wellformedness checks failed!\n\n<body>*/"
    // where <body> is the byte-exact `prettyWfErrorReport` text.  Strip the
    // fixed prefix/suffix to recover just <body>.
    const PREFIX: &str = "/*\nWARNING: the following wellformedness checks failed!\n\n";
    let body = block
        .strip_prefix(PREFIX)
        .and_then(|b| b.strip_suffix("*/"))
        .unwrap_or(&block);
    // HS `renderHtmlDoc (htmlDoc …)` = `postprocessHtmlDoc . escape`: first
    // entity-escape the body's `& < > " '`, then run HS `postprocessHtmlDoc =
    // unlines . map (addBreak . indent) . lines` (Html.hs:157-162) — each
    // line's leading spaces become `&nbsp;` runs, `<br/>` is appended, and
    // lines rejoin with `\n` (trailing `\n`).  `html_escape` never touches
    // spaces or newlines, so escaping the whole body first is byte-equivalent
    // to escaping each line's non-leading remainder in the loop.
    let rendered = tamarin_theory::pretty_hpj::postprocess_html(
        &crate::handlers::root::html_escape(body));
    // HS `makeWfErrorsHtml`: <div> + literal WARNING line + rendered body + </div>.
    format!(
        "<div class=\"wf-warning\">\n\
         WARNING: the following wellformedness checks failed!<br /><br />\n\
         {rendered}\n</div>",
    )
}
