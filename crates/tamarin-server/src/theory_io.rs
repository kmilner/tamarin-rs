// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parse + elaborate a `.spthy` file into a [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use tamarin_parser::parse_theory_with_base;
use tamarin_parser::wf::WfError;
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
            // err` = `show (ParserError e) = show e`, TheoryLoader.hs:439), so
            // it is emitted verbatim — no `parse error:` prefix, which HS never
            // prints.  This is what lands inside the eager-load dashed block
            // (Dispatch.hs:194-201 `show err`) and after the web upload's
            // "Theory loading failed:\n" banner (Handler.hs:809).
            LoadError::Parse(s) => write!(f, "{}", s),
            LoadError::Elaborate(s) => write!(f, "elaboration error: {}", s),
        }
    }
}
impl std::error::Error for LoadError {}

// =============================================================================
// `--no-ndc` (HS `TheoryLoadOptions.ndcCheck`)
// =============================================================================

/// The no-deconstruction-chain switch every web load applies to the theory it
/// loads.
///
/// HS partially applies the interactive mode's `TheoryLoadOptions` into the
/// `loadTheory thyLoadOptions` closure handed to `withWebUI`
/// (Interactive.hs:135), so every load the server performs — startup, upload,
/// reload — carries the CLI value.  `loadTheory` ends in `addParamsOptions`
/// (TheoryLoader.hs:449-452), whose `addNdcOption` (TheoryLoader.hs:821-826)
/// writes `opt.ndcCheck` into the theory's own
/// `_thyOptions._deductionChainCheck`, overwriting whatever the theory carried;
/// `checkCloseIntrRule` then reads that field back (TheoryLoader.hs:513-519).
/// `ndcCheck` is `not (argExists "no-ndc")` (TheoryLoader.hs:365-366) and
/// defaults to `True` (TheoryLoader.hs:279) — hence the initial value here.
///
/// Process-wide, mirroring the single `thyLoadOptions` HS captures once per
/// interactive run: `run_interactive` sets it from the CLI flag before the
/// first load, and all three load sites (startup, upload, reload) read it
/// through [`load_from_source`].
static NDC_CHECK: AtomicBool = AtomicBool::new(true);

/// Set the NDC-check switch [`load_from_source`] applies (`true` = run the
/// check, i.e. `--no-ndc` absent).
pub fn set_ndc_check(on: bool) {
    NDC_CHECK.store(on, Ordering::Relaxed);
}

/// The NDC-check switch [`load_from_source`] applies to each loaded theory.
pub fn ndc_check() -> bool {
    NDC_CHECK.load(Ordering::Relaxed)
}

/// The parser flags every web load parses with — HS `toParserFlags
/// thyOpts` (TheoryLoader.hs:285-291) inside the same captured
/// `loadTheory thyLoadOptions` closure as [`NDC_CHECK`] above, so the
/// interactive CLI's `-D/--defines` (and `--quit-on-warning` element)
/// reach `#ifdef` evaluation on startup loads, uploads, and reloads
/// alike.  Empty until `run_interactive` sets it; library/test embedders
/// that never call [`set_parser_flags`] parse flag-free.
static PARSER_FLAGS: std::sync::RwLock<Vec<String>> = std::sync::RwLock::new(Vec::new());

/// Set the parser flags [`load_from_source`] passes to `parse_theory`
/// (the port of HS `toParserFlags`, minus the `["diff" | diffMode]`
/// element — see `run_interactive`'s call site).
pub fn set_parser_flags(flags: Vec<String>) {
    *PARSER_FLAGS.write().expect("PARSER_FLAGS poisoned") = flags;
}

/// The parser flags [`load_from_source`] applies to each loaded theory.
pub fn parser_flags() -> Vec<String> {
    PARSER_FLAGS.read().expect("PARSER_FLAGS poisoned").clone()
}

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
        &src,
        TheoryOrigin::Local(PathBuf::from(path)),
        maude_path,
        derivcheck_timeout,
    )
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
    // `parseString` (Dispatch.hs:170 `thLoad srcThy path`; Handler.hs:806
    // `loadAndCloseTheory srcContent filename`).  `LoadError::Parse` then holds
    // the byte-for-byte parsec frame.
    let source_name = origin.label();
    // Deliberate divergence, same policy as the other web error surfaces: a
    // theory that trips one of the GHC `error`s inside HS's parser (`macro`'s
    // reserved name / duplicate argument, Theory/Text/Parser/Macro.hs:34-38)
    // takes down the HS web handler with an uncaught exception.  Here the
    // failure travels as an ordinary `LoadError::Parse` and reaches the user
    // through the normal parse-error surface — `Display for ParseError` renders
    // a GHC `error` as its bare message, without the parsec frame the position
    // would fake or the `HasCallStack` block that only the CLI reproduces.
    // Parser flags (`-D` defines + the `quit-on-warning` element) from the
    // interactive CLI, via [`PARSER_FLAGS`]; `#include` paths resolve
    // against the theory file's own directory — HS threads `Just inFile`
    // into the `theory` parser (`loadTheory`, TheoryLoader.hs:449-458) and
    // `include` resolves against `takeDirectory <$> inFile0`
    // (Theory/Text/Parser.hs:306-343).  An upload has no on-disk home
    // (HS's bare filename gives `takeDirectory = "."`), so it resolves
    // CWD-relative, the no-base default.
    let flags_owned = parser_flags();
    let flags: Vec<&str> = flags_owned.iter().map(String::as_str).collect();
    let base_dir = match &origin {
        TheoryOrigin::Local(p) => p.parent().map(|d| d.to_path_buf()),
        _ => None,
    };
    let mut parser_theory = parse_theory_with_base(src, &flags, base_dir)
        .map_err(|e| LoadError::Parse(e.with_source(source_name).to_string()))?;

    // HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) expands each
    // rule's `_restrict(φ)` into a fresh `Restr_<rule>_<i>` restriction
    // (inserted before the rule) and rewrites the rule's actions DURING
    // parsing.  RS captures `_restrict` into `Rule.embedded_restrictions`
    // at parse time; run the lifting pass here, immediately after parse and
    // BEFORE the wellformedness clone / elaboration / SAPIC translation —
    // the exact position `run_batch` in run.rs uses — so the transformed
    // parser theory drives every web renderer (rules / source / message /
    // graphs / sequents).
    tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parser_theory)
        .map_err(|e| LoadError::Parse(format!("_restrict expansion failed: {}", e.message)))?;

    // HS lifecycle markers, stderr via `traceM`: "Theory loaded" right
    // after parsing (TheoryLoader.hs:449-452, see line 451; `liftedAddProtoRule` runs
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
    // `check_theory` BEFORE the SAPIC `translate` pass; `run_batch` opens
    // with the same shared pass — macro-expanded clone, `check_theory`,
    // static "Message Derivation Checks" entry dropped for the dynamic
    // check in the maude block below).
    let mut wf_report = tamarin_theory::translated_wf::pre_translation_wf_report(&parser_theory);

    // "Theory translated" at the START of translation (TheoryLoader.hs:494-500, see line 496
    // prints before `processOpenTheory` runs); RS's `elaborate` is that
    // translation step.
    eprintln!("[Theory {}] Theory translated", parser_theory.name);
    let mut typed = elaborate(&parser_theory).map_err(|e| LoadError::Elaborate(e.message))?;
    // HS `addParamsOptions`' `addNdcOption` (TheoryLoader.hs:821-826), the last
    // step of `loadTheory` (TheoryLoader.hs:449-452): the CLI's `ndcCheck`
    // becomes the loaded theory's `_deductionChainCheck`, which the NDC pass in
    // the maude block below reads back.  [`NDC_CHECK`] carries the flag here.
    typed.options.deduction_chain_check = ndc_check();
    // Oracle path resolution base: HS threads the parser's `inFile` into
    // `defaultOracleNames` (Theory/Text/Parser.hs:250), so a
    // `heuristic: o "./oracle-…"` resolves against the theory's own
    // directory (`hs_take_directory`).  Local files carry their on-disk
    // path; uploads keep the bare filename (dir "." — as in HS, where an
    // uploaded theory has no on-disk home).
    typed.in_file = origin.label();
    let maude_sig = typed.signature.maude_sig.clone();

    // Subterm-convergence check on the signature's subterm-rule set (the
    // same swap `run_batch` performs, shared in `translated_wf`).
    tamarin_theory::translated_wf::swap_subterm_convergence_report(&mut wf_report, &maude_sig);

    // SAPIC `process:` translation — mirror `run_batch`'s CLI-side pass so
    // the web load path renders SAPIC theories exactly like `--prove`.  Runs
    // ONLY for `is_sapic` theories (exactly one top-level `process:`);
    // `apply_sapic` returns `Ok(vec![])` when
    // `!typed.is_sapic`, so it is safe to call unconditionally and leaves
    // non-process theories byte-unchanged.  It injects the generated MSR
    // rules + `single_session` restriction + `heuristic: p` into BOTH
    // `parser_theory` (which drives the web rules / source / message
    // renderers) and `typed` (for AC-variant pre-computation), so it MUST run
    // before `populate_rule_variants` below.  `user_set_heuristic` is true iff
    // a `heuristic:` item already populated `typed.heuristic` (HS
    // `addHeuristic` returns `Nothing` in that case).
    // HS `Acc.checkWellformedness t` (translateTheory, TheoryLoader.hs:494-500, see line 497)
    // runs on the PRE-translation theory — before `apply_sapic` injects the
    // SAPIC-generated rules (mirrors run.rs's CLI-side placement).
    let acc_wf = tamarin_accountability::check_wellformedness(&parser_theory, &typed);
    let user_set_heuristic = !typed.heuristic.is_empty();
    // HS `Sapic.checkWellformedness` (Warnings.hs) is part of `preReport`, which
    // is PREPENDED to the rest of the report (as in `run_batch`).  A hard
    // translation error still propagates as `LoadError::Elaborate`.
    let sapic_wf =
        tamarin_sapic::apply::apply_sapic(&mut parser_theory, &mut typed, user_set_heuristic)
            .map_err(|e| LoadError::Elaborate(e.message))?;
    // Accountability translation (HS `Sapic.translate >=> Acc.translate`,
    // `processOpenTheory`, TheoryLoader.hs:470-484, see line 472): expands each
    // `… accounts for` lemma into its
    // verification-condition lemmas + case-test predicates, injecting into
    // BOTH `parser_theory` (web renderers) and `typed` (lemma list, proof
    // state).  Without this the web UI has no pages for the VC sub-lemmas
    // batch `--prove` proves.  No-op for theories without accountability
    // lemmas / case tests.
    tamarin_accountability::translate(&mut parser_theory, &mut typed)
        .map_err(|e| LoadError::Elaborate(e.to_string()))?;
    // `preReport` order (as in `run_batch`): SAPIC warnings, then the
    // accountability RP check, then the rest.
    let mut pre_report = sapic_wf;
    pre_report.extend(acc_wf);
    tamarin_theory::translated_wf::prepend_wf_report(&mut wf_report, pre_report);

    // HS re-runs the full `checkWellformedness` on the TRANSLATED theory
    // (`checkTranslatedTheory`), i.e. after `apply_sapic` / `Acc::translate`
    // injected the generated rules and lemmas.  The six re-runs and their
    // splice positions are shared with the batch path (`run_batch`) — see
    // `tamarin_theory::translated_wf`.
    tamarin_theory::translated_wf::splice_translated_wf_reports(
        &parser_theory,
        &typed,
        &maude_sig,
        &mut wf_report,
    );

    // The theory's once-per-load NDC-checked intruder cache
    // (`check_close_intr_rule` below).  Stored on the `TheoryEntry` so
    // `ProofState::new` injects it into the web session / shared context
    // instead of re-running the check per context build.
    let mut ndc_cache: Option<Arc<Vec<tamarin_theory::rule::IntrRuleAC>>> = None;
    // The signature every Maude process for this theory loads its module
    // from, taken before the NDC join below — see
    // `TheoryEntry::prover_maude_sig` for why the join must not reach it.
    let prover_maude_sig = typed.signature.maude_sig.clone();
    if let Ok(maude) = MaudeHandle::start(maude_path, prover_maude_sig.clone()) {
        tamarin_theory::tools::rule_variants::populate_rule_variants(&mut typed, &maude, None);
        // Annotate per-rule loop breakers on the stored theory so the web
        // rules / source / message renderers emit HS's `// loop breaker: [<n>]`
        // comments — HS `prettyClosedProtoRule` reads them from the
        // `ProtoRuleACInfo` baked into every closed rule.  Our prover computes
        // them inside `ProofContext::new` on a local copy; run the same
        // whole-theory pass `run.rs` runs on the CLI side so the
        // byte-faithful `web_proto_rules` printer has them.
        tamarin_theory::constraint::solver::context::annotate_theory_loop_breakers(
            &mut typed, &maude,
        );

        // Once-per-theory NDC pass (HS `checkCloseIntrRule` inside
        // `checkTranslatedTheory`, TheoryLoader.hs — BEFORE the
        // derivation checks; `deduction_chain_check` holds the
        // `--no-ndc`-derived switch this load wrote above).  Emits the
        // `[Theory X] No Deconstruction Chain checks started/ended`
        // markers plus the per-function verdict lines, and joins the
        // verdicts into the stored theory's signature so every web
        // rendering of the `functions:` header shows `[NDC]`.
        let checked = tamarin_theory::close_rule::check_close_intr_rule(
            &maude,
            Some(&typed.name),
            typed.options.deduction_chain_check,
        );
        if !checked.ndc_funs.is_empty() {
            let mut sig = std::mem::take(&mut typed.signature.maude_sig);
            for f in &checked.ndc_funs {
                sig = sig.join_ndc_in_sig(*f, tamarin_term::function_symbols::NdcState::IsNdc);
            }
            typed.signature.maude_sig = sig;
        }
        ndc_cache = Some(Arc::new(checked.cache));

        // Dynamic Message Derivation Checks (as in `run_batch`): HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout` (HS
        // interactive default 5s).  The budget comes from ServerConfig
        // (CLI flag on the interactive path, 5s default otherwise) —
        // matching HS interactive, whose flag set ends in `theoryLoadFlags`
        // (Main/Mode/Interactive.hs:70), so the shared
        // `--derivcheck-timeout` (TheoryLoader.hs:180-185, read at
        // TheoryLoader.hs:391-393) applies.  Needs the Maude handle; runs on
        // the POST-translation parser theory (`parser_theory`, matching
        // run.rs's `&parsed` at that point).
        // HS brackets the check with stderr markers via `traceM`
        // (TheoryLoader.hs:578-594, see line 581,594) — emitted for every close (initial
        // load, upload, reload), and only when derivChecks != 0
        // (TheoryLoader.hs:578-579 skips the whole block on EQ).
        if derivcheck_timeout > 0 {
            eprintln!("[Theory {}] Derivation checks started", typed.name);
        }
        let extra = tamarin_theory::deriv_check::check_message_derivation(
            &parser_theory,
            &maude,
            derivcheck_timeout,
            ndc_cache
                .clone()
                .map(tamarin_theory::constraint::solver::context::IntrRuleCache::from),
        );
        wf_report.extend(extra);
        if derivcheck_timeout > 0 {
            eprintln!("[Theory {}] Derivation checks ended", typed.name);
        }
    }

    // HS `makeWfErrorsHtml` (src/Web/Handler.hs:469-475) — the header-banner
    // rendering of the same report; empty string when the report is empty.
    let errors_html = make_wf_errors_html(&wf_report);

    // "Theory closed" at the end of `closeTheory` (TheoryLoader.hs:696).
    eprintln!("[Theory {}] Theory closed", typed.name);

    Ok(TheoryEntry {
        idx: 0,
        name: typed.name.clone(),
        parser_theory: Arc::new(parser_theory),
        typed_theory: Arc::new(typed),
        prover_maude_sig,
        origin,
        loaded_at: Local::now(),
        primary: true,
        wf_report,
        errors_html,
        ndc_cache,
        proof_state: None,
    })
}

/// Build the HS `makeWfErrorsHtml` banner (`src/Web/Handler.hs:469-475`): wrap
/// the wellformedness report in a `<div class="wf-warning">`, prefixed by the
/// literal `WARNING: ...<br /><br />` line and followed by the report body
/// rendered exactly as HS's `renderHtmlDoc (htmlDoc $ prettyWfErrorReport
/// report)` — each source line's leading spaces turned into `&nbsp;` and a
/// `<br/>` appended, with NO entity escaping (HS `postprocessHtmlDoc`,
/// Text/PrettyPrint/Html.hs:157-162; see the body comment for why the
/// escaping `Document` instance never runs).  Empty report ⇒ empty string
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
    // HS `renderHtmlDoc = postprocessHtmlDoc . render . getHtmlDoc`
    // (Html.hs:151-153) — the body is NOT entity-escaped: `htmlDoc = HtmlDoc`
    // (Html.hs:96-97) only wraps an ALREADY BUILT plain `Doc`, so the escaping
    // `Document (HtmlDoc d)` instance (Html.hs:102-105) never runs over
    // `prettyWfErrorReport`'s text.  Only `postprocessHtmlDoc = unlines . map
    // (addBreak . indent) . lines` (Html.hs:157-162) applies: each line's
    // leading spaces become `&nbsp;` runs, `<br/>` is appended, and lines
    // rejoin with `\n` (trailing `\n`).  A body carrying `<`/`>` — a pair term
    // in a `Fr` fact or in the `multRestrictedReport` rule dump — therefore
    // reaches the browser raw, exactly as in HS.
    let rendered = tamarin_theory::pretty_hpj::postprocess_html(body);
    // HS `makeWfErrorsHtml`: <div> + literal WARNING line + rendered body + </div>.
    format!(
        "<div class=\"wf-warning\">\n\
         WARNING: the following wellformedness checks failed!<br /><br />\n\
         {rendered}\n</div>",
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The interactive `TheoryLoadOptions` plumbing added for HS parity:
    /// `-D` defines reach `#ifdef` evaluation via [`set_parser_flags`]
    /// (HS `toParserFlags`, TheoryLoader.hs:285-291), and a local file's
    /// `#include` resolves against ITS OWN directory
    /// (`takeDirectory <$> inFile`, Theory/Text/Parser.hs:306-343).  One
    /// test on purpose: `PARSER_FLAGS` is process-global, so the
    /// set/observe/reset sequence must not interleave with itself.
    /// `maude_path` is a nonexistent binary so the best-effort Maude block
    /// is skipped and the test stays hermetic.
    #[test]
    fn parser_flags_and_include_base_dir_reach_the_web_load() {
        let rule_count = |entry: &TheoryEntry| {
            entry
                .parser_theory
                .items
                .iter()
                .filter(|i| matches!(i, tamarin_parser::ast::TheoryItem::Rule(_)))
                .count()
        };
        let src = "theory T begin\n#ifdef FOO\nrule R: [ ] --> [ ]\n#endif\nend";
        let load = |src: &str, origin: TheoryOrigin| {
            load_from_source(src, origin, "/nonexistent/maude-for-test", 0)
                .expect("tiny theory loads")
        };

        // Flag absent: the #ifdef block is dropped.
        let entry = load(src, TheoryOrigin::Upload("t.spthy".into()));
        assert_eq!(rule_count(&entry), 0);
        // Flag set: the block parses, exactly as batch `-D=FOO`.
        set_parser_flags(vec!["FOO".to_string()]);
        let entry = load(src, TheoryOrigin::Upload("t.spthy".into()));
        set_parser_flags(Vec::new());
        assert_eq!(rule_count(&entry), 1);

        // #include next to the theory file resolves against that file's
        // directory (a Local origin), not the process CWD.
        let dir = std::env::temp_dir().join(format!("tamarin-rs-theory-io-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        std::fs::write(dir.join("inc.spthy"), "rule Inc: [ ] --> [ ]\n").expect("write include");
        let main = dir.join("main.spthy");
        std::fs::write(&main, "theory M begin\n#include \"inc.spthy\"\nend").expect("write main");
        let entry = load_from_path(&main, "/nonexistent/maude-for-test", 0)
            .expect("include resolves against the theory's dir");
        assert_eq!(rule_count(&entry), 1);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
