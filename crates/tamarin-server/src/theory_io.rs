// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Parse + elaborate a `.spthy` file into a [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tamarin_parser::parse_theory_with_base;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::elaborate::elaborate_with_in_file;
use tamarin_theory::wellformedness::WfError;

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
            // `Parse` already holds the complete plain-text diagnostic, so it
            // is emitted verbatim without adding another prefix. This is what
            // lands inside the eager-load block and the web upload failure
            // banner.
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
pub fn load_from_path(path: &Path, cfg: &crate::ServerConfig) -> Result<TheoryEntry, LoadError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| LoadError::Io(format!("{}: {}", path.display(), e)))?;
    load_from_source(&src, TheoryOrigin::Local(PathBuf::from(path)), cfg)
}

/// Parse + elaborate from a string (for the upload path), then "close"
/// the theory by pre-computing each protocol rule's AC-variants via
/// Maude (HS `closeTheory`), so the source / rules / overview renderers
/// can emit the `variants (modulo AC)` blocks byte-for-byte.  Variant
/// computation is best-effort: if Maude can't be started the theory is
/// still usable (rules just render without their variants block), unless
/// auto-sources or explicit rule variants require Maude-backed validation.
pub(crate) fn load_from_source(
    src: &str,
    origin: TheoryOrigin,
    cfg: &crate::ServerConfig,
) -> Result<TheoryEntry, LoadError> {
    // Attach the local path or uploaded filename to the structured diagnostic.
    // Errors originating in an included file already carry that file's path
    // and source text, which `with_source` deliberately leaves unchanged.
    let source_name = origin.label();
    // Parser flags (`-D` defines + the `quit-on-warning` element) come from
    // the server configuration. `#include` paths resolve against the theory
    // file's own directory — HS threads `Just inFile`
    // into the `theory` parser (`loadTheory`, TheoryLoader.hs) and
    // `include` resolves against `takeDirectory <$> inFile0`
    // (Theory/Text/Parser.hs).  An upload has no on-disk home
    // (HS's bare filename gives `takeDirectory = "."`), so it resolves
    // CWD-relative, the no-base default.
    let flags: Vec<&str> = cfg.parser_flags.iter().map(String::as_str).collect();
    let base_dir = match &origin {
        TheoryOrigin::Local(p) => p.parent().map(|d| d.to_path_buf()),
        _ => None,
    };
    let parsed = parse_theory_with_base(src, &flags, base_dir)
        .map_err(|e| LoadError::Parse(e.render_plain_with_source(&source_name, src)))?;

    // HS lifecycle markers, stderr via `traceM`: "Theory loaded" right
    // after parsing (TheoryLoader.hs).
    eprintln!("[Theory {}] Theory loaded", parsed.name);

    // "Theory translated" at the START of translation (TheoryLoader.hs
    // prints before `processOpenTheory` runs); RS's `elaborate` is that
    // translation step.
    eprintln!("[Theory {}] Theory translated", parsed.name);
    // Oracle path resolution base: HS threads the parser's `inFile` into
    // `defaultOracleNames` (Theory/Text/Parser.hs), so a
    // `heuristic: o "./oracle-…"` resolves against the theory's own
    // directory (`hs_take_directory`).  Local files carry their on-disk
    // path; uploads keep the bare filename (dir "." — as in HS, where an
    // uploaded theory has no on-disk home).
    let mut typed = elaborate_with_in_file(&parsed, &origin.label())
        .map_err(|e| LoadError::Elaborate(e.message))?;

    let config_block = parsed
        .configuration
        .as_deref()
        .map(tamarin_theory::prove::parse_config_block)
        .unwrap_or_default();
    if let Some(message) = config_block.flag_error {
        return Err(LoadError::Elaborate(format!(
            "configuration block: {message}"
        )));
    }
    let auto_sources = cfg.auto_sources || config_block.auto_sources;

    // Everything downstream of `elaborate` reads the internal theory; the
    // parser AST ends here.
    drop(parsed);
    // HS `addParamsOptions`' `addNdcOption` (TheoryLoader.hs), the last
    // step of `loadTheory` (TheoryLoader.hs): the CLI's `ndcCheck`
    // becomes the loaded theory's `_deductionChainCheck`, which the NDC pass in
    // the maude block below reads back.
    typed.options.deduction_chain_check = cfg.ndc_check;
    // The `addLemmaToProve` sibling of that same `addParamsOptions`
    // (TheoryLoader.hs): the CLI's `--prove`/`--lemma` selection
    // becomes the loaded theory's `_lemmasToProve`.
    typed.options.lemmas_to_prove = cfg.lemmas_to_prove.clone();

    // SAPIC `process:` translation — mirror `run_batch`'s CLI-side pass so
    // the web load path renders SAPIC theories exactly like `--prove`.  Runs
    // ONLY for theories with exactly one top-level `process:`;
    // `apply_sapic` returns `Ok(vec![])` otherwise, so it is safe to call
    // unconditionally and leaves
    // non-process theories byte-unchanged.  It injects the generated MSR
    // rules + `single_session` restriction + `heuristic: p` into `typed`,
    // which the web renderers and the AC-variant pre-computation read, so it
    // MUST run before `populate_rule_variants` below.  `user_set_heuristic`
    // is true iff a `heuristic:` item already populated `typed.heuristic` (HS
    // `addHeuristic` returns `Nothing` in that case).
    // HS `Acc.checkWellformedness t` (translateTheory, TheoryLoader.hs)
    // runs on the PRE-translation theory — before `apply_sapic` injects the
    // SAPIC-generated rules (mirrors run.rs's CLI-side placement).
    let acc_wf = tamarin_accountability::check_wellformedness(&typed);
    let user_set_heuristic = !typed.heuristic.is_empty();
    // HS `Sapic.checkWellformedness` (Warnings.hs) is the head of `preReport`
    // (as in `run_batch`).  A hard translation error still propagates as
    // `LoadError::Elaborate`.
    let sapic_wf = tamarin_sapic::apply::apply_sapic(&mut typed, user_set_heuristic)
        .map_err(|e| LoadError::Elaborate(e.message))?;
    // Accountability translation (HS `Sapic.translate >=> Acc.translate`,
    // `processOpenTheory`, TheoryLoader.hs): expands each
    // `… accounts for` lemma into its
    // verification-condition lemmas + case-test predicates, appending them to
    // `typed`, which carries the lemma list, the proof state and everything
    // the web renderers read.  Without this the web UI has no pages for the
    // VC sub-lemmas batch `--prove` proves.  No-op for theories without
    // accountability lemmas / case tests.
    tamarin_accountability::translate(&mut typed)
        .map_err(|e| LoadError::Elaborate(e.to_string()))?;
    // HS `preReport ++ postReport` (TheoryLoader.hs), as in
    // `run_batch`: SAPIC warnings, then the accountability RP check, then the
    // whole `checkWellformedness` pass over the TRANSLATED theory. The latter
    // runs below after variant computation so `ruleVariantsReport` sees its
    // live Maude result, and before zero-variant rules are removed.
    //
    // The result feeds two renderings: the `/* WARNING: ... */` comment in the
    // source/message routes (`format_wf_block`) and the
    // `<div class="wf-warning">` header banner in help/overview
    // (`errors_html`).
    let mut wf_report = sapic_wf;
    wf_report.extend(acc_wf);

    // The theory's once-per-load NDC-checked intruder cache
    // (`check_close_intr_rule` below).  Stored on the `TheoryEntry` so
    // `ProofState::new` injects it into the web session / shared context
    // instead of re-running the check per context build.
    let mut ndc_cache: Option<tamarin_theory::constraint::solver::context::IntrRuleCache> = None;
    // The signature every Maude process for this theory loads its module
    // from, taken before the NDC join below — see
    // `TheoryEntry::prover_maude_sig` for why the join must not reach it.
    let prover_maude_sig = typed.signature.clone();
    let started_maude = MaudeHandle::start(&cfg.maude_path, prover_maude_sig.clone());
    if auto_sources {
        started_maude.as_ref().map_err(|error| {
            LoadError::Elaborate(format!("auto-sources requires Maude: {error}"))
        })?;
    }
    if let Ok(maude) = started_maude {
        wf_report.extend(
            tamarin_theory::tools::rule_variants::prepare_theory_rules(
                &mut typed, &maude, None, true,
            )
            .map_err(|error| LoadError::Elaborate(error.to_string()))?,
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
            &typed.intruder_rules,
            cfg.solver_parameters,
        )
        .map_err(|error| LoadError::Elaborate(error.to_string()))?;
        if !checked.ndc_funs.is_empty() {
            let mut sig = std::mem::take(&mut typed.signature);
            for f in &checked.ndc_funs {
                sig = sig.join_ndc_in_sig(*f, tamarin_term::function_symbols::NdcState::IsNdc);
            }
            typed.signature = sig;
        }
        ndc_cache = Some(checked.cache.into());

        // Dynamic Message Derivation Checks (as in `run_batch`): HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout` (HS
        // interactive default 5s).  The budget comes from ServerConfig
        // (CLI flag on the interactive path, 5s default otherwise) —
        // matching HS interactive, whose flag set ends in `theoryLoadFlags`
        // (Main/Mode/Interactive.hs), so the shared
        // `--derivcheck-timeout` (TheoryLoader.hs, read at
        // TheoryLoader.hs) applies.  Needs the Maude handle; runs on
        // the POST-translation theory (`typed`, matching run.rs's
        // `&self.elaborated` at that point).
        // HS brackets the check with stderr markers via `traceM`
        // (TheoryLoader.hs) — emitted for every close (initial
        // load, upload, reload), and only when derivChecks != 0
        // (TheoryLoader.hs skips the whole block on EQ).
        if cfg.derivcheck_timeout > 0 {
            eprintln!("[Theory {}] Derivation checks started", typed.name);
        }
        let extra = tamarin_theory::deriv_check::check_message_derivation(
            &typed,
            &maude,
            cfg.derivcheck_timeout,
            ndc_cache.clone(),
            cfg.solver_parameters,
        )
        .map_err(|error| LoadError::Elaborate(error.to_string()))?;
        wf_report.extend(extra);
        if cfg.derivcheck_timeout > 0 {
            eprintln!("[Theory {}] Derivation checks ended", typed.name);
        }
        if auto_sources {
            tamarin_theory::auto_sources::apply_auto_sources(
                &mut typed,
                maude,
                None,
                ndc_cache.as_ref(),
                cfg.solver_parameters,
            )
            .map_err(|error| LoadError::Elaborate(error.to_string()))?;
        }
    } else {
        // Static checks remain available without Maude, but explicit families
        // require validation now: a recovered proof session must never inherit
        // unchecked variants from this load.
        wf_report.extend(
            tamarin_theory::wellformedness::check_wellformedness(&typed, None)
                .map_err(|error| LoadError::Elaborate(error.to_string()))?,
        );
        // Best-effort loading may skip Maude, but cannot turn a known unsafe
        // rule into a usable theory. Match prepare_theory_rules' fatal policy.
        let fatal = tamarin_theory::wellformedness::variants::fatal_wf_errors(&wf_report);
        if !fatal.is_empty() {
            return Err(LoadError::Elaborate(
                tamarin_theory::tools::rule_variants::VariantsError::UnsupportedInput(fatal)
                    .to_string(),
            ));
        }
    }

    // HS `makeWfErrorsHtml` (src/Web/Handler.hs) — the header-banner
    // rendering of the same report; empty string when the report is empty.
    let errors_html = make_wf_errors_html(&wf_report);

    // "Theory closed" at the end of `closeTheory` (TheoryLoader.hs).
    eprintln!("[Theory {}] Theory closed", typed.name);

    Ok(TheoryEntry {
        idx: 0,
        typed_theory: Arc::new(typed),
        prover_maude_sig: Arc::new(prover_maude_sig),
        origin,
        loaded_at: Local::now(),
        primary: true,
        wf_report: wf_report.into(),
        errors_html: errors_html.into(),
        ndc_cache,
        proof_state: None,
    })
}

/// Build the HS `makeWfErrorsHtml` banner (`src/Web/Handler.hs`): wrap
/// the wellformedness report in a `<div class="wf-warning">`, prefixed by the
/// literal `WARNING: ...<br /><br />` line and followed by the report body
/// rendered exactly as HS's `renderHtmlDoc (htmlDoc $ prettyWfErrorReport
/// report)` — each source line's leading spaces turned into `&nbsp;` and a
/// `<br/>` appended, with NO entity escaping (HS `postprocessHtmlDoc`,
/// Text/PrettyPrint/Html.hs; see the body comment for why the
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
    // (Html.hs) — the body is NOT entity-escaped: `htmlDoc = HtmlDoc`
    // (Html.hs) only wraps an ALREADY BUILT plain `Doc`, so the escaping
    // `Document (HtmlDoc d)` instance (Html.hs) never runs over
    // `prettyWfErrorReport`'s text.  Only `postprocessHtmlDoc = unlines . map
    // (addBreak . indent) . lines` (Html.hs) applies: each line's
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
    use tamarin_test_support::require_maude_path;

    fn test_config(maude: &str) -> crate::ServerConfig {
        let mut cfg = crate::ServerConfig::new(
            "127.0.0.1:0".parse().unwrap(),
            PathBuf::new(),
            maude.to_string(),
        );
        cfg.derivcheck_timeout = 0;
        cfg
    }

    /// The interactive `TheoryLoadOptions` plumbing added for HS parity:
    /// `-D` defines reach `#ifdef` evaluation through the load configuration
    /// (HS `toParserFlags`, TheoryLoader.hs), and a local file's
    /// `#include` resolves against ITS OWN directory
    /// (`takeDirectory <$> inFile`, Theory/Text/Parser.hs).
    /// `maude_path` is a nonexistent binary so the best-effort Maude block
    /// is skipped and the test stays hermetic.
    #[test]
    fn parser_flags_and_include_base_dir_reach_the_web_load() {
        let rule_count = |entry: &TheoryEntry| {
            entry
                .typed_theory
                .items
                .iter()
                .filter(|i| matches!(i, tamarin_theory::theory::TheoryItem::Rule(_)))
                .count()
        };
        let src = "theory T begin\n#ifdef FOO\nrule R: [ ] --> [ ]\n#endif\nend";
        let mut cfg = test_config("/nonexistent/maude-for-test");

        // Flag absent: the #ifdef block is dropped.
        let entry = load_from_source(src, TheoryOrigin::Upload("t.spthy".into()), &cfg)
            .expect("tiny theory loads");
        assert_eq!(rule_count(&entry), 0);
        // Flag set: the block parses, exactly as batch `-D=FOO`.
        cfg.parser_flags.push("FOO".to_string());
        let entry = load_from_source(src, TheoryOrigin::Upload("t.spthy".into()), &cfg)
            .expect("tiny theory loads");
        assert_eq!(rule_count(&entry), 1);

        // #include next to the theory file resolves against that file's
        // directory (a Local origin), not the process CWD.
        let dir = std::env::temp_dir().join(format!("tamarin-rs-theory-io-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        std::fs::write(dir.join("inc.spthy"), "rule Inc: [ ] --> [ ]\n").expect("write include");
        let main = dir.join("main.spthy");
        std::fs::write(&main, "theory M begin\n#include \"inc.spthy\"\nend").expect("write main");
        let entry = load_from_path(&main, &cfg).expect("include resolves against the theory's dir");
        assert_eq!(rule_count(&entry), 1);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn web_load_does_not_store_unchecked_explicit_variants_without_maude() {
        let complete = include_str!("../../tamarin-theory/tests/fixtures/manual_variants.spthy");
        let incomplete = format!(
            "{}\nend",
            complete.split(",\n  rule (modulo AC)").next().unwrap()
        );
        let cfg = test_config("/nonexistent/maude-for-test");
        for source in [complete, &incomplete] {
            let error = match load_from_source(
                source,
                TheoryOrigin::Upload("manual-variants.spthy".into()),
                &cfg,
            ) {
                Ok(_) => panic!("unchecked family must not reach a later recovered proof session"),
                Err(error) => error,
            };
            assert!(
                error
                    .to_string()
                    .contains("Maude is required to validate explicit rule variants"),
                "{error}"
            );
        }
    }

    #[test]
    fn web_load_reports_then_drops_rules_without_variants() {
        let Some(maude) = require_maude_path() else {
            return;
        };
        let src = "theory NoVariants\n\
                   begin\n\
                   builtins: symmetric-encryption\n\
                   rule NoVar:\n  [ In(~x), Fr(~x) ] --[ N(~x) ]-> [ ]\n\
                   rule Ok:\n  [ Fr(~k), In(c) ] --[ O(~k) ]-> [ Out(sdec(c, ~k)) ]\n\
                   end\n";
        let entry = load_from_source(
            src,
            TheoryOrigin::Upload("no-variants.spthy".into()),
            &test_config(&maude),
        )
        .expect("theory loads");

        assert!(entry
            .wf_report
            .iter()
            .any(|warning| warning.topic == "Rule has no variants"));
        let names: Vec<&str> = entry.typed_theory.rules().map(|rule| rule.name()).collect();
        assert_eq!(names, vec!["Ok"]);
    }
}

#[cfg(test)]
#[path = "theory_io_auto_sources_tests.rs"]
mod auto_sources_tests;
