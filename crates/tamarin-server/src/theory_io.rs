// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Load and close a `.spthy` file (HS `loadTheory` + `closeTheory`) into a
//! [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tamarin_theory::wellformedness::WfError;

use crate::state::{TheoryEntry, TheoryOrigin};
use crate::theory_loader::{load_theory, TheoryPipeline};

#[derive(Debug)]
pub enum LoadError {
    Io(String),
    /// The complete plain-text parser diagnostic.
    Parse(String),
    /// A failure after parsing (HS `closeTheory`).
    Close(crate::theory_loader::LoadError),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io(s) => write!(f, "IO error: {}", s),
            LoadError::Parse(s) => f.write_str(s),
            LoadError::Close(error) => write!(f, "{error}"),
        }
    }
}
impl std::error::Error for LoadError {}

/// Read the file and load it with [`load_from_source`].
pub fn load_from_path(path: &Path, cfg: &crate::ServerConfig) -> Result<TheoryEntry, LoadError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| LoadError::Io(format!("{}: {}", path.display(), e)))?;
    load_from_source(&src, TheoryOrigin::Local(PathBuf::from(path)), cfg)
}

/// HS `loadTheory` + `closeTheory`, as the web's `loadThy`/`closeThy` run
/// them for every load, upload and reload. `entry.idx` is left as `0`;
/// [`crate::TheoryStore::insert`] assigns the real index.
pub(crate) fn load_from_source(
    src: &str,
    origin: TheoryOrigin,
    cfg: &crate::ServerConfig,
) -> Result<TheoryEntry, LoadError> {
    let source_name = origin.label();
    // `#include` resolves against the theory file's directory; an upload has
    // none (HS `takeDirectory` of a bare name is "."), so it resolves
    // CWD-relative.
    let base_dir = match &origin {
        TheoryOrigin::Local(p) => p.parent().map(|d| d.to_path_buf()),
        _ => None,
    };
    let parsed = load_theory(&cfg.load, src, base_dir)
        .map_err(|e| LoadError::Parse(e.render_plain_with_source(&source_name, src)))?;
    let mut pipeline =
        TheoryPipeline::new(&cfg.load, parsed, &source_name, None).map_err(LoadError::Close)?;
    pipeline.translate_theory().map_err(LoadError::Close)?;
    pipeline
        .check_translated_theory()
        .map_err(LoadError::Close)?;
    let pe_trace = pipeline
        .close_translated_theory()
        .map_err(LoadError::Close)?;
    pipeline.closed_marker(&pe_trace);

    let crate::theory_loader::LoadedTheory::Closed(typed_theory) = pipeline.theory else {
        unreachable!("close mode closes the theory")
    };
    Ok(TheoryEntry {
        idx: 0,
        typed_theory,
        prover_maude_sig: Arc::new(pipeline.maude_sig),
        cut: pipeline.cut,
        origin,
        loaded_at: Local::now(),
        primary: true,
        wf_report: pipeline.wf_report.into(),
        ndc_cache: pipeline.ndc_cache,
        proof_state: None,
    })
}

/// HS `renderHtmlDoc (htmlDoc $ prettyWfErrorReport report)`: the report
/// text with leading spaces as `&nbsp;` and `<br/>` line ends
/// (`postprocessHtmlDoc`, Html.hs), and no entity escaping.
pub(crate) fn wf_report_html(report: &[WfError]) -> String {
    let body = tamarin_theory::pretty_theory::render_wf_error_report(report);
    tamarin_theory::pretty_hpj::postprocess_html(body.trim_end_matches('\n'))
}

/// HS `makeWfErrorsHtml` (src/Web/Handler.hs): the report in a
/// `<div class="wf-warning">` under a literal WARNING line; empty for an
/// empty report.  HS stores this as `errorsHtml`; the help page renders it
/// from the entry's report instead.
pub fn make_wf_errors_html(report: &[WfError]) -> String {
    if report.is_empty() {
        return String::new();
    }
    format!(
        "<div class=\"wf-warning\">\n\
         WARNING: the following wellformedness checks failed!<br /><br />\n\
         {}\n</div>",
        wf_report_html(report)
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
        cfg.load.derivation_checks = tamarin_theory::deriv_check::DerivCheckTimeout::Disabled;
        cfg
    }

    /// Interactive `TheoryLoadOptions` carries parser flags and include paths:
    /// `-D` defines reach `#ifdef` evaluation through the load configuration
    /// (HS `toParserFlags`, TheoryLoader.hs), and a local file's
    /// `#include` resolves against ITS OWN directory
    /// (`takeDirectory <$> inFile`, Theory/Text/Parser.hs).
    #[test]
    fn parser_flags_and_include_base_dir_reach_the_web_load() {
        let Some(maude) = require_maude_path() else {
            return;
        };
        let rule_count = |entry: &TheoryEntry| {
            entry
                .typed_theory
                .items
                .iter()
                .filter(|i| matches!(i, tamarin_theory::theory::TheoryItem::Rule(_)))
                .count()
        };
        let src = "theory T begin\n#ifdef FOO\nrule R: [ ] --> [ ]\n#endif\nend";
        let mut cfg = test_config(&maude);

        // Flag absent: the #ifdef block is dropped.
        let entry = load_from_source(src, TheoryOrigin::Upload("t.spthy".into()), &cfg)
            .expect("tiny theory loads");
        assert_eq!(rule_count(&entry), 0);
        // Flag set: the block parses, exactly as batch `-D=FOO`.
        cfg.load.defines.push("FOO".to_string());
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

    /// HS closes every web load with Maude, so a load that cannot start it
    /// fails instead of storing a theory no proof session can use.
    #[test]
    fn web_load_fails_when_maude_cannot_start() {
        let explicit = include_str!("../../tamarin-theory/tests/fixtures/manual_variants.spthy");
        let plain = "theory T begin\nrule R: [Fr(~k)] --[A(~k)]-> []\nend";
        let cfg = test_config("/nonexistent/maude-for-test");
        for source in [explicit, plain] {
            let error =
                match load_from_source(source, TheoryOrigin::Upload("no-maude.spthy".into()), &cfg)
                {
                    Ok(_) => panic!("a load without Maude must fail"),
                    Err(error) => error,
                };
            assert!(
                error.to_string().contains("failed to start maude"),
                "{error}"
            );
        }
    }

    /// HS `withWebUI` runs `closeTheory thyLoadOptions` for every web load,
    /// so `--partial-evaluation` refines the stored rules and
    /// `--quit-on-warning` rejects a theory with warnings.
    #[test]
    fn web_load_applies_partial_evaluation_and_quit_on_warning() {
        let Some(maude) = require_maude_path() else {
            return;
        };
        let src = include_str!("../../../tamarin-prover/examples/loops/Minimal_Loop_Example.spthy");
        let mut cfg = test_config(&maude);
        cfg.load.partial_evaluation = Some(tamarin_theory::tools::EvaluationStyle::Summary);
        let entry = load_from_source(src, TheoryOrigin::Upload("loop.spthy".into()), &cfg)
            .expect("theory loads");
        assert!(entry.typed_theory.items.iter().any(|item| matches!(
            item,
            tamarin_theory::theory::TheoryItem::Text((_, text))
                if text.contains("abstract state after partial evaluation")
        )));

        let mut cfg = test_config(&maude);
        cfg.load.quit_on_warning = true;
        let warns = "theory W begin\nbuiltins: symmetric-encryption\n\
                     rule NoVar:\n  [ In(~x), Fr(~x) ] --[ N(~x) ]-> [ ]\nend\n";
        match load_from_source(warns, TheoryOrigin::Upload("w.spthy".into()), &cfg) {
            Err(LoadError::Close(crate::theory_loader::LoadError::Warning(report))) => {
                assert!(report.iter().any(|w| w.topic == "Rule has no variants"));
            }
            Err(other) => panic!("expected a quit-on-warning rejection, got {other}"),
            Ok(_) => panic!("expected a quit-on-warning rejection"),
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
