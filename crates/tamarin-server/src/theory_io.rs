// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Load and close a `.spthy` file (HS `loadTheory` + `closeTheory`) into a
//! [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};

use tamarin_theory::wellformedness::WfError;

use crate::state::{TheoryEntry, TheoryOrigin};
use crate::theory_loader::{close_theory, load_theory};

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
    let closed = close_theory(&cfg.load, parsed, &source_name).map_err(LoadError::Close)?;
    closed.print_partial_evaluation_trace();
    Ok(TheoryEntry {
        idx: 0,
        typed_theory: closed.theory,
        prover_maude_sig: closed.maude.maude_sig(),
        cut: closed.cut,
        origin,
        loaded_at: Local::now(),
        primary: true,
        wf_report: closed.wf_report.into(),
        ndc_cache: closed.ndc_cache,
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
    use crate::ServerConfig;

    /// What a web load is given.
    enum Source {
        /// An upload of this text.
        Text(&'static str),
        /// A local file, workspace-relative.
        File(&'static str),
        /// A local file with its first `from` replaced by `to`.
        Edited(&'static str, &'static str, &'static str),
        /// Local files written side by side; the first is loaded.
        Files(&'static [(&'static str, &'static str)]),
    }

    /// One property of a loaded theory.
    enum Check {
        /// The protocol rules, by name.
        Rules(&'static [&'static str]),
        /// Whether the named lemma is present.
        Lemma(&'static str, bool),
        /// The `functions:` line of the signature, as the message page shows it.
        Functions(&'static str),
        /// A topic of the wellformedness report.
        WfTopic(&'static str),
    }

    struct Case {
        name: &'static str,
        source: Source,
        config: fn(&mut ServerConfig),
        /// The checks on the loaded theory, or text the load error contains.
        expect: Result<&'static [Check], &'static str>,
    }

    const PLAIN: fn(&mut ServerConfig) = |_| {};
    const IFDEF: &str = "theory T begin\n#ifdef FOO\nrule R: [ ] --> [ ]\n#endif\nend";
    const NO_VARIANTS: &str = "theory NoVariants\nbegin\nbuiltins: symmetric-encryption\n\
        rule NoVar:\n  [ In(~x), Fr(~x) ] --[ N(~x) ]-> [ ]\n\
        rule Ok:\n  [ Fr(~k), In(c) ] --[ O(~k) ]-> [ Out(sdec(c, ~k)) ]\nend\n";
    const RUNNING: &str =
        "tamarin-prover/examples/features/auto-sources/running-example/running.spthy";
    const NDC_XORR: &str = "crates/tamarin-server/tests/fixtures/ndc_xorr.spthy";

    /// The web load's own plumbing, which no batch gate sees: the interactive
    /// `TheoryLoadOptions` (`-D` defines, `--auto-sources`, `--no-ndc`,
    /// `--quit-on-warning`) reaching `loadTheory`/`closeTheory`, a configuration
    /// block read in interactive mode, `#include` resolved against the theory's
    /// own directory (`takeDirectory <$> inFile`, Theory/Text/Parser.hs), the
    /// "Rule has no variants" drop, and the loads HS refuses: no Maude to close
    /// with, unsupported products.
    const CASES: &[Case] = &[
        Case {
            name: "an #ifdef block without its define is dropped",
            source: Source::Text(IFDEF),
            config: PLAIN,
            expect: Ok(&[Check::Rules(&[])]),
        },
        Case {
            name: "-D reaches #ifdef",
            source: Source::Text(IFDEF),
            config: |cfg| cfg.load.defines.push("FOO".into()),
            expect: Ok(&[Check::Rules(&["R"])]),
        },
        Case {
            name: "#include resolves beside the theory file",
            source: Source::Files(&[
                ("main.spthy", "theory M begin\n#include \"inc.spthy\"\nend"),
                ("inc.spthy", "rule Inc: [ ] --> [ ]\n"),
            ]),
            config: PLAIN,
            expect: Ok(&[Check::Rules(&["Inc"])]),
        },
        Case {
            name: "no auto-sources lemma by default",
            source: Source::File(RUNNING),
            config: PLAIN,
            expect: Ok(&[Check::Lemma("AUTO_typing", false)]),
        },
        Case {
            name: "--auto-sources adds the sources lemma",
            source: Source::File(RUNNING),
            config: |cfg| cfg.load.auto_sources = true,
            expect: Ok(&[Check::Lemma("AUTO_typing", true)]),
        },
        Case {
            name: "a configuration block's --auto-sources applies in interactive mode",
            source: Source::Edited(RUNNING, "begin", "configuration: \"--auto-sources\"\nbegin"),
            config: PLAIN,
            expect: Ok(&[Check::Lemma("AUTO_typing", true)]),
        },
        Case {
            name: "the NDC pass tags xorr",
            source: Source::File(NDC_XORR),
            config: PLAIN,
            expect: Ok(&[Check::Functions(
                "functions: fst/1, pair/2, snd/1, zeroo/0, xorr/2 [AC,NDC]",
            )]),
        },
        Case {
            name: "--no-ndc skips the NDC pass",
            source: Source::File(NDC_XORR),
            config: |cfg| cfg.load.ndc_check = false,
            expect: Ok(&[Check::Functions(
                "functions: fst/1, pair/2, snd/1, zeroo/0, xorr/2 [AC]",
            )]),
        },
        Case {
            name: "a rule without variants is reported, then dropped",
            source: Source::Text(NO_VARIANTS),
            config: PLAIN,
            expect: Ok(&[
                Check::WfTopic("Rule has no variants"),
                Check::Rules(&["Ok"]),
            ]),
        },
        Case {
            name: "--quit-on-warning rejects a theory with warnings",
            source: Source::Text(NO_VARIANTS),
            config: |cfg| cfg.load.quit_on_warning = true,
            expect: Err("Rule has no variants"),
        },
        Case {
            name: "unsupported products are rejected",
            source: Source::File("tamarin-prover/examples/sp14/GDH.spthy"),
            config: PLAIN,
            expect: Err("Unsupported multiplication outside exponents"),
        },
        Case {
            name: "no Maude to close with (explicit variants)",
            source: Source::Text(include_str!(
                "../../tamarin-theory/tests/fixtures/manual_variants.spthy"
            )),
            config: |cfg| cfg.load.maude_path = "/nonexistent/maude-for-test".into(),
            expect: Err("failed to start maude"),
        },
        Case {
            name: "no Maude to close with",
            source: Source::Text("theory T begin\nrule R: [Fr(~k)] --[A(~k)]-> []\nend"),
            config: |cfg| cfg.load.maude_path = "/nonexistent/maude-for-test".into(),
            expect: Err("failed to start maude"),
        },
    ];

    fn load(case: &Case, maude: &str) -> Result<TheoryEntry, LoadError> {
        let mut cfg =
            ServerConfig::new("127.0.0.1:0".parse().unwrap(), PathBuf::new(), maude.into());
        cfg.load.derivation_checks = tamarin_theory::deriv_check::DerivCheckTimeout::Disabled;
        (case.config)(&mut cfg);
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        match &case.source {
            Source::Text(text) => {
                load_from_source(text, TheoryOrigin::Upload("t.spthy".into()), &cfg)
            }
            Source::File(path) => load_from_path(&root.join(path), &cfg),
            Source::Edited(path, from, to) => {
                let path = root.join(path);
                let text = std::fs::read_to_string(&path).expect("read the theory");
                load_from_source(&text.replacen(from, to, 1), TheoryOrigin::Local(path), &cfg)
            }
            Source::Files(files) => {
                let dir = tempfile::tempdir().expect("temp dir");
                for (name, text) in *files {
                    std::fs::write(dir.path().join(name), text).expect("write theory file");
                }
                load_from_path(&dir.path().join(files[0].0), &cfg)
            }
        }
    }

    fn check(entry: &TheoryEntry, check: &Check) -> Result<(), String> {
        let theory = &entry.typed_theory;
        match check {
            Check::Rules(want) => {
                let got: Vec<&str> = theory.rules().map(|rule| rule.name()).collect();
                (got == *want).then_some(()).ok_or(format!("rules {got:?}"))
            }
            Check::Lemma(name, want) => {
                let got = theory.lemmas().any(|lemma| lemma.name == *name);
                (got == *want)
                    .then_some(())
                    .ok_or(format!("lemma {name} present: {got}"))
            }
            Check::Functions(want) => {
                let block = tamarin_theory::pretty_theory::web_signature_block(&theory.signature);
                let got = block.lines().find(|l| l.starts_with("functions:"));
                (got == Some(want)).then_some(()).ok_or(format!("{got:?}"))
            }
            Check::WfTopic(topic) => {
                let topics: Vec<&str> = entry.wf_report.iter().map(|e| e.topic.as_str()).collect();
                topics
                    .contains(topic)
                    .then_some(())
                    .ok_or(format!("wf topics {topics:?}"))
            }
        }
    }

    #[test]
    fn web_loads_apply_their_options() {
        let Some(maude) = tamarin_test_support::require_maude_path() else {
            return;
        };
        // The process-wide setup `serve` applies: the web render width.
        crate::init_process_globals();
        let maude = maude.as_str();
        let failures: Vec<String> = std::thread::scope(|scope| {
            let runs: Vec<_> = CASES
                .iter()
                .map(|case| scope.spawn(move || (case, load(case, maude))))
                .collect();
            runs.into_iter()
                .filter_map(|run| {
                    let (case, result) = run.join().expect("load thread");
                    let problem = match (result, &case.expect) {
                        (Ok(entry), Ok(checks)) => checks
                            .iter()
                            .filter_map(|c| check(&entry, c).err())
                            .reduce(|a, b| format!("{a}; {b}")),
                        (Err(error), Err(want)) => (!error.to_string().contains(want))
                            .then(|| format!("error lacks {want:?}: {error}")),
                        (Ok(_), Err(want)) => {
                            Some(format!("loaded; expected an error with {want:?}"))
                        }
                        (Err(error), Ok(_)) => Some(format!("failed: {error}")),
                    };
                    problem.map(|p| format!("{}: {p}", case.name))
                })
                .collect()
        });
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }
}
