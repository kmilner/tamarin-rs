use super::*;
use tamarin_test_support::require_maude_path;

#[test]
fn auto_sources_reaches_interactive_loading_from_cli_and_configuration() {
    let Some(maude) = require_maude_path() else {
        return;
    };
    let source = include_str!(
        "../../../tamarin-prover/examples/features/auto-sources/running-example/running.spthy"
    );
    let mut cfg = crate::ServerConfig::new("127.0.0.1:0".parse().unwrap(), PathBuf::new(), maude);
    cfg.derivcheck_timeout = 0;
    for (cli, block) in [(false, false), (true, false), (false, true), (true, true)] {
        cfg.auto_sources = cli;
        let source = if block {
            source.replacen("begin", "configuration: \"--auto-sources\"\nbegin", 1)
        } else {
            source.to_owned()
        };
        let entry = load_from_source(
            &source,
            TheoryOrigin::Local(PathBuf::from("running.spthy")),
            &cfg,
        )
        .unwrap();
        assert_eq!(
            entry
                .typed_theory
                .lemmas()
                .filter(|lemma| lemma.name == "AUTO_typing")
                .count(),
            usize::from(cli || block)
        );
    }
}

#[test]
fn auto_sources_reports_unavailable_maude() {
    let mut cfg = crate::ServerConfig::new(
        "127.0.0.1:0".parse().unwrap(),
        PathBuf::new(),
        "/nonexistent/maude".into(),
    );
    cfg.auto_sources = true;
    let result = load_from_source(
        "theory T begin end",
        TheoryOrigin::Local(PathBuf::from("t.spthy")),
        &cfg,
    );
    assert!(
        matches!(result, Err(LoadError::Elaborate(message)) if message.contains("auto-sources requires Maude"))
    );
}
