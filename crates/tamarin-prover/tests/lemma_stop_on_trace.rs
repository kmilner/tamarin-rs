//! PR #962: per-lemma choice overrides configuration, but not the CLI.
mod common;

#[test]
fn lemma_stop_on_trace_precedence_matches_oracle() {
    if !common::maude_available() {
        return;
    }
    let fixture = common::fixture("lemma_stop_on_trace.spthy");
    for (flags, selected_steps) in [
        (vec!["--prove"], 3),
        (vec!["--prove", "--stop-on-trace=NONE"], 4),
    ] {
        let (rc, stdout, stderr) = common::run_binary(&flags, &[&fixture]);
        assert_eq!(rc, 0, "{stderr}");
        assert!(
            stdout.contains(&format!(
                "selected (exists-trace): verified ({selected_steps} steps)"
            )),
            "{stdout}"
        );
        assert!(
            stdout.contains("fallback (exists-trace): verified (4 steps)"),
            "{stdout}"
        );
        assert!(stdout.contains("stop-on-trace=SEQDFS"));
    }
}
