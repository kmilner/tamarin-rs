// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

mod common;

/// Fatal reports use Main.Console.renderDoc (110/73), whereas ordinary
/// wellformedness comments use the default render (100/67). The expected
/// report is captured from pristine upstream a75fec7f; this long action list
/// distinguishes the two layouts even though both reject the same family.
#[test]
fn fatal_variant_report_uses_the_console_layout() {
    if !common::maude_available() {
        return;
    }
    let (code, stdout, stderr) = common::run_raw(
        "tamarin_unsupported_input",
        "long_manual_variant",
        include_str!("../../../tamarin-prover/examples/regression/trace/manual-variant-action-alignment.spthy"),
        &["-D=LATE_CONFLICT", "--derivcheck-timeout=0"],
    );
    assert_eq!(code, 1, "{stderr}");
    assert!(stderr.contains("Unsupported rule semantics - aborting before proof search."));
    let (_, report) = stdout.split_once("\n\n").expect("fatal error heading");
    assert_eq!(
        report,
        include_str!("fixtures/manual_variant_fatal_report.txt")
    );
}
