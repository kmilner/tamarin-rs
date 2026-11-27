// Currently GPL 3.0; see README.md for licensing details.

//! Tests of the corpus loader in `test_corpus_common.rs`.  They live in
//! their own lib-only module because the integration tests include that file
//! by path (`tests/corpus_util/mod.rs`), which would run them twice.

use crate::test_corpus_common::{
    corpus_root_or_skip, manifest_requests_diff, parse_file, parse_source,
};

#[test]
fn corpus_parser_takes_diff_mode_from_the_test_manifest() {
    let Some(root) = corpus_root_or_skip("manifest diff mode") else {
        return;
    };
    let path = root.join("regression/negative/diff-side-products.spthy");
    assert!(manifest_requests_diff(&path));
    assert!(parse_file(&path).expect("diff mode parses it").is_diff);

    // A manifest that also runs the file in trace mode keeps it there.
    let path = root.join("regression/trace/dh-products-in-exponents.spthy");
    assert!(!manifest_requests_diff(&path));
    assert!(!parse_file(&path).expect("trace mode parses it").is_diff);
}

/// Each file loads in the one mode that accepts it, whatever the evidence
/// suggested first; a file neither mode accepts does not load.
#[test]
fn corpus_parser_settles_on_the_mode_that_accepts_the_file() {
    let rows: &[(&str, Option<bool>)] = &[
        ("rule R: [ In(x) ] --> [ Out(diff(x, x)) ]", Some(true)),
        ("restriction r [left]: \"F\"", Some(true)),
        (
            "/* diff(x,y) */ // diff (x,y)\nrule diffuse: [ ] --> [ ]",
            Some(false),
        ),
        ("rule R: [ ] -->", None),
    ];
    for &(body, is_diff) in rows {
        let src = format!("theory D begin\n{body}\nend\n");
        let parsed = parse_source(&src, None, false).map(|t| t.is_diff);
        assert_eq!(parsed, is_diff, "{body}");
    }
}
