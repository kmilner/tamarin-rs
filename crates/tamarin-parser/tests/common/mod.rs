#[track_caller]
pub fn assert_span(error: &tamarin_parser::ParseError, source: &str, expected: &str) {
    let labels = error.diagnostic_labels_with_source(source);
    assert_eq!(&source[labels[0].span.clone()], expected);
}
