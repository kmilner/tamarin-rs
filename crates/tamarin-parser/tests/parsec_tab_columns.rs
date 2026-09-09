//! Source columns use eight-column tab stops, including semantic error spans.
use tamarin_parser::parse_theory;

fn assert_diff_location(source: &str, line: u32, column: u32) {
    let error = parse_theory(source, &[]).unwrap_err();
    assert_eq!(error.line_column(), (line, column));
    let start = source.find("diff(").unwrap();
    assert_eq!(error.span(), start..start + 4);
}

#[test]
fn tabs_advance_to_the_next_eight_column_stop() {
    for (indent, column) in [
        ("\t", 27),
        ("\t\t", 35),
        (" \t", 27),
        ("       \t", 27),
        ("        \t", 35),
    ] {
        let source =
            format!("theory T begin\nrule X:\n{indent}[ ] --[ ]-> [ Out(diff(a,b)) ]\nend\n");
        assert_diff_location(&source, 3, column);
    }
}

#[test]
fn tabs_expand_at_their_own_position_and_newlines_reset_columns() {
    assert_diff_location(
        "theory T begin\nrule X:\n[ ] --[ ]-> [ Out(diff(a,b)) ]\t\nend\n",
        3,
        19,
    );
    assert_diff_location(
        "theory T begin\nrule X:\n[ ]\t--[ ]->\t[ Out(diff(a,b)) ]\nend\n",
        3,
        23,
    );
    assert_diff_location("theory T begin\nfunctions: h/1\nrule X:\n\t[ ] --[ ]-> [ Out(h(a)) ]\nrule Y:\n\t[ ] --[ ]-> [ Out(diff(a,b)) ]\nend\n", 6, 27);
}
