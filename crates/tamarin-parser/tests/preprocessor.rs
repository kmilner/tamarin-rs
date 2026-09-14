use tamarin_parser::{ast::TheoryItem, parse_diff_theory, parse_theory};

fn rule_names(source: &str, diff: bool) -> Vec<String> {
    let parse = if diff {
        parse_diff_theory
    } else {
        parse_theory
    };
    parse(source, &[])
        .unwrap_or_else(|error| panic!("{source}: {error}"))
        .items
        .into_iter()
        .map(|item| match item {
            TheoryItem::Rule(mut rule) => std::mem::take(&mut rule.name),
            other => panic!("unexpected active item: {other:?}"),
        })
        .collect()
}

#[test]
fn nested_conditionals_select_only_live_items() {
    for diff in [false, true] {
        for outer in [false, true] {
            for inner in [false, true] {
                let source = format!(
                    "theory T begin
                    {}
                    {}
                    #ifdef OUTER
                      #ifdef INNER
                        rule BOTH: [] --> []
                      #else
                        rule OUTER_ONLY: [] --> []
                      #endif
                    #else
                      #ifdef INNER
                        rule INNER_ONLY: [] --> []
                      #else
                        rule NEITHER: [] --> []
                      #endif
                    #endif
                    rule AFTER: [] --> []
                    end",
                    if outer { "#define OUTER" } else { "" },
                    if inner { "#define INNER" } else { "" },
                );
                let expected = [
                    match (outer, inner) {
                        (true, true) => "BOTH",
                        (true, false) => "OUTER_ONLY",
                        (false, true) => "INNER_ONLY",
                        (false, false) => "NEITHER",
                    },
                    "AFTER",
                ];
                assert_eq!(rule_names(&source, diff), expected);
            }
        }
    }
}

#[test]
fn inactive_text_is_opaque_regardless_of_its_syntax() {
    // None of these lines is a conditional directive. No declaration, quote,
    // comment, bracket or include parser should ever inspect them.
    let bodies = [
        "export: \"escaped \\\" #ifdef\"",
        "rule R [process=(unfinished",
        "lemma L [heuristic=s",
        "unbalanced ( [ { < syntax",
        "end\ntheory Another begin end",
        "/* unterminated comment",
        "text{* unterminated formal comment",
        "\"unterminated string\\",
        "'unterminated public literal",
        "#include \"missing-file-that-must-not-be-opened\"",
        "#include \"unfinished\\ ",
        "#define MUST_NOT_LEAK",
        "#endifSuffix\n#ifdef_1\n#else1\n#endif.0",
        "nonsense #ifdef INLINE #else #endif",
    ];
    for diff in [false, true] {
        for body in bodies {
            for nested in [
                body.to_string(),
                format!("#ifdef INNER\n{body}\n#else\n{body}\n#endif"),
            ] {
                for (before, after, expected) in [
                    (
                        "#ifdef OFF",
                        "#else\nrule LIVE: [] --> []\n#endif",
                        vec!["LIVE", "AFTER"],
                    ),
                    (
                        "#define ON\n#ifdef ON\nrule LIVE: [] --> []\n#else",
                        "#endif",
                        vec!["LIVE", "AFTER"],
                    ),
                ] {
                    let source = format!(
                        "theory T begin\n{before}\n{nested}\n{after}\n#ifdef MUST_NOT_LEAK\nrule LEAK: [] --> []\n#endif\nrule AFTER: [] --> []\nend"
                    );
                    assert_eq!(rule_names(&source, diff), expected, "{source}");
                }
            }
        }
    }
}

#[test]
fn directive_lines_are_structural_even_in_inactive_quotes_and_comments() {
    for diff in [false, true] {
        for (open, close) in [("/*", "*/"), ("export e: \"", "\""), ("text{*", "*}")] {
            let source = format!(
                "theory T begin
#ifdef OFF
{open}
#ifdef INNER
#else
#endif
{close}
#else
rule LIVE: [] --> []
#endif
end"
            );
            assert_eq!(rule_names(&source, diff), ["LIVE"]);
        }
    }
}

#[test]
fn active_comments_and_item_contents_own_directive_like_lines() {
    for parse in [parse_theory, parse_diff_theory] {
        for (open, close) in [
            ("/*", "*/"),
            ("export e: \"", "\""),
            ("text{*", "*}"),
            ("tactic: t prio: regex \"", "\""),
        ] {
            for body in ["#endif", "#ifdef OFF\n#else\n#endif"] {
                // Exercise both top-level and active conditional-item parsing.
                for prefix in ["", "#ifdef ON\n"] {
                    let suffix = if prefix.is_empty() { "" } else { "#endif\n" };
                    let source = format!(
                        "theory T begin\n#define ON\n{prefix}{open}\n{body}\n{close}\n{suffix}#ifdef ON\nrule LIVE: [] --> []\n#endif\nend"
                    );
                    let theory =
                        parse(&source, &[]).unwrap_or_else(|error| panic!("{source}: {error}"));
                    assert!(theory
                        .items
                        .iter()
                        .any(|item| matches!(item, TheoryItem::Rule(rule) if rule.name == "LIVE")));
                }
            }
        }
    }
}

#[test]
fn ordinary_names_and_inline_directive_text_are_not_reserved() {
    for parse in [parse_theory, parse_diff_theory] {
        for name in ["ifdef", "else", "endif"] {
            let source =
                format!("theory T begin lemma L: \"All {name}:node. Seen() @ #{name}\" end");
            parse(&source, &[]).unwrap_or_else(|error| panic!("{source}: {error}"));
            let source = format!("theory T begin lemma L: \"T\" by solve(Seen() @ #{name}) end");
            parse(&source, &[]).unwrap_or_else(|error| panic!("{source}: {error}"));
        }
        parse("theory T begin export e: \"#ifdef #else #endif\" end", &[]).unwrap();
    }
}

#[test]
fn conditionals_must_occupy_physical_lines() {
    for parse in [parse_theory, parse_diff_theory] {
        for body in [
            "#ifdef X #endif",
            "/* comment */ #ifdef X\n#endif",
            "#ifdef X\n#else #define BAD\n#endif",
            "#ifdef X\n#endif end",
            "#ifdef (X\n| Y)\n#endif",
            "#ifdef X /* multiline\ncomment */\n#endif",
        ] {
            let source = format!("theory T begin\n{body}\nend");
            assert!(parse(&source, &[]).is_err(), "{source}");
        }
        assert!(parse("theory T begin #ifdef X\n#endif\nend", &[]).is_err());
        assert!(parse(
            "theory T begin\n#define X\n#ifdef X\nrule R: [] --> [] #else\n#endif\nend",
            &[]
        )
        .is_err());
    }
}

#[test]
fn directive_headers_allow_indentation_and_single_line_comments() {
    for diff in [false, true] {
        for newline in ["\n", "\r\n"] {
            let source = "theory T begin\n#define X\n\t\u{2003}#ifdef /* flag */ (X & not Y) // selected\nrule LIVE: [] --> []\n  #else /* unused */\ninvalid [ \"\n\t#endif // done\nend".replace('\n', newline);
            assert_eq!(rule_names(&source, diff), ["LIVE"]);
        }
    }
}

#[test]
fn malformed_conditional_structure_is_rejected_in_both_arms() {
    for parse in [parse_theory, parse_diff_theory] {
        for definition in ["", "#define X"] {
            for body in [
                "#ifdef X\n",
                "#ifdef X\n#else\n",
                "#ifdef X\n#else\n#else\n#endif",
                "#ifdef X\n#ifdef Y\n#else\n#else\n#endif\n#endif",
                "#ifdef X\n#else\n#ifdef Y\n#else\n#else\n#endif\n#endif",
                "#ifdef X\n#else\n#ifdef Y\n#endif",
                "#ifdef X\n#ifdef\n#endif\n#endif",
            ] {
                let source = format!("theory T begin\n{definition}\n{body}\nend");
                assert!(parse(&source, &[]).is_err(), "{source}");
            }
        }
        let source = "theory T begin\n#ifdef OFF\nunfinished";
        let error = parse(source, &[]).unwrap_err();
        assert_eq!(error.span().start, source.len());
        assert_eq!(
            error.diagnostic_notes(),
            ["expected \"#endif\"; found end of input"]
        );
        let source = "theory T begin\n\t#ifdef X |\n#endif\nend";
        let error = parse(source, &[]).unwrap_err();
        assert_eq!(error.span().start, source.find('|').unwrap() + 1);
        assert_eq!(error.line_column(), (2, 19));
    }
}

#[test]
fn includes_share_flags_and_parse_comments_normally() {
    use tamarin_parser::parse_theory_with_base;
    let dir =
        std::env::temp_dir().join(format!("tamarin-conditional-lines-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let child = dir.join("flags.inc");
    std::fs::write(&child, "#ifdef PARENT\n#define CHILD\n#endif").unwrap();
    let source = "theory T begin\n#define PARENT\n#include \"flags.inc\"\n#ifdef CHILD\nrule LIVE: [] --> []\n#else\n#include \"missing\"\n#endif\nend";
    let parsed = parse_theory_with_base(source, &[], Some(dir.clone())).unwrap();
    assert!(parsed
        .items
        .iter()
        .any(|item| matches!(item, TheoryItem::Rule(rule) if rule.name == "LIVE")));
    std::fs::write(&child, "/*\n#ifdef OFF\n#endif\n*/\n#define CHILD").unwrap();
    let parsed = parse_theory_with_base(source, &[], Some(dir.clone())).unwrap();
    assert!(parsed
        .items
        .iter()
        .any(|item| matches!(item, TheoryItem::Rule(rule) if rule.name == "LIVE")));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn arbitrary_non_directive_lines_cannot_affect_branch_selection() {
    // Prefix every generated line with text: its remaining bytes must have no
    // preprocessor meaning, regardless of lexical/declaration validity.
    let alphabet = b"#ifdef#else#endif\"'\\/*()[]{}:;= \n";
    let mut random = 1_u64;
    for _ in 0..128 {
        let mut body = String::from("opaque ");
        for _ in 0..256 {
            random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
            let c = alphabet[(random >> 32) as usize % alphabet.len()] as char;
            body.push(c);
            if c == '\n' {
                body.push_str("opaque ");
            }
        }
        for diff in [false, true] {
            let source = format!(
                "theory T begin\n#ifdef OFF\n{body}\n#else\nrule LIVE: [] --> []\n#endif\nend"
            );
            assert_eq!(rule_names(&source, diff), ["LIVE"]);
            let source = format!(
                "theory T begin\n#define ON\n#ifdef ON\nrule LIVE: [] --> []\n#else\n{body}\n#endif\nend"
            );
            assert_eq!(rule_names(&source, diff), ["LIVE"]);
        }
    }
}

#[test]
fn flag_evaluation_still_validates_both_operands() {
    for condition in ["ON | (OFF &)", "OFF & (ON |)"] {
        for outer in ["ON", "OFF"] {
            let source = format!(
                "theory T begin\n#define ON\n#ifdef {outer}\n#ifdef {condition}\n#endif\n#endif\nend"
            );
            assert!(parse_theory(&source, &[]).is_err(), "{source}");
        }
    }
}

#[test]
fn flat_flag_chains_do_not_build_recursive_trees() {
    let condition = "X & ".repeat(1_000_000) + "X";
    let source =
        format!("theory T begin\n#define X\n#ifdef {condition}\nrule LIVE: [] --> []\n#endif\nend");
    assert_eq!(rule_names(&source, false), ["LIVE"]);
}

#[test]
fn deeply_nested_conditionals_use_a_heap_stack() {
    let depth = 20_000;
    for opening in ["#ifdef ON\n", "#ifdef OFF\n#else\n"] {
        let source = format!(
            "theory T begin\n#define ON\n{}rule LIVE: [] --> []\n{}end",
            opening.repeat(depth),
            "#endif\n".repeat(depth)
        );
        for diff in [false, true] {
            assert_eq!(rule_names(&source, diff), ["LIVE"]);
        }
    }
    let source = format!(
        "theory T begin\n{}invalid text\n{}rule LIVE: [] --> []\nend",
        "#ifdef OFF\n".repeat(depth),
        "#endif\n".repeat(depth)
    );
    assert_eq!(rule_names(&source, false), ["LIVE"]);
}
