use tamarin_parser::{parse_theory, parse_theory_with_base};

#[test]
fn deep_syntax_parses_and_drops_without_a_depth_cap() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let n = 8192;
        let grouped = |text: &str| "(".repeat(n) + text + &")".repeat(n);
        for body in [
            format!("#ifdef {}\n#endif", grouped("X")),
            format!("lemma L: \"{}\"", grouped("T")),
            format!("lemma L: \"{}\"", grouped("x = x")),
            format!("lemma L: \"{} = x\"", grouped("x")),
            format!("lemma L: \"{}T\"", "T ==> ".repeat(n)),
            format!("lemma L: \"All {}. T\"", "x ".repeat(n)),
            format!(
                "functions: f/1 rule R: [] --> [Out({}x{})]",
                "f(".repeat(n),
                ")".repeat(n)
            ),
            format!("rule R: [] --> [Out(<{}x>)]", "x,".repeat(n)),
            format!("process: {}0", "!".repeat(n)),
            format!("process: {}0", "0 | ".repeat(n)),
            format!("lemma L: \"T\" {}by sorry", "simplify ".repeat(n)),
        ] {
            drop(parse_theory(&format!("theory T begin\n{body}\nend"), &[]).unwrap());
        }
    });
}

#[test]
fn includes_reject_cycles_but_allow_repeated_completed_files() {
    let dir = std::env::temp_dir().join(format!("tamarin-include-cycle-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    for (first, second) in [
        ("#include \"./sub/../a.inc\"", ""),
        ("#include \"b.inc\"", "#include \"a.inc\""),
    ] {
        std::fs::write(dir.join("a.inc"), first).unwrap();
        std::fs::write(dir.join("b.inc"), second).unwrap();
        let error = parse_theory_with_base(
            "theory T begin\n#include \"a.inc\"\nend",
            &[],
            Some(dir.clone()),
        )
        .unwrap_err();
        assert!(error.to_string().contains("`#include` cycle"), "{error}");
        assert!(error.source_text().is_some());
    }
    std::fs::write(
        dir.join("a.inc"),
        "#ifdef SEEN\nrule Second: [] --> []\n#else\n#define SEEN\nrule First: [] --> []\n#endif",
    )
    .unwrap();
    let theory = parse_theory_with_base(
        "theory T begin\n#include \"a.inc\"\n#include \"a.inc\"\nend",
        &[],
        Some(dir.clone()),
    )
    .unwrap();
    let names: Vec<_> = theory
        .items
        .iter()
        .filter_map(|item| match item {
            tamarin_parser::ast::TheoryItem::Rule(r) => Some(r.name.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(names, ["First", "Second"]);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn nested_rules_share_stack_safe_let_substitution_and_renaming() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let deep_term = "y * ".repeat(495) + "y";
        // Exercise replacement and body variable collection, then capture-
        // avoiding renaming through both term and formula trees. The rule
        // frames remain live while all of these helper traversals run.
        let mut bodies = vec![format!("let y = {deep_term} in [] --> [Out(y)]")];
        bodies.extend(
            [
                (deep_term.clone(), "Ex y. x = x".to_owned()),
                (
                    "y".to_owned(),
                    "Ex y. ".to_owned() + &"T & ".repeat(495) + "x = x",
                ),
                ("y".to_owned(), format!("Ex y. {deep_term} = x")),
                (
                    "y".to_owned(),
                    "Ex y. ".to_owned() + &"T & ".repeat(495) + "y = x",
                ),
            ]
            .into_iter()
            .map(|(value, formula)| format!("let x = {value} in [] --[_restrict({formula})]-> []")),
        );
        for body in bodies {
            let source = format!(
                "theory T begin builtins: diffie-hellman {}rule R: {body} {}end",
                "rule R: [] --> [] left ".repeat(255),
                "right rule R: [] --> [] ".repeat(255),
            );
            drop(parse_theory(&source, &[]).unwrap());
        }
    });
}
