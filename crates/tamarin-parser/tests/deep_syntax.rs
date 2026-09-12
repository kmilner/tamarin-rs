use tamarin_parser::{parse_theory, parse_theory_with_base};

#[test]
fn deep_syntax_parses_and_drops_without_a_depth_cap() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let n = 8192;
            let grouped = |text: &str| "(".repeat(n) + text + &")".repeat(n);
            for body in [
                format!("#ifdef {}\n#endif", grouped("X")),
                format!("lemma L: \"{}\"", grouped("T")),
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
        })
        .unwrap()
        .join()
        .unwrap();
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
        assert!(error.to_string().contains("circular include"), "{error}");
        assert!(error.source_text().is_some());
    }
    std::fs::write(dir.join("a.inc"), "").unwrap();
    parse_theory_with_base(
        "theory T begin\n#include \"a.inc\"\n#include \"a.inc\"\nend",
        &[],
        Some(dir.clone()),
    )
    .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn let_substitution_clones_safely_inside_nested_rules() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            // Exercise substitution cloning while nested outer rules remain live.
            let source = format!(
                "theory T begin builtins: diffie-hellman {}rule R: let y = {}x in [] --> [Out(y)] {}end",
                "rule R: [] --> [] left ".repeat(250),
                "x * ".repeat(500),
                "right rule R: [] --> [] ".repeat(250),
            );
            drop(parse_theory(&source, &[]).unwrap());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn quantified_let_substitution_grows_the_stack_for_collection_and_renaming() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let deep_term = "y * ".repeat(495) + "y";
            // Exercise replacement and body variable collection, then capture-
            // avoiding renaming through both term and formula trees. The rule
            // frames remain live while all of these helper traversals run.
            for (value, formula) in [
                (deep_term.clone(), "Ex y. x = x".to_owned()),
                ("y".to_owned(), "Ex y. ".to_owned() + &"T & ".repeat(495) + "x = x"),
                ("y".to_owned(), format!("Ex y. {deep_term} = x")),
                ("y".to_owned(), "Ex y. ".to_owned() + &"T & ".repeat(495) + "y = x"),
            ] {
                let source = format!(
                    "theory T begin builtins: diffie-hellman {}rule R: let x = {value} in [] --[_restrict({formula})]-> [] {}end",
                    "rule R: [] --> [] left ".repeat(255),
                    "right rule R: [] --> [] ".repeat(255),
                );
                drop(parse_theory(&source, &[]).unwrap());
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
