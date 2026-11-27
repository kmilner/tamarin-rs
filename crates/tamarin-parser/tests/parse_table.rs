//! The parser's accept/reject table, checked against the pinned Haskell
//! oracle's `--parse-only` outcome.
//!
//! Each row of `tests/fixtures/parse_cases.tsv` is one input. Columns:
//!
//! - `name`: unique.
//! - `mode`: `theory` or `diff` (HS `--parse-only`, with `--diff`), either
//!   followed by `-D=FLAG` arguments; or `intruder`, the intruder-rule entry
//!   point, which HS has no command line for.
//! - `hs`: `ok` or `err`, the oracle's outcome, written by
//!   `scripts/capture_parse_refs.sh` and never by hand; `-` for `intruder`.
//! - `rs`: `ok`, or the port's error kind with its key payload. A leading `~`
//!   marks a deliberate divergence: the outcome must then differ from `hs`,
//!   and the comment above the row says why.
//! - `input`: the root theory, with `\n`, `\t` and `\\` escapes. A line
//!   `@@@ <path>` starts a further file, written beside the root so an
//!   `#include` can name it.
//!
//! Only the outcome is compared with HS. Parsec's positions and messages are
//! not a parity target: the port renders its own diagnostics.
//!
//! `PARSE_TABLE_BLESS=1 cargo test -p tamarin-parser --test parse_table`
//! rewrites the `rs` column from the port; review the diff.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use tamarin_parser::ast::{Rule, TheoryItem};
use tamarin_parser::{
    parse_diff_theory_with_base, parse_intruder_rules, parse_theory_with_rule_check, ParseError,
    ParseErrorKind, RuleConflictCheck,
};
use tamarin_term::maude_sig::pair_maude_sig;

const TABLE: &str = "tests/fixtures/parse_cases.tsv";

/// HS rejects a rule whose name an earlier, different rule took while it
/// parses (`liftedAddProtoRule`); the CLI installs the elaborated comparison.
/// Comparing the parsed rules gives the same verdict for every row here.
#[derive(Default)]
struct RulesDifferAsParsed {
    rules: Vec<Rule>,
}

impl RuleConflictCheck for RulesDifferAsParsed {
    fn declare(&mut self, item: &TheoryItem) {
        if let TheoryItem::Rule(r) = item {
            self.rules.push(r.clone());
        }
    }

    fn conflicts(&mut self, new: &Rule) -> bool {
        self.rules
            .iter()
            .find(|r| r.name == new.name)
            .is_some_and(|prev| {
                (&prev.attributes, &prev.lets, &prev.premises, &prev.actions)
                    != (&new.attributes, &new.lets, &new.premises, &new.actions)
                    || (
                        &prev.conclusions,
                        &prev.embedded_restrictions,
                        &prev.variants,
                    ) != (&new.conclusions, &new.embedded_restrictions, &new.variants)
            })
    }
}

/// The error kind and the payload that identifies it; spans and message text
/// are left out.
fn kind_tag(kind: &ParseErrorKind) -> String {
    use ParseErrorKind::*;
    match kind {
        Expected { context } => format!("Expected({context:?})"),
        ReservedKeyword { keyword } => format!("ReservedKeyword({keyword})"),
        IllegalDiffOperator(reason) => format!("IllegalDiffOperator({reason:?})"),
        DuplicateMacroArgument { argument } => format!("DuplicateMacroArgument({argument})"),
        UndeclaredFunction { name } => format!("UndeclaredFunction({name})"),
        ReservedBuiltin { name, context } => format!("ReservedBuiltin({name},{context:?})"),
        MalformedHexColor { .. } => "MalformedHexColor".into(),
        WrongFunctionArity {
            name,
            declared,
            used,
        } => format!("WrongFunctionArity({name},{declared},{used})"),
        ConflictingDeclaration { name, context } => {
            format!("ConflictingDeclaration({name},{context:?})")
        }
        DuplicateDeclaration { name, context } => {
            format!("DuplicateDeclaration({name},{context:?})")
        }
        NonBinaryAcFunction { name, arity } => format!("NonBinaryAcFunction({name},{arity})"),
        UnclosedDelimiter { opening, .. } => format!("UnclosedDelimiter({opening})"),
        UnclosedBlockComment { .. } => "UnclosedBlockComment".into(),
        UnknownItem { item, context } => format!("UnknownItem({item},{context:?})"),
        InvalidFactName { name } => format!("InvalidFactName({name})"),
        PersistentFreshFact => "PersistentFreshFact".into(),
        FactArity { name, arity } => format!("FactArity({name},{arity})"),
        IncludeIo { .. } => "IncludeIo".into(),
        Custom => "Custom".into(),
        other => format!("{other:?}"),
    }
}

fn unescape(cell: &str) -> String {
    let mut out = String::with_capacity(cell.len());
    let mut chars = cell.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('\\') => out.push('\\'),
            other => panic!("bad escape \\{other:?} in {cell:?}"),
        }
    }
    out
}

struct Row<'a> {
    line: usize,
    name: &'a str,
    mode: &'a str,
    hs: &'a str,
    rs: &'a str,
    input: String,
}

fn rows(table: &str) -> Vec<Row<'_>> {
    table
        .lines()
        .enumerate()
        .filter(|(_, l)| !l.is_empty() && !l.starts_with('#'))
        .map(|(i, l)| {
            let cols: Vec<&str> = l.split('\t').collect();
            assert_eq!(cols.len(), 5, "{TABLE}:{}: expected 5 columns", i + 1);
            Row {
                line: i + 1,
                name: cols[0],
                mode: cols[1],
                hs: cols[2],
                rs: cols[3],
                input: unescape(cols[4]),
            }
        })
        .collect()
}

/// Write the row's files into a fresh directory and return it with the root
/// source, or no directory when the row has no `#include`.
fn stage(name: &str, input: &str) -> (Option<PathBuf>, String) {
    let mut parts = input.split("\n@@@ ");
    let root = parts.next().unwrap_or_default().to_string();
    if !input.contains("#include") {
        return (None, root);
    }
    let dir =
        std::env::temp_dir().join(format!("tamarin_parse_table_{}_{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for part in parts {
        let (path, body) = part.split_once('\n').unwrap_or((part, ""));
        let path = dir.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, body).unwrap();
    }
    (Some(dir), root)
}

fn run(row: &Row<'_>) -> Result<(), ParseError> {
    let mut words = row.mode.split_whitespace();
    let kind = words.next().unwrap_or_default();
    let flags: Vec<&str> = words
        .map(|w| {
            w.strip_prefix("-D=")
                .unwrap_or_else(|| panic!("{}: bad mode argument {w:?}", row.name))
        })
        .collect();
    let (dir, root) = stage(row.name, &row.input);
    let result = match kind {
        "theory" => parse_theory_with_rule_check(
            &root,
            &flags,
            dir.clone(),
            Box::<RulesDifferAsParsed>::default(),
        )
        .map(drop),
        "diff" => parse_diff_theory_with_base(&root, &flags, dir.clone()).map(drop),
        "intruder" => parse_intruder_rules(&pair_maude_sig(), &root).map(drop),
        other => panic!("{}: unknown mode {other:?}", row.name),
    };
    if let Some(dir) = dir {
        let _ = std::fs::remove_dir_all(dir);
    }
    result
}

fn outcome(result: &Result<(), ParseError>) -> String {
    match result {
        Ok(()) => "ok".into(),
        Err(error) => kind_tag(error.kind()),
    }
}

#[test]
fn every_row_matches_the_port_and_the_oracle() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(TABLE);
    let table = std::fs::read_to_string(&path).unwrap();
    let captured_rev = table
        .lines()
        .find_map(|line| line.strip_prefix("# oracle: "))
        .expect("missing oracle revision in parse_cases.tsv");
    assert_eq!(
        captured_rev,
        tamarin_test_support::pinned_oracle_revision(),
        "refresh the parser references with scripts/capture_parse_refs.sh"
    );
    let rows = rows(&table);
    let bless = std::env::var_os("PARSE_TABLE_BLESS").is_some();
    let mut names = BTreeSet::new();
    let mut failures = Vec::new();
    let mut blessed: Vec<(usize, String)> = Vec::new();
    for row in &rows {
        assert!(names.insert(row.name), "duplicate row name {}", row.name);
        let hs_runs = !row.mode.starts_with("intruder");
        match (hs_runs, row.hs) {
            (true, "ok" | "err") | (false, "-") => {}
            _ => failures.push(format!(
                "{}: hs is {:?}; run scripts/capture_parse_refs.sh",
                row.name, row.hs
            )),
        }
        let got = outcome(&run(row));
        let (diverges, want) = match row.rs.strip_prefix('~') {
            Some(want) => (true, want),
            None => (false, row.rs),
        };
        if got != want {
            if bless {
                let marker = if diverges { "~" } else { "" };
                blessed.push((row.line, format!("{marker}{got}")));
            } else {
                failures.push(format!("{}: port gives {got}, table says {want}", row.name));
            }
        }
        if hs_runs && matches!(row.hs, "ok" | "err") {
            let agrees = (row.hs == "ok") == (got == "ok");
            if agrees == diverges {
                failures.push(format!(
                    "{}: oracle {}, port {got}{}",
                    row.name,
                    row.hs,
                    if diverges {
                        " (marked ~ as a divergence, but they now agree)"
                    } else {
                        ""
                    }
                ));
            }
        }
    }
    if bless && !blessed.is_empty() {
        let mut lines: Vec<String> = table.lines().map(String::from).collect();
        for (line, rs) in blessed {
            let mut cols: Vec<&str> = lines[line - 1].split('\t').collect();
            cols[3] = &rs;
            lines[line - 1] = cols.join("\t");
        }
        std::fs::write(&path, lines.join("\n") + "\n").unwrap();
    }
    assert!(
        failures.is_empty(),
        "{} of {} rows fail:\n{}",
        failures.len(),
        rows.len(),
        failures.join("\n")
    );
}
