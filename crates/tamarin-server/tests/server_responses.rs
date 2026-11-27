// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! The server-response table: every row of `tests/fixtures/server_responses.tsv`
//! is one HTTP request whose answer is compared with the Haskell server's,
//! captured by `tests/capture_haskell_fixtures.sh` from the same table.
//!
//! The table's header documents the columns and comparison modes.  Rows run
//! in groups: a `SERVE` row starts one fresh server with one theory loaded at
//! index 1, and the rows below it run against that server in file order, on
//! both sides.  So a stateful sequence (an autoprove, then the index it
//! allocated) replays identically, and its bytes are comparable.
//!
//! Every row runs, and the test reports every mismatch at once.

mod common;

use std::collections::BTreeSet;
use std::path::PathBuf;

use common::*;

const TABLE_PATH: &str = "tests/fixtures/server_responses.tsv";

enum Method {
    Get,
    Post,
    /// `POST /` with the given file as the `uploadedTheory` form field.
    Upload(PathBuf),
}

enum Compare {
    Bytes,
    /// Bytes, with the theory's load time and origin path blanked.
    LoadStamp,
    /// Bytes, with the `Generated from:` banner's build values blanked.
    Banner,
    /// Every listed line occurs in the body (and in the oracle's).
    Contains(Vec<String>),
    /// The `Location` header is the captured one.
    Redirect,
    /// A documented divergence: the body differs from the oracle's capture.
    Diverge,
    /// A documented divergence: the oracle answers something else (checked at
    /// capture time), and the port answers the named capture, byte for byte.
    DivergeAs(String),
}

struct Row {
    line: usize,
    method: Method,
    path: String,
    status: u16,
    content_type: Option<String>,
    compare: Compare,
    capture: Option<String>,
}

struct Group {
    line: usize,
    theory: String,
    config: Vec<String>,
    rows: Vec<Row>,
}

fn table_text() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(TABLE_PATH);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn parse_table() -> Vec<Group> {
    let mut groups: Vec<Group> = Vec::new();
    for (i, raw) in table_text().lines().enumerate() {
        let line = i + 1;
        if raw.is_empty() || raw.starts_with('#') {
            continue;
        }
        let cols: Vec<&str> = raw.split('\t').collect();
        if cols[0] == "SERVE" {
            groups.push(Group {
                line,
                theory: cols.get(1).expect("SERVE names a theory").to_string(),
                config: cols[2..].iter().map(|c| c.to_string()).collect(),
                rows: Vec::new(),
            });
            continue;
        }
        let [method, path, status, content_type, compare, capture] = cols[..] else {
            panic!("{TABLE_PATH}:{line}: expected 6 tab-separated columns: {raw:?}");
        };
        let method = match method {
            "GET" => Method::Get,
            "POST" => Method::Post,
            m => match m.strip_prefix("UPLOAD:") {
                Some(file) => Method::Upload(theory_path(file)),
                None => panic!("{TABLE_PATH}:{line}: unknown method {m}"),
            },
        };
        let compare = match compare {
            "bytes" => Compare::Bytes,
            "load-stamp" => Compare::LoadStamp,
            "banner" => Compare::Banner,
            "redirect" => Compare::Redirect,
            "diverge" => Compare::Diverge,
            c => {
                if let Some(lines) = c.strip_prefix("contains:") {
                    Compare::Contains(lines.split("\\n").map(str::to_string).collect())
                } else if let Some(other) = c.strip_prefix("diverge:") {
                    Compare::DivergeAs(other.to_string())
                } else {
                    panic!("{TABLE_PATH}:{line}: unknown comparison {c}")
                }
            }
        };
        let optional = |s: &str| (s != "-").then(|| s.to_string());
        let row = Row {
            line,
            method,
            path: path.to_string(),
            status: status
                .parse()
                .unwrap_or_else(|_| panic!("{TABLE_PATH}:{line}: bad status {status}")),
            content_type: optional(content_type),
            compare,
            capture: optional(capture),
        };
        groups
            .last_mut()
            .unwrap_or_else(|| panic!("{TABLE_PATH}:{line}: request before any SERVE row"))
            .rows
            .push(row);
    }
    groups
}

/// Where the first difference between two bodies is, for the failure report:
/// its line, and both bodies from a little before it.
fn first_difference(got: &str, want: &str) -> String {
    let at = got
        .char_indices()
        .zip(want.chars())
        .find(|((_, g), w)| g != w)
        .map_or(got.len().min(want.len()), |((i, _), _)| i);
    let line = got[..at].matches('\n').count() + 1;
    let start = got[..at].char_indices().rev().nth(60).map_or(0, |(i, _)| i);
    let clip = |s: &str| {
        s[start.min(s.len())..]
            .chars()
            .take(160)
            .collect::<String>()
    };
    format!(
        "first difference at line {line}:\n      port:   {:?}\n      oracle: {:?}",
        clip(got),
        clip(want)
    )
}

/// Run one row against the group's server; `Err` describes the mismatch.
async fn check_row(s: &TestServer, theory: &str, row: &Row) -> Result<(), String> {
    let request = match &row.method {
        Method::Get => s.client.get(s.url(&row.path)),
        Method::Post => s.client.post(s.url(&row.path)),
        Method::Upload(file) => {
            let content =
                std::fs::read(file).map_err(|e| format!("read {}: {e}", file.display()))?;
            let name = file
                .file_name()
                .expect("upload file name")
                .to_string_lossy();
            let part = reqwest::multipart::Part::bytes(content)
                .file_name(name.into_owned())
                .mime_str("text/plain")
                .expect("text/plain is a MIME type");
            s.client
                .post(s.url(&row.path))
                .multipart(reqwest::multipart::Form::new().part("uploadedTheory", part))
        }
    };
    let res = request.send().await.map_err(|e| format!("request: {e}"))?;
    let status = res.status().as_u16();
    let content_type = content_type(&res);
    let location = header(&res, reqwest::header::LOCATION);
    let body = res.text().await.map_err(|e| format!("read body: {e}"))?;

    let mut problems = Vec::new();
    if status != row.status {
        problems.push(format!("status {status}, expected {}", row.status));
    }
    if let Some(want) = row
        .content_type
        .as_ref()
        .filter(|want| **want != content_type)
    {
        problems.push(format!("content type {content_type:?}, expected {want:?}"));
    }
    let capture = || {
        haskell_capture(
            row.capture
                .as_deref()
                .expect("this comparison needs a capture"),
        )
    };
    let mut same = |got: String, want: String| {
        if got != want {
            problems.push(first_difference(&got, &want));
        }
    };
    match &row.compare {
        Compare::Bytes => same(body, capture()),
        Compare::LoadStamp => same(
            blank_load_stamp(&body, theory),
            blank_load_stamp(&capture(), theory),
        ),
        Compare::Banner => same(
            blank_version_banner(&body),
            blank_version_banner(&capture()),
        ),
        Compare::Redirect => same(location, capture()),
        Compare::DivergeAs(other) => same(body, haskell_capture(other)),
        Compare::Diverge => {
            if body == capture() {
                problems.push("the port now answers the oracle's body; drop `diverge`".into());
            }
        }
        Compare::Contains(lines) => {
            let oracle = row.capture.as_deref().map(haskell_capture);
            for line in lines {
                if !body.contains(line.as_str()) {
                    problems.push(format!("body lacks {line:?}; got {body:?}"));
                }
                if oracle.as_ref().is_some_and(|o| !o.contains(line.as_str())) {
                    problems.push(format!("the capture lacks {line:?}"));
                }
            }
        }
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n    "))
    }
}

async fn run_group(group: Group) -> Vec<String> {
    let config = group.config.clone();
    let s = start_server_with_theory_and(&group.theory, move |cfg| {
        for token in &config {
            match token.as_str() {
                // Navigation must not need the prover: every proof session
                // started after the load would fail.
                "maude=missing" => cfg.load.maude_path = "/definitely/missing/maude".into(),
                other => panic!("unknown SERVE config {other}"),
            }
        }
    })
    .await;
    let mut failures = Vec::new();
    for row in &group.rows {
        if let Err(problem) = check_row(&s, &group.theory, row).await {
            failures.push(format!(
                "{TABLE_PATH}:{} ({} served at line {}) {}:\n    {problem}",
                row.line, group.theory, group.line, row.path
            ));
        }
    }
    failures
}

#[tokio::test(flavor = "multi_thread")]
async fn every_row_answers_as_the_oracle_did() {
    let tasks: Vec<_> = parse_table()
        .into_iter()
        .map(|group| tokio::spawn(run_group(group)))
        .collect();
    let mut failures = Vec::new();
    for task in tasks {
        failures.extend(task.await.expect("group task"));
    }
    assert!(
        failures.is_empty(),
        "{} row(s) differ:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The capture directory holds exactly what the table names, so the captured
/// and the asserted sets cannot drift apart.
#[test]
fn every_capture_belongs_to_a_row() {
    let mut named = BTreeSet::new();
    for row in parse_table().into_iter().flat_map(|g| g.rows) {
        named.extend(row.capture);
        if let Compare::DivergeAs(other) = row.compare {
            named.insert(other);
        }
    }
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/haskell-responses");
    let present: BTreeSet<String> = std::fs::read_dir(&dir)
        .expect("read the capture directory")
        .map(|e| {
            e.expect("dir entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|name| name != "oracle_rev")
        .collect();
    let orphans: Vec<_> = present.difference(&named).collect();
    let missing: Vec<_> = named.difference(&present).collect();
    assert!(
        orphans.is_empty() && missing.is_empty(),
        "captures no row names: {orphans:?}; rows naming a missing capture: {missing:?} \
         (re-run tests/capture_haskell_fixtures.sh)"
    );
}
