//! Report data type and rendering (matches the oracle's WARNING comment).

use std::collections::BTreeSet;

/// One topic block of the wellformedness report: a header `topic` and the
/// already-formatted `message` body that appears beneath its underline.
#[derive(Debug, Clone, PartialEq)]
pub struct WfError {
    pub topic: String,
    pub message: String,
}

impl WfError {
    pub fn new(topic: impl Into<String>, message: impl Into<String>) -> Self {
        WfError {
            topic: topic.into(),
            message: message.into(),
        }
    }
}

pub type WfReport = Vec<WfError>;

/// The success line the oracle prints when no check fails.
pub const SUCCESS_LINE: &str = "/* All wellformedness checks were successful. */";

/// A topic header formatted exactly as the oracle renders it: the title on one
/// line, then `=` repeated to the title's (character) length on the next.
pub fn underline_topic(title: &str) -> String {
    let n = title.chars().count();
    let bar: String = std::iter::repeat('=').take(n).collect();
    format!("{}\n{}", title, bar)
}

/// The set of distinct topics present in a report.
pub fn topics(report: &WfReport) -> BTreeSet<String> {
    report.iter().map(|e| e.topic.clone()).collect()
}

/// Render one topic block: header + underline + blank line + body.
fn render_block(e: &WfError) -> String {
    format!("{}\n\n{}", underline_topic(&e.topic), e.message)
}

/// Render a full report as the oracle's WARNING comment (byte-identical), or
/// the success line for an empty report.
pub fn render_report(report: &WfReport) -> String {
    if report.is_empty() {
        return SUCCESS_LINE.to_string();
    }
    let blocks: Vec<String> = report.iter().map(render_block).collect();
    let inner = format!(
        "WARNING: the following wellformedness checks failed!\n\n{}",
        blocks.join("\n\n")
    );
    format!("/*\n{}\n*/", inner)
}

/// Insert `errors` into `report` immediately before the first entry whose topic
/// is one of `anchors`. If no anchor is present, append at the end.
pub fn insert_wf_before(report: &mut Vec<WfError>, errors: Vec<WfError>, anchors: &[&str]) {
    if errors.is_empty() {
        return;
    }
    match report
        .iter()
        .position(|e| anchors.iter().any(|a| *a == e.topic))
    {
        Some(i) => {
            let tail = report.split_off(i);
            report.extend(errors);
            report.extend(tail);
        }
        None => report.extend(errors),
    }
}
