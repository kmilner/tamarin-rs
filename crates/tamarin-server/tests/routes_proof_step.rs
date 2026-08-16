//! Integration tests for the live proof-tree mutation route.
//!
//! `/thy/trace/<idx>/proof-step/<lemma>/<path…>/<method>` has no upstream
//! counterpart (the HS UI applies methods through `/main/method/…`); it
//! applies one proof method in place and answers a `{html,title}` envelope
//! carrying the re-rendered sub-proof snippet plus the whole proof tree.
//!
//! Coverage:
//!   - the envelope and the applied method in the rendered tree;
//!   - the mutation is kept: `/main/proof/<lemma>` grows the sub-case the step
//!     produced (this is the only place the in-memory `ProofState` is checked
//!     to survive a request);
//!   - an unknown lemma is an `{alert}`, not a panic.

mod common;

use common::*;

// We need a Maude binary for these tests (the proof-step path boots
// Maude for the per-theory `ProofContext`); `common::maude_available`
// is the shared skip-guard.

#[tokio::test]
async fn proof_step_simplify_returns_html_envelope() {
    if !maude_available() {
        eprintln!("skipping: maude not available");
        return;
    }
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/proof-step/debug/simplify"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(
        json_top_keys(&v),
        ["html", "title"].iter().map(|k| k.to_string()).collect(),
        "a step that applies must be {{html,title}}, never the {{alert}} arm",
    );
    assert_eq!(v["title"], serde_json::json!("Proof of debug"));
    let html = v["html"].as_str().expect("html");
    // The tree appended below the snippet must show the method that was just
    // applied at the root, over the `sorry` child the step opened.
    assert!(
        html.contains("<h2>Proof of <code>debug</code></h2>")
            && html.contains("<span class=\"proof-method\">simplify</span>")
            && html.contains("<span class=\"proof-method\">sorry</span>"),
        "the rendered tree must carry the applied simplify and its open child; got: {html}",
    );
}

#[tokio::test]
async fn proof_step_then_view_shows_applied_method() {
    if !maude_available() {
        eprintln!("skipping: maude not available");
        return;
    }
    let s = start_server_with_theory("issue193.spthy").await;
    let proof_view = || async {
        let v: serde_json::Value = s
            .client
            .get(s.url("/thy/trace/1/main/proof/debug"))
            .send()
            .await
            .expect("send")
            .json()
            .await
            .expect("decode");
        v["html"].as_str().expect("html").to_string()
    };

    // The untouched root has no children.
    let before = proof_view().await;
    assert!(
        before.contains("<h3>0 sub-case(s)</h3>"),
        "the unstepped root must render no sub-cases; got: {before}",
    );

    let r1 = s
        .client
        .get(s.url("/thy/trace/1/proof-step/debug/simplify"))
        .send()
        .await
        .expect("send 1");
    assert_eq!(r1.status(), 200);

    // Same URL, same theory index: the applied step must be in the store, not
    // just in the step response.  Simplify opens exactly one case, named "".
    let after = proof_view().await;
    assert!(
        after.contains("<h3>1 sub-case(s)</h3>")
            && after.contains(
                "<h4>Case </h4><br/>\n<static-graph graphSrc=\"/thy/trace/1/intdot/proof/debug/_\">"
            ),
        "the proof view must show the sub-case the step opened; got: {after}",
    );
}

#[tokio::test]
async fn proof_step_unknown_lemma_returns_alert() {
    if !maude_available() {
        eprintln!("skipping: maude not available");
        return;
    }
    let s = start_server_with_theory("issue193.spthy").await;
    let res = s
        .client
        .get(s.url("/thy/trace/1/proof-step/NONEXISTENT/simplify"))
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let v: serde_json::Value = res.json().await.expect("decode");
    assert_eq!(json_top_keys(&v), one_key_set("alert"));
    assert_eq!(
        v["alert"],
        serde_json::json!("no system at path [] in lemma NONEXISTENT"),
    );
}
