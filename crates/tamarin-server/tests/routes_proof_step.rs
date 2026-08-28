//! Integration tests for the live proof-tree mutation route.
//!
//! `/thy/trace/<idx>/proof-step/<lemma>/<path…>/<method>` has no upstream
//! counterpart.  The HS UI applies methods through `/main/method/…`.  This
//! route applies one proof method in place.  It answers with a `{html,title}`
//! envelope.  The envelope holds the sub-proof snippet, which the server
//! renders again, and the complete proof tree.
//!
//! Coverage:
//!   - the envelope and the applied method in the rendered tree;
//!   - the route keeps the change: `/main/proof/<lemma>` then shows the
//!     sub-case that the step produced.  This is the only place that checks
//!     that the in-memory `ProofState` survives a request;
//!   - an unknown lemma gives an `{alert}`, not a panic;
//!   - the root system a lemma's proof view renders carries the `[reuse]`
//!     lemmas HS's `mkSystem` gathers, and only those.

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
    // The tree below the snippet must show the method that the step applied
    // at the root.  It must also show the `sorry` child that the step opened
    // under that method.
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

    // This is the same URL and the same theory index.  The applied step must
    // be in the store, not only in the step response.  Simplify opens exactly
    // one case, and the name of that case is "".
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

// The root system of a lemma's proof view is built by `ProofState::new`, and
// its `lemmas:` field holds the `[reuse]` lemmas declared before that lemma.
// HS gathers them in `mkSystem` (CloseRule.hs:167-188#mkSystem), which the
// interactive server imports and calls (Handler.hs:160#mkSystem), so the web
// root system honours `[hide_lemma=..]` exactly as `--prove` does.
#[tokio::test]
async fn proof_view_root_system_drops_a_hidden_reuse_lemma() {
    if !maude_available() {
        eprintln!("skipping: maude not available");
        return;
    }
    let s = start_server_with_theory("hide_reuse_lemma.spthy").await;
    let sequent = |lemma: &'static str| {
        let client = s.client.clone();
        let url = s.url(&format!("/thy/trace/1/main/proof/{lemma}"));
        async move {
            let v: serde_json::Value = client
                .get(url)
                .send()
                .await
                .expect("send")
                .json()
                .await
                .expect("decode");
            v["html"].as_str().expect("html").to_string()
        }
    };
    // `helper` is `[reuse]` and guards the action `Helper( k )`, which occurs
    // nowhere else in the fixture's formulas.
    let keeps = sequent("keeps_helper").await;
    assert!(
        keeps.contains("Helper("),
        "a lemma that hides nothing must carry the reuse lemma; got: {keeps}",
    );
    let hides = sequent("hides_helper").await;
    assert!(
        !hides.contains("Helper("),
        "`[hide_lemma=helper]` must drop the reuse lemma from the root system; got: {hides}",
    );
}
