//! Integration tests for the file-upload path (`POST /`).
//!
//! Haskell handles a multipart form with field name `uploadedTheory`
//! and re-renders the index with the theory installed at a fresh idx.
//! Rust does the same.

mod common;

use common::*;

#[tokio::test]
async fn test_post_index_uploads_theory() {
    let s = start_server_with_theory("issue193.spthy").await;

    // After start, the store has 1 theory at idx=1.  Posting a new
    // theory should register it at idx=2 and render the index showing
    // both.
    let src = std::fs::read_to_string(fixture_path("Tutorial.spthy")).expect("read Tutorial.spthy");
    let form = reqwest::multipart::Form::new().part(
        "uploadedTheory",
        reqwest::multipart::Part::text(src)
            .file_name("Tutorial.spthy")
            .mime_str("text/plain")
            .expect("set mime"),
    );

    let res = s
        .client
        .post(s.url("/"))
        .multipart(form)
        .send()
        .await
        .expect("send POST /");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read body");
    // Both theory names should now appear.
    assert!(
        body.contains("RevealingSignatures"),
        "POST / index should list pre-loaded theory; body={}",
        body
    );
    assert!(
        body.contains("Tutorial"),
        "POST / index should list newly uploaded theory; body={}",
        body
    );
    // And the new theory should be linked at idx=2.
    assert!(
        body.contains("/thy/trace/2/overview/help"),
        "second theory should be at idx=2; body={}",
        body
    );
}

#[tokio::test]
async fn test_post_index_with_empty_field_shows_alert() {
    let s = start_server_with_theory("issue193.spthy").await;
    // Empty field — Rust port renders the index with an inline
    // "No theory file given." banner (Haskell does too).
    let form = reqwest::multipart::Form::new().part(
        "uploadedTheory",
        reqwest::multipart::Part::text(String::new())
            .file_name("empty.spthy")
            .mime_str("text/plain")
            .expect("mime"),
    );
    let res = s
        .client
        .post(s.url("/"))
        .multipart(form)
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read");
    // The Rust port surfaces "No theory file given." via a
    // <p class="message"> banner.
    assert!(
        body.contains("No theory file given.")
            || body.contains("upload failed")
            || body.contains("Theory loading failed"),
        "expected an upload-error message; body={}",
        body
    );
}

#[tokio::test]
async fn test_post_index_with_garbage_source_shows_alert() {
    let s = start_server_with_theory("issue193.spthy").await;
    let form = reqwest::multipart::Form::new().part(
        "uploadedTheory",
        reqwest::multipart::Part::text("this is not a theory".to_string())
            .file_name("garbage.spthy")
            .mime_str("text/plain")
            .expect("mime"),
    );
    let res = s
        .client
        .post(s.url("/"))
        .multipart(form)
        .send()
        .await
        .expect("send");
    assert_eq!(res.status(), 200);
    let body = res.text().await.expect("read");
    assert!(
        body.contains("Theory loading failed")
            || body.contains("parse error")
            || body.contains("elaboration error"),
        "expected parse/elaborate error message in banner; body=\n{}",
        body
    );
}
