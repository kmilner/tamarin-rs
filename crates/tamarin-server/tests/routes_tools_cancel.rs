// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Server contracts no oracle capture can pin: the graph route's external
//! tools (`--with-json`'s renderer, `--image-format`, the `-Kfdp` retry),
//! driven through stub executables, and `/kill` cancellation of autoprove,
//! oracle and session-start work.  Responses an oracle CAN pin are rows of
//! `tests/fixtures/server_responses.tsv`.

mod common;

use common::*;

/// Write an executable `/bin/sh` stub standing in for an external tool into
/// `dir`, and return its path.  `dot` is called as HS `dotToImg` does
/// (`-T<format> -K<mode> -o <img> <graph>`), the `--with-json` renderer as
/// `jsonToImg` does (`<img> <json>`).
fn tool_stub(dir: &tempfile::TempDir, name: &str, body: &str) -> String {
    use std::os::unix::fs::PermissionsExt;
    let path = dir.path().join(name);
    std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write stub");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).expect("chmod stub");
    path.to_string_lossy().into_owned()
}

/// GET the proof graph of issue193's `debug` lemma from a server whose
/// config `mutate` points at stub tools.
async fn graph_with(mutate: impl FnOnce(&mut tamarin_server::ServerConfig)) -> reqwest::Response {
    let s = start_server_with_theory_and(ISSUE193, mutate).await;
    s.get("/thy/trace/1/graph/proof/debug").await
}

/// `/graph`'s external tools.  A failing `dot` layout is retried with
/// `-Kfdp`, and when both fail the route is HS's `notFound`.
/// `--image-format=png` reaches `dotToImg` as `-Tpng`, names the image
/// `<graph>.png` and serves it as `image/png` (`renderGraphCode`,
/// Web/Theory.hs; `imageFormatMIME`, Web/Types.hs).  `--with-json` switches
/// to HS's `OutJSON` branch: the system's JSON graph is written to a file
/// that the renderer turns into the image (`jsonToImg`, Web/Theory.hs), and a
/// failing renderer is `imgGenerated False`, the Not Found page.
#[tokio::test]
async fn graph_routes_drive_their_external_tools() {
    let dir = tempfile::tempdir().expect("stub dir");
    let fdp_only = tool_stub(
        &dir,
        "fdp-only",
        "[ \"$2\" = -Kfdp ] || exit 1\n[ -s \"$5\" ] || exit 2\nprintf '<svg><!--fdp--></svg>' > \"$4\"",
    );
    let res = graph_with(|cfg| cfg.dot_path = fdp_only).await;
    assert_eq!(res.status(), 200);
    assert_eq!(content_type(&res), "image/svg+xml");
    assert_eq!(res.text().await.expect("text"), "<svg><!--fdp--></svg>");

    let failing = tool_stub(&dir, "dot-fail", "exit 1");
    assert_eq!(graph_with(|cfg| cfg.dot_path = failing).await.status(), 404);

    // The stub writes its format, layout and output path into the image.
    let echo = tool_stub(
        &dir,
        "dot-echo",
        "printf '%s %s %s' \"$1\" \"$2\" \"$4\" > \"$4\"",
    );
    let res = graph_with(|cfg| {
        cfg.dot_path = echo;
        cfg.image_format = tamarin_server::ImageFormat::Png;
    })
    .await;
    assert_eq!(res.status(), 200);
    assert_eq!(content_type(&res), "image/png");
    let body = res.text().await.expect("text");
    assert!(body.starts_with("-Tpng -Kdot "), "{body}");
    assert!(body.ends_with(".dot.png"), "{body}");

    // The renderer is handed a non-empty JSON graph file.
    let json_ok = tool_stub(
        &dir,
        "json-ok",
        "[ -s \"$2\" ] || exit 3\ngrep -q graphs \"$2\" || exit 4\nprintf '<svg><!--json-stub--></svg>' > \"$1\"",
    );
    let res = graph_with(|cfg| cfg.json_path = Some(json_ok)).await;
    assert_eq!(res.status(), 200);
    assert_eq!(content_type(&res), "image/svg+xml");
    assert_eq!(
        res.text().await.expect("text"),
        "<svg><!--json-stub--></svg>"
    );

    let json_fail = tool_stub(&dir, "json-fail", "exit 7");
    assert_eq!(
        graph_with(|cfg| cfg.json_path = Some(json_fail))
            .await
            .status(),
        404
    );
}

/// Issue #50: acknowledging /kill must stop the blocking worker, and must
/// not publish its partial proof. Repeating the request also checks cleanup.
#[tokio::test]
async fn cancel_autoprove_stops_loop_without_publishing() {
    use std::time::Duration;

    let s = start_server_with_theory("loop.spthy").await;
    for path in [
        "/thy/trace/1/autoprove/idfs/0/False/proof/exec",
        "/thy/trace/1/autoproveAll/idfs/0/proof/exec",
        "/thy/trace/1/autoprove/idfs/0/False/proof/exec",
    ] {
        let client = s.client.clone();
        // jQuery adds a cache-busting query, absent from the UI cancel key.
        let url = format!("{}?_=123456789", s.url(path));
        let mut proof = tokio::spawn(async move {
            client
                .get(url)
                .send()
                .await
                .unwrap()
                .json::<serde_json::Value>()
                .await
                .unwrap()
        });
        // Let the worker enter the nonterminating search before cancelling.
        tokio::time::sleep(Duration::from_millis(250)).await;
        assert!(!proof.is_finished(), "loop unexpectedly finished");
        let response = s
            .client
            .get(s.url(&format!(
                "/kill?path={}",
                percent_encoding::utf8_percent_encode(path, percent_encoding::NON_ALPHANUMERIC)
            )))
            .send()
            .await
            .unwrap();
        assert_eq!(response.text().await.unwrap(), "Canceled request!");
        // The handler awaits spawn_blocking: this response proves the worker
        // exited, rather than just abandoning its JoinHandle.
        let result = tokio::time::timeout(Duration::from_secs(10), &mut proof).await;
        if result.is_err() {
            proof.abort();
        }
        assert_eq!(
            result.expect("cancelled worker exits promptly").unwrap()["alert"],
            "Canceled request!"
        );
        assert_eq!(s.get("/thy/trace/2/overview/help").await.status(), 404);
    }
    // A subsequent bounded search on the original theory still works.
    let response: serde_json::Value = s
        .get("/thy/trace/1/autoprove/idfs/1/False/proof/exec")
        .await
        .json()
        .await
        .unwrap();
    assert_eq!(redirect_idx(&response, "overview/proof/exec"), 2);
}

/// A blocked oracle must be terminated, and subsequent requests on the same
/// retained session must produce the same proof as a clean session.
#[cfg(unix)]
#[tokio::test]
async fn cancel_oracle_then_restart_preserves_proofs() {
    use std::os::unix::fs::PermissionsExt;
    use std::time::Duration;
    let dir = tempfile::tempdir().unwrap();
    let theory = dir.path().join("theory.spthy");
    std::fs::write(
        &theory,
        std::fs::read(fixture_path("oracle_missing.spthy")).unwrap(),
    )
    .unwrap();
    let oracle = dir.path().join("oracle");
    std::fs::write(&oracle, "#!/bin/sh\ncd \"$(dirname \"$0\")\"\nif mkdir blocked 2>/dev/null; then\n  touch ready\n  sleep 60\nfi\ncat >/dev/null\nprintf '0\\n'\n").unwrap();
    std::fs::set_permissions(&oracle, std::fs::Permissions::from_mode(0o755)).unwrap();
    let s = start_server_with_theory(theory.to_str().unwrap()).await;
    for path in [
        "/thy/trace/1/autoprove/idfs/0/False/proof/test",
        "/thy/trace/1/main/method/test/1",
        "/thy/trace/1/main/proof/test",
    ] {
        let client = s.client.clone();
        let url = s.url(path);
        let pending = tokio::spawn(async move {
            client
                .get(url)
                .send()
                .await
                .unwrap()
                .json::<serde_json::Value>()
                .await
                .unwrap()
        });
        let entered = tokio::time::timeout(Duration::from_secs(5), async {
            while !dir.path().join("ready").exists() {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await;
        let kill = format!(
            "/kill?path={}",
            percent_encoding::utf8_percent_encode(path, percent_encoding::NON_ALPHANUMERIC)
        );
        let killed = tokio::time::timeout(Duration::from_secs(5), s.get(&kill)).await;
        assert!(entered.is_ok(), "oracle never entered");
        assert_eq!(
            killed
                .expect("cancel waits for prompt worker exit")
                .text()
                .await
                .unwrap(),
            "Canceled request!"
        );
        // Start again before even consuming the old request's response.
        let retried: serde_json::Value = s
            .get("/thy/trace/1/autoprove/idfs/0/False/proof/test")
            .await
            .json()
            .await
            .unwrap();
        let idx = redirect_idx(&retried, "overview/proof/test");
        assert_eq!(pending.await.unwrap()["alert"], "Canceled request!");
        let clean = start_server_with_theory(theory.to_str().unwrap()).await;
        let baseline: serde_json::Value = clean
            .get("/thy/trace/1/autoprove/idfs/0/False/proof/test")
            .await
            .json()
            .await
            .unwrap();
        let baseline_idx = redirect_idx(&baseline, "overview/proof/test");
        assert_eq!(
            s.get(&format!("/thy/trace/{idx}/source"))
                .await
                .text()
                .await
                .unwrap(),
            clean
                .get(&format!("/thy/trace/{baseline_idx}/source"))
                .await
                .text()
                .await
                .unwrap()
        );
        std::fs::remove_file(dir.path().join("ready")).unwrap();
        std::fs::remove_dir(dir.path().join("blocked")).unwrap();
    }
}

/// Navigation also offers Cancel while lazily starting the proof session.
#[cfg(unix)]
#[tokio::test]
async fn cancel_navigation_during_session_start_then_retry() {
    use std::os::unix::fs::PermissionsExt;
    use std::time::Duration;
    for path in [
        "/thy/trace/1/overview/help",
        "/thy/trace/1/next/normal/proof/debug",
        "/thy/trace/1/prev/normal/proof/debug",
    ] {
        let dir = tempfile::tempdir().unwrap();
        let wrapper = dir.path().join("maude");
        let s = start_server_with_theory_and(ISSUE193, |cfg| {
            let maude = cfg.load.maude_path.replace("'", "'\"'\"'");
            let cwd = dir.path().to_str().unwrap().replace("'", "'\"'\"'");
            std::fs::write(&wrapper, format!(
                "#!/bin/sh\ncd '{cwd}'\nif [ -f block ]; then\n touch ready\n sleep 60 &\n wait\n exit 1\nfi\nexec '{maude}' \"$@\"\n"
            )).unwrap();
            std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
            cfg.load.maude_path = wrapper.to_str().unwrap().to_owned();
        }).await;
        std::fs::write(dir.path().join("block"), "").unwrap();
        let client = s.client.clone();
        let url = format!("{}?_=123456789", s.url(path));
        let pending = tokio::spawn(async move { client.get(url).send().await.unwrap() });
        tokio::time::timeout(Duration::from_secs(5), async {
            while !dir.path().join("ready").exists() {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .expect("navigation entered Maude startup");
        let kill = format!(
            "/kill?path={}",
            percent_encoding::utf8_percent_encode(path, percent_encoding::NON_ALPHANUMERIC)
        );
        let response = tokio::time::timeout(Duration::from_secs(5), s.get(&kill))
            .await
            .expect("navigation stops promptly");
        assert_eq!(response.text().await.unwrap(), "Canceled request!");
        assert_eq!(pending.await.unwrap().status(), 204);
        std::fs::remove_file(dir.path().join("block")).unwrap();
        let retry = s.get(path).await;
        assert_eq!(retry.status(), 200);
        let clean = start_server_with_theory(ISSUE193).await;
        assert_eq!(
            blank_times(&retry.text().await.unwrap()),
            blank_times(&clean.get(path).await.text().await.unwrap())
        );
    }
}
