// Currently GPL 3.0; see README.md for licensing details.

//! Interactive mode on the proved-only algebra backend.
//!
//! Each test drives the routes a user's session touches (the theory page,
//! opening a lemma, one manual proof step, autoprove from the state that
//! step reached, and the resulting proof) on a server whose sessions run on
//! the in-process Lean library, and compares every response with a server
//! on the Maude backend given the same requests.
//!
//! The native backend exists only in a build with `lean-unification`
//! (`cargo test -p tamarin-server --features tamarin-term/lean-unification`).
//! Without it these tests check that a proved-only load is refused, which is
//! all such a build can do. `scripts/interactive_backend_check.sh` runs the
//! same session against the real binary.

mod common;

use common::*;
use tamarin_term::algebra_backend::AlgebraBackend;

/// A corpus theory by absolute path. `fixture_path` joins its argument to
/// the fixtures directory, and joining an absolute path yields that path.
fn corpus_theory(relative: &str) -> String {
    let path = tamarin_test_support::corpus_root().join(relative);
    path.canonicalize()
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()))
        .display()
        .to_string()
}

async fn server(theory: &str, backend: AlgebraBackend) -> TestServer {
    start_server_with_theory_and(theory, |cfg| {
        cfg.algebra_backend = backend;
        if backend == AlgebraBackend::ProvedOnly {
            // A native session must never reach for a Maude binary.
            cfg.maude_path = "/nonexistent/maude-for-proved-only".into();
        }
    })
    .await
}

fn native_backend_is_built() -> bool {
    AlgebraBackend::ProvedOnly.validate().is_ok()
}

async fn body(s: &TestServer, path: &str) -> String {
    let response = s.get(path).await;
    assert_eq!(response.status(), 200, "{path}");
    response.text().await.expect("text")
}

async fn redirect(s: &TestServer, path: &str) -> String {
    let reply: serde_json::Value = serde_json::from_str(&body(s, path).await)
        .unwrap_or_else(|error| panic!("{path}: {error}"));
    reply["redirect"]
        .as_str()
        .unwrap_or_else(|| panic!("{path}: no redirect in {reply}"))
        .to_owned()
}

/// The session of one user on one lemma: every response body, labelled, with
/// the clock and the lines that name the algebra engine removed.
async fn session(s: &TestServer, lemma: &str) -> Vec<(&'static str, String)> {
    let mut seen = Vec::new();
    seen.push(("root", body(s, "/").await));
    seen.push(("theory page", body(s, "/thy/trace/1/overview/help").await));
    seen.push(("rules", body(s, "/thy/trace/1/main/rules").await));
    seen.push((
        "open lemma",
        body(s, &format!("/thy/trace/1/main/proof/{lemma}")).await,
    ));

    // One manual step: the first applicable method at the lemma's root.
    let stepped = redirect(s, &format!("/thy/trace/1/main/method/{lemma}/1")).await;
    assert!(stepped.starts_with("/thy/trace/2/overview/"), "{stepped}");
    seen.push(("manual step", stepped.clone()));
    seen.push(("state after step", body(s, &stepped).await));
    let pane = stepped.replacen("/overview/", "/main/", 1);
    seen.push(("pane after step", body(s, &pane).await));

    // Autoprove the rest from that state.
    let auto = stepped.replacen("/overview/", "/autoprove/idfs/0/False/", 1);
    let proved = redirect(s, &auto).await;
    assert!(proved.starts_with("/thy/trace/3/overview/"), "{proved}");
    seen.push(("autoprove", proved));
    seen.push((
        "proved overview",
        body(s, &format!("/thy/trace/3/overview/proof/{lemma}")).await,
    ));
    seen.push((
        "proved pane",
        body(s, &format!("/thy/trace/3/main/proof/{lemma}")).await,
    ));
    seen.push((
        "proved theory",
        body(s, "/thy/trace/3/download/proved.spthy").await,
    ));

    // Every lemma of the untouched theory.
    let all = redirect(
        s,
        &format!("/thy/trace/1/autoproveAll/idfs/0/proof/{lemma}"),
    )
    .await;
    assert!(all.starts_with("/thy/trace/4/overview/"), "{all}");
    seen.push((
        "all proved",
        body(s, "/thy/trace/4/download/all.spthy").await,
    ));

    seen.into_iter()
        .map(|(label, text)| {
            let text = blank_times(&text)
                .lines()
                .filter(|line| !line.starts_with("Maude version "))
                .filter(|line| !line.contains("processing time"))
                .map(|line| format!("{line}\n"))
                .collect();
            (label, text)
        })
        .collect()
}

/// Drop the index of every variable (`x.2`, `#vk.7`). Where a unification is
/// left to the AC engine, the proved unifier may number its witnesses
/// differently from Maude, which renumbers variables and changes nothing
/// else; batch output differs in the same way.
fn without_indices(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let named = i > 0 && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
        if bytes[i] == b'.' && named && bytes.get(i + 1).is_some_and(u8::is_ascii_digit) {
            i += 1;
            while bytes.get(i).is_some_and(u8::is_ascii_digit) {
                i += 1;
            }
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).expect("only ASCII bytes were removed")
}

/// Every lemma's verdict as the downloaded theory states it.
fn proved_lemmas(theory: &str) -> usize {
    theory.matches("\nqed").count() + theory.matches("\nSOLVED").count()
}

async fn compare_backends(theory: &str, lemma: &str, exact: bool) {
    if !native_backend_is_built() {
        return;
    }
    let native = session(&server(theory, AlgebraBackend::ProvedOnly).await, lemma).await;
    let finished = &native.last().expect("responses").1;
    assert!(proved_lemmas(finished) > 0, "{finished}");
    assert!(!finished.contains("by sorry"), "{finished}");

    if !maude_available() {
        return;
    }
    let maude = session(&server(theory, AlgebraBackend::Maude).await, lemma).await;
    assert_eq!(native.len(), maude.len());
    for ((label, native), (_, maude)) in native.iter().zip(&maude) {
        if exact {
            assert_eq!(native, maude, "{label}");
        } else {
            assert_eq!(without_indices(native), without_indices(maude), "{label}");
        }
    }
}

/// Diffie-Hellman: the two backends answer every request byte for byte.
#[tokio::test(flavor = "multi_thread")]
async fn native_session_on_a_diffie_hellman_theory_matches_maude() {
    compare_backends(
        &corpus_theory("cav13/DH_example.spthy"),
        "Accept_Secret",
        true,
    )
    .await;
}

/// XOR: the same proofs up to the numbering of variables.
#[tokio::test(flavor = "multi_thread")]
async fn native_session_on_an_xor_theory_matches_maude_up_to_numbering() {
    compare_backends(&corpus_theory("features/xor/CRxor.spthy"), "alive", false).await;
}

/// Requests that arrive together run on separate blocking threads, each of
/// which initialises its own Lean thread state. Every one must answer, and
/// each must answer what the same request answers alone.
#[tokio::test(flavor = "multi_thread")]
async fn concurrent_native_requests_each_complete() {
    if !native_backend_is_built() {
        return;
    }
    let theory = corpus_theory("features/xor/CRxor.spthy");
    let s = server(&theory, AlgebraBackend::ProvedOnly).await;
    let lemmas = ["alive", "recentalive_tag", "executable"];
    let paths: Vec<String> = lemmas
        .iter()
        .flat_map(|lemma| {
            [
                format!("/thy/trace/1/main/proof/{lemma}"),
                format!("/thy/trace/1/autoprove/idfs/0/False/proof/{lemma}"),
            ]
        })
        .collect();
    let together = futures_all(paths.iter().map(|path| body(&s, path))).await;
    for (path, reply) in paths.iter().zip(&together) {
        if path.contains("/autoprove/") {
            assert!(reply.contains("\"redirect\""), "{path}: {reply}");
        } else {
            assert_eq!(reply, &body(&s, path).await, "{path}");
        }
    }
    // Each autoprove published its own snapshot with a finished proof.
    for index in 2..=4 {
        let proved = body(&s, &format!("/thy/trace/{index}/download/t.spthy")).await;
        assert!(proved_lemmas(&proved) > 0, "{proved}");
    }
}

/// Poll a set of futures on this task until all are done.
async fn futures_all<F: std::future::Future<Output = String>>(
    futures: impl Iterator<Item = F>,
) -> Vec<String> {
    let mut pending: Vec<_> = futures.map(|future| Box::pin(future)).collect();
    let mut done: Vec<Option<String>> = pending.iter().map(|_| None).collect();
    std::future::poll_fn(|cx| {
        for (slot, future) in done.iter_mut().zip(&mut pending) {
            if slot.is_none()
                && let std::task::Poll::Ready(value) = future.as_mut().poll(cx)
            {
                *slot = Some(value);
            }
        }
        if done.iter().all(Option::is_some) {
            std::task::Poll::Ready(())
        } else {
            std::task::Poll::Pending
        }
    })
    .await;
    done.into_iter().map(Option::unwrap).collect()
}

/// A theory whose rewrite table the certifier does not accept still loads
/// and proves under the author's convergence premise, as it does in batch
/// mode; a raw session would refuse the table.
#[tokio::test(flavor = "multi_thread")]
async fn native_session_proves_under_uncertified_user_equations() {
    if !native_backend_is_built() {
        return;
    }
    let theory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tamarin-prover/tests/fixtures/native_user_equations_pairing.spthy")
        .canonicalize()
        .expect("prover fixture");
    let s = server(&theory.display().to_string(), AlgebraBackend::ProvedOnly).await;
    let all = redirect(&s, "/thy/trace/1/autoproveAll/idfs/0/proof/specialized").await;
    assert!(all.starts_with("/thy/trace/2/overview/"), "{all}");
    let proved = body(&s, "/thy/trace/2/download/all.spthy").await;
    assert_eq!(proved.matches("\nSOLVED").count(), 2, "{proved}");
}

/// Without the Lean library a proved-only server refuses to load a theory
/// instead of answering from a best-effort session.
#[test]
fn proved_only_needs_the_lean_library() {
    if native_backend_is_built() {
        return;
    }
    let cfg = {
        let mut cfg = tamarin_server::ServerConfig::new(
            "127.0.0.1:0".parse().unwrap(),
            None,
            "/nonexistent/maude".to_string(),
        );
        cfg.algebra_backend = AlgebraBackend::ProvedOnly;
        cfg
    };
    let loaded = tamarin_server::theory_io::load_from_path(&fixture_path("issue193.spthy"), &cfg);
    let error = loaded
        .err()
        .expect("proved-only load without Lean")
        .to_string();
    assert!(error.contains("lean-unification"), "{error}");
}
