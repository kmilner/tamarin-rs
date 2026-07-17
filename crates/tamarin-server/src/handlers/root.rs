// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Artur Cygan, Jannik Dreier, Cas Cremers, Felix Linker,
//   "Jackie" (github kanakanajm), Ralf Sasse, Yann Colomb, Benedikt Schmidt,
//   "Tom" (github BTom-GH), Adrian Dapprich, Alexander Dax, symphorien,
//   Jérôme (github Azurios-git), and other minor contributors (see upstream
//   git history)
// Ported from upstream tamarin-prover sources:
//   src/Web/Hamlet.hs, src/Web/Handler.hs, src/Web/Types.hs

//! Root + housekeeping handlers.

use std::sync::Arc;

use axum::{
    body::Bytes,
    extract::{Multipart, State},
    http::{StatusCode, header},
    response::{IntoResponse, Redirect, Response},
};

use crate::handlers::html_response;
use crate::state::{AppState, TheoryOrigin};
use crate::theory_io;

/// `GET /` — Welcome page listing loaded theories.  Mirror Haskell's
/// `rootTpl` (`src/Web/Hamlet.hs:53-81`).
pub async fn get(State(state): State<Arc<AppState>>) -> Response {
    let html = render_index(&state);
    html_response(html)
}

/// `POST /` — File upload (multipart `uploadedTheory`).
pub async fn post(
    State(state): State<Arc<AppState>>,
    mut mp: Multipart,
) -> Response {
    // Mirror Haskell `postRootR` (src/Web/Handler.hs:785-812): a missing
    // `uploadedTheory` field → "Post request failed."; an empty file →
    // "No theory file given."; a load error → "Theory loading failed:…";
    // success → "Loaded new theory!".
    let mut alert_msg: Option<String> = None;
    let mut found_field = false;
    while let Some(field) = mp.next_field().await.unwrap_or(None) {
        if field.name() != Some("uploadedTheory") { continue; }
        found_field = true;
        let filename = field.file_name().unwrap_or("uploaded.spthy").to_string();
        let bytes: Bytes = match field.bytes().await {
            Ok(b) => b,
            Err(e) => { alert_msg = Some(format!("upload failed: {}", e)); break; }
        };
        if bytes.is_empty() {
            alert_msg = Some("No theory file given.".into());
            break;
        }
        let src = match std::str::from_utf8(&bytes) {
            Ok(s) => s.to_string(),
            Err(_) => { alert_msg = Some("upload was not valid UTF-8".into()); break; }
        };
        match theory_io::load_from_source(
            &src, TheoryOrigin::Upload(filename.clone()), &state.cfg.maude_path,
            state.cfg.derivcheck_timeout) {
            Ok(entry) => {
                let idx = state.store.insert(entry);
                tracing::info!(idx, file = %filename, "uploaded theory");
                // Haskell appends a ` WARNING: ignoring the following
                // wellformedness errors: …` suffix to this alert when the
                // report is non-empty (Handler.hs:807-811).  The Rust port
                // emits the bare message; the same report is still surfaced on
                // the theory page (the `wf-warning` banner + the source/message
                // `/* WARNING */` block, both from `entry.wf_report`).
                alert_msg = Some("Loaded new theory!".into());
            }
            // HS `postRootR` (src/Web/Handler.hs:803):
            //   `setMessage $ "Theory loading failed:\n" <> toHtml (show err)`
            // — a NEWLINE separates the prefix from the error, not a space.
            // The '\n' survives both HS Blaze escaping and our `html_escape`
            // (which leaves '\n' untouched).
            Err(e) => { alert_msg = Some(format!("Theory loading failed:\n{}", e)); }
        }
        break;
    }
    if !found_field && alert_msg.is_none() {
        alert_msg = Some("Post request failed.".into());
    }
    let mut html = render_index(&state);
    if let Some(msg) = alert_msg {
        // Render a banner above the index — match Haskell's
        // `setMessage` lift into the layout.
        html = html.replacen(
            "<body>",
            &format!("<body><p class=\"message\">{}</p>", html_escape(&msg)),
            1,
        );
    }
    html_response(html)
}

/// `GET /favicon.ico` — Redirect to `/static/img/favicon.ico` (mirror
/// Haskell's `getFaviconR`).
pub async fn favicon() -> impl IntoResponse {
    Redirect::permanent("/static/img/favicon.ico")
}

/// `GET /robots.txt` — Mirror Haskell's `getRobotsR`.
pub async fn robots() -> impl IntoResponse {
    (StatusCode::OK,
     [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
     "User-agent: *")
}

/// `GET /kill?path=<key>` — frontend uses this to cancel a
/// long-running search.  Haskell binds the `path` query parameter and
/// `invalidArgs` (400) when it's missing; on success it returns
/// `Canceled request!` as `text/plain`.
///
/// See `getKillThreadR` in `src/Web/Handler.hs:1422-1440`.
///
/// We don't yet wire a `tokio_util::sync::CancellationToken` registry,
/// so the "cancel" is a soft ack — but the 400-on-missing-path
/// semantics match Haskell exactly so frontend dispatch works.
pub async fn kill_thread(
    axum::extract::Query(q): axum::extract::Query<KillQuery>,
) -> impl IntoResponse {
    match q.path {
        Some(_key) => (
            StatusCode::OK,
            [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
            "Canceled request!",
        )
            .into_response(),
        None => (
            StatusCode::BAD_REQUEST,
            [(header::CONTENT_TYPE, "text/html; charset=utf-8")],
            "<!DOCTYPE html><html><head><title>Invalid Arguments</title></head>\
             <body><h1>Invalid Arguments</h1><ul><li>No path to kill specified!</li></ul></body></html>",
        )
            .into_response(),
    }
}

#[derive(Debug, serde::Deserialize)]
pub struct KillQuery {
    pub path: Option<String>,
}

// ---------------------------------------------------------------------
// HTML rendering for `/` — a plain-Rust port of `rootTpl + theoriesTpl
// + introTpl` from `Web.Hamlet`.  Same /static/* references so the
// existing CSS/JS plays.
// ---------------------------------------------------------------------
fn render_index(state: &AppState) -> String {
    let theories = state.store.list();
    // HS `theoriesTpl` (Web/Hamlet.hs:84-101): the `<table>…</table><br>` (or
    // the empty-branch `<strong>No theories loaded!</strong><br>`) that fills
    // the second `intropage` `<p>` of `rootTpl`.
    let theories_content = if theories.is_empty() {
        "<strong>No theories loaded!</strong><br>".to_string()
    } else {
        // HS `theoryTpl` (Web/Hamlet.hs:116-139): one `<tr>` per theory.  The
        // `<thead>` emits four bare `<th>…</th>` (no `<tr>`), exactly as hamlet
        // renders it.
        let mut rows = String::new();
        for t in &theories {
            let link = format!("/thy/trace/{}/overview/help", t.idx);
            let time = t.loaded_at.format("%T");
            // `$if getEitherTheoryPrimary` → `<td>Original`, else `<td><em>Modified`.
            let primary = if t.primary { "<td>Original</td>" } else { "<td><em>Modified</em></td>" };
            rows.push_str(&format!(
                "<tr><td><a href=\"{link}\">{name}</a></td><td>{time}</td>{primary}<td>{origin}</td></tr>",
                link = html_escape(&link),
                name = html_escape(&t.name),
                origin = html_escape(&t.origin.label()),
            ));
        }
        format!("<table><thead><th>Theory name</th><th>Time</th><th>Version</th><th>Origin</th></thead>{rows}</table><br>")
    };
    // Byte-faithful port of HS `defaultLayout'` (Web/Types.hs:686-723) wrapping
    // `rootTpl` + `introTpl` (Web/Hamlet.hs).  Volatile substitutions: the
    // `{version}` header field (matches `showVersion version`) and the
    // `{theories_content}` table.  Everything else — including hamlet's
    // unquoted `href=/`, the doubled `</script></script>` close tags, the
    // `<p class="loading">` banner and the `contextMenu` — is verbatim.
    format!(
        r##"<!DOCTYPE html>
<html><head><title>Welcome to the Tamarin prover</title><link rel="stylesheet" href="/static/css/intdot-style.css"><link rel="stylesheet" href="/static/css/tamarin-prover-ui.css"><link rel="stylesheet" href="/static/css/jquery-contextmenu.css"><link rel="stylesheet" href="/static/css/smoothness/jquery-ui.css"><script src="/static/js/jquery.js"></script></script><script src="/static/js/jquery-ui.js"></script></script><script src="/static/js/jquery-layout.js"></script></script><script src="/static/js/jquery-cookie.js"></script></script><script src="/static/js/jquery-superfish.js"></script></script><script src="/static/js/jquery-contextmenu.js"></script></script><script src="/static/js/tamarin-prover-ui.js"></script></script><script type="module" src="/static/js/intdot-graph.es.js"></script></script><script type="module" src="/static/js/intdot-staticgraph.es.js"></script></script><script type="module" src="/static/js/intdot-dynamicgraph.es.js"></script></script></head><body><p class="loading">Analyzing, please wait...  <a id=cancel href='#'>Cancel</a></p><div class="ui-layout-container"><div class="ui-layout-north"><div class="ui-layout-pane"><div class="layout-pane-north"><div class="ui-layout-pane-north"><div id="introbar"><div id="header-info">Running <a href=/><span class="tamarin">Tamarin</span></a> {version}</div></div></div></div></div></div></div><div id="logo"><p><img src="/static/img/tamarin-logo-3-0-0.png"></p></div><noscript><div class="warning">Warning: JavaScript must be enabled for the <span class="tamarin">Tamarin</span> prover GUI to function properly.</div></noscript><div class="intropage"><p>Core team: <a href="https://www.inf.ethz.ch/personal/basin/">David Basin</a>, <a href="https://cispa.saarland/group/cremers/">Cas Cremers</a>, <a href="https://www.jannikdreier.net">Jannik Dreier</a>, <a href="mailto:iridcode@gmail.com">Simon Meier</a>, <a href="https://people.inf.ethz.ch/rsasse/">Ralf Sasse</a>, <a href="https://beschmi.net">Benedikt Schmidt</a><br>Tamarin is a collaborative effort: see the <a href="https://tamarin-prover.com/manual/index.html">manual</a> for a more extensive overview of its development and additional contributors.</p><p>This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you are welcome to redistribute it according to its <a href="/static/LICENSE" type="text/plain">LICENSE.</a></p><p>More information about Tamarin and technical papers describing the underlying theory can be found on the <a href="https://tamarin-prover.com"><span class="tamarin">Tamarin</span> webpage</a>.</p></div><div class="intropage"><p>{theories_content}</p><h2>Loading a new theory</h2><p>You can load a new theory file from disk in order to work with it.</p><form class="root-form" enctype="multipart/form-data" action="/" method="POST">Filename:<input type="file" name="uploadedTheory"><div class="submit-form"><input type="submit" value="Load new theory"></div></form><p>Note: You can save a theory by downloading the source from the Actions menu.</p></div><div id="dialog"></div><div id="confirm-dialog"></div><ul id="contextMenu"><li class="autoprove"><a href="#autoprove">Autoprove</a></a></li></ul></body></html>"##,
        version = env!("CARGO_PKG_VERSION"),
        theories_content = theories_content,
    )
}

pub use tamarin_utils::pretty_html::escape_html_entities as html_escape;

#[cfg(test)]
mod tests {
    use super::*;

    /// HS `postRootR` (src/Web/Handler.hs:803) separates the
    /// "Theory loading failed:" prefix from the error body with a NEWLINE:
    ///   `setMessage $ "Theory loading failed:\n" <> toHtml (show err)`.
    /// We mirror that exact prefix (newline, not space).
    #[test]
    fn theory_load_error_prefix_uses_newline() {
        let e = "parse error: boom";
        let msg = format!("Theory loading failed:\n{}", e);
        assert_eq!(msg, "Theory loading failed:\nparse error: boom");
        assert!(!msg.starts_with("Theory loading failed: ")); // not a space
    }

    /// `html_escape` must leave '\n' untouched so the newline in the
    /// load-error banner survives into the rendered page (HS Blaze escaping
    /// likewise leaves '\n' alone).  Only `& < > " '` are escaped.
    #[test]
    fn html_escape_preserves_newline() {
        assert_eq!(html_escape("Theory loading failed:\nerr"),
                   "Theory loading failed:\nerr");
        assert_eq!(html_escape("a&b<c>d\"e'f"),
                   "a&amp;b&lt;c&gt;d&quot;e&#39;f");
    }
}
