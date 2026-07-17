//! `web-clean` — a clean-room reimplementation of the response bodies produced
//! by the tamarin-prover interactive web UI.
//!
//! This crate reproduces the *web layer's* output: the URL route grammar, the
//! JSON response envelopes, and the HTML/DOT/text page templates. Content that
//! the prover produces (pretty-printed terms, constraint systems, proof-method
//! names, graph bodies) is treated as opaque input supplied by the caller — the
//! crate reproduces the scaffolding, escaping, links and envelopes around it.
//!
//! Everything here was derived from black-box observation of captured responses
//! and live probing; see `workspace/BEHAVIOR.md` for the observed spec.
//!
//! Module map:
//! * [`route`] — parse a request path into a structured route (the grammar).
//! * [`envelope`] — the two JSON response shapes (`{html,title}`, `{redirect}`).
//! * [`escape`] — HTML entity escaping.
//! * [`page`] — the full theory-view HTML shell (the `overview/*` pages).
//! * [`proofscript`] — the proof-script (west) pane and proof-tree line grammar.
//! * [`forms`] — the edit / delete / add-lemma form bodies.
//! * [`intdot`] — the `intdot` mini-page and empty-graph DOT skeleton.
//! * [`text`] — the plain-text bodies (`source`/`message`, `next`/`prev`).
//! * [`errors`] — the 404 Not Found page.

pub mod envelope;
pub mod errors;
pub mod escape;
pub mod forms;
pub mod intdot;
pub mod page;
pub mod proofscript;
pub mod route;
pub mod text;

mod notfound_template;
mod shell_template;
