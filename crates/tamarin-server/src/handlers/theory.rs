// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Per-theory HTTP handlers.  Each one looks up the theory by idx,
//! parses the trailing wildcard path, and emits HTML or the JSON
//! envelope the frontend expects.

// the `HashMap<String, String>` here are
// query-parameter maps (axum `Query` extractors + a keyed graph-options
// lookup), consumed by key only — never iterated into output — and off the
// batch `--prove` byte-parity surface (server UI only).  std kept: axum's
// `Query<HashMap<..>>` requires the std type.
#![allow(clippy::disallowed_types)]

use std::sync::Arc;

use axum::{
    extract::{Path, Query, State},
    http::{header, HeaderMap, StatusCode},
    response::{IntoResponse, Response},
};
use serde_json::Value;
use std::collections::HashMap;

use crate::handlers::{
    html_response, intdot_shell_html, internal_server_error, json_resp, path_parse, text_response,
    theory_html,
};
use crate::state::AppState;

use tamarin_theory::constraint::solver::search::NodeStatus;
use tamarin_theory::constraint::system::graph::{GraphOptions, SimplificationLevel};

// ---------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------

/// Parse the trailing wildcard path.  Returns `None` on UNPARSEABLE
/// input, mirroring Haskell's Yesod `PathMultiPiece TheoryPath`
/// instance (`fromPathMultiPiece = parseTheoryPath`,
/// `src/Web/Types.hs:662-665`): when `parseTheoryPath` returns
/// `Nothing`, Yesod routing yields `notFound` (404) BEFORE the handler
/// runs, so a malformed path 404s on every theory route.  Callers must
/// map `None` to [`not_found`].  Note the legitimate help view
/// (`/help`) parses to `TheoryPath::Help`, so it is NOT affected.
fn parse_path(raw: &str) -> Option<path_parse::TheoryPath> {
    path_parse::parse(raw)
}

/// Haskell's `notFound`: the miss itself.  Every one of them — an unknown
/// theory index as much as a theory path that does not resolve — carries the
/// same page, which the `not_found_page` layer in [`crate::routes`] renders
/// from the request path (see [`crate::handlers::not_found_response`]).
fn not_found() -> Response {
    StatusCode::NOT_FOUND.into_response()
}

/// A theory looked up from the store, with its user-declared function-symbol
/// sets installed on the request thread for as long as the value is held.
///
/// HS resolves a declared `[AC]` / nullary / unary symbol at PARSE time, so its
/// terms are born resolved; the port resolves them through thread-locals, which
/// start empty on every axum worker (see
/// [`TheoryEntry::install_user_funs`](crate::state::TheoryEntry::install_user_funs)).
/// Binding the sets to the looked-up theory makes that a property of the
/// handler boundary rather than of each renderer remembering: a handler cannot
/// hold the entry without them.  Renderers that install again nest harmlessly —
/// the guards restore in reverse order and each installs the same sets.
///
/// Not held across an `.await`: the sets belong to the thread, and a suspended
/// task can resume on another one.
struct LoadedTheory {
    entry: crate::state::TheoryEntry,
    _user_funs: tamarin_theory::elaborate::UserFunsForTheoryGuard,
}

impl std::ops::Deref for LoadedTheory {
    type Target = crate::state::TheoryEntry;

    fn deref(&self) -> &Self::Target {
        &self.entry
    }
}

/// The theory at `idx` with its user-fn sets installed (see [`LoadedTheory`]),
/// or `None` for an index naming no theory — HS `withTheory`'s `notFound`
/// (`src/Web/Handler.hs:662-672`).
fn load_theory(state: &AppState, idx: usize) -> Option<LoadedTheory> {
    let entry = state.store.get(idx)?;
    let user_funs = entry.install_user_funs();
    Some(LoadedTheory {
        entry,
        _user_funs: user_funs,
    })
}

// ---------------------------------------------------------------------
// Overview / main view
// ---------------------------------------------------------------------

/// `GET /thy/trace/<idx>/overview/*path` — full framed page.
pub async fn interactive_overview(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    if !state.store.contains(idx) {
        return not_found();
    }
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // The full framed page ALWAYS renders the left-pane proof-state tree
    // (`proof_state`), whose rule count (incl. the ISend/IRecv intruder
    // members of `crProtocol`) and raw/refined source-case annotations come
    // from the closed-theory `ProofContext`.  HS has these at theory-close
    // time for every page; RS builds the context lazily, so we must ensure it
    // here regardless of the center path — otherwise a frame whose center
    // needs no proof state (help/edit/add/delete) would show `(0 cases)` and a
    // proto-only rule count.  Best-effort: a Maude failure leaves the counts
    // as-is.
    let _ = state.store.ensure_proof_state(idx, &state.cfg);
    let Some(entry) = load_theory(&state, idx) else {
        return not_found();
    };
    html_response(theory_html::overview_page(&entry, &path))
}

/// `GET /thy/trace/<idx>/main/*path` — AJAX-only JsonHtml content
/// (no framing).  Missing idx returns 404 HTML to match Haskell's
/// `withTheory` / `notFound` (see `src/Web/Handler.hs:662-672`).
///
/// Special-cases the `TheoryMethod` path (Haskell `getTheoryPathMR` →
/// `applyMethodAtPath`): we look up the ranked applicable methods at
/// the indicated proof node, apply the requested one, allocate a fresh
/// theory idx for the post-step state, and return a `{redirect}` JSON
/// envelope pointing at `/thy/trace/<newIdx>/overview/proof/...`.
pub async fn theory_path_main(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    if !state.store.contains(idx) {
        return not_found();
    }
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // Method paths mutate the proof tree; dispatch separately.
    if let path_parse::TheoryPath::Method {
        lemma,
        idx: method_nr,
        sub,
    } = &path
    {
        return apply_method_and_redirect(&state, idx, lemma, *method_nr, sub).into_response();
    }
    materialise_proof_state_if_needed(&state, idx, &path);
    let Some(entry) = load_theory(&state, idx) else {
        return not_found();
    };
    let title = title_for(&entry, &path);
    let body = theory_html::path_html(&entry, &path);
    json_resp::html(title, body).into_response()
}

/// Build the `overview/proof` redirect URL for lemma `lemma` at proof
/// path `sub` under theory `idx`.  Percent-encodes the lemma segment
/// and each sub segment via the shared `path_parse` helpers, matching
/// Yesod `getUrlRender`.  `sub == &[]` yields the bare
/// `.../overview/proof/<lemma>` root URL (`encode_sub_path(&[]) == ""`).
fn overview_proof_url(idx: usize, lemma: &str, sub: &[String]) -> String {
    let mut u = format!(
        "/thy/trace/{}/overview/proof/{}",
        idx,
        path_parse::url_path_escape(lemma)
    );
    u.push_str(&path_parse::encode_sub_path(sub));
    u
}

/// Apply ranked method `method_nr` (1-based) at proof path `sub` in
/// lemma `lemma`'s tree.  Allocates a fresh idx for the post-step
/// state and returns a JsonRedirect pointing at the resulting
/// `overview/proof/<lemma>/<sub>` URL.  Mirrors Haskell's
/// `applyMethodAtPath` + `modifyTheory` flow in
/// `src/Web/Handler.hs:1078-1081` and `src/Web/Theory.hs:86-100`.
fn apply_method_and_redirect(
    state: &AppState,
    idx: usize,
    lemma: &str,
    method_nr: i64,
    sub: &[String],
) -> axum::Json<Value> {
    // Ensure the proof state at the *source* idx is built (so we can
    // navigate to the sub-path and rank candidate methods there).
    let src_ps = match state.store.ensure_proof_state(idx, &state.cfg) {
        Ok(p) => p,
        Err(e) => return json_resp::alert(format!("proof state init failed: {}", e)),
    };
    // Look up the system at the requested path.
    let sys_at_path = match src_ps.get_system_at(lemma, sub) {
        Some(s) => s,
        None => return json_resp::alert(format!("no system at path {:?} in lemma {}", sub, lemma)),
    };
    // Pick the N-th ranked method (1-based).  Filter to only those
    // methods whose `exec_proof_method` succeeds — matches Haskell's
    // `rankProofMethods` → `execMethods` (`ProofMethod.hs:519-534`)
    // semantics, and matches the user-visible numbering produced by
    // `write_applicable_methods` (which applies the same filter).
    // Without filtering here the numbering would drift on Sorry/no-op
    // candidates that the UI omits.
    let method = {
        // `exec_proof_method` below resolves user fun symbols via
        // thread-locals — install them (tokio workers start empty; see
        // `ProofState::user_funs`).
        let _user_funs_guard = src_ps.install_user_funs();
        let mut ctx_guard = src_ps.ctx.lock();
        // Install this lemma's per-lemma `use_induction`/`heuristic` into the
        // shared ctx BEFORE ranking, so the method-index → method mapping
        // matches HS (and the numbering `write_applicable_methods` displays).
        // Without this the mapping ranks under `AvoidInduction`/`Smart`, so a
        // `[use_induction]` lemma's method `1` resolves to the wrong method.
        src_ps.install_lemma_settings(&mut ctx_guard, lemma);
        // Haskell `applyMethodAtPath` ranks with `useHeuristic heuristic
        // (length proofPath)` (Web/Theory.hs:96); the depth selects
        // which ranking of a multi-ranking heuristic is active
        // (`rankings !! (depth mod n)`, ProofMethod.hs:580-589).  Pass
        // the proof-path length, not a hardcoded 0.
        let methods: Vec<_> = tamarin_theory::constraint::solver::search::candidate_methods(
            &sys_at_path,
            &ctx_guard,
            sub.len(),
        )
        .into_iter()
        // WHNF-depth applicability — MUST match the render pane's
        // filter (write_applicable_methods) so the clicked index
        // selects the same method the user saw.
        .filter(|m| {
            tamarin_theory::constraint::solver::proof_method::is_applicable_for_display(
                &ctx_guard,
                m,
                &sys_at_path,
            )
        })
        .collect();
        // The method index is read signed (`safeRead` at `ReadS Int`,
        // `src/Web/Types.hs:443`), so every `i` a client can type reaches
        // here.  Upstream guards it with `length methods >= i` alone and then
        // evaluates `methods !! (i-1)` (`src/Web/Theory.hs:99`), which admits
        // every `i <= 0` into the `!!`: the raised `Prelude.!!` text — GHC
        // CallStack and all — comes back as an ordinary 200 JSON alert, and
        // only an `i` past the end reaches the intended
        // "Sorry, but the prover failed on the selected method!"
        // (`src/Web/Handler.hs:1081`).  RS deliberately corrects that: an
        // index naming no ranked method is one failure, whichever side of the
        // list it falls off, and it always answers that alert.
        match method_nr
            .checked_sub(1)
            .and_then(|nth| usize::try_from(nth).ok())
            .and_then(|nth| methods.into_iter().nth(nth))
        {
            Some(m) => m,
            None => {
                return json_resp::alert("Sorry, but the prover failed on the selected method!")
            }
        }
    };
    // Allocate a fresh theory idx so the post-step state doesn't
    // overwrite the source (matches Haskell's `modifyTheory` →
    // `putTheory` allocating a new idx).  We FORK the source's proof
    // state so the post-step state retains the SAME tree shape as the
    // source (preserving any prior applied steps' children), then
    // apply the step in the fork.  Mirrors Haskell where `putTheory`
    // installs the modified `ClosedTheory` value (which contains its
    // full `IncrementalProof`) at the new idx.
    let new_idx = match state.store.clone_at_new_idx_forking_proof_state(idx) {
        Some(n) => n,
        None => return json_resp::alert(format!("theory index {} not found", idx)),
    };
    let new_ps = match state.store.ensure_proof_state(new_idx, &state.cfg) {
        Ok(p) => p,
        Err(e) => return json_resp::alert(format!("proof state init failed on fresh idx: {}", e)),
    };
    if let Err(e) = new_ps.apply_at_path(lemma, sub, method) {
        return json_resp::alert(format!("proof step failed: {}", e));
    }
    // Build the redirect URL.  Haskell's `getTheoryPathMR` for
    // `TheoryMethod` (`src/Web/Handler.hs:1078-1081`) advances the target
    // via `nextSmartThyPath newThy (TheoryProof lemma proofPath)`, i.e. it
    // walks INTO the freshly created child case of the grown tree.  We do
    // the same: re-fetch the entry at `new_idx` (its `proof_state` Arc is
    // the one `apply_at_path` just grew) and run the shared
    // `next_thy_path_inner` (smart) over it.  For a `TheoryProof` input that
    // arm always yields another `TheoryProof` (child path, next-lemma root,
    // or same path when nothing follows), so we render the `overview/proof`
    // URL from its `(lemma, sub)`.  The URL SHAPE matches Haskell's
    // `renderTheoryPath` (`src/Web/Types.hs:371-384, see line 373`): lemma root (sub=[]) →
    // `proof/<lemma>`; each sub segment is `prefixWithUnderscore`d.
    let Some(new_entry) = state.store.get(new_idx) else {
        return json_resp::alert(format!("theory index {} vanished", new_idx));
    };
    let src_path = path_parse::TheoryPath::Proof {
        lemma: lemma.to_string(),
        sub: sub.to_vec(),
    };
    let (target_lemma, target_sub) = match next_thy_path_inner(&src_path, &new_entry, true) {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma, sub),
        // `nextSmartThyPath` of a `TheoryProof` never leaves the proof arm;
        // fall back to the applied node if that invariant ever breaks.
        _ => (lemma.to_string(), sub.to_vec()),
    };
    let url = overview_proof_url(new_idx, &target_lemma, &target_sub);
    json_resp::redirect(url)
}

/// Build the per-theory `ProofState` when the path is a Proof / Method
/// / Lemma so the renderer can show the initial constraint system +
/// applicable proof methods. Best-effort: silent failure leaves
/// `entry.proof_state = None` (renderer falls back to the static
/// "sorry /* initial */" line).
fn materialise_proof_state_if_needed(state: &AppState, idx: usize, path: &path_parse::TheoryPath) {
    let needs = matches!(
        path,
        path_parse::TheoryPath::Proof { .. }
        | path_parse::TheoryPath::Method { .. }
        | path_parse::TheoryPath::Lemma(_)
        // Message / Rules pages need the closed-theory intruder-rule
        // classification + injective facts; Source pages need the
        // precomputed raw/refined source cases.  All live in the
        // `ProofContext` behind the `ProofState`.
        | path_parse::TheoryPath::Message
        | path_parse::TheoryPath::Rules
        | path_parse::TheoryPath::Source { .. }
    );
    if !needs {
        return;
    }
    let _ = state.store.ensure_proof_state(idx, &state.cfg);
}

/// Mirror Haskell `titleThyPath` (`src/Web/Theory.hs:1679-1700`).
/// Titles are independent of the theory name EXCEPT `TheoryHelp`.
fn title_for(entry: &crate::state::TheoryEntry, path: &path_parse::TheoryPath) -> String {
    use path_parse::SourceKind;
    use path_parse::TheoryPath::*;
    match path {
        // TheoryHelp -> "Theory: " ++ thy._thyName
        Help => format!("Theory: {}", entry.name),
        // TheoryRules -> "Multiset rewriting rules and restrictions"
        Rules => "Multiset rewriting rules and restrictions".to_string(),
        // TheoryMessage -> "Message theory"
        Message => "Message theory".to_string(),
        // TheoryTactic -> "Tactics"
        Tactic => "Tactics".to_string(),
        // TheorySource RawSource _ _ -> "Raw sources"
        Source {
            kind: SourceKind::Raw,
            ..
        } => "Raw sources".to_string(),
        // TheorySource RefinedSource _ _ -> "Refined sources"
        Source {
            kind: SourceKind::Refined,
            ..
        } => "Refined sources".to_string(),
        // TheoryEdit l -> "Edit Lemma: " ++ l
        Edit(l) => format!("Edit Lemma: {}", l),
        // TheoryAdd _ -> "Add new Lemma"  (HS ignores its argument)
        Add(_) => "Add new Lemma".to_string(),
        // TheoryDelete l -> "Delete " ++ l
        Delete(l) => format!("Delete {}", l),
        // TheoryLemma l -> "Lemma: " ++ l
        Lemma(l) => format!("Lemma: {}", l),
        // TheoryProof l [] -> "Lemma: " ++ l
        Proof { lemma, sub } if sub.is_empty() => format!("Lemma: {}", lemma),
        // TheoryProof l p | null (last p) -> "Method: " ++ methodName l p
        //                 | otherwise     -> "Case: " ++ last p
        //
        //   methodName l p = case resolveProofPath thy l p of
        //     Nothing    -> "None"
        //     Just proof -> renderHtmlDoc . prettyProofMethod . psMethod
        //                     . root $ proof
        // i.e. render the proof method stored at the node the path resolves
        // to.  `resolveProofPath` here == `navigate_at` on the live tree;
        // `psMethod . root` == that node's `.method`; `prettyProofMethod`
        // == `method_label`.  (`renderHtmlDoc` wraps operators in `hl_*`
        // spans the parity gate unwraps, so plain `method_label` compares
        // equal.)  Falls back to "None" when the tree/path is unresolvable,
        // exactly as HS's `Nothing` arm does.
        Proof { lemma, sub } => match sub.last() {
            // null (last p): "Method: " ++ methodName l p
            Some(s) if s.is_empty() => {
                let name = entry
                    .proof_state
                    .as_ref()
                    .and_then(|ps| ps.get_root(lemma))
                    .and_then(|root| {
                        crate::handlers::proof_tree::navigate_at(&root, sub).map(|n| {
                            // HS `methodName` = `renderHtmlDoc .
                            // prettyProofMethod` — the HtmlDoc LAYOUT
                            // (100/67, entity fill-widths, col 0): a
                            // long method title WRAPS at the same
                            // positions as HS's (the gate collapses
                            // the newline to a space; the break
                            // position is what must match).
                            let _guard = tamarin_theory::pretty_hpj::HtmlEntityWidthGuard::enable();
                            tamarin_theory::pretty_theory::pretty_proof_method_doc(&n.method)
                                .render_with(
                                    tamarin_theory::pretty_hpj::DEFAULT_LINE_LENGTH,
                                    tamarin_theory::pretty_hpj::DEFAULT_RIBBON,
                                )
                        })
                    })
                    .unwrap_or_else(|| "None".to_string());
                // HS `methodName` = `renderHtmlDoc . prettyProofMethod` and
                // `renderHtmlDoc` (`Text/PrettyPrint/Html.hs:151-153`) escapes HTML
                // entities in every text token via the `Document (HtmlDoc d)`
                // instance (`Text/PrettyPrint/Html.hs:102-105`, whose `char`,
                // `text` and `zeroWidthText` route through
                // `escapeHtmlEntities`, Html.hs:140-149), so a
                // method that mentions a tuple renders `&lt;B, A, …&gt;` in the
                // JSON `title`, not a raw `<…>` (which the semantic canonicalizer
                // would otherwise parse as a bogus HTML element).  Mirror that
                // escaping here; the operator `hl_*` spans / `<br/>` that
                // `renderHtmlDoc` also adds are unwrapped by the parity gate, so
                // entity escaping is the only load-bearing part.
                format!("Method: {}", crate::handlers::root::html_escape(&name))
            }
            // otherwise: "Case: " ++ last p
            Some(s) => format!("Case: {}", s),
            None => unreachable!("sub is non-empty: the [] case is handled above"),
        },
        // TheoryMethod{} -> "Method Path: This title should not be shown. ..."
        Method { .. } => {
            "Method Path: This title should not be shown. Please file a bug".to_string()
        }
    }
}

// ---------------------------------------------------------------------
// Source / message deduction (pretty-printed)
// ---------------------------------------------------------------------

/// Render the full closed-theory source, mirroring HS `getTheorySourceR`
/// and `getTheoryMessageDeductionR` — both are `render . prettyClosedTheory
/// . theory` (`Web/Handler.hs:1015-1022, :1050-1055`), i.e. identical output.
///
/// HS's stored `ClosedTheory` carries each lemma's LIVE
/// `IncrementalProof` — the close-time `checkAndExtendProver`-replayed
/// skeleton at load, updated in place by interactive proof steps — and
/// `prettyClosedTheory` prints it (`prettyIncrementalProof`, incl.
/// `/* unannotated */` markers).  Mirror that by rendering each lemma's
/// proof body from the live [`ProofState`] root via the byte-faithful
/// CLI printer (`pretty_proof_body` — same call the `--prove` output
/// path uses, run.rs).  A lemma with no live root (or no proof state at
/// all, e.g. Maude unavailable) falls back to `by sorry`, which equals
/// the printed form of the fresh `sorry Nothing` root.
///
/// The `Generated from:` version/build lines are placeholders
/// (the interactive server does not carry the CLI build constants — the
/// web-parity gate normalizes them away, as does HS's own `--prove` gate).
/// Wellformedness: the `/* WARNING: ... */` (or `/* All ... successful. */`)
/// block is rendered from the theory's stored `wf_report` — computed at load
/// by the same pipeline `--prove` runs — via the shared `format_wf_block`,
/// so it matches HS byte-for-byte (empty report ⇒ the "all successful" block).
fn render_theory_source(entry: &crate::state::TheoryEntry) -> String {
    // `pretty_closed_theory` AC-canonicalises parser-AST rule/lemma terms,
    // which reads the user-fn thread-locals — empty on an axum worker thread.
    // See `TheoryEntry::install_user_funs`.
    let _user_funs_guard = entry.install_user_funs();
    let build = tamarin_theory::pretty_theory::BuildInfo {
        tamarin_version: env!("CARGO_PKG_VERSION").to_string(),
        maude_version: String::new(),
        git_revision: String::new(),
        git_branch: String::new(),
        compiled_at: String::new(),
    };
    let wf_block = tamarin_theory::pretty_theory::format_wf_block(&entry.wf_report);
    let in_file = entry.origin.label();
    // Live proof bodies (HS `prettyClosedTheory` prints the stored
    // `IncrementalProof` of every lemma; see doc comment above).
    let proved: Vec<tamarin_theory::pretty_theory::ProvedLemma> = match &entry.proof_state {
        Some(ps) => entry
            .typed_theory
            .lemmas()
            .filter_map(|l| {
                ps.get_root(&l.name)
                    .map(|root| tamarin_theory::pretty_theory::ProvedLemma {
                        name: l.name.clone(),
                        proof_body: Some(tamarin_theory::pretty_theory::pretty_proof_body(&root)),
                    })
            })
            .collect(),
        None => Vec::new(),
    };
    let mut body = tamarin_theory::pretty_theory::pretty_closed_theory(
        &entry.parser_theory,
        &entry.typed_theory,
        &proved,
        &wf_block,
        &build,
        &in_file,
        false,
    );
    // `getTheorySourceR` / `getTheoryMessageDeductionR` / `getDownloadTheoryR`
    // are all `render . prettyClosedTheory` (Handler.hs:1015-1022, :1050-1055,
    // :1763-1766), and HughesPJ's `render` ends at the document's last
    // character — the batch path's trailing newline is `putStrLn`'s, not the
    // document's (Batch.hs:114-134, which is why `-o` files are written
    // without it).  `pretty_closed_theory` carries that newline for the
    // stdout caller, so the body served here is one byte shorter.
    if body.ends_with('\n') {
        body.pop();
    }
    // OPEN DIVERGENCE, width: `render` is HughesPJ's DEFAULT style, 100/67
    // (Text/PrettyPrint/Class.hs:77-78), where batch `renderDoc` pins
    // `lineLength = 110` -> ribbon 73 (Console.hs:243, 398-399).
    // `pretty_closed_theory` renders at 110/73 for its stdout caller and takes
    // no width, so these routes serve the wider layout: a group that fits 73
    // but not 67 stays on one line here and wraps upstream.  Visible on
    // `regression/trace/issue193.spthy`, whose captured oracle body is
    // `tests/fixtures/haskell-responses/source.txt`; the web gate's allowlist
    // holds no theory that crosses the boundary, so all 186 of its text rows
    // match.  Closing it means threading a width through the shared renderer,
    // whose acceptance test is the 432-file batch gate.
    body
}

pub async fn source_(State(state): State<Arc<AppState>>, Path(idx): Path<usize>) -> Response {
    // HS renders the CLOSED theory, whose per-lemma proofs exist from
    // theory-close time.  RS materialises the proof state lazily, so
    // ensure it here (best-effort — a Maude failure falls back to the
    // `by sorry` bodies).  Mirrors the framed-page
    // handler's unconditional `ensure_proof_state`.
    let _ = state.store.ensure_proof_state(idx, &state.cfg);
    let Some(entry) = load_theory(&state, idx) else {
        return not_found();
    };
    text_response(render_theory_source(&entry))
}

pub async fn message_deduction(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> Response {
    // See `source_` — identical output, identical proof-state need.
    let _ = state.store.ensure_proof_state(idx, &state.cfg);
    let Some(entry) = load_theory(&state, idx) else {
        return not_found();
    };
    text_response(render_theory_source(&entry))
}

// ---------------------------------------------------------------------
// Autoprove
// ---------------------------------------------------------------------

/// `GET /thy/trace/<idx>/autoprove/<ext>/<bound>/<quit>/*path`
///
/// `extractor` ∈ { characterize, idfs, bfs, seqdfs, sorry }
/// `bound` is the prover bound (0 = unlimited)
/// `quit` is `True`/`False` (Yesod `PathPiece Bool`; capital-cased).
///   The URL extractor on this handler is `String`, so the segment
///   reaches the body, where [`parse_bool_path_piece`] rejects
///   anything else with the 404 Yesod's routing answers before its
///   handler runs.
/// `path`'s first segment is typically `proof/<lemma-name>`.
pub async fn autoprove(
    State(state): State<Arc<AppState>>,
    Path((idx, extractor, bound, quit, raw_path)): Path<(usize, String, usize, String, String)>,
) -> Response {
    // Match Haskell's Yesod `PathPiece SolutionExtractor`
    // (`src/Web/Types.hs:639-651`): only the five known extractor names
    // parse; any other value makes `fromPathPiece` return `Nothing`, so
    // Yesod routing yields `notFound` (404) before the handler runs.
    // `autoprover_name` returns `None` for an unrecognised extractor and
    // otherwise the exact `fullName` Haskell `getAutoProverR` builds.
    let Some(name) = autoprover_name(&extractor, bound) else {
        return not_found();
    };
    // Match Haskell's Yesod `PathPiece Bool`: only "True" / "False"
    // are valid.  Anything else 404s.
    if parse_bool_path_piece(&quit).is_none() {
        return not_found();
    }
    let Some(entry) = state.store.get(idx) else {
        // Haskell: notFound from `withTheory`.  The handler returns
        // JSON in the success branch but 404 HTML when the theory is
        // missing.  We mirror that.
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // Haskell `getProverR` handles ONLY the `TheoryProof lemma proofPath`
    // arm (`src/Web/Handler.hs:1130-1135`); we additionally tolerate
    // Method/Lemma paths (pre-existing leniency — the UI only emits
    // `proof/...` autoprove links), treating them as the lemma root.
    let (lemma_name, sub): (String, Vec<String>) = match &path {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Method { lemma, .. } | path_parse::TheoryPath::Lemma(lemma) => {
            (lemma.clone(), Vec::new())
        }
        // Haskell `getProverR` non-`TheoryProof` arm
        // (`src/Web/Handler.hs:1137-1138`):
        //   JsonAlert $ "Can't run " <> name <> " on the given theory path!"
        _ => {
            return json_resp::alert(format!("Can't run {} on the given theory path!", name))
                .into_response()
        }
    };

    // Use the configured bound, or the URL-provided one when non-zero.
    let max_steps = if bound > 0 {
        bound
    } else {
        state.cfg.max_steps
    };
    // HS `getProverR` → `applyProverAtPath` (`src/Web/Theory.hs:146-149`)
    // → `focus proofPath prover` (`lib/theory/src/Theory/Proof.hs:602-612`):
    // navigate to the URL's proof path, take THAT subproof's root system
    // (`psInfo (root prf)`), run the autoprover from it, and graft the
    // result back at the path via `modifyAtPath` — the rest of the tree is
    // untouched.  Root autoprove is the `focus [] prover = prover` special
    // case.  The prover itself is `runAutoProver` (Web/Handler.hs:1236),
    // which "ignores the existing proof and tries to find one by itself"
    // (Theory/Proof.hs:741-745) — NOT `replaceSorryProver` (that wrapper is
    // batch-`--prove`-only, Main/TheoryLoader.hs:669-711, see line 706).  So any embedded
    // proof skeleton (e.g. Yubikey's `slightly_weaker_invariant` script,
    // replayed into the tree at `ProofState::new` time) is simply REPLACED
    // at the focused path: we search from the path node's stored system via
    // `run_proof_search` and never consult the skeleton.
    let src_ps = match state.store.ensure_proof_state(idx, &state.cfg) {
        Ok(p) => p,
        Err(e) => {
            return json_resp::alert(format!("proof state init failed: {}", e)).into_response()
        }
    };
    let Some(sys_at_path) = src_ps.get_system_at(&lemma_name, &sub) else {
        // Nonexistent lemma or proof path: HS `focus`'s `modifyAtPath`
        // returns `Nothing`, so `modifyTheory` emits the failure alert
        // (`src/Web/Handler.hs:1121-1138, see line 1133`):
        //   JsonAlert $ "Sorry, but " <> name <> " failed!"
        // where `name` is the `fullName` built by `getAutoProverR` from
        // the extractor + bound (see `autoprover_name`).
        return json_resp::alert(format!("Sorry, but {} failed!", name)).into_response();
    };
    // Mirror Haskell `modifyTheory` (`src/Web/Handler.hs:736-753, see line 748`): allocate a
    // fresh theory idx for the post-autoprove state.  Use the FORKING
    // clone so the new idx PRESERVES the source idx's proof trees (HS
    // `modifyTheory` puts the modified `ClosedTheory` — with its full
    // `IncrementalProof` — at the new idx, so proving accumulates and
    // SIBLING branches outside the focused path keep their prior state).
    let new_idx = state
        .store
        .clone_at_new_idx_forking_proof_state(idx)
        .unwrap_or(idx);
    let new_ps = match state.store.ensure_proof_state(new_idx, &state.cfg) {
        Ok(p) => p,
        Err(e) => {
            return json_resp::alert(format!("proof state init failed on fresh idx: {}", e))
                .into_response()
        }
    };

    // Run the search on a blocking thread so we don't block the runtime.
    //
    // The search runs under the lemma's OWN per-lemma `ProofContext`,
    // built by `prove_system_in_session` from the retained
    // `ProverSession` (see `ProofState::session`): HS's prover runs
    // under `getProofContext l thy` — with the `typing_assumptions`-
    // refined source cases gated on `lemmaSourceKind`, per-lemma
    // `is_exists_trace` / heuristic / `use_induction` — NOT under the
    // display-oriented shared web ctx (whose empty `typing_assumptions`
    // made e.g. NSPK3's `nonce_secrecy` search blow up on unrefined
    // KU-chain enumeration).
    let lemma_owned = lemma_name.clone();
    let sub_owned = sub.clone();
    let ps_for_search = new_ps.clone();
    let result = tokio::task::spawn_blocking(move || -> Result<NodeStatus, String> {
        let Some(session) = ps_for_search.session.clone() else {
            return Err("prover session unavailable".to_string());
        };
        let subtree = tamarin_theory::prove::prove_system_in_session(
            &session,
            &lemma_owned,
            sys_at_path,
            max_steps,
        )
        .map_err(|e| format!("prove failed: {}", e))?;
        let status = subtree.status.clone();
        // Graft the search result back at the URL's proof path (HS
        // `focus` → `modifyAtPath`; siblings untouched).
        ps_for_search.graft_at_path(&lemma_owned, &sub_owned, subtree)?;
        Ok(status)
    })
    .await;

    match result {
        Err(join_err) => json_resp::alert(format!("internal error: {}", join_err)).into_response(),
        Ok(Err(_)) => {
            // Prover failure (missing session, prove error) or a graft
            // whose lemma/path vanished between the fork and the graft —
            // surface HS's prover-failure alert
            // (`src/Web/Handler.hs:1121-1138, see line 1133`), same as the bad-path arm above.
            json_resp::alert(format!("Sorry, but {} failed!", name)).into_response()
        }
        Ok(Ok(status)) => {
            tracing::info!(idx, lemma = %lemma_name, ?status, "autoprove completed");
            // Map our internal NodeStatus to Tamarin's per-lemma
            // verdict relative to the lemma's trace-quantifier:
            //
            //   all-traces lemma:
            //     Contradictory  → verified
            //     Solved         → falsified (attack found)
            //
            //   exists-trace lemma:
            //     Solved         → verified (witness found)
            //     Contradictory  → falsified (no witness exists)
            //
            // Sorry / Unfinishable / Open all mean the search did
            // not produce a definitive answer.
            let is_exists = entry
                .typed_theory
                .lookup_lemma(&lemma_name)
                .map(|l| {
                    matches!(
                        l.trace_quantifier,
                        tamarin_theory::theory::TraceQuantifier::ExistsTrace
                    )
                })
                .unwrap_or(false);
            let verdict = match (status.clone(), is_exists) {
                (NodeStatus::Solved, false) => "falsified (attack found)",
                (NodeStatus::Solved, true) => "verified (witness found)",
                (NodeStatus::Contradictory, false) => "verified",
                (NodeStatus::Contradictory, true) => "falsified (no witness exists)",
                (NodeStatus::Unfinishable, _) => "Unfinishable",
                (NodeStatus::Sorry, _) => "Sorry (search exhausted budget)",
                (NodeStatus::Open, _) => "Open (incomplete)",
            };
            tracing::info!("autoprove verdict for {}: {}", lemma_name, verdict);
            // Haskell `getAutoProverR` (`src/Web/Handler.hs`) redirects via
            // `nextSmartThyPath newThy (TheoryProof lemma proofPath)` over the
            // freshly autoproved tree.  For a fully-proved all-traces lemma
            // (no interesting `Sorry`/`Finished Solved`/`Unfinishable` step)
            // that walks to the NEXT lemma's root; for an exists-trace lemma
            // it lands on the `Finished Solved` witness node.  Re-fetch the
            // entry at `new_idx` (its `proof_state` Arc is the fork the
            // grafted tree lives in) and run the shared smart traversal from
            // the proof path the autoprover was invoked at.
            let redir = match state.store.get(new_idx) {
                Some(new_entry) => {
                    let src_path = path_parse::TheoryPath::Proof {
                        lemma: lemma_name.clone(),
                        sub: sub.clone(),
                    };
                    let (tl, ts) = match next_thy_path_inner(&src_path, &new_entry, true) {
                        path_parse::TheoryPath::Proof { lemma, sub } => (lemma, sub),
                        _ => (lemma_name.clone(), Vec::new()),
                    };
                    overview_proof_url(new_idx, &tl, &ts)
                }
                None => overview_proof_url(new_idx, &lemma_name, &[]),
            };
            json_resp::redirect(redir).into_response()
        }
    }
}

/// Yesod `PathPiece Bool` accepts ONLY `True` and `False`
/// (capitalised).  See `instance PathPiece Bool` in `yesod-core`.
/// Returns `None` for any other input.
pub fn parse_bool_path_piece(s: &str) -> Option<bool> {
    match s {
        "True" => Some(true),
        "False" => Some(false),
        _ => None,
    }
}

/// Build the prover display name exactly as Haskell `getAutoProverR` /
/// `getAutoProverAllR` (`src/Web/Handler.hs:1228-1256 / :1259-1283`):
///
/// ```text
/// fullName   = proverName <> " (" <> intercalate ", " qualifiers <> ")"
/// qualifiers = extractorQualifier ++ boundQualifier
/// ```
///
/// `extractor` is the URL `#SolutionExtractor` path piece; Yesod's
/// `instance PathPiece SolutionExtractor` (`src/Web/Types.hs:639-651`)
/// accepts only the five strings below — any other value makes
/// `fromPathPiece` return `Nothing`, which Yesod turns into a routing
/// `notFound` (404) BEFORE the handler runs.  We mirror that by
/// returning `None` here for an unrecognised extractor.
///
/// Note: the displayed name is computed from the RAW extractor, NOT the
/// quit-on-empty–adjusted cut.  HS's `apCut = if quitOnEmpty then
/// CutAfterSorry else extractor` only affects the prover, while
/// `fullName`'s `extractorQualfier` matches on the original `extractor`.
fn autoprover_name(extractor: &str, bound: usize) -> Option<String> {
    let (prover_name, extractor_qual): (&str, &[&str]) = match extractor {
        "characterize" => ("characterization", &["dfs"]),
        "idfs" => ("the autoprover", &[]),
        "bfs" => ("the autoprover", &["bfs"]),
        "seqdfs" => ("the autoprover", &["seqdfs"]),
        "sorry" => ("the autoprover", &["sorry"]),
        _ => return None,
    };
    let mut qualifiers: Vec<String> = extractor_qual.iter().map(|s| s.to_string()).collect();
    if bound > 0 {
        qualifiers.push(format!("bound {}", bound));
    }
    Some(format!("{} ({})", prover_name, qualifiers.join(", ")))
}

/// `GET /thy/trace/<idx>/autoproveAll/<extractor>/<bound>/*path` —
/// run the autoprover on every lemma and return a redirect to the
/// fresh theory idx, matching Haskell `getAutoProverAllR` /
/// `getProverAllR` in `src/Web/Handler.hs:1259-1283 / :1141-1155`.
///
/// HS `getProverAllR` folds the SAME focus mechanism `autoprove` uses,
/// at the root path of every lemma (`src/Web/Handler.hs:1141-1155, see line 1155`):
///
/// ```text
/// proveAll thy = foldM (\tha lemma ->
///     applyProverAtPath tha lemma [] autoProver) thy (names thy)
/// ```
///
/// i.e. `runAutoProver` from each lemma's ROOT system, grafting the
/// result as that lemma's new proof — replacing any embedded proof
/// skeleton wholesale (`runAutoProver` "ignores the existing proof and
/// tries to find one by itself", Theory/Proof.hs:741-745; it is NOT
/// wrapped in `replaceSorryProver`, the batch-`--prove`-only wrapper —
/// Main/TheoryLoader.hs:669-711, see line 706).  We mirror that uniformly with
/// `autoprove`: fork the proof state at a fresh idx (HS `modifyTheory`)
/// and `run_proof_search` + `graft_at_path` at `[]` per lemma.
pub async fn autoprove_all(
    State(state): State<Arc<AppState>>,
    Path((idx, extractor, bound, _raw_path)): Path<(usize, String, usize, String)>,
) -> Response {
    // Match Haskell's Yesod `PathPiece SolutionExtractor`
    // (`src/Web/Types.hs:639-651`): an unrecognised extractor makes
    // `fromPathPiece` return `Nothing`, so Yesod routing 404s before
    // `getAutoProverAllR` runs.  (`getProverAllR` never surfaces the
    // prover `name` to the user — it always redirects — so unlike
    // `autoprove` we only need the validation, not the display name.)
    if autoprover_name(&extractor, bound).is_none() {
        return not_found();
    }
    let Some(entry) = state.store.get(idx) else {
        return not_found();
    };
    let lemma_names: Vec<String> = entry
        .typed_theory
        .lemmas()
        .map(|l| l.name.clone())
        .collect();
    let last_lemma = lemma_names.last().cloned();
    let max_steps = if bound > 0 {
        bound
    } else {
        state.cfg.max_steps
    };

    // Materialise the SOURCE idx's proof state, then fork it at a fresh
    // idx (HS `modifyTheory`; forking preserves prior proof trees — see
    // `autoprove`).  Each lemma is then proved from its root system into
    // the fork.
    if let Err(e) = state.store.ensure_proof_state(idx, &state.cfg) {
        return json_resp::alert(format!("proof state init failed: {}", e)).into_response();
    }
    let new_idx = state
        .store
        .clone_at_new_idx_forking_proof_state(idx)
        .unwrap_or(idx);
    let new_ps = match state.store.ensure_proof_state(new_idx, &state.cfg) {
        Ok(p) => p,
        Err(e) => {
            return json_resp::alert(format!("proof state init failed on fresh idx: {}", e))
                .into_response()
        }
    };
    let ps_for_search = new_ps.clone();
    let lemma_names_owned = lemma_names.clone();
    let _ = tokio::task::spawn_blocking(move || {
        // Per-lemma contexts from the retained session, exactly as
        // `autoprove` (HS runs each fold step under `getProofContext`).
        let Some(session) = ps_for_search.session.clone() else {
            tracing::warn!("autoproveAll: prover session unavailable; leaving trees as-is");
            return;
        };
        for lname in &lemma_names_owned {
            // Root system for this lemma — path `[]` is HS's
            // `focus [] prover = prover`, run on `psInfo (root prf)`.
            // A lemma whose formula failed guarded conversion has no
            // proof-tree entry; skip it best-effort and continue.
            let Some(sys) = ps_for_search.get_system_at(lname, &[]) else {
                continue;
            };
            match tamarin_theory::prove::prove_system_in_session(&session, lname, sys, max_steps) {
                Ok(subtree) => {
                    let _ = ps_for_search.graft_at_path(lname, &[], subtree);
                }
                Err(e) => {
                    // HS's fold would fail the whole `modifyTheory`; we
                    // keep the remaining lemmas best-effort and
                    // continue with the next lemma.
                    tracing::warn!(lemma = %lname, error = %e,
                        "autoproveAll: prove failed; lemma keeps prior tree");
                }
            }
        }
    })
    .await;

    // HS `getProverAllR` (`src/Web/Handler.hs:1141-1155, see line 1150`) advances the target
    // via `nextSmartThyPath thy (TheoryProof (last names) [])` over the
    // NEW theory — the same smart traversal as `autoprove`, seeded at
    // the LAST lemma's root.  Now that the fork holds the freshly
    // proved trees, we can run it faithfully.
    let redir = match (state.store.get(new_idx), last_lemma) {
        (Some(new_entry), Some(last)) => {
            let src_path = path_parse::TheoryPath::Proof {
                lemma: last.clone(),
                sub: Vec::new(),
            };
            let (tl, ts) = match next_thy_path_inner(&src_path, &new_entry, true) {
                path_parse::TheoryPath::Proof { lemma, sub } => (lemma, sub),
                _ => (last, Vec::new()),
            };
            overview_proof_url(new_idx, &tl, &ts)
        }
        // No lemmas at all: nothing to prove or point at.
        (_, None) => format!("/thy/trace/{}/overview/help", new_idx),
        (None, Some(last)) => overview_proof_url(new_idx, &last, &[]),
    };
    json_resp::redirect(redir).into_response()
}

/// `GET /thy/trace/<idx>/verify/*path` — returns:
///   - `{redirect}` when the path is `proof/<lemma>/<sub>`, re-pointing
///     navigation at the SAME idx/path.  NOTE: Haskell's
///     `getTheoryVerifyR` (`src/Web/Handler.hs:839-845`) calls
///     `editProof idx l`, which REBUILDS the lemma's proof via
///     `newProof`/`checkAndExtendProver` and `replaceTheory` before
///     redirecting.  The Rust port does NOT yet rebuild the proof; it
///     only re-emits the redirect URL.
///   - `{html,title}` (help-pane fallback) for everything else,
///     mirroring Haskell's `getTheoryPathMR idx TheoryHelp` in the
///     `_` arm of `getTheoryVerifyR`.
///
/// Reference: `src/Web/Handler.hs:839-847`.
pub async fn verify(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    let Some(entry) = load_theory(&state, idx) else {
        return json_resp::alert(format!("theory index {} not found", idx)).into_response();
    };
    // Unparseable path → routing-level 404 (see `parse_path`).
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    match path {
        // The success branch: re-point navigation at the same idx and
        // redirect.  (Haskell `editProof` → `replaceTheory` rebuilds
        // the proof here; the Rust port only redirects — see the
        // handler doc above.)
        path_parse::TheoryPath::Proof { lemma, sub } => {
            // Re-emit the proof path so navigation stays pointed at the
            // same node.  Mirrors Haskell `JsonRedirect` target
            // `/thy/trace/<idx>/overview/proof/<lemma>/...`, which goes
            // through Yesod `getUrlRender` and so percent-encodes each
            // path segment.  Use the shared helpers, identical to
            // `apply_method_and_redirect` (this file): `url_path_escape`
            // on the lemma, `prefixWithUnderscore` + `url_path_escape`
            // on each sub segment.
            let url = overview_proof_url(idx, &lemma, &sub);
            json_resp::redirect(url).into_response()
        }
        // Help-pane fallback: Haskell falls through to
        // `getTheoryPathMR idx TheoryHelp`, which is the JsonHtml for
        // the help screen.  We piggy-back on `theory_path_main` via a
        // synthesised Help path.
        _ => {
            let help_path = path_parse::TheoryPath::Help;
            let title = format!("Theory: {}", entry.name);
            let body = crate::handlers::theory_html::path_html(&entry, &help_path);
            json_resp::html(title, body).into_response()
        }
    }
}

// ---------------------------------------------------------------------
// Theory management
// ---------------------------------------------------------------------

pub async fn unload(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> impl IntoResponse {
    state.store.remove(idx);
    axum::response::Redirect::to("/")
}

/// `POST /thy/trace/<idx>/reload` — re-read the source `.spthy` from
/// disk and replace the entry at the same idx (mirrors Haskell
/// `postReloadTheoryR` in `src/Web/Handler.hs:443-459` which calls
/// `replaceTheory` — same idx, not a fresh allocation).
pub async fn reload(
    State(state): State<Arc<AppState>>,
    Path(idx): Path<usize>,
) -> axum::Json<Value> {
    let Some(entry) = state.store.get(idx) else {
        // Haskell prefers a JSON alert here (`JsonAlert "Theory not
        // found"`) rather than 404, since `reload` is a POST from a
        // form/button — surfacing through the standard alert UI.
        return json_resp::alert("Theory not found".to_string());
    };
    // Mirror Haskell `checkReloadOrigin` (`src/Web/Handler.hs:391-394`):
    // two distinct JsonAlert strings for the two non-Local origins.
    let path = match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => p.clone(),
        crate::state::TheoryOrigin::Upload(_) => {
            return json_resp::alert("Cannot reload: theory was uploaded (no file path)")
        }
        crate::state::TheoryOrigin::Interactive => {
            return json_resp::alert(
                "Cannot reload: theory was created interactively (no file path)",
            )
        }
    };
    match crate::theory_io::load_from_path(
        &path,
        &state.cfg.maude_path,
        state.cfg.derivcheck_timeout,
    ) {
        Ok(new_entry) => {
            // Replace at the SAME idx — matches Haskell's
            // `replaceTheory` (used by `postReloadTheoryR` and
            // `editProof`).  URLs that referenced this theory stay
            // valid.
            let kept_idx = state.store.replace_at(idx, new_entry).unwrap_or(idx);
            json_resp::redirect(format!("/thy/trace/{}/overview/help", kept_idx))
        }
        Err(e) => match e {
            // HS `reloadTheoryFromFile` (Handler.hs:413-414): a parse failure
            // becomes a JsonAlert
            //   "Parse error while reloading file:\n\n" ++ filePath
            //     ++ "\n\n" ++ show e
            // where `show e` is the parsec frame (already headed by the path).
            crate::theory_io::LoadError::Parse(frame) => json_resp::alert(format!(
                "Parse error while reloading file:\n\n{}\n\n{}",
                path.display(),
                frame,
            )),
            other => json_resp::alert(format!("reload failed: {}", other)),
        },
    }
}

pub async fn download(
    State(state): State<Arc<AppState>>,
    Path((idx, name)): Path<(usize, String)>,
) -> Response {
    // Haskell uses `application/octet-stream` to force the browser to
    // present a "Save As" dialog rather than render inline.  See
    // `getDownloadTheoryR` (`src/Web/Handler.hs:1763-1766`) — it
    // returns `(typeOctet, source)` where `source` is the RENDERED
    // in-memory theory (`render . prettyClosedTheory`, via
    // `getTheorySourceR`, `src/Web/Handler.hs:1015-1022`), so interactive
    // modifications (applied proof steps, autoprove results) are
    // reflected in the saved file.  Same body as the `source_` handler,
    // different content-type/disposition.
    let _ = state.store.ensure_proof_state(idx, &state.cfg);
    let Some(entry) = load_theory(&state, idx) else {
        return not_found();
    };
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static("application/octet-stream"),
    );
    // `name` is a client-supplied, percent-DECODED path segment, so it can hold
    // bytes no header value may carry (a newline, say).  Such a name simply
    // gets no disposition header rather than panicking the worker; every name
    // a header can represent is spliced exactly as before.
    if let Ok(disposition) = format!("attachment; filename=\"{name}\"").parse() {
        headers.insert(header::CONTENT_DISPOSITION, disposition);
    }
    (StatusCode::OK, headers, render_theory_source(&entry)).into_response()
}

// ---------------------------------------------------------------------
// Stubs (501) for features not yet ported.
// ---------------------------------------------------------------------

fn stub_alert(what: &str) -> axum::Json<Value> {
    json_resp::alert(format!(
        "{} is not yet implemented in the Rust port (frontend stub)",
        what
    ))
}

/// `GET /thy/trace/<idx>/next/<section>/*path` —
/// Compute the next theory-path under `section ∈ { normal, smart }`
/// and return its `/main/...` URL as `text/plain`.
///
/// Mirrors Haskell `getNextTheoryPathR` (`src/Web/Handler.hs:1538-1549`):
///   1. parse `path` into a TheoryPath
///   2. call `nextThyPath` or `nextSmartThyPath`
///   3. render `TheoryPathMR idx <new-path>` as a URL string
///
/// The `TheoryProof` arm walks the live proof tree (`getProofPaths` over the
/// materialised [`crate::handlers::proof_tree::ProofState`]); a lemma with no
/// materialised state has the single root path, so it yields no in-tree step
/// and the traversal falls through to the lemma jump, exactly as HS's
/// `getNextElement` does when no sibling exists.
pub async fn next_path(
    State(state): State<Arc<AppState>>,
    Path((idx, section, raw_path)): Path<(usize, String, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    let new_path = next_theory_path(&path, &section, &entry);
    let url = render_main_url(idx, &new_path);
    text_response(url)
}

/// `GET /thy/trace/<idx>/prev/<section>/*path` — symmetric to `next`.
pub async fn prev_path(
    State(state): State<Arc<AppState>>,
    Path((idx, section, raw_path)): Path<(usize, String, String)>,
) -> Response {
    let Some(entry) = state.store.get(idx) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    let new_path = prev_theory_path(&path, &section, &entry);
    let url = render_main_url(idx, &new_path);
    text_response(url)
}

/// Haskell `nextThyPath`/`nextSmartThyPath`.
///
/// The `section` argument is matched verbatim against the strings
/// `"normal"` / `"smart"`; any other value falls through to `const id`
/// (no-op) per Haskell's `next _ = const id` in
/// `src/Web/Handler.hs:1546-1549`.  That means e.g. `next/main/help`
/// returns the SAME path back — used by the frontend when the user
/// presses arrow keys outside the proof tree.
fn next_theory_path(
    p: &path_parse::TheoryPath,
    section: &str,
    entry: &crate::state::TheoryEntry,
) -> path_parse::TheoryPath {
    // HS `getNextTheoryPathR` (`Handler.hs:1546-1549`): `next "normal" =
    // nextThyPath`, `next "smart" = nextSmartThyPath`, everything else
    // `const id` (no-op).  The two differ ONLY in the `TheoryProof` arm.
    match section {
        "normal" => next_thy_path_inner(p, entry, false),
        "smart" => next_thy_path_inner(p, entry, true),
        _ => p.clone(),
    }
}

fn next_thy_path_inner(
    p: &path_parse::TheoryPath,
    entry: &crate::state::TheoryEntry,
    smart: bool,
) -> path_parse::TheoryPath {
    use path_parse::SourceKind;
    use path_parse::TheoryPath as T;
    let lemmas = lemma_names(entry);
    match p {
        T::Help => T::Message,
        T::Message => T::Rules,
        T::Rules => T::Tactic,
        T::Tactic => T::Source {
            kind: SourceKind::Raw,
            src_idx: 0,
            case_idx: 0,
        },
        T::Source {
            kind: SourceKind::Raw,
            ..
        } => T::Source {
            kind: SourceKind::Refined,
            src_idx: 0,
            case_idx: 0,
        },
        // Haskell `nextThyPath` (Web/Theory.hs:1769-1796, see line 1776): refined sources
        // advance to the FIRST lemma's proof root, falling back to Help
        // only when there are no lemmas.
        T::Source {
            kind: SourceKind::Refined,
            ..
        } => match lemmas.first() {
            Some(n) => T::Proof {
                lemma: n.clone(),
                sub: Vec::new(),
            },
            None => T::Help,
        },
        T::Lemma(n) => T::Proof {
            lemma: n.clone(),
            sub: Vec::new(),
        },
        T::Edit(_) | T::Add(_) | T::Delete(_) => T::Help,
        // HS `nextThyPath`/`nextSmartThyPath` TheoryProof arm
        // (Web/Theory.hs:1781-1784 / 1993-1996):
        //   | Just nextPath <- getNextPath l p -> TheoryProof l nextPath
        //   | Just nextLemma <- getNextLemma l -> TheoryProof nextLemma []
        //   | otherwise                        -> TheoryProof l p
        T::Proof { lemma, sub } => {
            let paths = lemma_proof_paths(entry, lemma);
            let next = if smart {
                next_smart_path(&paths, sub)
            } else {
                next_element_path(&paths, sub)
            };
            match next {
                Some(np) => T::Proof {
                    lemma: lemma.clone(),
                    sub: np,
                },
                None => match next_after(&lemmas, lemma) {
                    Some(nl) => T::Proof {
                        lemma: nl,
                        sub: Vec::new(),
                    },
                    None => p.clone(),
                },
            }
        }
        // HS `path@TheoryMethod{} -> path` (no-op).
        T::Method { .. } => p.clone(),
    }
}

fn prev_theory_path(
    p: &path_parse::TheoryPath,
    section: &str,
    entry: &crate::state::TheoryEntry,
) -> path_parse::TheoryPath {
    match section {
        "normal" => prev_thy_path_inner(p, entry, false),
        "smart" => prev_thy_path_inner(p, entry, true),
        _ => p.clone(),
    }
}

fn prev_thy_path_inner(
    p: &path_parse::TheoryPath,
    entry: &crate::state::TheoryEntry,
    smart: bool,
) -> path_parse::TheoryPath {
    use path_parse::SourceKind;
    use path_parse::TheoryPath as T;
    let lemmas = lemma_names(entry);
    let refined_root = || T::Source {
        kind: SourceKind::Refined,
        src_idx: 0,
        case_idx: 0,
    };
    match p {
        T::Help => T::Help,
        T::Message => T::Help,
        T::Rules => T::Message,
        T::Tactic => T::Rules,
        T::Source {
            kind: SourceKind::Raw,
            ..
        } => T::Tactic,
        T::Source {
            kind: SourceKind::Refined,
            ..
        } => T::Source {
            kind: SourceKind::Raw,
            src_idx: 0,
            case_idx: 0,
        },
        // HS `prevThyPath` (Web/Theory.hs:1874-1876):
        //   TheoryLemma l | Just prevLemma <- getPrevLemma l
        //                     -> TheoryProof prevLemma (lastPath prevLemma)
        //                 | otherwise -> TheorySource RefinedSource 0 0
        T::Lemma(n) => match prev_before(&lemmas, n) {
            Some(pl) => {
                let sub = last_path(&lemma_proof_paths(entry, &pl));
                T::Proof { lemma: pl, sub }
            }
            None => refined_root(),
        },
        T::Edit(_) | T::Add(_) | T::Delete(_) => T::Help,
        // HS `prevThyPath`/`prevSmartThyPath` TheoryProof arm
        // (Web/Theory.hs:1877-1880 / 2094-2098):
        //   | Just prevPath <- getPrevPath l p -> TheoryProof l prevPath
        //   | Just prevLemma <- getPrevLemma l ->
        //         TheoryProof prevLemma (lastPath prevLemma)
        //   | otherwise                        -> TheorySource RefinedSource 0 0
        T::Proof { lemma, sub } => {
            let paths = lemma_proof_paths(entry, lemma);
            let prev = if smart {
                prev_smart_path(&paths, sub)
            } else {
                prev_element_path(&paths, sub)
            };
            match prev {
                Some(pp) => T::Proof {
                    lemma: lemma.clone(),
                    sub: pp,
                },
                None => match prev_before(&lemmas, lemma) {
                    Some(pl) => {
                        let sub = last_path(&lemma_proof_paths(entry, &pl));
                        T::Proof { lemma: pl, sub }
                    }
                    None => refined_root(),
                },
            }
        }
        // HS `path@TheoryMethod{} -> path` (no-op).
        T::Method { .. } => p.clone(),
    }
}

/// Lemma names in declaration order (HS `getLemmas thy`).
fn lemma_names(entry: &crate::state::TheoryEntry) -> Vec<String> {
    entry
        .typed_theory
        .lemmas()
        .map(|l| l.name.clone())
        .collect()
}

/// The proof-path list for a lemma (HS `getProofPaths lemma._lProof`).  When
/// no proof state has been materialised yet (a freshly-loaded theory before
/// any autoprove), the lemma's proof is HS's initial `sorry` skeleton — a
/// single root path — which is exactly what the `next`/`prev` traversal needs
/// (an unproven lemma yields no in-tree next/prev step, only lemma jumps).
fn lemma_proof_paths(
    entry: &crate::state::TheoryEntry,
    lemma: &str,
) -> Vec<(
    Vec<String>,
    tamarin_theory::constraint::solver::proof_method::ProofMethod,
)> {
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    entry
        .proof_state
        .as_ref()
        .and_then(|ps| ps.get_root(lemma))
        .map(|root| crate::handlers::proof_tree::get_proof_paths(&root))
        .unwrap_or_else(|| vec![(Vec::new(), ProofMethod::Sorry(None))])
}

type PathList = [(
    Vec<String>,
    tamarin_theory::constraint::solver::proof_method::ProofMethod,
)];

/// HS `getNextElement (== path) (map fst paths)` — the path immediately after
/// the match; `None` if `sub` is absent or last.
fn next_element_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    paths.get(i + 1).map(|(p, _)| p.clone())
}

/// HS `nextSmartThyPath.getNextPath`: `dropWhile (/= path)`, then the first of
/// the REMAINING (after the match) whose method `isInterestingMethod`.
fn next_smart_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    paths[i + 1..]
        .iter()
        .find(|(_, m)| crate::handlers::proof_tree::is_interesting_method(m))
        .map(|(p, _)| p.clone())
}

/// HS `getPrevElement (== path) (map fst paths)` — the path immediately before
/// the match; `None` if `sub` is absent or first.
fn prev_element_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    i.checked_sub(1).map(|j| paths[j].0.clone())
}

/// HS `prevSmartThyPath.getPrevPath`: the LAST interesting-method path among
/// those STRICTLY BEFORE the match (`filter isInteresting . takeWhile (/=)`).
fn prev_smart_path(paths: &PathList, sub: &[String]) -> Option<Vec<String>> {
    let i = paths.iter().position(|(p, _)| p.as_slice() == sub)?;
    paths[..i]
        .iter()
        .rev()
        .find(|(_, m)| crate::handlers::proof_tree::is_interesting_method(m))
        .map(|(p, _)| p.clone())
}

/// HS `lastPath` = `last (map fst (getProofPaths ...))`.  The path list is
/// never empty (always contains the root `[]`), so this is total.
fn last_path(paths: &PathList) -> Vec<String> {
    paths.last().map(|(p, _)| p.clone()).unwrap_or_default()
}

/// HS `getNextElement (== l) names` — the lemma after `cur`.
fn next_after(names: &[String], cur: &str) -> Option<String> {
    let i = names.iter().position(|n| n == cur)?;
    names.get(i + 1).cloned()
}

/// HS `getPrevElement (== l) names` — the lemma before `cur`.
fn prev_before(names: &[String], cur: &str) -> Option<String> {
    let i = names.iter().position(|n| n == cur)?;
    i.checked_sub(1).map(|j| names[j].clone())
}

fn render_main_url(idx: usize, p: &path_parse::TheoryPath) -> String {
    let segs = p.render();
    if segs.is_empty() {
        return format!("/thy/trace/{}/main/help", idx);
    }
    let mut url = format!("/thy/trace/{}/main", idx);
    for s in &segs {
        url.push('/');
        url.push_str(s);
    }
    url
}

// ---------------------------------------------------------------------
// Graph routes — DOT pipeline live.
// ---------------------------------------------------------------------

/// Resolve the [`System`] to render at the given path.  Returns the
/// initial lemma system at proof-paths (`proof/<lemma>` or
/// `proof/<lemma>/<sub>`), or `None` for paths that have no associated
/// system (help / message / etc.).
///
/// Live proof state is materialised on first access via
/// [`TheoryStore::ensure_proof_state`].
fn resolve_system_for_path(
    state: &AppState,
    idx: usize,
    path: &path_parse::TheoryPath,
) -> Option<tamarin_theory::constraint::system::System> {
    let (lemma_name, sub) = match path {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Method { lemma, sub, .. } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Lemma(n) => (n.clone(), Vec::new()),
        _ => return None,
    };
    let ps = state.store.ensure_proof_state(idx, &state.cfg).ok()?;
    ps.get_system_at(&lemma_name, &sub)
}

/// `GET /thy/trace/<idx>/intdot/*path` — the interactive graph shell page.
///
/// HS `getInteractiveDotGraphR` (`src/Web/Handler.hs:903-911`) renders
/// `intdotLayout True` (`src/Web/Types.hs:795-824`) around a
/// `<dot-graph-viz>` custom element whose `dotsrc` points at the JSON graph
/// route; the bundled `intdot-graph.es.js` fetches that and draws the graph
/// client-side.  It does NOT resolve the constraint system itself — the shell
/// is system-agnostic.
///
/// The same page serves both as the pop-out window and as the iframe embedded
/// in the main theory view, so the floating `#popout-options` bar
/// (`popoutOptionsTpl`, `src/Web/Types.hs:769-777`) is hidden client-side when
/// embedded (the inline script sets `graph-embedded` on `<html>`).  Its
/// Options menu is `optionsMenuItemTpl True` — the trace-theory variant, which
/// includes the `abstr-toggle` entry.
pub async fn intdot(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    let Some(name) = state.store.name(idx) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    let dotsrc = graph_json_url(idx, &path);
    let title = crate::handlers::root::html_escape(&format!("Theory: {}", name));
    html_response(intdot_shell_html(&title, &dotsrc))
}

/// Yesod `getUrlRender (TheoryGraphJsonR idx path)` — re-render the parsed
/// path through `renderTheoryPath` + `prefixWithUnderscore` and percent-encode
/// each segment, exactly as the other URL builders here do.
fn graph_json_url(idx: usize, path: &path_parse::TheoryPath) -> String {
    let mut url = format!("/thy/trace/{}/json", idx);
    for seg in path.render() {
        url.push('/');
        url.push_str(&path_parse::url_path_escape(&seg));
    }
    url
}

/// Faithful port of Haskell `getOptions` (`src/Web/Handler.hs`): read a
/// render request's [`GraphOptions`] out of its already-parsed query
/// parameters.
///
/// The flags are presence-based (`un*`/`no-*` toggles arrive with an empty
/// value, so presence, not value, is what matters):
/// - `uncompress`     present => `compress = false`        (HS `isNothing`)
/// - `unabbreviate`   present => `abbreviate = false`      (HS `isNothing`)
/// - `no-auto-sources` present => `show_auto_source = false` (HS `isNothing`;
///   absent => `true`, which overrides the struct default of `false`)
/// - `clustering`     present => `clustering_similar_names = true` (HS `isJust`)
/// - `simplification` value read with `SimplificationLevel`'s derived `Read`,
///   i.e. only the tokens `SL0..SL3` parse (numeric `0..3`, the value the UI
///   actually sends, fails to parse); anything else falls back to `SL2`
///   (HS `fromMaybe SL2 (simpl >>= readMaybe . T.unpack)`).
///
/// The `uncompact`/`CompactBoringNodes` flag belongs to `DotOptions`
/// (`Handler.hs`), not `GraphOptions`, so it is not handled here.
fn graph_options_from_map(qs: &HashMap<String, String>) -> GraphOptions {
    let simplification_level = qs
        .get("simplification")
        .and_then(|v| read_simplification_level(v))
        .unwrap_or(SimplificationLevel::SL2);

    GraphOptions {
        simplification_level,
        // `isNothing <$> lookupGetParam "no-auto-sources"`: absent => true.
        show_auto_source: !qs.contains_key("no-auto-sources"),
        // `_goClustering = isJust clustering`.
        clustering_similar_names: qs.contains_key("clustering"),
        // `isNothing <$> lookupGetParam "unabbreviate"`.
        abbreviate: !qs.contains_key("unabbreviate"),
        // `isNothing <$> lookupGetParam "uncompress"`.
        compress: !qs.contains_key("uncompress"),
    }
}

/// Parse a `SimplificationLevel` exactly as Haskell's derived `Read` would.
///
/// The data type is `data SimplificationLevel = SL0 | SL1 | SL2 | SL3`
/// (`Graph.hs`), so its derived `Read` parses only the bare
/// constructor tokens. Following `Read`'s lexer it skips leading/trailing
/// whitespace and accepts one or more matched pairs of surrounding parentheses;
/// numeric input (e.g. `"2"`) fails. Returns `None` on any non-match.
fn read_simplification_level(s: &str) -> Option<SimplificationLevel> {
    let mut t = s.trim();
    // Derived `Read` allows one (or more) matched pairs of surrounding parens.
    while let (Some(inner), true) = (t.strip_prefix('('), t.ends_with(')')) {
        t = inner.strip_suffix(')')?.trim();
    }
    match t {
        "SL0" => Some(SimplificationLevel::SL0),
        "SL1" => Some(SimplificationLevel::SL1),
        "SL2" => Some(SimplificationLevel::SL2),
        "SL3" => Some(SimplificationLevel::SL3),
        _ => None,
    }
}

/// `GET /thy/trace/<idx>/graph/*path` — return an SVG image of the
/// graph (or DOT source as fallback when `dot` is missing).
///
/// Haskell uses `getTheoryGraphR` to shell out to `dot -Tpng` /
/// `-Tsvg`; we follow the same approach via `std::process::Command`.
pub async fn graph(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    // Held for the whole handler: the theory's user-fn sets stay installed
    // until it drops (see [`LoadedTheory`]).
    let Some(_theory) = load_theory(&state, idx) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // HS `getTheoryGraphR` (`src/Web/Handler.hs:1418-1432`) answers
    // `imgThyPath`'s `Nothing` with a generic `notFound`; there is no
    // placeholder SVG.  The label `imgThyPath` also carries is for its JSON
    // output format, which this route never asks for.
    let sys = match thy_path_system(&state, idx, &path, GRAPH_UNHANDLED_SITE) {
        Ok(resolved) => match resolved.into_system() {
            Some(s) => s,
            None => return not_found(),
        },
        Err(message) => return internal_server_error(&message),
    };
    let opts = graph_options_from_map(&query);
    // Try to render with dot; fall back to DOT-as-text when
    // unavailable.
    match crate::handlers::dot::render_svg_or_dot_with(&sys, &opts, &state.cfg.dot_path) {
        crate::handlers::dot::RenderResult::Svg(bytes) => {
            let mut headers = HeaderMap::new();
            headers.insert(
                header::CONTENT_TYPE,
                header::HeaderValue::from_static("image/svg+xml"),
            );
            (StatusCode::OK, headers, bytes).into_response()
        }
        crate::handlers::dot::RenderResult::Dot(dot) => {
            // Fallback: send the DOT as text/plain so the user (or
            // frontend's viz.js) can pick it up.
            text_response(dot)
        }
    }
}

/// `GET /thy/trace/<idx>/interactive-graph-def/*path` — return DOT
/// for the frontend to render client-side with viz.js.
pub async fn interactive_graph_def(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    // See [`graph`]: the binding keeps the user-fn sets installed.
    let Some(_theory) = load_theory(&state, idx) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // HS `getTheoryInteractiveGraphR` (`src/Web/Handler.hs:1464-1470`) answers
    // `dotGraphString`'s `Nothing` with `notFound`.  `dotGraphString` discards
    // the label its `thyPathSystem` returns (`(_, system) <- thyPathSystem …`).
    let sys = match thy_path_system(&state, idx, &path, INTERACTIVE_DOT_UNHANDLED_SITE) {
        Ok(resolved) => match resolved.into_system() {
            Some(s) => s,
            None => return not_found(),
        },
        Err(message) => return internal_server_error(&message),
    };
    let opts = graph_options_from_map(&query);
    let dot = tamarin_theory::constraint::system::dot::system_to_dot_with(&sys, &opts);
    text_response(dot)
}

/// `GET /thy/trace/<idx>/json/*path` — the constraint system at `path`
/// serialised to the JSON graph format the `<dot-graph-viz>` frontend reads.
///
/// Port of `getTheoryGraphJsonR` (`src/Web/Handler.hs:1435-1444`) over
/// `graphJsonThyPath` (`src/Web/Theory.hs:1307-1341`):
///
/// - `TheoryProof lemma path` — the sub-proof's system, run through
///   `Web.Utils.abbrev` when the `abbrevInBackend` parameter is present, and
///   labelled `Theory: <thy> Lemma: <lemma>`.  An unresolvable proof path is
///   HS `fromMaybe ""`: a 200 with an EMPTY body.
/// - `TheorySource kind i j` — the `(i-1, j-1)` case system, labelled
///   `Theory: <thy> Case: <i>:<j>`, with no backend abbreviation.  Indices
///   naming no case are a 404 (see [`thy_path_system`]).
/// - every other path — HS `error "Unhandled theory path. This is a bug."`,
///   i.e. 500.
///
/// The response `Content-Type` is the literal `.json`: HS hands the cached
/// file to `sendFile (fromString ".json")`, which uses that string verbatim as
/// the MIME type.
pub async fn graph_json(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    // See [`graph`]: held for the whole handler, and the source of the theory
    // name the `jsonLabel`s carry.
    let Some(theory) = load_theory(&state, idx) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    let opts = graph_options_from_map(&query);
    let resolved = match thy_path_system(&state, idx, &path, JSON_UNHANDLED_SITE) {
        Ok(r) => r,
        Err(message) => return internal_server_error(&message),
    };
    let label = resolved.json_label(&theory.name);
    match resolved {
        // HS `proofPathCode`: `fromMaybe BL.empty`, i.e. an unresolvable proof
        // path is a 200 with an empty body.
        PathSystem::Proof { system, .. } => {
            let Some(sys) = system else {
                return json_graph_response(String::new());
            };
            // `Web.Utils.abbrev abbreviate 30 sequent`, with `abbreviate` set
            // by the mere PRESENCE of `abbrevInBackend`.  This is the one
            // route that abbreviates, and — as upstream — only on this arm.
            let abbreviate = query.contains_key("abbrevInBackend");
            let sys = crate::web_utils_abbrev::abbrev(
                abbreviate,
                crate::web_utils_abbrev::MIN_ABBREV_SIZE,
                sys,
            );
            json_graph_response(
                tamarin_theory::constraint::system::json::sequents_to_json_pretty(
                    &opts,
                    &[(label, &sys)],
                ),
            )
        }
        PathSystem::Source { system, .. } => {
            let Some(sys) = system else {
                return not_found();
            };
            // No backend abbreviation on this arm; the serialiser takes a
            // `RenderSystem`, which the proof arm gets back from `abbrev`.
            let sys = tamarin_theory::constraint::system::graph::RenderSystem::from_prover(sys);
            json_graph_response(
                tamarin_theory::constraint::system::json::sequents_to_json_pretty(
                    &opts,
                    &[(label, &sys)],
                ),
            )
        }
    }
}

/// `200 OK` with HS's literal `.json` content type (see [`graph_json`]).
fn json_graph_response(body: String) -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static(".json"),
    );
    (StatusCode::OK, headers, body).into_response()
}

/// Where the `error "Unhandled theory path. This is a bug."` clause of the
/// `thyPathSystem` a route dispatches through sits in `src/Web/Theory.hs`, as
/// `LINE:COLUMN` — the CallStack the raised error carries names the exact
/// call, so each route reports its own copy: `graphJsonThyPath`'s (`/json`),
/// `imgThyPath`'s (`/graph`) and `dotGraphString`'s
/// (`/interactive-graph-def`).  This `error` is upstream's DELIBERATE answer
/// to a theory path the route does not draw, so the port reproduces its page
/// byte-for-byte.
const JSON_UNHANDLED_SITE: &str = "1318:31";

/// `imgThyPath`'s clause — see [`JSON_UNHANDLED_SITE`].
const GRAPH_UNHANDLED_SITE: &str = "1416:51";

/// `dotGraphString`'s clause — see [`JSON_UNHANDLED_SITE`].
const INTERACTIVE_DOT_UNHANDLED_SITE: &str = "2323:51";

/// The `error` `thyPathSystem`'s catch-all clause raises for a theory path that
/// is neither a proof nor a source case, as GHC renders it into Yesod's error
/// page.  `site` is the raising clause (see [`JSON_UNHANDLED_SITE`]).
fn unhandled_theory_path(site: &str) -> String {
    format!(
        "Unhandled theory path. This is a bug.\nCallStack (from HasCallStack):\n  \
         error, called at src/Web/Theory.hs:{site} in main:Web.Theory"
    )
}

/// HS `casesSystem k i j`: the `(i-1, j-1)` case of the `k` sources, or `None`
/// when either 1-based index names no case — the port's correction of the
/// raising `!!` upstream has there (see [`thy_path_system`]).
fn source_case_system(
    entry: &crate::state::TheoryEntry,
    kind: &path_parse::SourceKind,
    src_idx: i64,
    case_idx: i64,
) -> Option<tamarin_theory::constraint::system::System> {
    let want_refined = matches!(kind, path_parse::SourceKind::Refined);
    theory_html::source_list_case(entry, want_refined, src_idx, case_idx)
}

/// What [`thy_path_system`] resolved: the drawn system, plus the arm it came
/// from and that arm's `jsonLabel` ingredients.
///
/// The arm survives the resolution because the three graph routes answer an
/// unresolved system differently — `/json`'s proof arm with an empty 200, every
/// other combination with a `404`.
enum PathSystem {
    /// HS `proofPathSystem lemma proofPath`; `system` is `None` when the proof
    /// path does not resolve.
    Proof {
        lemma: String,
        system: Option<tamarin_theory::constraint::system::System>,
    },
    /// HS `casesSystem k i j`; `system` is `None` when the indices name no
    /// case (see [`source_case_system`]).
    Source {
        src_idx: i64,
        case_idx: i64,
        system: Option<tamarin_theory::constraint::system::System>,
    },
}

impl PathSystem {
    /// The `jsonLabel` the resolving clause builds — the graph's title in the
    /// JSON rendering.  Only `/json` asks for it; `imgThyPath` builds it for
    /// its `OutJSON` format and `dotGraphString` discards it outright.
    fn json_label(&self, thy_name: &str) -> String {
        match self {
            PathSystem::Proof { lemma, .. } => format!("Theory: {} Lemma: {}", thy_name, lemma),
            PathSystem::Source {
                src_idx, case_idx, ..
            } => format!("Theory: {} Case: {}:{}", thy_name, src_idx, case_idx),
        }
    }

    /// The system alone, for the two routes that draw it unlabelled.
    fn into_system(self) -> Option<tamarin_theory::constraint::system::System> {
        match self {
            PathSystem::Proof { system, .. } | PathSystem::Source { system, .. } => system,
        }
    }
}

/// HS `thyPathSystem`, the `Maybe (String, System)` dispatch every graph route
/// goes through (`graphJsonThyPath`'s `go` `src/Web/Theory.hs:1316-1318`,
/// `imgThyPath` `:1414-1416`, `dotGraphString` `:2321-2323`):
///
///   - `TheorySource k i j` — the `casesSystem` case, labelled
///     `Theory: <thy> Case: <i>:<j>`;
///   - `TheoryProof lemma path` — the sub-proof's system, labelled
///     `Theory: <thy> Lemma: <lemma>`;
///   - anything else — the catch-all `error`, at `unhandled_site` (see
///     [`JSON_UNHANDLED_SITE`]), which the routes render as a 500 page.
///
/// The port DIVERGES from upstream on the source-case indices.  Both are read
/// signed (`safeRead` at `ReadS Int`, `src/Web/Types.hs:443`), so every value a
/// client can type in the address bar arrives here, and upstream feeds them
/// straight into `cases !! (i-1) !! (j-1)` behind no bounds check at all
/// (`src/Web/Theory.hs:1322` for `/json`, `:1422` for `/graph`, `:2329` for
/// `/interactive-graph-def`): a non-positive or past-the-end index raises
/// `Prelude.!!` and Yesod serves a 500 page whose body is the exception text
/// with its GHC CallStack.  Here an index that names no case is an ordinary
/// miss — a `None` system, which every route answers with [`not_found`], the
/// same answer upstream gives an unresolvable proof path.
fn thy_path_system(
    state: &AppState,
    idx: usize,
    path: &path_parse::TheoryPath,
    unhandled_site: &str,
) -> Result<PathSystem, String> {
    match path {
        path_parse::TheoryPath::Source {
            kind,
            src_idx,
            case_idx,
        } => {
            // The source cases live on the materialised proof state, so the
            // entry is re-read afterwards (as the `main` handler does).
            materialise_proof_state_if_needed(state, idx, path);
            let system = state
                .store
                .get(idx)
                .and_then(|entry| source_case_system(&entry, kind, *src_idx, *case_idx));
            Ok(PathSystem::Source {
                src_idx: *src_idx,
                case_idx: *case_idx,
                system,
            })
        }
        path_parse::TheoryPath::Proof { lemma, .. } => Ok(PathSystem::Proof {
            lemma: lemma.clone(),
            system: resolve_system_for_path(state, idx, path),
        }),
        _ => Err(unhandled_theory_path(unhandled_site)),
    }
}

/// `GET /thy/trace/<idx>/proof-step/<lemma>/<path...>/<method>` —
/// apply a single proof method at the given path and return a
/// `{html, title}` JsonHtml envelope with the updated proof tree
/// rendered for `/main/proof/<lemma>`.
///
/// URL parsing:
///   - The first segment after `<idx>/proof-step/` is the lemma name.
///   - The LAST 1 or 2 segments are the method (e.g. `simplify`,
///     `induction`, `sorry`, `solve/<id>`).
///   - Everything in between is the proof-tree path (case names).
pub async fn proof_step(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> axum::Json<Value> {
    if !state.store.contains(idx) {
        return json_resp::alert(format!("theory index {} not found", idx));
    }
    // Parse the path: `<lemma>/<case>/.../<method>` or
    // `<lemma>/<case>/.../<method>/<arg>`.  The shared decoder reverses
    // the Haskell `prefixWithUnderscore` invariant per segment.
    let segs: Vec<String> = path_parse::decode_segments(&raw_path);
    if segs.is_empty() {
        return json_resp::alert("missing lemma name");
    }
    let lemma = segs[0].clone();
    // Identify the method head — the last segment is the method
    // unless the second-to-last segment is `solve` (then `solve/<id>`
    // is the method).
    let n = segs.len();
    if n < 2 {
        return json_resp::alert("missing proof method");
    }
    let method_start = if n >= 3 && segs[n - 2] == "solve" {
        n - 2
    } else {
        n - 1
    };
    let case_path: Vec<String> = segs[1..method_start].to_vec();
    let method_segs = &segs[method_start..];
    let ps = match state.store.ensure_proof_state(idx, &state.cfg) {
        Ok(p) => p,
        Err(e) => return json_resp::alert(format!("proof state init failed: {}", e)),
    };
    let sys_at_path = match ps.get_system_at(&lemma, &case_path) {
        Some(s) => s,
        None => {
            return json_resp::alert(format!(
                "no system at path {:?} in lemma {}",
                case_path, lemma
            ))
        }
    };
    let method = match crate::handlers::proof_tree::parse_method(method_segs, &sys_at_path) {
        Some(m) => m,
        None => return json_resp::alert(format!("unknown proof method: {:?}", method_segs)),
    };
    if let Err(e) = ps.apply_at_path(&lemma, &case_path, method) {
        return json_resp::alert(format!("proof step failed: {e}"));
    }
    // Re-render the updated proof tree.  Use the sub-proof snippet
    // for the node at `case_path` so the response shows Applicable
    // Proof Methods + Constraint System + N sub-case(s) just like
    // Haskell does.  Append the full proof tree below for navigation.
    let root = match ps.get_root(&lemma) {
        Some(r) => r,
        None => return json_resp::alert("proof tree disappeared"),
    };
    let node = match crate::handlers::proof_tree::navigate_at(&root, &case_path) {
        Some(n) => n,
        None => return json_resp::alert(format!("no node at path {:?} after step", case_path)),
    };
    // Install this lemma's per-lemma `use_induction`/`heuristic` into the
    // shared ctx before ranking the re-rendered snippet (HS `getProofContext`).
    // Also the user-fn thread-locals — the snippet execs candidate methods.
    let _user_funs_guard = ps.install_user_funs();
    let mut ctx_guard = ps.ctx.lock();
    ps.install_lemma_settings(&mut ctx_guard, &lemma);
    let mut html = crate::handlers::proof_tree::render_sub_proof_snippet(
        idx, &lemma, &case_path, node, &ctx_guard,
    );
    drop(ctx_guard);
    html.push_str("<hr><h3>Proof tree</h3>\n");
    html.push_str(&crate::handlers::proof_tree::render_proof_tree_html(
        idx, &lemma, &root,
    ));
    let title = format!("Proof of {}", lemma);
    json_resp::html(title, html)
}

/// `POST /thy/trace/<idx>/edit/*path` — STUB.
///
/// Haskell's `postTheoryEditR` (`src/Web/Handler.hs:851-886` and
/// the `postEditTheoryR` block-comment at :1588-1622) reparses the
/// lemma plaintext from a form field, calls `editLemma`, and
/// reinserts the modified theory.  The Rust port doesn't yet expose
/// per-lemma plaintext re-parsing through `tamarin-parser`, so this
/// stays an `{alert}` stub.  Blocker: needs a `parseLemmaWithMacros`
/// equivalent in `tamarin-parser` + lemma-replace API on
/// `tamarin-theory::theory::Theory`.
pub async fn edit_stub(_: State<Arc<AppState>>, _: Path<(usize, String)>) -> axum::Json<Value> {
    stub_alert("lemma editing")
}

/// `GET /thy/trace/<idx>/del/path/*path` — delete a lemma (path
/// `lemma/<name>`) or a proof step (path `proof/<lemma>/<sub>`).
/// Returns `{redirect}` on success, mirroring Haskell
/// `getDeleteStepR` in `src/Web/Handler.hs:1681-1698`.
///
/// Haskell uses `modifyTheory` which allocates a fresh idx for the
/// post-delete state.  We do the same (clone the snapshot) — full
/// proof-tree mutation lands later.
pub async fn delete_step(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    if !state.store.contains(idx) {
        return json_resp::alert(format!("theory index {} not found", idx)).into_response();
    }
    // Unparseable path → routing-level 404 (see `parse_path`).
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    match &path {
        // Haskell `removeLemma`-branch.
        path_parse::TheoryPath::Lemma(name) => {
            let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
            // Haskell `modifyTheory` passes `(const path)` as fpath,
            // i.e. the redirect target is the same path that was
            // deleted (a `TheoryLemma name`).  Render shape:
            // `/thy/trace/<newIdx>/overview/lemma/<name>`.  The URL goes
            // through Yesod `getUrlRender`, so percent-encode the name
            // exactly like `apply_method_and_redirect`'s lemma segment.
            json_resp::redirect(format!(
                "/thy/trace/{}/overview/lemma/{}",
                new_idx,
                path_parse::url_path_escape(name)
            ))
            .into_response()
        }
        // Haskell `applyProverAtPath ... sorryProver` branch — mark
        // the targeted proof step `sorry`.  Redirect target = same
        // proof path.
        path_parse::TheoryPath::Proof { lemma, sub } => {
            let new_idx = state.store.clone_at_new_idx(idx).unwrap_or(idx);
            // URL goes through Yesod `getUrlRender`; percent-encode each
            // segment via the shared helpers, identical to
            // `apply_method_and_redirect` (this file).
            let url = overview_proof_url(new_idx, lemma, sub);
            json_resp::redirect(url).into_response()
        }
        _ => json_resp::alert("Can't delete the given theory path!").into_response(),
    }
}

/// `POST /thy/trace/<idx>/get_and_append/<name>` — append every
/// modified lemma's plaintext to the source `.spthy` on disk.
/// Mirrors Haskell `postAppendNewLemmasR` (`src/Web/Handler.hs:1769-1784`).
///
/// We don't yet track per-lemma "modified" state in the Rust port
/// (lemma-editing is still stubbed), so every lemma is treated as
/// unmodified.  That puts us on Haskell's "nothing-to-append" arm:
/// the file is left alone and the response is
/// `{alert: "Appended lemmas to <path>"}` (the alert is informational
/// regardless of whether anything was appended — see Haskell's
/// `allptxts /= "" && isJust maybePath` guard, which short-circuits
/// the file write).
pub async fn append_new_lemmas(
    State(state): State<Arc<AppState>>,
    Path((idx, _name)): Path<(usize, String)>,
) -> axum::Json<Value> {
    let Some(entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx));
    };
    match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => {
            // Haskell's nothing-to-append arm.  We never write because
            // we have no "modified" flag.
            json_resp::alert(format!("Appended lemmas to {}", p.display()))
        }
        _ => {
            // Mirrors Haskell's `if isNothing maybePath then ...` branch.
            json_resp::alert("No origin found for the current theory.".to_string())
        }
    }
}

/// `GET /thy/equiv/<idx>/...` — STUB.
/// Blocker: needs `ClosedDiffTheory` in `tamarin-theory`
/// (not yet ported).  Haskell returns 404 HTML for these routes
/// when no diff theory at idx; we currently return `{alert}` so the
/// frontend can dispatch a useful message.
pub async fn diff_stub(_: State<Arc<AppState>>, _: Path<(usize, String)>) -> axum::Json<Value> {
    stub_alert("diff theories")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pinned submodule's `src/Web/Theory.hs`, embedded at build time: a
    /// submodule bump recompiles this module against the new source, so the
    /// coordinate check below runs on every bump.
    const WEB_THEORY_HS: &str = include_str!("../../../../tamarin-prover/src/Web/Theory.hs");

    /// The `error "Unhandled theory path. …"` raised inside the top-level
    /// binding `func`, as `LINE:COLUMN` — the coordinates GHC's `HasCallStack`
    /// prints: both 1-based, the column that of the `error` token itself.
    fn unhandled_site_in(func: &str) -> String {
        const RAISE: &str = "error \"Unhandled theory path. This is a bug.\"";
        let lines: Vec<&str> = WEB_THEORY_HS.lines().collect();
        let signature = format!("{} ::", func);
        let start = lines
            .iter()
            .position(|l| l.starts_with(&signature))
            .unwrap_or_else(|| panic!("no top-level `{func}` in src/Web/Theory.hs"));
        for (i, line) in lines.iter().enumerate().skip(start + 1) {
            if let Some(off) = line.find(RAISE) {
                return format!("{}:{}", i + 1, line[..off].chars().count() + 1);
            }
            // A new top-level signature ends the binding.
            assert!(
                !(line.starts_with(|c: char| c.is_ascii_alphabetic()) && line.contains("::")),
                "`{func}` raises no unhandled-theory-path error"
            );
        }
        panic!("`{func}` raises no unhandled-theory-path error");
    }

    // The three constants are pasted into 500 bodies verbatim, so nothing else
    // notices when a bump moves the clauses they name: the fixtures those
    // bodies are compared against were captured from the port, and move with
    // the constants rather than with upstream.
    #[test]
    fn unhandled_site_constants_name_the_pinned_call_sites() {
        assert_eq!(JSON_UNHANDLED_SITE, unhandled_site_in("graphJsonThyPath"));
        assert_eq!(GRAPH_UNHANDLED_SITE, unhandled_site_in("imgThyPath"));
        assert_eq!(
            INTERACTIVE_DOT_UNHANDLED_SITE,
            unhandled_site_in("dotGraphString")
        );
    }

    // `getUrlRender (TheoryGraphJsonR idx path)` re-renders the parsed path,
    // so an empty proof-tree case name comes back as the `_` segment
    // `prefixWithUnderscore` encodes it as.
    #[test]
    fn graph_json_url_encodes_empty_case_name() {
        let p = path_parse::TheoryPath::Proof {
            lemma: "injective_agree".into(),
            sub: vec![String::new()],
        };
        assert_eq!(
            graph_json_url(2, &p),
            "/thy/trace/2/json/proof/injective_agree/_"
        );
    }

    // -----------------------------------------------------------------
    // `getOptions` (`graph_options_from_map`)
    // -----------------------------------------------------------------

    /// Split a raw `key=value&...` query string the way axum's `Query`
    /// extractor hands the handlers their map, so the cases below can be
    /// written the way a request spells them.
    fn options_of(qs: &str) -> GraphOptions {
        let params: HashMap<String, String> = qs
            .split('&')
            .filter(|kv| !kv.is_empty())
            .map(|kv| {
                let mut it = kv.splitn(2, '=');
                let k = it.next().unwrap_or("");
                let v = it.next().unwrap_or("");
                (k.to_string(), v.to_string())
            })
            .collect();
        graph_options_from_map(&params)
    }

    #[test]
    fn empty_query_matches_haskell_getoptions_defaults() {
        // With no params HS `getOptions` yields: compress/abbreviate true
        // (uncompress/unabbreviate absent => isNothing => True), clustering
        // false (isJust Nothing), simplification SL2 (readMaybe of Nothing =>
        // fromMaybe SL2), and show_auto_source TRUE -- note this differs from
        // the struct default (False), because `no-auto-sources` is absent so
        // `isNothing` yields True.
        let o = options_of("");
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
        assert!(o.compress);
        assert!(o.abbreviate);
        assert!(!o.clustering_similar_names);
        assert!(o.show_auto_source);
    }

    #[test]
    fn full_query_mirrors_getoptions() {
        // The UI sends numeric simplification=2, which HS derived `Read` for
        // SimplificationLevel cannot parse (only SL0..SL3), so it falls back to
        // SL2. The presence flags flip their respective options off (or on, for
        // clustering).
        let o = options_of(
            "simplification=2&clustering=true&uncompress=&unabbreviate=&no-auto-sources=",
        );
        assert_eq!(o.simplification_level, SimplificationLevel::SL2);
        assert!(o.clustering_similar_names);
        assert!(!o.compress);
        assert!(!o.abbreviate);
        assert!(!o.show_auto_source);
    }

    #[test]
    fn simplification_numeric_falls_back_to_sl2() {
        // HS readMaybe on "0".."3" returns Nothing (derived Read wants SL0..SL3).
        for n in ["0", "1", "2", "3"] {
            let o = options_of(&format!("simplification={n}"));
            assert_eq!(
                o.simplification_level,
                SimplificationLevel::SL2,
                "numeric simplification={n} must fall back to SL2"
            );
        }
    }

    #[test]
    fn simplification_sl_tokens_parse() {
        assert_eq!(
            options_of("simplification=SL0").simplification_level,
            SimplificationLevel::SL0
        );
        assert_eq!(
            options_of("simplification=SL1").simplification_level,
            SimplificationLevel::SL1
        );
        assert_eq!(
            options_of("simplification=SL3").simplification_level,
            SimplificationLevel::SL3
        );
        // Derived `Read` is case-sensitive and tolerates surrounding parens.
        assert_eq!(
            read_simplification_level("(SL3)"),
            Some(SimplificationLevel::SL3)
        );
        assert_eq!(
            read_simplification_level(" ( SL3 ) "),
            Some(SimplificationLevel::SL3)
        );
        assert_eq!(read_simplification_level("sl2"), None);
        assert_eq!(read_simplification_level("2"), None);
        assert_eq!(read_simplification_level("SL4"), None);
        assert_eq!(read_simplification_level(""), None);
    }

    #[test]
    fn presence_flag_with_value_still_counts() {
        // `un*`/`no-*` flags are presence-based; a non-empty value (or no `=`)
        // is still "present".
        let o = options_of("uncompress");
        assert!(!o.compress);
        let o2 = options_of("clustering");
        assert!(o2.clustering_similar_names);
    }

    #[test]
    fn parse_query_unknown_param_keeps_haskell_defaults() {
        // Unknown params do not touch any field; result equals the empty-query
        // (getOptions) outcome, which has show_auto_source = true.
        let o = options_of("unknown=42");
        assert_eq!(o, options_of(""));
        assert!(o.show_auto_source);
    }

    /// The DOT route reads the same map: `simplification=SL3` selects SL3 and
    /// `uncompress` turns compression off.
    #[test]
    fn dot_query_params_select_simplification() {
        let opts = options_of("simplification=SL3&uncompress=");
        assert_eq!(opts.simplification_level, SimplificationLevel::SL3);
        assert!(!opts.compress);
    }
}
