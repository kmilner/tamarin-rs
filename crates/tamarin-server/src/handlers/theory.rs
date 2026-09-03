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
use tamarin_theory::prove::SearchOptions;

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

// ---------------------------------------------------------------------
// Overview / main view
// ---------------------------------------------------------------------

/// `GET /thy/trace/<idx>/overview/*path` — full framed page.
pub async fn interactive_overview(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
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
    // proto-only rule count. Build and render together on a blocking worker:
    // both source materialisation and the pretty-printers may block.
    match tokio::task::spawn_blocking(move || {
        let entry = state.store.materialized_snapshot(idx, &state.cfg)?;
        theory_html::overview_page(&entry, &path).map_err(crate::state::StoreError::Build)
    })
    .await
    {
        Ok(Ok(html)) => html_response(html),
        Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
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
        let worker_state = state.clone();
        let lemma = lemma.clone();
        let sub = sub.clone();
        let method_nr = *method_nr;
        return match tokio::task::spawn_blocking(move || {
            apply_method(&worker_state, idx, &lemma, method_nr, &sub)
        })
        .await
        {
            Ok(Ok((detached, target))) => {
                let new_idx = state.store.insert(detached);
                match target {
                    path_parse::TheoryPath::Proof { lemma, sub } => {
                        json_resp::redirect(overview_proof_url(new_idx, &lemma, &sub))
                            .into_response()
                    }
                    _ => json_resp::alert("proof navigation returned a non-proof path")
                        .into_response(),
                }
            }
            Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
            Ok(Err(error)) => json_resp::alert(error.to_string()).into_response(),
            Err(error) => json_resp::alert(format!("internal error: {error}")).into_response(),
        };
    }
    match tokio::task::spawn_blocking(move || {
        let entry = entry_for_path(&state, idx, &path)?;
        let body =
            theory_html::path_html(&entry, &path).map_err(crate::state::StoreError::Build)?;
        let title = title_for(&entry, &path).map_err(crate::state::StoreError::Build)?;
        Ok::<_, crate::state::StoreError>(json_resp::html(title, body))
    })
    .await
    {
        Ok(Ok(response)) => response.into_response(),
        Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => json_resp::alert(error.to_string()).into_response(),
        Err(error) => json_resp::alert(format!("internal error: {error}")).into_response(),
    }
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
/// lemma `lemma`'s tree. Returns the unpublished post-step state and redirect
/// target; the async handler publishes it only after the worker completes.
/// Mirrors Haskell's
/// `applyMethodAtPath` + `modifyTheory` flow in
/// `src/Web/Handler.hs:1078-1081` and `src/Web/Theory.hs:86-100`.
fn apply_method(
    state: &AppState,
    idx: usize,
    lemma: &str,
    method_nr: i64,
    sub: &[String],
) -> Result<(crate::state::TheoryEntry, path_parse::TheoryPath), crate::state::StoreError> {
    // Fork first, then derive every input to the transaction from that
    // detached snapshot. This prevents a concurrent reload from mixing a
    // system or ranking from one theory generation with another generation's
    // proof tree.
    let detached = state.store.detached_fork(idx, &state.cfg)?;
    let src_ps = detached
        .proof_state
        .clone()
        .expect("detached_fork always materialises a proof state");
    // Look up the system at the requested path.
    let sys_at_path = match src_ps
        .get_system_at(lemma, sub)
        .map_err(crate::state::StoreError::Build)?
    {
        Some(s) => s,
        None => {
            return Err(crate::state::StoreError::Build(format!(
                "no system at path {:?} in lemma {}",
                sub, lemma
            )))
        }
    };
    // Pick the N-th ranked method (1-based).  Filter to only those
    // methods whose `exec_proof_method` succeeds — matches Haskell's
    // `rankProofMethods` → `execMethods` (`ProofMethod.hs:519-534`)
    // semantics, and matches the user-visible numbering produced by
    // `write_applicable_methods` (which applies the same filter).
    // Without filtering here the numbering would drift on Sorry/no-op
    // candidates that the UI omits.
    let method = {
        let ctx = match src_ps.context_for_lemma(lemma) {
            Ok(ctx) => ctx,
            Err(e) => return Err(crate::state::StoreError::Build(e)),
        };
        // Haskell `applyMethodAtPath` ranks with `useHeuristic heuristic
        // (length proofPath)` (Web/Theory.hs:96); the depth selects
        // which ranking of a multi-ranking heuristic is active
        // (`rankings !! (depth mod n)`, ProofMethod.hs:580-589).  Pass
        // the proof-path length, not a hardcoded 0.
        let candidates = match tamarin_theory::constraint::solver::search::candidate_methods(
            &sys_at_path,
            &ctx,
            sub.len(),
        ) {
            Ok(methods) => methods,
            Err(error) => return Err(crate::state::StoreError::Build(error.to_string())),
        };
        let mut methods = Vec::new();
        // WHNF-depth applicability — MUST match the render pane's
        // filter (write_applicable_methods) so the clicked index
        // selects the same method the user saw.
        for method in candidates {
            let applicable =
                tamarin_theory::constraint::solver::proof_method::is_applicable_for_display(
                    &ctx,
                    &method,
                    &sys_at_path,
                )
                .map_err(|error| crate::state::StoreError::Build(error.to_string()))?;
            if applicable {
                methods.push(method);
            }
        }
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
                return Err(crate::state::StoreError::Build(
                    "Sorry, but the prover failed on the selected method!".to_string(),
                ));
            }
        }
    };
    if let Err(e) = src_ps.apply_at_path(lemma, sub, method) {
        return Err(crate::state::StoreError::Build(format!(
            "proof step failed: {e}"
        )));
    }
    // Build the redirect URL.  Haskell's `getTheoryPathMR` for
    // `TheoryMethod` (`src/Web/Handler.hs:1078-1081`) advances the target
    // via `nextSmartThyPath newThy (TheoryProof lemma proofPath)`, i.e. it
    // walks INTO the freshly created child case of the grown tree.  We do
    // the same by running `next_thy_path_inner` (smart) over the detached
    // entry. For a `TheoryProof` input that
    // arm always yields another `TheoryProof` (child path, next-lemma root,
    // or same path when nothing follows), so we render the `overview/proof`
    // URL from its `(lemma, sub)`.  The URL SHAPE matches Haskell's
    // `renderTheoryPath` (`src/Web/Types.hs:371-384, see line 373`): lemma root (sub=[]) →
    // `proof/<lemma>`; each sub segment is `prefixWithUnderscore`d.
    let src_path = path_parse::TheoryPath::Proof {
        lemma: lemma.to_string(),
        sub: sub.to_vec(),
    };
    let target = next_thy_path_inner(&src_path, &detached, true)?;
    Ok((detached, target))
}

/// Return one consistent theory snapshot, materialising its proof state for
/// paths whose renderer depends on it.
fn entry_for_path(
    state: &AppState,
    idx: usize,
    path: &path_parse::TheoryPath,
) -> Result<crate::state::TheoryEntry, crate::state::StoreError> {
    let needs = matches!(
        path,
        path_parse::TheoryPath::Proof { .. }
        // Message / Rules pages need the closed-theory intruder-rule
        // classification + injective facts; Source pages need the
        // precomputed raw/refined source cases.  All live in the
        // `ProofContext` behind the `ProofState`.
        | path_parse::TheoryPath::Message
        | path_parse::TheoryPath::Rules
        | path_parse::TheoryPath::Source { .. }
    );
    if needs {
        state.store.materialized_snapshot(idx, &state.cfg)
    } else {
        state
            .store
            .get(idx)
            .ok_or(crate::state::StoreError::NotFound(idx))
    }
}

/// Mirror Haskell `titleThyPath` (`src/Web/Theory.hs:1679-1700`).
/// Titles are independent of the theory name EXCEPT `TheoryHelp`.
fn title_for(
    entry: &crate::state::TheoryEntry,
    path: &path_parse::TheoryPath,
) -> Result<String, String> {
    use path_parse::SourceKind;
    use path_parse::TheoryPath::*;
    Ok(match path {
        // TheoryHelp -> "Theory: " ++ thy._thyName
        Help => format!("Theory: {}", entry.typed_theory.name),
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
                    .map(|ps| ps.get_method_at(lemma, sub))
                    .transpose()?
                    .flatten()
                    .map(|method| {
                        // HS `methodName` = `renderHtmlDoc .
                        // prettyProofMethod` — the HtmlDoc LAYOUT
                        // (100/67, entity fill-widths, col 0): a
                        // long method title WRAPS at the same
                        // positions as HS's (the gate collapses
                        // the newline to a space; the break
                        // position is what must match).
                        let _guard = tamarin_theory::pretty_hpj::HtmlEntityWidthGuard::enable();
                        tamarin_theory::pretty_theory::pretty_proof_method_doc(&method).render_with(
                            tamarin_theory::pretty_hpj::DEFAULT_LINE_LENGTH,
                            tamarin_theory::pretty_hpj::DEFAULT_RIBBON,
                        )
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
    })
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
/// path uses, run.rs). The source/download handlers supply a materialised
/// snapshot, so replay failures are returned rather than silently printed as
/// `by sorry`.
///
/// The `Generated from:` version/build lines are placeholders
/// (the interactive server does not carry the CLI build constants — the
/// web-parity gate normalizes them away, as does HS's own `--prove` gate).
/// Wellformedness: the `/* WARNING: ... */` (or `/* All ... successful. */`)
/// block is rendered from the theory's stored `wf_report` — computed at load
/// by the same pipeline `--prove` runs — via the shared `format_wf_block`,
/// so it matches HS byte-for-byte (empty report ⇒ the "all successful" block).
fn render_theory_source(entry: &crate::state::TheoryEntry) -> Result<String, String> {
    let build = tamarin_theory::pretty_theory::BuildInfo {
        tamarin_version: env!("CARGO_PKG_VERSION").to_string(),
        maude_version: String::new(),
        git_revision: String::new(),
        git_branch: String::new(),
        compiled_at: String::new(),
    };
    let wf_block = tamarin_theory::pretty_theory::format_wf_block(&entry.wf_report);
    // Live proof bodies (HS `prettyClosedTheory` prints the stored
    // `IncrementalProof` of every lemma; see doc comment above).
    let proof = entry
        .proof_state
        .as_ref()
        .expect("materialized_snapshot always has a proof state");
    let proved: Vec<tamarin_theory::pretty_theory::ProvedLemma> = entry
        .typed_theory
        .lemmas()
        .map(|lemma| {
            proof.proof_body(&lemma.name).map(|body| {
                let body = body.expect("iterated lemma exists in the proof session");
                tamarin_theory::pretty_theory::ProvedLemma {
                    name: lemma.name.clone(),
                    proof_body: Some(body.to_string()),
                }
            })
        })
        .collect::<Result<_, _>>()?;
    let mut body = tamarin_theory::pretty_theory::pretty_closed_theory(
        &entry.typed_theory,
        &proved,
        &wf_block,
        &build,
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
    // Width: `render` here is HughesPJ's DEFAULT style, 100/67
    // (Text/PrettyPrint/Class.hs:77-78).  `pretty_closed_theory` takes no
    // width because it renders at the process-global display width, which
    // `init_process_globals` pins to `DEFAULT_LINE_LENGTH`/`DEFAULT_RIBBON`
    // = 100/67 before any render — so these routes already match HS's
    // `render . prettyClosedTheory` (byte-verified against the captured
    // oracle body for `issue193.spthy`,
    // `tests/fixtures/haskell-responses/source.txt`).  The batch BINARY is
    // the one that differs: its `renderDoc` pins 110/73 (Console.hs:243,
    // 398-399) via its own width install.
    Ok(body)
}

pub async fn source_(State(state): State<Arc<AppState>>, Path(idx): Path<usize>) -> Response {
    // HS renders the CLOSED theory, whose per-lemma proofs exist from
    // theory-close time.  RS materialises the proof state lazily, so
    // ensure it here. Mirrors the framed-page handler's unconditional
    // materialisation. Rendering can also be expensive, so keep the whole
    // operation on a blocking worker.
    match tokio::task::spawn_blocking(move || {
        let entry = state.store.materialized_snapshot(idx, &state.cfg)?;
        render_theory_source(&entry).map_err(crate::state::StoreError::Build)
    })
    .await
    {
        Ok(Ok(source)) => text_response(source),
        Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
}

// ---------------------------------------------------------------------
// Autoprove
// ---------------------------------------------------------------------

/// Translate one web autoprover invocation into the values which differ from
/// the theory-wide session defaults. HS adapts `AutoProver` at each route;
/// neither the extractor nor `quitOnEmpty` is persistent session state.
fn web_search_options(
    extractor: &str,
    bound: usize,
    quit_on_empty: bool,
    ranking_depth_offset: usize,
) -> Option<SearchOptions> {
    use tamarin_theory::constraint::solver::context::CutStrategy;
    let extractor_cut = match extractor {
        "characterize" => CutStrategy::Nothing,
        "idfs" => CutStrategy::Dfs,
        "bfs" => CutStrategy::Bfs,
        "seqdfs" => CutStrategy::SeqDfs,
        "sorry" => CutStrategy::AfterSorry,
        _ => return None,
    };
    let cut = if quit_on_empty {
        CutStrategy::AfterSorry
    } else {
        extractor_cut
    };
    Some(SearchOptions {
        proof_bound: if bound == 0 { usize::MAX } else { bound },
        ranking_depth_offset,
        cut,
        oracle_only: quit_on_empty,
    })
}

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
    Path((idx, extractor, raw_bound, quit, raw_path)): Path<(
        usize,
        String,
        String,
        String,
        String,
    )>,
) -> Response {
    let Some(bound) = parse_web_bound(&raw_bound) else {
        return not_found();
    };
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
    let Some(quit_on_empty) = parse_bool_path_piece(&quit) else {
        return not_found();
    };
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // Haskell `getProverR` handles only `TheoryProof lemma proofPath`.
    let (lemma_name, sub): (String, Vec<String>) = match &path {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma.clone(), sub.clone()),
        // Haskell `getProverR` non-`TheoryProof` arm
        // (`src/Web/Handler.hs:1137-1138`):
        //   JsonAlert $ "Can't run " <> name <> " on the given theory path!"
        _ => {
            if !state.store.contains(idx) {
                return not_found();
            }
            return json_resp::alert(format!("Can't run {} on the given theory path!", name))
                .into_response();
        }
    };

    // Proof-depth bound: HS `getAutoProverR`'s `adapt` REPLACES the
    // theory autoprover's `apBound` with the URL's value —
    // `bound > 0 = Just bound`, `otherwise = Nothing`
    // (Web/Handler.hs:1235-1249) — so the CLI `--bound` never reaches
    // these routes and 0 means unbounded, not "fall back to a default".
    // The solver applies it as `boundProofDepth` (Theory/Proof.hs:336-344):
    // nodes at that depth become `sorry /* bound N hit */` leaves.
    let search_options = web_search_options(&extractor, bound, quit_on_empty, sub.len())
        .expect("extractor was validated by autoprover_name");
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
    // Keep the complete detached transaction on one blocking worker. Besides
    // keeping Maude/source work off Tokio, this means cancellation can only
    // discard an unpublished value; publication happens below after await.
    let worker_state = state.clone();
    let lemma_owned = lemma_name.clone();
    let sub_owned = sub.clone();
    let result = tokio::task::spawn_blocking(move || -> Result<_, crate::state::StoreError> {
        let detached = worker_state.store.detached_fork(idx, &worker_state.cfg)?;
        let proof = detached
            .proof_state
            .clone()
            .expect("detached_fork always materialises a proof state");
        let sys_at_path = proof
            .get_system_at(&lemma_owned, &sub_owned)
            .map_err(crate::state::StoreError::Build)?
            .ok_or_else(|| {
                crate::state::StoreError::Build("proof path did not resolve".to_string())
            })?;
        let session = proof.session.clone();
        let subtree = tamarin_theory::prove::prove_system_in_session_with_options(
            &session,
            &lemma_owned,
            sys_at_path,
            search_options,
        )
        .map_err(|e| crate::state::StoreError::Build(format!("prove failed: {e}")))?;
        let status = subtree.status;
        // Graft the search result back at the URL's proof path (HS
        // `focus` → `modifyAtPath`; siblings untouched).
        proof
            .graft_at_path(&lemma_owned, &sub_owned, subtree)
            .map_err(crate::state::StoreError::Build)?;
        let is_exists = detached
            .typed_theory
            .lookup_lemma(&lemma_owned)
            .is_some_and(|lemma| {
                matches!(
                    lemma.trace_quantifier,
                    tamarin_theory::theory::TraceQuantifier::ExistsTrace
                )
            });
        let source = path_parse::TheoryPath::Proof {
            lemma: lemma_owned,
            sub: sub_owned,
        };
        let target = next_thy_path_inner(&source, &detached, true)?;
        Ok((detached, status, is_exists, target))
    })
    .await;

    match result {
        Err(join_err) => json_resp::alert(format!("internal error: {}", join_err)).into_response(),
        Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(_)) => {
            // Prover failure (missing session, prove error) or a graft
            // whose lemma/path vanished between the fork and the graft —
            // surface HS's prover-failure alert
            // (`src/Web/Handler.hs:1121-1138, see line 1133`), same as the bad-path arm above.
            json_resp::alert(format!("Sorry, but {} failed!", name)).into_response()
        }
        Ok(Ok((detached, status, is_exists, target))) => {
            let new_idx = state.store.insert(detached);
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
            let verdict = match (status, is_exists) {
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
            // it lands on the `Finished Solved` witness node. The worker ran
            // that traversal against the grafted detached tree before
            // returning it for publication.
            let redir = match target {
                path_parse::TheoryPath::Proof { lemma, sub } => {
                    overview_proof_url(new_idx, &lemma, &sub)
                }
                _ => overview_proof_url(new_idx, &lemma_name, &[]),
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

fn parse_web_bound(raw: &str) -> Option<usize> {
    let bound = raw.parse::<i64>().ok()?;
    Some(usize::try_from(bound).unwrap_or(0))
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
    Path((idx, extractor, raw_bound, raw_path)): Path<(usize, String, String, String)>,
) -> Response {
    let Some(bound) = parse_web_bound(&raw_bound) else {
        return not_found();
    };
    // Match Haskell's Yesod `PathPiece SolutionExtractor`
    // (`src/Web/Types.hs:639-651`): an unrecognised extractor makes
    // `fromPathPiece` return `Nothing`, so Yesod routing 404s before
    // `getAutoProverAllR` runs.  (`getProverAllR` never surfaces the
    // prover `name` to the user — it always redirects — so unlike
    // `autoprove` we only need the validation, not the display name.)
    if autoprover_name(&extractor, bound).is_none() {
        return not_found();
    }
    if parse_path(&raw_path).is_none() {
        return not_found();
    }
    // URL-only proof-depth bound, exactly as `autoprove` above (HS
    // `getAutoProverAllR`'s identical `actualBound`, Web/Handler.hs:1265-1276).
    let search_options = web_search_options(&extractor, bound, false, 0)
        .expect("extractor was validated by autoprover_name");

    let worker_state = state.clone();
    let result = tokio::task::spawn_blocking(move || -> Result<_, crate::state::StoreError> {
        let detached = worker_state.store.detached_fork(idx, &worker_state.cfg)?;
        let lemma_names: Vec<String> = detached
            .typed_theory
            .lemmas()
            .map(|lemma| lemma.name.clone())
            .collect();
        let proof = detached
            .proof_state
            .clone()
            .expect("detached_fork always materialises a proof state");
        // Per-lemma contexts from the retained session, exactly as
        // `autoprove` (HS runs each fold step under `getProofContext`).
        let session = proof.session.clone();
        for lname in &lemma_names {
            // Root system for this lemma — path `[]` is HS's
            // `focus [] prover = prover`, run on `psInfo (root prf)`.
            // Any missing or invalid lemma aborts the detached transaction.
            let sys = proof
                .get_system_at(lname, &[])
                .map_err(crate::state::StoreError::Build)?
                .ok_or_else(|| {
                    crate::state::StoreError::Build(format!(
                        "missing root system for lemma {lname}"
                    ))
                })?;
            let subtree = tamarin_theory::prove::prove_system_in_session_with_options(
                &session,
                lname,
                sys,
                search_options,
            )
            .map_err(|error| crate::state::StoreError::Build(format!("prove {lname}: {error}")))?;
            proof
                .graft_at_path(lname, &[], subtree)
                .map_err(crate::state::StoreError::Build)?;
        }
        let target = match lemma_names.last() {
            Some(last) => {
                let source = path_parse::TheoryPath::Proof {
                    lemma: last.clone(),
                    sub: Vec::new(),
                };
                next_thy_path_inner(&source, &detached, true)?
            }
            None => path_parse::TheoryPath::Help,
        };
        Ok((detached, target))
    })
    .await;
    let (detached, target) = match result {
        Ok(Ok(result)) => result,
        Ok(Err(crate::state::StoreError::NotFound(_))) => return not_found(),
        Ok(Err(error)) => return json_resp::alert(error.to_string()).into_response(),
        Err(error) => return json_resp::alert(format!("internal error: {error}")).into_response(),
    };
    let new_idx = state.store.insert(detached);

    // HS `getProverAllR` (`src/Web/Handler.hs:1141-1155, see line 1150`) advances the target
    // via `nextSmartThyPath thy (TheoryProof (last names) [])` over the
    // NEW theory — the same smart traversal as `autoprove`, seeded at
    // the LAST lemma's root.  Now that the fork holds the freshly
    // proved trees, we can run it faithfully.
    let redir = match target {
        path_parse::TheoryPath::Proof { lemma, sub } => overview_proof_url(new_idx, &lemma, &sub),
        _ => format!("/thy/trace/{}/overview/help", new_idx),
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
    // Unparseable path → routing-level 404 (see `parse_path`).
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    let Some(entry) = state.store.get(idx) else {
        return json_resp::alert(format!("theory index {} not found", idx)).into_response();
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
            // path segment. Use the shared `overview_proof_url` helper.
            let url = overview_proof_url(idx, &lemma, &sub);
            json_resp::redirect(url).into_response()
        }
        // Help-pane fallback: Haskell falls through to
        // `getTheoryPathMR idx TheoryHelp`, which is the JsonHtml for
        // the help screen.  We piggy-back on `theory_path_main` via a
        // synthesised Help path.
        _ => {
            let help_path = path_parse::TheoryPath::Help;
            let title = format!("Theory: {}", entry.typed_theory.name);
            match crate::handlers::theory_html::path_html(&entry, &help_path) {
                Ok(body) => json_resp::html(title, body).into_response(),
                Err(error) => json_resp::alert(error).into_response(),
            }
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
    let Ok(snapshot) = state.store.snapshot(idx) else {
        // Haskell prefers a JSON alert here (`JsonAlert "Theory not
        // found"`) rather than 404, since `reload` is a POST from a
        // form/button — surfacing through the standard alert UI.
        return json_resp::alert("Theory not found".to_string());
    };
    // Mirror Haskell `checkReloadOrigin` (`src/Web/Handler.hs:391-394`):
    // two distinct JsonAlert strings for the two non-Local origins.
    let path = match &snapshot.entry.origin {
        crate::state::TheoryOrigin::Local(p) => p.clone(),
        crate::state::TheoryOrigin::Upload(_) => {
            return json_resp::alert("Cannot reload: theory was uploaded (no file path)");
        }
        crate::state::TheoryOrigin::Interactive => {
            return json_resp::alert(
                "Cannot reload: theory was created interactively (no file path)",
            );
        }
    };
    let worker_state = state.clone();
    let load = tokio::task::spawn_blocking(move || {
        crate::theory_io::load_from_path(
            &path,
            &worker_state.cfg.maude_path,
            worker_state.cfg.derivcheck_timeout,
            worker_state.cfg.solver_parameters,
        )
        .map_err(|error| (path, error))
    })
    .await;
    match load {
        Err(error) => json_resp::alert(format!("internal error: {error}")),
        Ok(Ok(new_entry)) => {
            // Replace at the SAME idx — matches Haskell's
            // `replaceTheory` (used by `postReloadTheoryR` and
            // `editProof`).  URLs that referenced this theory stay
            // valid.
            match state.store.replace_if_current(&snapshot, new_entry) {
                Ok(kept_idx) => {
                    json_resp::redirect(format!("/thy/trace/{}/overview/help", kept_idx))
                }
                Err(error) => json_resp::alert(error.to_string()),
            }
        }
        Ok(Err((path, error))) => match error {
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
    let source = match tokio::task::spawn_blocking(move || {
        let entry = state.store.materialized_snapshot(idx, &state.cfg)?;
        render_theory_source(&entry).map_err(crate::state::StoreError::Build)
    })
    .await
    {
        Ok(Ok(source)) => source,
        Ok(Err(crate::state::StoreError::NotFound(_))) => return not_found(),
        Ok(Err(error)) => return internal_server_error(&error.to_string()),
        Err(error) => return internal_server_error(&format!("internal error: {error}")),
    };
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static("application/octet-stream"),
    );
    // `name` is a client-supplied, percent-DECODED path segment, so it can hold
    // bytes no header value may carry (a newline, say).  Such a name simply
    // gets no disposition header rather than panicking the worker; every name
    // a header can represent is spliced verbatim into the disposition.
    if let Ok(disposition) = format!("attachment; filename=\"{name}\"").parse() {
        headers.insert(header::CONTENT_DISPOSITION, disposition);
    }
    (StatusCode::OK, headers, source).into_response()
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    match tokio::task::spawn_blocking(move || {
        let entry = if matches!(section.as_str(), "normal" | "smart")
            && matches!(&path, path_parse::TheoryPath::Proof { .. })
        {
            state.store.materialized_snapshot(idx, &state.cfg)?
        } else {
            state.store.snapshot(idx)?.entry
        };
        let new_path = next_theory_path(&path, &section, &entry)?;
        Ok::<_, crate::state::StoreError>(render_main_url(idx, &new_path))
    })
    .await
    {
        Ok(Ok(url)) => text_response(url),
        Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
}

/// `GET /thy/trace/<idx>/prev/<section>/*path` — symmetric to `next`.
pub async fn prev_path(
    State(state): State<Arc<AppState>>,
    Path((idx, section, raw_path)): Path<(usize, String, String)>,
) -> Response {
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    match tokio::task::spawn_blocking(move || {
        let entry = if matches!(section.as_str(), "normal" | "smart")
            && matches!(
                &path,
                path_parse::TheoryPath::Proof { .. } | path_parse::TheoryPath::Lemma(_)
            ) {
            state.store.materialized_snapshot(idx, &state.cfg)?
        } else {
            state.store.snapshot(idx)?.entry
        };
        let new_path = prev_theory_path(&path, &section, &entry)?;
        Ok::<_, crate::state::StoreError>(render_main_url(idx, &new_path))
    })
    .await
    {
        Ok(Ok(url)) => text_response(url),
        Ok(Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
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
) -> Result<path_parse::TheoryPath, crate::state::StoreError> {
    // HS `getNextTheoryPathR` (`Handler.hs:1546-1549`): `next "normal" =
    // nextThyPath`, `next "smart" = nextSmartThyPath`, everything else
    // `const id` (no-op).  The two differ ONLY in the `TheoryProof` arm.
    match section {
        "normal" => next_thy_path_inner(p, entry, false),
        "smart" => next_thy_path_inner(p, entry, true),
        _ => Ok(p.clone()),
    }
}

fn next_thy_path_inner(
    p: &path_parse::TheoryPath,
    entry: &crate::state::TheoryEntry,
    smart: bool,
) -> Result<path_parse::TheoryPath, crate::state::StoreError> {
    use path_parse::SourceKind;
    use path_parse::TheoryPath as T;
    let lemmas = lemma_names(entry);
    Ok(match p {
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
            let paths = lemma_proof_paths(entry, lemma)?;
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
    })
}

fn prev_theory_path(
    p: &path_parse::TheoryPath,
    section: &str,
    entry: &crate::state::TheoryEntry,
) -> Result<path_parse::TheoryPath, crate::state::StoreError> {
    match section {
        "normal" => prev_thy_path_inner(p, entry, false),
        "smart" => prev_thy_path_inner(p, entry, true),
        _ => Ok(p.clone()),
    }
}

fn prev_thy_path_inner(
    p: &path_parse::TheoryPath,
    entry: &crate::state::TheoryEntry,
    smart: bool,
) -> Result<path_parse::TheoryPath, crate::state::StoreError> {
    use path_parse::SourceKind;
    use path_parse::TheoryPath as T;
    let lemmas = lemma_names(entry);
    let refined_root = || T::Source {
        kind: SourceKind::Refined,
        src_idx: 0,
        case_idx: 0,
    };
    Ok(match p {
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
                let sub = last_path(&lemma_proof_paths(entry, &pl)?);
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
            let paths = lemma_proof_paths(entry, lemma)?;
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
                        let sub = last_path(&lemma_proof_paths(entry, &pl)?);
                        T::Proof { lemma: pl, sub }
                    }
                    None => refined_root(),
                },
            }
        }
        // HS `path@TheoryMethod{} -> path` (no-op).
        T::Method { .. } => p.clone(),
    })
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
) -> Result<
    Vec<(
        Vec<String>,
        tamarin_theory::constraint::solver::proof_method::ProofMethod,
    )>,
    crate::state::StoreError,
> {
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    let Some(proof) = entry.proof_state.as_ref() else {
        return Ok(vec![(Vec::new(), ProofMethod::Sorry(None))]);
    };
    proof
        .proof_index_root(lemma)
        .map(|root| {
            root.map(|root| crate::handlers::proof_tree::get_proof_index_paths(&root))
                .unwrap_or_else(|| vec![(Vec::new(), ProofMethod::Sorry(None))])
        })
        .map_err(crate::state::StoreError::Build)
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
/// [`TheoryStore::materialized_snapshot`].
fn resolve_system_for_path(
    entry: &crate::state::TheoryEntry,
    path: &path_parse::TheoryPath,
) -> Result<Option<tamarin_theory::constraint::system::System>, String> {
    let (lemma_name, sub) = match path {
        path_parse::TheoryPath::Proof { lemma, sub } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Method { lemma, sub, .. } => (lemma.clone(), sub.clone()),
        path_parse::TheoryPath::Lemma(n) => (n.clone(), Vec::new()),
        _ => return Ok(None),
    };
    let proof = entry
        .proof_state
        .as_ref()
        .expect("materialized_snapshot always has a proof state");
    proof.get_system_at(&lemma_name, &sub)
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // HS `getTheoryGraphR` (`src/Web/Handler.hs:1418-1432`) answers
    // `imgThyPath`'s `Nothing` with a generic `notFound`; there is no
    // placeholder SVG.  The label `imgThyPath` carries is for its `OutJSON`
    // branch, taken below only when `--with-json` was given.
    let opts = graph_options_from_map(&query);
    // `--with-json` switches this route to HS's `OutJSON` render branch
    // (`imgThyPath` picks `toJSON jsonLabel system`, Web/Theory.hs:1404-1412,
    // and `renderGraphCode` runs `jsonToImg`, Web/Theory.hs:1484-1491): the
    // system is serialised with the SAME serialiser and label the `/json/`
    // route uses — but never abbreviated, `imgThyPath` has no abbrev call —
    // written to a file, and `<json-cmd> <img> <json>` is spawned to produce
    // the image.  There is no `fdp` retry on this branch (`_ -> return
    // False`), and a failure is `Nothing` → HS's generic `notFound`.
    let result = tokio::task::spawn_blocking(
        move || -> Result<Option<Response>, crate::state::StoreError> {
            let entry = state.store.materialized_snapshot(idx, &state.cfg)?;
            let resolved = thy_path_system(&entry, &path, GRAPH_UNHANDLED_SITE)
                .map_err(crate::state::StoreError::Build)?;
            let label = resolved.json_label(&entry.typed_theory.name);
            let Some(sys) = resolved.into_system() else {
                return Ok(None);
            };
            if let Some(json_cmd) = state.cfg.json_path.as_deref() {
                let rsys =
                    tamarin_theory::constraint::system::graph::RenderSystem::from_prover(sys);
                let json = tamarin_theory::constraint::system::json::sequents_to_json_pretty(
                    &opts,
                    &[(label, &rsys)],
                );
                return Ok(Some(render_img_via_json_cmd(json_cmd, &json)));
            }
            Ok(Some(
                match crate::handlers::dot::render_svg_or_dot_with(&sys, &opts, &state.cfg.dot_path)
                {
                    crate::handlers::dot::RenderResult::Svg(bytes) => {
                        let mut headers = HeaderMap::new();
                        headers.insert(
                            header::CONTENT_TYPE,
                            header::HeaderValue::from_static("image/svg+xml"),
                        );
                        (StatusCode::OK, headers, bytes).into_response()
                    }
                    crate::handlers::dot::RenderResult::Dot(dot) => text_response(dot),
                },
            ))
        },
    )
    .await;
    match result {
        Ok(Ok(Some(response))) => response,
        Ok(Ok(None) | Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
}

/// `GET /thy/trace/<idx>/interactive-graph-def/*path` — return DOT
/// for the frontend to render client-side with viz.js.
pub async fn interactive_graph_def(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
    Query(query): Query<HashMap<String, String>>,
) -> Response {
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    // HS `getTheoryInteractiveGraphR` (`src/Web/Handler.hs:1464-1470`) answers
    // `dotGraphString`'s `Nothing` with `notFound`.  `dotGraphString` discards
    // the label its `thyPathSystem` returns (`(_, system) <- thyPathSystem …`).
    let opts = graph_options_from_map(&query);
    let result = tokio::task::spawn_blocking(
        move || -> Result<Option<String>, crate::state::StoreError> {
            let entry = state.store.materialized_snapshot(idx, &state.cfg)?;
            let resolved = thy_path_system(&entry, &path, INTERACTIVE_DOT_UNHANDLED_SITE)
                .map_err(crate::state::StoreError::Build)?;
            Ok(resolved.into_system().map(|sys| {
                tamarin_theory::constraint::system::dot::system_to_dot_with(&sys, &opts)
            }))
        },
    )
    .await;
    match result {
        Ok(Ok(Some(dot))) => text_response(dot),
        Ok(Ok(None) | Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
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
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    let opts = graph_options_from_map(&query);
    let result = tokio::task::spawn_blocking(
        move || -> Result<Option<String>, crate::state::StoreError> {
            let entry = state.store.materialized_snapshot(idx, &state.cfg)?;
            let resolved = thy_path_system(&entry, &path, JSON_UNHANDLED_SITE)
                .map_err(crate::state::StoreError::Build)?;
            let label = resolved.json_label(&entry.typed_theory.name);
            Ok(match resolved {
                // HS `proofPathCode`: `fromMaybe BL.empty`, i.e. an unresolvable proof
                // path is a 200 with an empty body.
                PathSystem::Proof { system, .. } => {
                    let Some(sys) = system else {
                        return Ok(Some(String::new()));
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
                    Some(
                        tamarin_theory::constraint::system::json::sequents_to_json_pretty(
                            &opts,
                            &[(label, &sys)],
                        ),
                    )
                }
                PathSystem::Source { system, .. } => {
                    let Some(sys) = system else {
                        return Ok(None);
                    };
                    // No backend abbreviation on this arm; the serialiser takes a
                    // `RenderSystem`, which the proof arm gets back from `abbrev`.
                    let sys =
                        tamarin_theory::constraint::system::graph::RenderSystem::from_prover(sys);
                    Some(
                        tamarin_theory::constraint::system::json::sequents_to_json_pretty(
                            &opts,
                            &[(label, &sys)],
                        ),
                    )
                }
            })
        },
    )
    .await;
    match result {
        Ok(Ok(Some(json))) => json_graph_response(json),
        Ok(Ok(None) | Err(crate::state::StoreError::NotFound(_))) => not_found(),
        Ok(Err(error)) => internal_server_error(&error.to_string()),
        Err(error) => internal_server_error(&format!("internal error: {error}")),
    }
}

/// HS `jsonToImg` (Web/Theory.hs:1484-1491): write the JSON graph to a
/// file, spawn `<json-cmd> <img> <json>` with empty stdin, and serve the
/// produced image.  A nonzero exit is HS's stdout report —
/// `jsonToImg: <cmd> failed with code <i> for file <json>:\n<err>` — then
/// the `WARNING: failed to convert` stderr trace (`renderGraphCode`,
/// Web/Theory.hs:1480-1481) and the route's `notFound`.
///
/// HS names both files under its cache dir by a hash of the content; this
/// port renders per-request under the system temp dir with a
/// process-unique name.  The image is served as SVG, matching the `dot`
/// branch's assumption (`--image-format` is parsed but not yet routed).
fn render_img_via_json_cmd(json_cmd: &str, json: &str) -> Response {
    use std::io::Write;
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join("tamarin-rs-graphs");
    if let Err(e) = std::fs::create_dir_all(&dir) {
        return internal_server_error(&format!("could not create {}: {e}", dir.display()));
    }
    let stem = format!(
        "graph-{}-{}",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    );
    let json_path = dir.join(format!("{stem}.json"));
    let img_path = dir.join(format!("{stem}.json.svg"));
    let write = std::fs::File::create(&json_path).and_then(|mut f| f.write_all(json.as_bytes()));
    if let Err(e) = write {
        return internal_server_error(&format!("could not write {}: {e}", json_path.display()));
    }
    let out = std::process::Command::new(json_cmd)
        .arg(&img_path)
        .arg(&json_path)
        .stdin(std::process::Stdio::null())
        .output();
    let rendered = match out {
        Ok(o) if o.status.success() => true,
        Ok(o) => {
            let code = o.status.code().unwrap_or(-1);
            println!(
                "jsonToImg: {json_cmd} failed with code {code} for file {}:\n{}",
                json_path.display(),
                String::from_utf8_lossy(&o.stderr)
            );
            false
        }
        // HS `readProcessWithExitCode` on a missing binary throws into the
        // request thread; answer the same `notFound` after the warning.
        Err(e) => {
            println!(
                "jsonToImg: {json_cmd} failed for file {}:\n{e}",
                json_path.display()
            );
            false
        }
    };
    let response = if rendered {
        match std::fs::read(&img_path) {
            Ok(bytes) => {
                let mut headers = HeaderMap::new();
                headers.insert(
                    header::CONTENT_TYPE,
                    header::HeaderValue::from_static("image/svg+xml"),
                );
                Some((StatusCode::OK, headers, bytes).into_response())
            }
            Err(_) => None,
        }
    } else {
        None
    };
    let _ = std::fs::remove_file(&json_path);
    let _ = std::fs::remove_file(&img_path);
    response.unwrap_or_else(|| {
        eprintln!("WARNING: failed to convert:\n  '{}'", json_path.display());
        not_found()
    })
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
) -> Result<Option<tamarin_theory::constraint::system::System>, String> {
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
    entry: &crate::state::TheoryEntry,
    path: &path_parse::TheoryPath,
    unhandled_site: &str,
) -> Result<PathSystem, String> {
    match path {
        path_parse::TheoryPath::Source {
            kind,
            src_idx,
            case_idx,
        } => {
            let system = source_case_system(entry, kind, *src_idx, *case_idx)?;
            Ok(PathSystem::Source {
                src_idx: *src_idx,
                case_idx: *case_idx,
                system,
            })
        }
        path_parse::TheoryPath::Proof { lemma, .. } => Ok(PathSystem::Proof {
            lemma: lemma.clone(),
            system: resolve_system_for_path(entry, path)?,
        }),
        _ => Err(unhandled_theory_path(unhandled_site)),
    }
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
/// post-delete state. We likewise publish a detached snapshot only after the
/// requested deletion succeeds.
pub async fn delete_step(
    State(state): State<Arc<AppState>>,
    Path((idx, raw_path)): Path<(usize, String)>,
) -> Response {
    // Unparseable path → routing-level 404 (see `parse_path`).
    let Some(path) = parse_path(&raw_path) else {
        return not_found();
    };
    match &path {
        // Haskell `removeLemma`-branch.
        path_parse::TheoryPath::Lemma(name) => {
            let delete_state = state.clone();
            let name_owned = name.clone();
            let detached = match tokio::task::spawn_blocking(move || {
                let mut detached = delete_state
                    .store
                    .materialized_snapshot(idx, &delete_state.cfg)?;
                detached.idx = 0;
                detached.primary = false;
                if detached.typed_theory.lookup_lemma(&name_owned).is_none() {
                    return Err(crate::state::StoreError::Build(
                        "Sorry, but removing the selected lemma failed!".to_string(),
                    ));
                }
                let mut theory = (*detached.typed_theory).clone();
                let removed = theory.remove_lemma(&name_owned);
                debug_assert!(removed);
                detached.typed_theory = Arc::new(theory);
                if let Some(previous) = detached.proof_state.take() {
                    detached.proof_state = Some(Arc::new(
                        previous
                            .rebase_onto(
                                &detached.typed_theory,
                                (*detached.prover_maude_sig).clone(),
                                &delete_state.cfg.maude_path,
                                delete_state.cfg.stop_on_trace,
                                detached.ndc_cache.as_ref(),
                                delete_state.cfg.solver_parameters,
                            )
                            .map_err(crate::state::StoreError::Build)?,
                    ));
                }
                Ok(detached)
            })
            .await
            {
                Ok(Ok(entry)) => entry,
                Ok(Err(crate::state::StoreError::NotFound(_))) => return not_found(),
                Ok(Err(error)) => return json_resp::alert(error.to_string()).into_response(),
                Err(error) => {
                    return json_resp::alert(format!("internal error: {error}")).into_response();
                }
            };
            let new_idx = state.store.insert(detached);
            // Haskell `modifyTheory` passes `(const path)` as fpath,
            // i.e. the redirect target is the same path that was
            // deleted (a `TheoryLemma name`).  Render shape:
            // `/thy/trace/<newIdx>/overview/lemma/<name>`.  The URL goes
            // through Yesod `getUrlRender`, so percent-encode the name with
            // the shared `url_path_escape` helper.
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
            let delete_state = state.clone();
            let lemma_owned = lemma.clone();
            let sub_owned = sub.clone();
            let detached =
                match tokio::task::spawn_blocking(move || -> Result<_, crate::state::StoreError> {
                    let detached = delete_state.store.detached_fork(idx, &delete_state.cfg)?;
                    let proof = detached
                        .proof_state
                        .clone()
                        .expect("detached_fork always materialises a proof state");
                    if !proof
                        .mark_removed_at_path(&lemma_owned, &sub_owned)
                        .map_err(crate::state::StoreError::Build)?
                    {
                        return Err(crate::state::StoreError::Build(
                            "Sorry, but removing the selected proof step failed!".to_string(),
                        ));
                    }
                    Ok(detached)
                })
                .await
                {
                    Ok(Ok(entry)) => entry,
                    Ok(Err(crate::state::StoreError::NotFound(_))) => return not_found(),
                    Ok(Err(error)) => return json_resp::alert(error.to_string()).into_response(),
                    Err(error) => {
                        return json_resp::alert(format!("internal error: {error}"))
                            .into_response();
                    }
                };
            let new_idx = state.store.insert(detached);
            // URL goes through Yesod `getUrlRender`; percent-encode each
            // segment via the shared `overview_proof_url` helper.
            let url = overview_proof_url(new_idx, lemma, sub);
            json_resp::redirect(url).into_response()
        }
        _ if !state.store.contains(idx) => not_found(),
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

    #[test]
    fn web_search_options_are_per_invocation() {
        use tamarin_theory::constraint::solver::context::CutStrategy;

        for (extractor, expected) in [
            ("idfs", CutStrategy::Dfs),
            ("bfs", CutStrategy::Bfs),
            ("seqdfs", CutStrategy::SeqDfs),
            ("sorry", CutStrategy::AfterSorry),
            ("characterize", CutStrategy::Nothing),
        ] {
            let nested = web_search_options(extractor, 5, false, 3).expect(extractor);
            assert_eq!(nested.proof_bound, 5);
            assert_eq!(nested.ranking_depth_offset, 3);
            assert_eq!(nested.cut, expected);
            assert!(!nested.oracle_only);
        }

        let unbounded = web_search_options("characterize", 0, false, 0).expect("all");
        assert_eq!(unbounded.proof_bound, usize::MAX);
        assert_eq!(unbounded.cut, CutStrategy::Nothing);

        let quit = web_search_options("characterize", 0, true, 0).expect("quit");
        assert_eq!(quit.cut, CutStrategy::AfterSorry);
        assert!(quit.oracle_only);
        assert!(web_search_options("unknown", 0, false, 0).is_none());
        assert!(web_search_options("unknown", 0, true, 0).is_none());
    }

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
}
