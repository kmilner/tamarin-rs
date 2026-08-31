#!/usr/bin/env bash
# Capture HTTP responses from the Haskell `tamarin-prover interactive`
# server for use as comparison fixtures in the Rust port integration
# tests.
#
# Usage:
#   ./tests/capture_haskell_fixtures.sh [PORT]
#
# Default port: 18901.
#
# Pre-requisites:
#   - the testing oracle built by `./setup.sh testing` (override its automatic
#     discovery with `HS_PATH`)
#   - `curl` and `maude` on PATH (override the latter with `MAUDE_PATH`)
#   - The Tamarin source tree's `examples/regression/trace/issue193.spthy`
#
# Output: writes each captured response into
#   tests/fixtures/haskell-responses/
# plus `oracle_rev`, the submodule revision they were captured from.  The
# `haskell_captures_match_the_submodule_pin` test in tests/common/mod.rs goes
# red when that stamp is not the current pin, so a submodule bump that forgets
# to re-run this script fails the suite instead of silently pinning the port to
# a stale oracle.
#
# Re-run this whenever Haskell behaviour changes.  The Rust port tests in
# `tests/routes_*.rs` compare against these captures several ways: byte
# equality for the error pages, the JSON graph and the dot graphs (there is
# one DOT serializer, `showDot`, on both sides), and JSON envelope key set for
# the route captures whose payload is not yet byte-stable.

set -euo pipefail

PORT="${1:-18901}"
BASE="http://127.0.0.1:${PORT}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
RES_DIR="${SCRIPT_DIR}/fixtures/haskell-responses"
FIXTURE="${SCRIPT_DIR}/fixtures/issue193.spthy"

[ -r "$ROOT/scripts/gate_common.sh" ] || {
  echo "error: missing scripts/gate_common.sh" >&2
  exit 2
}
# shellcheck source=../../../scripts/gate_common.sh
. "$ROOT/scripts/gate_common.sh"
HS_PATH=$(resolve_hs_oracle "$ROOT") || exit 2
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"

# Fixtures must come from the controlled build of the pin and current patch
# series, not an arbitrary binary that happens to have the same base commit.
oracle_rev_check "$HS_PATH" "$MAUDE" "$ROOT"
pin="$(git -C "$ROOT" rev-parse :tamarin-prover)"

if [[ ! -f "$FIXTURE" ]]; then
  echo "error: fixture $FIXTURE missing" >&2
  exit 1
fi

mkdir -p "$RES_DIR"

# Poll the just-launched $SERVER_PID until it serves the root page; dump its
# log and give up otherwise.  Optional $1 names the theory it is serving.
wait_for_server() {
  for _ in {1..40}; do
    if curl -fs -o /dev/null "$BASE/" 2>/dev/null; then
      return
    fi
    sleep 0.5
  done
  echo "error: Haskell server never came up${1:+ for $1} on $BASE/ (log: /tmp/haskell-server.log)" >&2
  cat /tmp/haskell-server.log >&2
  kill "$SERVER_PID" 2>/dev/null || true
  exit 1
}

# Spin Haskell up in its own work-dir so it doesn't dirty ours.
WORKDIR="$(mktemp -d)"
# Keep the completed capture beside the destination so GNU mv can atomically
# exchange the two directories without a cross-filesystem fallback.
CAPTURE_DIR="$(mktemp -d "${RES_DIR}.capture.XXXXXX")"
# BIGDIR is the second phase's work-dir (created further down); declaring it
# here keeps the trap's `${BIGDIR:+...}` well-defined under `set -u` and
# contributes no argument to `rm` while it is empty.
BIGDIR=""
trap 'rm -rf "$WORKDIR" "$CAPTURE_DIR" ${BIGDIR:+"$BIGDIR"}; pkill -P $$ -f "tamarin-prover interactive --port=${PORT}" 2>/dev/null || true' EXIT
cp "$FIXTURE" "$WORKDIR/issue193.spthy"

echo "starting Haskell tamarin-prover on port $PORT ..."
( cd "$WORKDIR" && "$HS_PATH" interactive --port="$PORT" --no-logging ./ ) >/tmp/haskell-server.log 2>&1 &
SERVER_PID=$!
wait_for_server
echo "Haskell server up, capturing fixtures into $RES_DIR ..."

# Convenience helper.
fetch() {
  local outfile="$1"; shift
  local url="$1"; shift
  local method="${1:-GET}"
  # Every method shares one option set, so a flag added here reaches all of
  # them:
  #   -s            no progress meter (the run prints its own table)
  #   -S            but DO report a transport failure on stderr; the `ERR`
  #                 cell alone does not say what went wrong, and stderr is
  #                 left alone so the message reaches the operator
  #   --path-as-is  keep the URL bytes curl sends identical to the ones
  #                 written below, which the Not Found page echoes back
  # We deliberately drop `-f`: we *want* the body of a non-2xx response (e.g.
  # Haskell returns 500 for graph stubs and 404 for /thy/equiv/...; the body
  # documents the route's default behaviour and is asserted against in the
  # Rust tests).
  local opts=(-sS --path-as-is)
  case "$method" in
    POST) opts+=(-X POST) ;;
    HEAD) opts+=(-I) ;;
  esac
  local status
  if ! status=$(curl "${opts[@]}" -o "${CAPTURE_DIR}/${outfile}" \
      -w "%{http_code}" "${BASE}${url}"); then
    printf "  %-30s %3s\n" "$url" ERR
    return 1
  fi
  printf "  %-30s %3s\n" "$url" "$status"
}

# ---------------- Live routes ----------------
fetch index.html                "/"
fetch robots.txt                "/robots.txt"
fetch overview_help.html        "/thy/trace/1/overview/help"
fetch main_help.json            "/thy/trace/1/main/help"
fetch main_rules.json           "/thy/trace/1/main/rules"
fetch main_message.json         "/thy/trace/1/main/message"
fetch main_lemma.json           "/thy/trace/1/main/lemma/debug"
fetch source.txt                "/thy/trace/1/source"
fetch message.json              "/thy/trace/1/message"
fetch download.txt              "/thy/trace/1/download/x.spthy"
fetch reload.json               "/thy/trace/1/reload" POST

# ---------------- Autoprove (Haskell uses capital False) ----------------
fetch autoprove.json            "/thy/trace/1/autoprove/idfs/0/False/proof/debug"
fetch autoprove_on_proven.json  "/thy/trace/2/autoprove/idfs/0/False/proof/debug"
fetch autoprove_on_rules.json   "/thy/trace/1/autoprove/idfs/0/False/rules"
fetch autoprove_all.json        "/thy/trace/1/autoproveAll/idfs/0/proof/debug"

# ---------------- Live routes (fully ported) ----------------
fetch next.txt                  "/thy/trace/1/next/main/lemma/debug"
fetch next_help.txt             "/thy/trace/1/next/main/help"
fetch prev.txt                  "/thy/trace/1/prev/main/lemma/debug"
fetch verify.json               "/thy/trace/1/verify/lemma/debug"
fetch verify_proof.json         "/thy/trace/1/verify/proof/debug"
fetch del_path.json             "/thy/trace/1/del/path/lemma/debug"
fetch del_path_bad.json         "/thy/trace/1/del/path/rules"
fetch kill.txt                  "/kill"
fetch kill_path.txt             "/kill?path=foo"

# ---------------- Yesod's 500 page (json graph route) ----------------
# `graphJsonThyPath` falls through to `error "Unhandled theory path. This is a
# bug."` on any theory path that is neither a proof nor a source case, so this
# URL raises; the body is Yesod's error page and is asserted byte-for-byte in
# `routes_graph.rs`.  Its OTHER 500s — the ones an out-of-range `cases/<i>/<j>`
# index raises inside `!!` — are captured by nothing on purpose: the port
# answers those with the ordinary Not Found page instead (a deliberate
# divergence, see `graph_json_out_of_range_source_index_is_not_found`).
fetch json_rules.html           "/thy/trace/1/json/rules"

# ---------------- Yesod's 404 page ----------------
# Every `notFound` — unknown theory index, unparseable theory path, or a URL
# matching no route at all — carries the same page, with the request's raw
# path echoed into it (HTML-escaped).  `/static` is a separate wai-app-static
# WAI app, so a missing asset there is a bare `File not found` instead.
fetch missing_idx_overview.html "/thy/trace/99/overview/help"
fetch not_found_theory_path.html "/thy/trace/1/json/main"
fetch not_found_unknown_route.html "/nonexistent"
fetch not_found_escaped_path.html "/a&b'c%3Cd"
fetch static_not_found.txt      "/static/js/does-not-exist.js"
# The theory-index route piece is `#Int`: a piece `PathPiece Int` cannot read
# does not match the route, and one that reads but names no live theory is the
# handler's miss — the same page either way.
fetch not_found_negative_idx.html "/thy/trace/-1/overview/help"
fetch not_found_unparsed_idx.html "/thy/trace/1x/overview/help"
fetch not_found_huge_idx.html   "/thy/trace/99999999999999999999/overview/help"

# ---------------- The dot routes' theory-path dispatch ----------------
# `/graph` (`imgThyPath`) and `/interactive-graph-def` (`dotGraphString`) draw
# source cases and proof nodes; every other theory path is their catch-all
# `error`.  The dot captures are the graph itself, asserted byte for byte in
# `routes_graph.rs::interactive_graph_def_renders_source_cases`.  Their
# out-of-range `cases/<i>/<j>` 500s are captured by
# nothing on purpose — the port answers those with `notFound` (a deliberate
# divergence, see `dot_routes_out_of_range_case_is_not_found`).
fetch igd_cases_refined.dot     "/thy/trace/1/interactive-graph-def/cases/refined/1/1"
fetch igd_cases_raw.dot         "/thy/trace/1/interactive-graph-def/cases/raw/1/1"
fetch igd_unhandled_path.html   "/thy/trace/1/interactive-graph-def/rules"
fetch graph_unhandled_path.html "/thy/trace/1/graph/help"

# ---------------- The method route's out-of-range index ----------------
# An `i` past the end of the ranked methods reaches `getTheoryPathMR`'s own
# "Sorry" alert — a 200 JSON alert that allocates no new theory index, so it is
# safe to capture in any order.  A non-positive `i` instead passes upstream's
# `length methods >= i` guard and raises inside `!!`, which comes back as an
# alert quoting the GHC CallStack; that one is captured by nothing on purpose,
# since the port answers this same "Sorry" alert for it (a deliberate
# divergence, see `test_method_out_of_range_index_alerts_match_haskell`).
fetch method_out_of_range.json  "/thy/trace/1/main/method/debug/9999"

# ---------------- Graph shell + the diff-theory stub ----------------
fetch intdot.html               "/thy/trace/1/intdot/lemma/debug"
fetch equiv_overview.json       "/thy/equiv/1/overview/help"

kill "$SERVER_PID" 2>/dev/null || true
wait "$SERVER_PID" 2>/dev/null || true

# ---------------- Backend abbreviation (second theory, second server) -------
# `abbrevInBackend` replaces every premise/conclusion term of `size >= 30` with
# a short `AbbrevName` constant, so it needs a theory carrying such a term plus
# a stored proof for the system to hang off — `BigTermProved.spthy`.  It is
# served from its OWN work-dir: a second `.spthy` alongside `issue193.spthy`
# would renumber the theory indices every URL above depends on.
BIGDIR="$(mktemp -d)"
cp "${SCRIPT_DIR}/fixtures/BigTermProved.spthy" "$BIGDIR/BigTermProved.spthy"
( cd "$BIGDIR" && "$HS_PATH" interactive --port="$PORT" --no-logging ./ ) >>/tmp/haskell-server.log 2>&1 &
SERVER_PID=$!
wait_for_server BigTermProved
fetch json_proof_abbrev.json    "/thy/trace/1/json/proof/done/_/Init/Init?abbrevInBackend=1"
rm -rf "$BIGDIR"

# Stamp the oracle these bytes came from only after every request succeeds,
# then atomically exchange the complete capture with the committed directory.
# After the exchange CAPTURE_DIR names the old fixtures, which the EXIT trap
# removes. A failure or interruption before the exchange leaves them untouched;
# one after it leaves the complete new generation in place. The stamp has no
# trailing newline (the same shape scripts/divergence_fixtures/ uses).
printf '%s' "$pin" > "${CAPTURE_DIR}/oracle_rev"
mv --exchange --no-copy --no-target-directory "$CAPTURE_DIR" "$RES_DIR"

echo "done.  Captures live under: ${RES_DIR} (oracle_rev: $pin)"
kill "$SERVER_PID" 2>/dev/null || true
wait "$SERVER_PID" 2>/dev/null || true
