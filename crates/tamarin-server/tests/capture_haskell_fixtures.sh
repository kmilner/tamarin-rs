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
#   - `tamarin-prover` on PATH
#   - `curl` on PATH
#   - The Tamarin source tree's `examples/regression/trace/issue193.spthy`
#
# Output: writes each captured response into
#   tests/fixtures/haskell-responses/
#
# Re-run this whenever Haskell behaviour changes.  The Rust port tests
# in `tests/routes_*.rs` compare the JSON envelope key set (not byte
# equality) against these captures.

set -euo pipefail

PORT="${1:-18901}"
BASE="http://127.0.0.1:${PORT}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RES_DIR="${SCRIPT_DIR}/fixtures/haskell-responses"
FIXTURE="${SCRIPT_DIR}/fixtures/issue193.spthy"

if ! command -v tamarin-prover >/dev/null 2>&1; then
  echo "error: tamarin-prover not on PATH" >&2
  exit 1
fi

if [[ ! -f "$FIXTURE" ]]; then
  echo "error: fixture $FIXTURE missing" >&2
  exit 1
fi

mkdir -p "$RES_DIR"

# Spin Haskell up in its own work-dir so it doesn't dirty ours.
WORKDIR="$(mktemp -d)"
trap 'rm -rf "$WORKDIR"; pkill -P $$ -f "tamarin-prover interactive --port=${PORT}" 2>/dev/null || true' EXIT
cp "$FIXTURE" "$WORKDIR/issue193.spthy"

echo "starting Haskell tamarin-prover on port $PORT ..."
( cd "$WORKDIR" && tamarin-prover interactive --port="$PORT" --no-logging ./ ) >/tmp/haskell-server.log 2>&1 &
SERVER_PID=$!

# Wait for the server to start serving.
for i in {1..40}; do
  if curl -fs -o /dev/null "$BASE/" 2>/dev/null; then
    break
  fi
  sleep 0.5
done
if ! curl -fs -o /dev/null "$BASE/" 2>/dev/null; then
  echo "error: Haskell server never came up on $BASE/ (log: /tmp/haskell-server.log)" >&2
  cat /tmp/haskell-server.log >&2
  kill "$SERVER_PID" 2>/dev/null || true
  exit 1
fi
echo "Haskell server up, capturing fixtures into $RES_DIR ..."

# Convenience helper.
fetch() {
  local outfile="$1"; shift
  local url="$1"; shift
  local method="${1:-GET}"
  # Note: we deliberately drop `curl -f`.  We *want* to capture the
  # body for non-2xx responses (e.g. Haskell returns 500 for graph
  # stubs and 404 for /thy/equiv/...; the body documents the route's
  # default behaviour and is asserted against in the Rust tests).
  # `--path-as-is` keeps the URL bytes curl sends identical to the ones
  # written here, which the Not Found page echoes back.
  local status
  if [[ "$method" == "POST" ]]; then
    status=$(curl -sS --path-as-is -X POST -o "${RES_DIR}/${outfile}" -w "%{http_code}" "${BASE}${url}" 2>/dev/null || echo "ERR")
  elif [[ "$method" == "HEAD" ]]; then
    status=$(curl -sI --path-as-is -o "${RES_DIR}/${outfile}" -w "%{http_code}" "${BASE}${url}" || echo "ERR")
  else
    status=$(curl -sS --path-as-is -o "${RES_DIR}/${outfile}" -w "%{http_code}" "${BASE}${url}" 2>/dev/null || echo "ERR")
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

# ---------------- Live routes (now fully ported) ----------------
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
# `graphJsonThyPath` indexes the source cases with `!!` and falls through to
# `error` on any other theory path, so these four URLs raise; the bodies are
# Yesod's error page and are asserted byte-for-byte in `routes_graph.rs`.
# The case indices are read as signed `Int`s, so `1/-1` indexes off the front
# of the case list exactly as `1/0` would.
fetch json_cases_neg_index.html "/thy/trace/1/json/cases/refined/0/0"
fetch json_cases_neg_case_index.html "/thy/trace/1/json/cases/refined/1/-1"
fetch json_cases_too_large.html "/thy/trace/1/json/cases/refined/9/9"
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
# `error`, and an out-of-range case index raises from their own `!!`.  The dot
# captures are the graph itself, asserted by label in `routes_graph.rs` (the
# port's dot emitter writes the same graph in a different dialect).
fetch igd_cases_refined.dot     "/thy/trace/1/interactive-graph-def/cases/refined/1/1"
fetch igd_cases_raw.dot         "/thy/trace/1/interactive-graph-def/cases/raw/1/1"
fetch igd_cases_neg_index.html  "/thy/trace/1/interactive-graph-def/cases/refined/0/0"
fetch igd_cases_too_large.html  "/thy/trace/1/interactive-graph-def/cases/refined/1/9"
fetch igd_unhandled_path.html   "/thy/trace/1/interactive-graph-def/rules"
fetch graph_cases_neg_index.html "/thy/trace/1/graph/cases/refined/0/0"
fetch graph_cases_too_large.html "/thy/trace/1/graph/cases/refined/1/9"
fetch graph_unhandled_path.html "/thy/trace/1/graph/help"

# ---------------- Stubs (capture for documentation) ----------------
fetch intdot.html               "/thy/trace/1/intdot/lemma/debug"
fetch equiv_overview.json       "/thy/equiv/1/overview/help"

echo "done.  Captures live under: ${RES_DIR}"
kill "$SERVER_PID" 2>/dev/null || true
wait "$SERVER_PID" 2>/dev/null || true
