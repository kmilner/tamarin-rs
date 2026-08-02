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
#   - `tamarin-prover` on PATH, built from the submodule pin (the script
#     refuses any other revision)
#   - `curl` on PATH
#   - The Tamarin source tree's `examples/regression/trace/issue193.spthy`
#
# Output: writes each captured response into
#   tests/fixtures/haskell-responses/
#
# Re-run this whenever Haskell behaviour changes.  The Rust port tests in
# `tests/routes_*.rs` compare against these captures several ways: byte
# equality for the error pages and the JSON graph, label equality for the
# dot graphs (the port's dot emitter writes the same graph in another
# dialect), and JSON envelope key set for the route captures whose payload
# is not yet byte-stable.

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

# Fixtures must come from the pinned patched oracle, not whatever
# tamarin-prover happens to be first on PATH (the brew release shadows it
# on this machine). Refuse any binary whose baked git revision differs
# from the submodule pin.
pin="$(git -C "${SCRIPT_DIR}/../../.." rev-parse :tamarin-prover)"
binrev="$(tamarin-prover --version 2>/dev/null | sed -n 's/^Git revision: \([0-9a-f]*\).*/\1/p')"
if [[ "$binrev" != "$pin" ]]; then
  echo "error: tamarin-prover on PATH is revision '${binrev:-unknown}' but the submodule pin is $pin" >&2
  echo "       put the testing oracle's bin dir first on PATH (tamarin-prover-testing/.stack-work/install/*/*/*/bin)" >&2
  exit 1
fi

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
# BIGDIR is the second phase's work-dir (created further down); declaring it
# here keeps the trap's `${BIGDIR:+...}` well-defined under `set -u` and
# contributes no argument to `rm` while it is empty.
BIGDIR=""
trap 'rm -rf "$WORKDIR" ${BIGDIR:+"$BIGDIR"}; pkill -P $$ -f "tamarin-prover interactive --port=${PORT}" 2>/dev/null || true' EXIT
cp "$FIXTURE" "$WORKDIR/issue193.spthy"

echo "starting Haskell tamarin-prover on port $PORT ..."
( cd "$WORKDIR" && tamarin-prover interactive --port="$PORT" --no-logging ./ ) >/tmp/haskell-server.log 2>&1 &
SERVER_PID=$!
wait_for_server
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
# `error`.  The dot captures are the graph itself, asserted by label in
# `routes_graph.rs` (the port's dot emitter writes the same graph in a
# different dialect).  Their out-of-range `cases/<i>/<j>` 500s are captured by
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

# ---------------- Stubs (capture for documentation) ----------------
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
( cd "$BIGDIR" && tamarin-prover interactive --port="$PORT" --no-logging ./ ) >>/tmp/haskell-server.log 2>&1 &
SERVER_PID=$!
wait_for_server BigTermProved
fetch json_proof_abbrev.json    "/thy/trace/1/json/proof/done/_/Init/Init?abbrevInBackend=1"
rm -rf "$BIGDIR"

echo "done.  Captures live under: ${RES_DIR}"
kill "$SERVER_PID" 2>/dev/null || true
wait "$SERVER_PID" 2>/dev/null || true
