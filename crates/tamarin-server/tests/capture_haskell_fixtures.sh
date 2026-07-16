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
  local status
  if [[ "$method" == "POST" ]]; then
    status=$(curl -sS -X POST -o "${RES_DIR}/${outfile}" -w "%{http_code}" "${BASE}${url}" 2>/dev/null || echo "ERR")
  elif [[ "$method" == "HEAD" ]]; then
    status=$(curl -sIo "${RES_DIR}/${outfile}" -w "%{http_code}" "${BASE}${url}" || echo "ERR")
  else
    status=$(curl -sS -o "${RES_DIR}/${outfile}" -w "%{http_code}" "${BASE}${url}" 2>/dev/null || echo "ERR")
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
fetch missing_idx_overview.html "/thy/trace/99/overview/help"

# ---------------- Stubs (capture for documentation) ----------------
fetch intdot.html               "/thy/trace/1/intdot/lemma/debug"
fetch graph.html                "/thy/trace/1/graph/lemma/debug"
fetch interactive_graph_def.html "/thy/trace/1/interactive-graph-def/lemma/debug"
fetch equiv_overview.json       "/thy/equiv/1/overview/help"

echo "done.  Captures live under: ${RES_DIR}"
kill "$SERVER_PID" 2>/dev/null || true
wait "$SERVER_PID" 2>/dev/null || true
