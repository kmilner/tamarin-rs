#!/usr/bin/env bash
# Capture the Haskell `tamarin-prover interactive` server's responses for
# every row of `tests/fixtures/server_responses.tsv`, the table that
# `tests/server_responses.rs` replays against the port.
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
#
# The table and this script share one reading (the table's header documents
# the columns):
#   - `SERVE <theory> [config]` stops the running oracle and serves that one
#     theory from a fresh work directory, so it is theory index 1.  The config
#     tokens are port-side harness tweaks; the oracle ignores them.
#   - every other row is one request, sent in file order to the current
#     server, so a stateful sequence (autoprove, then the index it allocated)
#     replays identically on both sides.
#   - the row's status and content type are checked against the oracle's
#     (a `diverge` row records the port's own; a `redirect` row only needs a
#     3xx), and a `contains:` row's lines must be in the oracle's body.
#   - the first row naming a capture writes it; every later row naming the
#     same capture must get the same bytes from the oracle.  A
#     `diverge:<other>` row's body must differ from `<other>`.
#
# Output: one file per named capture under tests/fixtures/haskell-responses/,
# plus `oracle_rev`, the submodule revision and patch series they were
# captured from.  `tests/capture_provenance.rs` checks both identities, so a
# source change that forgets to re-run this script fails the suite instead of
# silently pinning the port to a stale oracle.  The directory is replaced as a
# whole, so it holds exactly the captures the table names.

set -euo pipefail

PORT="${1:-18901}"
BASE="http://127.0.0.1:${PORT}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
RES_DIR="${SCRIPT_DIR}/fixtures/haskell-responses"
TABLE="${SCRIPT_DIR}/fixtures/server_responses.tsv"

[ -r "$ROOT/scripts/gate_common.sh" ] || {
  echo "error: missing scripts/gate_common.sh" >&2
  exit 2
}
# shellcheck source=../../../scripts/gate_common.sh
. "$ROOT/scripts/gate_common.sh"
[ -r "$ROOT/scripts/web_cache.sh" ] || {
  echo "error: missing scripts/web_cache.sh" >&2
  exit 2
}
# shellcheck source=../../../scripts/web_cache.sh
. "$ROOT/scripts/web_cache.sh"
HS_PATH=$(resolve_hs_oracle "$ROOT") || exit 2
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"

# Fixtures must come from the controlled build of the pin and current patch
# series, not an arbitrary binary that happens to have the same base commit.
oracle_rev_check "$HS_PATH" "$MAUDE" "$ROOT"
pin="$(git -C "$ROOT" rev-parse :tamarin-prover)"
patch_series="$(patch_series_fingerprint "$ROOT")" || exit 2

if ! web_port_free "$PORT"; then
  echo "error: port $PORT is already occupied; refusing to capture another service" >&2
  exit 2
fi
[ -r "$TABLE" ] || { echo "error: table $TABLE missing" >&2; exit 1; }

mkdir -p "$RES_DIR"
# Keep the completed capture beside the destination so GNU mv can atomically
# exchange the two directories without a cross-filesystem fallback.
CAPTURE_DIR="$(mktemp -d "${RES_DIR}.capture.XXXXXX")"
SCRATCH="$(mktemp -d)"
LOG="${SCRATCH}/haskell-server.log"
SERVER_PID=""

stop_server() {
  [ -n "$SERVER_PID" ] || return 0
  kill "$SERVER_PID" 2>/dev/null || true
  wait "$SERVER_PID" 2>/dev/null || true
  SERVER_PID=""
  if ! web_wait_port_free "$PORT"; then
    echo "error: port $PORT did not become free after stopping the oracle" >&2
    exit 1
  fi
}
trap 'stop_server; rm -rf "$CAPTURE_DIR" "$SCRATCH"' EXIT

# Poll the just-launched $SERVER_PID until it serves the root page; dump its
# log and give up otherwise.
wait_for_server() {
  local state
  for _ in {1..80}; do
    state=$(ps -o stat= -p "$SERVER_PID" 2>/dev/null || true)
    case "$state" in
      ''|*Z*)
        echo "error: Haskell server exited before becoming ready for $1" >&2
        cat "$LOG" >&2
        exit 1
        ;;
    esac
    if curl -fs -o /dev/null "$BASE/" 2>/dev/null; then
      return
    fi
    sleep 0.5
  done
  echo "error: Haskell server never came up for $1 on $BASE/" >&2
  cat "$LOG" >&2
  exit 1
}

# serve <line> <theory>: one fresh oracle serving <theory> (workspace-relative,
# or a bare name under tests/fixtures/) as its only theory.
serve() {
  local line=$1 theory=$2 src workdir
  case "$theory" in
    */*) src="${ROOT}/${theory}" ;;
    *) src="${SCRIPT_DIR}/fixtures/${theory}" ;;
  esac
  [ -f "$src" ] || fail "$line" "theory $src missing"
  stop_server
  workdir="$(mktemp -d "${SCRATCH}/serve.XXXXXX")"
  cp "$src" "$workdir/"
  ( cd "$workdir" && exec "$HS_PATH" interactive --port="$PORT" --no-logging ./ ) >>"$LOG" 2>&1 &
  SERVER_PID=$!
  wait_for_server "$theory"
  echo "line $line: serving $theory"
}

fail() {
  echo "error: line $1: $2" >&2
  exit 1
}

# request <line> <method> <path> <status> <content-type> <compare> <capture>
request() {
  local line=$1 method=$2 path=$3 status=$4 ctype=$5 compare=$6 capture=$7
  local body="${SCRATCH}/body" headers="${SCRATCH}/headers" got got_status got_ctype
  # `-sS` stays quiet but reports a transport failure; `--path-as-is` keeps
  # the bytes curl sends identical to the table's, which the Not Found page
  # echoes back.  No `-f`: a non-2xx body is a capture like any other.
  local opts=(-sS --path-as-is -o "$body" -D "$headers" -w '%{http_code}\t%{content_type}')
  case "$method" in
    GET) ;;
    POST) opts+=(-X POST) ;;
    UPLOAD:*)
      local file=${method#UPLOAD:}
      case "$file" in /*) ;; *) file="${ROOT}/${file}" ;; esac
      opts+=(-F "uploadedTheory=@${file};filename=$(basename "$file");type=text/plain")
      ;;
    *) fail "$line" "unknown method $method" ;;
  esac
  got=$(curl "${opts[@]}" "${BASE}${path}") || fail "$line" "$method $path: transport error"
  got_status=${got%%$'\t'*}
  got_ctype=${got#*$'\t'}
  printf '  %-4s %3s %-32s %s\n' "$line" "$got_status" "$got_ctype" "$path"

  case "$compare" in
    diverge*) ;;
    redirect)
      [[ "$got_status" == 3?? ]] || fail "$line" "$path: oracle answered $got_status, not a redirect"
      # The capture is the Location header's value.
      grep -i '^location:' "$headers" | head -n1 | sed 's/^[^:]*: *//' | tr -d '\r\n' > "$body"
      ;;
    *)
      [ "$got_status" = "$status" ] || fail "$line" "$path: oracle status $got_status, table says $status"
      if [ "$ctype" != - ] && [ "$got_ctype" != "$ctype" ]; then
        fail "$line" "$path: oracle content type '$got_ctype', table says '$ctype'"
      fi
      ;;
  esac
  case "$compare" in
    contains:*)
      local needle
      while IFS= read -r needle; do
        grep -qF -- "$needle" "$body" || fail "$line" "$path: oracle body lacks '$needle'"
      done < <(printf '%b\n' "${compare#contains:}")
      ;;
    diverge:*)
      local other="${CAPTURE_DIR}/${compare#diverge:}"
      [ -f "$other" ] || fail "$line" "diverge target ${compare#diverge:} is not captured above this row"
      if cmp -s "$body" "$other"; then
        fail "$line" "$path: the oracle now answers ${compare#diverge:}; this row no longer diverges"
      fi
      ;;
  esac

  [ "$capture" != - ] || return 0
  if [ -f "${CAPTURE_DIR}/${capture}" ]; then
    cmp -s "$body" "${CAPTURE_DIR}/${capture}" \
      || fail "$line" "$path: oracle body differs from $capture, which an earlier row captured"
  else
    mv "$body" "${CAPTURE_DIR}/${capture}"
  fi
}

lineno=0
while IFS= read -r raw || [ -n "$raw" ]; do
  lineno=$((lineno + 1))
  case "$raw" in ''|'#'*) continue ;; esac
  IFS=$'\t' read -r -a cols <<< "$raw"
  if [ "${cols[0]}" = SERVE ]; then
    serve "$lineno" "${cols[1]}"
    continue
  fi
  [ "${#cols[@]}" -eq 6 ] || fail "$lineno" "expected 6 tab-separated columns, got ${#cols[@]}"
  [ -n "$SERVER_PID" ] || fail "$lineno" "request before any SERVE row"
  request "$lineno" "${cols[@]}"
done < "$TABLE"
stop_server

# Stamp the oracle these bytes came from only after every request succeeds,
# then atomically exchange the complete capture with the committed directory.
# After the exchange CAPTURE_DIR names the old fixtures, which the EXIT trap
# removes. A failure or interruption before the exchange leaves them untouched;
# one after it leaves the complete new generation in place.
printf 'pin=%s\npatch_series_sha256=%s\n' "$pin" "$patch_series" \
  > "${CAPTURE_DIR}/oracle_rev"
mv --exchange --no-copy --no-target-directory "$CAPTURE_DIR" "$RES_DIR"

echo "done.  Captures live under: ${RES_DIR} (pin: $pin, patches: $patch_series)"
