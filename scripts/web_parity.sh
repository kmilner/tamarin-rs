#!/usr/bin/env bash
# Web-parity gate: semantic (structural) equivalence of the interactive web
# server between HS (oracle) and the Rust port, across a corpus of theory
# files.  The web analogue of corpus_file_diff.sh.
#
# Per file, two strictly-sequential phases so HS and RS never contend:
#   Phase 1 (HS): boot `HS tamarin-prover interactive` on a temp workdir with
#                 the one theory, crawl it (web_crawl.py), cache the response
#                 manifest content-keyed by sha256(file) under .web_hs_cache/
#                 (plus web_crawl.py's PLAN_VERSION, so a manifest crawled
#                 under an older URL plan is re-crawled, not reused).
#   Phase 2 (RS): boot RS on the same workdir, crawl, diff (web_diff.py) the
#                 two manifests semantically (web_normalize.py) → per-url rows.
#
# Env: FILE_TIMEOUT (per-file cap, 300s), READY_TIMEOUT (server-boot wait, 90s),
#      HS_PORT (3021), RS_PORT (3022), CORPUS_ROOT (tamarin-prover/examples/),
#      ALLOWLIST (REQUIRED: one relpath/line, or the literal `seed` for the
#      built-in 2-file smoke list), RESULTS_TSV, MAX_NODES
#      (400), CACHE, DIFFDIR, HS_PATH, RS_PATH, MAUDE_PATH, DERIVCHECK_TIMEOUT
#      (both servers, 30s), SERVER_MEM_KB (per-server address-space cap,
#      24 GiB), TAM_RS_NO_AUTO_BUILD.
# Output TSV (6 col): file  url  status  hs_http  rs_http  kind
#   status ∈ MATCH | DIFF | MISSING_RS | MISSING_HS | SKIP_*
#
# Exit status reports VACUITY, not divergence. DIFF/MISSING_* rows are the
# run's findings and are triaged against the residual ledger by hand, so they
# leave the exit code alone; a file that produced no comparison at all (SKIP_*,
# or no rows whatsoever) is a failure, because a crawl that never happened is
# indistinguishable from a crawl that matched when all you read is the summary.
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"

FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
READY_TIMEOUT="${READY_TIMEOUT:-90}"
HS_PORT="${HS_PORT:-3021}"
RS_PORT="${RS_PORT:-3022}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE="${CACHE:-$script_dir/.web_hs_cache}"
RESULTS_TSV="${RESULTS_TSV:-/tmp/web_parity.tsv}"
MAX_NODES="${MAX_NODES:-400}"
DIFFDIR="${DIFFDIR:-/tmp/web_parity_diffs}"
mkdir -p "$CACHE"

# Crawl-plan version handshake.  The cache key is sha256(theory) alone, so it
# cannot see a crawl PLAN that has grown (see web_crawl.py's PLAN_VERSION):
# a manifest from an older plan lacks the new URL families, which surface as
# MISSING_HS rows rather than as a cache miss.  Import the constant rather than
# re-parse it, so the two sides cannot drift.
PLAN_VERSION="$(python3 -c \
    'import sys; sys.path.insert(0,sys.argv[1]); import web_crawl; print(web_crawl.PLAN_VERSION)' \
    "$script_dir")"
[ -n "$PLAN_VERSION" ] || { echo "cannot read PLAN_VERSION from web_crawl.py" >&2; exit 2; }

# Plan version of a cached HS manifest.  A stamp is authoritative.  An ABSENT
# stamp is NOT evidence of the current plan: stamping was introduced together
# with PLAN_VERSION 2, so a stampless manifest is a v1 or v2 crawl, and the two
# are told apart by CONTENT — v2 added the source-case routes, so it visits
# `json/cases/…` and `main/cases/…/1/1`, which a v1 crawl never requested.
# Missing either ⇒ 1, i.e. stale, so a cache predating the plan growth is
# re-crawled instead of surfacing its unvisited URL families as MISSING_HS.
# The probe never needs extending for a future plan: every crawl from v2 on
# stamps itself, so "stampless" can only ever mean "v1 or v2".  A manifest that
# fails to parse yields nothing and is likewise treated as stale.
cached_plan_version() {
    python3 -c '
import json, sys
sys.path.insert(0, sys.argv[2])
import web_crawl
d = json.load(open(sys.argv[1]))
v = d.get(web_crawl.PLAN_VERSION_KEY)
if v is None:
    urls = d.get("manifest", {})
    v = 2 if (any("/json/cases/" in u for u in urls)
              and any(u.endswith("/main/cases/raw/1/1") for u in urls)) else 1
print(v)' \
        "$1" "$script_dir" 2>/dev/null
}

find_hs_bin() {
    local c
    for c in "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin)}" || { echo "no HS binary" >&2; exit 2; }
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
MAUDE_PATH="${MAUDE_PATH:-$(command -v maude)}"

# Auto-build RS (opt out with TAM_RS_NO_AUTO_BUILD=1).
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    echo "building RS (release)..." >&2
    ( cd "$repo_root" && cargo build --release -q -p tamarin-prover ) || {
        echo "RS build failed" >&2; exit 2; }
fi
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }

# --- file list ---
# ALLOWLIST is mandatory. It used to fall back to the seed list whenever it was
# unset OR named a file that did not exist, so a typo in the path turned a
# corpus-wide certification into a 2-file smoke test that still printed a
# summary and DONE_WEB_PARITY — the run narrowed silently and read as a pass.
# The seed list is still reachable, but only by asking for it.
seed_list() {
    cat <<EOF
Tutorial.spthy
csf26-ac/fast/counter.spthy
EOF
}
filelist() {
    if [ "${ALLOWLIST:-}" = seed ]; then seed_list; return; fi
    cat "$ALLOWLIST"
}
if [ -z "${ALLOWLIST:-}" ]; then
    echo "ALLOWLIST is required: a file of corpus-relative theory paths, one per" >&2
    echo "line, or ALLOWLIST=seed for the built-in 2-file smoke list." >&2
    exit 2
fi
if [ "$ALLOWLIST" != seed ] && [ ! -r "$ALLOWLIST" ]; then
    echo "ALLOWLIST '$ALLOWLIST' is not a readable file" >&2
    exit 2
fi

# Boot a server, wait until it answers on / , run the crawl, then kill it
# (whole process group, to reap maude children).  Args: bin port workdir out.
boot_crawl() {
    local bin="$1" port="$2" wd="$3" out="$4" kind="$5"
    local log="$wd/${kind}_server.log" pid
    # Pin the derivcheck budget like corpus_file_diff.sh does (30s): HS's
    # 5s default expires deterministically on ~12 corpus files even idle,
    # replacing the derivation report with a timeout block RS never emits
    # (48 bogus DIFF rows in the 2026-07-05 sweep).  RS honours the flag on
    # its web path too: `run_interactive` writes it into `ServerConfig`, and
    # every theory load reads it from there.
    # OOM containment: the server (and the maude children that inherit
    # these settings) is the sacrificial process, not the session — a
    # theory whose source computation heap-exhausts (LAK06-class) must
    # die at the cap and yield a SKIP/MISSING row, never take the
    # machine down.  Same guards as wf_gate.sh / pretty_gate.sh.
    ( echo 1000 > /proc/self/oom_score_adj 2>/dev/null
      ulimit -v "${SERVER_MEM_KB:-25165824}" 2>/dev/null
      exec setsid "$bin" interactive "$wd/thy" --port="$port" \
        --derivcheck-timeout="${DERIVCHECK_TIMEOUT:-30}" ) >"$log" 2>&1 &
    pid=$!
    # wait for readiness
    local ok="" i
    for ((i=0; i<READY_TIMEOUT; i++)); do
        if curl -sf -o /dev/null "http://127.0.0.1:$port/"; then ok=1; break; fi
        kill -0 "$pid" 2>/dev/null || break
        sleep 1
    done
    if [ -z "$ok" ]; then
        echo "  $kind server not ready ($wd)" >&2
        kill -- -"$pid" 2>/dev/null; wait "$pid" 2>/dev/null
        return 1
    fi
    # shellcheck disable=SC2086  # CRAWL_EXTRA_ARGS must word-split
    timeout "$FILE_TIMEOUT" python3 "$script_dir/web_crawl.py" \
        "http://127.0.0.1:$port" "$out" --max-nodes "$MAX_NODES" ${CRAWL_EXTRA_ARGS:-} 2>>"$log"
    local rc=$?
    kill -- -"$pid" 2>/dev/null; wait "$pid" 2>/dev/null
    return $rc
}

one_file() {
    local rel="$1" f="$CORPUS_ROOT/$1"
    [ -f "$f" ] || { printf '%s\t-\tSKIP_NO_FILE\t-\t-\t-\n' "$rel"; return 0; }
    # A theory with no lemma declaration legitimately discovers 0 lemmas —
    # allow it; otherwise 0 discovered lemmas is a transient failure and
    # web_crawl.py exits 3 (→ SKIP_*_FAIL below, manifest never cached).
    local CRAWL_EXTRA_ARGS=""
    grep -qE '^[[:space:]]*(lemma|equivLemma|diffLemma)([[:space:]]|\[|:)' "$f" \
        || CRAWL_EXTRA_ARGS="--allow-no-lemmas"
    export CRAWL_EXTRA_ARGS
    local key; key=$(sha256sum "$f" | cut -d' ' -f1)
    local hs_manifest="$CACHE/$key.hs.json"
    local wd; wd=$(mktemp -d)
    mkdir -p "$wd/thy"; cp "$f" "$wd/thy/"
    # Oracle staging — three upstream resolution modes, all relative to the
    # theory dir at EXEC time (the servers' CWD-relative `<stem>.oracle`
    # existence probe can never hit inside a mktemp workdir, whose path
    # contains a `.`; the effective name is always the quoted one or the
    # plain-`oracle` fallback):
    #   1. sibling scripts `o "./oracle-…"` — the oracle* glob;
    #   2. an unnamed `o`/`O` ranking execs plain `oracle` in the theory
    #      dir — stage a `<stem>.oracle` sibling under that fallback name
    #      (upstream's default-oracle recipe, cf. regression/trace/);
    #   3. explicit relative refs (`o "../heuristic/oracle-…"`) — stage at
    #      the same relative location, which may sit BESIDE the thy dir.
    local __of __q
    for __of in "$(dirname "$f")"/oracle*; do
        [ -f "$__of" ] && cp "$__of" "$wd/thy/"
    done
    if [ -f "${f%.spthy}.oracle" ] && [ ! -e "$wd/thy/oracle" ]; then
        cp "${f%.spthy}.oracle" "$wd/thy/oracle"
    fi
    while IFS= read -r __q; do
        [ -f "$(dirname "$f")/$__q" ] || continue
        mkdir -p "$wd/thy/$(dirname "$__q")"
        cp "$(dirname "$f")/$__q" "$wd/thy/$__q"
    done < <(grep -E 'heuristic' "$f" | grep -oE '"[^"]+"' | tr -d '"' | sort -u)

    # Phase 1: HS (cached, and only while the cached crawl plan is current)
    if [ -f "$hs_manifest" ]; then
        local hs_plan; hs_plan=$(cached_plan_version "$hs_manifest")
        if [ "$hs_plan" != "$PLAN_VERSION" ]; then
            echo "  stale HS manifest (crawl plan ${hs_plan:-?} != $PLAN_VERSION) — re-crawling" >&2
            rm -f "$hs_manifest"
        fi
    fi
    if [ ! -f "$hs_manifest" ]; then
        if ! MAUDE_PATH="$MAUDE_PATH" boot_crawl "$HS_PATH" "$HS_PORT" "$wd" "$hs_manifest" hs; then
            rm -f "$hs_manifest"; rm -rf "$wd"
            printf '%s\t-\tSKIP_HS_FAIL\t-\t-\t-\n' "$rel"; return 0
        fi
    fi
    # Phase 2: RS
    local rs_manifest="$wd/rs.json"
    if ! boot_crawl "$RS_PATH" "$RS_PORT" "$wd" "$rs_manifest" rs; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_RS_FAIL\t-\t-\t-\n' "$rel"; return 0
    fi
    # diff. Both crawls succeeded, so an empty or absent parity.tsv means the
    # differ itself fell over — which used to emit no rows for the file at all,
    # a file that silently left the run rather than a file that matched.
    python3 "$script_dir/web_diff.py" "$hs_manifest" "$rs_manifest" \
        "$wd/parity.tsv" "$DIFFDIR/$rel" >/dev/null 2>&1
    if [ ! -s "$wd/parity.tsv" ]; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_DIFF_FAIL\t-\t-\t-\n' "$rel"; return 0
    fi
    # prefix each row with the file
    awk -F'\t' -v r="$rel" '{print r"\t"$0}' "$wd/parity.tsv"
    rm -rf "$wd"
}

echo "web_parity: HS=$HS_PATH" >&2
echo "web_parity: RS=$RS_PATH  maude=$MAUDE_PATH" >&2
mkdir -p "$(dirname "$RESULTS_TSV")"
: > "$RESULTS_TSV" || { echo "cannot write RESULTS_TSV '$RESULTS_TSV'" >&2; exit 2; }
N=$(filelist | grep -c .)
# Zero files is the whole-run form of comparing nothing: no rows, an empty
# summary, and a DONE line that looks exactly like a clean sweep.
[ "$N" -gt 0 ] || { echo "ALLOWLIST '$ALLOWLIST' has no entries — nothing to crawl" >&2; exit 2; }
i=0
while IFS= read -r rel; do
    [ -n "$rel" ] || continue
    i=$((i+1)); echo "[$i/$N] $rel" >&2
    one_file "$rel" >> "$RESULTS_TSV"
done < <(filelist | grep .)

echo "=== SUMMARY ===" >&2
awk -F'\t' '{c[$3]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$RESULTS_TSV" >&2
echo "  files: $N   results: $RESULTS_TSV   diffs: $DIFFDIR" >&2

# Verdict — vacuity only (see the header note): a SKIP_* row is a file whose
# panes were never compared, and a file that contributed no row at all left the
# run without being noticed. DIFF/MISSING_* rows are findings, not vacuity, and
# are triaged by hand against the residual ledger.
skipped=$(awk -F'\t' '$3 ~ /^SKIP_/' "$RESULTS_TSV" | grep -c .)
rowfiles=$(cut -f1 "$RESULTS_TSV" | sort -u | grep -c .)
bad=''
[ "$skipped" -gt 0 ] && bad="SKIPPED=$skipped"
if [ "$rowfiles" -ne "$N" ]; then
    bad="${bad:+$bad }NO-ROWS=$((N - rowfiles))/$N"
    echo "  $rowfiles of $N files produced rows — the rest were never compared" >&2
fi
[ -n "$bad" ] && awk -F'\t' '$3 ~ /^SKIP_/' "$RESULTS_TSV" | head -20 >&2
echo "DONE_WEB_PARITY verdict=${bad:-OK}" >&2
[ -z "$bad" ]
