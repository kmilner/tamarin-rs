#!/usr/bin/env bash
# Web-parity gate: semantic (structural) equivalence of the interactive web
# server between HS (oracle) and the Rust port, across a corpus of theory
# files.  The web analogue of corpus_file_diff.sh.
#
# Per file, two strictly-sequential phases so HS and RS never contend:
#   Phase 1 (HS): boot `HS tamarin-prover interactive` on a temp workdir with
#                 the one theory, crawl it (web_crawl.py), cache the response
#                 manifest under an oracle/settings profile; source identity
#                 includes transitive includes and oracle scripts.
#   Phase 2 (RS): boot RS on the same workdir, crawl, diff (web_diff.py) the
#                 two manifests semantically (web_normalize.py) → per-url rows.
#
# Env: FILE_TIMEOUT (per-file cap, 300s), READY_TIMEOUT (server-boot wait, 90s),
#      HS_PORT (3021), RS_PORT (3022), CORPUS_ROOT (tamarin-prover/examples/),
#      ALLOWLIST (REQUIRED: one relpath/line, or the literal `seed` for the
#      built-in 2-file smoke list), RESULTS_TSV, MAX_NODES
#      (400), WEB_CACHE_ROOT, CACHE (exact legacy override), DIFFDIR, HS_PATH,
#      RS_PATH, MAUDE_PATH, DERIVCHECK_TIMEOUT
#      (both servers, 30s), SERVER_MEM_KB (per-server address-space cap,
#      24 GiB), TAM_RS_NO_AUTO_BUILD, WEB_LEDGER (residue ledger, or the
#      literal `none`), FAIL_ON_CAPPED.
# Output TSV (7 col): file  url  status  hs_http  rs_http  kind  class
#   status ∈ MATCH | LEDGERED | DIFF | MISSING_RS | MISSING_HS | CAPPED_* | SKIP_*
#   class  = the ledger class of a LEDGERED row, `-` on every other row
#
# The verdict fails on DIVERGENCE and on VACUITY:
#   UNDOCUMENTED  a DIFF/MISSING_* row that no entry of the residue ledger
#                 (websweep_ledger.tsv) excuses. Documented residue is rewritten
#                 to LEDGERED by apply_web_ledger below, so whatever still reads
#                 DIFF/MISSING_* afterwards is new — a server regression.
#   LEDGER,       a ledger entry that excused nothing — STALE or SHADOWED for a
#   LEDGER-       file this run compared, UNMATCHED for a path that has left the
#   UNMATCHED     corpus. Either way a mask waiting for a file to regress
#                 under it.
#   SKIPPED,      a file whose panes were never compared, or that contributed no
#   NO-COMPARE    comparison row at all. A crawl that never happened is
#                 indistinguishable from a crawl that matched when all you read
#                 is the summary.
# CAPPED_* rows (web_crawl.py truncated a crawl at MAX_NODES proof nodes) are
# always printed on the verdict line, so a truncated sweep cannot read as a
# complete one; they fail the run only under FAIL_ON_CAPPED=1.
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
# Shared gate plumbing (gate_common.sh): maude resolver, the oracle
# fingerprint recipe.  (The OOM guards here live inside boot_crawl, per
# server, with their own SERVER_MEM_KB cap.)
[ -r "$script_dir/gate_common.sh" ] || { echo "web_parity: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"

FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
READY_TIMEOUT="${READY_TIMEOUT:-90}"
HS_PORT="${HS_PORT:-3021}"
RS_PORT="${RS_PORT:-3022}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
WEB_FLAGS_MAP="${WEB_FLAGS_MAP:-$script_dir/web_flags.tsv}"
[ -r "$WEB_FLAGS_MAP" ] || { echo "web flag map is not readable: $WEB_FLAGS_MAP" >&2; exit 2; }
RESULTS_TSV="${RESULTS_TSV:-/tmp/web_parity.tsv}"
MAX_NODES="${MAX_NODES:-400}"
DIFFDIR="${DIFFDIR:-/tmp/web_parity_diffs}"
LEDGER="${WEB_LEDGER:-$script_dir/websweep_ledger.tsv}"
LEDGER_REPORTS=0

# Crawl-plan version handshake. The version participates in the cache profile
# and remains stamped inside each manifest as defence in depth. Import the
# constant rather than re-parsing it, so the two sides cannot drift.
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

HS_PATH=$(resolve_hs_oracle "$repo_root") || exit 2
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
# Both servers probe `maude` by name; resolve one (MAUDE_PATH > PATH >
# linuxbrew, hard fail otherwise) and put its directory on PATH for them.
MAUDE_PATH=$(resolve_maude) || exit 2
maude_on_path "$MAUDE_PATH"

# Refuse an oracle that was not built by setup.sh from the pinned submodule and
# current patch series. The binary SHA-256 also keys the general gate caches;
# web_cache.sh folds it into a profile shared with pane_byte_check.sh.
oracle_rev_check "$HS_PATH" "$MAUDE_PATH" "$repo_root"
[ -r "$script_dir/web_cache.sh" ] || { echo "web_parity: missing $script_dir/web_cache.sh" >&2; exit 2; }
. "$script_dir/web_cache.sh"
web_cache_init "$repo_root" "$script_dir" "$HS_PATH" "$PLAN_VERSION" \
    || { echo "web_parity: cannot select HS web cache" >&2; exit 2; }

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
# Blank lines and `#` comments are dropped here, in the ONE place the row count
# and the crawl loop both read, so the two cannot disagree about how many files
# the run covers.  websweep_ledger.tsv is not a file list: fed in as ALLOWLIST
# its rows resolve to no theory and the run fails on SKIPPED, loudly.
filelist() {
    if [ "${ALLOWLIST:-}" = seed ]; then seed_list; return; fi
    grep -v '^[[:space:]]*#' "$ALLOWLIST" | grep .
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

# --- residue ledger ---
# Checked BEFORE the crawl: a ledger the gate cannot parse would otherwise be
# discovered an hour later, at the one moment the run's findings depend on it.
# A missing ledger is an error rather than "no residue documented", which would
# fail every documented row as a fresh divergence; WEB_LEDGER=none says so
# explicitly, and then every DIFF/MISSING_* row is undocumented by definition.
if [ "$LEDGER" != none ] && [ ! -r "$LEDGER" ]; then
    echo "WEB_LEDGER '$LEDGER' is not a readable file (WEB_LEDGER=none runs" >&2
    echo "without one, and then every DIFF/MISSING_* row fails the verdict)" >&2
    exit 2
fi
check_ledger() {
    [ "$LEDGER" = none ] && return 0
    awk -F'\t' -v f="$LEDGER" '
      /^[[:space:]]*#/ || /^[[:space:]]*$/ { next }
      {
        if (NF < 3 || $1 == "" || $2 == "" || $3 == "") {
          printf "%s:%d: need path<TAB>class<TAB>symptom[<TAB>note]\n", f, FNR > "/dev/stderr"
          bad = 1; next
        }
        if ($3 !~ /^(any|none|DIFF|MISSING_RS|MISSING_HS)$/) {
          printf "%s:%d: symptom \"%s\" is not any|none|DIFF|MISSING_RS|MISSING_HS\n", \
                 f, FNR, $3 > "/dev/stderr"
          bad = 1
        }
        if (($1 SUBSEP $3) in seen) {
          printf "%s:%d: %s %s is listed twice — only one entry could ever match\n", \
                 f, FNR, $1, $3 > "/dev/stderr"
          bad = 1
        }
        seen[$1 SUBSEP $3] = 1
      }
      END { exit (bad ? 2 : 0) }' "$LEDGER"
}
check_ledger || { echo "web_parity: malformed ledger '$LEDGER'" >&2; exit 2; }

# An entry whose theory is not in the corpus AT ALL can never be reported stale
# by the post-run pass (it produces no rows in any run, however large), so it
# would sit in the ledger forever. That is a property of the ledger, not of this
# run's ALLOWLIST, so it is checked here against CORPUS_ROOT and reported even
# on a 2-file smoke run.
ledger_dead=0
if [ "$LEDGER" != none ]; then
    while IFS= read -r p; do
        [ -f "$CORPUS_ROOT/$p" ] && continue
        echo "LEDGER-UNMATCHED: $p is not in the corpus under $CORPUS_ROOT — drop its entry" >&2
        ledger_dead=$((ledger_dead + 1))
    done < <(grep -v '^[[:space:]]*#' "$LEDGER" | cut -f1 | grep . | sort -u)
fi

# Boot a server, wait until it answers on / , run the crawl, then kill it
# (whole process group, to reap maude children).  Args: bin port workdir out.
boot_crawl() {
    local bin="$1" port="$2" wd="$3" out="$4" kind="$5"
    local log="$wd/${kind}_server.log" pid
    local -a load_flags=()
    [ -z "${theory_flags:-}" ] || read -r -a load_flags <<< "$theory_flags"
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
        --derivcheck-timeout="${DERIVCHECK_TIMEOUT:-30}" "${load_flags[@]}" ) >"$log" 2>&1 &
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
    local theory_flags
    if ! theory_flags=$(web_flags_for "$rel"); then
        printf '%s\t-\tSKIP_UNSUPPORTED_FLAGS\t-\t-\t-\n' "$rel"
        return 0
    fi
    local key
    if ! key=$(web_cache_key "$rel" "$f" "$theory_flags"); then
        printf '%s\t-\tSKIP_INPUT_MANIFEST\t-\t-\t-\n' "$rel"
        return 0
    fi
    local hs_manifest="$CACHE/$key.hs.json" hs_fp_file="$CACHE/$key.hs.fp"
    local wd; wd=$(mktemp -d)
    mkdir -p "$wd/thy"
    if ! web_stage_inputs "$f" "$wd/thy" "$theory_flags" "$wd"; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_INPUT_STAGE\t-\t-\t-\n' "$rel"; return 0
    fi

    # Phase 1: HS (cached, and only while the cached crawl plan AND the oracle
    # that produced the manifest are the current ones).  A manifest with no
    # fingerprint sidecar was crawled before the stamp existed, by an oracle
    # nothing recorded — indistinguishable from one crawled by a stale binary,
    # so it is re-crawled rather than trusted.
    if ! web_cache_lock "$key"; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_CACHE_LOCK\t-\t-\t-\n' "$rel"; return 0
    fi
    web_cache_adopt_legacy "$key" "$f" "$PLAN_VERSION" || true
    if [ -f "$hs_manifest" ]; then
        local hs_plan; hs_plan=$(cached_plan_version "$hs_manifest")
        if [ "$hs_plan" != "$PLAN_VERSION" ]; then
            echo "  stale HS manifest (crawl plan ${hs_plan:-?} != $PLAN_VERSION) — re-crawling" >&2
            web_cache_invalidate "$key"
        fi
    fi
    if [ -f "$hs_manifest" ]; then
        local hs_fp=''
        [ -f "$hs_fp_file" ] && read -r hs_fp < "$hs_fp_file"
        if ! web_cache_stamp_matches "$hs_fp"; then
            echo "  stale HS manifest (oracle ${hs_fp:-unstamped} != $WEB_CACHE_ORACLE_STAMP) — re-crawling" >&2
            web_cache_invalidate "$key"
        fi
    fi
    if [ ! -f "$hs_manifest" ]; then
        if ! MAUDE_PATH="$MAUDE_PATH" boot_crawl "$HS_PATH" "$HS_PORT" "$wd" "$wd/hs-new.json" hs; then
            web_cache_unlock; rm -rf "$wd"
            printf '%s\t-\tSKIP_HS_FAIL\t-\t-\t-\n' "$rel"; return 0
        fi
        if ! web_cache_publish "$key" "$wd/hs-new.json"; then
            web_cache_unlock; rm -rf "$wd"
            printf '%s\t-\tSKIP_CACHE_WRITE\t-\t-\t-\n' "$rel"; return 0
        fi
    fi
    if ! cp "$hs_manifest" "$wd/hs.json"; then
        web_cache_unlock; rm -rf "$wd"
        printf '%s\t-\tSKIP_CACHE_READ\t-\t-\t-\n' "$rel"; return 0
    fi
    web_cache_unlock
    # Phase 2: RS
    local rs_manifest="$wd/rs.json"
    if ! boot_crawl "$RS_PATH" "$RS_PORT" "$wd" "$rs_manifest" rs; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_RS_FAIL\t-\t-\t-\n' "$rel"; return 0
    fi
    # diff. Both crawls succeeded, so an empty or absent parity.tsv means the
    # differ itself fell over — which used to emit no rows for the file at all,
    # a file that silently left the run rather than a file that matched.
    python3 "$script_dir/web_diff.py" "$wd/hs.json" "$rs_manifest" \
        "$wd/parity.tsv" "$DIFFDIR/$rel" >/dev/null 2>&1
    if [ ! -s "$wd/parity.tsv" ]; then
        rm -rf "$wd"
        printf '%s\t-\tSKIP_DIFF_FAIL\t-\t-\t-\n' "$rel"; return 0
    fi
    # prefix each row with the file
    awk -F'\t' -v r="$rel" '{print r"\t"$0}' "$wd/parity.tsv"
    rm -rf "$wd"
}

# apply_web_ledger <results.tsv>
#   Applied to the whole run AFTER the rows land, not per file: an entry is
#   stale or shadowed only relative to everything the run saw.
#   Every row gains a 7th column — the ledger class of a LEDGERED row, `-`
#   elsewhere — so the TSV has one shape whether or not a ledger is in use.
#   A DIFF/MISSING_* row is rewritten to LEDGERED when an entry for its file
#   matches: the file-wide `any` entry first, then the entry naming exactly this
#   status. MATCH/SKIP_*/CAPPED_* rows are never ledgerable — an entry documents
#   a divergence that WAS observed, and those rows observed agreement, a failure
#   to compare, or a truncation.
#   Entries that excused nothing are reported on stderr and counted into
#   LEDGER_REPORTS, which the verdict folds in:
#     LEDGER-STALE     its file WAS compared and no row of it matched.
#     LEDGER-SHADOWED  a narrower entry under an `any` entry for the same path;
#                      it can never match, so it can never go stale either.
#   An entry whose file this run did not compare is out of scope, not dead: it
#   is counted on one line rather than reported, so a 2-file smoke run does not
#   read as 77 rotten entries. The one out-of-scope case that IS always dead —
#   a path that has left the corpus — is caught before the crawl, against
#   CORPUS_ROOT (ledger_dead above).
apply_web_ledger() {
    local out=$1 led=$LEDGER rep
    LEDGER_REPORTS=0
    [ "$led" = none ] && led=/dev/null
    rep=$(mktemp) || return 1
    if awk -F'\t' -v OFS='\t' -v ledger="$led" '
      BEGIN {
        while ((getline line < ledger) > 0) {
          if (line ~ /^[[:space:]]*#/ || line ~ /^[[:space:]]*$/) continue
          split(line, a, "\t")
          if (a[3] == "" || a[3] == "none") continue
          cls[a[1] SUBSEP a[3]] = a[2]
        }
      }
      $3 == "MATCH" || $3 == "DIFF" || $3 == "MISSING_RS" || $3 == "MISSING_HS" \
        { compared[$1] = 1 }
      {
        if ($3 == "DIFF" || $3 == "MISSING_RS" || $3 == "MISSING_HS") {
          k = $1 SUBSEP "any"
          if (!(k in cls)) k = $1 SUBSEP $3
          if (k in cls) { hit[k] = 1; $3 = "LEDGERED"; print $0, cls[k]; next }
        }
        print $0, "-"
      }
      END {
        for (k in cls) {
          if (k in hit) continue
          split(k, kk, SUBSEP)
          if (!(kk[1] in compared)) { oos++; continue }
          if (kk[2] != "any" && (kk[1] SUBSEP "any") in cls)
            print "LEDGER-SHADOWED: " kk[1] " " kk[2] " can never match — the" \
                  " file-wide `any` entry takes every row" > "/dev/stderr"
          else
            print "LEDGER-STALE: " kk[1] " " kk[2] " excused nothing this run" \
                  " — drop or re-classify its entry" > "/dev/stderr"
        }
        if (oos > 0)
          printf "ledger: %d entry/entries out of scope for this run (their files were not compared)\n", \
                 oos > "/dev/stderr"
      }' "$out" 2> "$rep" > "$out.ledgered"; then
        mv "$out.ledgered" "$out"
    else
        # The rows keep their DIFF/MISSING_* status, so the verdict still fails
        # on them — but a run whose ledger never ran must say so rather than
        # report the residue as undocumented and leave the cause offscreen.
        rm -f "$out.ledgered"
        echo "LEDGER-ERROR: the ledger pass failed — no row was ledgered" >> "$rep"
    fi
    cat "$rep" >&2
    # Only the LEDGER-* reports are findings; the out-of-scope tally is not.
    LEDGER_REPORTS=$(grep -c '^LEDGER-' "$rep")
    rm -f "$rep"
}

echo "web_parity: HS=$HS_PATH  fp=$HS_FP" >&2
echo "web_parity: RS=$RS_PATH  maude=$MAUDE_PATH" >&2
echo "web_parity: HS-cache=$CACHE  mode=$WEB_CACHE_MODE" >&2
echo "web_parity: ledger=$LEDGER" >&2
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

apply_web_ledger "$RESULTS_TSV"

echo "=== SUMMARY ===" >&2
awk -F'\t' '{c[$3]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$RESULTS_TSV" >&2
awk -F'\t' '$3 == "LEDGERED" {c[$7]++}
            END{for(k in c) printf "  ledgered[%s] %d\n", k, c[k]}' "$RESULTS_TSV" >&2
echo "  files: $N   results: $RESULTS_TSV   diffs: $DIFFDIR" >&2

# Verdict — divergence AND vacuity (see the header note).
#   undoc      a DIFF/MISSING_* row the ledger pass did not excuse: the port and
#              the oracle disagree somewhere nobody has written down.
#   skipped    a file whose panes were never compared.
#   cmpfiles   files that produced a COMPARISON row. A file present only through
#              a SKIP_* or CAPPED_* row contributed no comparison, so counting
#              distinct files in column 1 would let it pass for one.
#   LEDGER_*   entries that excuse nothing (see apply_web_ledger) and entries
#              whose theory has left the corpus (ledger_dead, checked up front).
undoc=$(awk -F'\t' '$3 == "DIFF" || $3 == "MISSING_RS" || $3 == "MISSING_HS"' \
        "$RESULTS_TSV" | grep -c .)
skipped=$(awk -F'\t' '$3 ~ /^SKIP_/' "$RESULTS_TSV" | grep -c .)
capped=$(awk -F'\t' '$3 ~ /^CAPPED_/' "$RESULTS_TSV" | grep -c .)
cmpfiles=$(awk -F'\t' '$3 == "MATCH" || $3 == "LEDGERED" || $3 == "DIFF" ||
                       $3 == "MISSING_RS" || $3 == "MISSING_HS" {print $1}' \
           "$RESULTS_TSV" | sort -u | grep -c .)
bad=''
if [ "$undoc" -gt 0 ]; then
    bad="UNDOCUMENTED=$undoc"
    echo "  $undoc undocumented divergence row(s) — ledger them or fix the port:" >&2
    awk -F'\t' '$3 == "DIFF" || $3 == "MISSING_RS" || $3 == "MISSING_HS"' \
        "$RESULTS_TSV" | head -20 >&2
fi
[ "$skipped" -gt 0 ] && bad="${bad:+$bad }SKIPPED=$skipped"
if [ "$cmpfiles" -ne "$N" ]; then
    bad="${bad:+$bad }NO-COMPARE=$((N - cmpfiles))/$N"
    echo "  $cmpfiles of $N files produced a comparison row — the rest compared nothing" >&2
fi
[ "$LEDGER_REPORTS" -gt 0 ] && bad="${bad:+$bad }LEDGER=$LEDGER_REPORTS"
[ "$ledger_dead" -gt 0 ] && bad="${bad:+$bad }LEDGER-UNMATCHED=$ledger_dead"
if [ "$capped" -gt 0 ]; then
    echo "  $capped crawl(s) truncated at MAX_NODES=$MAX_NODES — those files were" >&2
    echo "  compared only down to the cap:" >&2
    awk -F'\t' '$3 ~ /^CAPPED_/ {print "    " $1 "\t" $3}' "$RESULTS_TSV" | head -20 >&2
    [ "${FAIL_ON_CAPPED:-0}" = 1 ] && bad="${bad:+$bad }CAPPED=$capped"
fi
[ "$skipped" -gt 0 ] && awk -F'\t' '$3 ~ /^SKIP_/' "$RESULTS_TSV" | head -20 >&2
echo "DONE_WEB_PARITY verdict=${bad:-OK} capped=$capped" >&2
[ -z "$bad" ]
