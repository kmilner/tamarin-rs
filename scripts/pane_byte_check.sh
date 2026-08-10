#!/usr/bin/env bash
# Byte-exact check of the interactive server's main/message + main/rules pane
# bodies (the JSON {html,title} envelope) against the HS reference cache
# (scripts/.web_hs_cache), content-keyed by sha256(file).  Boots RS per file
# (reusing web_parity's boot/crawl), then compares the two URL bodies byte-for-
# byte.  Each cached manifest carries a <key>.hs.fp sidecar naming the oracle
# binary (size.mtime) that crawled it — web_parity.sh stamps it and refuses to
# reuse a manifest that is unstamped or stamped by another binary, and this
# script honours the same contract (SKIP_STALE_CACHE): it cannot re-crawl the
# HS side, and a manifest from a long-gone oracle is not a reference.
#
#   scripts/pane_byte_check.sh <file-list>      (or ALLOWLIST=<file-list> ...)
#
# The file list is REQUIRED and has no default.  It used to default to
# scripts/websweep_residual.txt, which is the accepted-residue ledger — i.e.
# precisely the set where a DIFF is EXPECTED — so the default turned the gate
# below into a guaranteed red on a run nobody asked for.  Pass the corpus you
# actually mean to hold to byte parity.
#
# Output TSV: file  url  MATCH|DIFF|MISSING_*|SKIP_*  firstdiff_byte
# Exit status carries the verdict, which the DONE line repeats: nonzero on any
# DIFF, any MISSING_* (a pane one side never produced), any SKIP_* (a file whose
# bytes were never compared at all) and on any shortfall in the row count.
set -u
# OOM safeguards (per the campaign's oracle-script convention): make this driver
# the first OOM victim and cap the address space so a runaway prover subprocess
# cannot take the session down.
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 25165824 2>/dev/null || true
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
READY_TIMEOUT="${READY_TIMEOUT:-90}"
FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
RS_PORT="${RS_PORT:-3044}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE="${CACHE:-$script_dir/.web_hs_cache}"
RESULTS_TSV="${RESULTS_TSV:-/tmp/pane_byte.tsv}"
DIFFDIR="${DIFFDIR:-/tmp/pane_byte_diffs}"
MAX_NODES="${MAX_NODES:-400}"
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
MAUDE_PATH="${MAUDE_PATH:-$(command -v maude)}"
# Explicit only — a positional argument, or the ALLOWLIST env var. No default:
# see the header. An unset one is a run whose scope nobody chose.
ALLOWLIST="${1:-${ALLOWLIST:-}}"
mkdir -p "$DIFFDIR"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
# The HS pane bodies come EXCLUSIVELY from web_parity.sh's manifest cache, and
# each manifest's .hs.fp sidecar names the oracle that crawled it.  Verifying
# that stamp needs the oracle binary itself — required here even though only
# the RS server is ever booted, because without it a manifest crawled by a
# long-gone oracle would be compared as if it were the reference.
find_hs_bin() {
    local c
    for c in "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$repo_root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin)}" || true
[ -x "${HS_PATH:-/nonexistent}" ] || {
    echo "pane_byte_check: no HS oracle binary (set HS_PATH) — the cached HS" \
         "manifests carry the crawling oracle's fingerprint, which cannot be" \
         "verified without it" >&2
    exit 2
}
HS_FP=$(stat -c '%s.%Y' "$HS_PATH")
if [ -z "$ALLOWLIST" ]; then
    echo "usage: $0 <file-list>   (or ALLOWLIST=<file-list> $0)" >&2
    echo "pane_byte_check: no file list given, and there is no default —" \
         "scripts/websweep_residual.txt used to be it, and that is the set where" \
         "a DIFF is EXPECTED, not a corpus to hold to byte parity" >&2
    exit 2
fi
[ -f "$ALLOWLIST" ] || { echo "pane_byte_check: ALLOWLIST '$ALLOWLIST' does not exist" >&2; exit 2; }

# Wait (up to 30s) until nothing answers on the port — guards against a
# still-dying server from the previous file, which would make a bind-failed
# new server's crawl hit the STALE server (cross-theory contamination).
wait_port_free() {
    local port="$1" i
    for ((i=0; i<30; i++)); do
        curl -sf -o /dev/null "http://127.0.0.1:$port/" || return 0
        sleep 1
    done
    return 1
}

boot_crawl() {
    local bin="$1" port="$2" wd="$3" out="$4"
    local log="$wd/rs_server.log" pid ok="" i
    wait_port_free "$port" || { echo "  port $port not free before boot" >&2; return 1; }
    setsid "$bin" interactive "$wd/thy" --port="$port" \
        --derivcheck-timeout="${DERIVCHECK_TIMEOUT:-30}" >"$log" 2>&1 &
    pid=$!
    for ((i=0; i<READY_TIMEOUT; i++)); do
        curl -sf -o /dev/null "http://127.0.0.1:$port/" && { ok=1; break; }
        kill -0 "$pid" 2>/dev/null || break
        sleep 1
    done
    [ -z "$ok" ] && { kill -- -"$pid" 2>/dev/null; wait "$pid" 2>/dev/null; return 1; }
    timeout "$FILE_TIMEOUT" python3 "$script_dir/web_crawl.py" \
        "http://127.0.0.1:$port" "$out" --max-nodes "$MAX_NODES" ${CRAWL_EXTRA_ARGS:-} 2>>"$log"
    local rc=$?
    kill -- -"$pid" 2>/dev/null; wait "$pid" 2>/dev/null
    wait_port_free "$port" || true
    return $rc
}

one_file() {
    local rel="$1" f="$CORPUS_ROOT/$1"
    [ -f "$f" ] || { printf '%s\t-\tSKIP_NO_FILE\t-\n' "$rel"; return 0; }
    local key; key=$(sha256sum "$f" | cut -d' ' -f1)
    local hs_manifest="$CACHE/$key.hs.json"
    [ -f "$hs_manifest" ] || { printf '%s\t-\tSKIP_NO_CACHE\t-\n' "$rel"; return 0; }
    # Same reuse contract as web_parity.sh (which stamps the sidecar): a
    # manifest that is unstamped, or stamped by a different oracle binary, is
    # not this oracle's evidence.  web_parity re-crawls it; this script cannot
    # (it never boots the HS server), so the file SKIPs — a failing verdict —
    # rather than being compared against a reference nothing vouches for.
    local hs_fp=''
    [ -f "$CACHE/$key.hs.fp" ] && read -r hs_fp < "$CACHE/$key.hs.fp"
    if [ "$hs_fp" != "$HS_FP" ]; then
        printf '%s\t-\tSKIP_STALE_CACHE\t-\n' "$rel"; return 0
    fi
    local CRAWL_EXTRA_ARGS=""
    grep -qE '^[[:space:]]*(lemma|equivLemma|diffLemma)([[:space:]]|\[|:)' "$f" \
        || CRAWL_EXTRA_ARGS="--allow-no-lemmas"
    export CRAWL_EXTRA_ARGS
    local wd; wd=$(mktemp -d)
    mkdir -p "$wd/thy"; cp "$f" "$wd/thy/"
    # Oracle staging — keep in lockstep with web_parity.sh: sibling
    # oracle* glob, `<stem>.oracle` under the plain-`oracle` fallback
    # name, and quoted relative refs staged at their relative location.
    local __of __q
    for __of in "$(dirname "$f")"/oracle*; do [ -f "$__of" ] && cp "$__of" "$wd/thy/"; done
    if [ -f "${f%.spthy}.oracle" ] && [ ! -e "$wd/thy/oracle" ]; then
        cp "${f%.spthy}.oracle" "$wd/thy/oracle"
    fi
    while IFS= read -r __q; do
        [ -f "$(dirname "$f")/$__q" ] || continue
        mkdir -p "$wd/thy/$(dirname "$__q")"
        cp "$(dirname "$f")/$__q" "$wd/thy/$__q"
    done < <(grep -E 'heuristic' "$f" | grep -oE '"[^"]+"' | tr -d '"' | sort -u)
    if ! boot_crawl "$RS_PATH" "$RS_PORT" "$wd" "$wd/rs.json"; then
        rm -rf "$wd"; printf '%s\t-\tSKIP_RS_FAIL\t-\n' "$rel"; return 0
    fi
    python3 - "$rel" "$hs_manifest" "$wd/rs.json" "$DIFFDIR" <<'PY'
import json,sys,os
rel,hsp,rsp,diffdir=sys.argv[1:5]
hs=json.load(open(hsp))['manifest']; rs=json.load(open(rsp))['manifest']
for url in ['/thy/trace/#/main/message','/thy/trace/#/main/rules']:
    he=hs.get(url); re=rs.get(url)
    tag=url.split('/')[-1]
    if not he: print(f"{rel}\t{tag}\tMISSING_HS\t-"); continue
    if not re: print(f"{rel}\t{tag}\tMISSING_RS\t-"); continue
    hb=he.get('body',''); rb=re.get('body','')
    if hb==rb: print(f"{rel}\t{tag}\tMATCH\t-")
    else:
        fd=next((i for i in range(min(len(hb),len(rb))) if hb[i]!=rb[i]), min(len(hb),len(rb)))
        print(f"{rel}\t{tag}\tDIFF\t{fd}")
        safe=rel.replace('/','_')
        with open(os.path.join(diffdir,f"{safe}.{tag}.hs"),'w') as o: o.write(hb)
        with open(os.path.join(diffdir,f"{safe}.{tag}.rs"),'w') as o: o.write(rb)
PY
    rm -rf "$wd"
}

: > "$RESULTS_TSV"
# Comments and blanks dropped, duplicates collapsed, so N is exactly the number
# of files the loop will visit — the row-count check below is only as good as
# its denominator.
mapfile -t FILES < <(grep -v '^[[:space:]]*#' "$ALLOWLIST" | grep . | sort -u)
N=${#FILES[@]}
# Zero files is the whole-run form of comparing nothing: no rows, an empty
# histogram, and a verdict that reads exactly like a clean gate.
[ "$N" -gt 0 ] || { echo "pane_byte_check: '$ALLOWLIST' resolved to 0 entries — nothing to compare" >&2; exit 2; }
i=0
for rel in "${FILES[@]}"; do
    i=$((i+1)); echo "[$i/$N] $rel" >&2
    one_file "$rel" >> "$RESULTS_TSV"
done
echo "=== SUMMARY ===" >&2
awk -F'\t' '{c[$3]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$RESULTS_TSV" >&2
echo "  results: $RESULTS_TSV  diffs: $DIFFDIR" >&2

# Verdict — the histogram above is the whole story only if someone reads it,
# and every non-MATCH row here is a pane that was NOT shown to agree. DIFF and
# MISSING_* are findings; every SKIP_* is a file never compared at all (theory
# gone, no cached HS manifest, or the RS server never came up) — an absent
# .web_hs_cache/ turns the entire run into SKIP_NO_CACHE, which is the vacuous
# green this gate exists to refuse. A file that produced no row, or one pane row
# where two were due, is invisible in a histogram, so the counts are checked
# against the file list: two rows per file, except a SKIP_* file, which emits
# exactly one and is already a failure.
diffs=$(awk -F'\t' '$3=="DIFF"' "$RESULTS_TSV" | grep -c .)
missing=$(awk -F'\t' '$3 ~ /^MISSING_/' "$RESULTS_TSV" | grep -c .)
skips=$(awk -F'\t' '$3 ~ /^SKIP_/' "$RESULTS_TSV" | grep -c .)
rows=$(grep -c . "$RESULTS_TSV" 2>/dev/null) || rows=0
files=$(cut -f1 "$RESULTS_TSV" 2>/dev/null | sort -u | grep -c .) || files=0
expect=$((2 * N - skips))
bad=''
[ "$diffs" = 0 ] || bad="DIFF=$diffs"
[ "$missing" = 0 ] || bad="${bad:+$bad }MISSING=$missing"
[ "$skips" = 0 ] || bad="${bad:+$bad }SKIPPED=$skips"
[ "$files" = "$N" ] || bad="${bad:+$bad }FILE-COUNT=$files/$N"
[ "$rows" = "$expect" ] || bad="${bad:+$bad }ROW-COUNT=$rows/$expect"
echo "DONE_PANE_BYTE_CHECK verdict=${bad:-OK}"
[ -z "$bad" ]
