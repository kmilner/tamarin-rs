#!/usr/bin/env bash
# Byte-exact check of the interactive server's main/message + main/rules pane
# bodies (the JSON {html,title} envelope) against the HS reference cache
# (scripts/.web_hs_cache), content-keyed by sha256(file).  Boots RS per file
# (reusing web_parity's boot/crawl), then compares the two URL bodies byte-for-
# byte.  Output TSV: file  url  MATCH|DIFF|MISSING_*  firstdiff_byte
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
mkdir -p "$DIFFDIR"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }

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
N=$(grep -c . "$ALLOWLIST"); i=0
while IFS= read -r rel; do
    [ -n "$rel" ] || continue
    i=$((i+1)); echo "[$i/$N] $rel" >&2
    one_file "$rel" >> "$RESULTS_TSV"
done < <(grep . "$ALLOWLIST")
echo "=== SUMMARY ===" >&2
awk -F'\t' '{c[$3]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$RESULTS_TSV" >&2
echo "  results: $RESULTS_TSV  diffs: $DIFFDIR" >&2
