#!/usr/bin/env bash
# Fast full-corpus WELLFORMEDNESS gate: diff the wf WARNING block of every
# corpus theory against the Haskell oracle.  The wf report is emitted at
# theory-load time, so this runs WITHOUT `--prove` (~1s/file vs minutes) —
# fast enough to run on every build.
#
# REFERENCE SIDE: the no-prove LOAD cache (scripts/.hs_pretty_cache), whose
# <key>.load.gz holds the oracle's whole stripped theory-load stdout.
# pretty_gate.sh PHASE 0 writes it; this gate slices the wf block out of it,
# and PHASE 0 here fills any entry that is missing — one oracle LOAD per file,
# so a cold cache costs minutes.  It used to read corpus_file_diff.sh's
# `--prove` cache instead, which meant that after every bump this gate could
# compare nothing until that 30-60 min batch had refilled it.  .hs_file_cache
# stays the `--prove` gate's own cache.
#
# The RS side is whatever binary RS_PATH points at (default: the release
# build); a sealed-side harness that emits the same theory-load output can be
# gated the same way by setting RS_PATH.
#
# Env: RS_PATH, HS_PATH, HS_CACHE (dir), JOBS, FILE_TIMEOUT, HS_FILL_TIMEOUT,
#      RESULTS_TSV, ALLOWLIST, NO_HS_FILL (skip PHASE 0 on a known-warm cache).
# Output TSV (3 col): relpath  MATCH|DIFF|SKIP_*  diffcount
set -u
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 25165824 2>/dev/null || true

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(dirname "$script_dir")
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
HS_CACHE="${HS_CACHE:-$script_dir/.hs_pretty_cache}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
JOBS="${JOBS:-4}"
FILE_TIMEOUT="${FILE_TIMEOUT:-120}"
# The oracle side gets its own, far more generous cap: the csf26-ac AC-variant
# precomputation makes a PLAIN oracle load take ~170s on three files
# (chaum_offline_anonymity, KCL07, NSLPK3xor).  A cap that cuts those caches
# nothing for them, so they SKIP (a failing verdict) and every later run pays
# the same 170s again.
HS_FILL_TIMEOUT="${HS_FILL_TIMEOUT:-420}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"  # 30 matches corpus_file_diff; lower values make HS's load-sensitive derivation checks time out under parallel fill, poisoning the shared load cache
RESULTS_TSV="${RESULTS_TSV:-$script_dir/results/wf_gate_results.tsv}"
NO_HS_FILL="${NO_HS_FILL:-}"
mkdir -p "$(dirname "$RESULTS_TSV")" "$HS_CACHE"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }

find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin "$repo_root")}" || true
# Required even under NO_HS_FILL: the oracle binary's fingerprint is part of
# the cache key, so without it no entry can be ADDRESSED, let alone filled.
[ -x "${HS_PATH:-/nonexistent}" ] || {
    echo "wf_gate: no HS oracle binary (set HS_PATH) — the cache key carries the oracle's fingerprint, so entries cannot be looked up without it" >&2
    exit 2
}
# Oracle-binary fingerprint (sweep_common.sh:262's recipe), folded into every
# cache key: a rebuilt oracle must MISS, not answer out of the previous one's
# entries.  Loop-invariant, so taken once.
HS_FP=$(stat -c '%s.%Y' "$HS_PATH")
HS_FP_SALT=$(printf '%s' "$HS_FP" | sha256sum | cut -c1-12)
export RS_PATH HS_PATH HS_CACHE CORPUS_ROOT FLAGS_MAP FILE_TIMEOUT \
       HS_FILL_TIMEOUT DERIVCHECK_TIMEOUT HS_FP HS_FP_SALT

strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
# Isolate the wf report: either the success line, or the WARNING block that
# opens the leading theory comment (up to its closing `*/`).
wf_block() {
    awk '
        /^\/\* All wellformedness checks were successful\. \*\/$/ { print; next }
        /^WARNING: the following wellformedness checks failed!$/  { f=1 }
        f { print }
        f && /^\*\/$/ { f=0 }
    '
}
flags_for() { [ -f "$FLAGS_MAP" ] && awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"; }
# KEY FORMAT — identical to pretty_gate.sh's ckey (this gate READS the cache
# pretty_gate.sh writes) and to corpus_file_diff.sh's:
#   <sha256(theory)>[__f<12 hex of sha256(flags)>]__b<12 hex of sha256(HS_FP)>
ckey() {
    local h fl; h=$(sha256sum "$2" | cut -d' ' -f1); fl=$(flags_for "$1")
    if [ -n "$fl" ]; then h="${h}__f$(printf '%s' "$fl" | sha256sum | cut -c1-12)"; fi
    printf '%s__b%s' "$h" "$HS_FP_SALT"
}
export -f strip_env wf_block flags_for ckey

# --- PHASE 0: fill any MISSING <key>.load.gz with one oracle LOAD.
# Same artifact and same key pretty_gate.sh PHASE 0 writes, so whichever gate
# runs first on a cold cache pays for it once and the other finds it warm.
# The guard discipline is the script-level one at the top (oom_score_adj +
# ulimit -v, both inherited per child) plus this timeout; JOBS bounds how many
# oracles are in flight.
hs_fill_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key fl
    [ -f "$f" ] || return 0
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$HS_CACHE/$key.load.gz" ] && return 0
    # `.nohs` is pretty_gate.sh's sticky "the oracle gave nothing here" marker
    # (also set for the RS-unported --diff theories); honour it rather than
    # re-running the oracle on every invocation.
    [ -f "$HS_CACHE/$key.nohs" ] && return 0
    # `--diff` theories are not on the RS-matchable path (RS errors "not yet
    # ported"), so both gates skip them — set the marker pretty_gate.sh sets,
    # so the outcome does not depend on which gate reached the key first.
    case " $fl " in *" --diff "*) touch "$HS_CACHE/$key.nohs"; return 0;; esac
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f"); fi
    local tmp load rc; tmp=$(mktemp)
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$HS_FILL_TIMEOUT" "$HS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" "$farg" ) >"$tmp" 2>/dev/null
    rc=$?
    load=$(strip_env < "$tmp"); rm -f "$tmp"
    # A killed load leaves PARTIAL stdout, which is worse than none: cached, it
    # is a reference both gates would diff against forever.  Cache nothing and
    # leave no marker — the file reports SKIP (a failing verdict) and is
    # retried, instead of reporting a DIFF against a truncated oracle.
    if [ "$rc" = 124 ]; then
        echo "  HS TIMEOUT  $rel (${HS_FILL_TIMEOUT}s) — nothing cached" >&2; return 0
    fi
    if [ -z "$load" ]; then
        touch "$HS_CACHE/$key.nohs"; echo "  HS EMPTY!   $rel${fl:+  (flags: $fl)}" >&2; return 0
    fi
    printf '%s' "$load" | gzip > "$HS_CACHE/$key.load.gz"
}
export -f hs_fill_one

one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key fl hs rs d
    [ -f "$f" ] || { printf '%s\tSKIP_NO_HS\t0\n' "$rel"; return 0; }
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$HS_CACHE/$key.load.gz" ] || { printf '%s\tSKIP_NO_HS\t0\n' "$rel"; return 0; }
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* ]]; then fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f"); fi
    hs=$(zcat "$HS_CACHE/$key.load.gz" | strip_env | wf_block)
    # RS: theory-load only (NO --prove) so the wf block prints fast.
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$RS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" "$farg" ) >"$tmp" 2>/dev/null
    if [ "$?" = "124" ]; then rm -f "$tmp"; printf '%s\tSKIP_RS_TIMEOUT\t0\n' "$rel"; return 0; fi
    rs=$(strip_env < "$tmp" | wf_block); rm -f "$tmp"
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" = 0 ]; then printf '%s\tMATCH\t0\n' "$rel"; else printf '%s\tDIFF\t%s\n' "$rel" "$d"; fi
}
export -f one

# A set-but-unreadable ALLOWLIST is a typo, not a request for the default: it
# used to fall through to the whole 432-file corpus, so the run silently
# stopped being the one that was asked for.
if [ -n "${ALLOWLIST:-}" ] && [ ! -r "$ALLOWLIST" ]; then
    echo "ALLOWLIST '$ALLOWLIST' is not a readable file" >&2; exit 2
fi
filelist() {
    if [ -n "${ALLOWLIST:-}" ]; then cat "$ALLOWLIST"
    elif [ -f "$script_dir/parity_corpus.txt" ]; then cat "$script_dir/parity_corpus.txt"
    else (cd "$CORPUS_ROOT" && find . -name '*.spthy' | sed 's|^\./||'); fi
}

N=$(filelist | grep -c .)
# Zero files is the whole-run form of comparing nothing: no rows, MATCH=DIFF=0,
# and a verdict line that reads exactly like a clean gate.
[ "$N" -gt 0 ] || { echo "the file list resolved to 0 entries — nothing to compare" >&2; exit 2; }
if [ -z "$NO_HS_FILL" ]; then
    echo "=== PHASE 0: fill missing no-prove HS load cache ($HS_CACHE) ==="
    filelist | grep . | xargs -P"$JOBS" -I{} bash -c 'hs_fill_one "$@"' _ {}
fi
echo "=== PHASE 1: RS no-prove + wf diff ($N files) ==="
filelist | grep . | xargs -P"$JOBS" -I{} bash -c 'one "$@"' _ {} | sort > "$RESULTS_TSV"
m=$(awk -F'\t' '$2=="MATCH"' "$RESULTS_TSV" | wc -l)
diff=$(awk -F'\t' '$2=="DIFF"' "$RESULTS_TSV" | wc -l)
skip=$(awk -F'\t' '$2 ~ /^SKIP/' "$RESULTS_TSV" | wc -l)
total=$(grep -c . "$RESULTS_TSV")
echo "wf_gate: MATCH=$m DIFF=$diff SKIP=$skip of $N  ->  $RESULTS_TSV"
# Every SKIP is a file whose wf block was never compared — DIFF=0 then covers
# only the rest of the list, and at skip == total it covers nothing at all.
# A file that produced no row whatsoever is not even in `total`, so the run is
# measured against the DENOMINATOR it was asked for rather than against itself.
bad=''
[ "$diff" = 0 ] || bad="DIFF=$diff"
[ "$skip" = 0 ] || bad="${bad:+$bad }SKIPPED=$skip (never compared; PHASE 0 left $HS_CACHE unfilled — check for .nohs markers)"
[ "$total" = "$N" ] || bad="${bad:+$bad }ROW-COUNT=$total/$N"
echo "wf_gate: verdict=${bad:-OK}"
[ -z "$bad" ]
