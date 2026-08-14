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
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root=$(dirname "$script_dir")
# Shared gate plumbing: OOM prologue, strip_env, flags_for/ckey, filelist,
# maude resolver.
[ -r "$script_dir/gate_common.sh" ] || { echo "wf_gate: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
oom_prologue
# Both provers resolve `maude` by NAME from PATH when no --with-maude is
# passed; the resolver honours the operator's MAUDE_PATH/PATH before falling
# back to this box's off-PATH linuxbrew install.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"
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
# Oracle-binary fingerprint (gate_common's hs_fingerprint), folded into every
# cache key: a rebuilt oracle must MISS, not answer out of the previous one's
# entries.  Loop-invariant, so taken once.
hs_fingerprint "$HS_PATH"
export RS_PATH HS_PATH HS_CACHE CORPUS_ROOT FLAGS_MAP FILE_TIMEOUT \
       HS_FILL_TIMEOUT DERIVCHECK_TIMEOUT HS_FP HS_FP_SALT

# strip_env (gate_common.sh): DELETE the four volatile header lines.
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
# flags_for / ckey come from gate_common.sh — one key format for this gate,
# pretty_gate.sh (whose cache this gate READS) and corpus_file_diff.sh.
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
    # 124 is timeout(1)'s SIGTERM; >=128 is any other signal death (the OOM
    # killer's 137, an abort's 134), which truncates stdout the same way.
    if [ "$rc" = 124 ] || [ "$rc" -ge 128 ]; then
        echo "  HS KILLED   $rel (rc=$rc, cap ${HS_FILL_TIMEOUT}s) — nothing cached" >&2; return 0
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

# gate_common's filelist: ALLOWLIST > parity_corpus.txt > this gate's
# fallback, the whole corpus tree.  allowlist_guard rejects a
# set-but-unreadable ALLOWLIST (a typo, not a request for the default).
allowlist_guard
filelist_fallback() { (cd "$CORPUS_ROOT" && find . -name '*.spthy' | sed 's|^\./||'); }

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
