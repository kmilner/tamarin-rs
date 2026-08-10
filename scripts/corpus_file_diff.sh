#!/usr/bin/env bash
# Full-FILE raw diff of HS vs RS `--prove <file>` (proves ALL lemmas in the
# file in one invocation — truest byte-identical metric, avoids per-lemma
# source recompute).
#
# SCOPE — this gate compares STDOUT ONLY; both sides send stderr to /dev/null.
# A MATCH here therefore says nothing about the progress/diagnostic stream, and
# the flag sweeps (which do compare stderr, via sweep_common.sh's `io_diff`)
# are what cover it. Measured exposure at theory-load time, 365 corpus files:
# 6 diverge on stderr, all in classes the sweep ledger already documents —
# stderr-saturating-sources (3), stderr-oracle-calls (2), stderr-open-chains
# (1). The `--prove` stream is wider than the load-time one (oracle-call blocks
# repeat per call) and has NOT been measured.
#
# Two strictly-sequential phases so HS and RS never contend:
#   Phase 1 (HS): run HS on every allowlisted file, cache stripped stdout by
#                 ckey (theory sha + flags + ORACLE-BINARY FINGERPRINT) under
#                 .hs_file_cache/.  JOBS concurrent, -N$HS_N cores each.
#                 Timeout → .timeout marker; empty/no output (diff theory /
#                 include fragment / error) → .nohs; the oracle's exit status
#                 is recorded beside the entry as .rc.
#   Phase 2 (RS): run RS on every file, diff against the cached HS output and
#                 compare RS's exit status against the recorded .rc.
#
# Env: FILE_TIMEOUT (per-file cap both sides, default 300s), JOBS (4),
#      HS_N (RTS cores/HS, 4), HS_MAXHEAP (GHC -M g, 11), DERIVCHECK_TIMEOUT
#      (30), CORPUS_ROOT, RESULTS_TSV, ALLOWLIST (file with one rel-path per
#      line; default = scripts/parity_corpus.txt, and only when that is missing
#      too, $PREV_TSV column 1).
# Output TSV (5 col, tab-sep): relpath  status  HS_lines  RS_lines  diffcount
#   status ∈ MATCH | DIFF | RC_DIFF | SKIP_HS_TIMEOUT | SKIP_NO_HS
#          | SKIP_RS_TIMEOUT
# Exit status carries the verdict, which the DONE line repeats: nonzero on any
# DIFF, on any RC_DIFF (identical stdout, different exit status), on any SKIP_*
# (a file whose bytes were never compared), and when fewer rows land than files
# were listed.
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
# Shared gate plumbing: OOM prologue, strip_env, flags_for/ckey, filelist,
# maude resolver.
[ -r "$script_dir/gate_common.sh" ] || { echo "corpus_file_diff: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
# Heavy-subprocess guard, the same discipline wf_gate.sh / pretty_gate.sh use:
# every HS/RS child inherits its own 24 GiB ceiling (verified: GHC's RTS falls
# back to a smaller reservation rather than failing to start under the cap).
oom_prologue

FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
JOBS="${JOBS:-4}"
HS_N="${HS_N:-4}"
HS_MAXHEAP="${HS_MAXHEAP:-11}"
HS_RTS="${HS_RTS:--N$HS_N -M${HS_MAXHEAP}g}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE="${CACHE:-$script_dir/.hs_file_cache}"
RESULTS_TSV="${RESULTS_TSV:-/tmp/corpus_file_diff.tsv}"
PREV_TSV="${PREV_TSV:-/tmp/corpus_file_diff.PREV.tsv}"
ALLOWLIST="${ALLOWLIST:-}"
mkdir -p "$CACHE"

find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin "$repo_root")}" || { echo "no HS binary" >&2; exit 2; }
[ -x "$HS_PATH" ] || { echo "no HS binary at $HS_PATH" >&2; exit 2; }
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
# Both provers resolve `maude` by NAME (RS probes /usr/local/bin and /usr/bin
# first, then PATH; HS searches PATH) — and a maude-less environment turns
# every Phase-1 oracle run into a sticky .nohs cache marker.  Resolve one
# maude for the whole run and put its directory on PATH for the children.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"
# Oracle-binary fingerprint (gate_common's hs_fingerprint), folded into every
# cache key below.  Without it the key is sha256(theory)+flags, which cannot
# see the ORACLE changing: a rebuilt oracle keeps answering out of entries the
# previous one produced, and the gate certifies the port against an upstream
# that is no longer checked out.  Loop-invariant, so taken once.
hs_fingerprint "$HS_PATH"
export HS_PATH RS_PATH FILE_TIMEOUT DERIVCHECK_TIMEOUT HS_RTS CACHE CORPUS_ROOT
export HS_FP HS_FP_SALT

# strip_env (gate_common.sh): DELETE the four volatile header lines.
# Stripping `analyzed:` on BOTH sides means no cache path-rewrite is needed.
export -f strip_env

# --- per-file canonical flags (see file_flags.tsv) ---------------------------
# flags_for / ckey come from gate_common.sh: ckey salts the content-hash with
# a flags hash, so a flagged entry is a DISTINCT cache key from the bare one,
# and then with the oracle-binary fingerprint, so entries produced by a
# different oracle are a MISS rather than a stale hit.
# Special token `@cd`: not a prover flag — run the prover from the file's
# OWN directory with the bare filename (upstream's deforacle recipe,
# Makefile:199-201: default-oracle lookup is cwd-relative). Stripped from
# the flag list before invocation; still salts the cache key.
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
export FLAGS_MAP
export -f flags_for ckey

# --- file list (allowlist) ---
# gate_common's filelist: explicit ALLOWLIST env > committed canonical corpus
# (scripts/parity_corpus.txt) > this gate's fallback, which derives from
# PREV_TSV or refuses.  allowlist_guard rejects a set-but-unreadable
# ALLOWLIST (a typo, not a request for the default).
allowlist_guard
filelist_fallback() {
    if [ -f "$PREV_TSV" ]; then
        cut -f1 "$PREV_TSV"
    else
        echo "no ALLOWLIST, no $script_dir/parity_corpus.txt, no $PREV_TSV to derive from" >&2; exit 2
    fi
}

# --- Phase 1: HS ---
hs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key out rc fl
    [ -f "$f" ] || return 0
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    [ -f "$CACHE/$key.full.gz" ] && return 0
    [ -f "$CACHE/$key.timeout" ] && return 0
    [ -f "$CACHE/$key.nohs" ] && return 0
    # Record the flags this entry was generated with, so the cache is
    # self-documenting (we don't "lose track" of what each file needs).
    # Only for flagged files — flagless entries stay clutter-free.
    [ -n "$fl" ] && printf '%s' "$fl" > "$CACHE/$key.flags"
    # Run HS to a temp file so we capture `timeout`'s OWN exit code (124 on
    # timeout) — piping straight into strip_env would make $? reflect grep's
    # exit, misclassifying timeouts as empty (SKIP_NO_HS).
    # `@cd` token: run from the file's directory with the bare filename.
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then
        fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f")
    fi
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$HS_PATH" +RTS $HS_RTS -RTS \
            $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$farg" ) >"$tmp" 2>/dev/null
    rc=$?
    out=$(strip_env < "$tmp"); rm -f "$tmp"
    # Record the oracle's exit status beside the entry, BEFORE the payload, so
    # `.full.gz exists` implies `.rc exists` for everything this run fills.
    # Phase 2 compares RS's status against it (RC_DIFF).
    printf '%s' "$rc" > "$CACHE/$key.rc"
    if [ "$rc" = "124" ]; then
        touch "$CACHE/$key.timeout"; echo "  HS TIMEOUT  $rel" >&2
    elif [ -z "$out" ]; then
        touch "$CACHE/$key.nohs"; echo "  HS EMPTY!   $rel${fl:+  (flags: $fl)}" >&2
    else
        printf '%s' "$out" | gzip > "$CACHE/$key.full.gz"
    fi
}
export -f hs_one

# --- Phase 2: RS + diff ---
rs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key hs rs d rc fl
    [ -f "$f" ] || { printf '%s\tSKIP_NO_HS\t0\t0\t0\n' "$rel"; return 0; }
    key=$(ckey "$rel" "$f"); fl=$(flags_for "$rel")
    if [ -f "$CACHE/$key.timeout" ]; then printf '%s\tSKIP_HS_TIMEOUT\t0\t0\t0\n' "$rel"; return 0; fi
    if [ ! -f "$CACHE/$key.full.gz" ]; then printf '%s\tSKIP_NO_HS\t0\t0\t0\n' "$rel"; return 0; fi
    # `@cd` token: run from the file's directory with the bare filename.
    local rundir="" farg="$f"
    if [[ " $fl " == *" @cd "* || "$fl" == "@cd" ]]; then
        fl=${fl//@cd/}; rundir=$(dirname "$f"); farg=$(basename "$f")
    fi
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    local tmp; tmp=$(mktemp)
    ( [ -n "$rundir" ] && cd "$rundir"
      timeout "$FILE_TIMEOUT" "$RS_PATH" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$farg" ) >"$tmp" 2>/dev/null
    rc=$?
    rs=$(strip_env < "$tmp"); rm -f "$tmp"
    if [ "$rc" = "124" ]; then printf '%s\tSKIP_RS_TIMEOUT\t0\t0\t0\n' "$rel"; return 0; fi
    hs=$(zcat "$CACHE/$key.full.gz")
    local hsn rsn
    hsn=$(printf '%s\n' "$hs" | wc -l)
    rsn=$(printf '%s\n' "$rs" | wc -l)
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" != "0" ]; then printf '%s\tDIFF\t%s\t%s\t%s\n' "$rel" "$hsn" "$rsn" "$d"; return 0; fi
    # Byte-identical stdout still leaves the EXIT STATUS uncompared, and a
    # caller that scripts either binary sees that status, not the bytes.
    # Entries filled before the .rc channel existed have no file: those count
    # as RC_UNKNOWN in the summary rather than failing, and they acquire an
    # .rc the next time the entry is (re)filled — e.g. after a bump, when the
    # fingerprinted key changes and Phase 1 runs the oracle again.
    local hsrc
    if [ -f "$CACHE/$key.rc" ] && hsrc=$(cat "$CACHE/$key.rc") && [ "$hsrc" != "$rc" ]; then
        echo "  RC DIFF     $rel  (HS exit $hsrc, RS exit $rc)" >&2
        printf '%s\tRC_DIFF\t%s\t%s\t0\n' "$rel" "$hsn" "$rsn"; return 0
    fi
    printf '%s\tMATCH\t%s\t%s\t0\n' "$rel" "$hsn" "$rsn"
}
export -f rs_one

N=$(filelist | grep -c .)
# Zero files is the whole-run form of comparing nothing: no rows, an empty
# summary, and a DONE line that reads exactly like a clean gate.
[ "$N" -gt 0 ] || { echo "the file list resolved to 0 entries — nothing to compare" >&2; exit 2; }
echo "corpus_file_diff: $N files, JOBS=$JOBS, -N$HS_N, FILE_TIMEOUT=${FILE_TIMEOUT}s, cache=$CACHE"
echo "=== PHASE 1: Haskell (all files first, no RS) ==="
filelist | grep . | xargs -P "$JOBS" -I{} bash -c 'hs_one "$@"' _ {}
echo "=== PHASE 2: Rust + diff ==="
: > "$RESULTS_TSV"
filelist | grep . | xargs -P "$JOBS" -I{} bash -c 'rs_one "$@"' _ {} >> "$RESULTS_TSV"
sort -o "$RESULTS_TSV" "$RESULTS_TSV"
echo "=== SUMMARY ==="
awk -F'\t' '{c[$2]++} END{for(k in c) printf "  %-18s %d\n", k, c[k]}' "$RESULTS_TSV"
# Of the files whose bytes WERE compared, how many had no recorded oracle exit
# status to compare against.  Not a failure: it is what a cache filled before
# the .rc channel existed looks like, and each such entry backfills the first
# time Phase 1 refills it.  Reported so the number cannot quietly be 432.
rc_unknown=0
while IFS=$'\t' read -r rel st _; do
    case "$st" in MATCH|DIFF|RC_DIFF) ;; *) continue;; esac
    [ -f "$CORPUS_ROOT/$rel" ] || continue
    [ -f "$CACHE/$(ckey "$rel" "$CORPUS_ROOT/$rel").rc" ] || rc_unknown=$((rc_unknown+1))
done < "$RESULTS_TSV"
printf '  %-18s %d\n' "RC_UNKNOWN" "$rc_unknown"
echo "  results: $RESULTS_TSV"
# Verdict — the histogram above is the whole story only if someone reads it.
# A SKIP_* row is a file whose bytes were never compared (no HS reference, or
# either side out of time), an RC_DIFF row matched on bytes but not on exit
# status, and a file that produced no row at all left the run unnoticed; all
# three are indistinguishable from MATCH in an exit status of 0.
diffs=$(awk -F'\t' '$2=="DIFF"' "$RESULTS_TSV" | grep -c .)
rcdiffs=$(awk -F'\t' '$2=="RC_DIFF"' "$RESULTS_TSV" | grep -c .)
skips=$(awk -F'\t' '$2 ~ /^SKIP/' "$RESULTS_TSV" | grep -c .)
rows=$(grep -c . "$RESULTS_TSV")
bad=''
[ "$diffs" = 0 ] || bad="DIFF=$diffs"
[ "$rcdiffs" = 0 ] || bad="${bad:+$bad }RC_DIFF=$rcdiffs"
[ "$skips" = 0 ] || bad="${bad:+$bad }SKIPPED=$skips"
[ "$rows" = "$N" ] || bad="${bad:+$bad }ROW-COUNT=$rows/$N"
echo "DONE_CORPUS_FILE_DIFF verdict=${bad:-OK}"
[ -z "$bad" ]
