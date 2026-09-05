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
#                 ckey (theory + dependency shas + flags + ORACLE-BINARY FINGERPRINT) under
#                 .gate_cache/proof/. JOBS concurrent, -N$HS_N cores each.
#                 Timeout → cap-aware .timeout marker; unexplained empty output
#                 is never cached; the oracle's exit status
#                 is recorded beside the entry as .rc.
#   Phase 2 (RS): run RS on every file, diff against the cached HS output and
#                 compare RS's exit status against the recorded .rc.
#
# Env: FILE_TIMEOUT (per-file cap both sides, default 300s), JOBS (4),
#      HS_N (RTS cores/HS, 4), HS_MAXHEAP (GHC -M g, 11), DERIVCHECK_TIMEOUT
#      (30), CORPUS_ROOT, RESULTS_TSV, ALLOWLIST (file with one rel-path per
#      line; default = scripts/parity_corpus.txt, and only when that is missing
#      too, $PREV_TSV column 1).
# Output TSV (7 col, tab-sep): relpath  status  HS_lines  RS_lines  diffcount
#                              input_key  normalized_RS_sha256
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
CACHE="${CACHE:-$(shared_cache_dir "$repo_root" proof "$script_dir/.hs_file_cache")}" || exit 2
RESULTS_TSV="${RESULTS_TSV:-/tmp/corpus_file_diff.tsv}"
PREV_TSV="${PREV_TSV:-/tmp/corpus_file_diff.PREV.tsv}"
ALLOWLIST="${ALLOWLIST:-}"
mkdir -p "$CACHE"

HS_PATH=$(resolve_hs_oracle "$repo_root") || exit 2
[ -x "$HS_PATH" ] || { echo "no HS binary at $HS_PATH" >&2; exit 2; }
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
rs_stale_check "$RS_PATH" "$repo_root"
# Resolve and fingerprint one Maude for the whole run. It is passed explicitly
# to both provers; PATH is retained only for ancillary subprocesses.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"
oracle_rev_check "$HS_PATH" "$MAUDE" "$repo_root"
execution_fingerprint "$MAUDE" "$DERIVCHECK_TIMEOUT" || exit 2
# oracle_rev_check's binary fingerprint is folded into every
# cache key below.  Without it the key is sha256(theory)+flags, which cannot
# see the ORACLE changing: a rebuilt oracle keeps answering out of entries the
# previous one produced, and the gate certifies the port against an upstream
# that is no longer checked out.
export HS_PATH RS_PATH MAUDE FILE_TIMEOUT DERIVCHECK_TIMEOUT HS_RTS CACHE CORPUS_ROOT GATE_COMMON_DIR

export HS_FP HS_FP_PATH HS_FP_SALT EXEC_FP EXEC_FP_SALT MAUDE_FP MAUDE_FP_PATH

# strip_env (gate_common.sh): DELETE the four volatile header lines.
# Stripping `analyzed:` on BOTH sides means no cache path-rewrite is needed.
export -f strip_env

# --- per-file canonical flags (see file_flags.tsv) ---------------------------
# flags_for / ckey come from gate_common.sh: ckey salts the content-hash with
# a flags hash, so a flagged entry is a DISTINCT cache key from the bare one,
# and then with the oracle-binary fingerprint, so entries produced by a
# different oracle are a MISS rather than a stale hit.
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
export FLAGS_MAP
export -f flags_for file_sha256 parser_input_manifest manifest_encode manifest_normalize manifest_decode_into \
    input_manifest _include_shas_from_manifest \
    _oracle_shas_from_manifest input_content_key ckey cache_entry_lock \
    cache_entry_unlock cache_publish_text cache_publish_gzip cache_gzip_valid \
    cache_publish_proof \
    binary_sha256 binary_identity_unchanged execution_identity_unchanged \
    producer_identity_unchanged rs_identity_unchanged comparison_identity_unchanged

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
    local rel="$1" f="$CORPUS_ROOT/$1" key checked_key out rc fl old_cap old_seconds current_seconds lock_fd
    [ -f "$f" ] || return 0
    if ! key=$(ckey "$rel" "$f"); then
        echo "  INPUT MANIFEST FAILED  $rel" >&2
        return 0
    fi
    fl=$(flags_for "$rel")
    cache_entry_lock "$CACHE" "$key" lock_fd || return 0
    cache_gzip_valid "$CACHE/$key.full.gz" && { cache_entry_unlock "$lock_fd"; return 0; }
    if [ -f "$CACHE/$key.timeout" ]; then
        old_cap=$(cat "$CACHE/$key.timeout")
        old_seconds=$(duration_seconds "$old_cap") || old_seconds=
        current_seconds=$(duration_seconds "$FILE_TIMEOUT") || current_seconds=
        if [ -n "$old_seconds" ] && [ -n "$current_seconds" ] \
                && [ "$old_seconds" -ge "$current_seconds" ]; then
            cache_entry_unlock "$lock_fd"; return 0
        fi
        rm -f "$CACHE/$key.timeout"
    fi
    # Record the flags this entry was generated with, so the cache is
    # self-documenting (we don't "lose track" of what each file needs).
    # Only for flagged files — flagless entries stay clutter-free.
    # Run HS to a temp file so we capture `timeout`'s OWN exit code (124 on
    # timeout) — piping straight into strip_env would make $? reflect grep's
    # exit, misclassifying timeouts as empty (SKIP_NO_HS).
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    local tmp; tmp=$(mktemp)
    timeout "$FILE_TIMEOUT" "$HS_PATH" +RTS $HS_RTS -RTS \
            --with-maude="$MAUDE" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$f" >"$tmp" 2>/dev/null
    rc=$?
    out=$(strip_env < "$tmp"); rm -f "$tmp"
    # Never publish output under an identity computed before a concurrent
    # source edit. The next gate run will retry the now-current input.
    if ! checked_key=$(ckey "$rel" "$f") || [ "$checked_key" != "$key" ] \
            || ! producer_identity_unchanged; then
        echo "  INPUT CHANGED  $rel while Haskell was running — nothing cached" >&2
        cache_entry_unlock "$lock_fd"
        return 0
    fi
    # A signal death (the OOM killer's 137, an abort's 134) truncates stdout
    # the same way a timeout does, but caching it — payload OR marker — would
    # diff every later run against a truncated oracle, or skip the file
    # forever. Cache NOTHING, so the next run retries; until then Phase 2
    # reports SKIP_NO_HS, a failing verdict. (124, timeout(1)'s own status,
    # keeps its sticky .timeout marker below — same guard wf_gate.sh and
    # pretty_gate.sh apply to their load fills.)
    if [ "$rc" -ge 128 ]; then
        echo "  HS KILLED   $rel (rc=$rc, cap $FILE_TIMEOUT) — nothing cached" >&2
        cache_entry_unlock "$lock_fd"
        return 0
    fi
    # Record the oracle's exit status beside the entry, BEFORE the payload, so
    # `.full.gz exists` implies `.rc exists` for everything this run fills.
    # Phase 2 compares RS's status against it (RC_DIFF).
    if [ "$rc" = "124" ]; then
        [ -z "$fl" ] || cache_publish_text "$CACHE/$key.flags" "$fl" || true
        if ! cache_publish_text "$CACHE/$key.rc" "$rc" \
                || ! cache_publish_text "$CACHE/$key.timeout" "$FILE_TIMEOUT"; then
            echo "  CACHE WRITE FAILED  $rel — timeout not cached" >&2
            rm -f "$CACHE/$key.rc" "$CACHE/$key.timeout"
        fi
        echo "  HS TIMEOUT  $rel" >&2
    elif [ -z "$out" ]; then
        echo "  HS EMPTY!   $rel${fl:+  (flags: $fl)} — nothing cached" >&2
    else
        local normalized; normalized=$(mktemp)
        printf '%s' "$out" > "$normalized"
        [ -z "$fl" ] || cache_publish_text "$CACHE/$key.flags" "$fl" || true
        cache_publish_proof "$CACHE/$key.rc" "$CACHE/$key.full.gz" \
            "$rc" "$normalized" \
            || echo "  CACHE WRITE FAILED  $rel — proof not cached" >&2
        rm -f "$normalized"
    fi
    cache_entry_unlock "$lock_fd"
}
export -f duration_seconds hs_one

# --- Phase 2: RS + diff ---
# The first five columns retain the historical results contract. The final two
# bind a successful gate to the exact input and normalized proof bytes.
rs_result() { printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$@"; }
rs_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key checked_key input_key hs rs d rc fl out_sha
    [ -f "$f" ] || { rs_result "$rel" SKIP_NO_HS 0 0 0 - -; return 0; }
    if ! key=$(ckey "$rel" "$f"); then
        rs_result "$rel" SKIP_INPUT_MANIFEST 0 0 0 - -
        return 0
    fi
    input_key=${key%%__e*}
    fl=$(flags_for "$rel")
    if [ -f "$CACHE/$key.timeout" ]; then rs_result "$rel" SKIP_HS_TIMEOUT 0 0 0 "$input_key" -; return 0; fi
    if ! cache_gzip_valid "$CACHE/$key.full.gz"; then rs_result "$rel" SKIP_NO_HS 0 0 0 "$input_key" -; return 0; fi
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    local tmp; tmp=$(mktemp)
    timeout "$FILE_TIMEOUT" "$RS_PATH" --with-maude="$MAUDE" $fl --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove "$f" >"$tmp" 2>/dev/null
    rc=$?
    rs=$(strip_env < "$tmp"); rm -f "$tmp"
    if ! checked_key=$(ckey "$rel" "$f") || [ "$checked_key" != "$key" ] \
            || ! comparison_identity_unchanged; then
        rs_result "$rel" SKIP_INPUT_CHANGED 0 0 0 "$input_key" -
        return 0
    fi
    if [ "$rc" = "124" ]; then rs_result "$rel" SKIP_RS_TIMEOUT 0 0 0 "$input_key" -; return 0; fi
    out_sha=$(printf '%s\n' "$rs" | sha256sum | cut -d' ' -f1)
    hs=$(zcat "$CACHE/$key.full.gz")
    local hsn rsn
    hsn=$(printf '%s\n' "$hs" | wc -l)
    rsn=$(printf '%s\n' "$rs" | wc -l)
    d=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$rs") | grep -c '^[<>]')
    if [ "$d" != "0" ]; then rs_result "$rel" DIFF "$hsn" "$rsn" "$d" "$input_key" "$out_sha"; return 0; fi
    # Byte-identical stdout still leaves the EXIT STATUS uncompared, and a
    # caller that scripts either binary sees that status, not the bytes.
    # Entries filled before the .rc channel existed have no file: those count
    # as RC_UNKNOWN in the summary rather than failing, and they acquire an
    # .rc the next time the entry is (re)filled — e.g. after a bump, when the
    # fingerprinted key changes and Phase 1 runs the oracle again.
    local hsrc
    if [ -f "$CACHE/$key.rc" ] && hsrc=$(cat "$CACHE/$key.rc") && [ "$hsrc" != "$rc" ]; then
        echo "  RC DIFF     $rel  (HS exit $hsrc, RS exit $rc)" >&2
        rs_result "$rel" RC_DIFF "$hsn" "$rsn" 0 "$input_key" "$out_sha"; return 0
    fi
    rs_result "$rel" MATCH "$hsn" "$rsn" 0 "$input_key" "$out_sha"
}
export -f rs_result rs_one

mapfile -t FILES < <(filelist | grep .)
N=${#FILES[@]}
# Zero files is the whole-run form of comparing nothing: no rows, an empty
# summary, and a DONE line that reads exactly like a clean gate.
[ "$N" -gt 0 ] || { echo "the file list resolved to 0 entries — nothing to compare" >&2; exit 2; }
claim_output "$RESULTS_TSV" RESULTS_LOCK_FD || exit 2
echo "corpus_file_diff: $N files, JOBS=$JOBS, -N$HS_N, FILE_TIMEOUT=$FILE_TIMEOUT, cache=$CACHE"
echo "=== PHASE 1: Haskell (all files first, no RS) ==="
printf '%s\n' "${FILES[@]}" | xargs -P "$JOBS" -I{} bash -c 'hs_one "$@"' _ {}
echo "=== PHASE 2: Rust + diff ==="
printf '%s\n' "${FILES[@]}" | xargs -P "$JOBS" -I{} bash -c 'rs_one "$@"' _ {} >> "$RESULTS_TSV"
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
    if ! key=$(ckey "$rel" "$CORPUS_ROOT/$rel"); then
        rc_unknown=$((rc_unknown+1))
        continue
    fi
    [ -f "$CACHE/$key.rc" ] || rc_unknown=$((rc_unknown+1))
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
# Scope and proof digests come from the keys and normalized bytes actually used
# by Phase 2, not from a fresh post-run read of mutable source files.
scope_sha=$(awk -F'\t' '$2 !~ /^SKIP/ {print $1 "\t" $6}' "$RESULTS_TSV" \
    | LC_ALL=C sort | sha256sum | cut -d' ' -f1)
proof_sha=$(awk -F'\t' '$2 !~ /^SKIP/ {print $1 "\t" $6 "\t" $7}' "$RESULTS_TSV" \
    | LC_ALL=C sort | sha256sum | cut -d' ' -f1)
# files= is the count whose bytes were actually COMPARED (MATCH/DIFF/RC_DIFF;
# SKIP_* rows compared nothing). rs_ref_check.sh generate requires this exact
# scope and proof digest. Trailing fields preserve verdict-token consumers.
echo "DONE_CORPUS_FILE_DIFF verdict=${bad:-OK} files=$((rows - skips)) scope_sha256=$scope_sha proof_outputs_sha256=$proof_sha oracle_sha256=$HS_FP execution_sha256=$EXEC_FP"
[ -z "$bad" ]
