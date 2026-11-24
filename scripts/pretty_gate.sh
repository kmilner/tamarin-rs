#!/usr/bin/env bash
# Fast full-corpus THEORY PRETTY-PRINT gate: diff the rendered `theory <name>
# begin … end` echo of every corpus theory against the Haskell oracle.
#
# The theory echo is emitted at theory-load time, so this runs WITHOUT
# `--prove` (~1s/file vs minutes) — fast enough to run on every build, and it
# is exactly the observable the pretty-printer produces on the batch path.
#
# WHY A DEDICATED NON-PROVE HS CACHE (scripts/.gate_cache/load) and NOT the
# batch --prove cache (scripts/.gate_cache/proof): the batch cache is `--prove`
# output, so each lemma there is followed by its full PROOF TREE (solve(...) …
# qed).  That proof text is SOLVER output, not pretty-printer surface, and it
# does not appear on the no-prove echo path (lemmas render `by sorry`).  To
# compare the pure Theory→text render — including the LEMMA/RESTRICTION FORMULA
# rendering — both sides must be no-prove.  So we keep a separate no-prove HS
# reference cache; it is auto-filled on first run (fast) and reused warm after.
# ckey / flags_for / strip_env come from gate_common.sh, so per-file canonical
# flags stay identical to the other gates.
#
# PHASE 0 also stores the whole stripped load-time stdout as <key>.load.gz.
# That is wf_gate.sh's reference: the wellformedness report is load-time output
# too, so one oracle load per file feeds both gates, and wf_gate no longer has
# to wait for corpus_file_diff.sh's 30-60 min `--prove` batch after a bump.
#
# Extraction (theory_block in gate_common.sh): keep `^theory ` … `^end$`; DROP
# the trailing formal-comment blocks tamarin appends inside that span — the
# wellformedness report (`/* All wellformedness checks were successful. */` OR
# the multi-line `/*\nWARNING …\n*/`, a SEPARATE slice owned by wf_gate.sh) and
# the volatile `/*\nGenerated from: …\n*/` build stamp — and everything after
# `end` (the summary-of-summaries, which carries processing time).  Interior
# comments (rule AC-variant blocks, `guarded formula characterizing …`) are
# KEPT: they are pretty-printer output.
#
# Env: RS_PATH, HS_PATH, HS_CACHE (dir), JOBS, FILE_TIMEOUT, DERIVCHECK_TIMEOUT,
#      RESULTS_TSV, ALLOWLIST, NO_HS_FILL (skip phase 0 if the cache is warm).
# Output TSV (3 col): relpath  MATCH|DIFF|SKIP_*  diffcount
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root=$(dirname "$script_dir")
# Shared gate plumbing: OOM prologue, strip_env, flags_for/ckey, filelist,
# maude resolver.
[ -r "$script_dir/gate_common.sh" ] || { echo "pretty_gate: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
oom_prologue
# Resolve one Maude and pass its exact path to both provers.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
HS_CACHE="${HS_CACHE:-$(shared_cache_dir "$repo_root" load "$script_dir/.hs_pretty_cache")}" || exit 2
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
JOBS="${JOBS:-4}"
# Generous by design: the csf26-ac AC-variant precomputation makes the HS
# oracle's plain load take ~170s on three files (chaum_offline_anonymity,
# KCL07, NSLPK3xor).  A tighter cap caches nothing for them, so they SKIP (a
# failing verdict) and every later cold fill pays the same 170s again.
FILE_TIMEOUT="${FILE_TIMEOUT:-420}"
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"  # 30 matches corpus_file_diff; lower values make HS's load-sensitive derivation checks time out under parallel fill, poisoning the shared load cache
RESULTS_TSV="${RESULTS_TSV:-$script_dir/results/pretty_gate_results.tsv}"
mkdir -p "$(dirname "$RESULTS_TSV")"
NO_HS_FILL="${NO_HS_FILL:-}"
mkdir -p "$HS_CACHE"

HS_PATH=$(resolve_hs_oracle "$repo_root") || exit 2
[ -x "$RS_PATH" ] || { echo "no RS binary at $RS_PATH" >&2; exit 2; }
rs_stale_check "$RS_PATH" "$repo_root"
# The oracle binary is required even under NO_HS_FILL: its fingerprint is part
# of the cache key, so without it no entry can be ADDRESSED, let alone filled.
[ -x "${HS_PATH:-/nonexistent}" ] || {
    echo "pretty_gate: no HS oracle binary (set HS_PATH) — the cache key carries the oracle's fingerprint, so entries cannot be looked up without it" >&2
    exit 2
}
export RS_PATH HS_PATH MAUDE HS_CACHE CORPUS_ROOT FLAGS_MAP FILE_TIMEOUT DERIVCHECK_TIMEOUT GATE_COMMON_DIR

# Oracle handshake. The dependency digest sees theory-side scripts, while the
# provenance check verifies the submodule pin and patch series. The binary's
# SHA-256 turns every distinct build into a cache miss per entry.
oracle_rev_check "$HS_PATH" "$MAUDE" "$repo_root"
execution_fingerprint "$MAUDE" "$DERIVCHECK_TIMEOUT" || exit 2
export HS_FP HS_FP_PATH HS_FP_SALT EXEC_FP EXEC_FP_SALT MAUDE_FP MAUDE_FP_PATH

# flags_for / ckey come from gate_common.sh — one key format for this gate,
# wf_gate.sh (which reads THIS cache) and corpus_file_diff.sh.
export -f file_sha256 strip_env theory_block slice_gate_one flags_for parser_input_manifest manifest_encode manifest_normalize \
    manifest_decode_into input_manifest \
    _include_shas_from_manifest _oracle_shas_from_manifest input_content_key ckey \
    cache_entry_lock cache_entry_unlock cache_publish_gzip cache_gzip_valid \
    hs_load_cache_fill \
    binary_sha256 binary_identity_unchanged execution_identity_unchanged \
    producer_identity_unchanged rs_identity_unchanged comparison_identity_unchanged

# A change to the slicer invalidates only its derived output.
THEORY_SLICE="theory-$(file_sha256 <(declare -f theory_block))" || exit 2
export THEORY_SLICE

hs_fill_one() {
    local rel="$1" f="$CORPUS_ROOT/$1" key fl lock_fd
    [ -f "$f" ] || return 0
    if ! key=$(ckey "$rel" "$f"); then
        echo "  INPUT MANIFEST FAILED  $rel" >&2
        return 0
    fi
    fl=$(flags_for "$rel")
    # `--diff` theories are not on the RS-matchable path; skip filling them.
    # Ahead of the derive step below, so a .load.gz wf_gate left here cannot
    # promote a diff theory into this gate's comparison set.
    case " $fl " in *" --diff "*) return 0;; esac
    cache_gzip_valid "$HS_CACHE/$key.$THEORY_SLICE.gz" \
        && cache_gzip_valid "$HS_CACHE/$key.load.gz" && return 0
    hs_load_cache_fill "$rel" "$f" "$key" "$fl" "$FILE_TIMEOUT"
    cache_entry_lock "$HS_CACHE" "$key" lock_fd || return 0
    if ! cache_gzip_valid "$HS_CACHE/$key.$THEORY_SLICE.gz" \
            && cache_gzip_valid "$HS_CACHE/$key.load.gz"; then
        local derived
        derived=$(mktemp) || { cache_entry_unlock "$lock_fd"; return 0; }
        zcat "$HS_CACHE/$key.load.gz" | theory_block > "$derived"
        if [ -s "$derived" ]; then
            cache_publish_gzip "$HS_CACHE/$key.$THEORY_SLICE.gz" "$derived" || true
        fi
        rm -f "$derived"
    fi
    cache_entry_unlock "$lock_fd"
}
export -f hs_fill_one

# --- Phase 1: RS no-prove + diff vs cached HS theory echo.
one() { slice_gate_one "$1" theory_block "$THEORY_SLICE"; }
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
claim_output "$RESULTS_TSV" RESULTS_LOCK_FD || exit 2
if [ -z "$NO_HS_FILL" ]; then
    echo "=== PHASE 0: fill missing no-prove HS theory cache ($HS_CACHE) ==="
    filelist | grep . | xargs -P"$JOBS" -I{} bash -c 'hs_fill_one "$@"' _ {}
fi
echo "=== PHASE 1: RS no-prove + diff ($N files) ==="
filelist | grep . | xargs -P"$JOBS" -I{} bash -c 'one "$@"' _ {} | sort > "$RESULTS_TSV"
m=$(awk -F'\t' '$2=="MATCH"' "$RESULTS_TSV" | wc -l)
diff=$(awk -F'\t' '$2=="DIFF"' "$RESULTS_TSV" | wc -l)
skip=$(awk -F'\t' '$2 ~ /^SKIP/' "$RESULTS_TSV" | wc -l)
total=$(grep -c . "$RESULTS_TSV")
echo "pretty_gate: MATCH=$m DIFF=$diff SKIP=$skip of $N  ->  $RESULTS_TSV"
# Every SKIP is a file that was not compared, so DIFF=0 covers only the rest of
# the list; at skip == total it covers nothing at all.  And a file that
# produced no row whatsoever is not even in `total`, so the run has to be
# measured against the DENOMINATOR it was asked for, not against itself.
bad=''
[ "$diff" = 0 ] || bad="DIFF=$diff"
[ "$skip" = 0 ] || bad="${bad:+$bad }SKIPPED=$skip/$total (never compared; unfilled HS cache $HS_CACHE)"
[ "$total" = "$N" ] || bad="${bad:+$bad }ROW-COUNT=$total/$N"
# files= is the count actually COMPARED (MATCH+DIFF; SKIPs compared nothing).
# rs_ref_check.sh generate reads it to refuse a scoped (ALLOWLIST) log as
# evidence for a wider re-baseline. Trailing and additive, so `grep verdict=`
# consumers are unchanged.
echo "pretty_gate: verdict=${bad:-OK} files=$((m + diff))"
[ -z "$bad" ]
