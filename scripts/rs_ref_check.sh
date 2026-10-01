#!/usr/bin/env bash
# Reference-output gate for CI: compare ONE Rust binary's stripped --prove
# stdout against a committed, oracle-certified TSV of output hashes. The
# reference side is frozen into a file: a PR runner only builds and runs its
# own binary, so the job fits a slow GitHub runner.
#
#   scripts/rs_ref_check.sh generate --certified-by <gate-results>
#                                      # run BIN, WRITE the reference (manual)
#   scripts/rs_ref_check.sh check      # run BIN, DIFF against the reference;
#                                      # nonzero exit on any mismatch (CI)
#
# The reference is a BASELINE: every later `check` measures against it, so
# rewriting it turns whatever this binary does today into the definition of
# correct. Nothing in this script compares against the Haskell prover, so on its
# own `generate` would launder a regression into the baseline. Hence
# --certified-by <gate-results>: the saved output of an ORACLE gate run whose
# final verdict line is corpus_file_diff.sh's DONE_CORPUS_FILE_DIFF, reads OK,
# and carries the exact relpath/input-key scope and normalized proof-output
# aggregate being baselined — a
# same-sized but different allowlist proves nothing about this corpus. Its
# path, its verdict and the fingerprint of the oracle binary on this machine
# (checked against the submodule pin and current patch series) are stamped into the reference
# header beside `# maude:`, so the committed baseline carries the evidence
# that an oracle run justified it.
#
# Reference rows: relpath \t input_key \t output_sha256 \t lines
#   input_key = full SHA-256 of the tagged theory/include/oracle/flags identity,
#   so a submodule bump, dependency edit or flag change shows up as
#   INPUT_CHANGED ("regenerate the reference"), never as a silent false DIFF.
#
# Cross-machine determinism: prover parallelism is pinned via EXTRA_FLAGS
# (default --processors=4 --maude-processes=4) so a 4-core runner and a
# 24-core workstation execute the same schedule.  Maude version must match
# the one recorded in the reference header (unifier enumeration order can
# differ between Maude versions).
#
# Env: BIN (default target/release/tamarin-rs), REF (default
#      scripts/ci_ref_fast.tsv), ALLOWLIST (default
#      scripts/parity_corpus_fast.txt), FLAGS_MAP, CORPUS, TIMEOUT (120),
#      DERIV (30), JOBS, EXTRA_FLAGS, HS_PATH (the oracle binary whose
#      fingerprint `generate` stamps; found under tamarin-prover-testing/ if
#      unset)
set -u
# Exported: a bare assignment reaches none of the children, so `sort` collated
# the committed reference in the operator's locale and every regenerate on a
# differently-configured box re-ordered the whole ledger.
export LC_ALL=C

usage() {
    echo "usage: $0 generate --certified-by <gate-results>" >&2
    echo "       $0 check" >&2
}
MODE="${1:-}"
case "$MODE" in generate|check) shift ;; *) usage; exit 2;; esac
CERT=''
while [ $# -gt 0 ]; do
    case "$1" in
        --certified-by)
            [ $# -ge 2 ] || { echo "rs_ref_check: --certified-by needs a path" >&2; exit 2; }
            CERT="$2"; shift 2 ;;
        --certified-by=*) CERT="${1#*=}"; shift ;;
        # An argument this script does not understand is a request it is not
        # honouring; ignoring it would run something other than what was asked.
        *) echo "rs_ref_check: unknown argument '$1'" >&2; usage; exit 2 ;;
    esac
done

# Shared gate plumbing (gate_common.sh): OOM prologue, strip_env, flags_for,
# maude resolver, the oracle fingerprint recipe.
[ -r "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh" ] || { echo "rs_ref_check: missing $(dirname "${BASH_SOURCE[0]}")/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh"
# OOM discipline (see rs_vs_rs_diff.sh): provers die alone, not the session.
oom_prologue

ROOT="${ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
CORPUS="${CORPUS:-$ROOT/tamarin-prover/examples}"
BIN="${BIN:-$ROOT/target/release/tamarin-rs}"
REF="${REF:-$ROOT/scripts/ci_ref_fast.tsv}"
ALLOWLIST="${ALLOWLIST:-$ROOT/scripts/parity_corpus_fast.txt}"
FLAGS_MAP="${FLAGS_MAP:-$ROOT/scripts/file_flags.tsv}"
TIMEOUT="${TIMEOUT:-120}"
DERIV="${DERIV:-30}"
cores=$(nproc 2>/dev/null || echo 4)
JOBS="${JOBS:-$(( cores >= 24 ? 4 : cores >= 12 ? 2 : 1 ))}"
EXTRA_FLAGS="${EXTRA_FLAGS---processors=4 --maude-processes=4}"
export CORPUS BIN FLAGS_MAP TIMEOUT DERIV EXTRA_FLAGS GATE_COMMON_DIR

[ -x "$BIN" ] || { echo "rs_ref_check: no executable prover at '$BIN' (set BIN=)" >&2; exit 2; }
rs_stale_check "$BIN" "$ROOT"
[ -f "$ALLOWLIST" ] || { echo "rs_ref_check: ALLOWLIST '$ALLOWLIST' does not exist" >&2; exit 2; }
# One maude for the run (MAUDE_PATH > PATH > linuxbrew, hard fail otherwise);
# its directory goes on PATH so BIN's by-name probe finds the same binary the
# version handshake below inspects.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"
export MAUDE
if [ "$MODE" = generate ]; then
    # Checked BEFORE the sweep runs: refusing an unjustified re-baseline after
    # an hour of prover time would just teach the operator to keep the flag
    # handy rather than to have the evidence.
    [ -n "$CERT" ] || {
        echo "rs_ref_check: generate requires --certified-by <gate-results> — the saved" \
             "output of an oracle gate run (verdict=OK) that justifies this baseline." \
             "Without it this script only certifies the binary against itself." >&2
        exit 2; }
    [ -f "$CERT" ] || { echo "rs_ref_check: --certified-by '$CERT' does not exist" >&2; exit 2; }
    # Last verdict line wins: a saved log may hold several (a phase banner, a
    # retry), and the one that concludes the run is the one that certifies it.
    CERT_LINE=$(grep 'verdict=' "$CERT" | tail -1)
    [ -n "$CERT_LINE" ] || {
        echo "rs_ref_check: '$CERT' carries no 'verdict=' line — that is not a gate result" >&2
        exit 2; }
    # Only the proof-output differential certifies proof-output hashes. A
    # wf/pretty/sweep OK covers a different output surface.
    case "$CERT_LINE" in
        'DONE_CORPUS_FILE_DIFF verdict='*) ;;
        *)
            echo "rs_ref_check: '$CERT' does not end in the proof-output gate sentinel" \
                 "DONE_CORPUS_FILE_DIFF; wf/pretty/sweep results do not certify proof hashes;" \
                 "its last verdict line is: $CERT_LINE" >&2
            exit 2 ;;
    esac
    CERT_VERDICT=$(grep -oE 'verdict=[^ ]+' <<< "$CERT_LINE" | head -1)
    [ "$CERT_VERDICT" = verdict=OK ] || {
        echo "rs_ref_check: '$CERT' reads $CERT_VERDICT, not verdict=OK —" \
             "a failing gate run cannot justify a new baseline" >&2
        exit 2; }
    # files=N (emitted by every comparing gate beside the verdict) is how many
    # files that run ACTUALLY compared; it is checked against the allowlist
    # size below, so an OK from a scoped run (FAMILY=1, a narrowed ALLOWLIST)
    # cannot certify the unscoped baseline.
    CERT_FILES=$(grep -oE 'files=[0-9]+' <<< "$CERT_LINE" | tail -1)
    CERT_FILES=${CERT_FILES#files=}
    [ -n "$CERT_FILES" ] || {
        echo "rs_ref_check: '$CERT' carries no files=N beside its verdict — the gates" \
             "stamp the compared-file count there now; re-run the gate to produce a" \
             "log that says how much of the corpus its OK covers" >&2
        exit 2; }
    CERT_SCOPE=$(grep -oE 'scope_sha256=[0-9a-f]{64}' <<< "$CERT_LINE" | tail -1)
    CERT_SCOPE=${CERT_SCOPE#scope_sha256=}
    CERT_PROOF=$(grep -oE 'proof_outputs_sha256=[0-9a-f]{64}' <<< "$CERT_LINE" | tail -1)
    CERT_PROOF=${CERT_PROOF#proof_outputs_sha256=}
    CERT_ORACLE=$(grep -oE 'oracle_sha256=[0-9a-f]{64}' <<< "$CERT_LINE" | tail -1)
    CERT_ORACLE=${CERT_ORACLE#oracle_sha256=}
    CERT_EXEC=$(grep -oE 'execution_sha256=[0-9a-f]{64}' <<< "$CERT_LINE" | tail -1)
    CERT_EXEC=${CERT_EXEC#execution_sha256=}
    if [ -z "$CERT_SCOPE" ] || [ -z "$CERT_PROOF" ] \
            || [ -z "$CERT_ORACLE" ] || [ -z "$CERT_EXEC" ]; then
        echo "rs_ref_check: '$CERT' lacks the complete scope/proof/oracle/execution identity;" \
             "re-run corpus_file_diff.sh and save its new DONE line" >&2
        exit 2
    fi
    # The oracle binary is the specification the certifying run compared
    # against; its fingerprint (gate_common's hs_fingerprint, the same
    # binary-SHA recipe the cached gates key on) is what pins WHICH oracle
    # that was.
    HS_PATH="${HS_PATH:-$(find "$ROOT/tamarin-prover-testing/.stack-work/install" \
                               -name tamarin-prover -type f 2>/dev/null | head -1)}"
    [ -n "$HS_PATH" ] && [ -x "$HS_PATH" ] || {
        echo "rs_ref_check: no oracle binary to fingerprint (HS_PATH=${HS_PATH:-unset})" >&2
        exit 2; }
    # gate_common's oracle_rev_check fingerprints WHICH binary and pins
    # that it is the build of the submodule pin before `# oracle:` is stamped —
    # otherwise the header could bless a baseline with the fingerprint of an
    # oracle from another upstream (ALLOW_ORACLE_REV_MISMATCH=1 to override,
    # same policy as sweep_common.sh's preflight).
    oracle_rev_check "$HS_PATH" "$MAUDE" "$ROOT"
    execution_fingerprint "$MAUDE" "$DERIV" || exit 2
    if [ "$CERT_ORACLE" != "$HS_FP" ] || [ "$CERT_EXEC" != "$EXEC_FP" ]; then
        echo "rs_ref_check: '$CERT' was produced by a different oracle execution" \
             "(oracle or Maude/derivation timeout changed); re-run corpus_file_diff.sh" >&2
        exit 2
    fi
fi
if [ "$MODE" = check ]; then
    [ -n "$CERT" ] && { echo "rs_ref_check: --certified-by is only meaningful for generate" >&2; exit 2; }
    [ -f "$REF" ] || { echo "rs_ref_check: reference '$REF' missing — run generate first" >&2; exit 2; }
    ref_maude=$(awk -F': ' '/^# maude:/{print $2; exit}' "$REF")
    cur_maude=$("$MAUDE" --version)
    if [ -n "$ref_maude" ] && [ "$ref_maude" != "$cur_maude" ]; then
        echo "rs_ref_check: maude version mismatch: reference was generated with $ref_maude, this machine has $cur_maude" >&2
        exit 2
    fi
    execution_fingerprint "$MAUDE" "$DERIV" || exit 2
fi
CURRENT_ORACLE_PIN=$(git -C "$ROOT" rev-parse :tamarin-prover 2>/dev/null) || {
    echo "rs_ref_check: cannot read the tamarin-prover gitlink" >&2
    exit 2
}
CURRENT_PATCH_SERIES=$(patch_series_fingerprint "$ROOT") || {
    echo "rs_ref_check: cannot fingerprint the current Haskell patch series" >&2
    exit 2
}
export MAUDE_FP MAUDE_FP_PATH

# strip_env / flags_for / manifest hashing come from gate_common.sh. ikey is
# deliberately NOT gate_common's ckey: the reference key must not carry the
# oracle fingerprint (the header's `# oracle:` line records that separately),
# so it is the fingerprint-free input digest. Included inputs ARE carried: an
# edit to an `#include`d fragment changes the oracle's
# input, and without it check would blame the port (DIFF) instead of the
# input (INPUT_CHANGED).
ikey() { input_content_key "$2" "$(flags_for "$1")"; }
export -f file_sha256 strip_env flags_for parser_input_manifest manifest_encode manifest_normalize \
    manifest_decode_into input_manifest _include_shas_from_manifest \
    _oracle_shas_from_manifest input_content_key ikey binary_sha256 \
    binary_identity_unchanged execution_identity_unchanged rs_identity_unchanged \
    rs_execution_identity_unchanged

# one <rel> → "rel \t ikey \t sha|TIMEOUT|ERROR=n \t lines"
one() {
    local rel="$1" f="$CORPUS/$1" fl key checked_key rc out sha lines
    [ -f "$f" ] || { printf '%s\t-\tNOFILE\t0\n' "$rel"; return 0; }
    if ! key=$(ikey "$rel" "$f"); then
        printf '%s\t-\tERROR=2\t0\n' "$rel"
        return 0
    fi
    fl=$(flags_for "$rel")
    local tmp; tmp=$(mktemp)
    timeout "$TIMEOUT" "$BIN" --with-maude="$MAUDE" $fl $EXTRA_FLAGS --derivcheck-timeout="$DERIV" --prove "$f" >"$tmp" 2>/dev/null; rc=$?
    if [ "$rc" = 124 ]; then rm -f "$tmp"; printf '%s\t%s\tTIMEOUT\t0\n' "$rel" "$key"; return 0; fi
    if [ "$rc" != 0 ]; then rm -f "$tmp"; printf '%s\t%s\tERROR=%s\t0\n' "$rel" "$key" "$rc"; return 0; fi
    out=$(strip_env <"$tmp"); rm -f "$tmp"
    if ! checked_key=$(ikey "$rel" "$f") || [ "$checked_key" != "$key" ] \
            || ! rs_execution_identity_unchanged; then
        printf '%s\t%s\tERROR=2\t0\n' "$rel" "$key"
        return 0
    fi
    sha=$(printf '%s\n' "$out" | sha256sum | cut -d' ' -f1)
    lines=$(printf '%s\n' "$out" | wc -l)
    printf '%s\t%s\t%s\t%s\n' "$rel" "$key" "$sha" "$lines"
}
export -f one

mapfile -t FILES < <(grep -v '^[[:space:]]*#' "$ALLOWLIST" | grep . | sort -u)
# Zero files is the whole-run form of comparing nothing: `check` would report
# 0/0 match and exit clean, and `generate` would write an empty reference that
# every later check then passes against.
[ "${#FILES[@]}" -gt 0 ] || {
    echo "rs_ref_check: ALLOWLIST '$ALLOWLIST' resolved to 0 entries — nothing to compare" >&2
    exit 2; }
CURRENT_SCOPE=$(input_scope_fingerprint "$CORPUS" "$FLAGS_MAP" "${FILES[@]}") || {
    echo "rs_ref_check: could not fingerprint the current corpus/input scope" >&2
    exit 2
}
if [ "$MODE" = generate ] && [ "$CERT_SCOPE" != "$CURRENT_SCOPE" ]; then
    echo "rs_ref_check: '$CERT' covers a different corpus/input scope; re-run" \
         "corpus_file_diff.sh with this exact allowlist and inputs" >&2
    exit 2
fi
if [ "$MODE" = check ]; then
    ref_oracle=$(awk -F': ' '/^# oracle:/{print $2; exit}' "$REF")
    ref_oracle_pin=$(awk -F': ' '/^# oracle-pin:/{print $2; exit}' "$REF")
    ref_patch_series=$(awk -F': ' '/^# oracle-patch-series:/{print $2; exit}' "$REF")
    ref_exec=$(awk -F': ' '/^# execution:/{print $2; exit}' "$REF")
    ref_gate=$(awk -F': ' '/^# certified-gate:/{print $2; exit}' "$REF")
    ref_scope=$(awk -F': ' '/^# certified-scope-sha256:/{print $2; exit}' "$REF")
    ref_proof=$(awk -F': ' '/^# certified-proof-outputs-sha256:/{print $2; exit}' "$REF")
    if ! [[ "$ref_oracle" =~ ^[0-9a-f]{64}$ ]]; then
        echo "rs_ref_check: reference has no valid 64-hex oracle certificate; regenerate it only after a successful corpus_file_diff.sh gate" >&2
        exit 2
    fi
    if [ "$ref_oracle_pin" != "$CURRENT_ORACLE_PIN" ] \
            || [ "$ref_patch_series" != "$CURRENT_PATCH_SERIES" ]; then
        echo "rs_ref_check: reference was certified against a different Haskell gitlink or patch series" >&2
        exit 2
    fi
    if ! [[ "$ref_exec" =~ ^[0-9a-f]{64}$ ]]; then
        echo "rs_ref_check: reference has no valid 64-hex execution certificate; regenerate it only after a successful corpus_file_diff.sh gate" >&2
        exit 2
    fi
    if [ "$ref_exec" != "$EXEC_FP" ]; then
        echo "rs_ref_check: reference execution identity differs from this Maude version/derivation timeout" >&2
        exit 2
    fi
    if ! [[ "$ref_proof" =~ ^[0-9a-f]{64}$ ]]; then
        echo "rs_ref_check: reference has no valid proof-output certificate; regenerate it only after a successful corpus_file_diff.sh gate" >&2
        exit 2
    fi
    stored_proof=$(awk -F'\t' '!/^#/ && NF {print $1 "\t" $2 "\t" $3}' "$REF" \
        | LC_ALL=C sort | sha256sum | cut -d' ' -f1)
    if [ "$ref_gate" != DONE_CORPUS_FILE_DIFF ] || [ "$ref_scope" != "$CURRENT_SCOPE" ] \
            || [ "$ref_proof" != "$stored_proof" ]; then
        echo "rs_ref_check: reference is not certified for this exact corpus/input/proof set;" \
             "regenerate it only after a successful corpus_file_diff.sh gate" >&2
        exit 2
    fi
fi
# Reject stale reference keys before spending CI time proving the corpus. The
# full comparison below still owns missing-file/row diagnostics; this pass is
# only the cheap invariant that every committed row describes today's inputs.
if [ "$MODE" = check ]; then
    stale=0
    for rel in "${FILES[@]}"; do
        f="$CORPUS/$rel"
        [ -f "$f" ] || continue
        key=$(ikey "$rel" "$f") || {
            echo "rs_ref_check: could not compute input key for $rel" >&2
            exit 2
        }
        refkey=$(awk -F'\t' -v r="$rel" '!/^#/ && $1==r {print $2; exit}' "$REF")
        if [ -n "$refkey" ] && [ "$key" != "$refkey" ]; then
            echo "  INPUT_CHANGED  $rel (reference key is stale)"
            stale=$((stale+1))
        fi
    done
    if [ "$stale" -ne 0 ]; then
        echo "rs_ref_check: FAIL — $stale stale reference key(s); no proofs were run" >&2
        exit 1
    fi
fi
# The scoping check: the certifying run must have compared at least as many
# files as this generate is about to baseline. Checked BEFORE the prover
# burns an hour, like the flag itself.
if [ "$MODE" = generate ] && [ "$CERT_FILES" -ne "${#FILES[@]}" ]; then
    echo "rs_ref_check: '$CERT' compared $CERT_FILES file(s) but this generate" \
         "would baseline ${#FILES[@]}; re-run the gate over this exact corpus" >&2
    exit 2
fi
echo "rs_ref_check: $MODE — ${#FILES[@]} files, JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, BIN=$BIN"
RUN=$(mktemp)
printf '%s\n' "${FILES[@]}" | xargs -P "$JOBS" -I{} bash -c 'one "$@"' _ {} | sort > "$RUN"

bad=0
if [ "$MODE" = generate ]; then
    if grep -qE $'\t(TIMEOUT|ERROR=[0-9]+|NOFILE)\t' "$RUN"; then
        echo "rs_ref_check: refusing to write an incomplete reference — failed rows:" >&2
        grep -E $'\t(TIMEOUT|ERROR=[0-9]+|NOFILE)\t' "$RUN" >&2
        rm -f "$RUN"; exit 1
    fi
    # A row that never landed (an OOM-killed xargs child) is invisible in the
    # scan above, and a reference short of a file is a file CI stops covering.
    runrows=$(grep -c . "$RUN" 2>/dev/null) || runrows=0
    if [ "$runrows" -ne "${#FILES[@]}" ]; then
        echo "rs_ref_check: refusing to write a short reference — $runrows rows for ${#FILES[@]} files;" \
             "the missing ones would silently leave CI's coverage" >&2
        rm -f "$RUN"; exit 1
    fi
    run_proof=$(awk -F'\t' '{print $1 "\t" $2 "\t" $3}' "$RUN" \
        | LC_ALL=C sort | sha256sum | cut -d' ' -f1)
    if [ "$run_proof" != "$CERT_PROOF" ]; then
        echo "rs_ref_check: refusing to write a reference whose normalized proof" \
             "outputs differ from the certifying corpus_file_diff.sh run" >&2
        rm -f "$RUN"; exit 1
    fi
    { echo "# rs_ref_check reference — regenerate with: scripts/rs_ref_check.sh generate --certified-by <gate-results>"
      echo "# maude: $("$MAUDE" --version)"
      echo "# oracle: $HS_FP"
      echo "# oracle-pin: $CURRENT_ORACLE_PIN"
      echo "# oracle-patch-series: $CURRENT_PATCH_SERIES"
      echo "# execution: $EXEC_FP"
      echo "# certified-gate: DONE_CORPUS_FILE_DIFF"
      echo "# certified-scope-sha256: $CURRENT_SCOPE"
      echo "# certified-proof-outputs-sha256: $CERT_PROOF"
      echo "# certified-by: $CERT ($CERT_VERDICT)"
      cat "$RUN"; } > "$REF"
    echo "rs_ref_check: wrote $(grep -vc '^#' "$REF") rows to $REF"
else
    while IFS=$'\t' read -r rel key sha lines; do
        refrow=$(awk -F'\t' -v r="$rel" '!/^#/ && $1==r {print; exit}' "$REF")
        if [ -z "$refrow" ]; then
            echo "  NOREF          $rel (not in reference — regenerate to add it)"; bad=$((bad+1)); continue
        fi
        rkey=$(printf '%s' "$refrow" | cut -f2); rsha=$(printf '%s' "$refrow" | cut -f3)
        if [ "$key" != "$rkey" ]; then
            echo "  INPUT_CHANGED  $rel (theory/flags changed — submodule bump? regenerate the reference)"; bad=$((bad+1)); continue
        fi
        case "$sha" in
            TIMEOUT|ERROR=*|NOFILE) echo "  $sha  $rel"; bad=$((bad+1)); continue;;
        esac
        if [ "$sha" = "$rsha" ]; then
            echo "  MATCH          $rel"
        else
            echo "  DIFF           $rel (output hash changed, $lines lines — reproduce locally with rs_vs_rs_diff.sh)"; bad=$((bad+1))
        fi
    done < "$RUN"
    total=$(wc -l < "$RUN")
    echo "rs_ref_check: $((total-bad))/$total run rows match"
    # Reverse pass. The loop above walks the RUN and asks the reference about
    # each row, so it can only ever see what ran: drop a file from the allowlist
    # (or lose its row to a killed child) and its baseline sits in the reference
    # unconsulted while the gate reports 100% on the smaller set. The reference
    # is the coverage contract, so every row of it must have been executed.
    notrun=0
    while IFS= read -r m; do
        [ -n "$m" ] || continue
        echo "  NOTRUN         $m (in the reference, not in this run — the allowlist shrank, or its row was lost)"
        notrun=$((notrun+1))
    done < <(awk -F'\t' -v run="$RUN" \
        'FILENAME==run{ran[$1]=1;next} /^[[:space:]]*#/||NF==0{next} !($1 in ran){print $1}' \
        "$RUN" "$REF")
    # First-file detection is by FILENAME, not NR==FNR: an EMPTY run file makes
    # NR==FNR true throughout the reference too, which would swallow every row
    # into ran[] and report nothing — on exactly the run (all children lost)
    # this pass exists to catch.
    bad=$((bad+notrun))
    [ "$bad" = 0 ] || { rm -f "$RUN"; echo "rs_ref_check: FAIL — $bad file(s) diverge from or are missing against the committed main reference" >&2; exit 1; }
fi
rm -f "$RUN"
# No `verdict=` token here, deliberately. --certified-by accepts any log with a
# verdict line, and this gate compares the binary against a baseline the same
# binary lineage produced — a verdict= here would let one rs_ref_check run
# certify the next one's re-baseline, which is the circle the flag exists to
# break. The exit status is the verdict: every failure path above exits nonzero
# before reaching this line.
echo "DONE_RS_REF_CHECK"
