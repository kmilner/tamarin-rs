#!/usr/bin/env bash
# Behavioral-equivalence sweep for a "refactor that shouldn't change output":
# run TWO Rust binaries (PRE-patch baseline vs POST-patch) over every corpus
# file and diff their stripped --prove stdout.  No Haskell needed — if the two
# RS binaries agree everywhere, the refactor is behaviorally inert and inherits
# the baseline's HS-faithfulness by transitivity (covers even HS-timeout
# monsters).  Where they differ, those exact files get an HS comparison.
#
# Per-file prover flags come from file_flags.tsv (FLAGS_MAP) — the same map
# the batch gates use.  Without them the auto-sources / seqdfs families run in
# the wrong mode and explode in BOTH time and memory (the timeouts they
# produce are harness artifacts, not file properties).
#
# Each prover run is internally parallel (a rayon pool AND a Maude subprocess
# pool, both sized to the whole machine by default), so JOBS is the number of
# concurrent FILE PAIRS, not cores: keep it small.
#
# Env: PRE, POST   the two release binaries (must exist; no default fallback
#                  that silently "works")
#      ALLOWLIST   file list (default scripts/parity_corpus.txt — the canonical
#                  gate corpus; set ALLOWLIST= (empty) to sweep every .spthy,
#                  which includes known-infeasible monsters)
#      FLAGS_MAP, CORPUS, JOBS, TIMEOUT, DERIV, OUT,
#      RESUME      path to a prior TSV: files already present are skipped
#
# Exit status carries the verdict, which the DONE line repeats: nonzero on any
# DIFF and on every row that compared NOTHING — ERROR_ONE/ERROR_BOTH (a prover
# died; identical failure banners are not agreement), TIMEOUT_ONE/TIMEOUT_BOTH
# (a side was killed at the cap, so no output was produced to compare),
# EMPTY_BOTH, NOFILE — plus any allowlisted file that produced no row at all.
# TIMEOUT_BOTH being fatal is deliberate: at the default 180s cap a full-corpus
# --prove sweep WILL hit it, and "both binaries ran out of time" is a statement
# about the cap, not evidence that the refactor is inert. Raise TIMEOUT or
# narrow ALLOWLIST until the set you claim is covered actually is.
set -u

# Shared gate plumbing (gate_common.sh): OOM prologue, strip_env, flags_for,
# maude resolver.
[ -r "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh" ] || { echo "rs_vs_rs: missing $(dirname "${BASH_SOURCE[0]}")/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh"
# OOM discipline: make the sweep (and the provers it spawns, which inherit
# both settings) the kernel's preferred victim, and cap each prover's address
# space — a runaway prover must die alone, not take the session with it.
oom_prologue

ROOT="${ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
CORPUS="${CORPUS:-$ROOT/tamarin-prover/examples}"
PRE="${PRE:-/tmp/rs-prepatch}"
POST="${POST:-/tmp/rs-patched}"
TIMEOUT="${TIMEOUT:-180}"
cores=$(nproc 2>/dev/null || echo 8)
JOBS="${JOBS:-$(( cores >= 24 ? 3 : cores >= 12 ? 2 : 1 ))}"
DERIV="${DERIV:-30}"
OUT="${OUT:-/tmp/rs_vs_rs.tsv}"
RESUME="${RESUME:-}"
FLAGS_MAP="${FLAGS_MAP:-$ROOT/scripts/file_flags.tsv}"
ALLOWLIST="${ALLOWLIST-$ROOT/scripts/parity_corpus.txt}"
export PRE POST TIMEOUT DERIV CORPUS FLAGS_MAP

# Fail loudly on a broken setup instead of producing a vacuous sweep.
for b in "$PRE" "$POST"; do
    [ -x "$b" ] || { echo "rs_vs_rs: no executable prover at '$b' — set PRE= and POST= to the two release binaries" >&2; exit 2; }
done
if [ -n "$ALLOWLIST" ] && [ ! -f "$ALLOWLIST" ]; then
    echo "rs_vs_rs: ALLOWLIST '$ALLOWLIST' does not exist" >&2; exit 2
fi
# A maude-less environment makes every run fail fast on both sides — reported
# as ERROR_BOTH, never compared — so resolve one maude up front (hard fail
# when nothing resolves) and put its directory on PATH for the two binaries.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"

# strip_env / flags_for come from gate_common.sh.
export -f strip_env flags_for

one() {
    local rel="$1" f="$CORPUS/$1" a b ra rb da fl
    [ -f "$f" ] || { printf '%s\tNOFILE\t0\n' "$rel"; return 0; }
    fl=$(flags_for "$rel")
    local ta tb; ta=$(mktemp); tb=$(mktemp)
    timeout "$TIMEOUT" "$PRE"  $fl --derivcheck-timeout="$DERIV" --prove "$f" >"$ta" 2>/dev/null; ra=$?
    timeout "$TIMEOUT" "$POST" $fl --derivcheck-timeout="$DERIV" --prove "$f" >"$tb" 2>/dev/null; rb=$?
    if [ "$ra" = 124 ] && [ "$rb" = 124 ]; then rm -f "$ta" "$tb"; printf '%s\tTIMEOUT_BOTH\t0\n' "$rel"; return 0; fi
    if [ "$ra" = 124 ] || [ "$rb" = 124 ]; then rm -f "$ta" "$tb"; printf '%s\tTIMEOUT_ONE\tpre=%s,post=%s\n' "$rel" "$ra" "$rb"; return 0; fi
    # A prover that errors out (missing maude, bad flags, OOM-abort) must not
    # count as agreement — identical failure banners are vacuous evidence.
    if [ "$ra" != 0 ] && [ "$rb" != 0 ]; then rm -f "$ta" "$tb"; printf '%s\tERROR_BOTH\tpre=%s,post=%s\n' "$rel" "$ra" "$rb"; return 0; fi
    if [ "$ra" != 0 ] || [ "$rb" != 0 ]; then rm -f "$ta" "$tb"; printf '%s\tERROR_ONE\tpre=%s,post=%s\n' "$rel" "$ra" "$rb"; return 0; fi
    a=$(strip_env <"$ta"); b=$(strip_env <"$tb"); rm -f "$ta" "$tb"
    if [ -z "$a" ] && [ -z "$b" ]; then printf '%s\tEMPTY_BOTH\t0\n' "$rel"; return 0; fi
    da=$(diff <(printf '%s\n' "$a") <(printf '%s\n' "$b") | grep -c '^[<>]')
    if [ "$da" = 0 ]; then printf '%s\tSAME\t0\n' "$rel"
    else printf '%s\tDIFF\t%s\n' "$rel" "$da"; fi
}
export -f one

cd "$CORPUS"
# Resume: skip files already conclusively recorded in $RESUME (keep its rows).
declare -A DONE=()
if [ -n "$RESUME" ] && [ -f "$RESUME" ]; then
    while IFS=$'\t' read -r rel _; do DONE["$rel"]=1; done < "$RESUME"
    cp "$RESUME" "$OUT"
    echo "rs_vs_rs: resuming, ${#DONE[@]} files already done in $RESUME"
else
    : > "$OUT"
fi
if [ -n "$ALLOWLIST" ]; then
    # Comments and blanks dropped: they are not files, and now that NOFILE is
    # fatal they would fail the run rather than be quietly reported.
    mapfile -t ALL < <(grep -v '^[[:space:]]*#' "$ALLOWLIST" | grep . | sort -u)
    echo "rs_vs_rs: ALLOWLIST=$ALLOWLIST (${#ALL[@]} files)"
else
    mapfile -t ALL < <(find . -name '*.spthy' | sed 's|^\./||' | sort)
    echo "rs_vs_rs: no ALLOWLIST — sweeping ALL ${#ALL[@]} corpus files (includes known-infeasible ones)"
fi
# Zero files is the whole-run form of comparing nothing: no rows, an empty
# histogram, and a verdict that reads exactly like an inert refactor.
[ "${#ALL[@]}" -gt 0 ] || {
    echo "rs_vs_rs: the file list resolved to 0 entries — nothing to compare" >&2; exit 2; }
FILES=()
for f in "${ALL[@]}"; do [ -n "${DONE[$f]:-}" ] || FILES+=("$f"); done
TOTAL=${#FILES[@]}
echo "rs_vs_rs: ${#ALL[@]} total, $TOTAL to run, JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, PRE=$PRE POST=$POST"
# Live progress on stderr; every non-SAME row is left on its own line.
[ "$TOTAL" -gt 0 ] && printf '%s\n' "${FILES[@]}" \
    | xargs -P "$JOBS" -I{} bash -c 'one "$@"' _ {} \
    | tee -a "$OUT" \
    | awk -v t="$TOTAL" '{
        n++
        if ($2 != "SAME") printf "\r  %-13s %s\033[K\n", $2, $1 > "/dev/stderr"
        printf "\r  [%d/%d] %s\033[K", n, t, $1 > "/dev/stderr"
        fflush("/dev/stderr")
      } END { print "" > "/dev/stderr" }' >/dev/null
sort -o "$OUT" "$OUT"
echo "=== SUMMARY ==="
awk -F'\t' '{c[$2]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$OUT"
echo "=== DIFFs (behavioral changes from the refactor) ==="
awk -F'\t' '$2=="DIFF"{print "  "$3"\t"$1}' "$OUT" | sort -rn
echo "=== needs attention (rows that compared nothing) ==="
awk -F'\t' '$2 ~ /^(ERROR_|TIMEOUT_)/ || $2=="NOFILE" || $2=="EMPTY_BOTH" {print "  "$2"\t"$1}' "$OUT"
echo "  results: $OUT"

# Verdict — the histogram above is the whole story only if someone reads it.
# SAME is the only status that says the two binaries were shown to agree:
# everything else is either a behavioral change (DIFF) or a row where at least
# one side produced no output to compare (a prover that died, one killed at the
# cap, both silent). A file that produced no row at all is invisible in the
# histogram, so coverage is checked as a set: every allowlisted file must have a
# row. That is the RESUME-correct form of "rows == the number of files" — under
# RESUME the file carries rows from the earlier run too, so counting rows
# against this run's TOTAL would fail every resumed sweep.
diffs=$(awk -F'\t' '$2=="DIFF"' "$OUT" | grep -c .)
errs=$(awk -F'\t' '$2 ~ /^ERROR_/' "$OUT" | grep -c .)
touts=$(awk -F'\t' '$2 ~ /^TIMEOUT_/' "$OUT" | grep -c .)
nofile=$(awk -F'\t' '$2=="NOFILE"' "$OUT" | grep -c .)
empty=$(awk -F'\t' '$2=="EMPTY_BOTH"' "$OUT" | grep -c .)
# First-file detection is by FILENAME, not NR==FNR: an EMPTY OUT (a fresh run
# whose every child died before writing) makes NR==FNR true throughout the
# file list too, which would swallow every path into seen[] and count zero
# missing rows — a verdict of OK over no rows at all.
norow=$(awk -F'\t' -v out="$OUT" 'FILENAME==out{seen[$1]=1;next} !($1 in seen)' \
            "$OUT" <(printf '%s\n' "${ALL[@]}") | grep -c .)
bad=''
[ "$diffs" = 0 ] || bad="DIFF=$diffs"
[ "$errs" = 0 ] || bad="${bad:+$bad }ERROR=$errs"
[ "$touts" = 0 ] || bad="${bad:+$bad }TIMEOUT=$touts"
[ "$nofile" = 0 ] || bad="${bad:+$bad }NOFILE=$nofile"
[ "$empty" = 0 ] || bad="${bad:+$bad }EMPTY_BOTH=$empty"
[ "$norow" = 0 ] || bad="${bad:+$bad }ROW-COUNT=$(( ${#ALL[@]} - norow ))/${#ALL[@]}"
echo "DONE_RS_VS_RS verdict=${bad:-OK}"
[ -z "$bad" ]
