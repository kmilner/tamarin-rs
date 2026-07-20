#!/usr/bin/env bash
# Prove with the Rust port, re-verify with the reference Haskell prover.
#
#   ./prove_and_reverify.sh <theory.spthy> [extra prover flags…] > analyzed.spthy
#
# stdout receives the analyzed theory (the proof file) — but only once the
# Haskell re-check has agreed on every verdict — so redirecting stdout is a
# drop-in replacement for `tamarin-rs --prove --output=…`, with the
# re-verification as the added guarantee.  All progress/summary chatter goes
# to stderr.  On a verdict mismatch nothing is written to stdout and the
# script exits 1.
#
# tamarin-rs proves the theory and writes the analyzed output (the theory
# with embedded proof scripts) to a temp file; the Haskell tamarin-prover
# then loads that file WITHOUT --prove, which re-checks the embedded proof
# scripts step by step instead of searching from scratch.  Acceptance: the
# per-lemma verdicts (verified/falsified, per quantifier) of the Rust prove
# and the Haskell re-check agree for every lemma.  Step counts are NOT
# compared: re-checking a stored proof legitimately counts differently than
# the original search (upstream does the same on its own emit→recheck
# round-trip, e.g. Tutorial's exists-trace lemma: 5 steps → 7 steps).
#
# Env: RS_PATH (default target/release/tamarin-rs), HS_PATH (default: the
#      ./setup.sh testing oracle build), MAUDE_PATH, FILE_TIMEOUT (600s).
set -u

# OOM safeguards (repo convention): this driver dies first, and a runaway
# prover cannot take the machine down.
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 25165824 2>/dev/null || true

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

[ $# -ge 1 ] || { echo "usage: $0 <theory.spthy> [extra prover flags…]" >&2; exit 2; }
thy="$1"; shift
[ -f "$thy" ] || { echo "no such theory file: $thy" >&2; exit 2; }

RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
[ -x "$RS_PATH" ] || { echo "no Rust binary at $RS_PATH (cargo build --release)" >&2; exit 2; }
find_hs_bin() {
    local c
    for c in "$repo_root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin)}" || { echo "no Haskell oracle (./setup.sh testing)" >&2; exit 2; }
MAUDE_PATH="${MAUDE_PATH:-$(command -v maude || echo /home/linuxbrew/.linuxbrew/bin/maude)}"
export PATH="$(dirname "$MAUDE_PATH"):$PATH"
FILE_TIMEOUT="${FILE_TIMEOUT:-600}"

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT

# Lemma verdict lines of the "summary of summaries" block, e.g.
#   secrecy (all-traces): verified (12 steps)
summary_full() {
    awk '/^summary of summaries:/ {f=1; next} f' "$1" | grep -E '\((all-traces|exists-trace)\): '
}
summary_lines() {
    awk '/^summary of summaries:/ {f=1; next} f' "$1" \
        | grep -E '\((all-traces|exists-trace)\): ' \
        | sed -E 's/\([0-9]+ steps\)/(steps elided)/'
}

echo "=== prove (tamarin-rs) ===" >&2
t0=$SECONDS
timeout "$FILE_TIMEOUT" "$RS_PATH" "$thy" --prove "$@" \
    --output="$tmp/analyzed.spthy" > "$tmp/rs.out" 2> "$tmp/rs.err"
rc=$?
[ $rc = 124 ] && { echo "tamarin-rs timed out after ${FILE_TIMEOUT}s" >&2; exit 1; }
[ $rc = 0 ] || { echo "tamarin-rs failed (exit $rc):" >&2; tail -5 "$tmp/rs.err" >&2; exit 1; }
echo "  proved in $((SECONDS - t0))s" >&2

echo "=== re-verify (tamarin-prover, re-checking the emitted proofs) ===" >&2
t0=$SECONDS
timeout "$FILE_TIMEOUT" "$HS_PATH" "$tmp/analyzed.spthy" "$@" \
    > "$tmp/hs.out" 2> "$tmp/hs.err"
rc=$?
[ $rc = 124 ] && { echo "tamarin-prover timed out after ${FILE_TIMEOUT}s" >&2; exit 1; }
[ $rc = 0 ] || { echo "tamarin-prover failed (exit $rc):" >&2; tail -5 "$tmp/hs.err" >&2; exit 1; }
echo "  re-verified in $((SECONDS - t0))s" >&2

summary_lines "$tmp/rs.out" > "$tmp/rs.sum"
summary_lines "$tmp/hs.out" > "$tmp/hs.sum"
n=$(grep -c . "$tmp/rs.sum" || true)
[ "$n" -gt 0 ] || { echo "no lemma summaries found in the Rust output" >&2; exit 1; }

if diff "$tmp/rs.sum" "$tmp/hs.sum" > "$tmp/sum.diff"; then
    { echo
      echo "AGREE: both provers report identical verdicts for all $n lemma(s):"
      summary_full "$tmp/rs.out" | sed 's/^/  /'
    } >&2
    # The re-verified proof file is the payload: stdout only.
    cat "$tmp/analyzed.spthy"
else
    echo
    echo "MISMATCH between the Rust prover and the Haskell re-verification:" >&2
    sed 's/^/  /' "$tmp/sum.diff" >&2
    exit 1
fi
