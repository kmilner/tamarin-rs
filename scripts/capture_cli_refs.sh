#!/usr/bin/env bash
# Capture the HASKELL oracle's stdout for every row of
# crates/tamarin-prover/tests/fixtures/cli_refs/cases.tsv, so
# tests/cli_e2e.rs can byte-compare the port against it.
#
# The argv lives in cases.tsv, NOT here and NOT in the test: both sides read
# that one table, so a reference can never be captured with flags the test
# does not pass.  Adding a flag pin is therefore: add a row, run this script.
#
#   scripts/capture_cli_refs.sh            # capture every row
#   scripts/capture_cli_refs.sh <name>...  # capture only these rows
#
# Writes, next to the table:
#   <name>.stdout   RAW oracle stdout (the test normalizes build info, the
#                   `analyzed:` path and the processing time out of BOTH sides
#                   at comparison time, so nothing is stripped here)
#   CAPTURED.tsv    provenance (which oracle binary, its fingerprint, the
#                   submodule pin it must match, the maude, the date) plus one
#                   `<name>\t<bytes>` row per capture.  cli_e2e.rs asserts this
#                   lists exactly the rows in cases.tsv, so a partial capture
#                   cannot masquerade as a complete one.
#
# This is a PROVING run (every row carries --prove).  It is deliberately
# SERIAL: the oracle's `--prove` output is nondeterministic under parallel
# load (see the PE+prove flakiness note in the campaign ledger), and a flaky
# reference is worse than none.
#
# Env: HS_PATH (oracle binary), MAUDE (maude binary), FILE_TIMEOUT (120s per
#      row), ALLOW_ORACLE_REV_MISMATCH=1 (capture against an oracle that is
#      not the submodule pin — records the mismatch and continues).
#
# Exit: 0 only when every requested row was captured, non-empty, and satisfies
#       the `relation` column of its case.  The DONE line repeats the verdict.
set -u

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
# Shared gate plumbing (gate_common.sh): OOM prologue, strip_env, the oracle
# fingerprint recipe.  (The maude ladder below is deliberately NOT the shared
# resolver: it mirrors the RS test harness's own probe order, so captures use
# the maude cli_e2e.rs will.)
[ -r "$script_dir/gate_common.sh" ] || { echo "capture_cli_refs: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
# OOM discipline: a prover that explodes dies alone, it does not take the
# session with it.  Every subprocess below inherits these.
oom_prologue 16777216
FIXTURES="$repo_root/crates/tamarin-prover/tests/fixtures"
REFS="$FIXTURES/cli_refs"
CASES="$REFS/cases.tsv"
MANIFEST="$REFS/CAPTURED.tsv"
FILE_TIMEOUT="${FILE_TIMEOUT:-120}"

[ -f "$CASES" ] || { echo "capture_cli_refs: no case table at $CASES" >&2; exit 2; }

# --- oracle binary -----------------------------------------------------------
HS_PATH=$(resolve_hs_oracle "$repo_root") || exit 2
[ -x "$HS_PATH" ] || { echo "capture_cli_refs: HS_PATH '$HS_PATH' is not executable" >&2; exit 2; }

# --- maude -------------------------------------------------------------------
# Same ladder the test harness walks (crates/tamarin-prover/tests/common/mod.rs):
# the two /usr candidates, then $PATH, then this workspace's linuxbrew install.
if [ -z "${MAUDE:-}" ]; then
    for c in /usr/local/bin/maude /usr/bin/maude; do
        [ -x "$c" ] && { MAUDE="$c"; break; }
    done
fi
[ -n "${MAUDE:-}" ] || MAUDE="$(command -v maude 2>/dev/null || true)"
[ -n "${MAUDE:-}" ] || { [ -x /home/linuxbrew/.linuxbrew/bin/maude ] && MAUDE=/home/linuxbrew/.linuxbrew/bin/maude; }
[ -n "${MAUDE:-}" ] && [ -x "$MAUDE" ] || {
    echo "capture_cli_refs: no maude found (set MAUDE=/path/to/maude)" >&2; exit 2; }

# --- oracle revision/source preflight ---------------------------------------
# Require setup.sh's controlled build of the pin plus current patch series.
oracle_rev_check "$HS_PATH" "$MAUDE" "$repo_root"
binrev=${ORACLE_REVISION:-unknown}
rev_note="$ORACLE_SOURCE_STATUS: $ORACLE_SOURCE_NOTE"

# --- row selection -----------------------------------------------------------
want=("$@")
selected() {
    [ ${#want[@]} -eq 0 ] && return 0
    local w
    for w in "${want[@]}"; do [ "$w" = "$1" ] && return 0; done
    return 1
}

# strip_env (gate_common.sh) drops the machine- or run-local lines before
# COMPARING two captures (the files themselves keep them; cli_e2e.rs
# normalizes both sides).

mkdir -p "$REFS"
tmp_manifest=$(mktemp)
trap 'rm -f "$tmp_manifest"' EXIT

rows=0; captured=0; bad=''
declare -A CAPTURED_NAME=()
declare -A RELATION=()
declare -A ROW_NAME=()

echo "capture_cli_refs: oracle=$HS_PATH fp=$HS_FP maude=$MAUDE timeout=${FILE_TIMEOUT}s (serial)"

while IFS=$'\t' read -r name theory relation args; do
    case "$name" in ''|\#*) continue;; esac
    rows=$((rows + 1))
    ROW_NAME["$name"]=1
    selected "$name" || continue
    if [ ! -f "$FIXTURES/$theory" ]; then
        echo "  MISSING-THEORY $name ($theory)"; bad="${bad:+$bad }MISSING-THEORY=$name"; continue
    fi
    argv=${args//\{FIXTURES\}/$FIXTURES}
    out="$REFS/$name.stdout"
    tmp=$(mktemp)
    # Word splitting on $argv is intended: cases.tsv holds a flag list.
    timeout "$FILE_TIMEOUT" "$HS_PATH" --with-maude="$MAUDE" $argv "$FIXTURES/$theory" \
        >"$tmp" 2>/dev/null
    rc=$?
    if [ "$rc" != 0 ]; then
        rm -f "$tmp"
        echo "  FAIL           $name (oracle exit $rc)"
        bad="${bad:+$bad }EXIT=$name:$rc"; continue
    fi
    if [ ! -s "$tmp" ]; then
        rm -f "$tmp"
        echo "  EMPTY          $name (oracle wrote nothing — a zero-byte reference pins nothing)"
        bad="${bad:+$bad }EMPTY=$name"; continue
    fi
    mv "$tmp" "$out"
    CAPTURED_NAME["$name"]=1
    RELATION["$name"]="$relation"
    printf '%s\t%s\n' "$name" "$(stat -c '%s' "$out")" >> "$tmp_manifest"
    captured=$((captured + 1))
    echo "  OK             $name ($(stat -c '%s' "$out") bytes)"
done < "$CASES"

# A requested name that matches no row would otherwise vanish in selected()'s
# filter and the run would report verdict=OK having captured nothing — the
# exact vacuous success the exit contract ("every requested row was captured")
# rules out.
if [ ${#want[@]} -ne 0 ]; then
    for w in "${want[@]}"; do
        if [ -z "${ROW_NAME[$w]:-}" ]; then
            echo "  UNKNOWN-ROW    $w (no cases.tsv row has this name)"
            bad="${bad:+$bad }UNKNOWN-ROW=$w"
        fi
    done
fi

# --- relation check ----------------------------------------------------------
# cases.tsv declares how each row's bytes must relate to another row's.  A `!=`
# that turns out equal means the flag changed nothing and the pin is vacuous; a
# `=` that turns out different means the row's claim is stale.  Both are
# capture failures, not test failures: the reference set must not be committed
# in that state.  Only checkable when BOTH refs exist.
for name in "${!RELATION[@]}"; do
    rel="${RELATION[$name]}"
    case "$rel" in
        -|'') continue;;
        '!='*) op='!='; other="${rel#!=}";;
        '='*)  op='=';  other="${rel#=}";;
        *) echo "  BAD-RELATION   $name ($rel)"; bad="${bad:+$bad }BAD-RELATION=$name"; continue;;
    esac
    if [ ! -s "$REFS/$other.stdout" ]; then
        echo "  UNCHECKED      $name ($op$other — the other reference is not captured)"
        bad="${bad:+$bad }UNCHECKED-RELATION=$name"; continue
    fi
    if strip_env <"$REFS/$name.stdout" | diff -q - <(strip_env <"$REFS/$other.stdout") >/dev/null; then
        same=1
    else
        same=0
    fi
    if [ "$op" = '!=' ] && [ "$same" = 1 ]; then
        echo "  VACUOUS        $name (identical to $other — the flag changed nothing)"
        bad="${bad:+$bad }VACUOUS=$name"
    elif [ "$op" = '=' ] && [ "$same" = 0 ]; then
        echo "  STALE-RELATION $name (differs from $other, but cases.tsv claims =)"
        bad="${bad:+$bad }STALE-RELATION=$name"
    fi
done

# --- manifest ----------------------------------------------------------------
# Written only for a FULL capture: a partial run must not leave a manifest that
# claims to describe the whole set (cli_e2e.rs compares it against cases.tsv).
if [ ${#want[@]} -eq 0 ] && [ -z "$bad" ]; then
    { echo "# capture_cli_refs.sh provenance — regenerate with: scripts/capture_cli_refs.sh"
      echo "# hs_bin	$HS_PATH"
      echo "# hs_fp	$HS_FP"
      echo "# hs_rev	${binrev:-unknown} ($rev_note)"
      echo "# maude	$("$MAUDE" --version 2>/dev/null | head -1)"
      echo "# captured	$(date -u +%Y-%m-%dT%H:%M:%SZ)"
      sort "$tmp_manifest"; } > "$MANIFEST"
    echo "capture_cli_refs: wrote $captured rows to $MANIFEST"
elif [ ${#want[@]} -ne 0 ]; then
    echo "capture_cli_refs: partial run (rows named on the command line) — $MANIFEST left alone;" \
         "re-run with no arguments before committing"
fi

[ "$rows" -gt 0 ] || bad="${bad:+$bad }NO-ROWS"
if [ ${#want[@]} -eq 0 ] && [ "$captured" != "$rows" ]; then
    bad="${bad:+$bad }CAPTURED=$captured/$rows"
fi
echo "DONE_CAPTURE_CLI_REFS verdict=${bad:-OK} captured=$captured/$rows"
[ -z "$bad" ]
