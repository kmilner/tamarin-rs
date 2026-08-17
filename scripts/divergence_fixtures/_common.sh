# Shared by capture.sh and check.sh — sourced, never executed.
#
# The output slices below are the ones the corpus gates already compare, so a
# fixture verdict means the same thing a gate verdict does:
#   wf_block      == wf_gate.sh's slice
#   theory_block  == pretty_gate.sh's slice
# Keep them in step with those scripts.

# maude and dot live in linuxbrew here, and neither engine loads a theory
# without maude.
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
# Both engines are bounded: the OOM killer prefers this process tree, address
# space is capped, and every run is wrapped in `timeout`.
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 8388608 2>/dev/null || true

fixdir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(dirname "$(dirname "$fixdir")")"
expected="$fixdir/expected"
manifest="$fixdir/fixtures.tsv"
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
# GHC RTS bounds for the oracle: one capability and a 2G heap cap, so a
# runaway load fails loudly instead of swapping the machine.
hs_rts=(+RTS -N1 -M2G -RTS)

die() { echo "ERROR: $*" >&2; exit 1; }

# Drop the lines that carry build identity or wall-clock time.
strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}

# The wf report: either the success line or the WARNING block, up to its `*/`.
wf_block() {
    awk '
        /^\/\* All wellformedness checks were successful\. \*\/$/ { print; next }
        /^WARNING: the following wellformedness checks failed!$/  { f=1 }
        f { print }
        f && /^\*\/$/ { f=0 }
    '
}

# The pretty-printed theory echo: `theory … end`, minus the trailing wf report
# and `Generated from:` build stamp, minus everything after `end`.  Interior
# comments (AC-variant blocks, guarded-formula notes) are pretty-printer output
# and are kept.
theory_block() {
    awk '
        /^theory /              { cap=1 }
        !cap                    { next }
        /^\/\* All wellformedness checks were successful\. \*\/$/ { next }
        /^\/\*$/ {
            if ((getline nxt) > 0) {
                if (nxt == "WARNING: the following wellformedness checks failed!" || nxt == "Generated from:") {
                    while ((getline z) > 0) { if (z == "*/") break }
                    next
                }
                print; print nxt; next
            }
            print; next
        }
        { print }
        /^end$/                 { cap=0 }
    '
}

# `slice <name> < raw-stdout` — cut one comparable block out of a theory load.
slice() {
    case "$1" in
        wf)     wf_block ;;
        theory) theory_block ;;
        *)      die "unknown slice '$1' in $manifest" ;;
    esac
}

# The manifest's slice column is a comma-separated list, so one theory load can
# pin several blocks; `slices_of` expands it.
slices_of() { printf '%s\n' "$1" | tr ',' ' '; }

# `for_each_fixture <fn>` — call <fn> name slices mode flags for every row.
for_each_fixture() {
    local fn="$1" name sl mode flags
    while IFS=$'\t' read -r name sl mode flags; do
        case "$name" in ''|\#*) continue ;; esac
        [ -f "$fixdir/$name.spthy" ] || die "$manifest names $name but $name.spthy is missing"
        "$fn" "$name" "$sl" "$mode" "$flags"
    done < "$manifest"
}

# `census_fixture_dir` — cross-check the fixture directory against the manifest
# in both directions.  The scripts load, capture and compare only the files
# that the manifest names.  Without this census, a `.spthy` file that no row
# mentions would stay here undetected forever.  So would a capture that a
# retired row leaves behind.
census_fixture_dir() {
    local f
    declare -A claimed=([oracle_rev]=1)
    claim_one() {
        local name="$1" slices="$2" mode="$3" sl
        case "$mode" in
            match|diverge) ;;
            *) die "$manifest gives $name the unknown mode '$mode'" ;;
        esac
        claimed["$name.spthy"]=1
        for sl in $(slices_of "$slices"); do
            claimed["$name.$sl.hs.txt"]=1
            if [ "$mode" = diverge ]; then claimed["$name.$sl.rs.txt"]=1; fi
        done
    }
    for_each_fixture claim_one
    for f in "$fixdir"/*.spthy "$expected"/*; do
        # A first capture finds the expected/ directory empty.  The glob then
        # stays unexpanded.
        [ -e "$f" ] || continue
        [ -n "${claimed[$(basename "$f")]:-}" ] \
            || die "$(basename "$f") is claimed by no row of $manifest — add a row or delete the file"
    done
}

# `load <binary> <name> <flags> [rts…]` — load a fixture and print the stdout
# the slices are cut from.  Returns the engine's exit status.
load() {
    local bin="$1" name="$2" flags="$3"; shift 3
    local out rc; out="$(mktemp)"
    # shellcheck disable=SC2086
    ( cd "$fixdir" && timeout "$FILE_TIMEOUT" "$bin" $flags "$name.spthy" "$@" ) >"$out" 2>/dev/null
    rc=$?
    if [ "$rc" = 0 ]; then strip_env < "$out"; fi
    rm -f "$out"
    return "$rc"
}
