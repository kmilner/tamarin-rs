# Shared by capture.sh and check.sh — sourced, never executed.
#
# The output slices are the ones the corpus gates already compare, so a
# fixture verdict means the same thing a gate verdict does: strip_env, wf_block
# (wf_gate.sh) and theory_block (pretty_gate.sh) come from gate_common.sh, and
# summary_block below is the tail of stdout corpus_file_diff.sh compares in
# full.  Three more slices cover what no corpus gate reads: the whole stdout
# (`--parse-only` and `-m` documents), the outcome of a fatal run, and the
# `--output-dot`/`--output-json` trace files.

# maude and dot live in linuxbrew here, and neither engine loads a theory
# without maude.
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
# Both engines are bounded: the OOM killer prefers this process tree, address
# space is capped, and every run is wrapped in `timeout`.
echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
ulimit -v 8388608 2>/dev/null || true

fixdir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../gate_common.sh
. "$fixdir/../gate_common.sh"
repo_root="$(dirname "$(dirname "$fixdir")")"
expected="$fixdir/expected"
manifest="$fixdir/fixtures.tsv"
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
# GHC RTS bounds for the oracle: one capability and a 2G heap cap, so a
# runaway load fails loudly instead of swapping the machine.
hs_rts=(+RTS -N1 -M2G -RTS)

die() { echo "ERROR: $*" >&2; exit 1; }

# The run summary: everything from `summary of summaries:` on, which carries
# the `WARNING: N wellformedness check failed!` count and the per-lemma
# verdicts.  `strip_env` has already dropped the `analyzed:` and
# `processing time:` lines.
summary_block() {
    awk '/^summary of summaries:$/ { f=1 } f { print }'
}

# `error_kind < stderr` — the normalised KIND of a fatal run's error, never
# its bytes.  Positions, file names and the rendering differ by design (the
# port prints parse errors through codespan, the oracle through Parsec), so
# what both engines are held to is the category the message names.  The
# message is the first of:
#   * `tamarin-prover: <msg>`        a GHC `error`/`die`, which the port
#                                    reproduces under the same prefix;
#   * `error: <msg>` / `error[…]: <msg>`   a codespan diagnostic (the port);
#   * the first line of a Parsec block that opens with `"<file>" (line …`
#     and is not an `unexpected`/`expecting` line (the oracle);
#   * otherwise the last stderr line that is not a `[…]` marker, the Maude
#     banner or search progress — a bare `die` (`Please specify a valid
#     output file/directory`, the quit-on-warning abort).
# Its kind is the text before the first `:`, cut to five words, with quoted
# names and digits blanked.  A port wording that differs from the oracle's by
# design is mapped onto the oracle's kind in `kind_alias`, so the row still
# compares one kind with one kind.
error_kind() {
    local msg
    msg="$(awk '
        function emit(m) { print m; done = 1; exit }
        /^tamarin-prover: / { emit(substr($0, 17)) }
        /^error(\[[^]]*\])?: / { sub(/^error(\[[^]]*\])?: /, ""); emit($0) }
        /^"[^"]*" \(line [0-9]+, column [0-9]+\):$/ { parsec = 1; next }
        parsec && /^(unexpected|expecting) / { next }
        parsec { emit($0) }
        /^(\[|maude tool: | checking |searching for |attack found |CallStack |  error, called )/ { next }
        /./ { last = $0 }
        END { if (!done && last != "") print last }
    ')"
    [ -n "$msg" ] || { echo "(none)"; return; }
    # The port names the stage an elaboration error came from in front of the
    # message; the oracle fails inside its parser and has no such stage.
    msg="$(printf '%s\n' "$msg" | sed -E \
        -e 's/^elaboration error in [^:]*: //' \
        -e 's/^SAPIC translation: //' \
        -e 's/^in the proof of lemma `[^`]*`: //' \
        -e 's/^could not convert a disjunct of a stored proof goal: //')"
    msg="${msg%%:*}"
    msg="$(printf '%s\n' "$msg" | sed -e "s/'[^']*'/'_'/g" -e 's/"[^"]*"/"_"/g' -e 's/[0-9][0-9]*/N/g' \
        | awk '{ n = NF > 5 ? 5 : NF; s = $1; for (i = 2; i <= n; i++) s = s " " $i; print s }')"
    kind_alias "$msg"
}

# Port wordings that differ from the oracle's by design, mapped onto the
# oracle's kind.  Each arm says why the wording differs.
kind_alias() {
    case "$1" in
        # The port finds two rules under one name while parsing, and reports
        # a conflicting declaration; the oracle reports the duplicate rule.
        'Conflicting rule') echo 'duplicate rule' ;;
        *) printf '%s\n' "$1" ;;
    esac
}

# `run_row <binary> <input> <slices> <flags> <outdir> [rts…]` — load a fixture
# once and leave everything the slices are cut from in <outdir>: `stdout`
# (strip_env applied), `stderr`, `rc`, and the trace files `t.dot`/`t.json`
# when the row lists the `traces` slice.  Returns non-zero when the run cannot
# be compared: it timed out or its exit status disagrees with the row.
run_row() {
    local bin="$1" input="$2" slices="$3" flags="$4" out="$5"; shift 5
    local rc extra=()
    case ",$slices," in
        *,traces,*) extra=("--output-dot=$out/t.dot" "--output-json=$out/t.json") ;;
    esac
    # shellcheck disable=SC2086
    ( cd "$fixdir" && timeout "$FILE_TIMEOUT" "$bin" $flags "${extra[@]}" "$input" "$@" ) \
        >"$out/raw" 2>"$out/stderr"
    rc=$?
    echo "$rc" > "$out/rc"
    strip_env < "$out/raw" > "$out/stdout"
    [ "$rc" != 124 ] || return 1
    case ",$slices," in
        *,error,*|*,error-message,*) [ "$rc" != 0 ] ;;
        *) [ "$rc" = 0 ] ;;
    esac
}

# `slice <name> <outdir>` — cut one comparable block out of a run_row result.
slice() {
    local f
    case "$1" in
        wf)      wf_block < "$2/stdout" ;;
        theory)  theory_block < "$2/stdout" ;;
        summary) summary_block < "$2/stdout" ;;
        stdout)  cat "$2/stdout" ;;
        error)   printf 'rc %s\nkind %s\n' "$(cat "$2/rc")" "$(error_kind < "$2/stderr")" ;;
        error-message)
            awk -v rc="$(cat "$2/rc")" '
                /^tamarin-prover: / && !message { print "rc " rc; message=1 }
                message { sub(/[[:blank:]]+$/, ""); print }
            ' "$2/stderr" ;;
        traces)
            for f in dot json; do
                echo "== --output-$f =="
                if [ -f "$2/t.$f" ]; then cat "$2/t.$f"; echo; else echo "(not written)"; fi
            done ;;
        *)       die "unknown slice '$1' in $manifest" ;;
    esac
}

# The manifest's slice column is a comma-separated list, so one theory load can
# pin several blocks; `slices_of` expands it.
slices_of() { printf '%s\n' "$1" | tr ',' ' '; }

# `for_each_fixture <fn>` — call <fn> name slices mode flags input for every row.
for_each_fixture() {
    local fn="$1" name sl mode flags input
    while IFS=$'\t' read -r name sl mode flags input; do
        case "$name" in ''|\#*) continue ;; esac
        input=${input:-${name%%@*}.spthy}
        [ -f "$fixdir/$input" ] || die "$manifest names $name but $input is missing"
        "$fn" "$name" "$sl" "$mode" "$flags" "$input"
    done < "$manifest"
}

# `census_fixture_dir` — cross-check the fixture directory against the manifest
# in both directions.  The scripts load, capture and compare only the files
# that the manifest names.  Without this census, a `.spthy` file that no row
# mentions would stay here undetected forever.  So would a capture that a
# retired row leaves behind.  A fixture may bring sibling files it reads
# itself — an `#include`d `<fixture>.inc`, an oracle script
# `<fixture>.oracle`, a directory `<fixture>.d/` — and they are claimed with
# their fixture.
census_fixture_dir() {
    local f base
    declare -A claimed=([oracle_rev]=1)
    declare -A fixtures=()
    claim_one() {
        local name="$1" slices="$2" mode="$3" input="$5" sl
        case "$mode" in
            match|diverge) ;;
            *) die "$manifest gives $name the unknown mode '$mode'" ;;
        esac
        fixtures["${input%.spthy}"]=1
        for sl in $(slices_of "$slices"); do
            claimed["$name.$sl.hs.txt"]=1
            if [ "$mode" = diverge ]; then claimed["$name.$sl.rs.txt"]=1; fi
        done
    }
    for_each_fixture claim_one
    for f in "$fixdir"/*; do
        base="$(basename "$f")"
        case "$base" in
            _common.sh|capture.sh|check.sh|fixtures.tsv|expected) continue ;;
        esac
        [ -n "${fixtures[${base%%.*}]:-}" ] \
            || die "$base is claimed by no row of $manifest — add a row or delete the file"
    done
    for f in "$expected"/*; do
        # A first capture finds the expected/ directory empty.  The glob then
        # stays unexpanded.
        [ -e "$f" ] || continue
        [ -n "${claimed[$(basename "$f")]:-}" ] \
            || die "$(basename "$f") is claimed by no row of $manifest — add a row or delete the file"
    done
}
