#!/usr/bin/env bash
# RS-vs-HS performance benchmark → markdown tables.
#
# Runs each representative theory file through BOTH provers at several core
# counts, measuring wall-clock and peak resident memory.  Emits one markdown
# table per core count, wrapped in `<!-- BENCH:START -->` / `<!-- BENCH:END -->`
# markers, so the block can be written to docs/PERFORMANCE.md.
#
#   scripts/bench.sh            # measure, print the block to stdout
#   scripts/bench.sh --write    # measure, then rewrite the block IN PLACE
#                                     #   between the markers in docs/PERFORMANCE.md
#
# Env knobs:
#   FILES        space-separated relpaths under examples/ (default: representative set)
#   CORES        space-separated core counts            (default: "1 4 16")
#   TIMEOUT      per-run wall-clock cap, seconds        (default: 600)
#   DERIV        --derivcheck-timeout passed to both    (default: 30)
#   HS_PATH / RS_PATH    override the prover binaries
#   README_PATH  file to rewrite in --write mode        (default: docs/PERFORMANCE.md)
#   ALLOW_ORACLE_REV_MISMATCH=1 permit --write with an HS baseline other than
#                          the attested build of the pinned upstream revision
#
# Methodology:
#   - Core control: HS `+RTS -Nk -RTS`; RS `--processors=k` (its Maude pool
#     defaults to max(1, k), a 1:1 workers:maudes ratio).  Both prove all
#     lemmas (`--prove`).
#   - "peak RSS" is the largest sampled SUM across the command's live process
#     tree, so the prover, Maude workers, and re-verification phase are counted.
#   - Single run per cell (wall-clock is noisy by ±10%; magnitudes are stable).
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
CORPUS="$repo_root/tamarin-prover/examples"
README_PATH="${README_PATH:-$repo_root/docs/PERFORMANCE.md}"
TIMEOUT="${TIMEOUT:-600}"
DERIV="${DERIV:-30}"
CORES="${CORES:-1 4 16}"
FILES="${FILES:-classic/NSPK3.spthy ake/bilinear/Joux.spthy features/auto-sources/tamarin-repo/sapic/statVerifLeftRight/stateverif_left_right.spthy sapic/fast/Yubikey/Yubikey.spthy accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy csf19-wrapping/gcm.spthy wireguard/wireguard.spthy features/auto-sources/spore/CCITT_X509_3.spthy}"

case "$DERIV" in *[!0-9]*|'') echo "bench.sh: DERIV must be an integer" >&2; exit 2 ;; esac

cpu_count() {
    nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo unknown
}

WRITE=0
for arg in "$@"; do
    case "$arg" in
        --write) WRITE=1 ;;
        -h|--help) sed -n '2,30p' "$0"; exit 0 ;;
        *) echo "bench.sh: unknown argument '$arg' (try --write or --help)" >&2; exit 2 ;;
    esac
done

# Default HS baseline: the oracle the parity gates use (the ./setup.sh testing
# build of the pinned upstream revision, which Rust's proofs follow; a release
# can lack the replay fixes those proofs need). HS_PATH overrides.
[ -r "$script_dir/gate_common.sh" ] || exit 2
. "$script_dir/gate_common.sh"
HS_PATH="$(resolve_hs_oracle "$repo_root")" || exit 2
MAUDE="$(resolve_maude)" || exit 2
RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
[ -x "$RS_PATH" ] || { echo "bench.sh: no RS binary at $RS_PATH" >&2; exit 2; }
if command -v gtime >/dev/null 2>&1; then
    TIME_BIN="$(command -v gtime)"
elif /usr/bin/time -f '%e' -o /dev/null true 2>/dev/null; then
    TIME_BIN=/usr/bin/time
else
    echo "bench.sh: needs GNU time (install Homebrew's time package on macOS)" >&2
    exit 2
fi

# Baseline identity check: the generated block names the pinned upstream
# revision as the HS baseline, so --write requires the attested oracle build
# (ALLOW_ORACLE_REV_MISMATCH=1 overrides); a plain run only warns.
[ "$WRITE" = 1 ] || ALLOW_ORACLE_REV_MISMATCH=1
oracle_rev_check "$HS_PATH" "$MAUDE" "$repo_root"

# Sum RSS for root and every descendant present in one `ps` snapshot. Unlike
# GNU time's `ru_maxrss`, this measures simultaneous memory across Maude
# workers rather than the largest individual process.
tree_rss_kb() {
    ps -e -o pid=,ppid=,rss= 2>/dev/null | awk -v root="$1" '
        { parent[$1]=$2; rss[$1]=$3; ids[NR]=$1 }
        END {
            live[root]=1
            do {
                changed=0
                for (i=1; i<=NR; i++) {
                    p=ids[i]
                    if (!live[p] && live[parent[p]]) { live[p]=1; changed=1 }
                }
            } while (changed)
            total=0
            for (p in live) if (live[p]) total += rss[p]
            print total+0
        }'
}

# measure <cmd...> → prints "<secs>|<mb>" ("timeout|—" on cap, "fail:<rc>|—"
# on a nonzero exit). Wall time comes from GNU time; memory is sampled from the
# whole live process tree every 20 ms.
measure() {
    local timing rc wall rss now pid
    timing=$(mktemp)
    "$TIME_BIN" -f '%e' -o "$timing" timeout "$TIMEOUT" "$@" >/dev/null 2>/dev/null &
    pid=$!
    rss=0
    while kill -0 "$pid" 2>/dev/null; do
        now=$(tree_rss_kb "$pid")
        [ "$now" -gt "$rss" ] && rss=$now
        sleep 0.02
    done
    wait "$pid"; rc=$?
    if [ "$rc" = 124 ]; then rm -f "$timing"; printf 'timeout|—'; return; fi
    if [ "$rc" != 0 ]; then rm -f "$timing"; printf 'fail:%s|—' "$rc"; return; fi
    wall=$(cat "$timing")
    rm -f "$timing"
    awk -v w="$wall" -v k="$rss" 'BEGIN{ printf "%.1f|%.0f", w, k/1024 }'
}

cell_t() { case "$1" in timeout) printf 'timeout' ;; fail:*) printf 'fail' ;; *) printf '%s s' "$1" ;; esac; }
cell_m() { [ "$1" = "—" ] && printf '—' || printf '%s MB' "$1"; }

# pct <rs> <hs> → " (-44%)" (RS vs HS; negative = lower).  Empty when either
# side is non-numeric (timeout / — / zero baseline) so no bogus % is shown.
pct() {
    awk -v rs="$1" -v hs="$2" 'BEGIN{
        if (rs !~ /^[0-9.]+$/ || hs !~ /^[0-9.]+$/ || hs+0==0) { exit }
        printf " (%+.0f%%)", (rs-hs)/hs*100 }'
}
# RS cells: value + parenthetical % vs the HS value in the same row.
cell_rs_t() { case "$1" in timeout) printf 'timeout' ;; fail:*) printf 'fail' ;; *) printf '%s s%s' "$1" "$(pct "$1" "$2")" ;; esac; }
cell_rs_m() { [ "$1" = "—" ] && printf '—' || printf '%s MB%s' "$1" "$(pct "$1" "$2")"; }

# Emit the full marker block (header comment + per-core tables) to stdout.
gen_block() {
    local load_flags=(--with-maude="$MAUDE" --derivcheck-timeout="$DERIV")
    # Static header comment.  Kept in sync with the benchmark prose; this is the
    # single source of truth for "where do these numbers come from".
    cat <<'HDR' | sed "s/@DERIV@/$DERIV/g"
<!-- BENCH:START — auto-generated by scripts/bench.sh; do not edit by hand.

Regenerate these three tables in place:

    scripts/bench.sh --write     # measure, then rewrite this block
    scripts/bench.sh             # measure, print to stdout only

The HS baseline is the tamarin-prover build of the upstream revision this
repo pins (`./setup.sh testing`; the revision is in the "last run" line
below), the prover whose proofs Rust's follow.

Both provers prove every lemma (--prove --derivcheck-timeout=@DERIV@); HS at
`+RTS -Nk`, RS at `--processors=k`; wall-clock + peak RSS come from
GNU time plus a 20 ms process-tree sampler. Peak RSS is the largest sum across
all simultaneously live command processes, including Maude workers. Single
run per cell (wall-clock is noisy ±10%).
The RS+HS columns measure ./prove_and_reverify.sh (THREADS=k): prove with RS,
then re-CHECK the emitted proofs with HS — i.e. the total cost of a proof you
did not have to trust the port for; its peak RSS is the max across both
phases. The RS+HS and RS columns show the % change vs HS in parentheses
(negative = faster / less memory). Tune the theory set / core counts /
binaries via the FILES, CORES, TIMEOUT, DERIV, HS_PATH, RS_PATH env vars (see
the scripts/bench.sh header).
-->
HDR
    # oracle_rev_check captured the version line and revision.
    echo "<!-- last run: $(uname -m) $(uname -s), $(cpu_count) cores; HS baseline: ${HS_VERSION%%,*} at ${ORACLE_REVISION:0:8} -->"
    for k in $CORES; do
        echo
        echo "**${k} core$([ "$k" = 1 ] && echo '' || echo 's')**"
        echo
        echo "| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |"
        echo "|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|"
        for f in $FILES; do
            af="$CORPUS/$f"
            base="${f##*/}"; base="${base%.spthy}"
            [ -f "$af" ] || { echo "| \`$base\` | (missing) | | | | | |"; continue; }
            h=$(measure "$HS_PATH" +RTS -N${k} -RTS "${load_flags[@]}" --prove "$af")
            r=$(measure "$RS_PATH" --processors="$k" "${load_flags[@]}" --prove "$af")
            p=$(measure env THREADS="$k" HS_PATH="$HS_PATH" RS_PATH="$RS_PATH" \
                    "$repo_root/prove_and_reverify.sh" "$af" "${load_flags[@]}")
            echo "| \`$base\` | $(cell_t "${h%|*}") | $(cell_rs_t "${p%|*}" "${h%|*}") | **$(cell_rs_t "${r%|*}" "${h%|*}")** | $(cell_m "${h#*|}") | $(cell_rs_m "${p#*|}" "${h#*|}") | **$(cell_rs_m "${r#*|}" "${h#*|}")** |"
        done
    done
    echo
    echo "<!-- BENCH:END -->"
}

block="$(gen_block)"

if [ "$WRITE" = 1 ]; then
    [ -f "$README_PATH" ] || { echo "bench.sh: no benchmark document at $README_PATH" >&2; exit 2; }
    grep -q '<!-- BENCH:START' "$README_PATH" || {
        echo "bench.sh: no <!-- BENCH:START --> marker in $README_PATH" >&2; exit 2; }
    grep -q '<!-- BENCH:END -->' "$README_PATH" || {
        echo "bench.sh: no <!-- BENCH:END --> marker in $README_PATH" >&2; exit 2; }
    bf=$(mktemp); printf '%s\n' "$block" > "$bf"
    tmp=$(mktemp)
    # Replace everything from the BENCH:START line through the BENCH:END line
    # (inclusive) with the freshly generated block, leaving the rest untouched.
    awk -v bf="$bf" '
        BEGIN { while ((getline line < bf) > 0) blk = blk line "\n" }
        /<!-- BENCH:START/ { printf "%s", blk; skip=1; next }
        /<!-- BENCH:END -->/ { skip=0; next }
        !skip { print }
    ' "$README_PATH" > "$tmp" && mv "$tmp" "$README_PATH"
    rm -f "$bf"
    echo "bench.sh: rewrote bench tables in $README_PATH" >&2
else
    printf '%s\n' "$block"
fi
