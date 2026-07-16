#!/bin/bash
# Diff the full canonicalized proof tree (Haskell vs Rust) for EVERY lemma
# across the WHOLE corpus, print a per-lemma diff-line count, and a summary.
#
# Cached, parallelised HS pipeline (same output format / classification):
#   #1  HS canon CACHE keyed by (file-content-sha256, lemma, CACHE_VERSION).
#       HS is canonical and its proof depends only on the .spthy file, so its
#       canon tree is stable across RS-fix iterations -> on repeat runs HS is
#       essentially free.  (Env-gated `-2` lib instrumentation does NOT change
#       the env-off proof, so the cache stays valid across HS rebuilds.)
#   #2  JOBS defaults to nproc.
# RS stays per-lemma (it must be re-run every iteration; per-lemma keeps good
# load balance and the big-lemma proving dominates its parse cost anyway).
# HS is also per-lemma (matching the original): a per-file --prove pre-pass was
# tried and abandoned -- at JOBS=nproc, jcs18-class files each took >15 GB and
# triggered the OOM killer, since one process must prove ALL the file's lemmas
# sequentially.  Per-lemma HS is well load-balanced and OOM-resilient; the
# cache makes warm iterations effectively free anyway.
#
# Corpus enumeration mirrors EXACTLY the cargo test
#   corpus_proof_skeleton_match_probe  (oracle_solver.rs ~L828).
#
# Usage:
#   corpus_full_trace_diff.sh                 # full sweep
#   corpus_full_trace_diff.sh --sample        # tiny built-in sample (validation)
#   corpus_full_trace_diff.sh file1 [file2..] # sweep only the given .spthy files
#
# Env:
#   TIMEOUT=<secs>   per-lemma (RS) + per-file-scaled (HS) wall-clock cap (default 120)
#   JOBS=<n>         parallel workers (default: nproc)
#   EXTRA_ENV="..."  extra env passed to the RS dump_proof binary (e.g.
#                    EXTRA_ENV="TAM_PROVE_DEADLINE_MS=900000")
#   HS_CANON_CACHE=<dir>  HS canon cache dir (default: <script_dir>/.hs_canon_cache)
#   NO_HS_CACHE=1    disable the HS canon cache (always re-run HS)
#   CACHE_VERSION=<n>  bump to invalidate the HS cache if HS *logic* ever changes
#
# Output (stdout): one line per lemma, then a SUMMARY block.
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
canon="$script_dir/canon_proof_tree.py"

TIMEOUT="${TIMEOUT:-120}"
JOBS="${JOBS:-$(nproc)}"
EXTRA_ENV="${EXTRA_ENV:-}"
CORPUS_ROOT="${CORPUS_ROOT:-$repo_root/tamarin-prover/examples}"
CACHE_VERSION="${CACHE_VERSION:-1}"
HS_CANON_CACHE="${HS_CANON_CACHE:-$script_dir/.hs_canon_cache}"
NO_HS_CACHE="${NO_HS_CACHE:-}"
[ -n "$NO_HS_CACHE" ] || mkdir -p "$HS_CANON_CACHE" 2>/dev/null || true

# --- Locate the HS binary. Search worktree-local .stack-work first; fall back to
# the main worktree's .stack-work (git worktree doesn't copy untracked dirs).
find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        if [ -x "$c" ]; then echo "$c"; return 0; fi
    done
    return 1
}
hs_path="$(find_hs_bin "$repo_root" 2>/dev/null || true)"
if [ -z "$hs_path" ]; then
    main_root="$(git -C "$repo_root" worktree list --porcelain 2>/dev/null | awk '/^worktree/{print $2; exit}')"
    if [ -n "$main_root" ] && [ "$main_root" != "$repo_root" ]; then
        hs_path="$(find_hs_bin "$main_root" 2>/dev/null || true)"
    fi
fi
if [ -z "$hs_path" ]; then
    hs_path="$(command -v tamarin-prover 2>/dev/null || true)"
fi
if [ -z "$hs_path" ]; then
    echo "corpus_full_trace_diff.sh: no HS tamarin-prover binary found" >&2
    exit 2
fi

# --- Locate the RS dump_proof binary.
# Always (re)build it first — plain `cargo build --release` does NOT rebuild
# examples, which has silently produced stale-binary measurements. No-op (<1s)
# when already fresh. Skip: TAM_RS_NO_AUTO_BUILD=1.
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    if ! cargo build --release --example dump_proof \
            --manifest-path "$repo_root/Cargo.toml" >&2; then
        echo "corpus_full_trace_diff.sh: cargo build --example dump_proof failed" >&2
        exit 2
    fi
fi
rs_path="$repo_root/target/release/examples/dump_proof"
if [ ! -x "$rs_path" ]; then rs_path="$repo_root/target/debug/examples/dump_proof"; fi
if [ ! -x "$rs_path" ]; then
    echo "corpus_full_trace_diff.sh: dump_proof not built; run \`cargo build --example dump_proof --release\` at the repo root" >&2
    exit 2
fi

# --- HS canon cache key: sha256(file content) + lemma + CACHE_VERSION.
#     Stable across instrumentation rebuilds (proof depends only on file+logic).
hs_cache_key() {
    local f="$1" lemma="$2" h
    h=$(sha256sum "$f" 2>/dev/null | cut -d' ' -f1)
    printf '%s__%s__v%s.canon' "$h" "$lemma" "$CACHE_VERSION"
}

# --- Robust lemma-name list for a file (handles "lemma Foo:", "lemma Foo [..]:",
#     "lemma Foo[..]:", "lemma Foo :").  Strips block comments first so
#     `lemma Foo` inside `/* ... */` doesn't get enumerated (HS-faithful:
#     both provers parse-skip these, so they'd false-categorise as
#     "no HS skeleton" otherwise).  Block comments NEST in Tamarin's
#     grammar (`Theory.Text.Parser.Token.commentStyle`).
lemmas_of() {
    awk '
        BEGIN { depth = 0 }
        {
            line = $0
            while (length(line) > 0) {
                if (depth > 0) {
                    o = index(line, "/*")
                    c = index(line, "*/")
                    if (c == 0 && o == 0) { line = ""; break }
                    if (o > 0 && (c == 0 || o < c)) {
                        depth++; line = substr(line, o + 2)
                    } else {
                        depth--; line = substr(line, c + 2)
                    }
                } else {
                    # Find earliest of //, /*, *
                    lc = index(line, "//")
                    bc = index(line, "/*")
                    if (lc > 0 && (bc == 0 || lc < bc)) {
                        print substr(line, 1, lc - 1); line = ""; break
                    }
                    if (bc > 0) {
                        print substr(line, 1, bc - 1)
                        depth++; line = substr(line, bc + 2)
                    } else {
                        print line; line = ""; break
                    }
                }
            }
        }
    ' "$1" 2>/dev/null \
        | grep '^lemma ' \
        | sed -E 's/^lemma[[:space:]]+([A-Za-z0-9_]+).*/\1/'
}

# --- Slice one lemma's proof block out of a rendered theory and canonicalize.
slice_canon() {
    local lemma="$1" src="$2" dst="$3"
    awk -v lem="^lemma ${lemma}( |\\[|:)" '$0 ~ lem {p=1} p && /^lemma / && !($0 ~ lem) {exit} p' \
        "$src" | python3 "$CANON" > "$dst" 2>/dev/null
}
export -f hs_cache_key lemmas_of slice_canon
export HS_PATH="$hs_path" RS_PATH="$rs_path" CANON="$canon" TIMEOUT EXTRA_ENV \
       HS_CANON_CACHE CACHE_VERSION NO_HS_CACHE

# --- Per-lemma worker. Emits ONE machine-parseable line on stdout:
#       <file>\t<lemma>\t<status>\t<hs_lines>\t<rs_lines>\t<diff>\t<hs_ms>\t<rs_ms>
#     status in {MATCH, DIFF, SKIP_NO_HS, SKIP_RS_ERR, SKIP_TIMEOUT}.
#     hs_ms is "-" when HS came from the canon cache (not re-run).
worker() {
    local f="$1" lemma="$2"
    local tmp; tmp="$(mktemp -d)"
    # shellcheck disable=SC2064
    trap "rm -rf '$tmp'" RETURN

    # --- HS canon: cache (#2) first, else per-lemma fallback.
    # Cache stores 3 outcomes:
    #   <key>.canon   - non-empty proof tree (typical match/diff path)
    #   <key>.empty   - HS produced no skeleton (parsed-only / unprovable;
    #                   classify as SKIP_NO_HS without re-running HS)
    #   <key>.timeout - HS hit the wall-clock timeout last time
    #                   (classify as SKIP_TIMEOUT without re-running HS;
    #                   delete the marker manually to retry, e.g. after
    #                   raising TIMEOUT)
    # Additionally every non-timeout HS run stores the RAW stdout gzipped at
    #   <key>.full.gz - full uncanonicalised HS output (whole rendered theory).
    # The canon entry is derived data; the .full.gz is the source of truth so
    # that a future switch to direct (un-canonicalised) matching does not
    # require re-running HS over the whole corpus.
    # Caching negative outcomes (SKIP_NO_HS / SKIP_TIMEOUT) avoids re-running HS
    # for those lemmas every sweep — the timeout lemmas are the heaviest
    # jcs18 cases, using GB of RAM each, so this keeps warm-sweep CPU low.
    local hs_canon="$tmp/hs.canon" hs_rc=0 hs_ms="-"
    local key="" key_empty="" key_timeout=""
    if [ -z "$NO_HS_CACHE" ]; then
        key="$HS_CANON_CACHE/$(hs_cache_key "$f" "$lemma")"
        key_empty="${key%.canon}.empty"
        key_timeout="${key%.canon}.timeout"
    fi
    if [ -n "$key" ] && [ -f "$key_timeout" ]; then
        # Cached timeout — short-circuit to SKIP_TIMEOUT below.
        hs_rc=124
        : > "$tmp/hs.canon"
    elif [ -n "$key" ] && [ -f "$key_empty" ]; then
        # Cached empty canon — classify as SKIP_NO_HS below.
        : > "$tmp/hs.canon"
        hs_canon="$tmp/hs.canon"
    elif [ -n "$key" ] && [ -f "$key" ]; then
        hs_canon="$key"
    elif [ -n "$key" ] && [ -f "${key%.canon}.full.gz" ]; then
        # Derive the canon entry from the cached raw output (written by this
        # script or by corpus_raw_diff.sh) instead of re-running HS.
        gzip -dc "${key%.canon}.full.gz" 2>/dev/null > "$tmp/hs.full"
        slice_canon "$lemma" "$tmp/hs.full" "$tmp/hs.canon"
        if [ "$(grep -c . "$tmp/hs.canon")" -gt 0 ]; then
            cp -f "$tmp/hs.canon" "$key" 2>/dev/null || true
        else
            : > "$key_empty" 2>/dev/null || true
        fi
    else
        local hs_t0; hs_t0=$(date +%s%3N)
        timeout "$TIMEOUT" "$HS_PATH" +RTS -N1 -RTS --prove="$lemma" "$f" 2>/dev/null > "$tmp/hs.out"
        hs_rc=$?
        hs_ms=$(( $(date +%s%3N) - hs_t0 ))
        slice_canon "$lemma" "$tmp/hs.out" "$tmp/hs.canon"
        if [ -n "$key" ]; then
            if [ "$hs_rc" -eq 124 ]; then
                : > "$key_timeout" 2>/dev/null || true
            else
                gzip -c "$tmp/hs.out" > "${key%.canon}.full.gz" 2>/dev/null || true
                if [ "$(grep -c . "$tmp/hs.canon")" -gt 0 ]; then
                    cp -f "$tmp/hs.canon" "$key" 2>/dev/null || true
                else
                    : > "$key_empty" 2>/dev/null || true
                fi
            fi
        fi
    fi

    # HS timed out (cached marker or live run): skip the RS run entirely —
    # the lemma is SKIP_TIMEOUT either way, and HS-timeout lemmas are exactly
    # where RS's unbounded search OOMs the machine (17-43 GB RSS observed).
    if [ "$hs_rc" -eq 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "0" "0" "-" "$hs_ms" "-"
        return 0
    fi

    # --- RS: dump_proof emits only the proof tree for this lemma (per-lemma).
    local rs_t0; rs_t0=$(date +%s%3N)
    timeout "$TIMEOUT" env $EXTRA_ENV "$RS_PATH" "$f" "$lemma" 2>/dev/null | python3 "$CANON" > "$tmp/rs.canon" 2>/dev/null
    local rs_rc=${PIPESTATUS[0]}
    local rs_ms=$(( $(date +%s%3N) - rs_t0 ))

    local hs_lines rs_lines d
    hs_lines=$(grep -c . "$hs_canon"); hs_lines=${hs_lines// /}
    rs_lines=$(grep -c . "$tmp/rs.canon"); rs_lines=${rs_lines// /}

    if [ "$hs_rc" -eq 124 ] || [ "$rs_rc" -eq 124 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_TIMEOUT" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$hs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_NO_HS" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi
    if [ "$rs_lines" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "SKIP_RS_ERR" "$hs_lines" "$rs_lines" "-" "$hs_ms" "$rs_ms"
        return 0
    fi

    d=$(diff "$hs_canon" "$tmp/rs.canon" 2>/dev/null | wc -l); d=${d// /}
    if [ "$d" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "MATCH" "$hs_lines" "$rs_lines" "0" "$hs_ms" "$rs_ms"
    else
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "$lemma" "DIFF" "$hs_lines" "$rs_lines" "$d" "$hs_ms" "$rs_ms"
    fi
    return 0
}
export -f worker

# --- File-content filter (mirror corpus_proof_skeleton_match_probe exactly).
# Builtins (diffie-hellman/multiset/xor/bilinear-pairing) and macros are
# supported and, like the probe, not filtered here.
file_is_comparable() {
    local f="$1"
    grep -q 'diff('       "$f" 2>/dev/null && return 1
    grep -q 'predicates:' "$f" 2>/dev/null && return 1
    grep -q 'process:'    "$f" 2>/dev/null && return 1
    return 0
}

# --- Build the list of candidate files.
declare -a files=()
case "${1:-}" in
    --sample)
        for cand in \
            "$CORPUS_ROOT/loops/Typing_and_Destructors.spthy" \
            "$CORPUS_ROOT/classic/NSPK3.spthy"; do
            [ -f "$cand" ] && files+=("$cand")
        done
        for cand in "$CORPUS_ROOT"/*/*.spthy; do
            if [ -f "$cand" ] && grep -q 'builtins:' "$cand" 2>/dev/null && \
               grep -Eq 'diffie-hellman|multiset|xor|bilinear-pairing' "$cand" 2>/dev/null; then
                files+=("$cand"); break
            fi
        done
        ;;
    "" )
        # Whole examples/ tree; content filters above still apply.
        while IFS= read -r cand; do
            case "$cand" in */testParser/include/*) continue;; esac
            files+=("$cand")
        done < <(find "$CORPUS_ROOT" -name '*.spthy' 2>/dev/null | sort)
        ;;
    *)
        for cand in "$@"; do [ -f "$cand" ] && files+=("$cand"); done
        ;;
esac

# --- Emit the (file, lemma) task list + the comparable-file list.
tasklist="$(mktemp)"
filelist="$(mktemp)"
filtered_files=0
total_files=0
for f in "${files[@]}"; do
    total_files=$((total_files+1))
    if ! file_is_comparable "$f"; then
        filtered_files=$((filtered_files+1))
        continue
    fi
    printf '%s\n' "$f" >> "$filelist"
    while IFS= read -r lem; do
        [ -n "$lem" ] && printf '%s\t%s\n' "$f" "$lem" >> "$tasklist"
    done < <(lemmas_of "$f")
done

n_tasks=$(wc -l < "$tasklist"); n_tasks=${n_tasks// /}
n_files=$(wc -l < "$filelist"); n_files=${n_files// /}
echo "# corpus_full_trace_diff: $n_tasks lemmas across $((total_files-filtered_files)) files (filtered out $filtered_files of $total_files), JOBS=$JOBS, TIMEOUT=${TIMEOUT}s, HS-cache=$([ -n "$NO_HS_CACHE" ] && echo off || echo "$HS_CANON_CACHE")" >&2

# --- MAIN PASS: per-lemma RS + per-lemma HS (cached), parallel over lemmas.
results="$(mktemp)"
trap "rm -f '$tasklist' '$filelist' '$results'" EXIT
tr '\t' '\n' < "$tasklist" | xargs -d '\n' -P "$JOBS" -n 2 bash -c 'worker "$0" "$1"' > "$results"

sort -t$'\t' -k1,1 -k2,2 "$results" > "$results.sorted"

match=0; diffn=0; skip_no_hs=0; skip_rs_err=0; skip_timeout=0
declare -a divergent=() rs_times=() hs_times=()
declare -a rs_slow=() hs_slow=()
while IFS=$'\t' read -r f lem status hs rs d hs_ms rs_ms; do
    hs_ms="${hs_ms:--}"; rs_ms="${rs_ms:--}"
    if [ "$hs_ms" = "-" ]; then t=" [hs:cache rs:${rs_ms}ms]"; else t=" [hs:${hs_ms}ms rs:${rs_ms}ms]"; fi
    case "$status" in
        MATCH)        match=$((match+1));        echo "$f::$lem: MATCH (HS:$hs, RS:$rs)$t";;
        DIFF)         diffn=$((diffn+1));         echo "$f::$lem: $d diff lines (HS:$hs, RS:$rs)$t"; divergent+=("$d"$'\t'"$f::$lem (HS:$hs, RS:$rs)");;
        SKIP_NO_HS)   skip_no_hs=$((skip_no_hs+1));   echo "$f::$lem: SKIP (no HS skeleton)$t";;
        SKIP_RS_ERR)  skip_rs_err=$((skip_rs_err+1)); echo "$f::$lem: SKIP (RS produced no tree; HS:$hs)$t";;
        SKIP_TIMEOUT) skip_timeout=$((skip_timeout+1)); echo "$f::$lem: SKIP (timeout ${TIMEOUT}s)$t";;
        *)            echo "$f::$lem: SKIP (unknown status '$status')"; skip_no_hs=$((skip_no_hs+1));;
    esac
    if [ "$rs_ms" != "-" ]; then
        rs_times+=("$rs_ms"); rs_slow+=("$rs_ms"$'\t'"$status"$'\t'"$f::$lem")
    fi
    if [ "$hs_ms" != "-" ]; then
        hs_times+=("$hs_ms"); hs_slow+=("$hs_ms"$'\t'"$status"$'\t'"$f::$lem")
    fi
done < "$results.sorted"
rm -f "$results.sorted"

# --- Timing distribution helpers (input: array of ms values).
pctl() { # pctl <p> <sorted-file>
    local n; n=$(wc -l < "$2"); [ "$n" -eq 0 ] && { echo "-"; return; }
    local i=$(( (n * $1 + 99) / 100 )); [ "$i" -lt 1 ] && i=1
    sed -n "${i}p" "$2"
}
print_timing() { # print_timing <label> <times-array-name> <slow-array-name>
    local -n times_ref=$2 slow_ref=$3
    local n=${#times_ref[@]}
    if [ "$n" -eq 0 ]; then echo "$1: no timed runs"; return; fi
    local sorted; sorted="$(mktemp)"
    printf '%s\n' "${times_ref[@]}" | sort -n > "$sorted"
    echo "$1 ($n timed runs, ms): p50=$(pctl 50 "$sorted") p90=$(pctl 90 "$sorted") p99=$(pctl 99 "$sorted") max=$(pctl 100 "$sorted")"
    echo "  slowest:"
    printf '%s\n' "${slow_ref[@]}" | sort -t$'\t' -k1,1nr | head -10 | \
        awk -F'\t' '{printf "    %8dms  %-12s %s\n", $1, $2, $3}'
    rm -f "$sorted"
}

total=$((match+diffn+skip_no_hs+skip_rs_err+skip_timeout))
echo ""
echo "================ SUMMARY ================"
echo "total lemmas enumerated : $total"
echo "  0 diff (MATCH)        : $match"
echo "  divergent (DIFF)      : $diffn"
echo "  skipped               : $((skip_no_hs+skip_rs_err+skip_timeout))"
echo "      no HS skeleton    : $skip_no_hs"
echo "      RS no tree/err    : $skip_rs_err"
echo "      timeout (${TIMEOUT}s)  : $skip_timeout"
if [ "${#divergent[@]}" -gt 0 ]; then
    echo ""
    echo "divergent lemmas (largest diff first):"
    printf '%s\n' "${divergent[@]}" | sort -t$'\t' -k1,1nr | sed 's/^/  /; s/\t/ diff lines: /'
fi
echo ""
echo "================ TIMING ================"
print_timing "RS" rs_times rs_slow
print_timing "HS (uncached only)" hs_times hs_slow
