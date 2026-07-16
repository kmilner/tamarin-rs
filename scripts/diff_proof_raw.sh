#!/bin/bash
# Per-lemma RAW diff: full `--prove` stdout of the Haskell prover vs the Rust
# BINARY, byte-for-byte, stripping only the environment-dependent lines
# (Git revision / Compiled at / processing time). No canonicalisation.
#
# This is the per-lemma iteration tool for the raw-matching campaign; the
# corpus-wide counterpart is corpus_raw_diff.sh, and the older canonicalised
# pipeline (diff_proof_tree.sh / canon_proof_tree.py) is legacy.
#
# Usage:
#   diff_proof_raw.sh <file.spthy> <lemma> ["ENV1=v1 ENV2=v2"]
#     3rd arg: extra env vars for the RS run (e.g. "TAM_PROVE_DEADLINE_MS=900000")
#
# Env:
#   TIMEOUT=<secs>    wall-clock cap per side (default 300)
#   RS_TIMEOUT=<secs> RS-side cap (default: TIMEOUT). This is the manual
#                     single-lemma tool, so unlike corpus_raw_diff.sh (whose
#                     RS cap defaults to 30s for sweep speed) it lets RS run
#                     the full window by default.
#   QUIET=1           print only the summary line, not the diff body
#   NO_HS_CACHE=1     ignore the shared raw HS cache
#   HS_CANON_CACHE    cache dir (default <script_dir>/.hs_canon_cache); HS raw
#                     stdout is cached/reused as <key>.full.gz, shared with
#                     corpus_raw_diff.sh and corpus_full_trace_diff.sh
#   TAM_RS_NO_AUTO_BUILD=1  skip the cargo rebuild of the RS binary
set -uo pipefail

if [ $# -lt 2 ]; then
    echo "usage: $0 <file.spthy> <lemma> [\"ENV=val ...\"]" >&2
    exit 2
fi
file="$1"; lemma="$2"; extra_env="${3:-}"
TIMEOUT="${TIMEOUT:-300}"
RS_TIMEOUT="${RS_TIMEOUT:-$TIMEOUT}"
QUIET="${QUIET:-}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
CACHE_VERSION="${CACHE_VERSION:-1}"

# --- per-file canonical flags (see file_flags.tsv) ---
# Some theories need flags beyond bare `--prove` (e.g. --diff, --auto-sources)
# to run the way HS intends; bare runs time out / produce nothing. Look up the
# file's canonical flags (relpath under examples/) and pass them to BOTH HS and
# RS; salt the cache key so a flagged entry is distinct from the bare one.
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
file_rel="${file#"$repo_root"/tamarin-prover/examples/}"; file_rel="${file_rel#tamarin-prover/examples/}"
EXTRA_FLAGS=""
if [ -f "$FLAGS_MAP" ]; then
    EXTRA_FLAGS="$(awk -F'\t' -v r="$file_rel" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP")"
fi
FLAGS_SALT=""
[ -n "$EXTRA_FLAGS" ] && FLAGS_SALT="__f$(printf '%s' "$EXTRA_FLAGS" | sha256sum | cut -c1-12)"
[ -n "$EXTRA_FLAGS" ] && echo "diff_proof_raw: $file_rel canonical flags: $EXTRA_FLAGS" >&2
# Deriv-check timeout (secs) passed to BOTH binaries so the message-derivation
# section is compared deterministically.  HS's DEFAULT is 5s, which fires on
# heavy theories and records a "Derivation checks timed out" placeholder while
# RS (computing fully) shows the real results — a spurious DIFF.  30s lets both
# compute fully on the corpus (deriv-check output verified faithful when both run).
DERIVCHECK_TIMEOUT="${DERIVCHECK_TIMEOUT:-30}"
HS_CANON_CACHE="${HS_CANON_CACHE:-$script_dir/.hs_canon_cache}"
NO_HS_CACHE="${NO_HS_CACHE:-}"
# HS RTS flags. Upstream commit 00a282da ("Canonicalise maude's returned
# substitution entries", Maude/Types.hs:134) made HS proofs schedule-
# INDEPENDENT — `+RTS -Nk` for any k now yields byte-identical proofs
# (verified on UM3: all -N share md5 cd93570e…). So we no longer force
# single-thread; HS_RTS defaults to `-N` (all cores) to speed up cache
# regeneration. Override `HS_RTS=-N1` to reproduce the pre-canonicalisation
# single-thread reference if ever needed.
HS_RTS="${HS_RTS:--N}"
[ -n "$NO_HS_CACHE" ] || mkdir -p "$HS_CANON_CACHE" 2>/dev/null || true

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
[ -z "$hs_path" ] && hs_path="$(command -v tamarin-prover 2>/dev/null || true)"
if [ -z "$hs_path" ]; then
    echo "diff_proof_raw.sh: no HS tamarin-prover binary found" >&2
    exit 2
fi

if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    if ! cargo build --release --bin tamarin-prover \
            --manifest-path "$repo_root/Cargo.toml" >&2; then
        echo "diff_proof_raw.sh: cargo build --bin tamarin-prover failed" >&2
        exit 2
    fi
fi
rs_path="$repo_root/target/release/tamarin-prover"
if [ ! -x "$rs_path" ]; then
    echo "diff_proof_raw.sh: RS binary not built at $rs_path" >&2
    exit 2
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

strip_env_lines() {
    grep -v -e '^Git revision:' -e '^Compiled at:' -e '^[[:space:]]*processing time:' "$1"
}

# --- HS (shared raw cache).
key=""
if [ -z "$NO_HS_CACHE" ]; then
    h=$(sha256sum "$file" 2>/dev/null | cut -d' ' -f1)
    key="$HS_CANON_CACHE/${h}__${lemma}__v${CACHE_VERSION}${FLAGS_SALT}"
fi
if [ -n "$key" ] && [ -f "$key.full.gz" ]; then
    # The cache is keyed by file CONTENT, but HS echoes the input path verbatim
    # on its "analyzed:" line. A hit recorded from another checkout/worktree
    # would otherwise produce a spurious path-only diff — rewrite it to the
    # path of THIS invocation (exactly what HS would print for it).
    gzip -dc "$key.full.gz" 2>/dev/null \
        | awk -v f="$file" '/^analyzed: / { print "analyzed: " f; next } { print }' \
        > "$tmp/hs.out"
    hs_src="cache"
else
    # shellcheck disable=SC2086  # $EXTRA_FLAGS must word-split into flags
    timeout "$TIMEOUT" "$hs_path" +RTS $HS_RTS -RTS $EXTRA_FLAGS --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove="$lemma" "$file" 2>/dev/null > "$tmp/hs.out"
    hs_rc=$?
    if [ "$hs_rc" -eq 124 ]; then
        echo "$lemma: HS TIMEOUT (${TIMEOUT}s)"
        exit 1
    fi
    # Never cache empty HS output (startup failures poison the cache).
    [ -n "$key" ] && [ -s "$tmp/hs.out" ] && gzip -c "$tmp/hs.out" > "$key.full.gz" 2>/dev/null || true
    hs_src="run"
fi

# --- RS.
# shellcheck disable=SC2086
timeout "$RS_TIMEOUT" env $extra_env "$rs_path" $EXTRA_FLAGS --derivcheck-timeout="$DERIVCHECK_TIMEOUT" --prove="$lemma" "$file" 2>/dev/null > "$tmp/rs.out"
rs_rc=$?
if [ "$rs_rc" -eq 124 ]; then
    echo "$lemma: RS TIMEOUT (${RS_TIMEOUT}s)"
    exit 1
fi

strip_env_lines "$tmp/hs.out" > "$tmp/hs.cmp"
strip_env_lines "$tmp/rs.out" > "$tmp/rs.cmp"
hs_lines=$(grep -c . "$tmp/hs.cmp")
rs_lines=$(grep -c . "$tmp/rs.cmp")

d=$(diff "$tmp/hs.cmp" "$tmp/rs.cmp" | wc -l); d=${d// /}
echo "$lemma: $d raw diff lines (HS: $hs_lines [$hs_src], RS: $rs_lines)"
if [ "$d" -ne 0 ] && [ -z "$QUIET" ]; then
    diff "$tmp/hs.cmp" "$tmp/rs.cmp"
fi
[ "$d" -eq 0 ]
