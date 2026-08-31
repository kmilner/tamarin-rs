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
#   NO_HS_CACHE=1     ignore the raw HS cache
#   HS_CANON_CACHE    cache dir (default <script_dir>/.hs_canon_cache); HS raw
#                     stdout is cached/reused as <key>.full.gz, where key is
#                     sha256(theory)[__i<includes>][__o<oracle scripts>]__<lemma>__v<CACHE_VERSION>[__f<flags>]
#                     __b<oracle-binary fingerprint>. corpus_raw_diff.sh
#                     fingerprints its flagless entries the same way, so they
#                     are exchanged with this script's
#                     (a flagged run salts __f and stays distinct).
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
# Shared gate plumbing (gate_common.sh): OOM prologue, strip_env_lines,
# flags_for, the oracle fingerprint recipe.
[ -r "$script_dir/gate_common.sh" ] || { echo "diff_proof_raw: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
[ -r "$script_dir/proof_diff_common.sh" ] || { echo "diff_proof_raw: missing proof_diff_common.sh" >&2; exit 2; }
. "$script_dir/proof_diff_common.sh"
# OOM discipline: the provers below die alone at the cap, not the session.
oom_prologue
CACHE_VERSION="${CACHE_VERSION:-1}"

# --- per-file canonical flags (see file_flags.tsv) ---
# Some theories need flags beyond bare `--prove` (e.g. --diff, --auto-sources)
# to run the way HS intends; bare runs time out / produce nothing. Look up the
# file's canonical flags (gate_common's flags_for, relpath under examples/)
# and pass them to BOTH HS and RS; salt the cache key so a flagged entry is
# distinct from the bare one.
FLAGS_MAP="${FLAGS_MAP:-$script_dir/file_flags.tsv}"
file_rel="${file#"$repo_root"/tamarin-prover/examples/}"; file_rel="${file_rel#tamarin-prover/examples/}"
EXTRA_FLAGS="$(flags_for "$file_rel")"
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

hs_path=$(resolve_hs_oracle "$repo_root") || exit 2
# Oracle-binary fingerprint (gate_common's hs_fingerprint), salted into the
# cache key below: sha256(theory)+lemma cannot see the ORACLE changing, so a
# rebuilt oracle would keep being answered out of the previous one's entries.
hs_fingerprint "$hs_path"

# `tamarin-prover` is the PACKAGE; its only bin target is `tamarin-rs`, so
# --bin tamarin-prover selects nothing and cargo errors out.
if [ -z "${TAM_RS_NO_AUTO_BUILD:-}" ]; then
    if ! cargo build --release -p tamarin-prover \
            --manifest-path "$repo_root/Cargo.toml" >&2; then
        echo "diff_proof_raw.sh: cargo build -p tamarin-prover failed" >&2
        exit 2
    fi
fi
rs_path="$repo_root/target/release/tamarin-rs"
if [ ! -x "$rs_path" ]; then
    echo "diff_proof_raw.sh: RS binary not built at $rs_path" >&2
    exit 2
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# strip_env_lines (gate_common.sh): the triage policy — delete only the three
# unreproducible lines, keep `analyzed:` visible (the cache hit below rewrites
# its path to this invocation's).

# --- HS (shared raw cache).
key=""
if [ -z "$NO_HS_CACHE" ]; then
    key="$HS_CANON_CACHE/$(proof_cache_key "$file" "$lemma" "$EXTRA_FLAGS")"
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
    # >=128 is a signal death (OOM's 137), which truncates stdout the same way
    # the timeout does — bail before the cache write below can keep it.
    if [ "$hs_rc" -eq 124 ] || [ "$hs_rc" -ge 128 ]; then
        echo "$lemma: HS TIMEOUT/KILLED (rc=$hs_rc, cap ${TIMEOUT}s)"
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
