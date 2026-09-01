#!/usr/bin/env bash
# 3-way triage for files the RS-vs-RS sweep flagged as DIFF: for each file,
# compare RS-prepatch and RS-patched against FRESH Haskell, to decide whether
# the refactor moved RS TOWARD HS (improvement) or AWAY (regression).
#   d_pre  = diff(HS, RS-prepatch)   d_post = diff(HS, RS-patched)
#   d_post < d_pre  -> IMPROVED ;  d_post > d_pre -> REGRESSED ;
#   d_post==d_pre but content differs -> CHANGED(check) ; both 0 -> already-match
#
# Reads/fills corpus_file_diff.sh's HS cache (.hs_file_cache) at gate_common's
# fingerprinted ckey, and runs all three binaries with the file's canonical
# flags from file_flags.tsv (the same flags the sweep that flagged the DIFF
# used) — so a cache entry this script writes is exactly the entry the batch
# gate would have written.
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ -r "$script_dir/gate_common.sh" ] || { echo "triage_diff_vs_hs: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
# OOM discipline: three prover runs per file — each dies alone at the cap.
oom_prologue
ROOT="${ROOT:-$(cd "$script_dir/.." && pwd)}"
CORPUS="${CORPUS:-$ROOT/tamarin-prover/examples}"
PRE="${PRE:-/tmp/rs-prepatch}"; POST="${POST:-/tmp/rs-patched}"
DERIV="${DERIV:-30}"; FT="${FT:-300}"
CACHE="${CACHE:-$ROOT/scripts/.hs_file_cache}"
FLAGS_MAP="${FLAGS_MAP:-$ROOT/scripts/file_flags.tsv}"
HS="${HS:-$(ls $ROOT/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover 2>/dev/null | head -1)}"
# The oracle binary is required even on a fully-warm cache: its fingerprint is
# part of the cache key, so entries cannot be looked up without it.
[ -x "${HS:-/nonexistent}" ] || { echo "triage_diff_vs_hs: no HS oracle binary (set HS=) — the cache key carries the oracle's fingerprint" >&2; exit 2; }
hs_fingerprint "$HS"

for rel in "$@"; do
  f="$CORPUS/$rel"
  [ -f "$f" ] || { echo "MISSING $rel"; continue; }
  key=$(ckey "$rel" "$f")
  fl=$(flags_for "$rel")
  # Haskell: prefer cache; else run fresh and cache it (the entry lands under
  # the same key corpus_file_diff.sh computes, so the batch gate reuses it).
  # The fill follows hs_one's discipline: rc captured from a temp file (a
  # pipeline's $? would be strip_env's), NOTHING cached on a timeout — a
  # killed run's partial stdout must not become the gate's reference — and
  # .rc/.flags written before the payload, so the entry is byte-for-byte what
  # the batch gate's own Phase 1 would have written.  No sticky .nohs/.timeout
  # markers, though: minting those is the batch gate's call, not a triage's.
  if [ -f "$CACHE/$key.full.gz" ]; then hs=$(zcat "$CACHE/$key.full.gz");
  else
    echo "  (no HS cache for $rel — running fresh, up to ${FT}s)"
    tmp=$(mktemp)
    # shellcheck disable=SC2086  # $fl must word-split into separate flags
    timeout "$FT" "$HS" +RTS -N4 -M11g -RTS $fl --derivcheck-timeout="$DERIV" --prove "$f" >"$tmp" 2>/dev/null
    rc=$?
    hs=$(strip_env < "$tmp"); rm -f "$tmp"
    # 124 is timeout(1)'s status; >=128 is any other signal death (the OOM
    # killer's 137), which truncates stdout the same way — neither may be
    # cached, and neither can be triaged against.
    if [ "$rc" = 124 ] || [ "$rc" -ge 128 ]; then
      hs=""
    elif [ -n "$hs" ]; then
      [ -n "$fl" ] && printf '%s' "$fl" > "$CACHE/$key.flags"
      printf '%s' "$rc" > "$CACHE/$key.rc"
      printf '%s' "$hs" | gzip > "$CACHE/$key.full.gz"
    fi
  fi
  if [ -z "$hs" ]; then echo "NO_HS   $rel (HS timed out/empty — cannot triage)"; continue; fi
  # shellcheck disable=SC2086
  pre=$(timeout "$FT" "$PRE"  $fl --derivcheck-timeout="$DERIV" --prove "$f" 2>/dev/null | strip_env)
  # shellcheck disable=SC2086
  post=$(timeout "$FT" "$POST" $fl --derivcheck-timeout="$DERIV" --prove "$f" 2>/dev/null | strip_env)
  dpre=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$pre")  | grep -c '^[<>]')
  dpost=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$post") | grep -c '^[<>]')
  verdict="CHANGED"
  if [ "$dpost" -lt "$dpre" ]; then verdict="IMPROVED ✅"; fi
  if [ "$dpost" -gt "$dpre" ]; then verdict="REGRESSED ❌"; fi
  if [ "$dpost" = 0 ] && [ "$dpre" = 0 ]; then verdict="both-match"; fi
  printf '%-55s d(HS,pre)=%-5s d(HS,post)=%-5s  %s\n' "$rel" "$dpre" "$dpost" "$verdict"
done
