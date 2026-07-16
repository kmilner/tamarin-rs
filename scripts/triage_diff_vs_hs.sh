#!/usr/bin/env bash
# 3-way triage for files the RS-vs-RS sweep flagged as DIFF: for each file,
# compare RS-prepatch and RS-patched against FRESH Haskell, to decide whether
# the refactor moved RS TOWARD HS (improvement) or AWAY (regression).
#   d_pre  = diff(HS, RS-prepatch)   d_post = diff(HS, RS-patched)
#   d_post < d_pre  -> IMPROVED ;  d_post > d_pre -> REGRESSED ;
#   d_post==d_pre but content differs -> CHANGED(check) ; both 0 -> already-match
set -u
ROOT="${ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
CORPUS="${CORPUS:-$ROOT/tamarin-prover/examples}"
PRE="${PRE:-/tmp/rs-prepatch}"; POST="${POST:-/tmp/rs-patched}"
DERIV="${DERIV:-30}"; FT="${FT:-300}"
CACHE="${CACHE:-$ROOT/scripts/.hs_file_cache}"
HS="${HS:-$(ls $ROOT/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover 2>/dev/null | head -1)}"
strip_env(){ grep -v -e '^Git revision:' -e '^Compiled at:' -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'; }

for rel in "$@"; do
  f="$CORPUS/$rel"
  [ -f "$f" ] || { echo "MISSING $rel"; continue; }
  key=$(sha256sum "$f" | cut -d' ' -f1)
  # Haskell: prefer cache; else run fresh and cache it.
  if [ -f "$CACHE/$key.full.gz" ]; then hs=$(zcat "$CACHE/$key.full.gz");
  else
    echo "  (no HS cache for $rel — running fresh, up to ${FT}s)"
    hs=$(timeout "$FT" "$HS" +RTS -N4 -M11g -RTS --derivcheck-timeout="$DERIV" --prove "$f" 2>/dev/null | strip_env)
    [ -n "$hs" ] && printf '%s' "$hs" | gzip > "$CACHE/$key.full.gz"
  fi
  if [ -z "$hs" ]; then echo "NO_HS   $rel (HS timed out/empty — cannot triage)"; continue; fi
  pre=$(timeout "$FT" "$PRE"  --derivcheck-timeout="$DERIV" --prove "$f" 2>/dev/null | strip_env)
  post=$(timeout "$FT" "$POST" --derivcheck-timeout="$DERIV" --prove "$f" 2>/dev/null | strip_env)
  dpre=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$pre")  | grep -c '^[<>]')
  dpost=$(diff <(printf '%s\n' "$hs") <(printf '%s\n' "$post") | grep -c '^[<>]')
  verdict="CHANGED"
  if [ "$dpost" -lt "$dpre" ]; then verdict="IMPROVED ✅"; fi
  if [ "$dpost" -gt "$dpre" ]; then verdict="REGRESSED ❌"; fi
  if [ "$dpost" = 0 ] && [ "$dpre" = 0 ]; then verdict="both-match"; fi
  printf '%-55s d(HS,pre)=%-5s d(HS,post)=%-5s  %s\n' "$rel" "$dpre" "$dpost" "$verdict"
done
