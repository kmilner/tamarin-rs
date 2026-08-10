#!/usr/bin/env bash
# ONE-TIME, IDEMPOTENT re-keying of the HS oracle caches onto the
# fingerprint-bearing key the gates now compute.
#
# WHY: the caches used to be keyed by sha256(theory)[+flags hash], which cannot
# see the ORACLE changing.  A rebuilt oracle kept being answered out of the
# previous one's entries, so a gate could report byte parity against an
# upstream that was no longer checked out.  corpus_file_diff.sh, pretty_gate.sh,
# wf_gate.sh and diff_proof_raw.sh now salt the key with the oracle binary's
# fingerprint (`stat -c '%s.%Y'`, sweep_common.sh:262's recipe):
#
#   .hs_file_cache / .hs_pretty_cache
#       <sha256(theory)>[__f<12 hex flags>]__b<12 hex fingerprint>.<suffix>
#   .hs_canon_cache
#       <sha256(theory)>__<lemma>__v<N>[__f<12 hex flags>]__b<12 hex fp>.<suffix>
#
# Every existing entry becomes a MISS under those keys.  The entries are not
# stale, though — the certified battery ran against them with the oracle that
# is checked out right now — so this script renames them onto the new key
# instead of making the next gate spend 30-60 min regenerating them.
#
# It is a MIGRATION, not a gate: run it ONCE, right after the fingerprint
# change lands and before the next gate run.  Running it again is a no-op
# (everything is already suffixed).  It never runs the oracle on a theory and
# never writes cache CONTENT — only `mv`.
#
# Env:
#   DRY_RUN=1                    report what would move, move nothing
#   HS_PATH                      oracle binary (default: the stack-work build)
#   MAUDE_PATH                   maude for the `--version` revision probe
#   ALLOW_ORACLE_REV_MISMATCH=1  migrate anyway when the oracle is not the pin
#   CACHES="dir1 dir2 ..."       override the cache list (testing)
set -u

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
DRY_RUN="${DRY_RUN:-}"
MAUDE="${MAUDE_PATH:-/home/linuxbrew/.linuxbrew/bin/maude}"

find_hs_bin() {
    local root="$1" c
    for c in "$root"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$root"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_bin "$repo_root")}" || true
[ -x "${HS_PATH:-/nonexistent}" ] || {
    echo "migrate_hs_cache_fp: no HS oracle binary (set HS_PATH) — the new key IS its fingerprint, so there is nothing to migrate onto" >&2
    exit 2
}
HS_FP=$(stat -c '%s.%Y' "$HS_PATH")
HS_FP_SALT=$(printf '%s' "$HS_FP" | sha256sum | cut -c1-12)

# The premise of this migration is that the CURRENT oracle produced the entries
# being rekeyed.  If the binary is not the build of the submodule pin, that
# premise is false and the rename would stamp another revision's output as this
# one's.  Same policy (and same escape hatch) as sweep_common.sh's preflight.
# The probe needs --with-maude: without it `--version` resolves `maude` on PATH,
# dies before printing `Git revision:` on every box that keeps maude off PATH,
# and the check would pass by having tested nothing — so the outcome is printed
# either way.
rev_check() {
    local pin binrev
    pin=$(git -C "$repo_root" rev-parse :tamarin-prover 2>/dev/null) || pin=
    if [ -x "$MAUDE" ]; then
        binrev=$(timeout 60 "$HS_PATH" --with-maude="$MAUDE" --version 2>/dev/null \
                 | sed -n 's/^Git revision: \([^,]*\),.*/\1/p')
    else
        binrev=""
    fi
    if [ -z "$pin" ]; then echo "oracle revision: NOT CHECKED (no gitlink for tamarin-prover)"; return 0; fi
    if [ -z "$binrev" ]; then
        echo "oracle revision: NOT CHECKED (no 'Git revision:' from --version; maude '$MAUDE' missing?)"
        return 0
    fi
    if [ "$pin" != "$binrev" ]; then
        echo "ERROR: oracle is revision $binrev but the submodule pin is $pin — migrating would" \
             "relabel another upstream's cached output as this one's" \
             "(rebuild with ./setup.sh testing, or ALLOW_ORACLE_REV_MISMATCH=1)" >&2
        [ "${ALLOW_ORACLE_REV_MISMATCH:-0}" = 1 ] || exit 2
        echo "oracle revision: MISMATCH $binrev != $pin (overridden)"
        return 0
    fi
    echo "oracle revision: OK ($binrev == submodule pin)"
}

echo "oracle      : $HS_PATH"
echo "fingerprint : $HS_FP  ->  key suffix __b$HS_FP_SALT"
rev_check
[ -n "$DRY_RUN" ] && echo "MODE        : DRY RUN (nothing will be renamed)"
echo

# migrate_dir <cache-dir>
#   Rename every recognised entry onto the fingerprinted key.  An entry is
#   `<stem>.<suffix>` where <stem> starts with the theory's 64-hex sha256;
#   <suffix> (full.gz, theory.gz, load.gz, timeout, nohs, flags, rc, ...) is
#   carried over untouched, so this stays correct for artifacts added later.
migrate_dir() {
    local dir="$1"
    local moved=0 already=0 other=0 collide=0 unknown=0 failed=0
    local p base stem suffix new
    if [ ! -d "$dir" ]; then
        printf '  %-18s absent — nothing to migrate\n' "$(basename "$dir")"
        return 0
    fi
    shopt -s nullglob
    for p in "$dir"/*; do
        [ -f "$p" ] || continue
        base=${p##*/}
        case "$base" in
            *.*) stem=${base%%.*}; suffix=${base#*.};;
            *)   unknown=$((unknown+1)); continue;;
        esac
        if ! [[ $stem =~ ^[0-9a-f]{64}(__.*)?$ ]]; then
            unknown=$((unknown+1)); continue
        fi
        if [[ $stem =~ __b[0-9a-f]{12}$ ]]; then
            # Already fingerprinted: this run's oracle (idempotent re-run) or
            # another one's (left alone — it is that oracle's evidence).
            if [ "$stem" = "${stem%__b*}__b$HS_FP_SALT" ]; then already=$((already+1))
            else other=$((other+1)); fi
            continue
        fi
        new="$dir/${stem}__b${HS_FP_SALT}.${suffix}"
        if [ -e "$new" ]; then collide=$((collide+1)); continue; fi
        if [ -n "$DRY_RUN" ]; then moved=$((moved+1)); continue; fi
        if mv -n "$p" "$new"; then moved=$((moved+1)); else failed=$((failed+1)); fi
    done
    shopt -u nullglob
    printf '  %-18s migrated=%-5d already=%-5d other-oracle=%-4d collided=%-3d unrecognised=%-3d failed=%d\n' \
        "$(basename "$dir")" "$moved" "$already" "$other" "$collide" "$unknown" "$failed"
    [ "$collide" = 0 ] || echo "      NOTE: $collide entr(ies) already existed under the new key; the" \
        "fingerprinted one wins and the old-key file is now unreachable — delete at leisure."
    [ "$failed" = 0 ] || { echo "      ERROR: $failed rename(s) failed" >&2; return 1; }
    return 0
}

CACHES="${CACHES:-$script_dir/.hs_file_cache $script_dir/.hs_pretty_cache $script_dir/.hs_canon_cache}"
rc=0
# shellcheck disable=SC2086  # $CACHES is a deliberate space-separated list
for d in $CACHES; do
    migrate_dir "$d" || rc=1
    # pretty_gate.sh's old oracle-rev stamp: it could never fire (setup.sh
    # git-applies patches/ without committing, so every patched build bakes in
    # exactly the pin) and nothing reads it now.  Reported, not deleted.
    [ -f "$d/.oracle_rev" ] && echo "      NOTE: $d/.oracle_rev is the retired oracle-rev stamp — no longer read; safe to delete."
done
echo
echo "DONE_MIGRATE_HS_CACHE_FP verdict=$([ "$rc" = 0 ] && echo OK || echo FAILED)"
exit "$rc"
