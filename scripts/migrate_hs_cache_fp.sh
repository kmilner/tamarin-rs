#!/usr/bin/env bash
# IDEMPOTENT re-keying of HS oracle caches onto the binary-SHA fingerprint
# the gates now compute. It handles both pre-fingerprint entries and entries
# keyed by the former size+mtime fingerprint.
#
# WHY: the caches used to be keyed by sha256(theory)[+flags hash], which cannot
# see the ORACLE changing.  A rebuilt oracle kept being answered out of the
# previous one's entries, so a gate could report byte parity against an
# upstream that was no longer checked out.  corpus_file_diff.sh, pretty_gate.sh,
# wf_gate.sh and diff_proof_raw.sh now salt the key with the oracle binary's
# fingerprint (binary SHA-256, gate_common.sh's hs_fingerprint):
#
#   .hs_file_cache / .hs_pretty_cache
#       <sha256(theory)>[__f<12 hex flags>]__b<12 hex fingerprint>.<suffix>
#   .hs_canon_cache
#       <sha256(theory)>__<lemma>__v<N>[__f<12 hex flags>]__b<12 hex fp>.<suffix>
#
# Matching entries are not stale — the certified battery ran against them with
# this exact attested oracle — so this script renames them onto the new key
# instead of making the next gate regenerate them.
#
# It is a migration, not a gate: run it after a fingerprint-recipe change and
# before the next gate. Re-running is a no-op. It never runs the oracle on a
# theory or rewrites captured output; web sidecar writes change identity only.
#
# Env:
#   DRY_RUN=1                    report what would move, move nothing
#   HS_PATH                      oracle binary (default: the stack-work build)
#   MAUDE_PATH                   maude for the optional `--version` revision probe
#   ALLOW_ORACLE_REV_MISMATCH=1  migrate despite failed source attestation
#   CACHES="dir1 dir2 ..."       override the cache list (testing)
set -u

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
# gate_common.sh owns the fingerprint and source-attestation checks this
# migration relies on, so source it rather than duplicating either policy.
[ -r "$script_dir/gate_common.sh" ] || { echo "migrate_hs_cache_fp: missing $script_dir/gate_common.sh (owns the fingerprint recipe)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
DRY_RUN="${DRY_RUN:-}"
MAUDE=
if resolved_maude=$(resolve_maude 2>/dev/null); then
    MAUDE=$resolved_maude
fi

HS_PATH=$(resolve_hs_oracle "$repo_root") || exit 2
[ -x "${HS_PATH:-/nonexistent}" ] || {
    echo "migrate_hs_cache_fp: no HS oracle binary (set HS_PATH) — the new key IS its fingerprint, so there is nothing to migrate onto" >&2
    exit 2
}
oracle_rev_check "$HS_PATH" "$MAUDE" "$repo_root"

echo "oracle      : $HS_PATH"
echo "fingerprint : $HS_FP  ->  key suffix __b$HS_FP_SALT"
echo "legacy      : $HS_FP_LEGACY  ->  old suffix __b$HS_FP_LEGACY_SALT"
echo "oracle source: $ORACLE_SOURCE_STATUS ($ORACLE_SOURCE_NOTE)"
[ -n "$DRY_RUN" ] && echo "MODE        : DRY RUN (nothing will be renamed)"
echo

# migrate_dir <cache-dir>
#   Rename every recognised entry onto the fingerprinted key.  An entry is
#   `<stem>.<suffix>` where <stem> starts with the theory's 64-hex sha256;
#   <suffix> (full.gz, theory.gz, load.gz, timeout, nohs, flags, rc, ...) is
#   carried over untouched, so this stays correct for artifacts added later.
migrate_dir() {
    local dir="$1"
    local moved=0 upgraded=0 already=0 other=0 collide=0 unknown=0 failed=0
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
            # Upgrade this binary's former size+mtime key. Other binaries'
            # entries remain their evidence and are never relabelled.
            if [ "$stem" = "${stem%__b*}__b$HS_FP_SALT" ]; then already=$((already+1))
            elif [ "$stem" = "${stem%__b*}__b$HS_FP_LEGACY_SALT" ]; then
                new="$dir/${stem%__b*}__b${HS_FP_SALT}.${suffix}"
                if [ -e "$new" ]; then collide=$((collide+1))
                elif [ -n "$DRY_RUN" ]; then upgraded=$((upgraded+1))
                elif mv -n "$p" "$new"; then upgraded=$((upgraded+1))
                else failed=$((failed+1)); fi
            else other=$((other+1)); fi
            continue
        fi
        new="$dir/${stem}__b${HS_FP_SALT}.${suffix}"
        if [ -e "$new" ]; then collide=$((collide+1)); continue; fi
        if [ -n "$DRY_RUN" ]; then moved=$((moved+1)); continue; fi
        if mv -n "$p" "$new"; then moved=$((moved+1)); else failed=$((failed+1)); fi
    done
    shopt -u nullglob
    printf '  %-18s migrated=%-5d upgraded=%-5d already=%-5d other-oracle=%-4d collided=%-3d unrecognised=%-3d failed=%d\n' \
        "$(basename "$dir")" "$moved" "$upgraded" "$already" "$other" "$collide" "$unknown" "$failed"
    [ "$collide" = 0 ] || echo "      NOTE: $collide entr(ies) already existed under the new key; the" \
        "fingerprinted one wins and the old-key file is now unreachable — delete at leisure."
    [ "$failed" = 0 ] || { echo "      ERROR: $failed rename(s) failed" >&2; return 1; }
    return 0
}

migrate_web_sidecars() {
    local dir="$script_dir/.web_hs_cache" p value upgraded=0 already=0 other=0 failed=0
    [ -d "$dir" ] || return 0
    shopt -s nullglob
    for p in "$dir"/*.hs.fp; do
        value=$(cat "$p" 2>/dev/null) || { failed=$((failed+1)); continue; }
        if [ "$value" = "$HS_FP" ]; then
            already=$((already+1))
        elif [ "$value" = "$HS_FP_LEGACY" ]; then
            if [ -n "$DRY_RUN" ]; then upgraded=$((upgraded+1))
            elif printf '%s\n' "$HS_FP" > "$p.tmp.$$" && mv "$p.tmp.$$" "$p"; then
                upgraded=$((upgraded+1))
            else
                rm -f "$p.tmp.$$"; failed=$((failed+1))
            fi
        else
            other=$((other+1))
        fi
    done
    shopt -u nullglob
    printf '  %-18s upgraded=%-5d already=%-5d other-oracle=%-4d failed=%d\n' \
        ".web_hs_cache" "$upgraded" "$already" "$other" "$failed"
    [ "$failed" = 0 ]
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
migrate_web_sidecars || rc=1
echo
echo "DONE_MIGRATE_HS_CACHE_FP verdict=$([ "$rc" = 0 ] && echo OK || echo FAILED)"
exit "$rc"
