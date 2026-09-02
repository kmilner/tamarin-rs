#!/usr/bin/env bash
# Shared web-gate cache plumbing. Source after gate_common.sh and after the HS
# binary and crawl-plan settings have been resolved.

# web_cache_init <repo-root> <script-dir> <hs-binary> <plan-version>
#
# Selects a cache profile and exports CACHE, WEB_CACHE_ROOT,
# WEB_ORACLE_SHA256, WEB_CACHE_ORACLE_STAMP and WEB_CACHE_PROFILE.  By default
# every linked worktree of a repository shares one pool below the main
# checkout, while oracle binary content and crawl settings select disjoint
# profile directories inside it.  Thus testing a second Tamarin build cannot
# evict or overwrite the first build's manifests.
#
# CACHE remains an exact-directory compatibility override.  A non-empty
# unstamped directory is treated as a legacy cache and retains the old
# size.mtime sidecar contract; new/default profiles use the binary SHA-256.
web_cache_init() {
    local repo=$1 scripts=$2 hs=$3 plan=$4 common shared profile_text marker maude_sha

    if [ "${HS_FP_PATH:-}" = "$hs" ] && [ -n "${HS_FP:-}" ]; then
        WEB_ORACLE_SHA256=$HS_FP
    else
        WEB_ORACLE_SHA256=$(binary_sha256 "$hs") || return 1
    fi
    maude_sha=$(binary_sha256 "$MAUDE_PATH") || return 1
    profile_text=$(printf '%s\n' \
        "format=1" \
        "oracle_sha256=$WEB_ORACLE_SHA256" \
        "plan_version=$plan" \
        "maude_sha256=$maude_sha" \
        "derivcheck_timeout=${DERIVCHECK_TIMEOUT:-30}" \
        "max_nodes=${MAX_NODES:-400}" \
        "request_timeout=${WEB_CRAWL_TIMEOUT:-120}")
    WEB_CACHE_PROFILE=$(printf '%s' "$profile_text" | sha256sum | cut -c1-16)

    if [ -z "${WEB_CACHE_ROOT:-}" ]; then
        common=$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir 2>/dev/null) || common=
        if [ -n "$common" ]; then
            shared=$(dirname "$common")
            WEB_CACHE_ROOT="$shared/scripts/.web_hs_cache"
        else
            WEB_CACHE_ROOT="$scripts/.web_hs_cache"
        fi
    fi
    WEB_CACHE_LOCAL_LEGACY="$scripts/.web_hs_cache"

    if [ -z "${CACHE:-}" ]; then
        CACHE="$WEB_CACHE_ROOT/oracle-${WEB_ORACLE_SHA256:0:16}/profile-$WEB_CACHE_PROFILE"
        WEB_CACHE_ORACLE_STAMP="$WEB_ORACLE_SHA256"
        WEB_CACHE_MODE=profiled
    else
        WEB_CACHE_MODE=explicit
        # Preserve deliberately selected legacy caches without rewriting every
        # old manifest. New empty CACHE overrides still receive a profile
        # marker and use the stable content stamp.
        if find "$CACHE" -maxdepth 1 -name '*.hs.json' -print -quit 2>/dev/null | grep -q . \
                && [ ! -f "$CACHE/PROFILE" ]; then
            WEB_CACHE_MODE=legacy-explicit
        fi
        WEB_CACHE_ORACLE_STAMP="$WEB_ORACLE_SHA256"
    fi

    mkdir -p "$CACHE" || return 1
    marker="$CACHE/PROFILE"
    if [ -f "$marker" ]; then
        if [ "$(cat "$marker")" != "$profile_text" ]; then
            echo "web cache profile mismatch in $CACHE" >&2
            echo "Choose another CACHE directory or remove the incorrect empty profile." >&2
            return 2
        fi
    elif [ "$WEB_CACHE_MODE" != legacy-explicit ]; then
        printf '%s\n' "$profile_text" > "$marker" || return 1
    fi
    export CACHE WEB_CACHE_ROOT WEB_ORACLE_SHA256 WEB_CACHE_ORACLE_STAMP \
        WEB_CACHE_PROFILE WEB_CACHE_MODE WEB_CACHE_LOCAL_LEGACY
}

# Serialize access to one shared cache entry. Locks are advisory and remain as
# empty files in the cache; the kernel releases them if a gate is interrupted.
web_cache_lock() {
    local key=$1 fd
    exec {fd}>"$CACHE/$key.hs.lock" || return 1
    if ! flock "$fd"; then
        exec {fd}>&-
        return 1
    fi
    WEB_CACHE_LOCK_FD=$fd
}

web_cache_unlock() {
    [ -n "${WEB_CACHE_LOCK_FD:-}" ] || return 0
    flock -u "$WEB_CACHE_LOCK_FD"
    exec {WEB_CACHE_LOCK_FD}>&-
}

# Publish the manifest before its commit marker, with both renames occurring
# from the cache filesystem. Callers hold the entry lock, so readers either
# copy the old committed entry or the new one, never an in-progress crawl.
web_cache_publish() {
    local key=$1 source=$2 tmp
    tmp=$(mktemp -d "$CACHE/.${key}.publish.XXXXXX") || return 1
    if ! ln "$source" "$tmp/manifest" 2>/dev/null \
            && ! cp "$source" "$tmp/manifest"; then
        rmdir "$tmp"
        return 1
    fi
    if ! printf '%s\n' "$WEB_CACHE_ORACLE_STAMP" > "$tmp/stamp"; then
        rm -f "$tmp/manifest"
        rmdir "$tmp"
        return 1
    fi
    # Invalidate the old entry before replacing either half. If this process
    # dies between the two renames, the complete manifest remains uncommitted
    # and will be regenerated instead of being paired with an old stamp.
    rm -f "$CACHE/$key.hs.fp"
    if ! mv -f "$tmp/manifest" "$CACHE/$key.hs.json" \
            || ! mv -f "$tmp/stamp" "$CACHE/$key.hs.fp"; then
        rm -f "$tmp/manifest" "$tmp/stamp"
        rmdir "$tmp"
        return 1
    fi
    rmdir "$tmp"
}

web_cache_invalidate() {
    local key=$1
    # The stamp is the commit marker, so remove it before the manifest.
    rm -f "$CACHE/$key.hs.fp" "$CACHE/$key.hs.json"
}

# web_flags_for <corpus-relative-path>
# Return the separately declared interactive recipe. Keeping this map distinct
# from file_flags.tsv prevents batch-only modes from leaking into one server.
# Unknown flags in the web map are a hard scope miss, not silently dropped.
web_flags_for() {
    local map=${WEB_FLAGS_MAP:-} raw word
    local -a words=() kept=()
    [ -n "$map" ] || return 0
    [ -r "$map" ] || {
        echo "web_flags_for: map is not readable: $map" >&2
        return 1
    }
    raw=$(awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$map") || return 1
    [ -z "$raw" ] || read -r -a words <<< "$raw"
    for word in "${words[@]}"; do
        case "$word" in
            -D=*|--stop-on-trace=*|--no-ndc|--quit-on-warning) kept+=("$word");;
            *) echo "web_flags_for: unsupported interactive flag for $1: $word" >&2; return 1;;
        esac
    done
    printf '%s' "${kept[*]}"
}

# web_cache_stamp_matches <stamp>
# Profiled caches require their stable content stamp. An explicitly selected
# old flat cache may still carry the former size+mtime stamp; accept it only in
# that compatibility mode, while stamping every newly crawled manifest with
# the content SHA-256.
web_cache_stamp_matches() {
    [ "$1" = "$WEB_CACHE_ORACLE_STAMP" ] && return 0
    [ "$WEB_CACHE_MODE" = legacy-explicit ] && [ "$1" = "$HS_FP_LEGACY" ]
}

# web_stage_inputs <source-theory> <destination-directory> [flags] [staging-root]
# Copy the theory, its transitive includes, and its executable oracle inputs
# into the temporary server tree. Both web consumers use this one spelling so
# cache identity and staged inputs cannot drift apart. Relative dependencies
# may leave the theory directory, but never the caller's private staging root.
web_stage_inputs() {
    local src=$1 dest_dir=$2 flags=${3:-} stage_root=${4:-$2}
    local tag input rel manifest stage_root_abs target
    manifest=$(input_manifest "$src" "$flags") || return 1
    stage_root_abs=$(realpath -m -- "$stage_root") || return 1
    while IFS=$'\t' read -r tag input rel; do
        case "$tag" in S|O) ;; *) continue;; esac
        # Absolute inputs remain absolute at runtime and need no staged alias.
        [ -n "$rel" ] || continue
        target=$(realpath -m -- "$dest_dir/$rel") || return 1
        case "$target" in
            "$stage_root_abs"/*) ;;
            *) echo "web_stage_inputs: staged path escapes destination: $rel" >&2; return 1;;
        esac
        mkdir -p "$dest_dir/$(dirname "$rel")" || return 1
        if [ "$tag" = O ]; then
            cp -p "$input" "$dest_dir/$rel" || return 1
        else
            cp "$input" "$dest_dir/$rel" || return 1
        fi
    done <<< "$manifest"
}

# web_cache_key <corpus-relative-path> <absolute-theory>
#
# The profile directory already identifies the oracle and crawl settings. The
# filename identifies all source inputs: the theory itself, transitive
# #includes, and executable oracle files selected by the theory's directory or
# quoted heuristic paths. The relpath argument is reserved for future
# path-sensitive inputs and keeps this API parallel with gate_common's ckey.
web_cache_key() {
    local rel=$1 theory=$2 flags= h deps oracles manifest
    if [ "$#" -ge 3 ]; then
        flags=$3
    else
        flags=$(web_flags_for "$rel") || return 1
    fi
    h=$(file_sha256 "$theory") || return 1
    manifest=$(input_manifest "$theory" "$flags") || return 1
    deps=$(_include_shas_from_manifest "$manifest") || return 1
    oracles=$(_oracle_shas_from_manifest "$manifest") || return 1
    deps=$(printf '%s\n%s' "$deps" "$oracles" | sed '/^[[:space:]]*$/d' | sort -u)
    if [ -n "$deps" ]; then
        h="${h}__d$(printf '%s' "$deps" | sha256sum | cut -c1-12)"
    fi
    if [ -n "$flags" ]; then
        h="${h}__f$(printf '%s' "$flags" | sha256sum | cut -c1-12)"
    fi
    printf '%s' "$h"
}

# web_cache_adopt_legacy <new-key> <absolute-theory> <plan-version>
#
# Lazily hard-link a valid flat-cache manifest into the selected profile. This
# makes the transition space-free and lets linked worktrees discover historical
# `.web_hs_cache*` directories without an operator renaming/switching them.
# Inputs with includes or oracle scripts deliberately do not migrate: their old
# theory-only key cannot prove that those auxiliary inputs were current.
web_cache_adopt_legacy() {
    local key=$1 theory=$2 plan=$3 old_key legacy manifest stamp cached_plan
    [ "$WEB_CACHE_MODE" = profiled ] || return 1
    [ ! -e "$CACHE/$key.hs.json" ] || return 0
    old_key=$(file_sha256 "$theory") || return 1
    [ "$key" = "$old_key" ] || return 1

    for legacy in "$WEB_CACHE_ROOT" "$WEB_CACHE_ROOT"_* \
            "$WEB_CACHE_LOCAL_LEGACY" "$WEB_CACHE_LOCAL_LEGACY"_*; do
        [ -d "$legacy" ] || continue
        [ "$legacy" != "$CACHE" ] || continue
        manifest="$legacy/$old_key.hs.json"
        [ -f "$manifest" ] || continue
        stamp=
        [ -f "$legacy/$old_key.hs.fp" ] && read -r stamp < "$legacy/$old_key.hs.fp"
        case $stamp in
            "$HS_FP_LEGACY"|"$HS_FP"|"$WEB_ORACLE_SHA256") ;;
            *) continue ;;
        esac
        cached_plan=$(python3 - "$manifest" "$plan" <<'PY'
import json, sys
try:
    doc = json.load(open(sys.argv[1], encoding="utf-8"))
except (OSError, ValueError):
    raise SystemExit(1)
value = doc.get("__plan_version__")
if value is None:
    urls = doc.get("manifest", {})
    value = 2 if (any("/json/cases/" in u for u in urls)
                  and any(u.endswith("/main/cases/raw/1/1") for u in urls)) else 1
print(value)
PY
        ) || continue
        [ "$cached_plan" = "$plan" ] || continue
        if web_cache_publish "$key" "$manifest"; then
            echo "  adopted legacy HS manifest from $legacy" >&2
            return 0
        fi
    done
    return 1
}
