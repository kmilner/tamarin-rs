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

    WEB_ORACLE_SHA256=$(sha256sum "$hs" | cut -d' ' -f1) || return 1
    maude_sha=$(sha256sum "$MAUDE_PATH" | cut -d' ' -f1) || return 1
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
            WEB_CACHE_ORACLE_STAMP="$HS_FP"
            WEB_CACHE_MODE=legacy-explicit
        else
            WEB_CACHE_ORACLE_STAMP="$WEB_ORACLE_SHA256"
        fi
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
        WEB_CACHE_PROFILE WEB_CACHE_MODE
}

# web_stage_inputs <source-theory> <destination-directory>
# Copy the theory, its transitive includes, and its executable oracle inputs
# into the temporary server tree. Both web consumers use this one spelling so
# cache identity and staged inputs cannot drift apart.
web_stage_inputs() {
    local src=$1 dest_dir=$2
    web_stage_includes "$src" "$dest_dir/$(basename "$src")" 0 || return 1
    web_stage_oracles "$src" "$dest_dir"
}

web_stage_includes() {
    local src=$1 dst=$2 depth=$3 inc
    [ "$depth" -lt 8 ] || { echo "web cache: include nesting exceeds 8 at $src" >&2; return 1; }
    mkdir -p "$(dirname "$dst")" && cp "$src" "$dst" || return 1
    while IFS= read -r inc; do
        [ -n "$inc" ] || continue
        [ -f "$(dirname "$src")/$inc" ] || {
            echo "web cache: missing include '$inc' from $src" >&2; return 1;
        }
        web_stage_includes "$(dirname "$src")/$inc" "$(dirname "$dst")/$inc" $((depth + 1)) \
            || return 1
    done < <(grep -oE '#include[[:space:]]*"[^"]+"' "$src" 2>/dev/null \
             | sed 's/.*"\(.*\)"/\1/')
}

web_stage_oracles() {
    local src=$1 dest_dir=$2 f q
    for f in "$(dirname "$src")"/oracle*; do
        if [ -f "$f" ]; then cp "$f" "$dest_dir/" || return 1; fi
    done
    if [ -f "${src%.spthy}.oracle" ] && [ ! -e "$dest_dir/oracle" ]; then
        cp "${src%.spthy}.oracle" "$dest_dir/oracle" || return 1
    fi
    while IFS= read -r q; do
        [ -f "$(dirname "$src")/$q" ] || continue
        mkdir -p "$dest_dir/$(dirname "$q")" || return 1
        cp "$(dirname "$src")/$q" "$dest_dir/$q" || return 1
    done < <(grep -E 'heuristic' "$src" 2>/dev/null | grep -oE '"[^"]+"' | tr -d '"' | sort -u)
}

# web_cache_key <corpus-relative-path> <absolute-theory>
#
# The profile directory already identifies the oracle and crawl settings. The
# filename identifies all source inputs: the theory itself, transitive
# #includes, and executable oracle files selected by the theory's directory or
# quoted heuristic paths. The relpath argument is reserved for future
# path-sensitive inputs and keeps this API parallel with gate_common's ckey.
web_cache_key() {
    local _rel=$1 theory=$2 h deps dir q p
    h=$(sha256sum "$theory" | cut -d' ' -f1) || return 1
    dir=$(dirname "$theory")
    deps=$(include_shas "$theory")

    for p in "$dir"/oracle*; do
        [ -f "$p" ] && deps="${deps}${deps:+$'\n'}$(sha256sum "$p" | cut -d' ' -f1) ${p#$dir/}"
    done
    p="${theory%.spthy}.oracle"
    if [ -f "$p" ]; then
        deps="${deps}${deps:+$'\n'}$(sha256sum "$p" | cut -d' ' -f1) ${p#$dir/}"
    fi
    while IFS= read -r q; do
        p="$dir/$q"
        [ -f "$p" ] || continue
        deps="${deps}${deps:+$'\n'}$(sha256sum "$p" | cut -d' ' -f1) $q"
    done < <(grep -E 'heuristic' "$theory" 2>/dev/null | grep -oE '"[^"]+"' | tr -d '"' | sort -u)

    deps=$(printf '%s' "$deps" | sed '/^[[:space:]]*$/d' | sort -u)
    if [ -n "$deps" ]; then
        h="${h}__d$(printf '%s' "$deps" | sha256sum | cut -c1-12)"
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
    old_key=$(sha256sum "$theory" | cut -d' ' -f1) || return 1
    [ "$key" = "$old_key" ] || return 1

    for legacy in "$WEB_CACHE_ROOT" "$WEB_CACHE_ROOT"_*; do
        [ -d "$legacy" ] || continue
        [ "$legacy" != "$CACHE" ] || continue
        manifest="$legacy/$old_key.hs.json"
        [ -f "$manifest" ] || continue
        stamp=
        [ -f "$legacy/$old_key.hs.fp" ] && read -r stamp < "$legacy/$old_key.hs.fp"
        case $stamp in
            "$HS_FP"|"$WEB_ORACLE_SHA256") ;;
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
        if ln "$manifest" "$CACHE/$key.hs.json" 2>/dev/null; then
            printf '%s\n' "$WEB_CACHE_ORACLE_STAMP" > "$CACHE/$key.hs.fp"
            echo "  adopted legacy HS manifest from $legacy" >&2
            return 0
        fi
    done
    return 1
}
