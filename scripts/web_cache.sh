#!/usr/bin/env bash
# Shared web-gate cache plumbing. Source after gate_common.sh and after the HS
# binary and crawl-plan settings have been resolved.

# web_cache_init <repo-root> <script-dir> <hs-binary> <plan-version>
#
# Selects a cache profile and exports CACHE, WEB_CACHE_ROOT,
# WEB_ORACLE_SHA256, WEB_CACHE_ORACLE_STAMP and WEB_CACHE_PROFILE.  By default
# every linked worktree of a repository shares one pool below the main
# checkout, while oracle versions and crawl settings select disjoint
# profile directories inside it.  Thus testing a second Tamarin build cannot
# evict or overwrite the first build's manifests.
#
# CACHE overrides the exact directory, with the same producer-profile checks.
web_cache_init() {
    local repo=$1 scripts=$2 hs=$3 plan=$4 profile_text marker
    local dot_path dot_sha dot_version crawl_path="$scripts/web_crawl.py" url_key_path="$scripts/web_url_key.py"

    if [ "${HS_FP_PATH:-}" = "$hs" ] && [ -n "${HS_FP:-}" ]; then
        WEB_ORACLE_SHA256=$HS_FP
    else
        hs_fingerprint "$hs" "$MAUDE_PATH" || return 1
        WEB_ORACLE_SHA256=$HS_FP
    fi
    execution_fingerprint "$MAUDE_PATH" "${DERIVCHECK_TIMEOUT:-30}" || return 1
    if dot_path=$(command -v dot 2>/dev/null) && [ -n "$dot_path" ]; then
        dot_sha=$(binary_sha256 "$dot_path") || return 1
        DOT_FP_PATH=$dot_path
        DOT_FP=$dot_sha
        dot_version=$("$dot_path" -V 2>&1) || return 1
        [ -n "$dot_version" ] || return 1
        dot_version=${dot_version%% (*}
    else
        echo "web cache: Graphviz 'dot' is required for a reproducible crawl" >&2
        return 2
    fi
    WEB_CRAWL_FP=$(file_sha256 "$crawl_path") || {
        echo "web cache: cannot fingerprint $crawl_path" >&2
        return 2
    }
    WEB_CRAWL_FP_PATH=$crawl_path
    WEB_URL_KEY_FP=$(file_sha256 "$url_key_path") || {
        echo "web cache: cannot fingerprint $url_key_path" >&2
        return 2
    }
    WEB_URL_KEY_FP_PATH=$url_key_path
    WEB_PRODUCER_PROTOCOL_FP=$(web_producer_protocol_fingerprint) || {
        echo "web cache: cannot fingerprint the shell producer protocol" >&2
        return 2
    }
    profile_text=$(printf '%s\n' \
        "format=3" \
        "oracle_sha256=$WEB_ORACLE_SHA256" \
        "plan_version=$plan" \
        "execution_sha256=$EXEC_FP" \
        "graphviz_version=$dot_version" \
        "crawler_sha256=$WEB_CRAWL_FP" \
        "url_key_sha256=$WEB_URL_KEY_FP" \
        "producer_protocol_sha256=$WEB_PRODUCER_PROTOCOL_FP" \
        "max_nodes=${MAX_NODES:-400}")
    WEB_CACHE_PROFILE=$(printf '%s' "$profile_text" | sha256sum | cut -c1-16)

    if [ -z "${WEB_CACHE_ROOT:-}" ]; then
        WEB_CACHE_ROOT=$(shared_cache_dir "$repo" web "$scripts/.web_hs_cache") || return 1
    fi
    WEB_CACHE_SCRIPTS=$scripts
    # Some manifests are hundreds of MiB. Keep per-run copies beside the
    # build artifacts rather than on a size-limited /tmp tmpfs.
    WEB_WORK_ROOT="${WEB_WORK_ROOT:-$repo/target/web-work}"
    mkdir -p "$WEB_WORK_ROOT" || return 1

    if [ -z "${CACHE:-}" ]; then
        CACHE="$WEB_CACHE_ROOT/oracle-${WEB_ORACLE_SHA256:0:16}/profile-$WEB_CACHE_PROFILE"
        WEB_CACHE_MODE=profiled
    else
        WEB_CACHE_MODE=explicit
    fi
    WEB_CACHE_ORACLE_STAMP="$WEB_ORACLE_SHA256"

    mkdir -p "$CACHE" || return 1
    marker="$CACHE/PROFILE"
    local profile_lock_fd profile_tmp
    exec {profile_lock_fd}>"$CACHE/.profile.lock" || return 1
    flock "$profile_lock_fd" || { exec {profile_lock_fd}>&-; return 1; }
    if [ -f "$marker" ]; then
        if [ "$(cat "$marker")" != "$profile_text" ]; then
            echo "web cache profile mismatch in $CACHE" >&2
            echo "Choose another CACHE directory or remove the incorrect empty profile." >&2
            flock -u "$profile_lock_fd"; exec {profile_lock_fd}>&-
            return 2
        fi
    else
        if find "$CACHE" -maxdepth 1 -name '*.hs.json' -print -quit | grep -q .; then
            echo "web cache '$CACHE' has no complete producer profile" >&2
            echo "Choose an empty CACHE directory or a cache with a matching PROFILE." >&2
            flock -u "$profile_lock_fd"; exec {profile_lock_fd}>&-
            return 2
        fi
        profile_tmp=$(mktemp "$CACHE/.PROFILE.XXXXXX") || {
            flock -u "$profile_lock_fd"; exec {profile_lock_fd}>&-; return 1
        }
        if ! printf '%s\n' "$profile_text" > "$profile_tmp" \
                || ! mv -f "$profile_tmp" "$marker"; then
            rm -f "$profile_tmp"
            flock -u "$profile_lock_fd"; exec {profile_lock_fd}>&-
            return 1
        fi
    fi
    flock -u "$profile_lock_fd"; exec {profile_lock_fd}>&-
    export CACHE WEB_CACHE_ROOT WEB_ORACLE_SHA256 WEB_CACHE_ORACLE_STAMP \
        WEB_CACHE_PROFILE WEB_CACHE_MODE WEB_WORK_ROOT
    export WEB_CACHE_SCRIPTS
    export DOT_FP_PATH DOT_FP MAUDE_FP_PATH MAUDE_FP HS_FP_PATH HS_FP \
        WEB_CRAWL_FP_PATH WEB_CRAWL_FP WEB_URL_KEY_FP_PATH WEB_URL_KEY_FP
    export WEB_PRODUCER_PROTOCOL_FP
}

# Capture code used only to compare two completed manifests. Keeping this out
# of web_cache_init means response-normalization changes reuse HS crawl bytes,
# and the pane-byte gate need not depend on a comparator it never invokes.
web_comparator_init() {
    local diff_path="$1/web_diff.py" normalize_path="$1/web_normalize.py"
    WEB_DIFF_FP=$(file_sha256 "$diff_path") || {
        echo "web comparison: cannot fingerprint $diff_path" >&2
        return 2
    }
    WEB_DIFF_FP_PATH=$diff_path
    WEB_NORMALIZE_FP=$(file_sha256 "$normalize_path") || {
        echo "web comparison: cannot fingerprint $normalize_path" >&2
        return 2
    }
    WEB_NORMALIZE_FP_PATH=$normalize_path
    export WEB_DIFF_FP_PATH WEB_DIFF_FP WEB_NORMALIZE_FP_PATH WEB_NORMALIZE_FP
}

# Read a literal crawl-schema constant without importing the module. The main
# crawler then always executes its source file, and this probe cannot populate
# or consume a stale local bytecode cache.
web_crawl_constant() {
    python3 - "$1" "$2" <<'PY'
import ast, sys
tree = ast.parse(open(sys.argv[1], encoding="utf-8").read(), sys.argv[1])
for node in tree.body:
    if isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == sys.argv[2]
            for target in node.targets):
        print(ast.literal_eval(node.value))
        break
else:
    raise SystemExit(1)
PY
}

# Read the crawler's top-level plan stamp without loading a potentially
# gigabyte-scale manifest. web_crawl.py writes the stamp before the `manifest`
# object; refuse an unexpectedly large/missing prefix rather than scanning the
# response payload and mistaking body text for metadata.
web_manifest_plan_version() {
    python3 - "$1" "$2" <<'PY'
import json, re, sys

with open(sys.argv[1], "rb") as source:
    prefix = source.read(1024 * 1024)
manifest_key = re.search(rb'"manifest"\s*:', prefix)
if manifest_key is None:
    raise SystemExit(1)
prefix = prefix[:manifest_key.start()]
key = re.escape(json.dumps(sys.argv[2]).encode())
match = re.search(key + rb'\s*:\s*([0-9]+)', prefix)
if match is None:
    raise SystemExit(1)
print(match.group(1).decode())
PY
}

# Run an importing Python command without consulting a persistent local .pyc.
# A unique prefix lives in the caller's disposable workdir; disabling writes
# avoids compiling the standard library into that directory on every crawl.
web_python_isolated() {
    local pycache=$1
    shift
    PYTHONDONTWRITEBYTECODE=1 PYTHONPYCACHEPREFIX="$pycache" "$@"
}

# Hash only loaded shell functions that can change a successfully completed
# manifest. Readiness, shutdown, workdir allocation and other lifecycle helpers
# determine whether a crawl completes, not its bytes, so changing them must not
# strand an otherwise reusable HS cache. Flag and dependency discovery stay
# outside: their concrete output is already part of each entry's input key.
web_producer_protocol_fingerprint() {
    local protocol
    protocol=$(declare -f web_python_isolated \
        web_exec_server web_exec_crawler \
        web_stage_inputs web_crawl_args_for_theory \
    ) || return 1
    printf '%s' "$protocol" | sha256sum | cut -d' ' -f1
}

# The crawler and its imported URL-key helper determine which response bytes
# enter a manifest. They are part of the web producer just as surely as the HS,
# Maude, and Graphviz executables, and must remain fixed across a crawl.
web_harness_identity_unchanged() {
    local protocol
    protocol=$(web_producer_protocol_fingerprint) || return 1
    [ -n "${WEB_CRAWL_FP_PATH:-}" ] && [ -n "${WEB_CRAWL_FP:-}" ] \
        && [ -n "${WEB_URL_KEY_FP_PATH:-}" ] && [ -n "${WEB_URL_KEY_FP:-}" ] \
        && [ -n "${WEB_PRODUCER_PROTOCOL_FP:-}" ] \
        && binary_identity_unchanged "$WEB_CRAWL_FP_PATH" "$WEB_CRAWL_FP" \
        && binary_identity_unchanged "$WEB_URL_KEY_FP_PATH" "$WEB_URL_KEY_FP" \
        && [ "$protocol" = "$WEB_PRODUCER_PROTOCOL_FP" ]
}

web_comparator_identity_unchanged() {
    [ -n "${WEB_DIFF_FP_PATH:-}" ] && [ -n "${WEB_DIFF_FP:-}" ] \
        && [ -n "${WEB_NORMALIZE_FP_PATH:-}" ] && [ -n "${WEB_NORMALIZE_FP:-}" ] \
        && binary_identity_unchanged "$WEB_DIFF_FP_PATH" "$WEB_DIFF_FP" \
        && binary_identity_unchanged "$WEB_NORMALIZE_FP_PATH" "$WEB_NORMALIZE_FP"
}

web_producer_identity_unchanged() {
    producer_identity_unchanged && web_harness_identity_unchanged
}

web_comparison_identity_unchanged() {
    web_producer_identity_unchanged && web_comparator_identity_unchanged \
        && rs_identity_unchanged
}

web_make_workdir() {
    mktemp -d "$WEB_WORK_ROOT/run.XXXXXX"
}

# A no-lemma theory is a valid crawl, while an unexpectedly empty discovery is
# a failed producer. Keep the one decision shared by both web-cache consumers
# and in the fingerprinted producer protocol.
web_crawl_args_for_theory() {
    grep -qE '^[[:space:]]*(lemma|equivLemma|diffLemma)([[:space:]]|\[|:)' "$1" \
        || printf '%s\n' --allow-no-lemmas
}

# Byte-affecting invocations are kept separate from lifecycle orchestration so
# the producer fingerprint can follow the successful-manifest boundary.
web_exec_server() {
    local bin=$1 port=$2 wd=$3 theory_flags=$4
    local -a load_args=() dot_args=()
    [ -z "$theory_flags" ] || read -r -a load_args <<< "$theory_flags"
    [ -z "${DOT_FP_PATH:-}" ] || dot_args=(--with-dot="$DOT_FP_PATH")
    exec setsid "$bin" interactive "$wd/thy" --port="$port" \
        --with-maude="$MAUDE_PATH" "${dot_args[@]}" \
        --derivcheck-timeout="${DERIVCHECK_TIMEOUT:-30}" "${load_args[@]}"
}

web_exec_crawler() {
    local port=$1 wd=$2 out=$3 kind=$4 crawl_flags=$5
    local -a crawl_args=()
    [ -z "$crawl_flags" ] || read -r -a crawl_args <<< "$crawl_flags"
    web_python_isolated "$wd/${kind}-pycache" \
        timeout "${FILE_TIMEOUT:-300}" python3 "$WEB_CACHE_SCRIPTS/web_crawl.py" \
        "http://127.0.0.1:$port" "$out" --max-nodes "${MAX_NODES:-400}" \
        "${crawl_args[@]}"
}

# Return a readable, collision-resistant per-theory namespace contained below
# the requested diagnostics root. Corpus paths may legitimately contain `..`;
# they must never become filesystem traversal when a bundle replaces its target.
web_diagnostic_target() {
    local root=$1 rel=$2 readable digest
    root=$(realpath -m -- "$root") || return 1
    readable=$(printf '%s' "$rel" | sed 's/[^A-Za-z0-9._-]/_/g') || return 1
    digest=$(printf '%s' "$rel" | sha256sum | cut -c1-16) || return 1
    printf '%s/theory-%s__%s\n' "$root" "${readable:0:120}" "$digest"
}

# Stage a complete diagnostic bundle before replacing the previous one under
# the writer lock. Readers may briefly see no directory during replacement.
web_publish_diagnostics() {
    local source=$1 target=$2 parent target_name lock_id lock_fd staged
    [ -d "$source" ] || return 1
    parent=$(dirname -- "$target")
    target_name=$(basename -- "$target")
    case "$target_name" in ''|.|..) return 1;; esac
    mkdir -p "$parent" || return 1
    parent=$(realpath -- "$parent") || return 1
    target="$parent/$target_name"
    lock_id=$(printf '%s' "$target" | sha256sum | cut -c1-16)
    cache_entry_lock "$parent" ".web-diagnostics.$lock_id" lock_fd || return 1
    staged=$(mktemp -d "$parent/.web-diagnostics.$lock_id.publish.XXXXXX") || {
        cache_entry_unlock "$lock_fd"; return 1
    }
    if ! cp -a "$source/." "$staged/"; then
        rm -rf "$staged"
        cache_entry_unlock "$lock_fd"
        return 1
    fi
    if ! rm -rf -- "$target"; then
        rm -rf -- "$staged"
        cache_entry_unlock "$lock_fd"
        return 1
    fi
    if find "$staged" -mindepth 1 -print -quit | grep -q .; then
        if ! mv -T -- "$staged" "$target"; then
            rm -rf -- "$staged"
            cache_entry_unlock "$lock_fd"
            return 1
        fi
    else
        rmdir "$staged"
    fi
    cache_entry_unlock "$lock_fd"
}

web_port_free() {
    python3 - "$1" <<'PY'
import socket, sys
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
try:
    s.bind(("127.0.0.1", int(sys.argv[1])))
except OSError:
    raise SystemExit(1)
finally:
    s.close()
PY
}

web_wait_port_free() {
    local port=$1 i
    for ((i=0; i<${PORT_FREE_TIMEOUT:-30}; i++)); do
        web_port_free "$port" && return 0
        sleep 1
    done
    return 1
}

web_stop_group() {
    local pid=$1 i
    [ -n "$pid" ] || return 0
    kill -TERM -- -"$pid" 2>/dev/null || true
    for ((i=0; i<${SERVER_STOP_TIMEOUT:-5}; i++)); do
        kill -0 -- -"$pid" 2>/dev/null || break
        sleep 1
    done
    if kill -0 -- -"$pid" 2>/dev/null; then
        kill -KILL -- -"$pid" 2>/dev/null || true
    fi
    wait "$pid" 2>/dev/null || true
}

# web_boot_crawl <bin> <port> <workdir> <manifest> <kind> <theory-flags> <crawl-flags>
# Run one guarded server lifecycle. Explicit flags prevent the two web gates'
# callers from communicating through dynamically scoped shell variables.
_web_boot_crawl() (
    local bin=$1 port=$2 wd=$3 out=$4 kind=$5 theory_flags=$6 crawl_flags=$7
    local log="$wd/${kind}_server.log" pid= ok= i rc
    trap 'web_stop_group "$pid"; rm -rf "$wd"; exit 130' HUP INT TERM
    web_wait_port_free "$port" || {
        echo "  port $port not free before $kind server boot" >&2
        return 1
    }
    ( oom_prologue "${SERVER_MEM_KB:-25165824}"
      # The parent owns any cache-entry lock. A server orphaned by an
      # interrupted gate must not keep that lock alive indefinitely.
      [ -z "${WEB_CACHE_LOCK_FD:-}" ] || exec {WEB_CACHE_LOCK_FD}>&-
      web_exec_server "$bin" "$port" "$wd" "$theory_flags"
    ) >"$log" 2>&1 &
    pid=$!
    for ((i=0; i<${READY_TIMEOUT:-90}; i++)); do
        if curl -sf -o /dev/null "http://127.0.0.1:$port/"; then ok=1; break; fi
        kill -0 "$pid" 2>/dev/null || break
        sleep 1
    done
    if [ -z "$ok" ]; then
        echo "  $kind server not ready ($wd)" >&2
        if [ -s "$log" ]; then
            echo "  $kind server log (last 20 lines):" >&2
            tail -n 20 "$log" | sed 's/^/    /' >&2
        fi
        web_stop_group "$pid"
        return 1
    fi
    ( [ -z "${WEB_CACHE_LOCK_FD:-}" ] || exec {WEB_CACHE_LOCK_FD}>&-
      web_exec_crawler "$port" "$wd" "$out" "$kind" "$crawl_flags"
    ) 2>>"$log"
    rc=$?
    web_stop_group "$pid"
    pid=
    if [ "$rc" -ne 0 ]; then
        echo "  $kind crawl failed with rc=$rc ($wd)" >&2
        if [ -s "$log" ]; then
            echo "  $kind server/crawler log (last 20 lines):" >&2
            tail -n 20 "$log" | sed 's/^/    /' >&2
        fi
    fi
    if ! web_wait_port_free "$port"; then
        echo "  port $port still occupied after $kind server shutdown" >&2
        return 1
    fi
    return "$rc"
)

web_abort_active_boot() {
    [ -n "${WEB_BOOT_PID:-}" ] || return 0
    kill -TERM "$WEB_BOOT_PID" 2>/dev/null || true
    wait "$WEB_BOOT_PID" 2>/dev/null || true
    WEB_BOOT_PID=
}

# Keep the lifecycle subshell addressable by the driver. If only the driver
# receives a signal, its trap can terminate this child; the child's own trap
# then shuts down the complete server process group before returning.
web_boot_crawl() {
    WEB_BOOT_PID=
    _web_boot_crawl "$@" &
    WEB_BOOT_PID=$!
    local rc=0
    wait "$WEB_BOOT_PID" || rc=$?
    WEB_BOOT_PID=
    return "$rc"
}

# Serialize access to one shared cache entry. Locks are advisory and remain as
# empty files in the cache; the kernel releases them if a gate is interrupted.
web_cache_lock() {
    cache_entry_lock "$CACHE" "$1.hs" WEB_CACHE_LOCK_FD
}

web_cache_unlock() {
    [ -n "${WEB_CACHE_LOCK_FD:-}" ] || return 0
    cache_entry_unlock "$WEB_CACHE_LOCK_FD"
    unset WEB_CACHE_LOCK_FD
}

# Snapshot an immutable cache payload into a work directory without copying
# large manifests when both paths are on the same filesystem.
web_cache_snapshot() {
    local source=$1 target=$2
    ln -L -- "$source" "$target" 2>/dev/null || cp -- "$source" "$target"
}

# Publish the manifest before its commit marker, with both renames occurring
# from the cache filesystem. Callers hold the entry lock, so readers either
# copy the old committed entry or the new one, never an in-progress crawl.
web_cache_publish() {
    local key=$1 source=$2 tmp stage_id path suffix
    stage_id=$(printf '%s' "$key" | sha256sum | cut -d' ' -f1) || return 1
    # The caller holds this key's cache lock. Recover only exact direct-child
    # staging names minted by this function, never broader lookalikes.
    for path in "$CACHE/.${stage_id}.publish."*; do
        [ -d "$path" ] && [ ! -L "$path" ] || continue
        suffix=${path##*.publish.}
        [ "${#suffix}" -eq 6 ] || continue
        case "$suffix" in *[!A-Za-z0-9]*) continue;; esac
        [ -f "$path/.web-cache-stage" ] || continue
        rm -rf -- "$path" || return 1
    done
    tmp=$(mktemp -d "$CACHE/.${stage_id}.publish.XXXXXX") || return 1
    if ! : > "$tmp/.web-cache-stage"; then
        rmdir "$tmp"
        return 1
    fi
    if ! web_cache_snapshot "$source" "$tmp/manifest"; then
        rm -rf -- "$tmp"
        return 1
    fi
    if ! printf '%s\n' "$WEB_CACHE_ORACLE_STAMP" > "$tmp/stamp"; then
        rm -rf -- "$tmp"
        return 1
    fi
    # Invalidate the old entry before replacing either half. If this process
    # dies between the two renames, the complete manifest remains uncommitted
    # and will be regenerated instead of being paired with an old stamp.
    rm -f "$CACHE/$key.hs.fp"
    if ! mv -f "$tmp/manifest" "$CACHE/$key.hs.json" \
            || ! mv -f "$tmp/stamp" "$CACHE/$key.hs.fp"; then
        rm -rf -- "$tmp"
        return 1
    fi
    rm -f "$tmp/.web-cache-stage"
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
web_cache_stamp_matches() {
    [ "$1" = "$WEB_CACHE_ORACLE_STAMP" ]
}

# web_stage_inputs <source-theory> <destination-directory> [flags] [staging-root]
# Stage only parser-selected inputs. The broader input_manifest is for cache
# invalidation: speculative dependencies must never change the staged theory.
# Relative dependencies may leave the theory directory, but never the caller's
# private staging root. Validate every destination before copying any file.
web_stage_inputs() {
    local src=$1 dest_dir=$2 flags=${3:-} stage_root=${4:-$2}
    local tag input_field rel_field input rel manifest stage_root_abs target physical
    local -A staged_sources=()
    manifest=$(parser_input_manifest "$src" "$flags") || return 1
    manifest=$(manifest_normalize <<< "$manifest") || return 1
    IFS= read -r -d '' stage_root_abs < <(realpath -z -m -- "$stage_root") || return 1
    while IFS=$'\t' read -r tag input_field rel_field; do
        case "$tag" in S|O) ;; *) continue;; esac
        manifest_decode_into "$input_field" input || return 1
        manifest_decode_into "$rel_field" rel || return 1
        # Absolute inputs remain absolute at runtime and need no staged alias.
        [ -n "$rel" ] || continue
        IFS= read -r -d '' target < <(realpath -z -m -- "$dest_dir/$rel") || return 1
        case "$target" in
            "$stage_root_abs"/*) ;;
            *) echo "web_stage_inputs: staged path escapes destination: $rel" >&2; return 1;;
        esac
        IFS= read -r -d '' physical < <(realpath -z -- "$input") || return 1
        if [[ -v staged_sources["$target"] ]] && [ "${staged_sources[$target]}" != "$physical" ]; then
            echo "web_stage_inputs: conflicting inputs for staged path: $rel" >&2
            return 1
        fi
        staged_sources[$target]=$physical
    done <<< "$manifest"
    while IFS=$'\t' read -r tag input_field rel_field; do
        case "$tag" in S|O) ;; *) continue;; esac
        manifest_decode_into "$input_field" input || return 1
        manifest_decode_into "$rel_field" rel || return 1
        [ -n "$rel" ] || continue
        # Preserve lexical aliases such as b/../a: the b directory must exist
        # for the parser to open that spelling in the staged tree.
        local rel_parent=.
        if [[ "$rel" == */* ]]; then rel_parent=${rel%/*}; fi
        mkdir -p "$dest_dir/$rel_parent" || return 1
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
    local rel=$1 theory=$2 flags=
    if [ "$#" -ge 3 ]; then
        flags=$3
    else
        flags=$(web_flags_for "$rel") || return 1
    fi
    input_content_key "$theory" "$flags"
}
