# Shared gate plumbing. Source me:
#   [ -r "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh" ] || exit 2
#   . "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh"
# Owns the helpers the gate/sweep/triage scripts used to carry as private
# copies (which drifted): the OOM prologue, the three environment-line
# strip policies, flags_for, the oracle fingerprint recipe, the `#include`
# digest + the gate cache key, the gate file list, the maude resolver, the
# Haskell-oracle and Maude resolvers, stale-RS-binary check and the
# oracle-rev-vs-pin preflight. Policy DIFFERENCES between the old copies
# are deliberate and stay separate named functions here (the three strip
# policies); only drifted duplicates were unified.
#
# This file defines functions and GATE_COMMON_DIR only — it runs nothing and
# sources nothing, so sweep_common.sh can source it without cycles.

GATE_COMMON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# --- OOM prologue ------------------------------------------------------------
# oom_prologue [cap-kb]
#   Volunteer the calling process tree as the kernel's first OOM victim and cap
#   its address space (default 24 GiB; the sweeps' per-run cap is 16 GiB).
#   `ulimit -v` is per-process and inherited, so every prover child gets its
#   own ceiling — a runaway prover dies alone instead of taking the session.
oom_prologue() {
    echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
    ulimit -v "${1:-25165824}" 2>/dev/null || true
}

# --- environment-line strip policies -----------------------------------------
# Three DELIBERATELY different treatments of the volatile prover lines
# (Git revision / Compiled at / processing time / analyzed). Never unify them:
#
# strip_env — the GATE policy: DELETE all four lines from stdin. Stripping
#   `analyzed:` on both sides means the content-keyed caches need no
#   path rewrite when a hit comes from another checkout.
strip_env() {
    grep -v -e '^Git revision:' -e '^Compiled at:' \
            -e '^[[:space:]]*processing time:' -e '^[[:space:]]*analyzed:'
}
# strip_env_lines <file> — the TRIAGE policy: delete only the three lines no
#   run can reproduce, KEEPING `analyzed:` visible so the stricter triage
#   tools (diff_proof_raw.sh, corpus_raw_diff.sh) can still show a diff on a
#   line the gates ignore. Their caches rewrite the cached `analyzed:` path
#   to the current invocation's instead.
strip_env_lines() {
    grep -v -e '^Git revision:' -e '^Compiled at:' -e '^[[:space:]]*processing time:' "$1"
}
# norm — the SWEEP policy: BLANK the four lines to placeholders on stdin.
#   A blanked line still pins that the line was printed and where, which is
#   what sweep_common.sh's nonempty_compared leans on (delete vs blank is the
#   difference between "no evidence" and "weak evidence").
norm() {
    sed -e 's/^Git revision:.*/GITREV/' -e 's/^Compiled at:.*/COMPILED/' \
        -e 's/^[[:space:]]*analyzed:.*/ANALYZED/' -e 's/^[[:space:]]*processing time:.*/PTIME/'
}

# --- per-file canonical flags (file_flags.tsv) -------------------------------
# flags_for <relpath> — echo the extra prover flags for a corpus relpath
#   (empty if none, or if $FLAGS_MAP is unset/absent — a missing map means "no
#   flags", status 0).
flags_for() {
    [ -f "${FLAGS_MAP:-}" ] || return 0
    awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"
}

# --- oracle and execution identity + gate cache key --------------------------
# patch_series_fingerprint <repo-root>
#   Hash the ordered patch list and every listed patch. This is the source
#   identity that setup.sh stamps beside the binary after its controlled build.
patch_series_fingerprint() {
    local repo=$1 series="$1/patches/series" name patch payload= sha
    [ -f "$series" ] || return 1
    while IFS= read -r name || [ -n "$name" ]; do
        case "$name" in ''|'#'*) continue ;; esac
        [ -f "$repo/patches/$name" ] || return 1
    done < "$series"
    while IFS= read -r name || [ -n "$name" ]; do
        case "$name" in ''|'#'*) continue ;; esac
        patch="$repo/patches/$name"
        sha=$(file_sha256 "$patch") || return 1
        payload+="$name"$'\t'"$sha"$'\n'
    done < "$series"
    printf '%s' "$payload" | sha256sum | cut -d' ' -f1
}

# file_sha256 <file> — hash one file without a pipeline hiding read failures.
file_sha256() {
    local line
    line=$(sha256sum < "$1") || return 1
    printf '%s\n' "${line%% *}"
}

# binary_sha256 <file> — the one executable-content fingerprint recipe.
binary_sha256() { file_sha256 "$1"; }

# Capture the Rust binary used by the comparison half of a gate.  Its hash is
# deliberately not part of any Haskell cache key: rebuilding the port must not
# invalidate an expensive oracle cache, but a comparison already in flight
# must not silently straddle two Rust executables.
rs_fingerprint() {
    RS_FP_PATH=$1
    [ -x "$RS_FP_PATH" ] || return 1
    RS_FP=$(binary_sha256 "$RS_FP_PATH") || return 1
    export RS_FP_PATH RS_FP
}

binary_identity_unchanged() {
    local path=$1 expected=$2 current
    current=$(binary_sha256 "$path") || return 1
    [ "$current" = "$expected" ]
}

rs_identity_unchanged() {
    [ -n "${RS_FP_PATH:-}" ] && [ -n "${RS_FP:-}" ] || return 1
    binary_identity_unchanged "$RS_FP_PATH" "$RS_FP"
}

# execution_fingerprint <maude-binary> <derivcheck-timeout>
#   Set EXEC_FP and EXEC_FP_SALT for every Haskell-output cache.  The oracle
#   version and Tamarin's derivation-check cap select reusable output across
#   platforms. Executable hashes only detect replacement during this run.
execution_fingerprint() {
    local maude=$1 deriv=$2 payload version
    [ -x "$maude" ] || {
        echo "execution_fingerprint: maude '$maude' is not executable" >&2
        return 1
    }
    MAUDE_FP=$(binary_sha256 "$maude") || return 1
    MAUDE_FP_PATH=$maude
    version=$("$maude" --version) || return 1
    [ -n "$version" ] || return 1
    payload=$(printf 'format=2\nmaude_version=%s\nderivcheck_timeout=%s\n' \
        "$version" "$deriv") || return 1
    EXEC_FP=$(printf '%s' "$payload" | sha256sum | cut -d' ' -f1) || return 1
    EXEC_FP_SALT=${EXEC_FP:0:12}
}

# producer_identity_unchanged
# Rehash the executables captured at startup.
# This guard detects a tool replaced during the run, independently of the
# portable versions used to select persistent cache entries.
execution_identity_unchanged() {
    local current
    [ -n "${MAUDE_FP_PATH:-}" ] && [ -n "${MAUDE_FP:-}" ] || return 1
    current=$(binary_sha256 "$MAUDE_FP_PATH") || return 1
    [ "$current" = "$MAUDE_FP" ] || return 1
    if [ -n "${DOT_FP_PATH:-}" ]; then
        current=$(binary_sha256 "$DOT_FP_PATH") || return 1
        [ "$current" = "${DOT_FP:-}" ] || return 1
    fi
}

producer_identity_unchanged() {
    local current
    execution_identity_unchanged || return 1
    [ -n "${HS_FP_PATH:-}" ] && [ -n "${HS_FP:-}" ] || return 1
    current=$(binary_sha256 "$HS_FP_PATH") || return 1
    [ "$current" = "$HS_BINARY_FP" ]
}

# Use after a Rust invocation has contributed to a verdict.  The oracle and
# execution identities protect the cached/reference side; the Rust identity
# protects the side being certified without coupling it to the cache key.
comparison_identity_unchanged() {
    producer_identity_unchanged && rs_identity_unchanged
}

# Rust-only checks have no Haskell producer, but still depend on Maude and the
# selected Rust executable remaining fixed for the duration of the run.
rs_execution_identity_unchanged() {
    execution_identity_unchanged && rs_identity_unchanged
}

# duration_seconds <GNU-timeout-duration>
# Convert the integer s/m/h/d spellings accepted by timeout(1), for deciding
# whether a cached timeout reached at least the cap requested by this run.
duration_seconds() {
    local value=$1 number unit factor
    if [[ "$value" =~ ^([0-9]+)([smhd]?)$ ]]; then
        number=${BASH_REMATCH[1]}
        unit=${BASH_REMATCH[2]}
        case $unit in
            ''|s) factor=1 ;;
            m) factor=60 ;;
            h) factor=3600 ;;
            d) factor=86400 ;;
        esac
        printf '%s\n' "$((number * factor))"
    else
        return 1
    fi
}

# hs_fingerprint <oracle-binary> [maude-binary] [repo-root]
# Capture version and source attestation once for both cache selection and
# oracle_rev_check. Executable bytes only verify the attestation and detect
# replacement during a run; persistent identities remain version-based.
hs_fingerprint() {
    local hs=$1 repo=${3:-$GATE_COMMON_DIR/..} output main stamp key value
    local stamp_binary stamp_pin stamp_series
    local -a maude_args=()
    HS_FP_LEGACY=$(stat -c '%s.%Y' "$hs") || return 1
    HS_BINARY_FP=$(binary_sha256 "$hs") || return 1
    [ -z "${2:-}" ] || maude_args=("--with-maude=$2")
    output=$(timeout 60 "$hs" "${maude_args[@]}" --version 2>/dev/null) || return 1
    HS_VERSION=$(printf '%s\n' "$output" | head -1)
    [ -n "$HS_VERSION" ] || return 1
    HS_REVISION=$(printf '%s\n' "$output" | sed -n 's/^Git revision: \([^ ,]*\).*/\1/p')
    HS_ATTESTATION_STATUS=missing
    HS_ATTESTATION_PIN=
    HS_PATCH_SERIES=unattested
    main=$(git -C "$repo" worktree list --porcelain 2>/dev/null \
        | awk '/^worktree/{print $2; exit}') || main=
    for stamp in "${hs}.tamarin-rs-oracle" \
            "$repo/tamarin-prover-testing/.stack-work/tamarin-rs-oracle" \
            "${main:+$main/tamarin-prover-testing/.stack-work/tamarin-rs-oracle}"; do
        [ -r "$stamp" ] || continue
        HS_ATTESTATION_STATUS=mismatch
        stamp_binary= stamp_pin= stamp_series=
        while IFS='=' read -r key value || [ -n "$key" ]; do
            case "$key" in
                binary_sha256) stamp_binary=$value ;;
                pin) stamp_pin=$value ;;
                patch_series_sha256) stamp_series=$value ;;
            esac
        done < "$stamp"
        if [ "$stamp_binary" = "$HS_BINARY_FP" ]; then
            HS_ATTESTATION_STATUS=matched
            HS_ATTESTATION_PIN=$stamp_pin
            HS_PATCH_SERIES=$stamp_series
            break
        fi
    done
    HS_FP=$(printf 'format=2\nversion=%s\nrevision=%s\npatch_series=%s\n' \
        "$HS_VERSION" "$HS_REVISION" "$HS_PATCH_SERIES" | sha256sum | cut -d' ' -f1) || return 1
    HS_FP_SALT=${HS_FP:0:12}
    HS_FP_PATH=$hs
    export HS_BINARY_FP
}
# parser_input_manifest <theory> [flags]
#   Ask the real parser which include/preprocessor/oracle inputs are active.
#   Tagged TSV rows are `S<TAB>x:<hex-source><TAB>x:<hex-staged>` and `O<...>`.
#   Encoding keeps arbitrary Unix path bytes out of the delimiters. Missing
#   active inputs are fatal. Other syntax errors fall back to the
#   independent conservative scanner in input_manifest: malformed theories
#   are part of the parity corpus too, and must remain comparable.
parser_input_manifest() {
    local theory flags=${2:-}
    # NUL termination preserves trailing newlines in the filename.
    IFS= read -r -d '' theory < <(realpath -z -- "$1") || return 1
    local bin=${INPUT_MANIFEST_BIN:-${RS_PATH:-${RS_BIN:-${BIN:-$GATE_COMMON_DIR/../target/release/tamarin-rs}}}}
    [ -x "$bin" ] || {
        echo "input_manifest: no executable Rust prover at '$bin'" >&2
        return 1
    }
    local -a argv=()
    [ -z "$flags" ] || read -r -a argv <<< "$flags"
    "$bin" "${argv[@]}" input-manifest "$theory"
}

# Manifest paths use `x:<hex bytes>` so tabs, newlines, and non-UTF-8 Unix path
# bytes cannot corrupt the line-oriented format. Accept legacy/raw fields too:
# this keeps test doubles and old binaries useful, while every current producer
# emits the encoded form. The caller names the destination variable so trailing
# newlines survive (command substitution would strip them).
manifest_decode_into() {
    local field=$1 var=$2 escaped= i pair
    case "$field" in
        x:*[!0-9a-f]*|x:?) return 1 ;;
        x:*)
            field=${field#x:}
            [ $(( ${#field} % 2 )) -eq 0 ] || return 1
            for ((i=0; i<${#field}; i+=2)); do
                pair=${field:i:2}
                [ "$pair" != 00 ] || return 1
                escaped+="\\x$pair"
            done
            printf -v "$var" '%b' "$escaped"
            ;;
        *) printf -v "$var" '%s' "$field" ;;
    esac
}

manifest_encode() {
    printf 'x:'
    printf '%s' "$1" | od -An -v -tx1 | tr -d ' \n'
}

# Put legacy/raw rows from test doubles or an older binary into the current
# representation before union/dedup. Current encoded rows pass through.
manifest_normalize() {
    local tag source staged
    while IFS=$'\t' read -r tag source staged; do
        case "$tag" in S|O) ;; *) continue;; esac
        # Current producers encode every field together. A legacy source path
        # is absolute, so use that field to classify the whole row; this avoids
        # misreading an old relative path literally named `x:beef` as hex.
        case "$source" in
            x:*) ;;
            *)
                source=$(manifest_encode "$source") || return 1
                staged=$(manifest_encode "$staged") || return 1
                ;;
        esac
        printf '%s\t%s\t%s\n' "$tag" "$source" "$staged"
    done
}

# input_manifest <theory> [flags]
#   Union the parser's exact manifest with a deliberately conservative,
#   parser-independent scan of existing includes and executable oracle paths.
#   Cache correctness must not depend solely on the Rust parser being tested:
#   if it accidentally omits an input, the independent side still invalidates
#   the entry. The parser remains authoritative for active missing includes;
#   other syntax failures retain the independent conservative identity.
input_manifest() {
    local theory=$1 flags=${2:-} exact conservative root root_field root_name_field error
    [ -f "$theory" ] && [ -r "$theory" ] || {
        echo "input_manifest: theory '$theory' is not a readable file" >&2
        return 1
    }
    error=$(mktemp) || return 1
    if exact=$(parser_input_manifest "$theory" "$flags" 2>"$error"); then
        exact=$(manifest_normalize <<< "$exact") || { rm -f "$error"; return 1; }
    elif grep -q '^failed to read included file ' "$error"; then
        cat "$error" >&2
        rm -f "$error"
        return 1
    else
        # The gate still runs both provers and compares their parse failure.
        # Key the attempt on every existing dependency the grammar-independent
        # scanner can see, rather than making malformed corpus fixtures
        # permanently uncacheable.
        exact=
    fi
    rm -f "$error"
    conservative=$(python3 "$GATE_COMMON_DIR/conservative_inputs.py" "$theory" "$flags") \
        || return 1
    IFS= read -r -d '' root < <(realpath -z -- "$theory") || return 1
    root_field=$(manifest_encode "$root") || return 1
    # Parameter expansion preserves a basename ending in newlines; command
    # substitution around basename(1) would silently remove them.
    root_name_field=$(manifest_encode "${root##*/}") || return 1
    {
        printf 'S\t%s\t%s\n' "$root_field" "$root_name_field"
        printf '%s\n%s\n' "$exact" "$conservative" | awk -F'\t' 'NF >= 3'
    } | LC_ALL=C awk -F'\t' '!seen[$0]++'
}

# shared_cache_root <repo-root>
#   One cache pool under the common/main worktree, shared by linked worktrees.
shared_cache_root() {
    local repo=$1 common shared
    if [ -n "${TAMARIN_RS_CACHE_ROOT:-}" ]; then
        printf '%s\n' "$TAMARIN_RS_CACHE_ROOT"
        return 0
    fi
    common=$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir 2>/dev/null) \
        || common=
    if [ -n "$common" ]; then shared=$(dirname "$common"); else shared=$repo; fi
    printf '%s/scripts/.gate_cache\n' "$shared"
}

# shared_cache_dir <repo-root> <name> [legacy-dir]
#   Resolve a named cache below the common root.  On first use, an old cache in
#   the main checkout is renamed into place under a migration lock; a legacy
#   directory in any other worktree is left untouched for manual import.
shared_cache_dir() {
    local repo=$1 name=$2 legacy=${3:-} root target fd common shared
    root=$(shared_cache_root "$repo") || return 1
    mkdir -p "$root" || return 1
    target="$root/$name"
    exec {fd}>"$root/.migration.lock" || return 1
    flock "$fd" || { exec {fd}>&-; return 1; }
    if [ ! -e "$target" ] && [ -n "$legacy" ] && [ -d "$legacy" ]; then
        common=$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir 2>/dev/null) \
            || common=
        shared=${common:+$(dirname "$common")}
        case "$legacy" in
            "$shared"/*) mv "$legacy" "$target" || { flock -u "$fd"; exec {fd}>&-; return 1; } ;;
            *) echo "shared_cache_dir: preserving worktree-local legacy cache $legacy; import it into $target manually" >&2 ;;
        esac
    fi
    mkdir -p "$target" || { flock -u "$fd"; exec {fd}>&-; return 1; }
    flock -u "$fd"; exec {fd}>&-
    printf '%s\n' "$target"
}

# Non-web cache publication primitives. Callers lock one key across their
# check/run/publish transaction; payloads are validated and atomically renamed
# from the destination filesystem.
cache_entry_lock() {
    local dir=$1 key=$2 var=$3 _cache_fd
    exec {_cache_fd}>"$dir/$key.lock" || return 1
    flock "$_cache_fd" || { exec {_cache_fd}>&-; return 1; }
    printf -v "$var" '%s' "$_cache_fd"
}
cache_entry_unlock() {
    local fd=$1
    flock -u "$fd"; exec {fd}>&-
}

# A nonzero run with no diagnostic or product is not reproducible evidence
# about its input: it commonly means the process could not start or was killed
# by its environment. Such a result must not become a durable cache entry.
transient_silent_failure() {
    [ "$1" -ne 0 ] && [ ! -s "$2" ] && [ ! -s "$3" ]
}

# claim_output <path> <fd-var>
# Hold an exclusive lock beside a shared result file for the caller's lifetime.
# Without it, two gate runs interleave rows and can manufacture both duplicate
# evidence and misleading row-count failures.
claim_output() {
    local target=$1 var=$2 _output_fd
    mkdir -p "$(dirname "$target")" || return 1
    exec {_output_fd}>"$target.lock" || return 1
    if ! flock -n "$_output_fd"; then
        echo "ERROR: another gate is writing '$target'" >&2
        exec {_output_fd}>&-
        return 1
    fi
    if ! : > "$target"; then
        exec {_output_fd}>&-
        return 1
    fi
    printf -v "$var" '%s' "$_output_fd"
}
cache_publish_text() {
    local target=$1 value=$2 tmp
    tmp=$(mktemp "$(dirname "$target")/.publish.XXXXXX") || return 1
    printf '%s' "$value" > "$tmp" && mv -f "$tmp" "$target" || { rm -f "$tmp"; return 1; }
}
cache_publish_gzip() {
    local target=$1 source=$2 tmp
    tmp=$(mktemp "$(dirname "$target")/.publish.XXXXXX") || return 1
    gzip -c "$source" > "$tmp" && gzip -t "$tmp" && mv -f "$tmp" "$target" \
        || { rm -f "$tmp"; return 1; }
}
cache_gzip_valid() { [ -f "$1" ] && gzip -t "$1" 2>/dev/null; }

# Fill the shared no-prove Haskell load artifact used by pretty_gate and
# wf_gate. The caller supplies the already-computed input key and flags; this
# helper owns the per-entry lock and rechecks both inputs and producer bytes
# before publishing.
hs_load_cache_fill() {
    local rel=$1 f=$2 key=$3 fl=$4 timeout_secs=$5
    local lock_fd tmp normalized rc checked_key
    cache_entry_lock "$HS_CACHE" "$key" lock_fd || return 0
    cache_gzip_valid "$HS_CACHE/$key.load.gz" \
        && { cache_entry_unlock "$lock_fd"; return 0; }
    case " $fl " in *" --diff "*) cache_entry_unlock "$lock_fd"; return 0;; esac
    tmp=$(mktemp) || { cache_entry_unlock "$lock_fd"; return 0; }
    normalized=$(mktemp) || {
        rm -f "$tmp"; cache_entry_unlock "$lock_fd"; return 0
    }
    # shellcheck disable=SC2086  # $fl must become distinct CLI arguments.
    if timeout "$timeout_secs" "$HS_PATH" --with-maude="$MAUDE" $fl \
            --derivcheck-timeout="$DERIVCHECK_TIMEOUT" "$f" >"$tmp" 2>/dev/null; then
        rc=0
    else
        rc=$?
    fi
    if ! strip_env < "$tmp" > "$normalized"; then
        echo "  HS NORMALIZE FAILED  $rel — nothing cached" >&2
        rm -f "$tmp" "$normalized"; cache_entry_unlock "$lock_fd"; return 0
    fi
    rm -f "$tmp"
    # These gates cover valid loadable corpus inputs. Any nonzero status means
    # the stdout is not a reference result, even when it looks complete.
    if [ "$rc" -ne 0 ]; then
        echo "  HS FAILED   $rel (rc=$rc, cap ${timeout_secs}s) — nothing cached" >&2
        rm -f "$normalized"; cache_entry_unlock "$lock_fd"; return 0
    fi
    # Command substitution in the former producers stripped trailing newlines,
    # so one or more blank lines counted as empty. Preserve that contract while
    # streaming large outputs through a file.
    if ! grep -q . "$normalized"; then
        echo "  HS EMPTY!   $rel${fl:+  (flags: $fl)} — nothing cached" >&2
        rm -f "$normalized"; cache_entry_unlock "$lock_fd"; return 0
    fi
    if ! checked_key=$(ckey "$rel" "$f") || [ "$checked_key" != "$key" ] \
            || ! producer_identity_unchanged; then
        echo "  INPUT CHANGED  $rel while Haskell was running — nothing cached" >&2
        rm -f "$normalized"; cache_entry_unlock "$lock_fd"; return 0
    fi
    cache_publish_gzip "$HS_CACHE/$key.load.gz" "$normalized" || true
    rm -f "$normalized"
    cache_entry_unlock "$lock_fd"
}

# Publish proof stdout only after its exit status is durable. Callers hold the
# entry lock, so an orphaned .rc after a payload failure is harmless and the
# next fill may retry; the unsafe inverse (.full.gz without .rc) is impossible.
cache_publish_proof() {
    local rc_target=$1 payload_target=$2 rc=$3 source=$4
    cache_publish_text "$rc_target" "$rc" || return 1
    cache_publish_gzip "$payload_target" "$source"
}

_include_shas_from_manifest() {
    local manifest=$1 first=1 tag src_field rel_field src rel identity_rel sha
    while IFS=$'\t' read -r tag src_field rel_field; do
        [ "$tag" = S ] || continue
        if [ "$first" = 1 ]; then first=0; continue; fi
        manifest_decode_into "$src_field" src || return 1
        manifest_decode_into "$rel_field" rel || return 1
        sha=$(file_sha256 "$src") || return 1
        identity_rel=$rel
        case "$rel" in *$'\t'*|*$'\n'*) identity_rel=$rel_field;; esac
        if [ -z "$identity_rel" ]; then
            identity_rel=$src
            case "$src" in *$'\t'*|*$'\n'*) identity_rel=$src_field;; esac
            identity_rel="external:$identity_rel"
        fi
        printf '%s %s\n' "$sha" "$identity_rel"
    done <<< "$manifest"
}

_oracle_shas_from_manifest() {
    local manifest=$1 src_field rel_field src rel identity_rel sha mode
    local -a rows=()
    while IFS=$'\t' read -r tag src_field rel_field; do
        [ "$tag" = O ] || continue
        manifest_decode_into "$src_field" src || return 1
        manifest_decode_into "$rel_field" rel || return 1
        sha=$(file_sha256 "$src") || return 1
        mode=$(stat -Lc '%a' "$src") || return 1
        identity_rel=$rel
        case "$rel" in *$'\t'*|*$'\n'*) identity_rel=$rel_field;; esac
        if [ -z "$identity_rel" ]; then
            identity_rel=$src
            case "$src" in *$'\t'*|*$'\n'*) identity_rel=$src_field;; esac
            identity_rel="external:$identity_rel"
        fi
        rows+=("$sha $mode $identity_rel")
    done <<< "$manifest"
    [ "${#rows[@]}" -eq 0 ] || printf '%s\n' "${rows[@]}" | sort -u
}

# input_content_key <theory> [flags]
#   Canonical identity for every source input seen by the parser.  Producer
#   identity deliberately lives outside this key so the same helper can back
#   gate caches, proof caches, web caches and reference certificates.
input_content_key() {
    local theory=$1 flags=${2:-} theory_sha inc ora manifest payload
    theory_sha=$(file_sha256 "$theory") || return 1
    manifest=$(input_manifest "$theory" "$flags") || return 1
    inc=$(_include_shas_from_manifest "$manifest") || return 1
    ora=$(_oracle_shas_from_manifest "$manifest") || return 1
    payload=$(printf 'format=1\ntheory_sha256=%s\nflags_sha256=%s\nincludes:\n%s\noracles:\n%s\n' \
        "$theory_sha" "$(printf '%s' "$flags" | sha256sum | cut -d' ' -f1)" \
        "$inc" "$ora") || return 1
    printf '%s' "$payload" | sha256sum | cut -d' ' -f1
}

# input_scope_fingerprint <corpus-root> <flags-map> <relpath...>
#   Hash the exact sorted relpath/input-key pairs covered by a run.  This is a
#   certificate identity, not just a file count: a different same-sized
#   allowlist cannot certify a reference update.
input_scope_fingerprint() {
    local corpus=$1 flags_map=$2 rel key
    shift 2
    local tmp
    tmp=$(mktemp) || return 1
    local FLAGS_MAP=$flags_map
    for rel in "$@"; do
        key=$(input_content_key "$corpus/$rel" "$(flags_for "$rel")") || {
            rm -f "$tmp"
            return 1
        }
        printf '%s\t%s\n' "$rel" "$key" >> "$tmp" || {
            rm -f "$tmp"
            return 1
        }
    done
    LC_ALL=C sort -u "$tmp" -o "$tmp" || { rm -f "$tmp"; return 1; }
    file_sha256 "$tmp"
    local rc=$?
    rm -f "$tmp"
    return "$rc"
}
# ckey <relpath> <abs-file> — the gate cache key. Uses $HS_FP_SALT (set by
#   hs_fingerprint), $EXEC_FP_SALT (set by execution_fingerprint),
#   parser-selected dependencies and flags_for, so an entry whose
#   included fragments or oracle scripts changed, a flagged entry and an entry
#   produced by a different oracle binary are all a MISS. KEY FORMAT (shared by
#   corpus_file_diff.sh, wf_gate.sh, pretty_gate.sh and triage_diff_vs_hs.sh):
#     <sha256(canonical theory/include/oracle/flags identity)>
#                     __e<first 12 hex of EXEC_FP>__b<first 12 hex of HS_FP>
ckey() {
    local h fl
    [ -n "${EXEC_FP_SALT:-}" ] || {
        echo "ckey: execution_fingerprint has not been computed" >&2
        return 1
    }
    fl=$(flags_for "$1")
    h=$(input_content_key "$2" "$fl") || return 1
    printf '%s__e%s__b%s' "$h" "$EXEC_FP_SALT" "$HS_FP_SALT"
}

# --- gate file list ----------------------------------------------------------
# allowlist_guard — a set-but-unreadable ALLOWLIST is a typo, not a request for
#   the default: falling through would silently run something other than what
#   was asked for.
allowlist_guard() {
    if [ -n "${ALLOWLIST:-}" ] && [ ! -r "$ALLOWLIST" ]; then
        echo "ALLOWLIST '$ALLOWLIST' is not a readable file" >&2; exit 2
    fi
}
# filelist — the gates' shared precedence: explicit ALLOWLIST env > the
#   committed canonical corpus (scripts/parity_corpus.txt) > the sourcing
#   script's own filelist_fallback (corpus_file_diff.sh derives from PREV_TSV
#   or refuses; wf_gate.sh/pretty_gate.sh walk the corpus tree).
filelist() {
    if [ -n "${ALLOWLIST:-}" ]; then cat "$ALLOWLIST"
    elif [ -f "$GATE_COMMON_DIR/parity_corpus.txt" ]; then cat "$GATE_COMMON_DIR/parity_corpus.txt"
    else filelist_fallback; fi
}

# --- maude resolver ----------------------------------------------------------
# resolve_hs_oracle [repo-root] — print the oracle binary selected for a run.
# An explicit HS_PATH is authoritative and a broken value is a hard failure.
# Otherwise prefer this worktree's build, then the main worktree's shared build,
# then tamarin-prover on PATH.
resolve_hs_oracle() {
    local repo=${1:-$(cd "$GATE_COMMON_DIR/.." && pwd)} main c
    if [ -n "${HS_PATH:-}" ]; then
        if [ -x "$HS_PATH" ]; then printf '%s\n' "$HS_PATH"; return 0; fi
        echo "resolve_hs_oracle: HS_PATH='$HS_PATH' is not executable" >&2
        return 2
    fi
    for c in "$repo"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover; do
        if [ -x "$c" ]; then printf '%s\n' "$c"; return 0; fi
    done
    main=$(git -C "$repo" worktree list --porcelain 2>/dev/null \
        | awk '/^worktree/{print $2; exit}')
    if [ -n "$main" ] && [ "$main" != "$repo" ]; then
        for c in "$main"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover; do
            if [ -x "$c" ]; then printf '%s\n' "$c"; return 0; fi
        done
    fi
    if c=$(command -v tamarin-prover 2>/dev/null) && [ -n "$c" ]; then
        printf '%s\n' "$c"; return 0
    fi
    echo "resolve_hs_oracle: no Haskell tamarin-prover found in this worktree," \
         "the main worktree, or PATH" >&2
    return 2
}

# resolve_maude — print the one maude this run uses. Resolution order:
#     1. $MAUDE_PATH when set. Set-but-unusable is a HARD FAIL, never a
#        silent fall-through: a wrong MAUDE_PATH must not quietly become
#        whatever else is lying around.
#     2. `maude` on the operator's own PATH.
#     3. /home/linuxbrew/.linuxbrew/bin/maude (this box keeps maude off PATH).
#   Nothing resolving is a hard fail naming all three steps.
resolve_maude() {
    local m
    if [ -n "${MAUDE_PATH:-}" ]; then
        if [ -x "$MAUDE_PATH" ]; then printf '%s\n' "$MAUDE_PATH"; return 0; fi
        echo "resolve_maude: MAUDE_PATH='$MAUDE_PATH' is set but is not an executable" \
             "file — refusing to fall back to PATH or the linuxbrew install" \
             "(fix or unset MAUDE_PATH)" >&2
        return 2
    fi
    if m=$(command -v maude 2>/dev/null) && [ -n "$m" ]; then printf '%s\n' "$m"; return 0; fi
    if [ -x /home/linuxbrew/.linuxbrew/bin/maude ]; then
        printf '%s\n' /home/linuxbrew/.linuxbrew/bin/maude; return 0
    fi
    echo "resolve_maude: no maude found — \$MAUDE_PATH is unset, 'maude' is not on" \
         "PATH, and /home/linuxbrew/.linuxbrew/bin/maude does not exist." \
         "Install maude or set MAUDE_PATH." >&2
    return 2
}
# maude_on_path <resolved-maude> — prepend the resolved maude's directory to
#   PATH, so children that probe `maude` by NAME (both provers do, when no
#   --with-maude is passed) exec exactly the binary the resolver chose.
maude_on_path() { PATH="$(dirname "$1"):$PATH"; export PATH; }

# --- preflights --------------------------------------------------------------
# oracle_rev_check <hs-bin> <maude> <repo-root>
#   The oracle IS the specification, so it must be the controlled setup.sh
#   build of the submodule pin plus the current ordered patch series. setup.sh
#   writes an attestation beside the executable containing those two source
#   identities and the executable's SHA-256; this check rejects a manually
#   rebuilt dirty worktree even when its base commit matches. The check is
#   skipped only when the repo has no readable gitlink. A binary built outside
#   a git checkout stamps `UNKNOWN`, which is rejected. Set
#   ALLOW_ORACLE_REV_MISMATCH=1 only for a deliberate cross-source comparison.
#   A byte-identical HS_PATH copy may use the canonical setup attestation.
#   Fingerprinting captures the version/revision using the explicit backend,
#   so no second process or attestation lookup is needed here.
oracle_rev_check() {
    local hs=$1 maude=$2 repo=$3 pin expected_series reason=
    hs_fingerprint "$hs" "$maude" "$repo" || {
        echo "ERROR: cannot fingerprint oracle '$hs'" >&2
        exit 2
    }
    ORACLE_REVISION=$HS_REVISION
    ORACLE_SOURCE_STATUS=verified
    ORACLE_SOURCE_NOTE=
    pin=$(git -C "$repo" rev-parse :tamarin-prover 2>/dev/null) || pin=
    if [ -z "$pin" ]; then
        ORACLE_SOURCE_STATUS=not-checked
        ORACLE_SOURCE_NOTE="no readable tamarin-prover gitlink"
        return 0
    fi
    if [ -z "$HS_REVISION" ]; then
        reason="prints no Git revision"
    elif [ "$HS_REVISION" != "$pin" ]; then
        reason="is revision $HS_REVISION but the submodule pin is $pin"
    elif [ "$HS_ATTESTATION_STATUS" = matched ]; then
        expected_series=$(patch_series_fingerprint "$repo") || expected_series=
        if [ "$HS_ATTESTATION_PIN" != "$pin" ]; then
            reason="attests pin ${HS_ATTESTATION_PIN:-missing}, expected $pin"
        elif [ -z "$expected_series" ] || [ "$HS_PATCH_SERIES" != "$expected_series" ]; then
            reason="was built with a different patch series"
        fi
    elif [ "$HS_ATTESTATION_STATUS" = mismatch ]; then
        reason="does not match any available setup.sh source attestation"
    else
        reason="has no setup.sh source attestation"
    fi
    if [ -n "$reason" ]; then
        ORACLE_SOURCE_STATUS=failed
        ORACLE_SOURCE_NOTE=$reason
        echo "ERROR: oracle '$hs' $reason — it would certify the port against" \
             "unverified Haskell sources (rebuild with ./setup.sh testing, or" \
             "ALLOW_ORACLE_REV_MISMATCH=1)" >&2
        if [ "${ALLOW_ORACLE_REV_MISMATCH:-0}" = 1 ]; then
            ORACLE_SOURCE_STATUS=waived
            ORACLE_SOURCE_NOTE="$reason (waived by ALLOW_ORACLE_REV_MISMATCH=1)"
        else
            exit 2
        fi
    else
        ORACLE_SOURCE_NOTE="revision and setup attestation match the submodule pin"
    fi
}

# rs_stale_check [rs-bin] [repo-root]  (defaults: $RS_BIN, $REPO)
#   Refuse to run when an in-tree target binary predates its sources — a stale
#   binary silently certifies the wrong code (ALLOW_STALE_BIN=1 overrides).
#   An external/sealed binary cannot truthfully be matched to this checkout by
#   Cargo dep-info or mtimes, so only fingerprint its contents for the run's
#   replacement guards. Its source provenance remains the caller's concern.
#
#   A `crates/**/*.rs` glob is not the whole input set. The binary also bakes
#   in files from OUTSIDE crates/ via `include_str!` — `tamarin-prover/data/
#   intruder_variants_{dh,bp}.spthy` are compiled into `intruder_variants.rs`,
#   so a submodule bump that edits them changes the port's behaviour on every
#   DH theory while leaving every path the glob covers untouched. Cargo already
#   records the complete list next to the binary in its dep-info file, so read
#   that when it is there rather than re-deriving it. Paths under `.git/` are
#   excluded: build.rs watches HEAD/refs/packed-refs to bake the revision and
#   timestamp into `Git revision:` / `Compiled at:`, and every gate normalizes
#   those two lines away, so a commit is not a reason to rebuild.
rs_stale_check() {
    local bin=${1:-$RS_BIN} repo=${2:-$REPO} newest= dep p missing= bin_abs target_abs
    bin_abs=$(realpath -m -- "$bin") || bin_abs=$bin
    target_abs=$(realpath -m -- "$repo/target") || target_abs=$repo/target
    case "$bin_abs" in
        "$target_abs"/*) ;;
        *)
            rs_fingerprint "$bin" || {
                echo "ERROR: cannot fingerprint Rust binary $bin" >&2
                exit 2
            }
            return 0
            ;;
    esac
    dep="$bin.d"
    if [ -f "$dep" ]; then
        while read -r p; do
            case $p in '' | */.git/*) continue ;; esac
            case $p in /*) ;; *) p="$repo/$p";; esac
            if [ ! -e "$p" ]; then missing=$p; break; fi
            if [ "$p" -nt "$bin" ]; then newest=$p; break; fi
        done < <(head -1 "$dep" | cut -d: -f2- | tr ' ' '\n')
    else
        # Older/non-Cargo builds have no dep-info. This conservative fallback
        # is necessarily broader, but must not replace Cargo's exact list when
        # it is available (test-only Rust files do not rebuild this binary).
        newest=$(find "$repo/crates" -name '*.rs' -newer "$bin" -print -quit 2>/dev/null)
    fi
    [ -n "$newest" ] || newest=$(find "$repo/crates" -name 'Cargo.toml' -newer "$bin" -print -quit 2>/dev/null)
    # The workspace root manifests are inputs too: a dependency bump there
    # rebuilds the binary but leaves every file under crates/ untouched.
    [ -n "$newest" ] || newest=$(find "$repo/Cargo.toml" "$repo/Cargo.lock" -newer "$bin" -print -quit 2>/dev/null)
    if [ -n "$missing" ]; then
        echo "ERROR: $bin dep-info names missing source $missing — rebuild first (ALLOW_STALE_BIN=1 to override)" >&2
        [ "${ALLOW_STALE_BIN:-0}" = 1 ] || exit 2
    elif [ -n "$newest" ]; then
        echo "ERROR: $bin is older than $newest — rebuild first (ALLOW_STALE_BIN=1 to override)" >&2
        [ "${ALLOW_STALE_BIN:-0}" = 1 ] || exit 2
    fi
    rs_fingerprint "$bin" || {
        echo "ERROR: cannot fingerprint Rust binary $bin" >&2
        exit 2
    }
}
