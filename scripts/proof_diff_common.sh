# Shared helpers for the raw and canonical proof-differential tools. Source
# gate_common.sh first: proof_cache_key uses its include and oracle digests.

# proof_now_ms
#   Monotonicity is unnecessary for elapsed prover timings, but millisecond
#   units must be stable across GNU and uutils `date`. uutils ignores the field
#   width in `%3N`; divide the full nanosecond timestamp instead. BSD date does
#   not implement `%N`, so keep a Python fallback for diagnostics on macOS.
proof_now_ms() {
    local ns
    ns=$(date +%s%N 2>/dev/null)
    case "$ns" in
        ''|*[!0-9]*) python3 -c 'import time; print(time.time_ns() // 1_000_000)' ;;
        *) printf '%s\n' "$((ns / 1000000))" ;;
    esac
}

# proof_cache_key <theory> <lemma> [flags]
#   The extension-free key shared by all three .hs_canon_cache users.
proof_cache_key() {
    local theory=$1 lemma=$2 flags=${3:-} h inc ora manifest flag_salt=
    h=$(file_sha256 "$theory" 2>/dev/null) || return 1
    manifest=$(input_manifest "$theory" "$flags") || return 1
    inc=$(_include_shas_from_manifest "$manifest") || return 1
    ora=$(_oracle_shas_from_manifest "$manifest") || return 1
    if [ -n "$inc" ]; then h="${h}__i$(printf '%s' "$inc" | sha256sum | cut -c1-12)"; fi
    if [ -n "$ora" ]; then h="${h}__o$(printf '%s' "$ora" | sha256sum | cut -c1-12)"; fi
    if [ -n "$flags" ]; then
        flag_salt="__f$(printf '%s' "$flags" | sha256sum | cut -c1-12)"
    fi
    printf '%s__%s__v%s%s__b%s' "$h" "$lemma" "$CACHE_VERSION" "$flag_salt" "$HS_FP_SALT"
}

# proof_lemmas_of <theory>
#   Enumerate source lemmas while respecting Tamarin's nested block comments.
proof_lemmas_of() {
    awk '
        BEGIN { depth = 0 }
        {
            line = $0
            while (length(line) > 0) {
                if (depth > 0) {
                    o = index(line, "/*")
                    c = index(line, "*/")
                    if (c == 0 && o == 0) { line = ""; break }
                    if (o > 0 && (c == 0 || o < c)) {
                        depth++; line = substr(line, o + 2)
                    } else {
                        depth--; line = substr(line, c + 2)
                    }
                } else {
                    lc = index(line, "//")
                    bc = index(line, "/*")
                    if (lc > 0 && (bc == 0 || lc < bc)) {
                        print substr(line, 1, lc - 1); line = ""; break
                    }
                    if (bc > 0) {
                        print substr(line, 1, bc - 1)
                        depth++; line = substr(line, bc + 2)
                    } else {
                        print line; line = ""; break
                    }
                }
            }
        }
    ' "$1" 2>/dev/null \
        | grep '^lemma ' \
        | sed -E 's/^lemma[[:space:]]+([A-Za-z0-9_]+).*/\1/'
}

# proof_lemma_block <lemma> <rendered-theory>
#   Print one rendered lemma through (but not including) the next lemma. Keep
#   the lemma name out of a dynamic regular expression: awks disagree about
#   whether a backslash in a `-v` string survives to escape `[`, and lemma
#   names need only an exact prefix plus one of Tamarin's header delimiters.
proof_lemma_block() {
    awk -v lemma="$1" '
        BEGIN { prefix = "lemma " lemma }
        {
            target = index($0, prefix) == 1
            if (target) {
                delim = substr($0, length(prefix) + 1, 1)
                target = delim == " " || delim == "[" || delim == ":"
            }
            if (target) capture = 1
            else if (capture && /^lemma /) exit
            if (capture) print
        }
    ' "$2"
}
