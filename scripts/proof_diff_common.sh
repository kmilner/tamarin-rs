# Shared helpers for the raw and canonical proof-differential tools. Source
# gate_common.sh first: proof_cache_key uses its include and oracle digests.

# proof_cache_key <theory> <lemma> [flags]
#   The extension-free key shared by all three .hs_canon_cache users.
proof_cache_key() {
    local theory=$1 lemma=$2 flags=${3:-} h inc flag_salt=
    h=$(sha256sum "$theory" 2>/dev/null | cut -d' ' -f1)
    inc=$(include_shas "$theory")
    if [ -n "$inc" ]; then h="${h}__i$(printf '%s' "$inc" | sha256sum | cut -c1-12)"; fi
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
