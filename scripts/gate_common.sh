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
#   flags", status 0). The special token `@cd` is not a prover flag: it tells
#   the caller to run from the file's own directory with the bare filename
#   (upstream's cwd-relative default-oracle recipe).
flags_for() {
    [ -f "${FLAGS_MAP:-}" ] || return 0
    awk -F'\t' -v r="$1" '!/^#/ && $1==r {print $2; exit}' "$FLAGS_MAP"
}

# --- oracle fingerprint + gate cache key -------------------------------------
# hs_fingerprint <oracle-binary>
#   Set HS_FP (the size.mtime fingerprint every cached gate keys on) and
#   HS_FP_SALT (its 12-hex sha256, the `__b` component of ckey). Returns
#   stat's status, so a caller that must not proceed without a fingerprint can
#   `hs_fingerprint "$HS_PATH" || exit 2`.
hs_fingerprint() {
    HS_FP=$(stat -c '%s.%Y' "$1") || return 1
    HS_FP_SALT=$(printf '%s' "$HS_FP" | sha256sum | cut -c1-12)
}
# include_shas <theory>
#   sha + name of every file the theory pulls in with `#include "..."`, depth
#   first and transitively, resolved against the INCLUDING file's directory
#   (the spelling upstream uses: examples/testParser/include/include1.spthy,
#   which parity_corpus.txt carries, reaches include_2.spthy and
#   include/include3.spthy that way). Those files are oracle inputs, so a
#   theory sha alone cannot key its output: edit an included file and a cached
#   entry keeps answering for the old one, and a reference row reads DIFF
#   instead of INPUT_CHANGED. Prints NOTHING for a theory with no includes —
#   every corpus file but three — so include-free keys (ckey below, hs_run's
#   digest in sweep_common.sh, rs_ref_check.sh's ikey) are byte-identical to
#   the pre-include ones and the existing entries/rows stay valid.
include_shas() {
    local -A _include_seen=()
    _include_shas_walk() {
        local f=$1 dir inc dep key
        dir=$(dirname "$f")
        while IFS= read -r inc; do
            [ -n "$inc" ] || continue
            dep="$dir/$inc"
            [ -f "$dep" ] || continue
            key=$(cd "$(dirname "$dep")" && printf '%s/%s' "$PWD" "$(basename "$dep")") \
                || return 1
            [ -z "${_include_seen[$key]+x}" ] || continue
            _include_seen[$key]=1
            printf '%s %s\n' "$(sha256sum "$dep" | cut -d' ' -f1)" "$inc"
            _include_shas_walk "$dep" || return 1
        done < <(grep -oE '#include[[:space:]]*"[^"]+"' "$f" 2>/dev/null \
                 | sed 's/.*"\(.*\)"/\1/')
    }
    _include_shas_walk "$1"
    local status=$?
    unset -f _include_shas_walk
    return "$status"
}
# oracle_shas <theory> [flags]
#   Content + mode of every executable-oracle input that can affect this
#   invocation: theory-adjacent/CWD `oracle*` files, quoted heuristic paths,
#   the exact upstream default-oracle candidate, and CLI `--oraclename`.
#   Some entries are conservative extras; over-invalidation is preferable to
#   serving a proof produced by an older oracle script.
oracle_shas() {
    local theory=$1 flags=${2:-} theory_dir run_dir farg p q word next prefix group
    theory_dir=$(dirname "$theory")
    run_dir=$PWD
    farg=$theory
    if [[ " $flags " == *" @cd "* || "$flags" == "@cd" ]]; then
        run_dir=$theory_dir
        farg=$(basename "$theory")
    fi
    {
        for p in "$theory_dir"/oracle* "$run_dir"/oracle*; do
            [ -f "$p" ] || continue
            printf '%s %s scan:%s\n' "$(sha256sum "$p" | cut -d' ' -f1)" \
                "$(stat -c '%a' "$p")" "${p##*/}"
        done

        # HS defaultOracleNames: prefix before the first dot, then the final
        # slash group INCLUDING its slash. Probe it from the invocation CWD.
        prefix=${farg%%.*}
        if [[ "$prefix" == */* ]]; then group="/${prefix##*/}"; else group=$prefix; fi
        p="${group}.oracle"
        [[ "$p" == /* ]] || p="$run_dir/$p"
        if [ -f "$p" ]; then
            printf '%s %s default:%s\n' "$(sha256sum "$p" | cut -d' ' -f1)" \
                "$(stat -c '%a' "$p")" "$group.oracle"
        fi

        while IFS= read -r q; do
            [ -n "$q" ] || continue
            if [[ "$q" == /* ]]; then p=$q; else p="$theory_dir/$q"; fi
            [ -f "$p" ] || continue
            printf '%s %s quoted:%s\n' "$(sha256sum "$p" | cut -d' ' -f1)" \
                "$(stat -c '%a' "$p")" "$q"
        done < <(grep -E 'heuristic' "$theory" 2>/dev/null | grep -oE '"[^"]+"' | tr -d '"' | sort -u)

        next=0
        for word in $flags; do
            q=
            case "$word" in
                --oraclename=*) q=${word#--oraclename=} ;;
                --oraclename) next=1; continue ;;
                *) if [ "$next" = 1 ]; then q=$word; next=0; fi ;;
            esac
            [ -n "$q" ] || continue
            if [[ "$q" == /* ]]; then p=$q; else p="$run_dir/$q"; fi
            [ -f "$p" ] || continue
            printf '%s %s cli:%s\n' "$(sha256sum "$p" | cut -d' ' -f1)" \
                "$(stat -c '%a' "$p")" "$q"
        done
    } | sort -u
}
# ckey <relpath> <abs-file> — the gate cache key. Uses $HS_FP_SALT (set by
#   hs_fingerprint), include_shas, oracle_shas and flags_for, so an entry whose
#   included fragments or oracle scripts changed, a flagged entry and an entry
#   produced by a different oracle binary are all a MISS. KEY FORMAT (shared by
#   corpus_file_diff.sh, wf_gate.sh, pretty_gate.sh, triage_diff_vs_hs.sh,
#   and scripts/migrate_hs_cache_fp.sh which rekeyed older entries onto it):
#     <sha256(theory)>[__i<12 hex of sha256(include shas)>]
#                     [__o<12 hex of sha256(oracle shas)>]
#                     [__f<12 hex of sha256(flags)>]__b<12 hex of sha256(HS_FP)>
ckey() {
    local h fl inc ora; h=$(sha256sum "$2" | cut -d' ' -f1); fl=$(flags_for "$1")
    inc=$(include_shas "$2")
    ora=$(oracle_shas "$2" "$fl")
    if [ -n "$inc" ]; then h="${h}__i$(printf '%s' "$inc" | sha256sum | cut -c1-12)"; fi
    if [ -n "$ora" ]; then h="${h}__o$(printf '%s' "$ora" | sha256sum | cut -c1-12)"; fi
    if [ -n "$fl" ]; then h="${h}__f$(printf '%s' "$fl" | sha256sum | cut -c1-12)"; fi
    printf '%s__b%s' "$h" "$HS_FP_SALT"
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
    for c in "$repo"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$repo"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        if [ -x "$c" ]; then printf '%s\n' "$c"; return 0; fi
    done
    main=$(git -C "$repo" worktree list --porcelain 2>/dev/null \
        | awk '/^worktree/{print $2; exit}')
    if [ -n "$main" ] && [ "$main" != "$repo" ]; then
        for c in "$main"/tamarin-prover-testing/.stack-work/install/*/*/*/bin/tamarin-prover \
                 "$main"/tamarin-prover-testing/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
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
# oracle_revision <hs-bin> <maude>
#   Print the revision token embedded in an oracle binary. Development builds
#   may append a dirty-worktree note before the branch comma, so parse the
#   first token after the label rather than everything before that comma.
oracle_revision() {
    timeout 60 "$1" --with-maude="$2" --version 2>/dev/null \
        | sed -n 's/^Git revision: \([^[:space:],]*\).*/\1/p'
}

# oracle_rev_check <hs-bin> <maude> <repo-root>
#   The oracle IS the specification, so it has to be the build of the submodule
#   pin: an oracle from another revision compares the port against a different
#   upstream and reports the result as parity. Skipped when the gitlink cannot
#   be read or the binary prints no `Git revision:` line at all, since neither
#   absence is evidence of a mismatch; ALLOW_ORACLE_REV_MISMATCH=1 for a
#   deliberate cross-revision comparison. A binary built outside a git checkout
#   stamps the literal `UNKNOWN`, and that IS evidence: the oracle is built
#   from the pinned worktree, so anything unstamped is a packaged release
#   rather than the specification. `--version` prints the `Git revision:` line
#   as part of `ensureMaudeAndGetVersion`'s block (Console.hs:333-338), so the
#   probe needs `--with-maude=<maude>`: without it the probe resolves `maude`
#   on PATH, dies before the line, and the guard would skip on exactly the
#   boxes that keep maude off PATH.
oracle_rev_check() {
    local hs=$1 maude=$2 repo=$3 pin binrev
    pin=$(git -C "$repo" rev-parse :tamarin-prover 2>/dev/null) || pin=
    binrev=$(oracle_revision "$hs" "$maude")
    if [ -n "$pin" ] && [ -n "$binrev" ] && [ "$pin" != "$binrev" ]; then
        echo "ERROR: oracle '$hs' is revision $binrev but the submodule pin is $pin" \
             "— it would certify the port against the wrong upstream" \
             "(rebuild with ./setup.sh testing, or ALLOW_ORACLE_REV_MISMATCH=1)" >&2
        [ "${ALLOW_ORACLE_REV_MISMATCH:-0}" = 1 ] || exit 2
    fi
}

# rs_stale_check [rs-bin] [repo-root]  (defaults: $RS_BIN, $REPO)
#   Refuse to run when the release binary predates the sources — a stale binary
#   silently certifies the wrong code (ALLOW_STALE_BIN=1 overrides).
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
    local bin=${1:-$RS_BIN} repo=${2:-$REPO} newest dep p
    newest=$(find "$repo/crates" \( -name '*.rs' -o -name 'Cargo.toml' \) -newer "$bin" -print -quit 2>/dev/null)
    # The workspace root manifests are inputs too: a dependency bump there
    # rebuilds the binary but leaves every file under crates/ untouched.
    [ -n "$newest" ] || newest=$(find "$repo/Cargo.toml" "$repo/Cargo.lock" -newer "$bin" -print -quit 2>/dev/null)
    dep="$bin.d"
    if [ -z "$newest" ] && [ -f "$dep" ]; then
        while read -r p; do
            case $p in '' | */.git/*) continue ;; esac
            if [ -e "$p" ] && [ "$p" -nt "$bin" ]; then newest=$p; break; fi
        done < <(head -1 "$dep" | cut -d: -f2- | tr ' ' '\n')
    fi
    if [ -n "$newest" ]; then
        echo "ERROR: $bin is older than $newest — rebuild first (ALLOW_STALE_BIN=1 to override)" >&2
        [ "${ALLOW_STALE_BIN:-0}" = 1 ] || exit 2
    fi
}
