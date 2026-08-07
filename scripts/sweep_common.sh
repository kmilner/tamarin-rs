# Shared helpers for the flag-parity sweeps (pe_sweep.sh, module_sweep.sh,
# json_sweep.sh). Source me. Provides:
#   grun         — OOM-guarded, memory-capped, time-capped run
#   norm         — blank the volatile banner lines (same set as corpus_file_diff.sh)
#   nerr         — collapse the duplicated [Open Chains] stderr line
#   hs_run       — run the Haskell oracle through a content-keyed result cache
#   family_list  — resolve a *_family.txt subset against a base directory
#   sweep_export — export the helpers + environment the xargs children need
#   sweep_retry  — serial re-run of the ERROR rows at a higher cap
#   rs_stale_check — refuse to sweep with a release binary older than the sources
#   sweep_banner / sweep_finish — denominator + fingerprints up front, ledger
#                  application + summary + DONE sentinel at the end
#
# The oracle cache (HS_CACHE, default scripts/.hs_sweep_cache/, gitignored)
# keys on sha256(theory) + the sweep-provided flag tag + the oracle binary
# fingerprint + the maude path — oracle output is deterministic for that key,
# so iterating on the Rust side never re-runs the oracle. Timeouts are cached
# WITH their cap: a timeout at cap T satisfies any request with cap <= T
# (it would time out again), while a finished run satisfies every cap.
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HS_BIN=${HS_PATH:-$(find "$REPO/tamarin-prover-testing/.stack-work/install" -name tamarin-prover -type f 2>/dev/null | head -1)}
MAUDE=${MAUDE_PATH:-/home/linuxbrew/.linuxbrew/bin/maude}
EXAMPLES=$REPO/tamarin-prover/examples
CSR=$REPO/tamarin-prover/case-studies-regression
RS_BIN=${RS_BIN:-$REPO/target/release/tamarin-rs}
TIMEOUT=${TIMEOUT:-120}
JOBS=${JOBS:-3}
HS_CACHE=${HS_CACHE:-$REPO/scripts/.hs_sweep_cache}
LEDGER=$REPO/scripts/sweep_expected.tsv

grun() { ( echo 1000 > /proc/self/oom_score_adj; ulimit -v 16777216; timeout "$TIMEOUT" "$@" ); }

# Blank the volatile lines (same set as scripts/corpus_file_diff.sh).
norm() { sed -e 's/^Git revision:.*/GITREV/' -e 's/^Compiled at:.*/COMPILED/' \
             -e 's/^[[:space:]]*analyzed:.*/ANALYZED/' -e 's/^[[:space:]]*processing time:.*/PTIME/'; }

# Known pre-existing divergence (NOT any flag's): RS's derivation-check stage
# emits the "[Open Chains] Too many chain constraints" warning twice where HS
# emits it once (visible at the plain path too). Collapse consecutive
# duplicates of that exact line on both sides.
nerr() { awk '!(/^\[Open Chains\] Too many chain constraints/ && $0 == prev) { print } { prev = $0 }'; }

# Oracle-binary fingerprint, part of every cache key. Loop-invariant, so it is
# taken once here rather than per cached lookup.
HS_FP=$(stat -c '%s.%Y' "$HS_BIN")

# hs_run <workdir> <theory> <tag> <flag...>
#   Executes  grun $HS_BIN --with-maude=$MAUDE <flag...> <theory>
#   with stdout -> $workdir/hs.out, stderr -> $workdir/hs.err; any artifact the
#   flags write as $workdir/hs.* (e.g. hs.json) is cached alongside. Returns the
#   run's exit code. <tag> must uniquely encode the flag SEMANTICS while
#   excluding volatile paths (pass e.g. "json+dot", not the tmp-dir flags).
hs_run() {
  local wd=$1 f=$2 tag=$3; shift 3
  local key
  key=$( { sha256sum "$f" | cut -d' ' -f1; echo "$tag"; echo "$HS_FP"; echo "$MAUDE"; } | sha256sum | cut -d' ' -f1 )
  local dir="$HS_CACHE/${key:0:2}/$key"
  if [ -f "$dir/rc" ]; then
    local crc ccap
    crc=$(cat "$dir/rc"); ccap=$(cat "$dir/cap")
    if [ "$crc" -lt 124 ] || [ "$ccap" -ge "$TIMEOUT" ]; then
      cp "$dir"/hs.* "$wd/" && return "$crc"
    fi
  fi
  grun "$HS_BIN" --with-maude="$MAUDE" "$@" "$f" > "$wd/hs.out" 2> "$wd/hs.err"
  local rc=$?
  local tmp="$dir.tmp.$$"
  mkdir -p "$tmp" && cp "$wd"/hs.* "$tmp/" \
    && echo "$TIMEOUT" > "$tmp/cap" && echo "$rc" > "$tmp/rc" \
    && mkdir -p "$(dirname "$dir")" && rm -rf "$dir" && mv "$tmp" "$dir"
  return "$rc"
}

# family_list <family-file> <base-dir>
#   The FAMILY=1 subset: strip comments/blank lines, resolve each entry against
#   <base-dir>, and warn (to stderr) about entries that no longer exist rather
#   than silently shrinking the denominator.
family_list() {
  local list=$1 base=$2 rel f
  while read -r rel; do
    f="$base/$rel"
    if [ -f "$f" ]; then echo "$f"; else echo "WARNING: family entry missing: $f" >&2; fi
  done < <(sed 's/#.*//;/^\s*$/d' "$list")
}

# sweep_export [extra function names...]
#   Hand the helpers and settings to the `bash -c 'one ...'` children xargs
#   spawns; a sweep with its own extra helper passes its name.
sweep_export() {
  export -f one grun norm nerr hs_run "$@"
  export HS_BIN RS_BIN MAUDE OUT TIMEOUT HS_CACHE HS_FP
}

# sweep_retry <out.tsv> <status-col> <retry-cap>
#   Heavy files are load-sensitive, so the parallel pass's ERROR rows get one
#   serial re-run at the higher cap; the retry rows REPLACE the originals. The
#   oracle cache remembers a timeout together with its cap, so a genuinely
#   hopeless file burns the oracle once ever.
#   `one` is re-invoked with the row's key fields (everything left of the
#   status column) plus a trailing `retry` detail tag — sweeps that take no tag
#   ignore the extra argument.
sweep_retry() {
  local out=$1 col=$2 cap=$3 rows fields
  rows=$(awk -F'\t' -v col="$col" '$col == "ERROR"' "$out")
  [ -n "$rows" ] || return 0
  echo "== retrying $(grep -c . <<< "$rows") ERROR rows serially at TIMEOUT=$cap =="
  awk -F'\t' -v col="$col" '$col != "ERROR"' "$out" > "$out.keep" && mv "$out.keep" "$out"
  while IFS=$'\t' read -r -a fields; do
    TIMEOUT=$cap one "${fields[@]:0:$((col - 1))}" retry
  done <<< "$rows"
}

# Refuse to sweep when target/release/tamarin-rs predates the sources — a stale
# binary silently certifies the wrong code (ALLOW_STALE_BIN=1 overrides).
rs_stale_check() {
  local newest
  newest=$(find "$REPO/crates" \( -name '*.rs' -o -name 'Cargo.toml' \) -newer "$RS_BIN" -print -quit 2>/dev/null)
  if [ -n "$newest" ]; then
    echo "ERROR: $RS_BIN is older than $newest — rebuild first (ALLOW_STALE_BIN=1 to override)" >&2
    [ "${ALLOW_STALE_BIN:-0}" = 1 ] || exit 2
  fi
}

# sweep_banner <name> <total>
sweep_banner() {
  echo "== $1: $2 items | JOBS=$JOBS TIMEOUT=$TIMEOUT =="
  echo "== rs: $(git -C "$REPO" describe --always --dirty 2>/dev/null) rs_bin_mtime=$(stat -c %Y "$RS_BIN") hs_bin=$HS_FP =="
}

# apply_ledger <out.tsv> <sweep-name> <status-col> [sub-unit-col]
#   Rewrites DIFF/ERROR rows whose file has a ledger entry for this sweep to
#   status LEDGERED (class appended); prints LEDGER-STALE for entries none of
#   whose rows diverged — the entry should then be removed.
#   The row key is the file path made relative to tamarin-prover/, matched
#   EXACTLY against the ledger's path column. A ledger entry may narrow itself
#   to one sub-unit (the module of a module-sweep row) via its 5th column; an
#   entry without one covers every row of the file.
apply_ledger() {
  local out=$1 sweep=$2 col=$3 unitcol=${4:-0}
  [ -f "$LEDGER" ] || return 0
  awk -F'\t' -v OFS='\t' -v sweep="$sweep" -v col="$col" -v unitcol="$unitcol" -v ledger="$LEDGER" '
    BEGIN {
      while ((getline line < ledger) > 0) {
        if (line ~ /^#/ || line ~ /^[[:space:]]*$/) continue
        split(line, a, "\t")
        if (a[1] == sweep) { cls[a[2] SUBSEP a[5]] = a[3] }
      }
    }
    {
      rel = $1
      sub(/^.*\/tamarin-prover\//, "", rel)
      key = rel SUBSEP ""
      if (!(key in cls) && unitcol > 0) key = rel SUBSEP $unitcol
      if (key in cls) {
        if ($col == "DIFF" || $col == "ERROR") { $col = "LEDGERED"; $NF = $NF " [" cls[key] "]"; hit[key] = 1 }
        else if ($col == "OK") ok[key] = 1
      }
      print
    }
    END {
      for (k in ok) {
        if (k in hit) continue
        split(k, kk, SUBSEP)
        print "LEDGER-STALE: " sweep " " kk[1] (kk[2] == "" ? "" : " " kk[2]) " came back OK — drop its entry" > "/dev/stderr"
      }
    }
  ' "$out" > "$out.ledgered" && mv "$out.ledgered" "$out"
}

# sweep_finish <out.tsv> <sweep-name> <status-col> [sub-unit-col]
sweep_finish() {
  local out=$1 sweep=$2 col=$3 unitcol=${4:-0}
  apply_ledger "$out" "$sweep" "$col" "$unitcol"
  echo "== summary =="
  cut -f"$col" "$out" | sort | uniq -c
  awk -F'\t' -v col="$col" '$col == "DIFF" || $col == "ERROR"' "$out" | head -40
  echo "== DONE $sweep $(date -u +%FT%TZ) =="
}
