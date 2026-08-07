# Shared helpers for the flag-parity sweeps (pe_sweep.sh, module_sweep.sh,
# json_sweep.sh). Source me. Provides:
#   grun         — OOM-guarded, memory-capped, time-capped run
#   norm         — blank the volatile banner lines (same set as corpus_file_diff.sh)
#   hs_run       — run the Haskell oracle through a content-keyed result cache
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

hs_fingerprint() { stat -c '%s.%Y' "$HS_BIN"; }

# hs_run <workdir> <theory> <tag> <flag...>
#   Executes  grun $HS_BIN --with-maude=$MAUDE <flag...> <theory>
#   with stdout -> $workdir/hs.out, stderr -> $workdir/hs.err; any artifact the
#   flags write as $workdir/hs.* (e.g. hs.json) is cached alongside. Returns the
#   run's exit code. <tag> must uniquely encode the flag SEMANTICS while
#   excluding volatile paths (pass e.g. "json+dot", not the tmp-dir flags).
hs_run() {
  local wd=$1 f=$2 tag=$3; shift 3
  local key
  key=$( { sha256sum "$f" | cut -d' ' -f1; echo "$tag"; hs_fingerprint; echo "$MAUDE"; } | sha256sum | cut -d' ' -f1 )
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
  echo "== rs: $(git -C "$REPO" describe --always --dirty 2>/dev/null) rs_bin_mtime=$(stat -c %Y "$RS_BIN") hs_bin=$(hs_fingerprint) =="
}

# apply_ledger <out.tsv> <sweep-name> <status-col>
#   Rewrites DIFF/ERROR rows whose file has a ledger entry for this sweep to
#   status LEDGERED (class appended); prints LEDGER-STALE for ledgered files
#   that came back OK — the entry should then be removed.
apply_ledger() {
  local out=$1 sweep=$2 col=$3
  [ -f "$LEDGER" ] || return 0
  awk -F'\t' -v OFS='\t' -v sweep="$sweep" -v col="$col" -v ledger="$LEDGER" '
    BEGIN {
      while ((getline line < ledger) > 0) {
        if (line ~ /^#/ || line ~ /^[[:space:]]*$/) continue
        n = split(line, a, "\t")
        if (a[1] == sweep) { cls[a[2]] = a[3] }
      }
    }
    {
      matched = ""
      for (p in cls) if (index($1, "/tamarin-prover/" p)) { matched = p; break }
      if (matched != "") {
        seen[matched] = 1
        if ($col == "DIFF" || $col == "ERROR") { $col = "LEDGERED"; $NF = $NF " [" cls[matched] "]" }
        else if ($col == "OK") stale[matched] = 1
      }
      print
    }
    END { for (p in stale) print "LEDGER-STALE: " sweep " " p " came back OK — drop its entry" > "/dev/stderr" }
  ' "$out" > "$out.ledgered" && mv "$out.ledgered" "$out"
}

# sweep_finish <out.tsv> <sweep-name> <status-col>
sweep_finish() {
  local out=$1 sweep=$2 col=$3
  apply_ledger "$out" "$sweep" "$col"
  echo "== summary =="
  cut -f"$col" "$out" | sort | uniq -c
  awk -F'\t' -v col="$col" '$col == "DIFF" || $col == "ERROR"' "$out" | head -40
  echo "== DONE $sweep $(date -u +%FT%TZ) =="
}
