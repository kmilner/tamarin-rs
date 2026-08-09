# Shared helpers for the flag-parity sweeps (pe_sweep.sh, module_sweep.sh,
# json_sweep.sh). Source me. Provides:
#   grun         — OOM-guarded, memory-capped, time-capped run
#   norm         — blank the volatile banner lines (same set as corpus_file_diff.sh)
#   nerr         — collapse the duplicated [Open Chains] stderr line
#   io_diff      — first of stdout/stderr that differs after normalization
#   infra_abort / nocompare_check — detect a row that compared NOTHING
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

# Normalize the two known pre-existing stderr divergences (NEITHER is any
# flag's — both reproduce on a plain `tamarin-prover <file>` run, and both are
# byte-identical between the current binary and a pre-branch build):
#
#   [Open Chains]        RS's derivation-check stage emits the "Too many chain
#                        constraints" warning twice where HS emits it once;
#                        consecutive duplicates of that exact line collapse.
#   [Saturating Sources] HS traces saturation progress on every CLI close
#                        (TheoryLoader closes with showSaturation = True), while
#                        RS gates the trace on a process-global that only the
#                        --precompute-only path sets; where RS does trace, it
#                        produces 2 sequences to HS's 4 (see run.rs's note on
#                        the redundant auto-sources closes). 282 of the 372
#                        case-studies-regression theories differ by these lines
#                        alone.
#
# Dropping them is the only way the stderr axis can police ANYTHING else: left
# in, the class alone paints the corpus red and a genuinely new warning hides
# in the noise. It is a real port gap, not an accepted divergence — closing it
# retires this filter.
nerr() {
  awk '!(/^\[Open Chains\] Too many chain constraints/ && $0 == prev) { print } { prev = $0 }' \
    | grep -v '^\[Saturating Sources\]'
}

# io_diff <workdir>
#   Echoes the first of stdout/stderr that differs between <workdir>/hs.* and
#   <workdir>/rs.* after normalization, and returns 1; returns 0 (silently)
#   when both match.
io_diff() {
  local d=$1
  if ! diff -q <(norm < "$d/hs.out") <(norm < "$d/rs.out") >/dev/null; then echo stdout; return 1; fi
  if ! diff -q <(norm < "$d/hs.err" | nerr) <(norm < "$d/rs.err" | nerr) >/dev/null; then echo stderr; return 1; fi
  return 0
}

# ---------------------------------------------------------------------------
# NO-COMPARE — the verdict for a row that compared nothing.
#
# Every sweep decides parity by pitting two runs against each other, so any
# condition that stops BOTH runs before they analyse the theory makes them
# agree for free: identical (empty) stdout, identical abort stderr, identical
# rc. That reads as OK while certifying nothing, which is worse than a DIFF —
# a DIFF gets looked at. Such rows get status NO-COMPARE, which apply_ledger
# refuses to convert to LEDGERED (only DIFF/ERROR are ledgerable) and
# sweep_finish counts as a failure in the summary, the DONE sentinel and the
# exit code.
#
# The two vacuity families the sweeps can hit, both detected by
# nocompare_check:
#   infra-abort  the environment failed, not the theory — an unusable maude
#                (ensureMaude's abort or its "executable not found / does not
#                work" report) or a theory file that could not be opened. Both
#                binaries emit the SAME text for these, so they are pure
#                false-green fuel. Flagged on EITHER side: a run that never
#                loaded the theory has nothing to say about the other's output.
#   no-analysis  both sides exited 0 having produced no artifact at all, so
#                comparing the artifacts compared two absences.
# A timeout/kill is the third way to compare nothing; the sweeps already fence
# that off as ERROR (and its capacity/hs-timeout ledger classes) before any
# verdict is reached, so it never reaches this helper.
# ---------------------------------------------------------------------------

# infra_abort <stderr-file>
#   True when the run died of its environment. Anchored patterns only: the
#   maude report lines are emitted verbatim by both binaries, and the file
#   error is the top-level `tamarin-prover: <path>: ...` abort (a theory's own
#   oracle can mention an unopenable file mid-run without aborting).
infra_abort() {
  local err=$1
  [ -f "$err" ] || return 1
  grep -qE "^tamarin-prover: Maude is not installed\.|\
^ Please install one of the following versions of Maude:|\
^tamarin-prover: .*: (openFile|hGetContents): " "$err"
}

# nocompare_check <hs-rc> <rs-rc> <hs.err> <rs.err> [artifact...]
#   Echoes why the row's verdict would be vacuous and returns 0; returns 1 when
#   the two sides really did produce something to compare. The artifacts are
#   the files this sweep's OK rests on (stdout, exported json/dot).
nocompare_check() {
  local hrc=$1 rrc=$2 herr=$3 rerr=$4; shift 4
  local sides='' a
  infra_abort "$herr" && sides=hs
  infra_abort "$rerr" && sides="${sides:+$sides+}rs"
  if [ -n "$sides" ]; then
    echo "infra-abort $sides: environment failed before the theory was analysed (rc hs=$hrc rs=$rrc)"
    return 0
  fi
  if [ "$hrc" -eq 0 ] && [ "$rrc" -eq 0 ] && [ $# -gt 0 ]; then
    for a; do [ -s "$a" ] && return 1; done
    echo "no-analysis: rc 0 on both sides with every compared artifact empty"
    return 0
  fi
  return 1
}

# sweep_preflight — refuse to sweep unless both sides can actually run.
#
# A broken maude is the silent killer: `ensureMaude` aborts on BOTH sides with
# byte-identical stderr and the same rc, every row compares equal, and the
# sweep reports 100% OK without having compared a single theory. Verified:
# with MAUDE_PATH=/nonexistent/maude the pe rows come back OK. A missing
# oracle or RS binary is the same class of false green (and `find -newer`
# cannot see a binary that is not there at all). All three are hard errors —
# there is no ALLOW_ override, because none of them leaves anything to compare.
# Run at source time so no sweep can forget it.
sweep_preflight() {
  local v
  if [ -z "$HS_BIN" ] || [ ! -x "$HS_BIN" ]; then
    echo "ERROR: no HS oracle binary (HS_PATH=${HS_PATH:-unset}, resolved '$HS_BIN')" >&2
    exit 2
  fi
  if [ ! -x "$RS_BIN" ]; then
    echo "ERROR: RS binary '$RS_BIN' is missing or not executable — build it first" >&2
    exit 2
  fi
  if [ "$(readlink -f "$HS_BIN")" = "$(readlink -f "$RS_BIN")" ]; then
    echo "ERROR: HS_PATH and RS_BIN resolve to the same binary ('$HS_BIN')" \
         "— every row would be a binary agreeing with itself" >&2
    exit 2
  fi
  if [ ! -x "$MAUDE" ]; then
    echo "ERROR: maude '$MAUDE' is missing or not executable — both sides would abort" \
         "identically and EVERY row would read OK (set MAUDE_PATH)" >&2
    exit 2
  fi
  v=$("$MAUDE" --version 2>/dev/null) || v=
  if [ -z "$v" ]; then
    echo "ERROR: '$MAUDE --version' produced nothing — that is not a working maude" >&2
    exit 2
  fi
}
sweep_preflight

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
      # A cached infrastructure abort certifies nothing about the theory and
      # would keep doing so after the environment is repaired: drop it and
      # re-run rather than serving it forever.
      if cp "$dir"/hs.* "$wd/"; then
        if infra_abort "$wd/hs.err"; then rm -rf "$dir"; else return "$crc"; fi
      fi
    fi
  fi
  grun "$HS_BIN" --with-maude="$MAUDE" "$@" "$f" > "$wd/hs.out" 2> "$wd/hs.err"
  local rc=$?
  # Same reason in the other direction: an abort is a property of this
  # environment, so storing it would poison every later sweep at this key.
  infra_abort "$wd/hs.err" && return "$rc"
  local tmp="$dir.tmp.$$"
  mkdir -p "$tmp" && cp "$wd"/hs.* "$tmp/" \
    && echo "$TIMEOUT" > "$tmp/cap" && echo "$rc" > "$tmp/rc" \
    && mkdir -p "$(dirname "$dir")" && rm -rf "$dir" && mv "$tmp" "$dir"
  return "$rc"
}

# family_list <family-file> <base-dir>
#   The FAMILY=1 subset: strip comments/blank lines and resolve each entry
#   against <base-dir>. An entry that no longer exists is fatal, not a warning:
#   the family is one representative per divergence class, so a vanished entry
#   silently shrinks the denominator and retires a class nobody checks again.
#   Callers run this inside a command substitution, so they must test its
#   status (`LIST=$(list_files) || exit 2`).
family_list() {
  local list=$1 base=$2 rel f missing=0
  while read -r rel; do
    f="$base/$rel"
    if [ -f "$f" ]; then echo "$f"
    else echo "ERROR: family entry missing: $f" >&2; missing=$((missing + 1)); fi
  done < <(sed 's/#.*//;/^\s*$/d' "$list")
  if [ "$missing" -gt 0 ]; then
    echo "ERROR: $missing entry/entries of $list no longer exist — fix the family list" >&2
    exit 2
  fi
}

# sweep_export [extra function names...]
#   Hand the helpers and settings to the `bash -c 'one ...'` children xargs
#   spawns; a sweep with its own extra helper passes its name.
sweep_export() {
  export -f one grun norm nerr io_diff infra_abort nocompare_check hs_run "$@"
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
  # `one` runs children on the loop's stdin; give them /dev/null instead, so a
  # child that reads stdin cannot swallow the remaining rows and silently
  # shrink the retry set.
  while IFS=$'\t' read -r -a fields; do
    TIMEOUT=$cap one "${fields[@]:0:$((col - 1))}" retry < /dev/null
  done <<< "$rows"
}

# Refuse to sweep when target/release/tamarin-rs predates the sources — a stale
# binary silently certifies the wrong code (ALLOW_STALE_BIN=1 overrides).
rs_stale_check() {
  local newest
  newest=$(find "$REPO/crates" \( -name '*.rs' -o -name 'Cargo.toml' \) -newer "$RS_BIN" -print -quit 2>/dev/null)
  # The workspace root manifests are inputs too: a dependency bump there
  # rebuilds the binary but leaves every file under crates/ untouched.
  [ -n "$newest" ] || newest=$(find "$REPO/Cargo.toml" "$REPO/Cargo.lock" -newer "$RS_BIN" -print -quit 2>/dev/null)
  if [ -n "$newest" ]; then
    echo "ERROR: $RS_BIN is older than $newest — rebuild first (ALLOW_STALE_BIN=1 to override)" >&2
    [ "${ALLOW_STALE_BIN:-0}" = 1 ] || exit 2
  fi
}

# sweep_banner <name> <total>
#   Records the denominator for sweep_finish's row-count check. An empty
#   corpus is the whole-sweep form of NO-COMPARE — zero rows, zero DIFFs, a
#   summary that looks perfect — so it aborts here.
sweep_banner() {
  if [ "$2" -le 0 ]; then
    echo "ERROR: $1 has nothing to sweep — the file list resolved to 0 items" >&2
    exit 2
  fi
  SWEEP_TOTAL=$2
  echo "== $1: $2 items | JOBS=$JOBS TIMEOUT=$TIMEOUT =="
  echo "== rs: $(git -C "$REPO" describe --always --dirty 2>/dev/null) rs_bin_mtime=$(stat -c %Y "$RS_BIN") hs_bin=$HS_FP =="
}

# apply_ledger <out.tsv> <sweep-name> <status-col> [sub-unit-col]
#   Rewrites DIFF/ERROR rows whose file has a ledger entry for this sweep to
#   status LEDGERED (class appended); prints LEDGER-STALE for entries none of
#   whose rows diverged — the entry should then be removed. NO-COMPARE is
#   deliberately not ledgerable: a ledger entry documents a divergence that WAS
#   observed, and a row that observed nothing cannot be one.
#   The row key is the file path made relative to tamarin-prover/, matched
#   EXACTLY against the ledger's path column. A ledger entry may narrow itself
#   to one sub-unit (the module of a module-sweep row) via its 5th column; an
#   entry without one covers every row of the file.
#   A 6th column narrows further, to the SYMPTOM: the row's detail (its last
#   field — `stderr`, `json`, `dot-labels`, …) must equal it. Without one an
#   entry excuses whatever goes wrong with that file, so a documented stderr
#   divergence would also swallow a brand-new json regression beside it.
#   Staleness ignores that 6th column. An OK row carries the detail `-`, which
#   matches no symptom, so gating the OK branch on it would make a
#   symptom-narrowed entry UNREPORTABLE as stale — it would sit in the ledger
#   forever, excusing a symptom the file had stopped producing. A file that
#   comes back OK produced no symptom at all, so every entry naming it is stale.
apply_ledger() {
  local out=$1 sweep=$2 col=$3 unitcol=${4:-0}
  [ -f "$LEDGER" ] || return 0
  awk -F'\t' -v OFS='\t' -v sweep="$sweep" -v col="$col" -v unitcol="$unitcol" -v ledger="$LEDGER" '
    BEGIN {
      while ((getline line < ledger) > 0) {
        if (line ~ /^#/ || line ~ /^[[:space:]]*$/) continue
        split(line, a, "\t")
        if (a[1] == sweep) { cls[a[2] SUBSEP a[5]] = a[3]; det[a[2] SUBSEP a[5]] = a[6] }
      }
    }
    {
      rel = $1
      sub(/^.*\/tamarin-prover\//, "", rel)
      key = rel SUBSEP ""
      if (!(key in cls) && unitcol > 0) key = rel SUBSEP $unitcol
      if (key in cls) {
        if (($col == "DIFF" || $col == "ERROR") && (det[key] == "" || det[key] == $NF)) {
          $col = "LEDGERED"; $NF = $NF " [" cls[key] "]"; hit[key] = 1
        } else if ($col == "OK") ok[key] = 1
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
#   Returns nonzero — and says so in the DONE sentinel — when the run proved
#   nothing: NO-COMPARE rows, or rows that never landed at all (a child that
#   died before appending, an xargs that never ran, a retry that dropped its
#   row). Both are silent in a plain status histogram, which is exactly how a
#   sweep gets to look green without having compared anything.
sweep_finish() {
  local out=$1 sweep=$2 col=$3 unitcol=${4:-0} nc rows total bad='' bd
  apply_ledger "$out" "$sweep" "$col" "$unitcol"
  echo "== summary =="
  cut -f"$col" "$out" | sort | uniq -c
  awk -F'\t' -v col="$col" '$col == "DIFF" || $col == "ERROR"' "$out" | head -40
  nc=$(awk -F'\t' -v col="$col" '$col == "NO-COMPARE"' "$out" | grep -c .)
  rows=$(grep -c . "$out")
  total=${SWEEP_TOTAL:-$rows}
  # A row still reading DIFF/ERROR after the ledger pass is an undocumented
  # divergence, so the sentinel must not read OK above a list of them.
  bd=$(awk -F'\t' -v col="$col" '$col == "DIFF" || $col == "ERROR"' "$out" | grep -c .)
  [ "$bd" -gt 0 ] && bad="DIFF/ERROR=$bd"
  if [ "$nc" -gt 0 ]; then
    bad="${bad:+$bad }NO-COMPARE=$nc"
    echo "== $nc row(s) compared NOTHING — these are failures, not agreement =="
    awk -F'\t' -v col="$col" '$col == "NO-COMPARE"' "$out" | head -40
  fi
  if [ "$rows" -ne "$total" ]; then
    bad="${bad:+$bad }ROW-COUNT=$rows/$total"
    echo "== $rows rows for $total items — the missing ones were never compared =="
  fi
  echo "== DONE $sweep $(date -u +%FT%TZ) verdict=${bad:-OK} =="
  [ -z "$bad" ]
}
