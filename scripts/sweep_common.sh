# Shared helpers for the flag-parity sweeps (pe_sweep.sh, module_sweep.sh,
# json_sweep.sh). Source me. Provides:
#   grun         — OOM-guarded, memory-capped, time-capped run
#   norm         — blank the volatile banner lines (same set as corpus_file_diff.sh)
#   nerr         — collapse the duplicated [Open Chains] stderr line
#   io_diff      — first of stdout/stderr that differs after normalization
#   row          — append one tab-separated row to $OUT
#   infra_abort / nocompare_check — detect a row that compared NOTHING
#   hs_run       — run the Haskell oracle through a content-keyed result cache
#   sweep_one    — the standard per-item body: oracle vs port on one flag set
#                  (pe_sweep/module_sweep; json_sweep's artifact comparisons
#                  keep their own body)
#   list_lines / resolve_list — data lines of a path list, resolved against a
#                  base directory (the corpora and the *_family.txt subsets)
#   sweep_out    — resolve $OUT against a per-sweep default, create its directory
#   sweep_export — export the helpers + environment the xargs children need
#   sweep_retry  — serial re-run of the ERROR rows at RETRY_TIMEOUT
#   sweep_banner / sweep_finish — denominator + fingerprints up front, ledger
#                  application + summary + DONE sentinel at the end
#   sweep_drive  — the whole driver tail: stale check, list, banner, parallel
#                  pass, retry, verdict
# and, via gate_common.sh (sourced below): norm, the OOM prologue grun wraps,
# include_shas (folded into hs_run's cache key below), rs_stale_check, the
# maude resolver and the oracle preflights.
#
# The oracle cache (HS_CACHE, default scripts/.hs_sweep_cache/, gitignored)
# keys on sha256(theory) + the sweep-provided flag tag + the oracle binary
# fingerprint + the maude path — oracle output is deterministic for that key,
# so iterating on the Rust side never re-runs the oracle. Timeouts are cached
# WITH their cap: a timeout at cap T satisfies any request with cap <= T
# (it would time out again), while a finished run satisfies every cap.
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
[ -r "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh" ] || { echo "sweep_common: missing $(dirname "${BASH_SOURCE[0]}")/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$(dirname "${BASH_SOURCE[0]}")/gate_common.sh"
HS_BIN=${HS_PATH:-$(find "$REPO/tamarin-prover-testing/.stack-work/install" -name tamarin-prover -type f 2>/dev/null | head -1)}
MAUDE=$(resolve_maude) || exit 2
EXAMPLES=$REPO/tamarin-prover/examples
CSR=$REPO/tamarin-prover/case-studies-regression
# RS_PATH is the spelling the other gates (corpus_file_diff.sh, pretty_gate.sh)
# use, so it is honoured here too: a sweep that ignored it would quietly certify
# target/release while the caller believed it had swapped the binary.
RS_BIN=${RS_BIN:-${RS_PATH:-$REPO/target/release/tamarin-rs}}
TIMEOUT=${TIMEOUT:-120}
RETRY_TIMEOUT=${RETRY_TIMEOUT:-600}
JOBS=${JOBS:-3}
HS_CACHE=${HS_CACHE:-$REPO/scripts/.hs_sweep_cache}
# Overridable so the ledger machinery can be exercised against a mutated copy
# without editing the real one.
LEDGER=${LEDGER:-$REPO/scripts/sweep_expected.tsv}

# Per-run guard: gate_common's OOM prologue at the sweeps' 16 GiB cap, inside
# a subshell so each prover invocation carries its own ceiling.
grun() { ( oom_prologue 16777216; timeout "$TIMEOUT" "$@" ); }

# row <field...> — append one tab-separated row to $OUT. One write per row, so
# the parallel children's appends interleave by line rather than mid-field.
row() { local IFS=$'\t'; printf '%s\n' "$*" >> "$OUT"; }

# norm (gate_common.sh): BLANK the volatile lines to placeholders — the same
# four lines the gates' strip_env deletes, kept as position evidence here
# because nonempty_compared distinguishes blanked from deleted.

# Normalize the two known pre-existing stderr divergences (NEITHER is any
# flag's — both reproduce on a plain `tamarin-prover <file>` run, and both are
# byte-identical between the current binary and a pre-branch build):
#
#   [Open Chains]        RS's derivation-check stage emits the "Too many chain
#                        constraints" warning twice where HS emits it once;
#                        consecutive duplicates of that exact line collapse.
#   [Saturating Sources] Both sides trace saturation progress on every CLI
#                        close (showSaturation = True), but the SEQUENCE COUNTS
#                        still differ structurally: HS traces once per force of
#                        a ClosedRuleCache thunk, RS once per saturation it
#                        actually runs — one extra sequence on a theory with a
#                        [sources] lemma, one where HS emits none on a theory
#                        whose proofs never consult a source case, and counts
#                        differing both ways under --auto-sources (run.rs's
#                        close_translated_theory enumerates all three). 282 of
#                        the 372 case-studies-regression theories differ by
#                        these lines alone.
#
# Dropping them is the only way the stderr axis can police ANYTHING else: left
# in, the class alone paints the corpus red and a genuinely new warning hides
# in the noise. It is a real port gap, not an accepted divergence — closing it
# retires this filter.
#
# What that costs, measured by injecting lines into the RS side: a stderr line
# beginning "[Saturating Sources]" is invisible to every sweep whatever it says,
# and so is any difference in how many times the [Open Chains] warning repeats
# CONSECUTIVELY (the ledger's stderr-open-chains rows are the non-consecutive
# count differences, which do still surface). Any other stderr byte is caught.
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
# The three vacuity families the sweeps can hit, all detected by
# nocompare_check:
#   infra-abort  the environment failed, not the theory — an unusable maude
#                (ensureMaude's abort or its "executable not found / does not
#                work" report) or a theory file that could not be opened. Both
#                binaries emit the SAME text for these, so they are pure
#                false-green fuel. Flagged on EITHER side: a run that never
#                loaded the theory has nothing to say about the other's output.
#   no-analysis  both sides exited 0 having produced no artifact at all, so
#                comparing the artifacts compared two absences.
#   no-output    both sides failed with the SAME nonzero rc and printed nothing
#                THAT THE VERDICT LOOKS AT. No product is written on a failure,
#                so the streams are the whole verdict; two silent failures agree
#                about nothing, and a matching rc alone is not evidence.
#                Emptiness is judged through the same filters the comparison
#                uses (see nonempty_compared): a run whose every byte is a line
#                norm blanks or nerr drops has left the verdict nothing, even
#                though the raw file is not empty.
# A timeout/kill is the fourth way to compare nothing, and the only one that is
# ledgerable. The sweeps fence it off as ERROR before this helper is reached, so
# an UNDOCUMENTED one fails the sweep exactly like any other ERROR. A DOCUMENTED
# one (the capacity/oracle-timeout ledger classes) does NOT become LEDGERED:
# apply_ledger gives it the terminal status UNCOMPARED, which sweep_finish
# reports as its own UNCOMPARED=n figure on the DONE line. Non-fatal, because
# the cap is a property of the box rather than of the port; never folded into
# the clean count, because nothing was compared.
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

# nonempty_compared <file>
#   True when <file> still carries content IN THE FORM THE VERDICT COMPARES IT.
#   io_diff pits the streams against each other through norm (and nerr for
#   stderr), so raw emptiness is the wrong question for a stream: a stderr whose
#   every line is "[Saturating Sources]" reaches io_diff empty, and two empty
#   bodies match whatever the two sides actually printed.
#   The distinction is delete vs blank. nerr DELETES its lines, leaving nothing
#   behind, so a stream made only of them is no evidence. norm BLANKS its lines
#   to placeholders (GITREV/COMPILED/ANALYZED/PTIME), which still pin that the
#   line was printed and where — weak evidence, but not none — so such a stream
#   counts as compared.
#   Exported artifacts (json/dot) are compared byte-for-byte, so for them raw
#   emptiness IS the right question.
nonempty_compared() {
  case $1 in
    *.out) [ -n "$(norm < "$1" 2>/dev/null)" ] ;;
    *.err) [ -n "$(norm < "$1" 2>/dev/null | nerr)" ] ;;
    *)     [ -s "$1" ] ;;
  esac
}

# nocompare_check <hs-rc> <rs-rc> <workdir> [product...]
#   Echoes why the row's verdict would be vacuous and returns 0; returns 1 when
#   the two sides really did produce something to compare. <workdir> holds the
#   run's hs.out/hs.err/rs.out/rs.err; the products are the documents this
#   sweep's OK rests on when the run succeeds (stdout, exported json/dot).
nocompare_check() {
  local hrc=$1 rrc=$2 wd=$3; shift 3
  local sides='' a
  infra_abort "$wd/hs.err" && sides=hs
  infra_abort "$wd/rs.err" && sides="${sides:+$sides+}rs"
  if [ -n "$sides" ]; then
    echo "infra-abort $sides: environment failed before the theory was analysed (rc hs=$hrc rs=$rrc)"
    return 0
  fi
  if [ "$hrc" -eq 0 ] && [ "$rrc" -eq 0 ] && [ $# -gt 0 ]; then
    for a; do nonempty_compared "$a" && return 1; done
    echo "no-analysis: rc 0 on both sides with every compared artifact empty"
    return 0
  fi
  # Differing rcs ARE a comparison result (the sweeps report them as DIFF), so
  # only a matching rc can be vacuous.
  if [ "$hrc" -eq "$rrc" ]; then
    for a in "$wd"/hs.out "$wd"/hs.err "$wd"/rs.out "$wd"/rs.err; do
      nonempty_compared "$a" && return 1
    done
    echo "no-output: matching rc $hrc with nothing on either side that survives normalization"
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
  # gate_common's oracle_rev_check: the oracle must be the build of the
  # submodule pin — the same policy divergence_fixtures/capture.sh enforces on
  # its captures (rationale, skip conditions and the ALLOW_ORACLE_REV_MISMATCH
  # escape hatch are documented at the definition).
  oracle_rev_check "$HS_BIN" "$MAUDE" "$REPO"
}
sweep_preflight

# sweep_preflight's source check also computes the oracle fingerprint used by
# every cache key.

# include_shas / oracle_shas come from gate_common.sh (they are part of ckey
# and of rs_ref_check.sh's ikey there too); hs_run folds them into its digest
# below, and each prints nothing when that dependency class is absent.

# hs_run <workdir> <theory> <tag> <flag...>
#   Executes  grun $HS_BIN --with-maude=$MAUDE <flag...> <theory>
#   with stdout -> $workdir/hs.out, stderr -> $workdir/hs.err; any artifact the
#   flags write as $workdir/hs.* (e.g. hs.json) is cached alongside. Returns the
#   run's exit code. <tag> must uniquely encode the flag SEMANTICS while
#   excluding volatile paths (pass e.g. "json+dot", not the tmp-dir flags).
hs_run() {
  local wd=$1 f=$2 tag=$3; shift 3
  local key legacy_key legacy_dir
  key=$( { sha256sum "$f" | cut -d' ' -f1; echo "$tag"; echo "$HS_FP"; echo "$MAUDE"
           include_shas "$f"; oracle_shas "$f" "$*"; } | sha256sum | cut -d' ' -f1 )
  local dir="$HS_CACHE/${key:0:2}/$key"
  if [ ! -f "$dir/rc" ]; then
    # Preserve the costly cache generated before hs_fingerprint switched from
    # size+mtime to binary SHA-256. This must reproduce the former key exactly,
    # including executable-oracle inputs. Compute it only on a miss: a warm
    # entry should not pay for a second dependency walk forever.
    legacy_key=$( { sha256sum "$f" | cut -d' ' -f1; echo "$tag"; echo "$HS_FP_LEGACY"; echo "$MAUDE"
                    include_shas "$f"; oracle_shas "$f" "$*"; } | sha256sum | cut -d' ' -f1 )
    legacy_dir="$HS_CACHE/${legacy_key:0:2}/$legacy_key"
    if [ -f "$legacy_dir/rc" ]; then
      local promote="$dir.promote.$$"
      mkdir -p "$(dirname "$dir")" && cp -a "$legacy_dir" "$promote" \
        && mv -T "$promote" "$dir" || rm -rf "$promote"
    fi
  fi
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

# sweep_one <file> <unit> <tag> <cache-tag> <flag...>
#   The per-item body pe_sweep.sh and module_sweep.sh carried as byte-identical
#   private copies: oracle via hs_run, port via grun, verdict via
#   nocompare_check / rc / io_diff. The varying tokens are parameters:
#     <unit>       optional extra result column between the file and the status
#                  ('' for none; module_sweep passes the -m module)
#     <tag>        optional detail suffix appended to every row ('' for none;
#                  pe_sweep passes '-' or sweep_retry's 'retry' marker — an OK
#                  row's whole detail is the tag, or '-' when there is none)
#     <cache-tag>  hs_run's flag-semantics tag
#     <flag...>    the flags both sides run under
#   json_sweep.sh's body stays its own: its verdict rests on exported
#   json/dot artifacts and a both-fail stream comparison, not this shape.
sweep_one() {
  local f=$1 unit=$2 tag=$3 ctag=$4; shift 4
  local d hrc rrc nc io
  local -a k=("$f"); [ -n "$unit" ] && k+=("$unit")
  # No tmpdir means every redirection below would target /, so bail and let
  # sweep_finish's row-count check report the row that never landed.
  d=$(mktemp -d) || return
  hs_run "$d" "$f" "$ctag" "$@"; hrc=$?
  # A broken environment is diagnosed before the cap is blamed for it: an
  # unusable maude both aborts and hangs, and "timeout" would be the wrong
  # story (and a ledgerable one).
  if infra_abort "$d/hs.err"; then row "${k[@]}" NO-COMPARE "infra-abort hs (rs not run) hs=$hrc${tag:+ $tag}"; rm -rf "$d"; return; fi
  # An oracle timeout is cached at this cap, so it comes back instantly while
  # the RS side would burn the full cap producing nothing to compare against.
  if [ "$hrc" -ge 124 ]; then row "${k[@]}" ERROR "timeout/kill hs=$hrc rs=skipped${tag:+ $tag}"; rm -rf "$d"; return; fi
  grun "$RS_BIN" --with-maude="$MAUDE" "$@" "$f" > "$d/rs.out" 2> "$d/rs.err"; rrc=$?
  if [ "$rrc" -ge 124 ]; then row "${k[@]}" ERROR "timeout/kill hs=$hrc rs=$rrc${tag:+ $tag}"
  elif nc=$(nocompare_check "$hrc" "$rrc" "$d" "$d/hs.out" "$d/rs.out"); then row "${k[@]}" NO-COMPARE "$nc${tag:+ $tag}"
  elif [ "$hrc" -ne "$rrc" ]; then row "${k[@]}" DIFF "rc hs=$hrc rs=$rrc${tag:+ $tag}"
  elif ! io=$(io_diff "$d"); then row "${k[@]}" DIFF "$io${tag:+ $tag}"
  else row "${k[@]}" OK "${tag:--}"; fi
  rm -rf "$d"
}

# list_lines <file>
#   A path list's data lines: `#` comment (whole-line or trailing) and blanks
#   removed, trailing whitespace trimmed. The trim matters — an entry followed
#   by an inline comment would otherwise keep the spaces that separated them,
#   and nothing downstream that matches a path EXACTLY (resolve_list's -f test,
#   pe_sweep's grep -vxF exclusion) would recognise it.
list_lines() { sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$1"; }

# resolve_list <list-file> <base-dir>
#   Resolve every entry of a path list against <base-dir>. An entry that no
#   longer exists is fatal, not a warning: a vanished entry silently shrinks the
#   denominator, and nothing downstream can tell a corpus that got smaller from
#   a corpus that came back clean. For the *_family.txt subsets it would also
#   retire a divergence class nobody checks again.
#   Callers run this inside a command substitution, so they must test its
#   status (`LIST=$(list_files) || exit 2`); for the same reason it has to be
#   the last stage of whatever pipeline it sits in, or its exit is swallowed.
resolve_list() {
  local list=$1 base=$2 rel f missing=0
  while read -r rel; do
    f="$base/$rel"
    if [ -f "$f" ]; then echo "$f"
    else echo "ERROR: list entry missing: $f" >&2; missing=$((missing + 1)); fi
  done < <(list_lines "$list")
  if [ "$missing" -gt 0 ]; then
    echo "ERROR: $missing entry/entries of $list no longer exist — fix the list" >&2
    exit 2
  fi
}

# sweep_out <default-path> — resolve $OUT, make sure its directory exists, and
#   prove it is writable now rather than discovering it when the first child
#   tries to append: an unwritable OUT leaves every `row` write failing into
#   stderr and the sweep reaching sweep_finish with no file at all.
sweep_out() {
  OUT=${OUT:-$1}
  mkdir -p "$(dirname "$OUT")" && : > "$OUT" || {
    echo "ERROR: cannot write OUT '$OUT' — no row of this sweep would land" >&2
    exit 2
  }
}

# sweep_export [extra function names...]
#   Hand the helpers and settings to the `bash -uc 'one ...'` children xargs
#   spawns; a sweep with its own extra helper passes its name. Anything a child
#   needs must be listed here — under the children's -u a name that was missed
#   aborts the child instead of expanding to empty, and the row it never wrote
#   turns up in sweep_finish's row-count check.
sweep_export() {
  export -f one row grun oom_prologue norm nerr io_diff infra_abort nonempty_compared \
            nocompare_check include_shas oracle_shas hs_run sweep_one "$@"
  export HS_BIN RS_BIN MAUDE OUT TIMEOUT HS_CACHE HS_FP HS_FP_LEGACY
}

# sweep_retry <out.tsv> <status-col>
#   Heavy files are load-sensitive, so the parallel pass's ERROR rows get one
#   serial re-run at RETRY_TIMEOUT; the retry rows REPLACE the originals. The
#   oracle cache remembers a timeout together with its cap, so a genuinely
#   hopeless file burns the oracle once ever.
#   `one` is re-invoked with the row's key fields (everything left of the
#   status column) plus a trailing `retry` detail tag — sweeps that take no tag
#   ignore the extra argument.
sweep_retry() {
  local out=$1 col=$2 cap=$RETRY_TIMEOUT rows fields
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

# rs_stale_check comes from gate_common.sh; called bare by the sweeps, it
# defaults to this file's $RS_BIN and $REPO.

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
#   Rewrites DIFF/ERROR rows whose file has a ledger entry for this sweep to a
#   terminal status, with the class appended to the detail. WHICH terminal
#   status depends on whether the row compared anything at all:
#     LEDGERED    a divergence was observed and is documented. Counted clean.
#     UNCOMPARED  the row compared NOTHING: a side was killed at the cap
#                 (status ERROR, or a detail whose first word is
#                 `timeout/kill`), so there is no observation for the entry to
#                 excuse — only a cost to record. sweep_finish reports these as
#                 their own UNCOMPARED=n figure instead of hiding them in the
#                 clean count, and they are deliberately not fatal: the cap is a
#                 property of the box. An UNDOCUMENTED one stays ERROR and fails
#                 the sweep, so the only way a timeout goes quiet is by being
#                 written down in the ledger.
#   NO-COMPARE is deliberately not ledgerable at all:
#   a ledger entry documents a divergence that WAS observed, and a row that
#   observed nothing cannot be one.
#   The row key is the file path made relative to tamarin-prover/, matched
#   EXACTLY against the ledger's path column. A ledger entry may narrow itself
#   to one sub-unit (the module of a module-sweep row) via its 5th column; an
#   entry without one covers every row of the file.
#   A 6th column narrows further, to the SYMPTOM: the FIRST WORD of the row's
#   detail (`stderr`, `json`, `both-fail-stdout`, …) must equal it. The rest of
#   the detail is per-row prose — rcs, the `retry` marker pe_sweep appends — so
#   matching the whole field would make the column inert wherever a sweep
#   annotates. Without a 6th column an entry excuses whatever goes wrong with
#   that file, so a documented stderr divergence would also swallow a brand-new
#   json regression beside it.
#
#   Three stderr reports keep the ledger from accumulating entries that excuse
#   nothing. All three ignore the 6th column: an OK row carries the detail `-`,
#   which matches no symptom, so gating them on it would make a
#   symptom-narrowed entry unreportable — it would sit in the ledger forever,
#   excusing a symptom the file had stopped producing.
#     LEDGER-STALE      the entry's rows all came back OK, so it documents a
#                       divergence that no longer happens.
#     LEDGER-UNMATCHED  the entry matched no row AT ALL: its file has left this
#                       sweep's corpus, or a file-wide entry for the same path
#                       shadows it. Neither state can ever produce a STALE
#                       report, so without this the entry is invisible forever.
#                       Suppressed under FAMILY=1, where almost every entry is
#                       out of scope by construction.
#     LEDGER-DUP        two entries share a (path, sub-unit) key, so only the
#                       later one is reachable.
#   All three set LEDGER_REPORTS, which sweep_finish folds into the verdict: an
#   entry that excuses nothing today is a mask waiting for the file to regress
#   under it, and a report nothing fails on is a report that stays in the
#   ledger.
apply_ledger() {
  local out=$1 sweep=$2 col=$3 unitcol=${4:-0} full=1 rep
  LEDGER_REPORTS=0
  [ -f "$LEDGER" ] || return 0
  [ "${FAMILY:-0}" = 1 ] && full=0
  rep=$(mktemp) || return 1
  awk -F'\t' -v OFS='\t' -v sweep="$sweep" -v col="$col" -v unitcol="$unitcol" \
      -v ledger="$LEDGER" -v prefix="$REPO/tamarin-prover/" -v full="$full" '
    BEGIN {
      while ((getline line < ledger) > 0) {
        if (line ~ /^#/ || line ~ /^[[:space:]]*$/) continue
        split(line, a, "\t")
        if (a[1] != sweep) continue
        k = a[2] SUBSEP a[5]
        if (k in cls)
          print "LEDGER-DUP: " sweep " " a[2] (a[5] == "" ? "" : " " a[5]) \
                " is listed twice — only the last entry is reachable" > "/dev/stderr"
        cls[k] = a[3]; det[k] = a[6]
      }
    }
    {
      # Exact prefix strip, not a regex: a greedy /.*\/tamarin-prover\// would
      # cut at the LAST such component, so a checkout under a directory of that
      # name would key rows on a truncated path and match the wrong entry.
      rel = $1
      if (index(rel, prefix) == 1) rel = substr(rel, length(prefix) + 1)
      key = rel SUBSEP ""
      if (!(key in cls) && unitcol > 0) key = rel SUBSEP $unitcol
      if (key in cls) {
        seen[key] = 1
        split($NF, d, " ")
        if (($col == "DIFF" || $col == "ERROR") && (det[key] == "" || det[key] == d[1])) {
          # A killed run produced nothing to disagree with, so "documented"
          # cannot mean "agrees" here: the row terminates as UNCOMPARED, which
          # sweep_finish counts apart from the clean rows. hit[] is still set —
          # the entry IS excusing this row, so it must not be reported STALE.
          $col = ($col == "ERROR" || d[1] == "timeout/kill") ? "UNCOMPARED" : "LEDGERED"
          $NF = $NF " [" cls[key] "]"; hit[key] = 1
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
      if (full) for (k in cls) {
        if (k in seen) continue
        split(k, kk, SUBSEP)
        print "LEDGER-UNMATCHED: " sweep " " kk[1] (kk[2] == "" ? "" : " " kk[2]) \
              " matched no row of this sweep — the entry can never be reported stale" > "/dev/stderr"
      }
    }
  ' "$out" 2> "$rep" > "$out.ledgered" && mv "$out.ledgered" "$out"
  cat "$rep" >&2
  LEDGER_REPORTS=$(grep -c . "$rep")
  rm -f "$rep"
}

# sweep_finish <out.tsv> <sweep-name> <status-col> [sub-unit-col]
#   Returns nonzero — and says so in the DONE sentinel — when the run proved
#   nothing: NO-COMPARE rows, or rows that never landed at all (a child that
#   died before appending, an xargs that never ran, a retry that dropped its
#   row). Both are silent in a plain status histogram, which is exactly how a
#   sweep gets to look green without having compared anything.
#
#   The DONE line carries UNCOMPARED=n beside the verdict, always — the rows
#   apply_ledger terminated as UNCOMPARED are documented timeouts/kills, so they
#   do not fail the run, but they are not agreement either and a reader must not
#   have to go looking for them. verdict=OK UNCOMPARED=25 means "the rows it
#   compared agree, and 25 rows were never compared".
sweep_finish() {
  local out=$1 sweep=$2 col=$3 unitcol=${4:-0} nc unc rows total bad='' bd
  # The parallel children append in completion order, which varies with load;
  # sorting makes two runs of the same corpus diffable against each other.
  sort -o "$out" "$out"
  apply_ledger "$out" "$sweep" "$col" "$unitcol"
  echo "== summary =="
  cut -f"$col" "$out" | sort | uniq -c
  awk -F'\t' -v col="$col" '$col == "DIFF" || $col == "ERROR"' "$out" | head -40
  nc=$(awk -F'\t' -v col="$col" '$col == "NO-COMPARE"' "$out" | grep -c .)
  # Counted AFTER apply_ledger, which is what mints the status.
  unc=$(awk -F'\t' -v col="$col" '$col == "UNCOMPARED"' "$out" | grep -c .)
  # An ABSENT out.tsv makes grep print nothing at all, and an empty `rows`
  # turns the row-count test below into a shell error that leaves the flag
  # unset — the one state (no file, so no comparison whatsoever) that most
  # needs the flag.
  rows=$(grep -c . "$out" 2>/dev/null) || rows=0
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
  if [ "$unc" -gt 0 ]; then
    echo "== $unc row(s) UNCOMPARED — a documented timeout/kill reached no verdict on them =="
    awk -F'\t' -v col="$col" '$col == "UNCOMPARED"' "$out" | head -40
  fi
  if [ "$rows" -ne "$total" ]; then
    bad="${bad:+$bad }ROW-COUNT=$rows/$total"
    echo "== $rows rows for $total items — the missing ones were never compared =="
  fi
  if [ "${LEDGER_REPORTS:-0}" -gt 0 ]; then
    bad="${bad:+$bad }LEDGER=$LEDGER_REPORTS"
    echo "== $LEDGER_REPORTS ledger entry/entries excuse nothing (see LEDGER-* on stderr) — drop them =="
  fi
  # files= counts the distinct FILES that actually reached a verdict (OK, DIFF
  # or LEDGERED — ERROR/NO-COMPARE/UNCOMPARED rows compared nothing).
  # rs_ref_check.sh generate reads it to refuse a scoped run (FAMILY=1, a
  # narrowed list) as evidence for a wider re-baseline. Trailing and additive,
  # so `grep -oE 'verdict=[^ ]+'` consumers are unchanged.
  local nf
  nf=$(awk -F'\t' -v col="$col" '$col=="OK"||$col=="DIFF"||$col=="LEDGERED"{print $1}' "$out" | sort -u | grep -c .)
  echo "== DONE $sweep $(date -u +%FT%TZ) verdict=${bad:-OK} UNCOMPARED=$unc files=$nf =="
  [ -z "$bad" ]
}

# sweep_drive <sweep> <status-col> [unit-col [unit...]]
#   The driver tail the three sweeps carried as triplicated copies: stale-RS
#   check, the sweep's own list_files resolved and deduped, banner, parallel
#   pass, serial retry of the ERROR rows, ledger + verdict. The caller must
#   have defined list_files and one (and run sweep_export). With units given,
#   every file expands to one (file, unit) job per unit and `one` receives
#   both fields (module_sweep's modules; <unit-col> is then the ledger's
#   sub-unit column); without, one job per file.
#   xargs -d '\n': one field per argument, with quote and backslash processing
#   off, so nothing about a path's spelling can split or reshape it.
sweep_drive() {
  local sweep=$1 col=$2 unitcol=${3:-0} LIST n f u
  shift 2; [ $# -gt 0 ] && shift
  local -a units=("$@")
  rs_stale_check
  LIST=$(list_files) || exit 2
  LIST=$(sort -u <<< "$LIST")
  : > "$OUT"
  n=$(grep -c . <<< "$LIST")
  if [ "${#units[@]}" -gt 0 ]; then
    sweep_banner "${sweep}_sweep" "$(( n * ${#units[@]} ))"
    while IFS= read -r f; do
      for u in "${units[@]}"; do printf '%s\n%s\n' "$f" "$u"; done
    done <<< "$LIST" | xargs -r -d '\n' -P "$JOBS" -n 2 bash -uc 'one "$0" "$1"'
  else
    sweep_banner "${sweep}_sweep" "$n"
    xargs -r -d '\n' -P "$JOBS" -n 1 bash -uc 'one "$0"' <<< "$LIST"
  fi
  sweep_retry "$OUT" "$col"
  sweep_finish "$OUT" "$sweep" "$col" "$unitcol"
}
