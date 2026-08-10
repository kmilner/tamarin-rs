# Testing the Rust port

How the port is verified against the Haskell prover, from unit tests up to
full-corpus byte parity. Commands run from the repository root unless noted;
the pristine Haskell sources and the examples corpus live in the
`tamarin-prover/` submodule.

## Prerequisites

**The Haskell oracle.** `./setup.sh testing` materialises a patched copy of
the prover at `tamarin-prover-testing/` (the submodule itself is never
modified); build it with stack. Parity scripts auto-discover the binary under
`tamarin-prover-testing/.stack-work/`; set `HS_PATH` to point them at a
specific binary instead.

**A current release build.** Every gate but `web_parity.sh` uses
`target/release/tamarin-rs` as-is and only checks that the file exists — a
binary from an older commit gates green and says nothing. Only the three flag
sweeps refuse a stale binary (`rs_stale_check`). Build before you gate:

```bash
cargo build --release                          # the gates' RS side
cargo build --release --example dump_proof     # separate target; the plain build does NOT cover it
```

The binary stamps its own provenance, so you can always check what a gate
actually measured:

```bash
target/release/tamarin-rs <any-theory> | grep '^Git revision:'
```

**`maude`, and `dot` for the web gate's graph pages.** These reach the two
sides differently, and getting it wrong is a silent vacuous pass rather than
an error:

- *Shell scripts* want them on `PATH`. `wf_gate.sh` and `pretty_gate.sh`
  prepend linuxbrew themselves; the rest inherit your `PATH`. On hosts where
  these come from linuxbrew they are often *not* on `PATH` by default:

  ```bash
  export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
  ```

- *The Rust suite* ignores `PATH` entirely. All 32 files under `crates/` that
  resolve maude read `$MAUDE_PATH`, and fall back to `/usr/local/bin/maude`
  and `/usr/bin/maude` — nothing else. With `MAUDE_PATH` unset on a host whose
  maude is elsewhere, every one of those tests returns early and the run still
  prints `ok`; the only tell is the wall clock. Always set it:

  ```bash
  MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace
  ```

  (A `MAUDE_PATH` that is set but names a missing file panics rather than
  skipping — the misconfiguration is caught, the omission is not.)

## The correctness criterion

**Byte-identical raw `--prove` stdout**, after deleting four
environment-volatile lines: `Git revision:`, `Compiled at:`,
`processing time:` and `analyzed:` (the last carries the input path). That is
the `strip_env` shared by `corpus_file_diff.sh`, `wf_gate.sh`,
`pretty_gate.sh`, `rs_ref_check.sh`, `rs_vs_rs_diff.sh`,
`triage_diff_vs_hs.sh` and `divergence_fixtures/_common.sh`; the sweeps blank
the same four lines instead of deleting them.

Two triage scripts are stricter than the gates they triage:
`diff_proof_raw.sh` and `corpus_raw_diff.sh` keep `analyzed:`. Since both take
a single file, the line is constant across their two sides and the difference
does not bite in practice — but it is a real asymmetry, so a diff confined to
that line is an artefact, not a finding.

Stderr and exit status are outside the criterion on the prove path: the batch
gate sends both sides' stderr to `/dev/null` and inspects only rc 124
(timeout). The flag sweeps do compare stderr and rc, but none of them proves.

## The verification ladder

Three tiers by cost. Every gate in them carries its own verdict — see
"Reading a gate's result" below — so a tier is an `&&` chain, not a reading
exercise. (The two sweeps that do *not*, `pane_byte_check.sh` and
`rs_vs_rs_diff.sh`, are deliberately absent from the tiers for that reason.)

**Tier 1 — inner loop, minutes, no oracle binary needed past the cache.**

| Command | Checks | Cost |
|---|---|---|
| `cargo fmt --all --check` | formatting (CI enforces it) | seconds |
| `cargo clippy --workspace --all-targets -- -D warnings` | lints (CI enforces it) | seconds warm |
| `MAUDE_PATH=$(command -v maude) cargo test --profile ci --workspace` | Rust unit + integration suites | minutes |
| `scripts/divergence_fixtures/check.sh` | 19 corner fixtures vs committed oracle captures | ~5 s |
| `scripts/wf_gate.sh` | wellformedness block, 432 files, vs the batch cache | ~45 s |
| `scripts/pretty_gate.sh` | `theory … end` echo, 432 files, vs its own oracle cache | ~45 s |

**Tier 2 — pre-push, tens of minutes.**

| Command | Checks |
|---|---|
| `scripts/rs_ref_check.sh check` | what CI's `rs-parity` job runs: output hashes vs `ci_ref_fast.tsv` |
| `FAMILY=1 scripts/pe_sweep.sh` / `module_sweep.sh` / `json_sweep.sh` | flag parity, one representative per divergence class |

**Tier 3 — milestone, hours.**

| Command | Checks |
|---|---|
| `scripts/corpus_file_diff.sh` | the ground-truth batch gate: 432-file `--prove` byte parity (~30–60 min cold) |
| `scripts/pe_sweep.sh` / `module_sweep.sh` / `json_sweep.sh` | the same sweeps over their full corpora |
| `ALLOWLIST=<filelist> scripts/web_parity.sh` | interactive-mode gate: crawl + semantic diff |
| `scripts/bench.sh` | performance tables (see README) |

**What CI enforces is Tier 1 plus `rs_ref_check.sh check` — and none of it is
an oracle comparison.** `rs_ref_check.sh` diffs this branch's output hashes
against `ci_ref_fast.tsv`, a reference generated from *main's own binary*; it
is a self-consistency check, and after a deliberate output change the
documented fix is to regenerate the reference from the very binary whose
output moved. `cargo test`'s oracle-backed cases skip themselves when no
oracle is present, which is CI's state. Oracle parity is therefore a *local*
property, established only by the gates above — nothing in CI can catch a
divergence from the Haskell prover.

When a gate goes red, drop to "Debugging a divergence" below.

## Reading a gate's result

`corpus_file_diff.sh`, `wf_gate.sh`, `pretty_gate.sh` and `web_parity.sh`
each end with a `verdict=` line and return it in the exit status. Read that,
not the histogram above it — a DIFF count of 0 is also what a run that
compared nothing prints, and the verdict is what separates the two:

```
wf_gate: MATCH=432 DIFF=0 SKIP=0  ->  .../scripts/results/wf_gate_results.tsv
wf_gate: verdict=OK
```

What each verdict folds in differs, so do not generalise:

| Gate | Fails on |
|---|---|
| `corpus_file_diff.sh` | DIFF, any `SKIP_*`, rows ≠ files listed, empty file list |
| `wf_gate.sh` | DIFF, any `SKIP_*`, zero rows |
| `pretty_gate.sh` | DIFF, any `SKIP_*`, zero rows |
| `web_parity.sh` | `SKIP_*` and files that produced no row — **vacuity only**, never a DIFF |
| `pe/module/json_sweep.sh` | undocumented DIFF/ERROR, NO-COMPARE, stale ledger entries |

Only `corpus_file_diff.sh` compares its row count against the file list;
`wf_gate.sh` and `pretty_gate.sh` assert only that *some* row landed, so a
child killed mid-run leaves its file uncompared without a trace. `web_parity.sh`
reports divergence as findings for hand-triage against
`scripts/websweep_residual.txt` and leaves the status alone.

Two sweeps carry no verdict at all and always exit 0 —
`scripts/pane_byte_check.sh` and `scripts/rs_vs_rs_diff.sh`. For those, read
the `=== SUMMARY ===` histogram yourself and confirm the row count matches
your file list; `$?` tells you nothing.

## Rust test suite

```bash
MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace
MAUDE_PATH="$(command -v maude)" cargo test -p tamarin-theory --test oracle_solver
```

~1580 tests, 10 `#[ignore]`d. `--profile ci` is what CI uses and what to
prefer locally: it is release optimisation without fat LTO, which the release
profile would re-run at every one of the ~44 test-binary links. Each profile
also gets its own target tree, so alternating between plain `cargo test`
(dev), `--release` and `--profile ci` builds the suite three times over —
`target/debug` alone runs to tens of gigabytes. Pick one and stay on it.

`MAUDE_PATH` is not optional here; see Prerequisites. Without it,
`cargo test -p tamarin-prover --test output_module` reports the same
`15 passed` in 0.02 s that a real run takes 0.43 s to produce.

The oracle-backed cases in `oracle_solver` skip silently when no HS binary is
reachable, the same way. A green `oracle_solver` is evidence only on a box
with both maude and the oracle.

`oracle_solver` also carries heavyweight corpus probes behind `#[ignore]`:

```bash
cargo test --test oracle_solver corpus_proof_skeleton_match_probe --release -- --ignored --nocapture
```

- `corpus_verdict_match_coverage_probe` — verdict agreement sweep.
- `corpus_proof_skeleton_match_probe` — canonicalised proof-tree comparison
  per lemma. Historically the primary metric; superseded by the byte gate
  below, which subsumes it.

**Neither probe asserts anything.** Both print a match rate and a divergence
list to stderr and return — `--ignored` runs report success at any rate. They
are diagnostics to read, not gates to pass, which is why `--nocapture` is part
of the command line.

## Single-lemma parity

```bash
cargo build --release
TAM_RS_NO_AUTO_BUILD=1 scripts/diff_proof_raw.sh \
    tamarin-prover/examples/classic/NSPK3.spthy injective_agree
```

Raw byte-for-byte diff of one lemma's `--prove` output; exit 0 = identical.

**`TAM_RS_NO_AUTO_BUILD=1` is currently required.** The auto-build step in
`diff_proof_raw.sh` and `corpus_raw_diff.sh` runs
`cargo build --release --bin tamarin-prover`, and there is no such bin target
— the *package* is `tamarin-prover`, the binary is `tamarin-rs`. Cargo
answers `error: no bin target named 'tamarin-prover' in default-run packages`
and both scripts treat that as fatal (`exit 2`) before doing any work. Build
the binary yourself and set the variable until the scripts are fixed.

## Corpus gate (the batch parity metric)

```bash
cargo build --release
RESULTS_TSV=/tmp/gate.tsv scripts/corpus_file_diff.sh    # ALLOWLIST defaults to the 432-file corpus
```

Ends in `DONE_CORPUS_FILE_DIFF verdict=OK` and exits 0, or names what is
wrong (`DIFF=n`, `SKIPPED=n`, `ROW-COUNT=n/432`) and exits nonzero. There is
nothing to tally by hand: the script prints its own `=== SUMMARY ===`
histogram, and the verdict additionally covers the two failure modes a
histogram cannot show you — files whose bytes were never compared, and files
that produced no row at all.

Whole-file `--prove` diff over the canonical 432-file corpus
(`scripts/parity_corpus.txt` — the submodule's examples plus one repo-local
Nat+reuse fixture listed by `../..`-relative path). Two strictly sequential phases: Haskell
output is computed once per file-content hash and cached under
`scripts/.hs_file_cache/`; the Rust binary is then diffed against the cache
— so re-runs after Rust-only changes skip the Haskell side entirely.
Theories whose upstream recipe needs extra arguments get them from
`scripts/file_flags.tsv`, applied identically to both provers.

Env knobs (full list in the script header): `ALLOWLIST` (one relative path
per line; unset uses `scripts/parity_corpus.txt`, set-but-unreadable is
`exit 2`), `RESULTS_TSV`, `JOBS` (4), `HS_N` (RTS cores per oracle, 4),
`HS_MAXHEAP` (GHC `-M`, 11 g), `FILE_TIMEOUT` (300 s), `DERIVCHECK_TIMEOUT`
(30 s), `CORPUS_ROOT`, `CACHE`, `HS_PATH`, `RS_PATH`, `FLAGS_MAP`.

**Budget for it.** `JOBS=4` is a memory bound, not a leftover: four
concurrent oracles at `-N4 -M11g` plus four Rust provers is up to ~44 GB of
GHC heap. This is also the one gate with no `oom_score_adj` / `ulimit -v`
prologue — every other one has it, directly or through a sourced helper — so
on a constrained box run it under your own guard rather than raising `JOBS`.

**Cache-staleness trap.** `.hs_file_cache/` keys on
`sha256(theory)` plus a hash of the file's `file_flags.tsv` entry — nothing
about the oracle that produced the bytes. Change the oracle's behaviour and
every entry is silently stale under an unchanged key, which surfaces as false
DIFFs, or as a false MATCH when the port has moved the same way.

`bump_submodule.sh` handles the submodule case for you: it renames
`.hs_file_cache/`, `.web_hs_cache/` and `.hs_pretty_cache/` aside as
`.pre-bump-<sha>` before rebuilding. `.hs_canon_cache/` (the single-lemma
triage cache) is *not* archived, so `diff_proof_raw.sh` keeps serving
pre-bump bytes after one.

The case nothing catches is **editing `patches/tamarin-prover-fixes.patch`
and re-running `./setup.sh testing`**. `pretty_gate.sh` stamps the oracle's
baked `Git revision:` into its cache dir and wipes on a change, but
`setup.sh` applies the patch to a worktree and never commits it, so that
revision is the submodule pin for *every* patched build — identical before
and after a patch edit. The stamp cannot fire, and the other caches have no
stamp at all. Only `.hs_sweep_cache/` is safe: `sweep_common.sh` folds
`stat -c '%s.%Y'` of the oracle binary into every key, so a rebuild is a
cache miss rather than a policy the operator has to remember.

After a patch rebuild, clear the caches by hand (or point `CACHE` at a fresh
directory) before trusting any gate but the sweeps.

## Fast gates (run on every build)

Both slice the *load-time* output — no `--prove` — so they cost ~45 s over
the whole 432-file corpus instead of the batch gate's tens of minutes.

```bash
scripts/wf_gate.sh        # the wellformedness WARNING block
scripts/pretty_gate.sh    # the pretty-printed `theory … end` echo
```

They differ in where their reference side comes from, which decides what a
cold cache costs you:

- `wf_gate.sh` extracts its slice from **`corpus_file_diff.sh`'s `--prove`
  cache** and has no fill phase of its own. With `.hs_file_cache/` archived —
  which is the state `bump_submodule.sh` leaves — every file reports
  `SKIP_NO_HS` and the only way back is a full batch-gate run.
- `pretty_gate.sh` owns `.hs_pretty_cache/` and fills it itself in PHASE 0
  with a cheap no-prove oracle pass. `NO_HS_FILL=1` skips that phase, which is
  what you want on a warm cache; on a cold one it turns the whole run into
  `SKIP_NO_HS`.

Env: `RS_PATH`, `HS_CACHE`, `JOBS` (4), `FILE_TIMEOUT` (120 s wf / 420 s
pretty — the csf26-ac AC-variant precomputation makes three files take ~170 s
to load under the oracle), `RESULTS_TSV`, `ALLOWLIST`, `CORPUS_ROOT`,
`FLAGS_MAP`, `DERIVCHECK_TIMEOUT`; `HS_PATH` and `NO_HS_FILL` for
`pretty_gate.sh`. Both prepend linuxbrew to `PATH` themselves, so they use
linuxbrew's maude whatever the operator set.

## Corner fixtures (no oracle, no proving)

```bash
scripts/divergence_fixtures/check.sh          # ~5 s, 19 fixtures
```

Behaviour that no theory under the submodule's `examples/` tree reaches, so
`wf_gate`/`pretty_gate`/`corpus_file_diff` all stay green across a regression
in any of it. Only the port runs: the oracle side is captured bytes committed
under `divergence_fixtures/expected/`, stamped with the pin they came from
(`expected/oracle_rev`) — `check.sh` refuses to run when that stamp no longer
matches the submodule pin, so a bump forces a fresh `capture.sh`. One fixture,
`ac_marker_collapse`, must NOT match — the check asserts both sides of a
deliberate divergence, which a MATCH-only corpus gate cannot express.

It is the cheapest real assertion in the tree and it runs **nowhere
automatically** — not in CI, not under `cargo test`. Run it by hand.

## Flag-parity sweeps

```bash
FAMILY=1 scripts/pe_sweep.sh        # --partial-evaluation
FAMILY=1 scripts/module_sweep.sh    # -m / --output-module
FAMILY=1 scripts/json_sweep.sh      # --output-json / --output-dot
```

Load-time only (none of them proves), but the only gates that compare
**stderr and exit status** as well as stdout, and the only ones whose cache
key includes the oracle binary. `FAMILY=1` is the inner-loop subset — one
representative per divergence class, seconds on a warm cache; dropping it
gives the milestone corpus. Documented residuals live in
`scripts/sweep_expected.tsv` and report as `LEDGERED`; see `scripts/README.md`
for what the ledger can and cannot excuse.

## CI reference gate

```bash
scripts/rs_ref_check.sh check       # exactly what CI's rs-parity job runs
```

Compares one binary's stripped `--prove` output hashes against
`scripts/ci_ref_fast.tsv` over the 365-file fast corpus. Note what this is
*not*: the reference was generated from main's own binary, so a pass means
"this branch agrees with main", not "this branch agrees with the oracle".
`generate` rewrites the reference and is manual — needed after a deliberate
output change, a submodule bump, or a Maude version change (the pinned
version is recorded in the reference header and enforced).

## Refactor inertness (RS-vs-RS)

For "this refactor must not change output" checks, no Haskell needed:

```bash
PRE=/tmp/rs-prepatch POST=/tmp/rs-patched scripts/rs_vs_rs_diff.sh
```

Runs two Rust binaries (pre/post) over every example and diffs stripped
stdout; agreement everywhere means the change is behaviorally inert and
inherits the baseline's HS-faithfulness by transitivity.
`scripts/triage_diff_vs_hs.sh` then 3-way-triages any DIFF files against
fresh Haskell output (moved toward HS or away?).

The transitivity argument needs *agreement everywhere*, and the script does
not check that for you: it prints a histogram and `DONE_RS_VS_RS`, and exits 0
on any outcome. Confirm the row count matches your file list, and read the
histogram past the `=== needs attention ===` block — that block lists
`ERROR_BOTH`/`ERROR_ONE`/`TIMEOUT_ONE`/`NOFILE`/`EMPTY_BOTH` but omits
`TIMEOUT_BOTH`, a file neither binary finished and therefore nothing compared.

## Web-parity gate (interactive mode)

```bash
ALLOWLIST=seed              RESULTS_TSV=/tmp/web.tsv scripts/web_parity.sh   # 2-file smoke
ALLOWLIST=<filelist>        RESULTS_TSV=/tmp/web.tsv scripts/web_parity.sh
```

**`ALLOWLIST` is required** — one corpus-relative path per line, or the
literal `seed` for the built-in 2-file smoke list. Unset or unreadable is
`exit 2`, not a fall-through to a default corpus.

Boots both servers on the same theory (HS on port 3021, RS on 3022), crawls
every proof-tree / constraint-system / graph / source page — autoproving
each lemma along the way — and diffs the pages semantically
(`web_crawl.py` / `web_normalize.py` / `web_diff.py`). HS crawl manifests
are cached content-keyed under `scripts/.web_hs_cache/` (same staleness
trap as above). Env knobs: `FILE_TIMEOUT`, `READY_TIMEOUT`, `HS_PORT`,
`RS_PORT`, `MAX_NODES` (400 proof-node visits per theory), `CACHE`,
`DIFFDIR`, `DERIVCHECK_TIMEOUT`, `SERVER_MEM_KB` (per-server address-space
cap, 24 GiB), `HS_PATH`, `RS_PATH`, `MAUDE_PATH`, `CORPUS_ROOT`,
`TAM_RS_NO_AUTO_BUILD` (it rebuilds the port by default, unlike every other
gate).

**Its exit status reports vacuity, not divergence.** `SKIP_*` rows and files
that produced no row fail the run; DIFF and `MISSING_*` rows leave the status
alone and are findings for you to triage by hand. The known cosmetic residue
(identical proof states rendered with different internal counter values on a
few AC-heavy theories — see the README) lives in
`scripts/websweep_residual.txt`; a page-level DIFF is only actionable if its
file is not in that list or the diff is structural. No script performs that
comparison — unlike `sweep_expected.tsv`, the web ledger is read by no gate,
so an entry that has stopped excusing anything is never reported.

`scripts/pane_byte_check.sh` is the byte-exact companion for the
`main/message` and `main/rules` panes. Pass it an explicit `ALLOWLIST`: its
default is `websweep_residual.txt`, i.e. exactly the set where a DIFF is
expected, and it has no verdict line and always exits 0 — including when a
missing `.web_hs_cache/` makes every row `SKIP_NO_CACHE`.

## Debugging a divergence

Work top-down: which lemma → which proof step → which solver call.

**Proof-tree diff** (canonicalised, per lemma):

```bash
scripts/diff_proof_tree.sh tamarin-prover/examples/Tutorial.spthy Client_auth
scripts/diff_proof_tree.sh <file> <lemma> "TAM_RS_DBG_APPLY_EQ_STORE=1"   # extra env for the RS run
target/release/examples/dump_proof <file> <lemma> | python3 scripts/canon_proof_tree.py
```

`scripts/corpus_diff_proof_trees.sh` runs the same diff over a hand-picked
regression corpus (PASS/FAIL tally); `scripts/corpus_full_trace_diff.sh`
does it for every lemma in the corpus.

**Proof-search state trace** — both provers emit a `[STATE]` line at every
proof-method expansion; diffing them pinpoints the first divergence:

```bash
TAM_HS_TRACE_STATE=1 <hs-binary>                 --prove=<lemma> <file> 2>&1 | grep '^\[STATE\]' > /tmp/hs.trace
TAM_RS_TRACE_STATE=1 target/release/tamarin-rs --prove=<lemma> <file> 2>&1 | grep '^\[STATE\]' > /tmp/rs.trace
diff /tmp/hs.trace /tmp/rs.trace | head
```

**Maude IPC trace** — lock-step command/response comparison:

```bash
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify target/release/tamarin-rs --prove <file>
scripts/diff_maude_io.sh <file> <lemma>       # side-by-side HS↔RS Maude traffic
scripts/diff_aes_calls.sh <file> <lemma>      # apply_eq_store call counts per site
```

See `crates/tamarin-term/src/maude_proc.rs` for the env-gated trace points.

**Diagnostic env flags** (all off by default; solving behavior is never
env-configurable — these only dump, count, verify-and-panic, or force a
reference path whose output is byte-identical). `TAM_HS_*` work on the
instrumented Haskell build, the rest on the Rust binary:

| Variable | Effect |
|---|---|
| `TAM_RS_DBG_INTR_DUMP=1` | assembled intruder-rule cache (index, kind, budget/flags, facts) |
| `TAM_RS_DBG_SOURCES_DUMP=1` | per-source goal + refined case names after `ensure_saturated` |
| `TAM_DBG_PERFORM_SPLIT=1` | perform_split case lists (RS) |
| `TAM_HS_DBG_PERFORM_SPLIT=1` | same, HS side |
| `TAM_RS_DBG_APPLY_EQ_STORE=1` | applyEqStore IN/OUT (RS) |
| `TAM_HS_DBG_APPLY_EQ_STORE=1` | same, HS side |
| `TAM_DBG_AES_VARIANTS=1` | apply_eq_store variant before→after counts |
| `TAM_HS_TRACE_CHAINS=1` | HS-side solveChain enter/extend |
| `TAM_RS_VERIFY_BOUNDS_CACHE=1` | panic if the bounds_max cache diverges from a full recompute |
| `TAM_RS_VERIFY_SUBST_SKIP=1` | panic if a marker-skipped `subst_system` pass was not a bit-identical no-op |
| `TAM_RS_VERIFY_FP=1` | panic if a bloom-skipped fact descent would actually have changed the fact |
| `TAM_RS_VERIFY_FACT_MAX=1` | panic if a Fact's cached `max_var` diverges from a full walk of its terms |
| `TAM_RS_VERIFY_CANON_TABLES=1` | panic if a per-store incremental canon table diverges from a full rebuild |
| `TAM_RS_NO_SIMP_NOOP_SKIP=1` | force the full Simplify pass (disable the no-op shortcut; A/B oracle) |
| `TAM_RS_NO_SOURCE_CACHE=1` | disable the session source cache + presaturation pre-pass (per-lemma recompute) |
| `TAM_RS_SUBST_SKIP_STATS=1` | `subst_system` call/skip counters to stderr |
| `TAM_RS_FP_STATS=1` | fact-descent bloom-skip counters to stderr |
| `TAM_RS_SIMP_NOOP_STATS=1` | Simplify no-op shortcut hit/miss counters to stderr |
| `TAM_RS_CANON_TABLE_STATS=1` | canon-table cache hit/rebuild counters to stderr |

The `TAM_RS_VERIFY_*` hooks certify the solver's internal caches and skip
optimisations: exporting them during a full corpus-gate run re-executes every
skipped computation and panics on any divergence, turning the byte gate into a
self-check of the optimisation machinery as well. The `TAM_RS_NO_*` switches
are the A/B complement — they force the pre-optimisation reference path, whose
output must stay byte-identical.

The list is not exhaustive — grep the sources for `TAM_DBG_` / `TAM_RS_` /
`TAM_HS_` for the full set.

## Script index

Per-script detail — env contracts, verdict semantics, cache layout — lives in
`scripts/README.md`; this is the map.

**Gates**

| Script | Purpose |
|---|---|
| `corpus_file_diff.sh` | the ground-truth batch byte gate (cached HS, per-file) |
| `wf_gate.sh` | wellformedness block, 432 files, off the batch cache |
| `pretty_gate.sh` | `theory … end` echo, 432 files, own no-prove cache |
| `divergence_fixtures/check.sh` (+ `capture.sh`, `fixtures.tsv`) | corners the corpus cannot reach; no oracle, no proving |
| `pe_sweep.sh` / `module_sweep.sh` / `json_sweep.sh` (+ `sweep_common.sh`) | flag parity: stdout, stderr and rc |
| `rs_ref_check.sh` | CI's gate: output hashes vs `ci_ref_fast.tsv` (RS-vs-RS, not oracle) |
| `web_parity.sh` (+ `web_crawl.py`, `web_normalize.py`, `web_diff.py`) | interactive-mode gate |
| `pane_byte_check.sh` | byte-exact pane HTML vs the web cache (no verdict; always exits 0) |
| `rs_vs_rs_diff.sh` / `triage_diff_vs_hs.sh` | refactor-inertness sweep + 3-way triage (no verdict; always exits 0) |

**Data files**

| File | Purpose |
|---|---|
| `parity_corpus.txt` | canonical 432-file corpus list |
| `parity_corpus_fast.txt` | 365-file CI subset (every file proving in ≤1.5 s) |
| `file_flags.tsv` | per-file extra prover flags, applied to both sides |
| `ci_ref_fast.tsv` | committed output-hash reference for `rs_ref_check.sh` |
| `sweep_expected.tsv` | the flag sweeps' residual ledger (applied mechanically) |
| `pe_family.txt` / `module_family.txt` / `json_family.txt` | `FAMILY=1` subsets |
| `websweep_residual.txt` | accepted web-parity residue (hand-triage only; no gate reads it) |

**Triage**

| Script | Purpose |
|---|---|
| `diff_proof_raw.sh` | one lemma, raw HS↔RS diff — needs `TAM_RS_NO_AUTO_BUILD=1` |
| `corpus_raw_diff.sh` | raw per-lemma diff across the corpus — same |
| `compare_parity_tsv.py` | compare two gate TSVs by (file, lemma) |
| `diff_maude_io.sh` / `diff_aes_calls.sh` | Maude-IPC and eq-store call-site diffs |
| `diff_proof_tree.sh` / `canon_proof_tree.py` / `corpus_diff_proof_trees.sh` | structural proof-tree diffs, pre-byte-parity era; superseded by the byte gates and only worth reaching for when output diverges too grossly to read |
| `corpus_full_trace_diff.sh` / `canonicalize_trace.py` / `diff_trace.py` | canonicalised `[EXEC]` trace diffing; the most detailed comparison |

**Maintenance**

| Script | Purpose |
|---|---|
| `bump_submodule.sh` | submodule bump: patch rebase, oracle rebuild, cache archiving, cite remap, re-certification checklist |
| `bench.sh` | RS-vs-HS wall-clock + memory tables (`--write` regenerates the README block) |
| `check_hs_cites.py` / `remap_hs_cites.py` / `extend_anchor_citations.py` | upstream line-cite validation and remapping |
| `gen_license_headers.py` (+ `header_identities.json`) | GPL notice maintenance (`--check` for staleness) |
