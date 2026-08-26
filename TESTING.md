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

- *Shell scripts* resolve maude for themselves, through the one resolver in
  `scripts/gate_common.sh`: `$MAUDE_PATH` when set → `maude` on your `PATH` →
  `/home/linuxbrew/.linuxbrew/bin/maude` → hard fail naming all three steps. A
  `MAUDE_PATH` that is set but is not an executable file is a hard fail too,
  never a silent fall-through to something else. The gates
  (`corpus_file_diff.sh`, `wf_gate.sh`, `pretty_gate.sh`), the three flag
  sweeps, `rs_ref_check.sh`, `rs_vs_rs_diff.sh`, `web_parity.sh` and
  `pane_byte_check.sh` all take that route, so an explicit `MAUDE_PATH`, or a
  `maude` on your own `PATH`, wins over the linuxbrew install instead of being
  overridden by it. Two deliberate exceptions: `capture_cli_refs.sh` walks the
  Rust test harness's own ladder (its captures must use the maude
  `cli_e2e.rs` will), and `migrate_hs_cache_fp.sh` tolerates a missing maude
  so its revision probe reports `NOT CHECKED` rather than blocking a
  rename-only migration.

  The resolved binary's own directory is prepended to `PATH`, which is how the
  children pick it up: the flag sweeps pass `--with-maude` outright, and
  everything else lets each engine resolve by name — the oracle straight off
  `PATH`, the port only after trying `/usr/local/bin/maude` and
  `/usr/bin/maude`, so a host carrying either of those hands the port that one
  whatever the script resolved (this box has neither).

  Two things are plain `PATH` lookups: `dot`, which the web servers
  invoke by name, and the per-lemma triage tools (`diff_proof_raw.sh`,
  `corpus_raw_diff.sh`, `corpus_full_trace_diff.sh`, `triage_diff_vs_hs.sh`),
  which run the provers on whatever they inherit. On hosts where these come
  from linuxbrew and it is *not* on `PATH` by default:

  ```bash
  export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
  ```

- *The Rust suite* mostly ignores `PATH`. 28 files under `crates/` resolve
  maude, and they do not all do it alike. 13 test sites — both
  `tests/common/mod.rs` harnesses, `tamarin-theory`'s `oracle_solver`, and ten
  `#[cfg(test)]` modules under `tamarin-theory` and `tamarin-server` — probe
  `$MAUDE_PATH` → `/usr/local/bin/maude` → `/usr/bin/maude` → `$PATH` →
  `/home/linuxbrew/.linuxbrew/bin/maude`, and **panic** when none of them
  resolves rather than skipping. The other 15 (the remaining in-crate test
  modules, plus the production probe in `tamarin-prover/src/run.rs` and the
  server example) still read `$MAUDE_PATH` and the two `/usr` paths and
  nothing else, so on a host whose maude is elsewhere they return early and
  the run still prints `ok`. Set it — it is the one thing every probe honours:

  ```bash
  MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace
  ```

  `TAM_ALLOW_NO_MAUDE=1` is the escape hatch for the 13: it restores their old
  silent skip, and is the only way a machine with no maude at all gets a green
  run. A `MAUDE_PATH` that is set but names a missing file is an assertion
  failure at 11 of the 13 (`rule_tests.rs` and `rule_variants.rs` still pass it
  through unchecked) and a silent fallback everywhere else.

## The correctness criterion

**Byte-identical raw `--prove` stdout**, after deleting four
environment-volatile lines: `Git revision:`, `Compiled at:`,
`processing time:` and `analyzed:` (the last carries the input path). That is
`strip_env`, defined once in `scripts/gate_common.sh` and sourced from there
by `corpus_file_diff.sh`, `wf_gate.sh`, `pretty_gate.sh`, `rs_ref_check.sh`,
`rs_vs_rs_diff.sh`, `capture_cli_refs.sh` and `triage_diff_vs_hs.sh`;
`divergence_fixtures/_common.sh` keeps its own copy of the same four-line
policy. The sweeps blank the same four lines instead of deleting them
(`norm`, also in `gate_common.sh`: a blanked line still pins that the line was
printed and where, which their no-compare check leans on).

Two triage scripts are stricter than the gates they triage:
`diff_proof_raw.sh` and `corpus_raw_diff.sh` keep `analyzed:` — that is
`strip_env_lines`, the third strip policy `gate_common.sh` carries. Since
both take a single file, the line is constant across their two sides and the
difference does not bite in practice — but it is a real asymmetry, so a diff
confined to that line is an artefact, not a finding.

Stderr is outside the criterion on the prove path: the batch gate sends both
sides' stderr to `/dev/null`. Exit status is not — the oracle's rc is cached
beside its stdout and compared, so identical bytes under a different status
are `RC_DIFF`, a failing row. The flag sweeps compare stderr as well as rc,
but none of them proves.

## The verification ladder

Three tiers by cost. Every gate here carries its own verdict — see "Reading a
gate's result" below — so a tier is an `&&` chain, not a reading exercise.
`pane_byte_check.sh` and `rs_vs_rs_diff.sh` carry one too; they sit outside the
tiers because they answer narrower questions (pane bytes, refactor inertness),
not because their exit status means nothing.

**Tier 1 — inner loop, minutes; no oracle *run* past the cache, but the two
fast gates do need the oracle binary present to address it.**

| Command | Checks | Cost |
|---|---|---|
| `cargo fmt --all --check` | formatting (CI enforces it) | seconds |
| `cargo clippy --workspace --all-targets -- -D warnings` | lints (CI enforces it) | seconds warm |
| `MAUDE_PATH=$(command -v maude) cargo test --profile ci --workspace` | Rust unit + integration suites | minutes |
| `scripts/divergence_fixtures/check.sh` | 52 corner fixtures vs committed oracle captures (CI runs this too) | ~10 s |
| `scripts/wf_gate.sh` | wellformedness block, 432 files, vs the shared load cache | ~45 s |
| `scripts/pretty_gate.sh` | `theory … end` echo, 432 files, vs the same load cache | ~45 s |

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

**What CI enforces is `cargo fmt`, clippy, `cargo test --workspace`,
`scripts/divergence_fixtures/check.sh` and `rs_ref_check.sh check`.** Only one
of those is a comparison against Haskell bytes, and it is a frozen one: the
`Divergence fixtures` step in the `test` job builds `--profile ci --bin
tamarin-rs` and runs the fixture check against captures committed in-tree, so
it catches drift on 19 corners (and a bump landing without a re-capture — see
below) but sees nothing outside them. `rs_ref_check.sh` diffs this branch's
output hashes against `ci_ref_fast.tsv`, a reference generated from *main's
own binary*; it is a self-consistency check, and after a deliberate output
change the documented fix is to regenerate the reference from the very binary
whose output moved. `cargo test`'s oracle-backed cases skip themselves when no
oracle is present, which is CI's state. General oracle parity is therefore a
*local* property, established only by the gates above.

When a gate goes red, drop to "Debugging a divergence" below.

## Reading a gate's result

Every gate here returns its verdict in the exit status, and all but
`rs_ref_check.sh` repeat it on a `verdict=` line — that one omits the token on
purpose, so its own log cannot be fed back as `--certified-by` evidence. Read
the verdict, not the histogram above it: a DIFF count of 0 is also what a run
that compared nothing prints, and the verdict is what separates the two.

```
wf_gate: MATCH=432 DIFF=0 SKIP=0 of 432  ->  .../scripts/results/wf_gate_results.tsv
wf_gate: verdict=OK files=432
```

The trailing `files=<n>` on every comparing gate's verdict line is the number
of files that run *actually compared* (skipped/uncompared rows excluded);
`rs_ref_check.sh generate` reads it to refuse a scoped log as evidence for a
wider re-baseline.

What each verdict folds in differs, so do not generalise:

| Gate | Fails on |
|---|---|
| `corpus_file_diff.sh` | DIFF, `RC_DIFF`, any `SKIP_*`, `ROW-COUNT`, empty file list |
| `wf_gate.sh` | DIFF, any `SKIP_*`, `ROW-COUNT`, empty file list |
| `pretty_gate.sh` | DIFF, any `SKIP_*`, `ROW-COUNT`, empty file list |
| `web_parity.sh` | undocumented DIFF/`MISSING_*`, `SKIP_*`, files with no comparison row, dead ledger entries |
| `pe/module/json_sweep.sh` | undocumented DIFF/ERROR, NO-COMPARE, stale ledger entries |
| `pane_byte_check.sh` | DIFF, `MISSING_*`, any `SKIP_*`, `FILE-COUNT`/`ROW-COUNT`, empty file list |
| `rs_vs_rs_diff.sh` | DIFF, `ERROR_*`, `TIMEOUT_*` (incl. `TIMEOUT_BOTH`), `NOFILE`, `EMPTY_BOTH`, missing rows |
| `rs_ref_check.sh check` | hash mismatch, `INPUT_CHANGED`, `NOTRUN`, maude-version mismatch |
| `capture_cli_refs.sh` | any row not captured, empty, or failing its `relation` column |
| `migrate_hs_cache_fp.sh` | a failed rename (`verdict=FAILED`); exit 2 when the oracle is not the pin |

All three corpus gates count their file list up front and fail on
`ROW-COUNT=rows/N`, so a child killed mid-run no longer leaves its file
uncompared without a trace, and each hard-exits 2 when the list resolves to
zero entries. `corpus_file_diff.sh` additionally prints `RC_UNKNOWN=n` — cache
entries filled before the `.rc` channel existed, which is *not* a failure;
they backfill on the next fill.

The three flag sweeps carry two non-fatal fields beside the verdict:
`== DONE <sweep> <ts> verdict=OK UNCOMPARED=<n> files=<n> ==`. See
"Flag-parity sweeps" below for what UNCOMPARED rows are; `files=` is the
compared-file count described above.

## Rust test suite

```bash
MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace
MAUDE_PATH="$(command -v maude)" cargo test -p tamarin-theory --test oracle_solver
```

The workspace holds 1566 tests. One of them carries the `#[ignore]`
attribute, so an ordinary run reports 1565 passed. CI uses `--profile ci`,
and it is the profile to
prefer locally: it is release optimisation without fat LTO, which the release
profile would re-run at every one of the ~44 test-binary links. Each profile
also gets its own target tree, so alternating between plain `cargo test`
(dev), `--release` and `--profile ci` builds the suite three times over —
`target/debug` alone runs to tens of gigabytes. Pick one and stay on it.

`MAUDE_PATH` is not optional at the 15 sites that still probe only two `/usr`
paths; see Prerequisites. Without it, `cargo test -p tamarin-prover --test
output_module` prints `14 passed` in 0.02 s, the same count a real run needs
0.43 s to produce. At the 13 widened sites an unresolvable maude is now a
panic naming `TAM_ALLOW_NO_MAUDE=1`, so those cannot report a vacuous green.

The oracle-backed cases in `oracle_solver` still skip silently when no HS
binary is reachable — the HS skip is deliberate, only the maude one was
closed. A green `oracle_solver` is evidence only on a box with both maude and
the oracle.

`crates/tamarin-server`'s suite additionally pins its committed HTTP captures
to the submodule: `haskell_captures_match_the_submodule_pin` compares
`tests/fixtures/haskell-responses/oracle_rev` against `git -C tamarin-prover
rev-parse HEAD` and fails — with no skip path — when a bump lands without
re-running `tests/capture_haskell_fixtures.sh`, which re-stamps that file on
every successful capture.

`crates/tamarin-prover`'s `cli_e2e` suite byte-compares flag pins against
committed oracle stdout under `tests/fixtures/cli_refs/`. Both sides read one
argv table, `cli_refs/cases.tsv`, so adding a pin is "add a row, re-run the
capture":

```bash
scripts/capture_cli_refs.sh              # serial, proving, guarded; or <name>… for one row
```

It writes `<name>.stdout` plus `CAPTURED.tsv` (oracle path and fingerprint,
submodule pin, maude version, per-row byte counts — the tests assert it lists
exactly the rows in `cases.tsv`) and ends in `DONE_CAPTURE_CLI_REFS
verdict=<...> captured=N/M`. Env: `HS_PATH`, `MAUDE`, `FILE_TIMEOUT` (120 s),
`ALLOW_ORACLE_REV_MISMATCH`. Those tests hard-fail rather than skip while the
captures are missing.

`oracle_solver` also holds one expensive corpus probe. The `#[ignore]`
attribute keeps this probe out of a normal test run. Run it with this command:

```bash
cargo test --test oracle_solver corpus_proof_skeleton_match_probe --release -- --ignored --nocapture
```

`corpus_proof_skeleton_match_probe` compares the port's proof tree against
the oracle's proof tree. It compares the two trees in a canonical form. It
makes one comparison per lemma, over the whole `examples/` tree. This probe
is not the correctness criterion. That criterion is byte-identical `--prove`
stdout, and the corpus gate below checks it. That gate is stricter than this
probe on the files it covers, because a proof is part of the stdout it
compares. Its file list is narrower: it names 431 of the 1042 `.spthy` files
under `examples/`, so this probe reaches files the gate never opens.

**The probe asserts.** It prints its match rate and its list of divergences.
It then calls `enforce_probe_ledger`. That function fails the test in four
ways. The first way is coverage below `STRUCTURAL_MIN_COMPARED`, which is 540
comparisons. The second way is a `STRUCTURAL_MISMATCH_LEDGER` that is still
`None`. The panic message then prints the paste-ready
`const … = Some(&[…]);` for you to commit. The third way is a mismatch that
the list does not name, which is a regression. The fourth way is a listed
identity that the run compared and found clean. That entry is stale, and you
remove it in a commit that explains the fix. The run does not always compare
every identity in the list. The usual cause is a per-file oracle timeout
under machine load. The probe prints those identities, and they count towards
neither failure. The list holds mismatch identities in the form
`<corpus-relative-path>::<lemma>`. It does not hold a count. The set of
eligible lemmas changes with machine load. A count limit therefore gives
false results in both directions. The mismatch identities stay the same.
The probe prints all of these lines to stderr, so the command line includes
`--nocapture`.

## Wellformedness fixtures (oracle-differential)

```bash
cargo run -p tamarin-parser --example wellformedness_fixtures
```

`-- --no-tamarin` skips the oracle pass. Each fixture under
`tests/wellformedness_fixtures/` is checked three ways: it parses, the Rust
`wf::check_theory` emits the topics `expected.txt` claims for it, and
`tamarin-prover` emits them too. Expectations are positive by default;
a line beginning `#!<fixture> : <topics>` is a *negative* pin — topics that
must NOT appear on either side — which is how a fixture whose positive
expectations all live post-elaboration still compares something. The run ends
in `VERDICT: PASS|FAIL (N fixture(s), M failure(s))` and exits nonzero on an
empty roster, a `.spthy` no `expected.txt` line mentions, a line with no
topics, a `#!` line naming an unlisted fixture, an oracle that fails to
launch, or a fixture emptied by the two post-elaboration removals without an
`EMPTY_RUST_EXPECTATION_ALLOWLIST` entry *and* negative pins.
`crates/tamarin-parser/tests/wellformedness.rs` reads the same file offline,
and it enforces the same pins. Both harnesses check the `#!` topics against
`wf::check_theory`. Both remove the two post-elaboration topics from the
positive expectations. Both then fail a fixture that keeps neither a
parser-level expectation nor a negative pin. Only the example runner compares
against the oracle.

## Single-lemma parity

```bash
scripts/diff_proof_raw.sh \
    tamarin-prover/examples/classic/NSPK3.spthy injective_agree
```

Raw byte-for-byte diff of one lemma's `--prove` output; exit 0 = identical.
`diff_proof_raw.sh` and `corpus_raw_diff.sh` auto-build with
`cargo build --release -p tamarin-prover`; pass `TAM_RS_NO_AUTO_BUILD=1` to
diff a binary you built yourself.

All three `.hs_canon_cache/` users — `diff_proof_raw.sh`,
`corpus_raw_diff.sh` and `corpus_full_trace_diff.sh` — key on the oracle
fingerprint, so a rebuilt oracle is a MISS rather than a stale hit, and their
flagless entries are exchanged (a `diff_proof_raw.sh` run under the file's
canonical flags salts `__f` into the key and stays distinct). All three carry
the gates' `oom_prologue` as well — as does `triage_diff_vs_hs.sh` — so a
prover that outgrows the 24 GiB cap dies alone.

## Corpus gate (the batch parity metric)

```bash
cargo build --release
RESULTS_TSV=/tmp/gate.tsv scripts/corpus_file_diff.sh    # ALLOWLIST defaults to the 432-file corpus
```

Ends in `DONE_CORPUS_FILE_DIFF verdict=OK files=<n>` and exits 0, or names
what is wrong (`DIFF=n`, `RC_DIFF=n`, `SKIPPED=n`, `ROW-COUNT=n/432`) and
exits nonzero. There is nothing to tally by hand: the script prints its own
`=== SUMMARY ===` histogram, and the verdict additionally covers the failure
modes a histogram cannot show you — files whose bytes were never compared,
files that produced no row at all, and files whose bytes matched under a
different exit status (`RC_DIFF`; the oracle's rc is cached as `<key>.rc`
beside its stdout). The summary's `RC_UNKNOWN=n` counts entries filled before
that channel existed and is deliberately not a failure.

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
(30 s), `CORPUS_ROOT`, `CACHE`, `HS_PATH`, `RS_PATH`, `FLAGS_MAP`,
`MAUDE_PATH`. It resolves one maude up front and exits 2 when nothing
resolves: an oracle run without maude fails at load, and Phase 1 would write
that as a sticky `.nohs` marker the next run would honour.

**Budget for it.** `JOBS=4` is a memory bound, not a leftover: four
concurrent oracles at `-N4 -M11g` plus four Rust provers is up to ~44 GB of
GHC heap. It carries the shared `oom_prologue` — `oom_score_adj=1000` plus a
24 GiB `ulimit -v`, inherited by every child — as do the two fast gates and
the triage tools that run provers, so a runaway prover dies alone. The ceiling
is still yours to respect: on a constrained box lower `JOBS` rather than
raising it.

**Cache keys carry the oracle.** `.hs_file_cache/` and `.hs_pretty_cache/`
entries are named
`<sha256(theory)>[__i<12 hex sha256(include shas)>][__f<12 hex sha256(flags)>]__b<12 hex sha256(HS_FP)>.<suffix>`
— the `__i` component (present only on `#include`-carrying theories) digests
every included file, transitively — where `HS_FP` is `stat -c '%s.%Y'` of the
oracle binary — `gate_common.sh`'s
`hs_fingerprint`, the one definition every cached gate sources. A rebuilt
oracle, whether a bump or a
`patches/tamarin-prover-fixes.patch` edit re-applied by `./setup.sh testing`,
is a clean MISS per entry rather than a silently stale hit. Nothing is archived
and nothing is wiped: `bump_submodule.sh` deliberately leaves the caches in
place. Both fast gates therefore need the oracle binary even on a warm cache —
its fingerprint is part of the address — and exit 2 without one,
`NO_HS_FILL=1` included.

**Run the migration once.** Entries written under the pre-fingerprint key are
unreachable. `scripts/migrate_hs_cache_fp.sh` renames them onto the current
names — `mv` only, it never runs the oracle — and must run before the next
gate run, or the caches regenerate from scratch. It refuses (exit 2) unless
the checked-out oracle is the submodule pin, since that premise is what makes
adopting the old entries legitimate;
`ALLOW_ORACLE_REV_MISMATCH=1` overrides, `DRY_RUN=1` reports without moving,
and it prints per-cache migrated/already/other-oracle/collided/unrecognised/
failed counts plus `DONE_MIGRATE_HS_CACHE_FP verdict=OK|FAILED`. It is
idempotent. Every tool that touches `.hs_file_cache/` computes the same
fingerprinted key, `triage_diff_vs_hs.sh` included, so nothing writes entries
the migration would have to chase.

One gap remains: `.hs_canon_cache/` and `.web_hs_cache/` still key an
`#include`ing theory on the includer alone, so an edit below
`testParser/include/` leaves those two serving the pre-edit oracle. The gate
caches above, the sweeps' `.hs_sweep_cache/` and `rs_ref_check.sh`'s
reference keys all digest the included files (`gate_common.sh`'s
`include_shas`).

## Fast gates (run on every build)

Both slice the *load-time* output — no `--prove` — so they cost ~45 s over
the whole 432-file corpus instead of the batch gate's tens of minutes.

```bash
scripts/wf_gate.sh        # the wellformedness WARNING block
scripts/pretty_gate.sh    # the pretty-printed `theory … end` echo
```

They share one reference cache, `.hs_pretty_cache/`, and both can fill it:

- `<key>.load.gz` is the oracle's whole stripped load-time stdout. Either
  gate's PHASE 0 writes it — one cheap no-prove oracle load per missing entry,
  `JOBS`-limited — so a bump no longer costs a 30–60 min batch refill before
  `wf_gate.sh` can compare anything. `.hs_file_cache/` is the `--prove` gate's
  alone.
- `wf_gate.sh` slices the wf block out of `.load.gz`; `pretty_gate.sh` derives
  `<key>.theory.gz` from it and skips a key only when *both* artifacts exist.
  A cache `wf_gate.sh` filled first costs `pretty_gate.sh` no oracle run at
  all; a cache holding only `.theory.gz` costs it one load per key to add the
  `.load.gz` — minutes over the corpus, not the batch gate's tens of minutes.
- `NO_HS_FILL=1` skips PHASE 0 in either: right on a warm cache, an all-`SKIP`
  (failing) run on a cold one. Both still require the oracle binary, because
  the cache key is its fingerprint.
- A `--diff` theory is marked with the sticky `<key>.nohs` and SKIPped by both
  (the port does not do `--diff`), so the outcome does not depend on which
  gate ran first. The default corpus lists no `--diff` file.
- A fill that times out is discarded rather than cached: the file reports SKIP
  (a failing verdict) and is retried, so raising the timeout fixes it with no
  cache surgery.

Env: `RS_PATH`, `HS_PATH`, `HS_CACHE`, `JOBS` (4), `FILE_TIMEOUT` (the RS
side: 120 s wf / 420 s pretty), `HS_FILL_TIMEOUT` (`wf_gate.sh`'s oracle side,
420 s — the csf26-ac AC-variant precomputation makes three files take ~170 s
to load under the oracle), `NO_HS_FILL`, `RESULTS_TSV`, `ALLOWLIST`,
`CORPUS_ROOT`, `FLAGS_MAP`, `DERIVCHECK_TIMEOUT` (30 s, matching the batch
gate — lower values make the oracle's load-sensitive derivation checks time
out under parallel fill, and the "Derivation checks timed out." block then
sits in the shared load cache as a wrong reference until those entries are
deleted), and `MAUDE_PATH`. Both resolve one maude through `gate_common.sh`
(`MAUDE_PATH` → `PATH` → linuxbrew → hard fail) and prepend *that* binary's
directory to `PATH`, so the maude an operator points them at is the one the
oracle and the port both run.

## Corner fixtures (no oracle, no proving)

```bash
scripts/divergence_fixtures/check.sh          # ~10 s, 52 fixtures
```

Behaviour that no theory under the submodule's `examples/` tree reaches, so
`wf_gate`/`pretty_gate`/`corpus_file_diff` all stay green across a regression
in any of it. Only the port runs: the oracle side is captured bytes committed
under `divergence_fixtures/expected/`, stamped with the pin they came from
(`expected/oracle_rev`) — `check.sh` refuses to run when that stamp no longer
matches the submodule pin, so a bump forces a fresh `capture.sh`. The rows
the manifest marks `diverge` must NOT match — the check asserts both sides of
a deliberate divergence, which a MATCH-only corpus gate cannot express.

It is the cheapest real assertion in the tree, and the only oracle-byte
comparison CI makes: the `test` job's `Divergence fixtures` step builds
`--profile ci --bin tamarin-rs`, puts `/opt/maude` on `PATH` (the port's own
probe does not read `MAUDE_PATH`) and runs it, ~5–10 s. `cargo test` does not.

## Flag-parity sweeps

```bash
FAMILY=1 scripts/pe_sweep.sh        # --partial-evaluation
FAMILY=1 scripts/module_sweep.sh    # -m / --output-module
FAMILY=1 scripts/json_sweep.sh      # --output-json / --output-dot
```

Load-time only (none of them proves), but the only gates that compare
**stderr** as well as stdout and rc. `FAMILY=1` is the inner-loop subset — one
representative per divergence class, seconds on a warm cache; dropping it
gives the milestone corpus. Documented residuals live in
`scripts/sweep_expected.tsv` and report as `LEDGERED`; see `scripts/README.md`
for what the ledger can and cannot excuse.

**`UNCOMPARED` is the status to watch.** A ledgered row whose outcome is ERROR,
or whose ledger entry names the `timeout/kill` symptom, terminates as
`UNCOMPARED` rather than `LEDGERED`: the ledger documents *why* nothing was
compared, it does not turn a timeout into agreement. Those rows are listed
under their own `== n row(s) UNCOMPARED ==` block and counted on the DONE
sentinel, `== DONE <sweep> <ts> verdict=<...> UNCOMPARED=<n> files=<n> ==` —
both fields are always present, and neither fails the verdict (`files=` is
the distinct compared-file count `rs_ref_check.sh generate` reads). On
today's ledger that is 23 rows (pe 19, json 3, module 1). Read `verdict=OK
UNCOMPARED=19` as "the rows it compared agree, and 19 were not compared".
An *undocumented* timeout is still a plain ERROR and still fails.

## CI reference gate

```bash
scripts/rs_ref_check.sh check       # exactly what CI's rs-parity job runs
```

Compares one binary's stripped `--prove` output hashes against
`scripts/ci_ref_fast.tsv` over the 365-file fast corpus, in both directions:
a run row with no reference row is a mismatch, and a reference row that never
ran is `NOTRUN`, so a trimmed `ALLOWLIST` fails instead of silently shrinking
coverage. Note what this is *not*: the reference was generated from main's own
binary, so a pass means "this branch agrees with main", not "this branch
agrees with the oracle".

`generate` rewrites the reference and is manual — needed after a deliberate
output change, a submodule bump, or a Maude version change (the pinned version
is recorded in the reference header and enforced):

```bash
scripts/corpus_file_diff.sh 2>&1 | tee /tmp/fullgate.log
scripts/rs_ref_check.sh generate --certified-by /tmp/fullgate.log
```

**`--certified-by` is required, and it must be a comparing gate's log.** The
named file's last `verdict=` line must read exactly `verdict=OK` AND carry a
known comparing-gate sentinel — `wf_gate:`, `pretty_gate:`,
`DONE_CORPUS_FILE_DIFF`, or a sweep's `== DONE` line; anything else is
refused, `rs_vs_rs_diff.sh`'s `DONE_RS_VS_RS` (proves nothing about Haskell)
and `migrate_hs_cache_fp.sh`'s rename log (never runs the oracle) by name —
AND carry `files=<n>` covering at least every file being baselined, so an OK
from a `FAMILY=1`/narrowed-`ALLOWLIST` run cannot certify the unscoped
corpus. The log's path, its verdict and `HS_PATH`'s fingerprint — revision-
checked against the submodule pin (`gate_common.sh`'s `oracle_rev_check`,
`ALLOW_ORACLE_REV_MISMATCH=1` to override) — are stamped into the reference
header beside `# maude:`. Without all that, `generate` would launder whatever
this binary does today into the baseline. `rs_ref_check.sh`'s own
`DONE_RS_REF_CHECK` line carries no `verdict=` token, so it cannot certify
itself. `generate` also refuses to write a reference with fewer rows than
files, rejects unknown arguments, and aborts on an `ALLOWLIST` resolving to
zero entries (as does `check`).

## Refactor inertness (RS-vs-RS)

For "this refactor must not change output" checks, no Haskell needed:

```bash
PRE=/tmp/rs-prepatch POST=/tmp/rs-patched scripts/rs_vs_rs_diff.sh
```

Runs two Rust binaries (pre/post) over every example and diffs stripped
stdout; agreement everywhere means the change is behaviorally inert and
inherits the baseline's HS-faithfulness by transitivity.
`scripts/triage_diff_vs_hs.sh` then 3-way-triages any DIFF files against
Haskell output (moved toward HS or away?). It reads and fills the batch gate's
`.hs_file_cache/` at the same fingerprinted key, and runs all three binaries
under the file's canonical `file_flags.tsv` flags — the same flags the sweep
that flagged the file used — so the comparison is like-for-like and an entry
it writes is one `corpus_file_diff.sh` will reuse. It needs the oracle binary
present even on a warm cache (the fingerprint is part of the key) and exits 2
without one. Env: `PRE`, `POST`, `HS`, `CACHE`, `FLAGS_MAP`, `FT` (300 s),
`DERIV` (30 s), `CORPUS`.

The transitivity argument needs *agreement everywhere*, and the script checks
it: `DONE_RS_VS_RS verdict=<...>` folds in DIFF, `ERROR_*`,
`TIMEOUT_*`, `NOFILE`, `EMPTY_BOTH` and a `ROW-COUNT` shortfall against the
allowlist, and the exit status carries it. `TIMEOUT_BOTH` is fatal too —
"neither binary finished" is a statement about the cap, not evidence of
inertness — and it is listed in the `=== needs attention ===` block.
Practical consequence: a full-corpus `--prove` sweep at the default 180 s cap
reports red until you raise `TIMEOUT` or narrow `ALLOWLIST`. An empty file
list is `exit 2`, and so is an environment with no resolvable maude — every
run would fail fast on both sides and be scored `ERROR_BOTH`, which is a
sweep that compared nothing.

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
(`web_crawl.py` / `web_normalize.py` / `web_diff.py`). HS crawl manifests are
cached content-keyed under `scripts/.web_hs_cache/`, each with a
`<sha256>.hs.fp` sidecar naming the oracle that produced it; an unstamped or
foreign-stamped manifest is re-crawled rather than reused, so the first run
after an oracle rebuild re-crawls the whole HS side (hours on the 77-file
milestone list). Env knobs: `FILE_TIMEOUT`, `READY_TIMEOUT`, `HS_PORT`,
`RS_PORT`, `MAX_NODES` (400 proof-node visits per theory), `CACHE`,
`DIFFDIR`, `DERIVCHECK_TIMEOUT`, `SERVER_MEM_KB` (per-server address-space
cap, 24 GiB), `HS_PATH`, `RS_PATH`, `MAUDE_PATH`, `CORPUS_ROOT`,
`TAM_RS_NO_AUTO_BUILD` (it rebuilds the port by default, unlike every other
gate), `WEB_LEDGER` (default `scripts/websweep_ledger.tsv`; the literal `none`
runs without one, which makes every DIFF undocumented by definition) and
`FAIL_ON_CAPPED`.

**Its exit status reports divergence as well as vacuity.** DIFF and
`MISSING_*` rows are matched mechanically against the residue ledger
`scripts/websweep_ledger.tsv` (path / class / symptom / note): a documented row
rewrites to `LEDGERED` and carries its class in the results TSV's new 7th
column; anything left fails as `UNDOCUMENTED=n`. `SKIP_*` rows and files with
no comparison row fail as vacuity (`NO-COMPARE=<missing>/<N>`), and ledger
entries that excuse nothing fail as `LEDGER-UNMATCHED`. A malformed or
unreadable ledger aborts with `exit 2` before any crawling. The line reads
`DONE_WEB_PARITY verdict=<...> capped=<N>`; `CAPPED_HS`/`CAPPED_RS` rows (a
crawl truncated at `MAX_NODES`) are always reported and fail only under
`FAIL_ON_CAPPED=1`. `scripts/websweep_residual.txt` is the milestone crawl
list; the machine-checked residue lives in the ledger.

`scripts/pane_byte_check.sh` is the byte-exact companion for the
`main/message` and `main/rules` panes:

```bash
scripts/pane_byte_check.sh <file-list>          # or ALLOWLIST=<file-list> ...
```

The file list is **required** — no argument is `exit 2`, because the old
default was `websweep_residual.txt`, exactly the set where a DIFF is expected.
It ends in `DONE_PANE_BYTE_CHECK verdict=<...>` and exits nonzero on DIFF,
`MISSING_*`, any `SKIP_*` and any `FILE-COUNT`/`ROW-COUNT` shortfall, so a
missing `.web_hs_cache/` (all rows `SKIP_NO_CACHE`) is a red run rather than a
clean-looking histogram. It reads the same `.hs.fp` sidecar and cannot
re-crawl, so a manifest from another oracle is `SKIP_STALE_CACHE`; it needs
the oracle binary present to check that, even though it only boots the port.

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

`scripts/gate_common.sh` is the shared core underneath them: the gates, the
three flag sweeps (via `sweep_common.sh`) and the cache-touching triage tools
source it for the OOM prologue, the three strip policies, `flags_for`/`ckey`,
`hs_fingerprint`, the gate file list, the maude resolver and the
stale-binary / oracle-revision preflights. A consumer that cannot read it
exits 2 rather than running with a private fallback.

**Gates**

| Script | Purpose |
|---|---|
| `corpus_file_diff.sh` | the ground-truth batch byte gate (cached HS, per-file) |
| `wf_gate.sh` | wellformedness block, 432 files, off the shared no-prove load cache |
| `pretty_gate.sh` | `theory … end` echo, 432 files, same cache, fills it too |
| `divergence_fixtures/check.sh` (+ `capture.sh`, `fixtures.tsv`) | corners the corpus cannot reach; no oracle, no proving — CI's only oracle-byte comparison |
| `pe_sweep.sh` / `module_sweep.sh` / `json_sweep.sh` (+ `sweep_common.sh`) | flag parity: stdout, stderr and rc |
| `rs_ref_check.sh` | CI's gate: output hashes vs `ci_ref_fast.tsv` (RS-vs-RS, not oracle) |
| `capture_cli_refs.sh` | captures the oracle stdout `cli_e2e.rs`'s flag pins compare against |
| `web_parity.sh` (+ `web_crawl.py`, `web_normalize.py`, `web_diff.py`) | interactive-mode gate |
| `pane_byte_check.sh` | byte-exact pane HTML vs the web cache; file list required |
| `rs_vs_rs_diff.sh` / `triage_diff_vs_hs.sh` | refactor-inertness sweep + 3-way triage |

**Data files**

| File | Purpose |
|---|---|
| `parity_corpus.txt` | canonical 432-file corpus list |
| `parity_corpus_fast.txt` | 365-file CI subset (every file proving in ≤1.5 s) |
| `file_flags.tsv` | per-file extra prover flags, applied to both sides |
| `ci_ref_fast.tsv` | committed output-hash reference for `rs_ref_check.sh` |
| `sweep_expected.tsv` | the flag sweeps' residual ledger (applied mechanically) |
| `pe_family.txt` / `module_family.txt` / `json_family.txt` | `FAMILY=1` subsets |
| `websweep_residual.txt` | the web milestone crawl list (residue itself is ledgered below) |
| `websweep_ledger.tsv` | the web gate's residue ledger (applied mechanically) |
| `crates/tamarin-prover/tests/fixtures/cli_refs/cases.tsv` | the argv table both `capture_cli_refs.sh` and `cli_e2e.rs` read |

**Triage**

| Script | Purpose |
|---|---|
| `diff_proof_raw.sh` | one lemma, raw HS↔RS diff |
| `corpus_raw_diff.sh` | raw per-lemma diff across the corpus |
| `compare_parity_tsv.py` | compare two gate TSVs by (file, lemma) |
| `diff_maude_io.sh` / `diff_aes_calls.sh` | Maude-IPC and eq-store call-site diffs |
| `diff_proof_tree.sh` / `canon_proof_tree.py` / `corpus_diff_proof_trees.sh` | structural proof-tree diffs, pre-byte-parity era; superseded by the byte gates and only worth reaching for when output diverges too grossly to read |
| `corpus_full_trace_diff.sh` / `canonicalize_trace.py` / `diff_trace.py` | canonicalised `[EXEC]` trace diffing; the most detailed comparison |

**Maintenance**

| Script | Purpose |
|---|---|
| `bump_submodule.sh` | submodule bump: patch rebase, oracle rebuild, cite remap, 6-step re-certification checklist (the caches self-invalidate, so none is archived) |
| `migrate_hs_cache_fp.sh` | one-time re-keying of the HS caches onto the fingerprint-bearing names |
| `bench.sh` | RS-vs-HS wall-clock + memory tables (`--write` regenerates the README block) |
| `check_hs_cites.py` / `remap_hs_cites.py` / `extend_anchor_citations.py` | upstream line-cite validation and remapping |
| `gen_license_headers.py` (+ `header_identities.json`) | GPL notice maintenance (`--check` for staleness) |
