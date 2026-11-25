# Testing the Rust port

How the port is verified against the Haskell prover, from unit tests up to
full-corpus byte parity. Commands run from the repository root unless noted;
the pristine Haskell sources and the examples corpus live in the
`tamarin-prover/` submodule.

## Prerequisites

**Supported host.** The shell harness currently supports GNU/Linux and is
exercised on Ubuntu in CI. macOS is not currently supported: the scripts rely
on Bash 4.3+ and GNU/Linux utilities and interfaces including `sha256sum`,
`stat -c`, `timeout`, `setsid`, `flock`, `nproc`, GNU `xargs`, and `/proc`.
Installing individual GNU tools with Homebrew is therefore not yet a supported
configuration.

On Ubuntu or Debian, install the harness's system tools with:

```bash
sudo apt-get update
sudo apt-get install bash build-essential ca-certificates coreutils curl \
    diffutils findutils gawk git graphviz grep gzip libgmp-dev pkg-config \
    procps python3 sed unzip util-linux zlib1g-dev
```

You also need a stable Rust toolchain (including Cargo, rustfmt and Clippy),
Stack for `./setup.sh testing`, and Maude; Maude 3.5.1 matches CI. Set
`MAUDE_PATH` if Maude is not installed at a location described below.
GNU `time` is required only for `scripts/bench.sh` (`sudo apt-get install time`),
and `lld` is an optional but substantially faster linker for the full Rust
suite (`sudo apt-get install lld`).

The server embeds its GUI at compile time. Install Node.js 22.12+ or 24+ and
npm. Cargo initializes a missing submodule and builds the frontend automatically
when building or testing the workspace. It rebuilds the frontend when its sources
or build configuration change; the first build needs network access for missing
Git and npm dependencies.

**The Haskell oracle.** `./setup.sh testing` materialises a patched copy of
the prover at `tamarin-prover-testing/` (the submodule itself is never
modified). That directory is disposable: when its revision differs, setup
resets it to the current branch's submodule pin while retaining its ignored
`.stack-work/` compiler cache. Parity scripts auto-discover the binary under
`tamarin-prover-testing/.stack-work/`; set `HS_PATH` to point them at a
specific binary instead. A byte-identical copy of the setup-built binary is
accepted using the fixed attestation retained under `.stack-work/`; a genuinely
different binary needs its own adjacent `.tamarin-rs-oracle` attestation or the
explicit `ALLOW_ORACLE_REV_MISMATCH=1` waiver.

**A current release build.** Every gate refuses an in-tree `target/` binary
that predates Cargo's recorded inputs (`rs_stale_check`). A deliberately
external/sealed `RS_PATH` is content-fingerprinted against replacement during
the run, but its source provenance cannot be inferred from this checkout and
remains the caller's responsibility. Build before you gate:

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
  overridden by it. `capture_cli_refs.sh` is the deliberate exception: it walks
  the Rust test harness's own ladder because its captures must use the maude
  `cli_e2e.rs` will.

  The resolved binary's own directory is prepended to `PATH`, which is how the
  children pick it up: the flag sweeps pass `--with-maude` outright, and
  everything else lets each engine resolve by name — the oracle straight off
  `PATH`, the port only after trying `/usr/local/bin/maude` and
  `/usr/bin/maude`, so a host carrying either of those hands the port that one
  whatever the script resolved (this box has neither).

  Two things are plain `PATH` lookups: `dot`, which the web servers
  invoke by name, and the per-lemma triage tools (`diff_proof_raw.sh`,
  `corpus_raw_diff.sh`, `triage_diff_vs_hs.sh`),
  which run the provers on whatever they inherit. On hosts where these come
  from linuxbrew and it is *not* on `PATH` by default:

  ```bash
  export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
  ```

- *The Rust suite* resolves maude in one place: `tamarin-test-support`, a
  dev-dependency of every crate that has a maude-gated test. Its
  `require_maude_path` probes `$MAUDE_PATH` → `/usr/local/bin/maude` →
  `/usr/bin/maude` → `$PATH` → `/home/linuxbrew/.linuxbrew/bin/maude` →
  `/opt/homebrew/bin/maude`, and **panics** when none of them resolves rather
  than skipping. A `MAUDE_PATH` that is set but names a missing file is an
  assertion failure. The binary under test resolves its own default
  separately, and reads no environment variable — `default_maude_path`
  (`tamarin-prover/src/run.rs`) walks the two `/usr` paths and then a bare
  `maude` for the OS to find on `$PATH`. Setting `MAUDE_PATH` is what makes
  the two agree:

  ```bash
  MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace
  ```

  `TAM_ALLOW_NO_MAUDE=1` is the escape hatch: it turns the panic back into a
  skip, and is the only way a machine with no maude at all gets a green run.

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

### Parser-error diagnostics

Rust's user-facing parser diagnostics intentionally do not reproduce Haskell's
parsec/GHC exception text. Errors retain semantic failure classifications and
source spans; legacy Parsec state and GHC call-site metadata have been removed.
`Display` uses the plain-text diagnostic renderer. Batch and web surfaces render
these classifications (for example unknown applications, wrong arity, reserved
names, malformed attributes and include errors) with compact byte spans. They borrow
the root source rather than copying the whole input into each error value. An
error inside an included file retains that file's path and contents, because
the root source cannot render its labels correctly.

Unknown names in a `builtins:` block are rejected. This intentionally follows
the upstream builtin table rather than the port's former accept-and-ignore
fallback, so a Tamarin submodule update that adds a builtin must update the
Rust table and its parser tests in the same change.

The focused regression suites are:

```bash
cargo test -p tamarin-parser --test structured_errors --test lookup_arity_errors
cargo test -p tamarin-prover parser_diagnostic_ --lib
cargo test -p tamarin-server --test routes_upload
```

The parity gates still require matching acceptance, exit status, and successful
`--prove` output. They deliberately do not require byte-identical parser-error
stderr. The flag sweeps recognize Rust's `error:` header followed by a codespan
source-location line and normalize that frame along with
Haskell's Parsec header plus `unexpected`/`expecting` lines. They retain any
unrecognized lines, including runtime errors before or after a diagnostic.
Unrecognized Haskell semantic-message formats remain visible for review rather
than being silently treated as parser presentation. Focused normalization tests
run as part of `python3 scripts/test_web_harness.py`.

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
| `scripts/divergence_fixtures/check.sh` | 55 corner fixtures vs committed oracle captures (CI runs this too) | ~10 s |
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
| `ALLOWLIST=<filelist> scripts/web_parity.sh` | interactive-mode gate: crawl + HTML byte comparison |
| `scripts/bench.sh` | performance tables (see [results](docs/PERFORMANCE.md)) |

**CI enforces `cargo fmt`, clippy,
`cargo test --workspace`, the 18-file wellformedness roster,
`scripts/divergence_fixtures/check.sh`, and `rs_ref_check.sh check`.** It runs
no live Haskell binary. The divergence step compares 55 corner cases with
committed oracle captures (and rejects a submodule bump without a recapture),
while wellformedness and several unit suites also pin committed oracle output.
`rs_ref_check.sh` compares this branch's hashes with `ci_ref_fast.tsv`, whose
proof bytes and exact input scope were certified by a successful live-oracle
gate when the reference was generated. CI does not rerun that oracle. Tests
requiring a live oracle skip when it is absent, as it is in CI; parity outside
the committed fast corpus remains a local property established by the gates
above.

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

### GUI browser regression

The HTTP route tests compare HTML and graph data; browser coverage also checks
that the JavaScript loads and actually draws graphs. CI runs this after the
Rust suite. To run it locally:

```bash
cargo build --profile ci --bin tamarin-rs
npm install --prefix target/gui-browser-test --no-audit --no-fund --no-save playwright@1.63.0
target/gui-browser-test/node_modules/.bin/playwright install chromium
node scripts/test_gui.mjs
```

Use `RS_PATH` to select another binary and `CHROMIUM_PATH` to use an existing
Chromium installation. Maude and Graphviz must be on `PATH`. The test copies
only the binary to a temporary installation, launches from an
unrelated theory directory, and checks page loading, an autoproved graph in
an iframe and standalone window, and server-rendered SVG. It also checks that
a local `data/` directory cannot shadow the embedded GUI, and fails on browser
errors.

### Unit and integration suites

```bash
MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace
MAUDE_PATH="$(command -v maude)" cargo test -p tamarin-theory --test oracle_solver
```

The exact test inventory evolves with the workspace; use Cargo's summary as
the authoritative count. Tests carrying `#[ignore]` are omitted by an
ordinary run. CI uses `--profile ci`, and it is the profile to
prefer locally: it is release optimisation without fat LTO, which the release
profile would re-run at every one of the ~44 test-binary links. Each profile
also gets its own target tree, so alternating between plain `cargo test`
(dev), `--release` and `--profile ci` builds the suite three times over —
`target/debug` alone runs to tens of gigabytes. Pick one and stay on it.

`MAUDE_PATH` is what points the binary under test at the same maude the
harness resolved; see Prerequisites. An unresolvable maude is a panic naming
`TAM_ALLOW_NO_MAUDE=1`, so no maude-gated test can report a vacuous green.
`tamarin-test-support`'s own `maude_path_is_read_in_one_place` holds that
line: it walks every `.rs` file under `crates/` and fails when any file
outside the support crate reads `$MAUDE_PATH`.

Whole-corpus structural audits live under one integration-test target so they
can share expensive theory loading:

```bash
MAUDE_PATH="$(command -v maude)" cargo test --profile ci -p tamarin-theory --test corpus_audits
```

`tests/corpus_audits.rs` registers the audit modules under
`tests/corpus_audits/`. Corpus discovery and parsing share their implementation
with the in-crate tests; each test binary keeps a process-wide, per-path
single-flight parse/elaboration cache, so concurrent audits elaborate each
theory once without serialising unrelated theories. Add another whole-corpus
audit to this target rather than creating a separate integration-test binary.

The oracle-backed cases in `oracle_solver` still skip silently when no HS
binary is reachable — the HS skip is deliberate, only the maude one was
closed. A green `oracle_solver` is evidence only on a box with both maude and
the oracle.

`crates/tamarin-server`'s suite additionally pins its committed HTTP captures
to the submodule: `haskell_captures_match_the_submodule_pin` compares
`tests/fixtures/haskell-responses/oracle_rev` against `git -C tamarin-prover
rev-parse HEAD` and fails — with no skip path — when a bump lands without
re-running `tests/capture_haskell_fixtures.sh`, which re-stamps that file on
every successful capture. The normal `scripts/bump_submodule.sh` path runs
that capture automatically after rebuilding the testing oracle. `SKIP_BUILD=1`
also skips the capture and prints a warning, so that exceptional workflow must
build the oracle and run the capture explicitly before testing or committing.

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
cargo run -p tamarin-theory --example wellformedness_fixtures
```

`-- --no-tamarin` skips the oracle pass. Each fixture under
`tests/wellformedness_fixtures/` is checked three ways: it parses, the Rust
`wellformedness::check_wellformedness` emits the topics `expected.txt`
claims for it, and `tamarin-prover` emits them too. Expectations are
positive by default; a line beginning `#!<fixture> : <topics>` is a
*negative* pin — topics that must NOT appear on either side. The run ends in
`VERDICT: PASS|FAIL (N fixture(s), M failure(s))` and exits nonzero on an
empty roster, a `.spthy` no `expected.txt` line mentions, a line with no
topics, a `#!` line naming an unlisted fixture, or an oracle that fails to
launch. `crates/tamarin-theory/tests/wellformedness_fixture_reports.rs` reads
the same file offline: it holds that roster to the fixture directory, and it
pins each fixture's whole rendered `/* WARNING … */` block against an oracle
capture under `tests/wellformedness_fixtures/reports/`.

## Single-lemma parity

```bash
scripts/diff_proof_raw.sh \
    tamarin-prover/examples/classic/NSPK3.spthy injective_agree
```

Raw byte-for-byte diff of one lemma's `--prove` output; exit 0 = identical.
`diff_proof_raw.sh` and `corpus_raw_diff.sh` auto-build with
`cargo build --release -p tamarin-prover`; pass `TAM_RS_NO_AUTO_BUILD=1` to
diff a binary you built yourself.

Both `.gate_cache/raw/` users — `diff_proof_raw.sh` and
`corpus_raw_diff.sh` — key on the oracle fingerprint, so a rebuilt oracle is a
MISS rather than a stale hit, and their
flagless entries are exchanged (a `diff_proof_raw.sh` run under the file's
canonical flags salts `__f` into the key and stays distinct). Both carry the
gates' `oom_prologue` as well — as does `triage_diff_vs_hs.sh` — so a
prover that outgrows the 24 GiB cap dies alone.
Their common key and nested-comment-aware lemma scanner live in
`scripts/proof_diff_common.sh`; oracle discovery lives in `gate_common.sh`.

Do **not** treat `.gate_cache/raw/` as a cache that must be exhaustively warmed
after every oracle rebuild. It belongs to the per-lemma triage tools above and
should be populated on demand while investigating a divergence. For the
routine post-bump milestone gate, run `corpus_file_diff.sh`: it proves all
lemmas once per theory, fills `.gate_cache/proof/`, and its byte-for-byte
comparison is stronger than canonical proof-tree comparison.

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
`scripts/.gate_cache/proof/`; the Rust binary is then diffed against the cache
— so re-runs after Rust-only changes skip the Haskell side entirely.
Theories whose upstream recipe needs extra arguments get them from
`scripts/file_flags.tsv`, applied identically to both provers.

Oracle timeout markers record the cap that produced them. A later run with
the same or a lower `FILE_TIMEOUT` reuses that result; raising the cap retries
the entry and replaces the marker or publishes the completed cache payload.
Legacy empty markers are retried once and upgraded automatically.

Env knobs (full list in the script header): `ALLOWLIST` (one relative path
per line; unset uses `scripts/parity_corpus.txt`, set-but-unreadable is
`exit 2`), `RESULTS_TSV`, `JOBS` (4), `HS_N` (RTS cores per oracle, 4),
`HS_MAXHEAP` (GHC `-M`, 11 g), `FILE_TIMEOUT` (300 s), `DERIVCHECK_TIMEOUT`
(30 s), `CORPUS_ROOT`, `CACHE`, `HS_PATH`, `RS_PATH`, `FLAGS_MAP`,
`MAUDE_PATH`. It resolves one maude up front and exits 2 when nothing
resolves. The resolved Maude path is passed explicitly to both provers, and an
unexplained empty oracle run is not cached.

`TIMING proof` lines report input-key calculation, cache reads, Rust proving,
normalization/checking and comparison, plus phase and whole-gate totals.

**Budget for it.** `JOBS=4` is a memory bound, not a leftover: four
concurrent oracles at `-N4 -M11g` plus four Rust provers is up to ~44 GB of
GHC heap. It carries the shared `oom_prologue` — `oom_score_adj=1000` plus a
24 GiB `ulimit -v`, inherited by every child — as do the two fast gates and
the triage tools that run provers, so a runaway prover dies alone. The ceiling
is still yours to respect: on a constrained box lower `JOBS` rather than
raising it.

**Cache keys carry the oracle.** `.gate_cache/proof/` and `.gate_cache/load/`
entries are named
`<sha256(tagged theory/include/oracle/flags identity)>__e<12 hex execution>__b<12 hex oracle>.<suffix>`.
The full input digest covers every included file transitively plus executable
oracle contents/modes and flags. The execution digest covers the Maude version
and the derivation timeout; the oracle digest comes from `hs_fingerprint`.
A changed
oracle, whether a bump or a `patches/series` edit re-applied by
`./setup.sh testing`, is a clean MISS per entry rather than a silently stale
hit. Nothing is archived and nothing is wiped: `bump_submodule.sh`
deliberately leaves the caches in place. Both fast gates therefore need the
oracle binary even on a warm cache —
its fingerprint is part of the address — and exit 2 without one,
`NO_HS_FILL=1` included.

`./setup.sh testing` writes a source attestation beside that binary and at a
fixed location under `.stack-work/`: the submodule pin, the ordered
patch-series SHA-256 and the binary SHA-256. `oracle_rev_check` verifies all
three, and therefore accepts a byte-identical `HS_PATH` copy without trusting
an arbitrary unstamped binary. This distinguishes the intended patched oracle
from a dirty-worktree build whose `Git revision:` happens to have the same base
commit. When the generated source tree and attested binary are already current,
setup skips the timestamp-changing relink entirely.

**Older cache generations stay safe and separate.** Current Haskell-output
keys cover the oracle release/revision and patch series, Maude version and
derivation-check timeout. Format-4 web profiles additionally cover Graphviz,
the crawler's explicit `PLAN_VERSION`, its URL-key helper's source hash, and
the loaded shell protocol that stages and invokes a crawl.

Unlike format 3, format 4 does not use the crawler's entire source hash to
select persistent entries. Bump `PLAN_VERSION` when routes, decoding,
redirect/error handling or stateful request ordering change; timing and
scheduling changes to independent reads do not require a bump. The full
crawler source hash still detects edits during an active run. Older profiles
remain on disk for older checkouts and are not promoted automatically; any
manual migration must establish that the completed captures remain compatible.

Changes confined to `web_diff.py` or response normalization reuse the same
captures: those files guard the comparison verdict but are not cache
producers. The shell protocol hash is computed from producer functions, so
unrelated comments, cache plumbing and comparison-only edits do not strand
manifests either.

All current gate caches live under the main/common worktree's gitignored
`scripts/.gate_cache/`, in `proof`, `load`, `raw`, `sweep`, and `web`
subdirectories. Linked worktrees therefore reuse exactly the same pool.
`TAMARIN_RS_CACHE_ROOT` overrides the common root. On first use, a legacy
cache in the main checkout is renamed into an absent destination; caches in
other linked worktrees are left untouched and reported for manual import.
The Rust executable is intentionally outside the Haskell cache key, so a Rust
rebuild retains the expensive oracle entries. Gates fingerprint it separately
and refuse any verdict whose Rust binary changed during the comparison.

The raw, web, proof, load and sweep caches, plus `rs_ref_check.sh`
references, all digest included files transitively and executable oracle
inputs. Tool identities use versions (plus the Haskell revision and patch
series), so platform-specific rebuilds do not invalidate the cache. Executable
hashes only guard in-flight replacement and source attestations. Unchanged
executable metadata avoids repeated hashing; a metadata change triggers a
content check. The web cache stages both dependency classes through one helper
shared by both consumers.

Dependency discovery unions the hidden parser-backed `tamarin-rs input-manifest`
mode with a conservative parser-independent scan of every existing lexical
include and executable quoted oracle path. The first side applies the exact
preprocessor/heuristic semantics; the second prevents a parser omission from
creating a stale cache hit. Missing active includes remain hard failures;
ordinary syntax errors use the conservative identity so intentionally
malformed parity fixtures can still compare the two provers' diagnostics.
Manifest path fields are byte-preserving hex rather than raw TSV text, so a
valid Unix filename containing tabs, newlines, or non-UTF-8 bytes cannot alias
another dependency or corrupt web staging. The parser also reports whether the
active theory declares lemmas; web crawls use that metadata to permit empty
lemma discovery only for theories without lemma declarations.
Run `./setup.sh testing` (or otherwise build `target/release/tamarin-rs`)
before the shell/Python harness checks; `INPUT_MANIFEST_BIN` may select an
equivalent development binary while working on the manifest itself.

## Fast gates (run on every build)

Both slice the *load-time* output — no `--prove` — so they cost ~45 s over
the whole 432-file corpus instead of the batch gate's tens of minutes.

```bash
scripts/wf_gate.sh        # the wellformedness WARNING block
scripts/pretty_gate.sh    # the pretty-printed `theory … end` echo
```

They share one reference cache, `.gate_cache/load/`, and both can fill it:

- `<key>.load.gz` is the oracle's whole stripped load-time stdout. Either
  gate's PHASE 0 writes it — one cheap no-prove oracle load per missing entry,
  `JOBS`-limited — so a bump no longer costs a 30–60 min batch refill before
  `wf_gate.sh` can compare anything. `.gate_cache/proof/` is the `--prove` gate's
  alone.
- `wf_gate.sh` slices the wf block out of `.load.gz`; `pretty_gate.sh` derives
  `<key>.theory.gz` from it and skips a key only when *both* artifacts exist.
  A cache `wf_gate.sh` filled first costs `pretty_gate.sh` no oracle run at
  all; a cache holding only `.theory.gz` costs it one load per key to add the
  `.load.gz` — minutes over the corpus, not the batch gate's tens of minutes.
- `NO_HS_FILL=1` skips PHASE 0 in either: right on a warm cache, an all-`SKIP`
  (failing) run on a cold one. Both still require the oracle binary, because
  the cache key is its fingerprint.
- A `--diff` theory is reported directly as `SKIP_UNSUPPORTED_DIFF` by both
  gates (the port does not do `--diff`); unsupported inputs create no cache
  state. The default corpus lists no `--diff` file.
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
deleted), and `MAUDE_PATH`. Both resolve one Maude through `gate_common.sh`
(`MAUDE_PATH` → `PATH` → linuxbrew → hard fail) and pass that exact path to
the oracle and port.

## Corner fixtures (no oracle, no proving)

```bash
scripts/divergence_fixtures/check.sh          # ~10 s, 55 fixtures
```

Behaviour that no theory under the submodule's `examples/` tree reaches, so
`wf_gate`/`pretty_gate`/`corpus_file_diff` all stay green across a regression
in any of it. Only the port runs: the oracle side is captured bytes committed
under `divergence_fixtures/expected/`, stamped with the pin they came from
(`expected/oracle_rev`) — `check.sh` refuses to run when that stamp no longer
matches the submodule pin, so a bump forces a fresh `capture.sh`. The rows
currently all require a match. The manifest also supports `diverge` rows, which
must reproduce recorded port bytes while remaining different from the oracle;
this preserves both sides of a deliberate divergence when one exists.

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
today's ledger that is 23 rows (pe 19, module 3, json 1). The three module
rows are one input tested in `spthy`, `spthytyped`, and `msr` output modes.
Read `verdict=OK
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
coverage. The reference is a committed oracle-certified snapshot, not a live
oracle run. A pass establishes agreement with those certified bytes over this
exact fast corpus; broader and newly updated oracle behaviour still needs the
local gates.

`generate` rewrites the reference and is manual — needed after a deliberate
output change, a submodule bump, or a Maude version change (the pinned version
is recorded in the reference header and enforced):

```bash
ALLOWLIST=scripts/parity_corpus_fast.txt scripts/corpus_file_diff.sh 2>&1 \
  | tee /tmp/fast-proof-gate.log
scripts/rs_ref_check.sh generate --certified-by /tmp/fast-proof-gate.log
```

**`--certified-by` is required, and it must be the proof-output gate's log.**
The named file's last `verdict=` line must be
`DONE_CORPUS_FILE_DIFF verdict=OK` and must carry the exact sorted
relpath/input-key scope being baselined, plus the oracle and execution
fingerprints. Run `corpus_file_diff.sh` with the same allowlist as the
reference generation; a wf/pretty/flag sweep or a same-sized different corpus
cannot certify proof-output hashes. The gate also certifies an aggregate of
the normalized proof bytes actually compared; `generate` refuses to write if
its newly produced rows do not have that exact aggregate. The log's path, its verdict and
`HS_PATH`'s fingerprint — revision-
checked against the submodule pin and current patch series, both of which are
also recorded in the reference and enforced directly by `check`
(`gate_common.sh`'s `oracle_rev_check`,
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
`.gate_cache/proof/` at the same fingerprinted key, and runs all three binaries
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
ALLOWLIST=scripts/websweep_residual.txt RESULTS_TSV=/tmp/web.tsv scripts/web_parity.sh  # milestone corpus
ALLOWLIST=<filelist>        RESULTS_TSV=/tmp/web.tsv scripts/web_parity.sh
```

**`ALLOWLIST` is required** — one corpus-relative path per line, or the
literal `seed` for the built-in 2-file smoke list. Unset or unreadable is
`exit 2`, not a fall-through to a default corpus.

Runs two independent theories concurrently by default (`JOBS=2`). Each worker
owns a pair of ports: the defaults use 3021/3022 and 3023/3024 for HS/RS.
Within each theory, the Haskell crawl finishes before Rust starts. Workers
claim the next theory as they become free; use `JOBS=1` to reduce memory use.

The crawler autoproves each lemma and visits proof-tree, constraint-system,
graph and source pages up to the configured proof-node cap. Autoprove and
other state-changing requests stay sequential. Read-only proof/graph pages
use `WEB_FETCH_JOBS=2` concurrent requests per server (allowed range 1–16),
with results recorded in crawl-plan order.

HTML is compared byte for byte, including tag spelling, attribute order,
highlighting and whitespace. Only environment fields such as versions,
timestamps, theory indices and work-directory paths are normalized; malformed
markup is preserved rather than repaired. JSON envelopes additionally allow
different key order and encoding. Graph and plain-text responses retain their
byte comparisons apart from environment fields.

Both engines receive the per-theory interactive recipe from
`scripts/web_flags.tsv` (`WEB_FLAGS_MAP` overrides it), and those flags are
part of the input key. The auto-sources examples use `--auto-sources`, as
upstream's interactive instructions require; Rust also honors the equivalent
in-file configuration block. Unsupported flags fail explicitly.

HS crawl manifests are cached in profiles under `scripts/.gate_cache/web/`.
`web_cache.sh` selects a
profile from oracle, Maude and Graphviz versions (including the oracle revision
and patch series), the URL-key helper's source SHA-256, the loaded shell
producer protocol, plus the derivation timeout, crawl-plan version and node cap
(not the HTTP request deadline, which cannot alter a successful complete
manifest); entry keys cover the theory, flags, transitive includes and
executable oracle inputs. Linked worktrees share the main
checkout's pool, so switching Tamarin versions automatically reselects the
corresponding cache instead of overwriting it. Per-entry locks and atomic
publication let background fills and readers safely use that shared pool at
the same time. Each manifest records its actual per-run work directory;
comparison replaces the HS and RS roots with one token, so a warm manifest
remains comparable when `WEB_WORK_ROOT` is customized or a later run receives
another `mktemp` name.

The default crawl budgets are 420 seconds for the whole file
(`FILE_TIMEOUT`) and 180 seconds for one HTTP request
(`WEB_CRAWL_TIMEOUT`). Raising either can recover a slow oracle crawl without
changing the cache profile: failed or timed-out crawls are never published,
and a successful deadline cannot change response bytes.

`web_diff.py` and the full response normalizer are comparison
inputs rather than cache producers: their hashes are checked before and after
each diff without selecting another HS profile. Diff artifacts are staged with
the result and replace their traversal-safe, hashed per-theory `DIFFDIR`
namespace only after that final check; an all-MATCH rerun removes old
diagnostics. Each importing Python process
uses a fresh per-workdir bytecode cache, so the checked source is the code that
executes. Old flat `.web_hs_cache*` entries do not attest Maude,
derivation or Graphviz identity, so they remain available to old checkouts but
are not promoted into current profiles. Both consumers use one guarded server
lifecycle that refuses an occupied port before boot and waits for release after
shutdown. Cancellation stops active probes, crawlers and servers and removes
their work directories. Both gates also reject a source whose input key changes
while it is being staged. Env knobs:
`JOBS` (2, `web_parity.sh` only), `WEB_FETCH_JOBS` (2), `WEB_FLAGS_MAP`,
`FILE_TIMEOUT`, `WEB_CRAWL_TIMEOUT`, `READY_TIMEOUT`, `HS_PORT`, `RS_PORT`, `MAX_NODES` (400
proof-node visits per theory), `WEB_CACHE_ROOT`, `CACHE` (exact-directory
override; existing manifests require a matching `PROFILE`), `WEB_WORK_ROOT` (large per-run manifests; defaults
under `target/`, not a size-limited `/tmp`),
`DIFFDIR`, `DERIVCHECK_TIMEOUT`, `SERVER_MEM_KB` (per-server address-space
cap, 24 GiB), `HS_PATH`, `RS_PATH`, `MAUDE_PATH`, `CORPUS_ROOT`,
`TAM_RS_NO_AUTO_BUILD` (it rebuilds the port by default, unlike every other
gate), `WEB_LEDGER` (default `scripts/websweep_ledger.tsv`; the literal `none`
runs without one, which makes every DIFF undocumented by definition) and
`FAIL_ON_CAPPED`.

`TIMING` lines report server startup, crawl and shutdown, crawler phases,
comparison work and total gate time. Use these to distinguish proving/fetching
cost from comparison overhead; totals depend on the corpus, cache warmth and
worker settings.

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
missing selected cache profile (all rows `SKIP_NO_CACHE`) is a red run rather
than a clean-looking histogram. It reads the same `.hs.fp` sidecar and cannot
re-crawl, so a manifest from another oracle is `SKIP_STALE_CACHE`; it needs
the oracle binary present to select and check that profile, even though it only
boots the port.

The focused harness regression checks do not need a running Tamarin server,
but start a local HTTP fixture and require permission to bind loopback sockets.
They also use the parser-backed Rust binary described above. CI runs the same
command:

```bash
python3 scripts/test_web_harness.py
```

## Algebra backends

The binary has two algebra backends. `--algebra-backend=maude`, the default,
is the oracle-compatible one every gate above measures.
`--algebra-backend=native-only` exists in a build with
`--features lean-unification` and answers from the Lean library in-process;
it starts no Maude. Build and test it with the feature on:

```bash
cargo build --profile ci -p tamarin-prover --features lean-unification
MAUDE_PATH="$(command -v maude)" cargo test --profile ci --workspace \
    --features tamarin-term/lean-unification,tamarin-prover/lean-unification
```

The CI job `lean-spec` runs the native suites; without the feature the
native tests compile to nothing or check only that the backend is refused.

### Parallel search on native-only

Parallel proof search (`--processors=N`) runs on both backends. A
native-only session has no process to lease, so the batch pipeline builds no
pool for it and every job of a search shares the session's one handle. Jobs
do not take turns on it: each answer is computed on the calling Rayon worker
(Lean's per-thread state is set up on a worker's first call; the workers have
64 MiB stacks), no lock is held across a call into the Lean library, and the
session memos sit behind their own short locks. An answer is a function of
the request alone, so a job gets the same answer whether it computes it or
reads what another job stored, and stdout and the exit status are the same
for every `--processors`, also when the backend fails (below).

A search under a cancelled scope stops inside its Lean call: the call polls
the flag of the scope its job runs under, and a request on any enclosing
token raises that flag at once. A stopped call returns no reply, so nothing
is stored, and it is a cancellation, never a failure of the session. A job
that runs into a failure after its request was cancelled records nothing
either.

A failure that a live job runs into (an unsupported request, an exhausted
search budget, an error absorbed where there is no error channel) is held by
that job, not by the session. The jobs in question are the cases of a forked
search node and the rules of the derivation checks, which run as an ordered
map (`tamarin_utils::parallel::try_map_until`) whose later items are
speculative; each item has a scope of its own
(`CancellationScope::job`) that holds its first failure.

- Inside the failed job every further backend call fails with that failure,
  and `MaudeHandle::check_backend_status` fails. Nothing the job computes
  afterwards leaves it: the session memos take no entry from a failed job,
  a source set built under one is not stored
  (`SharedOnce`, `SourceSlot`), and the job's result is the failure
  (`visit_forked` checks the status before it returns a case).
- A failed job ends the traversal of its map where a returned error would.
  If the map returns the job's result, the failure moves to the job around
  the map, and from the outermost job to the session latch, which fails the
  run with the message a one-worker run prints. If an earlier case stops
  the traversal first, the job is discarded and its failure with it.
- Work outside such a job (the main thread, a lemma of a batch, a source
  build that a lemma starts) is always wanted, and its failures go to the
  job around it or straight to the session latch, as on one worker.

So a run fails for every `--processors` exactly when it fails for one, with
the same message. `a_discarded_search_job_takes_its_failure_with_it` and
`a_failure_on_the_path_of_the_search_fails_every_number_of_workers`
(`crates/tamarin-prover/tests/native_backend.rs`) run both directions on
one and eight workers under a reduced `TAM_RS_ALGEBRA_SEARCH_WORK`.

The provenance tally (`[ALGEBRA_PROVENANCE]`, stderr) counts what the jobs
asked, so its split between fresh and cached answers, and the requests of
speculative jobs, vary with the number of workers and between runs.

### The "assumed convergent" line

On native-only a proved certifier examines the session's rewrite table. The
three built-in tables are certified; a table with user equations may not be,
and then normalization and variant answers are counted under the origin
`assumed` (`TAM_MAUDE_CACHE_STATS=1` prints the counts as
`[ALGEBRA_PROVENANCE]`, and the certifier's verdict as
`[ALGEBRA_PROVENANCE] rewrite table: certified|uncertified`). Such a run
prints, once per theory, on stderr:

```
[Theory <name>] note: the equational theory's convergence was not certified by the proved checker; results assume the user-specified equations are convergent, as Maude-based Tamarin also assumes
```

- The wording is stable (`tamarin_term::algebra_backend::ASSUMED_CONVERGENT_NOTICE`);
  match on `convergence was not certified`.
- It is printed as soon as the session's table has been built and the
  certifier has declined it, which is while the rule variants are computed:
  after `Theory translated` and before any lemma is attempted. A theory that
  leaves the pipeline early on an error still gets the line if its table was
  uncertified. Interactive mode prints it at each theory load.
- It never reaches stdout, so the byte comparisons of stdout are unaffected.
  It is a Rust-side diagnostic, so `--quiet` drops it. The Maude backend
  never prints it: Maude has no certifier and assumes convergence always.

`crates/tamarin-prover/tests/lean_unification.rs` pins all of this: an
uncertified user-equation theory prints the line exactly once, a theory of
built-ins prints none, and the Maude backend prints none.

### Interactive mode on native-only

`tamarin-rs interactive --algebra-backend=native-only <theories>` serves the
web UI from native sessions. `crates/tamarin-server/tests/routes_native_backend.rs`
drives a session over HTTP on both backends (theory page, open a lemma, one
manual proof step, autoprove from the state it reached, the finished proof,
and requests that arrive together) and compares the responses: byte for byte
on a Diffie-Hellman theory, and up to the numbering of variables on an XOR
theory, where the proved unifier may number the witnesses of an AC
unification differently from Maude (batch output differs in the same way).

```bash
MAUDE_PATH="$(command -v maude)" cargo test --profile ci -p tamarin-server \
    --features tamarin-term/lean-unification --test routes_native_backend
```

`scripts/interactive_backend_check.sh` does the same against the real binary
with `curl`: it starts one server per backend on a free localhost port,
saves every response under `scripts/results/interactive_backend/<backend>/`, stops
the server by PID and ends in `INTERACTIVE_BACKEND_CHECK verdict=OK|FAIL`.

### Backend gate

That native-only answers correctly is proved. That it answers at all, and in
reasonable time, is not, so `scripts/backend_gate.py` measures both against
the Maude backend of the same binary. It proves each theory of a list on
both backends (`--processors=1 --derivcheck-timeout=30`), every prover
process under its own memory cap and timeout, and fails when

| Status | Meaning |
|---|---|
| `VERDICT_DIFF` | a lemma's verdict, or the number of wellformedness warnings, differs from Maude's and the pair is not listed in `scripts/backend_gate/verdict_exceptions.tsv` |
| `NATIVE_FAIL` | the theory finishes on Maude but not on native-only (nonzero exit, memory cap or timeout) and is not listed in `scripts/backend_gate/pending.tsv` |
| `SLOW` | Maude takes more than `--min-ref-seconds` (1 s) and native-only more than `--max-ratio` (2) times Maude, by the minimum over `--runs` runs of each backend, and the theory is not pending |
| `REF_FAIL` | Maude itself does not finish (`--allow-ref-failures` reports it as `REF_FAIL_OK` instead) |
| `XPASS` | a pending theory now finishes within the limits: remove its line |
| `STALE_EXCEPTION` | a listed verdict exception no longer differs: remove its line |

`XFAIL` (a pending theory that still fails) and `EXCEPTION` (a listed
verdict difference, with exactly the listed verdicts) are reported and do not
fail the gate. A pending entry never excuses a verdict difference. The last
line is `DONE_BACKEND_GATE verdict=OK|FAIL ...`; the exit status is 0, 1 for
a failed gate and 2 when the gate could not run.

```bash
cargo build --profile ci -p tamarin-prover --features lean-unification
scripts/backend_gate.py --smoke      # 33 theories, about two minutes; what CI runs
scripts/backend_gate.py --full       # the 454-theory corpus; manual or nightly
scripts/backend_gate.py --list my.tsv --timeout 300 --runs 3
```

- **`--smoke`** reads `scripts/backend_gate/smoke.tsv`: fast theories over
  Diffie-Hellman, XOR, bilinear pairing, multisets, natural numbers, user
  equations and SAPIC, the native regression fixtures, and the pending
  theories. Three runs per backend where the timing rule applies, 60 s per
  process. The `lean-spec` CI job runs it after `scripts/test_backend_gate.py`,
  which tests the gate itself against a stand-in prover.
- **`--full`** reads `scripts/backend_gate/corpus.tsv`: the parity corpus,
  the remaining provable examples and the fixtures, with their per-file
  flags. One run, 300 s per process, Maude failures reported only. Add
  `--jobs N` on a machine with memory to spare and `--resume` to continue an
  interrupted run from the records in `--out`.
- A **list** holds one theory per line, relative to `tamarin-prover/examples`,
  optionally followed by a tab and extra prover flags. The pending and
  exceptions files name theories by the same path.
- **Caps.** `--mem` (6G) and `--timeout` apply to each prover process.
  `--mem-cap=auto` puts each process in a transient systemd scope with
  `MemoryMax` when `systemd-run --user --scope` works, which bounds resident
  memory and lets a timeout kill the whole scope; otherwise it sets
  `RLIMIT_AS`, as `ulimit -v` does. `--jobs` (2) bounds how many run at once.
  A pending theory's native run gets the shorter `--pending-timeout` (20 s).
- **Results** go to `scripts/results/backend_gate/<mode>/` (`--out`): stdout and
  stderr of every run, one JSON record per run (exit status, seconds, peak
  RSS, command), and `summary.tsv` with one row per theory. `--verbose`
  prints every row and `--steps` lists step-count differences, which are
  reported as `OK_STEPS` and do not fail the gate.

`pending.tsv` is currently empty. `verdict_exceptions.tsv` lists the two lemmas of
the fixture `native_ac_marker_trace`, where native-only finds a trace that
the Maude run does not and is right.

## Debugging a divergence

Work top-down: which lemma → which proof step → which solver call.

**Proof-tree diff** (canonicalised, per lemma):

```bash
scripts/diff_proof_tree.sh tamarin-prover/examples/Tutorial.spthy Client_auth
scripts/diff_proof_tree.sh <file> <lemma> "TAM_RS_DBG_APPLY_EQ_STORE=1"   # extra env for the RS run
target/release/examples/dump_proof <file> <lemma> | python3 scripts/canon_proof_tree.py
```

`scripts/corpus_diff_proof_trees.sh` runs the same diff over a small,
hand-picked regression corpus (PASS/FAIL tally).

**Diagnostic env flags** (all off by default; solving behavior is never
env-configurable — these only dump, count, verify-and-panic, or force a
reference path whose output is byte-identical):

| Variable | Effect |
|---|---|
| `TAM_RS_DBG_INTR_DUMP=1` | assembled intruder-rule cache (index, kind, budget/flags, facts) |
| `TAM_RS_DBG_SOURCES_DUMP=1` | per-source goal + refined case names after `ensure_saturated` |
| `TAM_DBG_PERFORM_SPLIT=1` | perform_split case lists (RS) |
| `TAM_RS_DBG_APPLY_EQ_STORE=1` | applyEqStore IN/OUT (RS) |
| `TAM_RS_DBG_APPLY_EQ_STORE_FILTER=substantive` | limit that dump to calls with equations or substitutions |
| `TAM_DBG_AES_VARIANTS=1` | apply_eq_store variant before→after counts |
| `TAM_RS_VERIFY_BOUNDS_CACHE=1` | panic if the bounds_max cache diverges from a full recompute |
| `TAM_RS_VERIFY_SUBST_SKIP=1` | panic if a marker-skipped `subst_system` pass was not a bit-identical no-op |
| `TAM_RS_VERIFY_FP=1` | panic if a bloom-skipped fact descent would actually have changed the fact |
| `TAM_RS_VERIFY_FACT_MAX=1` | panic if a Fact's cached `max_var` diverges from a full walk of its terms |
| `TAM_RS_VERIFY_CANON_TABLES=1` | panic if a per-store incremental canon table diverges from a full rebuild |
| `TAM_RS_VERIFY_REDUCE_NF=1` | panic if a normal-form fast path elided a Maude reduce that would have changed the term |
| `TAM_RS_NO_SIMP_NOOP_SKIP=1` | force the full Simplify pass (disable the no-op shortcut; A/B oracle) |
| `TAM_RS_NO_SOURCE_CACHE=1` | disable persistent session source-case reuse (recompute for each proof/source context; A/B oracle) |
| `TAM_RS_DISABLE_BOUNDS_CACHE=1` | force the full `bounds_max` walk (disable the cache; A/B oracle) |
| `TAM_RS_DISABLE_PARALLEL_EXPAND=1` | expand proof-tree siblings serially instead of per-child in parallel |
| `TAM_RS_KEEP_SYS=1` | keep every proof node's `System` instead of dropping the ones the search no longer needs |
| `TAM_RS_SUBST_SKIP_STATS=1` | `subst_system` call/skip counters to stderr |
| `TAM_RS_FP_STATS=1` | fact-descent bloom-skip counters to stderr |
| `TAM_RS_SIMP_NOOP_STATS=1` | Simplify no-op shortcut hit/miss counters to stderr |
| `TAM_RS_CANON_TABLE_STATS=1` | canon-table cache hit/rebuild counters to stderr |
| `TAM_MAUDE_CACHE_STATS=1` | one reduce/unify/reply cache hit-rate line per theory session at teardown, with the session's `[ALGEBRA_PROVENANCE]` tally |
| `TAM_DBG_VARIANTS=1` | every variant family as handed to the caller, one member per line, and the native solver that proposed it; compare the two backends' dumps to find a family listed differently |
| `TAM_DBG_UNIFY=1` | every unification request with its answers as handed to the caller, on either backend |
| `TAM_DBG_VARIANT_CHECK=1` | native-only: every family submitted to the Lean variant certificate checker with its member count, its charge against the work bound, the verdict and the time |
| `TAM_RS_VARIANT_CHECK_WORK=<n>` | native-only: work bound of the variant certificate checker (default 65536, `0` for none); see "Variant check budget" |
| `TAM_RS_ALGEBRA_SEARCH_WORK=<n>` | native-only: work bound of one interruptible Lean search, in questions asked (default 16777216, `0` for none); see "Search budget" |
| `TAM_RS_ALGEBRA_SEARCH_REPORT=<n>` | native-only: print to stderr every interruptible Lean call that asked at least `n` questions |
| `TAM_SATURATION_LIMIT=<n>` | source-saturation step cap; outranks the CLI `-s=` |
| `TAM_PROVE_DEADLINE_MS=<n>` | per-search wall-clock cap (co-operative) |

The `TAM_RS_VERIFY_*` hooks certify the solver's internal caches and skip
optimisations: exporting them during a full corpus-gate run re-executes every
skipped computation and panics on any divergence, turning the byte gate into a
self-check of the optimisation machinery as well. The `TAM_RS_NO_*` /
`TAM_RS_DISABLE_*` switches are the A/B complement — they force the
pre-optimisation reference path, whose output must stay byte-identical.

The table lists every Rust-side diagnostic/solver flag. Test-only dependency
escape hatches are separate:
`TAM_ALLOW_NO_MAUDE=1`, `TAM_ALLOW_NO_CORPUS=1`, and
`TAM_ALLOW_NO_DOT=1` explicitly permit the corresponding tests to skip when
that external dependency is unavailable. They should not be set for a gate.

### Variant check budget

On the native-only backend a family of variants is used only after the Lean
certificate checker accepted it, whoever proposed it: a specialised Rust
solver, the folding export, or the bounded narrowing search of the Lean
library (`tamarin_checked_variants`, which answers kind-level queries and
queries on a table the certifier did not accept). There is no switch that
skips the check and no family that bypasses it. A rejected family, and one
the checker does not decide, fail the session with "variants not certified".

The checker runs under two bounds, and it can be cancelled.

- **Work bound** (`TAM_RS_VARIANT_CHECK_WORK`, default 65536, `0` for none):
  the number of positions that are not variables at which it looks for
  narrowing steps, added up over the members of the family in their listed
  order (the family's *charge*, which `TAM_DBG_VARIANT_CHECK=1` prints). The
  members within the bound are checked; unless that is the whole family, the
  reply is "variants not certified: out of budget". The largest charge among
  the 9593 checks of the 449 corpus theories that finish is 4204 (320
  members, `idbased/BP_IBS_3`, 6.3 s), so the default leaves a factor of
  fifteen. The contract limits this reply exactly: status 3 with a nonzero
  work bound implies that the bound is below the charge or that a term the
  check has to normalize has a rewrite path as long as the depth
  (`theoryVariantCheck_decides`, clause `exhausts`).
- **Search bound** (`TAM_RS_VARIANT_CHECK_SEARCH`, default 67108864 = 2^26,
  `0` for none): the checker asks before every member, before every
  narrowing successor and inside every unification, matching and reduction
  it runs whether to go on (`lean/Tamarin/Interrupt.lean` in
  tamarin-algebra). A call that has asked more often is stopped and fails the
  session with "out of budget: one Lean variant check was stopped after N
  search steps"; it is never an answer. The count is a function of the
  request, so the bound is deterministic. The largest check of the corpus
  sample asks 1,456,150 questions (`idbased/BP_IBS_3`), so the default leaves
  a factor of 46; `TAM_RS_ALGEBRA_SEARCH_REPORT=<n>` prints every call that
  asks at least `n`.
- **Cancellation.** The same questions are answered "stop" as soon as the
  request's cancellation token is set. The call returns no reply, the error
  is the ordinary "request cancelled", and the session stays usable.

The search bound is what stops a family whose cost is inside the unifier,
which the charge does not see. The 247-member family of
`LIST(x*x.1, x*inv(x.1))` has a charge of only 1958 and was not checked in
900 s (7.7 GB). It now returns within 0.1 s of a cancellation (39 ms and
71 ms measured) and is stopped after about 3 s by a search bound of 2^20
(`interruption::a_runaway_variant_check_stops_when_its_request_is_cancelled`,
`..._stops_at_its_search_bound`). The folding search on `mult('c',w,w,y)`,
which a fuzzing run found deaf to its cancellation, returns 4 ms after it
(`a_runaway_variant_search_stops_when_its_request_is_cancelled`). The check itself is no faster:
`mult('c',x,x,x)` over Diffie-Hellman exponents still takes about 5 s for 8
variants where Maude takes 0.3 s, and the ignored test
`signed_graph_joint_product_and_quotient_share_all_valued_witnesses` remains
the acceptance test for a checker that finishes the 247-member family.

A kind-level AC product, one that holds a factor outside the sort of its
operator (no well-sorted theory produces one, and the corpus has none), used
to cost the closure test time and memory proportional to 2^k in its width
`k`. The narrowing layer now sets aside only sub-products of the factors
outside the sort, so the cost is independent of the width: 129 public names
and one Node variable check in milliseconds
(`kind_level_product_check_is_not_exponential`). It is still exponential in
the number of factors outside the sort; the search bound stops such a call.

A sorted query that no specialised Rust solver covers (`fst(x^z)`,
`sdec(x, y^z)`, `inv(x XOR z)`, a product that is not in normal form) gets its
family from the Lean proposer `tamarin_fold_variants`: folding variant
narrowing in the order of Maude's search, which lists Maude's family on these
queries (`TAM_DBG_VARIANTS=1` prints `solver fold` and the time of each call).
The search ends only on a table with the finite variant property, so it runs only
on a table the certifier accepted (all builtin tables, and every table of
constructor-pattern rules whose results are subterms or constants, which the
certifier is proved to accept); on any other table, and on a kind-level
query, the proposal comes from the bounded narrowing search
(`solver checked_export`). The folding search runs under a bound on its narrowing sites that starts at 8192 and grows
fourfold while a call reports it exhausted. A call is interruptible like the
checker: it stops on cancellation and at the search bound above
(`TAM_RS_VARIANT_CHECK_SEARCH`, "out of budget: one Lean variant search was
stopped after N search steps"). Beyond 524288 sites the session
fails with "variants not found: out of budget". The
families of the regression queries (up to 96 members) need fewer than 4000
sites. Regressions: `folding_proposes_the_variants_no_specialised_solver_covers`
(`tamarin-term`) and `folded_rule_variants_prove_the_traces_without_maude`
(`tamarin-prover`).

### Search budget

On the native-only backend ordinary unification, its existence decision and
the single-path reducers are Lean exports whose searches can take time, and
for unification memory, exponential in the width of an AC product. One such
call used to be uninterruptible. Each of these exports now asks its caller
before every step of a search whether to go on (`lean/Tamarin/Interrupt.lean`
in tamarin-algebra), and the C bridge answers "stop" from then on as soon as

- the request's cancellation token is set (a timeout, a cancelled sibling of
  a parallel search), or
- the call has asked more questions than its work bound.

A stopped call returns no reply. Cancellation surfaces as the ordinary
"request cancelled" and leaves the session usable. The work bound fails the
session with "out of budget: one Lean unification was stopped after N search
steps" (or "reduction", "unifiability decision"); it is never an answer, and
never a shorter family. The number of questions a call asks is a function of
its request, so the bound is deterministic.

The default bound is 16777216 questions (`TAM_RS_ALGEBRA_SEARCH_WORK`, `0` for
none). Over the 449 corpus theories that finish, the largest call asks 11967
questions (a unifiability decision of `sp14/group_joux`); the largest
unification asks 6331 (`TAK1`) and the largest reduction 1906 (`wireguard`),
so the default leaves a factor of 1400. `TAM_RS_ALGEBRA_SEARCH_REPORT=<n>`
prints every call that asks at least `n`. What the bound buys on the runaway
calls of the fuzzing campaign (one call each, optimized build; the
fuzzer's watchdog resolves 0.1 s, the tests measure the two exact figures):

| request | before | cancelled | at the default bound |
| --- | --- | --- | --- |
| unify `i+i+i+i+j+j+j+n = l+l+l+m+m+m+k+k` over naturals | no reply; 7.6 GB after 8 s | returns 54 ms after a cancellation at 0.3 s (136 MB), 0.4 s after one at 2 s (0.8 GB, the time to release it) | "out of budget" after 1.2 s at 0.4 GB |
| unify `merge(v,v,w,w,w,w) = merge(z,y,x)`, user AC symbol | no reply; 4.7 GB after 30 s | within 0.1 s of a cancellation at 0.3 s, 0.6 s after one at 5 s (1.3 GB to release) | "out of budget" after 1.2 s at 0.4 GB |
| unifiable `'a'+u+u+u+y+y+y+y = x+x+x+z+z+z+w` | answers after 1.9 s, deaf to a cancellation at 1 s | returns within 0.1 s of the cancellation | answers (144513 questions) |
| reduce `select(pair(f0+…+f63, hash(x)), other)`, rule with a product of three variables | no reply in 45 s at 15 MB, when the run was killed | returns 0.2 ms after the cancellation | "out of budget" after 15 s at 15 MB |

A question costs the first-match search of the reducers about fifteen times
as much time as it costs the enumeration of the unifier, which is why the
same bound is spent in 15 s there and in 1.2 s here.

The questions sit where the measured runaway calls spend their time (the
first-match search of the bag matcher, the selection of basis solutions and
the answers built from them, the frontier of the component search and the
partition fallback). Nothing proves that every long loop asks: a call that
is slow somewhere else still returns only when it is done. Matching
(`theory_match`, `theory_match_exists`), table certification and the proposers
other than the folding search are not interruptible. The variant checker and
the folding search are: see "Variant check budget".
The tests are `interruption::*` in `crates/tamarin-term/tests/native_backend`.

### What Rust does with a unifier

On the native-only backend the answer to a unification request is computed and
named in Lean. Rust walks trees in both directions and decides nothing:

- **The request** (`Packet::encode_total`) lists the rows of the term graph,
  with variables and constants numbered by first occurrence and operators by
  the fixed ids of the session's theory description (`Theory`, see
  `lean/Tamarin/Theory.lean` in tamarin-algebra): the builtin flags, the
  arities of the other free symbols and the number of user AC symbols. Lean
  builds the declarations from that description.
- **The reply** of `tamarin_lean_theory_unify` is not read on its own. Its
  words go to no decision except "does the family have a member"
  (`family_has_member`, the one place that reads a stored family for the
  existence question).
- **The names** of the variables in the range of an answer come from
  `tamarin_lean_name_unifiers`. Rust sends it the name hint and index of every
  request variable and receives a table for each answer, and
  `read_named` reads the reply through the tables as the Lean library
  specifies (`UnifierNames.apply`): a variable token is the variable its
  entry names, a binding to a variable that stands for its own request
  variable is left out, and anything the tables do not cover is an error.
  The contract theorem is about what this reading returns.
- **Maude's names** are proposed, not applied. `unifier_presentation` computes
  the names the Maude backend composes and sends them as a proposal. The
  export takes them when they rename each answer injectively and apart from
  the request, and the answer keeps them when it is then read back as the
  composition; otherwise every range variable is called `x` and numbered
  above the request (`unspelled=` in `TAM_MAUDE_CACHE_STATS=1` counts those
  families).
- **Lean's own proposal.** For a request the Maude backend's free unifier
  solves alone, by a test that unifies nothing (`solved_by_free_unifier`: no
  AC or C symbol, or each AC or C term faces only a variable used once), the
  proposal comes from the algebra library instead (`Unifiers::self_named`,
  `tamarin_lean_self_name_unifiers`): Rust tells a proposer in Lean which
  request variables each variable of the answer is the whole image of and how
  often it occurs, the proposer proposes the names the Maude backend composes,
  and the bridge passes them to `tamarin_name_unifiers` in the same call. The
  answer is read through those tables only when they are the tables of that
  proposal; otherwise the request takes the path above (`self_named=` and
  `self_declined=` count the two, `spelled=` the requests of that path). In
  builds with debug assertions every such answer is compared with the answer of
  the path above.

`crates/tamarin-term/src/lean_unification/whole/wire_tests.rs` holds the
tests, on the queries of `examples/audit_fuzz.rs` for every signature that
fuzzer knows (the file is included as a module, so the two cannot drift):

| test | what it holds the code to |
| --- | --- |
| `a_request_reads_back_as_the_terms_it_was_built_from` | the rows of a request, read with its own tables, are the terms that were encoded |
| `a_term_sent_through_the_matcher_comes_back_as_itself` | request encoder, Lean reader and writer, and Rust reader compose to the identity on a term |
| `requests_that_differ_have_different_words`, `a_changed_variable_changes_the_words_and_a_renaming_does_not` | two requests have the same words only if they differ in the choice of names of variables and constants: constants, sorts, free against AC operators, one operator against another, argument order, one variable against two, one theory against another |
| `the_reader_of_a_named_family_agrees_with_the_library` | `read_named` returns what Lean's own `apply` returns for the same reply and tables, also for tables that were damaged, and fails where it has no reading |
| `a_free_request_is_named_by_the_library_as_the_maude_backend_names_it` | for a request the free unifier solves alone, with or without AC operators, the names Lean proposes itself give the Maude backend's answer, the composition of the empty fresh substitution with the free unifier |
| `a_request_is_solved_by_the_free_unifier_only_where_no_ac_terms_meet` | the test of those requests: AC terms face to face, a product bound by a variable used once or more, a clash |
| `a_family_has_a_member_exactly_when_a_row_follows_its_status_row` | the empty family, a family of answers without bindings, and words that are no family |
| `a_reply_is_read_only_through_tables_that_name_all_of_it` | default names, a proposed name, a request variable's own name, proposals that are not taken, and the memo of tables |

```bash
MAUDE_PATH="$(command -v maude)" cargo test --profile ci -p tamarin-term \
    --features lean-unification --lib wire_tests -- --test-threads=4
```

The naming export costs one Lean call for each unification the session has
not answered before, unless the same names were asked for the same shape of
family before (the tables are memoized by the words of the request,
`UnifyReplies`). A call takes 9 to 15 µs, and reading the reply through the
tables as long as the decoder it replaces. Theories that ask thousands of
new unifications a second pay a few percent of CPU time for it
(`csf12/KEA_plus_AdvKey` 8%, `ake/dh/NAXOS_eCK` 3 to 7%, `wireguard` 5%,
`csf26-ac/fast/Joux` 4%, `csf18-xor/CH07` 2%); over the whole corpus it is
0.3%.

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
| `rs_ref_check.sh` | CI's gate: output hashes vs the oracle-certified `ci_ref_fast.tsv` snapshot |
| `capture_cli_refs.sh` | captures the oracle stdout `cli_e2e.rs`'s flag pins compare against |
| `web_parity.sh` (+ `web_crawl.py`, `web_normalize.py`, `web_diff.py`) | interactive-mode gate |
| `pane_byte_check.sh` | byte-exact pane HTML vs the web cache; file list required |
| `rs_vs_rs_diff.sh` / `triage_diff_vs_hs.sh` | refactor-inertness sweep + 3-way triage |
| `backend_gate.py` (+ `test_backend_gate.py`) | native-only against Maude: verdicts, liveness and time, under per-process caps |
| `interactive_backend_check.sh` | one interactive session over HTTP on both algebra backends |

**Data files**

| File | Purpose |
|---|---|
| `parity_corpus.txt` | canonical 432-file corpus list |
| `parity_corpus_fast.txt` | 365-file CI subset (every file proving in ≤1.5 s) |
| `file_flags.tsv` | per-file batch flags |
| `web_flags.tsv` | separate per-file interactive flags; unsupported entries fail the web gates |
| `ci_ref_fast.tsv` | committed output-hash reference for `rs_ref_check.sh` |
| `sweep_expected.tsv` | the flag sweeps' residual ledger (applied mechanically) |
| `pe_family.txt` / `module_family.txt` / `json_family.txt` | `FAMILY=1` subsets |
| `websweep_residual.txt` | the web milestone crawl list (residue itself is ledgered below) |
| `websweep_ledger.tsv` | the web gate's residue ledger (applied mechanically) |
| `backend_gate/smoke.tsv` / `backend_gate/corpus.tsv` | the backend gate's CI list and its full list, with per-file flags |
| `backend_gate/pending.tsv` | theories native-only is known not to finish yet (expected failures the gate honours and reports) |
| `backend_gate/verdict_exceptions.tsv` | documented verdict differences between the backends |
| `backend_gate/theories/` | regression theories that live only in the backend gate |
| `crates/tamarin-prover/tests/fixtures/cli_refs/cases.tsv` | the argv table both `capture_cli_refs.sh` and `cli_e2e.rs` read |

**Triage**

| Script | Purpose |
|---|---|
| `diff_proof_raw.sh` | one lemma, raw HS↔RS diff |
| `corpus_raw_diff.sh` | raw per-lemma diff across the corpus |
| `compare_parity_tsv.py` | compare two gate TSVs by (file, lemma) |
| `diff_proof_tree.sh` / `canon_proof_tree.py` / `corpus_diff_proof_trees.sh` | structural proof-tree diffs, pre-byte-parity era; superseded by the byte gates and only worth reaching for when output diverges too grossly to read |
**Maintenance**

| Script | Purpose |
|---|---|
| `bump_submodule.sh` | submodule bump: patch rebase, oracle rebuild, automatic server-fixture refresh, and explicit re-certification checklist (the caches self-invalidate, so none is archived) |
| `bench.sh` | RS-vs-HS wall-clock + memory tables (`--write` regenerates `docs/PERFORMANCE.md`) |
