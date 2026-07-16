# Testing the Rust port

How the port is verified against the Haskell prover, from unit tests up to
full-corpus byte parity. Commands run from the repository root unless noted;
the pristine Haskell sources and the examples corpus live in the
`tamarin-prover/` submodule.

**Prerequisites:** the patched Haskell oracle — run `./setup.sh testing` to
materialise a patched copy of the prover at `tamarin-prover-testing/` (the
submodule itself is never modified) and build it with stack. Parity scripts
auto-discover the binary under `tamarin-prover-testing/.stack-work/`;
set `HS_PATH` to point them at a specific binary instead. Also needed:
`maude` on `PATH` (`dot` too, for graph pages in the web gate). On hosts
where these come from linuxbrew they are often *not* on `PATH` by default:

```bash
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
```

The correctness criterion everywhere is **byte-identical raw `--prove`
output**, after stripping only the environment-volatile header lines
(Git revision, compile time, processing time).

## The verification ladder

| Step | Command | Checks |
|---|---|---|
| 1 | `cargo test` | Rust unit + integration suites (~1000 tests) |
| 2 | `scripts/diff_proof_raw.sh <file> <lemma>` | one lemma, raw HS↔RS diff |
| 3 | `scripts/corpus_file_diff.sh` | the batch gate: 419-file corpus, byte parity |
| 4 | `scripts/web_parity.sh` | interactive-mode gate: crawl + semantic diff |
| 5 | `scripts/bench.sh` | performance tables (see README) |

## Rust test suite

```bash
cargo test                                           # whole workspace
cargo test -p tamarin-theory --test oracle_solver    # solver vs corpus fixtures (needs maude)
```

`oracle_solver` also carries heavyweight corpus probes behind `#[ignore]`,
run explicitly when needed:

```bash
cargo test --test oracle_solver corpus_proof_skeleton_match_probe --release -- --ignored --nocapture
```

- `corpus_verdict_match_coverage_probe` — verdict agreement sweep.
- `corpus_proof_skeleton_match_probe` — canonicalised proof-tree comparison
  per lemma. Historically the primary metric; superseded by the byte gate
  below, which subsumes it.

## Single-lemma parity

```bash
scripts/diff_proof_raw.sh tamarin-prover/examples/classic/NSPK3.spthy injective_agree
```

Raw byte-for-byte diff of one lemma's `--prove` output; exit 0 = identical.
Rebuilds the Rust binary first (set `TAM_RS_NO_AUTO_BUILD=1` to use the
existing build).

## Corpus gate (the batch parity metric)

```bash
ALLOWLIST=scripts/parity_corpus.txt RESULTS_TSV=/tmp/gate.tsv scripts/corpus_file_diff.sh
awk -F'\t' '{print $2}' /tmp/gate.tsv | sort | uniq -c     # expect: 419 MATCH
```

Whole-file `--prove` diff over the canonical 419-file corpus
(`scripts/parity_corpus.txt`). Two strictly sequential phases: Haskell
output is computed once per file-content hash and cached under
`scripts/.hs_file_cache/`; the Rust binary is then diffed against the cache
— so re-runs after Rust-only changes skip the Haskell side entirely.
Theories whose upstream recipe needs extra arguments get them from
`scripts/file_flags.tsv`, applied identically to both provers.

Env knobs (full list in the script header): `ALLOWLIST` (one relative path
per line), `RESULTS_TSV`, `JOBS` (default 4), `FILE_TIMEOUT` (300 s),
`CORPUS_ROOT`, `CACHE`, `HS_PATH`, `RS_PATH`.

**Cache-staleness trap:** the HS cache is keyed on theory content only. If
the *Haskell binary's* behavior changes, the cache is silently stale —
point `CACHE` at a fresh directory after any accepted Haskell-side change.

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

## Web-parity gate (interactive mode)

```bash
ALLOWLIST=<filelist> RESULTS_TSV=/tmp/web.tsv scripts/web_parity.sh
```

Boots both servers on the same theory (HS on port 3021, RS on 3022), crawls
every proof-tree / constraint-system / graph / source page — autoproving
each lemma along the way — and diffs the pages semantically
(`web_crawl.py` / `web_normalize.py` / `web_diff.py`). HS crawl manifests
are cached content-keyed under `scripts/.web_hs_cache/` (same staleness
trap as above). Env knobs: `FILE_TIMEOUT`, `READY_TIMEOUT`, `HS_PORT`,
`RS_PORT`, `MAX_NODES`, `CACHE`, `DIFFDIR`.

The known cosmetic residue (identical proof states rendered with different
internal counter values on a few AC-heavy theories — see the README) lives
in `scripts/websweep_residual.txt`; a page-level DIFF is only actionable if
its file is not in that list or the diff is structural.

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
TAM_RS_TRACE_STATE=1 target/release/tamarin-prover --prove=<lemma> <file> 2>&1 | grep '^\[STATE\]' > /tmp/rs.trace
diff /tmp/hs.trace /tmp/rs.trace | head
```

**Maude IPC trace** — lock-step command/response comparison:

```bash
TAM_DBG_MAUDE_IO=full TAM_DBG_MAUDE_IO_FILTER=unify target/release/tamarin-prover --prove <file>
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

| Script | Purpose |
|---|---|
| `corpus_file_diff.sh` | the batch byte gate (cached HS, per-file) |
| `parity_corpus.txt` | canonical 419-file corpus list |
| `file_flags.tsv` | per-file extra prover flags (both sides) |
| `diff_proof_raw.sh` | one lemma, raw HS↔RS diff |
| `corpus_raw_diff.sh` | raw per-lemma diff across the corpus |
| `rs_vs_rs_diff.sh` / `triage_diff_vs_hs.sh` | refactor-inertness sweep + 3-way triage |
| `compare_parity_tsv.py` | compare two gate TSVs by (file, lemma) |
| `parity_check.sh` | quick raw check of specific files |
| `web_parity.sh` (+ `web_crawl.py`, `web_normalize.py`, `web_diff.py`) | interactive-mode gate |
| `websweep_residual.txt` | known cosmetic web residue |
| `diff_proof_tree.sh` / `canon_proof_tree.py` / `corpus_diff_proof_trees.sh` / `corpus_full_trace_diff.sh` | canonicalised proof-tree diffs |
| `diff_maude_io.sh` / `diff_aes_calls.sh` | Maude-IPC and eq-store call-site diffs |
| `canonicalize_trace.py` / `diff_trace.py` | trace canonicaliser + differ |
| `bench.sh` | RS-vs-HS wall-clock + memory tables (`--write` regenerates the README block) |
