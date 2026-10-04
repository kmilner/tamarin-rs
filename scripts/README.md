# Running the proof and web corpora

These are the two headline parity tests. Both compare the Rust port with the
patched Haskell oracle; both automatically generate missing oracle cache
entries and reuse valid ones. **The command to generate a cache is the same
command you use to run the test.** It also runs the Rust comparison.

## Prepare once (and again after changing the sources)

From the repository root, on GNU/Linux:

```bash
./setup.sh testing
cargo build --release -p tamarin-prover
```

You also need Maude, Graphviz and the system tools listed in
[TESTING.md](../TESTING.md#prerequisites). The oracle must be built from the
current submodule and patch list. Both binaries are required even with warm
caches. Do not rebuild them or edit producer inputs during an active run.

## Run

```bash
scripts/test.sh proof     # 504 theories: full --prove stdout and exit status
scripts/test.sh web       # 77 theories: crawled web responses
scripts/test.sh all       # both, sequentially, even if the first fails
```

Cold runs can take hours. Warm runs reuse Haskell results but still run Rust.
Defaults are a 600-second per-file limit, two proof workers with four Haskell
RTS threads each, and one web worker. Adjust to the machine and desired scope:

```bash
JOBS=4 FILE_TIMEOUT=900 scripts/test.sh proof
ALLOWLIST=seed scripts/test.sh web                  # two-theory smoke test
ALLOWLIST=/tmp/my-theories.txt scripts/test.sh proof # paths relative to examples/
```

For `all`, corpus-specific overrides (`ALLOWLIST`, `CACHE`, `RESULTS_TSV`,
`DIFFDIR`) are rejected: use individual commands instead. The entry point
never rebuilds binaries. `scripts/test.sh --help` describes its interface;
underlying gates still accept their existing environment settings.

## Results and caches

Each invocation prints a fresh directory under `scripts/results/`, containing
`run.log`, `results.tsv` and `exit-code`; web runs also save `diffs/` when needed.
`RESULTS_ROOT` changes the parent directory. `all` produces one directory per
suite. An interrupted run may have partial output and no `exit-code`.

Read the final verdict, not just the MATCH count. Missing results, timeouts and
unexplained differences fail the gates. Web results may include explicitly
ledgered differences; proof-node caps are reported but fail only with
`FAIL_ON_CAPPED=1`. Neither a filled cache nor a capped crawl proves full parity.

The web crawl fetches four different views of each selected proof node:
the HTML proof/constraint pane, graph definition, JSON graph, and graph-view
HTML shell. These are not repeated samples of a deterministic response;
each representation is compared between Haskell and Rust to cover its own
rendering/serialization path. The default 400-node cap permits up to 1,600
node-view requests per server, plus initial lemma, source and other pages.
See [web-parity coverage](../TESTING.md#web-parity-gate-interactive-mode).

| Suite | Corpus | Persistent oracle cache |
|---|---|---|
| Proof | [`parity_corpus.txt`](parity_corpus.txt) | `scripts/.gate_cache/proof/` |
| Web | [`websweep_residual.txt`](websweep_residual.txt) (77-theory regression set, not the full proof corpus) | `scripts/.gate_cache/web/` |

The proof list is explicit, not automatic discovery. Its 504 theories include
upstream and patched trace-proof regressions. Patch-only fixtures use paths into
`tamarin-prover-testing/examples/`, so `./setup.sh testing` must materialize
them. Required default-case flags are in `file_flags.tsv`; extra `-D` variants,
negative-input, equivalence-mode and export-only scenarios are not covered
merely by adding their theory to this proof gate. See
[regression coverage](../TESTING.md#upstream-regression-coverage).
Typed-export and reloaded-proof regressions have their own fast check:
`cargo test --profile ci -p tamarin-prover --test sapic_export`.

The fast CI proof set includes all 65 patched proof regressions and the
upstream negated-equivalence case (430 theories total). GDH now belongs to the
CLI rejection tests and full proof gate, not the successful-proof fast set.
For that committed-hash
check, `./setup.sh testing-sources` prepares the fixtures without building
Haskell; `scripts/rs_ref_check.sh check` then needs only Rust and Maude.

Adding list entries does not invalidate existing Haskell cache entries.
An already-running gate snapshots its list at startup: run the expanded list
afterwards (or an explicit additions-only `ALLOWLIST`) to cover the new files.

Caches are gitignored, fingerprinted and shared across worktrees. After an
upstream/patch change, rebuild the oracle and rerun these commands: new keys
are selected automatically. **Do not delete the old caches**; old checkouts can
still reuse them. Repeating an interrupted run reuses completed entries.
`TAMARIN_RS_CACHE_ROOT` relocates the cache pool. Proof timeout markers are
cap-aware, so increasing `FILE_TIMEOUT` permits another attempt.

`file_flags.tsv` and `web_flags.tsv` supply per-theory options;
`websweep_ledger.tsv` records accepted web differences separately from the
corpus selection. See [the cache contracts](REFERENCE.md#the-hs-reference-caches)
for exact identities and publication rules.

## Everything else is supporting coverage or diagnosis

You do not need to run every script to generate the two caches.

| Need | Tool | Why it remains separate |
|---|---|---|
| Test the harness itself | `scripts/test.sh harness` | Cache, certificate, crawler and comparison regression tests; no full corpus run |
| Rust unit/integration tests | `cargo test` | Fast, local coverage independent of corpus parity |
| Fast CI proof check | `rs_ref_check.sh check` | Committed certified hashes; no Haskell run |
| Fast load-only feedback | `pretty_gate.sh`, `wf_gate.sh` | Shared load cache; no proofs |
| CLI option/stderr coverage | `pe_sweep.sh`, `module_sweep.sh`, `json_sweep.sh` | Flag combinations and stderr that the proof corpus does not cover |
| Corpus blind spots | `divergence_fixtures/check.sh` | Targeted regression fixtures used in CI |
| Inspect a proof mismatch | `diff_proof_raw.sh` | One lemma at a time; `corpus_raw_diff.sh` batches that diagnostic |
| Recheck just cached web panes | `pane_byte_check.sh` | Narrow diagnostic, not an additional milestone gate |
| Verify a Rust refactor | `rs_vs_rs_diff.sh`, `triage_diff_vs_hs.sh` | Compare two Rust builds, then consult Haskell on differences |

For specialist settings and maintenance tools, see [REFERENCE.md](REFERENCE.md).
For certification, CI, and debugging policy, see [TESTING.md](../TESTING.md).
`corpus_file_diff.sh` and `web_parity.sh` remain the underlying engines so cache
logic has one implementation and existing automation keeps working.
