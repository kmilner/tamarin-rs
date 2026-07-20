# tamarin-prover (Rust port)

A Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/) with the goal
of reproducing the Haskell prover's output byte-for-byte. Typically
4–16× faster (up to 42×) on several-fold less memory.

## Important notes

Always verify generated proofs against regular tamarin-prover. All proofs generated
by this prover  should be reverifiable against regular tamarin
by simply running them on the command line (i.e. `tamarin-prover proof.spthy`).
You should not directly trust the output of this given the extensive use of LLMs in
translating code.

To make this easy there is a `prove_and_reverify.sh` script in the root of this repo.
In many cases, proving in tamarin-rs and reverifying in tamarin-prover is still faster than proving
in tamarin-prover directly; you may also find tamarin-rs useful for iterating more quickly before
checking against the regular tamarin-prover.

At time of writing there are two open issues in Haskell affecting proof reverifiability. If
you'd like to build a version of tamarin-prover that has patches applied already, you
can use `./setup.sh testing`, we use this patched version for internal testing. These
issues are https://github.com/tamarin-prover/tamarin-prover/issues/871 and
https://github.com/tamarin-prover/tamarin-prover/issues/881. Once the associated pull requests
are merged all proofs should be identical; If you do find any that differ (even if they cross-verify)
please report them in the github issues so they can be fixed!

The licensing of this code is somewhat complicated, but the built binary is GPL 3.0. 
See [License](#license) if you are interested in future prospects for redistribution.

## Summary

- **Parity:** byte-identical `--prove` output with the Haskell prover on a
  419-file corpus — every theory under `tamarin-prover/examples/` that uses only ported
  features. Stored proofs replay and validate across provers in both
  directions, and the interactive web UI agrees page-for-page with the
  Haskell server across ≈380 theories / ≈120,000 crawled pages.
- **Performance:** 1.7–42× faster across 1–16 cores (median ≈8×), with
  peak memory 3.4–26× lower at one core — see [Performance](#performance).
- **Not yet ported:** observational equivalence (`--diff`) — see
  [Not yet ported](#not-yet-ported).
- **Testing process:** [TESTING.md](TESTING.md) documents the parity-gate
  ladder and divergence-debugging tools.


## Repository layout

```
crates/            the Rust port (crate breakdown below)
scripts/           parity gates, benchmarks, and divergence-debugging harnesses
tests/             wellformedness fixture corpus
patches/
  tamarin-prover-fixes.patch   local Haskell fixes not yet upstream —
                               stored-formula normalisation / gconj
                               idempotence, assorted solver and
                               equation-store fixes, and the solver-trace
                               instrumentation the diff harnesses depend on
tamarin-prover/    upstream submodule, pinned to a known-good commit and kept
                   PRISTINE — holds the canonical Haskell sources, the
                   examples/ corpus, and the web data/ assets
tamarin-prover-testing/   (untracked; created by ./setup.sh testing) patched
                   copy of the prover, built as the byte-parity oracle
target/            Rust build output (release binary under target/release/)
```

## Building

```
./setup.sh                           # init the pristine submodule
cargo build --release                # → target/release/tamarin-rs
cargo test                           # Rust unit + integration tests
```

The submodule must be present even for a plain `cargo build`: `tamarin-theory`
embeds `tamarin-prover/data/intruder_variants_dh.spthy` and
`intruder_variants_bp.spthy` at compile time, the web server serves the
submodule's `data/` assets at runtime, and the tests read the
`tamarin-prover/examples/` corpus. The submodule working tree is never
modified, so tracking upstream is an ordinary submodule bump —
`scripts/bump_submodule.sh` automates it (rebases the patch onto the new pin,
rebuilds the oracle, archives the now-stale gate caches, and prints the
verification checklist; `--check` dry-runs the patch rebase first).

The release profile uses `lto = "fat"` and `codegen-units = 1`.

Building the Haskell oracle is needed only for the parity gates, not for the
Rust build itself:

```
./setup.sh testing                   # patched oracle → tamarin-prover-testing/
```

This materialises a git worktree of the pinned commit at
`tamarin-prover-testing/`, applies `patches/tamarin-prover-fixes.patch` there
(the submodule itself stays untouched), and builds it with stack. The parity
scripts discover that binary automatically; `HS_PATH=<binary>` overrides.

## Parity status

The correctness criterion is byte-identical raw `--prove` output, ignoring
the volatile header lines (Git revision, compile time, processing time).
The batch gate (`scripts/corpus_file_diff.sh`, corpus in
`scripts/parity_corpus.txt`) currently reports:

| Result | Files | Meaning |
|--------|------:|---------|
| MATCH | 419 | Rust output byte-identical to Haskell |
| DIFF  |   0 | — |
| SKIP  |   0 | — |

The corpus spans every feature-complete theory family under `tamarin-prover/examples/` —
classic and AKE protocols, XOR / bilinear-pairing / multiset theories, the
auto-sources suites, accountability case studies, and 77 SAPiC `process:`
theories — each run under its canonical upstream invocation
(`scripts/file_flags.tsv`). Theories outside the corpus need an unported
feature (`--diff`), hit a known auto-prover or SAPiC-rendering divergence
tracked for porting, exceed the gate's per-file Haskell time budget under
their canonical flags, or are the same files upstream's own regression
suite excludes as non-terminating.

Stored proofs are validated, not just displayed: loading a proof-carrying
file replays every stored step against a freshly derived constraint system,
and proof files are cross-compatible in both directions with byte-identical
analysis output from either loader.

The interactive web UI (`interactive` subcommand) is verified by a semantic
crawl gate (`scripts/web_parity.sh`): both servers are booted on the same
theory, every proof-tree, constraint-system, graph and source page is
crawled — autoproving each lemma along the way — and compared after
normalisation. The two UIs agree page-for-page except for a small documented
residue that renders *identical* proof states with different internal
counter values (fresh-variable witness indices, goal-creation numbers,
term-abbreviation picks on a few AC-heavy theories); these never appear in
proof scripts, proof structure, or verdicts.

## Performance

Wall-clock time and peak memory for both provers on eight representative
theories, proving all lemmas (`--derivcheck-timeout=30`) on x86_64 Linux,
24 cores (GHC 9.6.7, Maude 3.5.1); Haskell at `+RTS -N{1,4,16}`, the Rust
port at `--processors={1,4,16}`. Tables are generated by `scripts/bench.sh`
(regenerate in place with `scripts/bench.sh --write`); the RS columns show
the change versus Haskell (negative = faster / less memory).

<!-- BENCH:START — auto-generated by scripts/bench.sh; do not edit by hand.

Regenerate these three tables in place:

    scripts/bench.sh --write     # measure, then rewrite this block
    scripts/bench.sh             # measure, print to stdout only

Both provers prove every lemma (--prove --derivcheck-timeout=30); HS at
`+RTS -Nk`, RS at `--processors=k`; wall-clock + peak RSS come from
`/usr/bin/time -v` (the prover process only — Maude is a separate subprocess on
both sides and is excluded). Single run per cell (wall-clock is noisy ±10%).
The P+R columns measure ./prove_and_reverify.sh (THREADS=k): prove with RS,
then re-CHECK the emitted proofs with HS — i.e. the total cost of a proof you
did not have to trust the port for; its peak RSS is the max across both
phases. The RS and P+R columns show the % change vs HS in parentheses
(negative = faster / less memory). Tune the theory set / core counts /
binaries via the FILES, CORES, TIMEOUT, DERIV, HS_PATH, RS_PATH env vars (see
the scripts/bench.sh header).
-->
<!-- last run: x86_64 Linux, 24 cores -->

**1 core**

| Theory | HS time | RS time | P+R time | HS memory | RS memory | P+R memory |
|--------|--------:|--------:|---------:|----------:|----------:|-----------:|
| `NSPK3` | 2.2 s | 0.5 s (-77%) | 1.4 s (-36%) | 58 MB | 17 MB (-71%) | 45 MB (-22%) |
| `Joux` | 17.5 s | 4.6 s (-74%) | 12.3 s (-30%) | 234 MB | 43 MB (-82%) | 89 MB (-62%) |
| `stateverif_left_right` | 27.9 s | 3.6 s (-87%) | 24.9 s (-11%) | 838 MB | 39 MB (-95%) | 822 MB (-2%) |
| `Yubikey` | 33.6 s | 5.2 s (-85%) | 26.4 s (-21%) | 273 MB | 47 MB (-83%) | 235 MB (-14%) |
| `mixvote_SmHh-multi-session` | 40.1 s | 4.6 s (-89%) | 28.9 s (-28%) | 857 MB | 35 MB (-96%) | 827 MB (-4%) |
| `gcm` | 80.5 s | 14.2 s (-82%) | 88.4 s (+10%) | 1241 MB | 100 MB (-92%) | 1245 MB (+0%) |
| `wireguard` | 81.7 s | 7.3 s (-91%) | 46.6 s (-43%) | 1178 MB | 46 MB (-96%) | 761 MB (-35%) |
| `CCITT_X509_3` | 373.1 s | 28.3 s (-92%) | 32.3 s (-91%) | 2404 MB | 303 MB (-87%) | 303 MB (-87%) |

**4 cores**

| Theory | HS time | RS time | P+R time | HS memory | RS memory | P+R memory |
|--------|--------:|--------:|---------:|----------:|----------:|-----------:|
| `NSPK3` | 1.1 s | 0.4 s (-64%) | 1.0 s (-9%) | 79 MB | 26 MB (-67%) | 55 MB (-30%) |
| `Joux` | 14.0 s | 6.2 s (-56%) | 13.1 s (-6%) | 278 MB | 45 MB (-84%) | 98 MB (-65%) |
| `stateverif_left_right` | 17.6 s | 2.3 s (-87%) | 22.3 s (+27%) | 788 MB | 54 MB (-93%) | 839 MB (+6%) |
| `Yubikey` | 22.0 s | 3.2 s (-85%) | 18.5 s (-16%) | 297 MB | 63 MB (-79%) | 250 MB (-16%) |
| `mixvote_SmHh-multi-session` | 20.9 s | 2.0 s (-90%) | 16.9 s (-19%) | 898 MB | 58 MB (-94%) | 991 MB (+10%) |
| `gcm` | 56.0 s | 5.7 s (-90%) | 56.4 s (+1%) | 1267 MB | 183 MB (-86%) | 1344 MB (+6%) |
| `wireguard` | 45.6 s | 3.9 s (-91%) | 30.2 s (-34%) | 1255 MB | 75 MB (-94%) | 803 MB (-36%) |
| `CCITT_X509_3` | 152.7 s | 7.8 s (-95%) | 10.4 s (-93%) | 4300 MB | 638 MB (-85%) | 584 MB (-86%) |

**16 cores**

| Theory | HS time | RS time | P+R time | HS memory | RS memory | P+R memory |
|--------|--------:|--------:|---------:|----------:|----------:|-----------:|
| `NSPK3` | 1.1 s | 0.7 s (-36%) | 1.4 s (+27%) | 131 MB | 35 MB (-73%) | 100 MB (-24%) |
| `Joux` | 14.8 s | 6.4 s (-57%) | 13.5 s (-9%) | 323 MB | 52 MB (-84%) | 146 MB (-55%) |
| `stateverif_left_right` | 15.9 s | 2.5 s (-84%) | 20.6 s (+30%) | 920 MB | 78 MB (-92%) | 841 MB (-9%) |
| `Yubikey` | 21.2 s | 3.1 s (-85%) | 17.8 s (-16%) | 346 MB | 95 MB (-73%) | 311 MB (-10%) |
| `mixvote_SmHh-multi-session` | 16.4 s | 2.2 s (-87%) | 15.5 s (-5%) | 929 MB | 115 MB (-88%) | 1042 MB (+12%) |
| `gcm` | 45.9 s | 5.1 s (-89%) | 56.5 s (+23%) | 1325 MB | 238 MB (-82%) | 1432 MB (+8%) |
| `wireguard` | 38.8 s | 3.8 s (-90%) | 28.4 s (-27%) | 1281 MB | 114 MB (-91%) | 830 MB (-35%) |
| `CCITT_X509_3` | 140.7 s | 3.3 s (-98%) | 5.7 s (-96%) | 5627 MB | 699 MB (-88%) | 766 MB (-86%) |

<!-- BENCH:END -->

Memory is the maximum resident set of the prover process; Maude runs as a
separate subprocess on both sides and is excluded. Across all theories and
core counts the Rust port is 1.7–42× faster (median ≈8×); peak memory is
3.4–26× lower at one core and 4–11× lower at sixteen. The worst cells are
the sub-second `NSPK3` runs, where startup and timer granularity dominate
both provers.

The port parallelises at two levels, both via rayon: independent lemmas are
proved concurrently, and within a lemma the proof-search fan-out and source
saturation run in parallel over a pool of Maude subprocesses
(`--processors=N` sets the worker count, `--maude-processes=M`, default `N`,
the pool size). Multi-lemma theories gain the most across cores; theories
dominated by source saturation also speed up at a single core because
refined sources are computed once and shared across lemmas.

## Implemented

- **Parser:** full `.spthy` grammar — `macros:`, `predicates:`, `equations:`,
  `restrictions:`, `tactics:`, `heuristic:`, `#define`/`#include`
  preprocessing, multi-line comments, Unicode symbols.
- **Elaborator:** rule signatures, lemma formulas → guarded form, macro and
  predicate expansion, restriction insertion, source-kind classification.
- **Builtins:** `hashing`, `symmetric-encryption`, `asymmetric-encryption`,
  `signing`, `revealing-signing`, `diffie-hellman`, `xor`,
  `bilinear-pairing`, `multiset`, `natural-numbers`, `subterm`,
  `locations-report`, plus custom functions and equations.
- **Solver:** full constraint-system port — simplification, source
  refinement/saturation, chain extension, contradiction detection,
  induction, stored-proof replay with plain-load proof validation, and
  AC-modulo unification via pooled Maude.
- **`--auto-sources`:** automatic sources-lemma generation
  (HS `addAutoSourcesLemma`).
- **SAPiC `process:`** — the process-calculus frontend, byte-identical to HS
  `Sapic.translate`: core constructs, mutable state, locks, `let`
  bindings/destructors, secret/private channels, progress and
  reliable-channel translations, `report()`, and the opt-in
  `--translation-state-optimisation` pure-state path.
- **Accountability** — `test` case tests and `accounts for` lemmas expand
  into the verification-condition lemmas (six per case test plus one
  `_verif_empty` per lemma) and case-test predicates, with the
  "Accountability (RP check)" wellformedness report
  (HS `Accountability.translate` / `Accountability.Generation`).
- **Heuristics:** smart (`s`/`S`), goal-number (`C`/`c`), injective
  (`i`/`I`), SAPiC (`p`/`P`), oracle (`o`/`O`), and `tactic:` rankings —
  per-file, per-lemma, or CLI-overridden (HS `selectHeuristic`).
- **CLI:** `--prove`/`--lemma`, `--bound`, `--heuristic`, `--oraclename`,
  `--oracle-only`, `--processors`, `--maude-processes`,
  `--derivcheck-timeout`, `--stop-on-trace` (all five policies —
  `dfs`/`bfs`/`seqdfs`/`sorry`/`none` — including in-file
  `configuration:` blocks), `-D` defines, `--parse-only`,
  `--precompute-only`, `-O/--output`, `--quiet`, `-v/--verbose`,
  `--quit-on-warning`; exit codes and summary lines mirror HS.
- **Subcommands:** `interactive` (HTTP server), `variants` (DH/BP
  intruder-rule variants dump), `test` (install self-check).

## Not yet ported

- **`diff(...)` / `--diff`** — observational-equivalence mode.
- Parse-only CLI flags: `--saturation`, `--open-chains`,
  `--partial-evaluation`, `--replication-bound`;
  `--output-json`/`--output-dot` write stubs and `--output-module=…` errors.

Theories using these features are tracked in `scripts/file_flags.tsv` and
re-enter the gate automatically once the feature lands.

## Crate layout

The workspace crates under `crates/` (`tamarin-prover/` here is the binary
crate, distinct from the `tamarin-prover/` submodule at the repository root):

```
tamarin-utils/          fresh-ident state, small util types
tamarin-term/           Term/LTerm/LNTerm, MaudeSig, Maude IPC, normalisation
tamarin-parser/         .spthy AST + lexer + parser + #include resolver
tamarin-theory/         elaborator, constraint system, solver, simplify, sources, replay
tamarin-sapic/          SAPiC process: frontend — translation to multiset-rewrite rules
tamarin-accountability/ accountability frontend — case tests → VC lemmas
tamarin-export/         ProVerif / DeepSec / SPDL export (placeholder)
tamarin-server/         interactive HTTP server (Axum)
tamarin-prover/         the binary: CLI parser + run dispatch
```

## Testing

`cargo test` runs the Rust suites; parity against the Haskell prover is the
real correctness gate — `scripts/corpus_file_diff.sh` for batch mode,
`scripts/web_parity.sh` for the interactive UI. See
[TESTING.md](TESTING.md) for the full verification ladder, the gate
environment reference, and the divergence-debugging toolbox.

## License

The licensing situation of this code is somewhat complicated. Portions of the
code are written based only on the observable output behaviour of tamarin-prover
while other parts were written with access to Tamarin's GPL 3.0 code. To my understanding,
this makes the resulting binary GPL 3.0 for the moment, as some of the contents are
a 'translation' of GPL 3 code..

Relicensing tamarin-prover is made difficult because of a very long tail of
contributors over many years, making it very difficult to get in touch with each
and every one of them to relicense their contributions. An eventual goal is to
relicense tamarin-rs fully under MIT if possible, which will require one or both of:

- Permission of the largest contributors (or their instutitions, where the institution
  is the only party capable of relicensing).
- Where getting permission is infeasible, replacing the associated contribution with a
  cleanroom implementation of the feature.

Cleanroom implementations have to be performed by an LLM with access only to the observable
behaviour of tamarin-prover, not the source code. Unfortunately I (as a contributor to
tamarin-prover) am, to my understanding, tainted and cannot participate in this process
except to audit the output. This work will be tracked along with full tool-call transcripts
to prove there was no access to GPL 3.0 source in https://github.com/kmilner/tamarin-cleanroom
but it will be a long process (the segments being reimplemented have to be sufficiently broad
so as to not inherit any information about the GPL 3.0 source code beyond broad module interfaces
etc). Early experiments with clean room implementation of the formatting code had limited success,
so for now there is no active work on this.

Code with GPL 3.0 attribution is stated at the top of the header file, including the associated
github usernames that have not yet granted permission for reuse. Currently, this is everyone,
because I haven't started asking yet. If you want to preempt this and give your permission please
send me an email or file a github issue!

You can regenerate these headers (and inspect how they were generated) in scripts/gen_license_headers.py

So, in summary:
- All Rust code in this repository (`crates/`, `scripts/`, `tests/`) is
  MIT-licensed by default, however code which is based on GPL 3.0 code is
  still GPL 3.0 until either replaced by a cleanroom implementation or
  granted permission for relicensing by the related authors. This is indicated
  by comments at the top of those files. THE BINARY YOU BUILD IS GPL 3.0.
- The `tamarin-prover/` submodule is a separate upstream project licensed under
  GPL 3.0 (see `tamarin-prover/LICENSE`). `patches/tamarin-prover-fixes.patch`
  modifies those GPL 3 sources and is therefore itself GPL-3.
- None of this is legal advice, consult a lawyer.
