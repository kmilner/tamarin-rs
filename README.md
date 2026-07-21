# tamarin-prover (Rust port)

A Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/) with the goal
of reproducing the Haskell prover's output byte-for-byte. Typically
3–14× faster (up to 50×) on several-fold less memory.

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
- **Performance:** 2.8–50× faster across 1–16 cores (median ≈8×), with
  peak memory 3.5–27× lower at one core — see [Performance](#performance).
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
(regenerate in place with `scripts/bench.sh --write`); the RS+HS and RS
columns show the change versus Haskell (negative = faster / less memory).

<!-- BENCH:START — auto-generated by scripts/bench.sh; do not edit by hand.

Regenerate these three tables in place:

    scripts/bench.sh --write     # measure, then rewrite this block
    scripts/bench.sh             # measure, print to stdout only

Both provers prove every lemma (--prove --derivcheck-timeout=30); HS at
`+RTS -Nk`, RS at `--processors=k`; wall-clock + peak RSS come from
`/usr/bin/time -v` (the prover process only — Maude is a separate subprocess on
both sides and is excluded). Single run per cell (wall-clock is noisy ±10%).
The RS+HS columns measure ./prove_and_reverify.sh (THREADS=k): prove with RS,
then re-CHECK the emitted proofs with HS — i.e. the total cost of a proof you
did not have to trust the port for; its peak RSS is the max across both
phases. The RS+HS and RS columns show the % change vs HS in parentheses
(negative = faster / less memory). Tune the theory set / core counts /
binaries via the FILES, CORES, TIMEOUT, DERIV, HS_PATH, RS_PATH env vars (see
the scripts/bench.sh header).
-->
<!-- last run: x86_64 Linux, 24 cores -->

**1 core**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 2.3 s | 1.4 s (-39%) | 0.5 s (-78%) | 60 MB | 46 MB (-23%) | 17 MB (-72%) |
| `Joux` | 17.0 s | 12.0 s (-29%) | 4.5 s (-74%) | 246 MB | 90 MB (-63%) | 45 MB (-82%) |
| `stateverif_left_right` | 28.1 s | 24.7 s (-12%) | 3.2 s (-89%) | 839 MB | 820 MB (-2%) | 32 MB (-96%) |
| `Yubikey` | 33.4 s | 26.0 s (-22%) | 4.8 s (-86%) | 274 MB | 235 MB (-14%) | 47 MB (-83%) |
| `mixvote_SmHh-multi-session` | 39.9 s | 28.6 s (-28%) | 4.3 s (-89%) | 846 MB | 822 MB (-3%) | 31 MB (-96%) |
| `gcm` | 81.7 s | 86.8 s (+6%) | 12.7 s (-84%) | 1250 MB | 1270 MB (+2%) | 85 MB (-93%) |
| `wireguard` | 82.4 s | 46.2 s (-44%) | 7.0 s (-92%) | 1190 MB | 858 MB (-28%) | 46 MB (-96%) |
| `CCITT_X509_3` | 370.9 s | 31.7 s (-91%) | 26.5 s (-93%) | 2400 MB | 302 MB (-87%) | 303 MB (-87%) |

**4 cores**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 1.1 s | 1.0 s (-9%) | 0.3 s (-73%) | 85 MB | 56 MB (-34%) | 25 MB (-71%) |
| `Joux` | 14.2 s | 10.9 s (-23%) | 4.2 s (-70%) | 271 MB | 99 MB (-63%) | 43 MB (-84%) |
| `stateverif_left_right` | 17.1 s | 21.8 s (+27%) | 2.0 s (-88%) | 786 MB | 765 MB (-3%) | 47 MB (-94%) |
| `Yubikey` | 21.8 s | 18.5 s (-15%) | 2.9 s (-87%) | 293 MB | 255 MB (-13%) | 62 MB (-79%) |
| `mixvote_SmHh-multi-session` | 18.9 s | 16.2 s (-14%) | 1.8 s (-90%) | 882 MB | 957 MB (+9%) | 62 MB (-93%) |
| `gcm` | 56.1 s | 62.5 s (+11%) | 5.7 s (-90%) | 1237 MB | 1373 MB (+11%) | 139 MB (-89%) |
| `wireguard` | 43.5 s | 29.9 s (-31%) | 3.2 s (-93%) | 1207 MB | 872 MB (-28%) | 76 MB (-94%) |
| `CCITT_X509_3` | 156.2 s | 10.0 s (-94%) | 7.6 s (-95%) | 4426 MB | 477 MB (-89%) | 482 MB (-89%) |

**16 cores**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 1.1 s | 1.0 s (-9%) | 0.4 s (-64%) | 134 MB | 98 MB (-27%) | 33 MB (-75%) |
| `Joux` | 14.9 s | 11.2 s (-25%) | 4.3 s (-71%) | 328 MB | 148 MB (-55%) | 51 MB (-84%) |
| `stateverif_left_right` | 17.2 s | 23.0 s (+34%) | 2.0 s (-88%) | 883 MB | 794 MB (-10%) | 65 MB (-93%) |
| `Yubikey` | 20.8 s | 17.2 s (-17%) | 2.6 s (-87%) | 348 MB | 314 MB (-10%) | 85 MB (-76%) |
| `mixvote_SmHh-multi-session` | 16.0 s | 15.0 s (-6%) | 1.7 s (-89%) | 931 MB | 1030 MB (+11%) | 113 MB (-88%) |
| `gcm` | 50.1 s | 60.0 s (+20%) | 4.4 s (-91%) | 1320 MB | 1409 MB (+7%) | 203 MB (-85%) |
| `wireguard` | 38.0 s | 28.1 s (-26%) | 2.9 s (-92%) | 1315 MB | 826 MB (-37%) | 108 MB (-92%) |
| `CCITT_X509_3` | 139.0 s | 5.2 s (-96%) | 2.8 s (-98%) | 5787 MB | 735 MB (-87%) | 741 MB (-87%) |

<!-- BENCH:END -->

Memory is the maximum resident set of the prover process; Maude runs as a
separate subprocess on both sides and is excluded. Across all theories and
core counts the Rust port is 2.8–50× faster (median ≈8×); peak memory is
3.5–27× lower at one core and 4–13× lower at sixteen. The worst cells are
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
