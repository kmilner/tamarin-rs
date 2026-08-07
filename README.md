# tamarin-prover (Rust port)

A Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/) with the goal
of reproducing the Haskell prover's output byte-for-byte. Typically
4–32× faster than the most recent Tamarin release (up to 80×) on
4–45× less memory.

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

At time of writing there are two upstream issues in Haskell affecting proof
reverifiability: https://github.com/tamarin-prover/tamarin-prover/issues/871
(fixed on the develop branch, not yet in a release) and
https://github.com/tamarin-prover/tamarin-prover/issues/881 (fix pending in
https://github.com/tamarin-prover/tamarin-prover/pull/882). If you'd like to
build a version of tamarin-prover that has the fixes applied already, you can
use `./setup.sh testing`; we use this patched version for internal testing.
Once both fixes are merged and released all proofs should be identical; if you
do find any that differ (even if they cross-verify) please report them in the
github issues so they can be fixed!

The licensing of this code is somewhat complicated, but the built binary is GPL 3.0. 
See [License](#license) if you are interested in future prospects for redistribution.

## Summary

- **Parity:** byte-identical `--prove` output with the Haskell prover on a
  431-file corpus — every theory under `tamarin-prover/examples/` that uses only ported
  features. Stored proofs replay and validate across provers in both
  directions, and the interactive web UI agrees page-for-page with the
  Haskell server except for a small documented cosmetic residue, tracked by
  a ≈63,800-page sweep of the 75-theory residue ledger
  (`scripts/results/websweep_ef3f0468_post_review_20260801.tsv`) — see
  [Parity status](#parity-status).
- **Performance:** 4.3–80× faster than the most recent Tamarin release
  (1.12.0) across 1–16 cores (median ≈16×), with peak memory 4.3–45×
  lower at one core — see [Performance](#performance).
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
| MATCH | 431 | Rust output byte-identical to Haskell |
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
24 cores (Maude 3.5.1); Haskell at `+RTS -N{1,4,16}`, the Rust port at
`--processors={1,4,16}`. The Haskell baseline is the **most recent
tamarin-prover release (1.12.0)** — the binary users actually install — not
the develop branch this repo pins for parity testing: develop carries
performance work of its own that is not in a release yet, so expect a
smaller gap against a develop build. Tables are generated by
`scripts/bench.sh` (regenerate in place with `scripts/bench.sh --write`);
the RS+HS and RS columns show the change versus Haskell (negative = faster
/ less memory).

<!-- BENCH:START — auto-generated by scripts/bench.sh; do not edit by hand.

Regenerate these three tables in place:

    scripts/bench.sh --write     # measure, then rewrite this block
    scripts/bench.sh             # measure, print to stdout only

The HS baseline is the most recent tamarin-prover RELEASE (the exact version
is in the "last run" line below) — the prover users actually have installed —
not the develop branch this repo's parity oracle is pinned to; develop has
since gained performance work of its own, so the gap versus a develop build
is smaller than these tables show.

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
<!-- last run: x86_64 Linux, 24 cores; HS baseline: tamarin-prover 1.12.0 -->

**1 core**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 4.8 s | 2.3 s (-52%) | **0.5 s (-90%)** | 78 MB | 62 MB (-21%) | **18 MB (-77%)** |
| `Joux` | 22.3 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **4.5 s (-80%)** | 274 MB | — | **44 MB (-84%)** |
| `stateverif_left_right` | 46.0 s | 39.5 s (-14%) | **3.2 s (-93%)** | 1039 MB | 1216 MB (+17%) | **32 MB (-97%)** |
| `Yubikey` | 65.4 s | 49.9 s (-24%) | **4.8 s (-93%)** | 413 MB | 337 MB (-18%) | **46 MB (-89%)** |
| `mixvote_SmHh-multi-session` | 71.4 s | 53.7 s (-25%) | **4.3 s (-94%)** | 1044 MB | 1420 MB (+36%) | **33 MB (-97%)** |
| `gcm` | 136.4 s | 138.2 s (+1%) | **12.7 s (-91%)** | 1493 MB | 1509 MB (+1%) | **84 MB (-94%)** |
| `wireguard` | 163.8 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **6.8 s (-96%)** | 2105 MB | — | **47 MB (-98%)** |
| `CCITT_X509_3` | 560.2 s | 37.8 s (-93%) | **26.6 s (-95%)** | 4879 MB | 302 MB (-94%) | **302 MB (-94%)** |

**4 cores**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 2.6 s | 1.7 s (-35%) | **0.3 s (-88%)** | 107 MB | 74 MB (-31%) | **26 MB (-76%)** |
| `Joux` | 18.4 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **4.3 s (-77%)** | 287 MB | — | **45 MB (-84%)** |
| `stateverif_left_right` | 27.1 s | 34.6 s (+28%) | **2.0 s (-93%)** | 1002 MB | 1263 MB (+26%) | **47 MB (-95%)** |
| `Yubikey` | 48.4 s | 39.0 s (-19%) | **3.0 s (-94%)** | 402 MB | 341 MB (-15%) | **61 MB (-85%)** |
| `mixvote_SmHh-multi-session` | 36.7 s | 30.6 s (-17%) | **1.9 s (-95%)** | 1043 MB | 1390 MB (+33%) | **61 MB (-94%)** |
| `gcm` | 94.3 s | 101.4 s (+8%) | **5.2 s (-94%)** | 1476 MB | 1526 MB (+3%) | **142 MB (-90%)** |
| `wireguard` | 104.5 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **3.3 s (-97%)** | 2116 MB | — | **77 MB (-96%)** |
| `CCITT_X509_3` | 238.4 s | 14.0 s (-94%) | **7.5 s (-97%)** | 8782 MB | 649 MB (-93%) | **647 MB (-93%)** |

**16 cores**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 2.6 s | 1.8 s (-31%) | **0.4 s (-85%)** | 162 MB | 126 MB (-22%) | **33 MB (-80%)** |
| `Joux` | 19.7 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **4.4 s (-78%)** | 355 MB | — | **53 MB (-85%)** |
| `stateverif_left_right` | 26.4 s | 35.4 s (+34%) | **1.9 s (-93%)** | 1049 MB | 1218 MB (+16%) | **64 MB (-94%)** |
| `Yubikey` | 45.3 s | 37.8 s (-17%) | **2.6 s (-94%)** | 510 MB | 390 MB (-24%) | **86 MB (-83%)** |
| `mixvote_SmHh-multi-session` | 29.4 s | 28.5 s (-3%) | **1.7 s (-94%)** | 1069 MB | 1480 MB (+38%) | **110 MB (-90%)** |
| `gcm` | 84.1 s | 89.2 s (+6%) | **4.4 s (-95%)** | 1474 MB | 1645 MB (+12%) | **212 MB (-86%)** |
| `wireguard` | 83.0 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **3.0 s (-96%)** | 2228 MB | — | **113 MB (-95%)** |
| `CCITT_X509_3` | 223.2 s | 9.3 s (-96%) | **2.8 s (-99%)** | 11453 MB | 737 MB (-94%) | **740 MB (-94%)** |

<!-- BENCH:END -->

Memory is the maximum resident set of the prover process; Maude runs as a
separate subprocess on both sides and is excluded. Across all theories and
core counts the Rust port is 4.3–80× faster than the 1.12.0 release
(median ≈16×); peak memory is 4.3–45× lower at one core and 5–20× lower
at sixteen. The smallest gains are on `Joux`, whose runtime is dominated
by AC-heavy Maude queries both provers pay for equally.

The `not supported` entries in the RS+HS column are not failures of the
port: the emitted `Joux` and `wireguard` proofs are correct, but the
unpatched 1.12.0 release cannot replay them (`analysis incomplete`) due
to two upstream tamarin-prover issues —
[#871](https://github.com/tamarin-prover/tamarin-prover/issues/871)
(proof shape depends on thread count; already fixed on the develop
branch) and
[#881](https://github.com/tamarin-prover/tamarin-prover/issues/881)
(emitted proofs normalise differently on reload; fix pending in
[#882](https://github.com/tamarin-prover/tamarin-prover/pull/882)). The
patched `./setup.sh testing` build applies both fixes and re-verifies
both theories.

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
  `--quit-on-warning`, `--saturation`, `--open-chains`,
  `--partial-evaluation=summary|verbose` (abstract-interpretation
  fixpoint, refined-rule re-emission, stderr step trace),
  `--output-json`/`--output-dot` (solved-trace export; JSON is
  byte-exact aeson-pretty, dot labels/framing byte-exact over the
  web renderer's body dialect), `-m/--output-module` for
  `spthy`/`spthytyped`/`msr` (translate-only mode), and the
  `interactive`-mode `--with-dot`/`--with-json`/`--no-compress`;
  exit codes and summary lines mirror HS.
- **Subcommands:** `interactive` (HTTP server), `variants` (DH/BP
  intruder-rule variants dump), `test` (install self-check).

## Not yet ported

- **`diff(...)` / `--diff`** — observational-equivalence mode.
- Export modules: `-m proverif`/`proverifequiv`/`deepsec` and their
  satellite flags (`--replication-bound`, the `--proverif-no-*`
  family) — the HS `Export.hs` backend. Note the pinned upstream
  oracle itself crashes on all 21 of its own export examples (the
  `dest-*` builtins bug), so there is currently no oracle output to
  port against.

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
except to audit the output. Any work on thhis should be tracked along with full tool-call transcripts
to prove there was no access to GPL 3.0 source. 
The segments being reimplemented have to be sufficiently broad
so as to not inherit any information about the GPL 3.0 source code beyond broad module interfaces
etc). Early experiments with clean room implementation of the formatting code had limited success,
so for now there is no active work on this.

Ported files carry a short GPL 3.0 notice at the top; the upstream authors whose permission a
given file awaits are computed on demand from its citations with
`scripts/gen_license_headers.py --authors <file>` (range-blame at the pinned submodule commit).
Currently no one has granted permission, because I haven't started asking yet. If you want to
preempt this and give your permission please send me an email or file a github issue!

You can regenerate the notices with scripts/gen_license_headers.py (`--check` verifies them).

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
