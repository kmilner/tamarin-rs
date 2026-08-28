# tamarin-prover (Rust port)

A Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/) with the goal
of reproducing the Haskell prover's output byte-for-byte. Across the README's
representative suite it is 4.3–88× faster than the most recent Tamarin
release (median 19×), with 2.2–22× lower peak process-tree memory at one
core.

## Important notes

Always verify generated proofs against regular tamarin-prover. All proofs generated
by this prover should be reverifiable against regular tamarin
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
  432-file corpus — the feature-complete theories under
  `tamarin-prover/examples/` plus one repo-local regression fixture. Stored
  proofs replay and validate across provers in both directions, and the
  interactive web UI agrees page-for-page with the Haskell server except for
  a small documented cosmetic residue, enumerated theory-by-theory in
  `scripts/websweep_residual.txt` (77 files) and re-checked by a ≈69,600-page
  crawl sweep — see [Parity status](#parity-status).
- **Performance:** 4.3–88× faster than the most recent Tamarin release
  (1.12.0) across 1–16 cores (median 19×). At one core, peak process-tree
  memory is 2.2–22× lower; at sixteen cores it ranges from 18% higher on
  tiny `NSPK3` to 13× lower on `CCITT_X509_3` — see
  [Performance](#performance).
- **Not yet ported:** observational equivalence (`--diff`) and the
  ProVerif / DeepSec export modules — see
  [Not yet ported](#not-yet-ported).
- **Testing process:** [TESTING.md](TESTING.md) documents the parity-gate
  ladder and divergence-debugging tools.


## Repository layout

```
crates/            the Rust port (crate breakdown below)
scripts/           parity gates, benchmarks, and divergence-debugging harnesses
tests/             wellformedness fixture corpus
patches/
  series                       ordered list of one Haskell patch per
                               not-yet-merged upstream PR
  tamarin-prover-pr-*.patch    patches applied to the testing oracle
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
`scripts/bump_submodule.sh` automates it (checks each PR patch against the new
pin, rebuilds the oracle, leaves fingerprinted old cache entries safely in
place, and prints the verification checklist; `--check` changes nothing).

The release profile uses `lto = "fat"` and `codegen-units = 1`.

Building the Haskell oracle is needed only for the parity gates, not for the
Rust build itself:

```
./setup.sh testing                   # patched oracle → tamarin-prover-testing/
```

This materialises a git worktree of the pinned commit at
`tamarin-prover-testing/`, applies the files in `patches/series` there (the
submodule itself stays untouched), and builds it with stack. When needed, the
testing worktree is reset to the current branch's pin; ignored `.stack-work/`
artifacts remain as the compiler cache. The parity scripts discover that
binary automatically; `HS_PATH=<binary>` overrides.

## Parity status

The correctness criterion is byte-identical raw `--prove` output, ignoring
the volatile header lines (Git revision, compile time, processing time, and
the `analyzed:` path).
The batch gate (`scripts/corpus_file_diff.sh`, corpus in
`scripts/parity_corpus.txt`) currently reports:

| Result | Files | Meaning |
|--------|------:|---------|
| MATCH | 432 | Rust output byte-identical to Haskell |
| DIFF  |   0 | — |
| SKIP  |   0 | — |

The corpus spans every feature-complete theory family under `tamarin-prover/examples/` —
classic and AKE protocols, XOR / bilinear-pairing / multiset theories, the
auto-sources suites, accountability case studies, and 79 SAPiC `process:`
theories — each run under its canonical upstream invocation: bare `--prove`,
plus the extra flags `scripts/file_flags.tsv` records for the 40 theories
whose upstream recipe needs them. Theories outside the corpus need an unported
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
GNU time plus a 20 ms process-tree sampler. Peak RSS is the largest sum across
all simultaneously live command processes, including Maude workers. Single
run per cell (wall-clock is noisy ±10%).
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
| `NSPK3` | 4.9 s | 2.3 s (-53%) | **0.5 s (-90%)** | 105 MB | 92 MB (-12%) | **48 MB (-54%)** |
| `Joux` | 22.2 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **4.3 s (-81%)** | 294 MB | — | **77 MB (-74%)** |
| `stateverif_left_right` | 47.6 s | 39.2 s (-18%) | **2.6 s (-95%)** | 1052 MB | 1143 MB (+9%) | **60 MB (-94%)** |
| `Yubikey` | 66.4 s | 50.3 s (-24%) | **4.2 s (-94%)** | 426 MB | 378 MB (-11%) | **96 MB (-77%)** |
| `mixvote_SmHh-multi-session` | 73.9 s | 53.8 s (-27%) | **3.6 s (-95%)** | 1051 MB | 1450 MB (+38%) | **61 MB (-94%)** |
| `gcm` | 134.6 s | 134.8 s (+0%) | **9.4 s (-93%)** | 1492 MB | 1543 MB (+3%) | **117 MB (-92%)** |
| `wireguard` | 166.1 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **5.9 s (-96%)** | 2146 MB | — | **99 MB (-95%)** |
| `CCITT_X509_3` | 574.3 s | 35.6 s (-94%) | **24.2 s (-96%)** | 4905 MB | 309 MB (-94%) | **306 MB (-94%)** |

**4 cores**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 2.6 s | 1.8 s (-31%) | **0.4 s (-85%)** | 140 MB | 120 MB (-14%) | **117 MB (-16%)** |
| `Joux` | 18.1 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **4.2 s (-77%)** | 346 MB | — | **140 MB (-60%)** |
| `stateverif_left_right` | 26.2 s | 34.6 s (+32%) | **1.6 s (-94%)** | 992 MB | 1258 MB (+27%) | **145 MB (-85%)** |
| `Yubikey` | 48.0 s | 40.2 s (-16%) | **2.5 s (-95%)** | 425 MB | 389 MB (-8%) | **182 MB (-57%)** |
| `mixvote_SmHh-multi-session` | 37.8 s | 33.6 s (-11%) | **1.5 s (-96%)** | 1053 MB | 1465 MB (+39%) | **144 MB (-86%)** |
| `gcm` | 107.0 s | 86.0 s (-20%) | **4.3 s (-96%)** | 1477 MB | 1578 MB (+7%) | **219 MB (-85%)** |
| `wireguard` | 107.7 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **2.9 s (-97%)** | 2228 MB | — | **185 MB (-92%)** |
| `CCITT_X509_3` | 236.9 s | 13.8 s (-94%) | **6.7 s (-97%)** | 9325 MB | 601 MB (-94%) | **640 MB (-93%)** |

**16 cores**

| Theory | HS time | RS+HS time | RS time | HS memory | RS+HS memory | RS memory |
|--------|--------:|-----------:|--------:|----------:|-------------:|----------:|
| `NSPK3` | 2.6 s | 1.8 s (-31%) | **0.4 s (-85%)** | 196 MB | 235 MB (+20%) | **231 MB (+18%)** |
| `Joux` | 19.3 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **4.4 s (-77%)** | 395 MB | — | **262 MB (-34%)** |
| `stateverif_left_right` | 25.9 s | 35.3 s (+36%) | **1.6 s (-94%)** | 1081 MB | 1197 MB (+11%) | **369 MB (-66%)** |
| `Yubikey` | 45.0 s | 39.3 s (-13%) | **2.4 s (-95%)** | 466 MB | 588 MB (+26%) | **401 MB (-14%)** |
| `mixvote_SmHh-multi-session` | 29.9 s | 26.7 s (-11%) | **1.4 s (-95%)** | 1100 MB | 1469 MB (+34%) | **402 MB (-63%)** |
| `gcm` | 71.8 s | 76.0 s (+6%) | **3.4 s (-95%)** | 1563 MB | 1611 MB (+3%) | **487 MB (-69%)** |
| `wireguard` | 84.5 s | not supported ([#871](https://github.com/tamarin-prover/tamarin-prover/issues/871), [#881](https://github.com/tamarin-prover/tamarin-prover/issues/881); see below) | **2.6 s (-97%)** | 2508 MB | — | **397 MB (-84%)** |
| `CCITT_X509_3` | 220.2 s | 9.0 s (-96%) | **2.5 s (-99%)** | 11607 MB | 860 MB (-93%) | **891 MB (-92%)** |

<!-- BENCH:END -->

Memory in the tables above is the largest simultaneous RSS sum across the
prover's complete process tree, sampled every 20 ms; see the methodology note
in the generated block. Across all theories and core counts the Rust port is
4.3–88× faster than the 1.12.0 release (median 19×). At one core, peak
memory is 2.2–22× lower. At sixteen cores the fixed worker-pool overhead is
visible on small theories: memory ranges from 18% higher on `NSPK3` to 13×
lower on `CCITT_X509_3`. The smallest speed gains are on `Joux`, whose runtime
is dominated by AC-heavy Maude queries both provers pay for equally.

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
  `restrictions:`, `tactic:`, `heuristic:`, `#define`/`#include`
  preprocessing, multi-line comments, Unicode symbols — plus the
  wellformedness checks (`tamarin_theory::wellformedness`).
- **Elaborator:** rule signatures, lemma formulas → guarded form, macro and
  predicate expansion, restriction insertion, source-kind classification.
- **Builtins:** `hashing`, `symmetric-encryption`, `asymmetric-encryption`,
  `signing`, `revealing-signing`, the four `dest-*` destructor builtins,
  `diffie-hellman`, `xor`, `bilinear-pairing`, `multiset`,
  `natural-numbers`, `locations-report`, `reliable-channel`, plus custom
  functions and equations.
- **Solver:** full constraint-system port — simplification, source
  refinement/saturation, chain extension, contradiction detection,
  induction, stored-proof replay with plain-load proof validation, and
  AC-modulo unification via pooled Maude.
- **`--auto-sources`:** automatic sources-lemma generation
  (HS `addAutoSourcesLemma`).
- **SAPiC `process:`** — the process-calculus frontend, byte-identical to HS
  `Sapic.translate`: core constructs, mutable state, locks, `let`
  bindings/destructors, secret/private channels, progress and
  reliable-channel translations, `report()`, and the pure-state path the
  in-file `options: translation-state-optimisation` opts into.
- **Accountability** — `test` case tests and `accounts for` lemmas expand
  into the verification-condition lemmas (six per case test plus one
  `_verif_empty` per lemma) and case-test predicates, with the
  "Accountability (RP check)" wellformedness report
  (HS `Accountability.translate` / `Accountability.Generation`).
- **Heuristics:** smart (`s`/`S`), goal-number (`C`/`c`), injective
  (`i`/`I`), SAPiC (`p`/`P`), oracle (`o`/`O`), and `tactic:` rankings —
  per-file, per-lemma, or CLI-overridden (HS `selectHeuristic`).
- **CLI:** `--prove`/`--lemma`, `--heuristic`, `--oraclename`,
  `--oracle-only`, `--processors`, `--maude-processes`,
  `--derivcheck-timeout`, `--stop-on-trace` (all five policies —
  `dfs`/`bfs`/`seqdfs`/`sorry`/`none` — including in-file
  `configuration:` blocks), `-D` defines, `--parse-only`,
  `--precompute-only`, `-o/--output` and `-O/--Output`,
  `--quit-on-warning`, `--saturation`, `--open-chains`, `--no-ndc`,
  `--partial-evaluation=summary|verbose` (abstract-interpretation
  fixpoint, refined-rule re-emission, stderr step trace),
  `--output-json`/`--output-dot` (solved-trace export; JSON is
  byte-exact aeson-pretty, DOT is byte-exact whole-document — the
  `showDot` serializer the interactive graph routes also serve),
  `-m/--output-module` for
  `spthy`/`spthytyped`/`msr` (translate-only mode), the `--with-maude`
  path, and the `--with-dot`/`--with-json` renderers interactive mode
  draws graphs with; exit codes and summary lines mirror HS.
  `--quiet`, `-v/--verbose` and `--no-compress` are accepted
  without changing batch output: `--quiet` and `--no-compress` are inert
  in HS too, and HS's verbose stderr trace has no port yet.  `--bound=N`
  truncates batch `--prove` search at proof depth N with
  `sorry /* bound N hit */` leaves (HS `boundProofDepth`); in interactive
  mode it is accepted but dead, as in HS (the web routes carry their own
  per-request bound).
  The front end itself does not produce identical output to tamarin-prover,
  although flag names and value semantics should match.
- **Subcommands:** `interactive` (HTTP server), `variants` (DH/BP
  intruder-rule variants dump), `test` (install self-check).

## Not yet ported

- **`diff(...)` / `--diff`** — observational-equivalence mode.
- Export modules: `-m proverif`/`proverifequiv`/`deepsec` and their
  satellite flags (`--replication-bound`, the `--proverif-no-*`
  family) — the HS `Export.hs` backend. The three values parse; a run
  that reaches them fails with a "not yet ported" message. The reference
  output the pinned oracle offers is thin: over the 1042-file corpus
  `-m proverif` and `-m proverifequiv` produce output for the same 44
  files, none of which has an `equivLemma`; `-m deepsec` emits nothing
  anywhere; and 38 of the 123 process-bearing files, including all 21
  under `examples/sapic/export/`, crash the oracle, whose `builtins`
  table has no arm for the `dest-*` or `natural-numbers` names.

Diff theories are recorded with their canonical `--diff` invocation in
`scripts/file_flags.tsv`; they join `scripts/parity_corpus.txt` once the
feature lands.

## Crate layout

The workspace crates under `crates/` (`tamarin-prover/` here is the binary
crate, distinct from the `tamarin-prover/` submodule at the repository root):

```
tamarin-utils/          fresh-name state, pretty-printer, DAG/dot helpers, small util types
tamarin-term/           Term/LTerm/LNTerm, MaudeSig, Maude IPC, normalisation
tamarin-parser/         .spthy AST + lexer + parser + #include resolver
tamarin-theory/         elaborator, wellformedness, constraint system, solver, simplify, sources, replay
tamarin-sapic/          SAPiC process: frontend — translation to multiset-rewrite rules
tamarin-accountability/ accountability frontend — case tests → VC lemmas
tamarin-test-support/   maude resolution shared by every crate's maude-gated tests
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
a 'translation' of GPL 3 code.

Relicensing tamarin-prover is made difficult because of a very long tail of
contributors over many years, making it very difficult to get in touch with each
and every one of them to relicense their contributions. An eventual goal is to
relicense tamarin-rs fully under MIT if possible, which will require one or both of:

- Permission of the largest contributors (or their institutions, where the institution
  is the only party capable of relicensing).
- Where getting permission is infeasible, replacing the associated contribution with a
  cleanroom implementation of the feature.

Cleanroom implementations have to be performed by an LLM with access only to the observable
behaviour of tamarin-prover, not the source code. Unfortunately I (as a contributor to
tamarin-prover) am, to my understanding, tainted and cannot participate in this process
except to audit the output. Any work on this should be tracked along with full tool-call transcripts
to prove there was no access to GPL 3.0 source.
The segments being reimplemented have to be sufficiently broad
so as to not inherit any information about the GPL 3.0 source code beyond broad module interfaces
etc. Early experiments with clean room implementation of the formatting code had limited success,
so for now there is no active work on this.

Ported files carry a short GPL 3.0 notice at the top; the upstream authors whose permission a
given file awaits are computed on demand from its citations with
`scripts/gen_license_headers.py --authors <file>` (range-blame at the pinned submodule commit).
The same script regenerates the notices; `--check` verifies them.
Currently no one has granted permission, because I haven't started asking yet. If you want to
preempt this and give your permission please send me an email or file a github issue!

So, in summary:
- All Rust code in this repository (`crates/`, `scripts/`, `tests/`) is
  MIT-licensed by default, however code which is based on GPL 3.0 code is
  still GPL 3.0 until either replaced by a cleanroom implementation or
  granted permission for relicensing by the related authors. This is indicated
  by comments at the top of those files. THE BINARY YOU BUILD IS GPL 3.0.
- The `tamarin-prover/` submodule is a separate upstream project licensed under
  GPL 3.0 (see `tamarin-prover/LICENSE`). The files under `patches/` modify
  those GPL 3 sources and are therefore themselves GPL-3.
- None of this is legal advice, consult a lawyer.
