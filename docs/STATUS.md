# Compatibility and porting status

[Back to README](../README.md)

Commands below run from the repository root.

## Parity status

The correctness criterion is byte-identical raw `--prove` output, ignoring
the volatile header lines (Git revision, compile time, processing time, and
the `analyzed:` path).
The proof gate (`scripts/test.sh proof`) compares stdout and exit status for
the 523 theories in `scripts/parity_corpus.txt`. The explicit list covers
classic and AKE protocols, XOR / bilinear-pairing / multiset theories,
auto-sources, accountability, SAPiC and upstream/patch regressions. Each runs
with `--prove` and any per-theory options in `scripts/file_flags.tsv`.
Patch-only fixtures are read from `tamarin-prover-testing/examples/`.
Equivalence mode, negative inputs, export-only scenarios and extra command
sidecar options require separate coverage; see
[regression coverage](../TESTING.md#upstream-regression-coverage).

Stored proofs are validated, not just displayed: loading a proof-carrying
file replays every stored step against a freshly derived constraint system,
with cross-prover replay checked by focused regressions.

The interactive web UI (`interactive` subcommand) is verified by a crawl
gate (`scripts/test.sh web`) over 78 theories: both servers load the same theory
with the same flags, autoprove each lemma, and compare proof-tree, constraint-system,
graph and source pages. HTML is compared byte for byte, including highlighting,
markup and whitespace, except for environment fields such as timestamps and
work-directory paths. JSON envelopes also allow different key order and
encoding. Proof-node visits are capped at 400 per theory by default; truncated
crawls are reported, and `FAIL_ON_CAPPED=1` makes them fail the gate. Within
that coverage, `scripts/websweep_ledger.tsv` records accepted differences;
unexplained differences and missing comparisons fail the gate. The ledger is
not a claim that a fresh run passes.

Each gate saves its log, results and exit status under `scripts/results/`.
Use the final verdict to assess parity; neither warm caches nor focused
regression passes certify a full corpus. See [TESTING.md](../TESTING.md) for
the verification policy.

## Proof reverification

Use `./setup.sh testing` to build the pinned, patched Haskell prover used for
internal testing. Released Haskell versions may lack fixes required to replay
some proofs; [patches/README.md](../patches/README.md) documents the oracle's
patch series. Please report output differences even if the proofs cross-verify.

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
  (HS `addAutoSourcesLemma`) in batch and interactive mode, also enabled by
  an in-file `configuration: "--auto-sources"` block.
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
  Command-line help and diagnostics may differ from tamarin-prover; flag
  names and value semantics should match.
- **Subcommands:** `interactive` (HTTP server), `variants` (DH/BP
  intruder-rule variants dump), `test` (install self-check).

### Conditional directives

Conditional directives (`#ifdef`, `#else`, `#endif`) must occupy their own
physical lines, with optional indentation and same-line trailing comments.
The condition must stay on the `#ifdef` line. Active code parses comments and
quoted text normally. In inactive branches, every conditional line is structural;
all other text is ignored, including incomplete declarations, quotes, and brackets.

## Not yet ported

- **`diff(...)` / `--diff`** — observational-equivalence mode.
- Export modules: `-m proverif`/`proverifequiv`/`deepsec` and their
  satellite flags (`--replication-bound`, the `--proverif-no-*`
  family) — the HS `Export.hs` backend. The three values parse; a run
  that reaches them fails with a "not yet ported" message. The reference
  output for these backends is outside the proof and web parity gates.

Diff theories are recorded with their canonical `--diff` invocation in
`scripts/file_flags.tsv`; they join `scripts/parity_corpus.txt` once the
feature lands.
