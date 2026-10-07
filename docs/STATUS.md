# Compatibility and porting status

[Back to README](../README.md)

Commands below run from the repository root.

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

The interactive web UI (`interactive` subcommand) is verified by a crawl
gate (`scripts/web_parity.sh`): both servers load the same theory with the
same flags, autoprove each lemma, and compare proof-tree, constraint-system,
graph and source pages. HTML is compared byte for byte, including highlighting,
markup and whitespace, except for environment fields such as timestamps and
work-directory paths. JSON envelopes also allow different key order and
encoding. Proof-node visits are capped at 400 per theory by default; truncated
crawls are reported, and `FAIL_ON_CAPPED=1` makes them fail the gate. Within
that coverage, the two UIs agree except for a small documented residue that
renders *identical* proof states with different internal
counter values (fresh-variable witness indices, goal-creation numbers,
term-abbreviation picks on a few AC-heavy theories); these never appear in
proof scripts, proof structure, or verdicts.

## Proof reverification

At time of writing there are two upstream issues in Haskell affecting proof
reverifiability: https://github.com/tamarin-prover/tamarin-prover/issues/871
(fixed on the develop branch, not yet in a release) and
https://github.com/tamarin-prover/tamarin-prover/issues/881 (fix pending in
https://github.com/tamarin-prover/tamarin-prover/pull/882). If you'd like to
build a version of tamarin-prover that has the fixes applied already, you can
use `./setup.sh testing`; we use this patched version for internal testing.
These fixes address the affected proof-replay cases. Please report any
remaining output differences in GitHub issues, even if the proofs cross-verify.

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
  output the pinned oracle offers is thin: over the 1042-file corpus
  `-m proverif` and `-m proverifequiv` produce output for the same 44
  files, none of which has an `equivLemma`; `-m deepsec` emits nothing
  anywhere; and 38 of the 123 process-bearing files, including all 21
  under `examples/sapic/export/`, crash the oracle, whose `builtins`
  table has no arm for the `dest-*` or `natural-numbers` names.

Diff theories are recorded with their canonical `--diff` invocation in
`scripts/file_flags.tsv`; they join `scripts/parity_corpus.txt` once the
feature lands.
