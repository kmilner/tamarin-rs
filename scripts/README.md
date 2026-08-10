# scripts/ — parity gates, caches, and triage tools

Per-script reference. For *which* gates to run and in what order, start from
the verification ladder in [`../TESTING.md`](../TESTING.md).

Every script compares the Rust port (`target/release/tamarin-rs`) against the
patched Haskell oracle (`../tamarin-prover-testing/`, built by
`./setup.sh testing`). Result TSVs land in `results/` (gitignored).
Most scripts take `ALLOWLIST=` (file of corpus-relative paths) to run a
subset, and `RS_PATH=`/`HS_PATH=` to point at other binaries.

**Build the port first.** Every gate but `web_parity.sh` takes
`target/release/tamarin-rs` as it finds it and only checks that the file is
executable, so a binary from an older commit gates green in silence. Only the
three flag sweeps refuse one (`rs_stale_check`, `ALLOW_STALE_BIN=1`
overrides). `target/release/tamarin-rs <theory> | grep '^Git revision:'` says
what a gate actually measured.

## The HS reference caches

Five, all gitignored, none keyed alike:

| Cache | Fed by / read by | Key |
|---|---|---|
| `.hs_file_cache/` | `corpus_file_diff.sh` writes; `wf_gate.sh` reads | theory sha + flags hash |
| `.hs_pretty_cache/` | `pretty_gate.sh` | theory sha + flags hash, plus an oracle-rev stamp on the dir |
| `.web_hs_cache/` | `web_parity.sh` writes; `pane_byte_check.sh` reads | theory sha |
| `.hs_canon_cache/` | `diff_proof_raw.sh`, `corpus_raw_diff.sh`, `corpus_full_trace_diff.sh` | theory sha + lemma + cache version |
| `.hs_sweep_cache/` | the three flag sweeps | theory sha + every `#include`d file's sha + flags + **oracle-binary fingerprint** + maude path |

Only `.hs_sweep_cache/` is self-invalidating. The other four cannot see an
oracle change at all, so after one their entries are stale under unchanged
keys — which reads as a false DIFF, or as a false MATCH when the port moved
the same way. They also key an `#include`ing theory on the includer alone, so
an edit below `testParser/include/` leaves them serving the pre-edit oracle.

Two mechanisms cover part of that gap, and it is worth knowing exactly which
part:

- **A submodule bump is handled for you.** `bump_submodule.sh` renames
  `.hs_file_cache/`, `.web_hs_cache/` and `.hs_pretty_cache/` aside as
  `.pre-bump-<sha>` before rebuilding the oracle. `.hs_canon_cache/` is not in
  that list, so the single-lemma triage tools keep serving pre-bump bytes.
- **A patch rebuild is handled by nothing.** `pretty_gate.sh` stamps the
  oracle's baked `Git revision:` into `.hs_pretty_cache/.oracle_rev` and wipes
  the cache when it changes — but `setup.sh testing` applies
  `patches/tamarin-prover-fixes.patch` to a worktree and never commits it, so
  that revision is the submodule pin for every patched build, before and after
  a patch edit alike. The stamp is only ever exercised by the case
  `bump_submodule.sh` already archives. Clear the caches by hand after editing
  the patch and re-running `./setup.sh testing`.

## Primary gates — run these before trusting a change

- **`corpus_file_diff.sh`** — the ground-truth batch gate: byte-diffs full
  `--prove` stdout for all 432 corpus files against the HS cache (generating
  missing cache entries from the oracle). Slow (~30–60 min cold); run at
  milestones or with `ALLOWLIST=` for touched families. It is also the
  heaviest thing here — `JOBS=4` oracles at `-N4 -M11g` plus four Rust
  provers, up to ~44 GB of GHC heap — and the only *gate* here with **no
  `oom_score_adj` / `ulimit -v` prologue** (every other one has it, directly
  or through `sweep_common.sh` / `divergence_fixtures/_common.sh`), and no
  stale-binary or oracle-revision preflight. Wrap it yourself on a constrained
  box, and check what the two binaries are before you trust the number.
- **`wf_gate.sh`** — fast (~45 s over the whole corpus on 24 cores)
  wellformedness gate: diffs only the theory-load warning block against the
  batch cache, no proving. Run on every build. It has no fill phase of its
  own, so `.hs_file_cache/` archived — the state a bump leaves — means 432×
  `SKIP_NO_HS` and a full batch-gate run to get back.
- **`pretty_gate.sh`** — fast theory pretty-print gate (same ~45 s): diffs the
  load-time `theory … end` echo against the oracle. Run when touching parsing
  or printing. Unlike `wf_gate.sh` it owns its cache and refills it in PHASE 0
  with a cheap no-prove oracle pass; `NO_HS_FILL=1` skips that phase for a
  warm cache, and turns a cold one into an all-`SKIP` run.

  All three carry their verdict in the exit status and repeat it on the last
  line (`verdict=`): nonzero on a DIFF and on any `SKIP_*` row. A SKIP is a
  file whose bytes were never compared, which a DIFF count of 0 cannot
  distinguish from a match. A set-but-unreadable `ALLOWLIST` is `exit 2` in
  all three rather than a silent fall-through to the whole 432-file corpus.

  They differ on the third vacuity mode, a file that produced no row at all —
  a child killed by the OOM guard leaves no DIFF, no SKIP, and a still-nonzero
  total. Only `corpus_file_diff.sh` catches it: it counts the file list up
  front and fails on `ROW-COUNT=rows/N`. `wf_gate.sh` and `pretty_gate.sh`
  assert only that the row count is above zero, so on a 432-file run they
  cannot tell 431 comparisons from 432.
- **`web_parity.sh`** — interactive-mode gate: crawls both web servers per
  theory and diffs the responses — pane/JSON semantically, graph routes
  byte-for-byte. Run on server changes. `ALLOWLIST=` is REQUIRED (one
  corpus-relative path per line; `ALLOWLIST=seed` is the built-in 2-file smoke
  list, and the full cached set is the milestone sweep) — it used to fall back
  to the seed list whenever it was unset or misspelt, which turned a
  certification run into a 2-file one without saying anything. The exit status
  reports VACUITY, not divergence: `SKIP_*` rows and files that produced no row
  fail the run, while DIFF/MISSING rows are findings for the operator to triage
  against the residual ledger and leave the status alone. That triage is
  entirely manual: no script matches a `web_parity` row against
  `websweep_residual.txt`, so unlike `sweep_expected.tsv` the web ledger
  cannot report an entry that has stopped excusing anything.
- **`pane_byte_check.sh`** — byte-exact (not just semantic) check of the
  `main/message` + `main/rules` panes against the web cache. Run when byte
  fidelity of pane HTML matters. **No verdict line, and it always exits 0** —
  read the `=== SUMMARY ===` histogram and check the row count yourself. Two
  traps follow from that: its default `ALLOWLIST` is
  `websweep_residual.txt`, i.e. the set where a DIFF is *expected* rather than
  a clean corpus, so pass one explicitly; and an absent `.web_hs_cache/` makes
  every row `SKIP_NO_CACHE`, which is a run that compared nothing and still
  succeeds.
- **`rs_ref_check.sh`** — CI parity gate: `check` compares one binary's
  stripped `--prove` output hashes against the committed reference
  `ci_ref_fast.tsv` (what the `rs-parity` CI job runs on every PR);
  `generate` rewrites that reference from a trusted build of main — manual,
  needed only after a deliberate output change, a submodule bump, or a Maude
  version change (the pinned version is recorded in the reference header and
  enforced). The reference comes from main's own binary, so this is an
  RS-vs-RS self-consistency check, not an oracle comparison — and since it is
  the only parity gate CI runs, **no CI job can catch a divergence from the
  Haskell prover**. Oracle parity is established locally, by the gates above.
- **`pe_sweep.sh` / `module_sweep.sh` / `json_sweep.sh`** — flag-parity
  sweeps for `--partial-evaluation`, `-m/--output-module`, and
  `--output-json`/`--output-dot`. Built on `sweep_common.sh`: oracle outputs
  are cached content-keyed under `.hs_sweep_cache/` (timeouts cached with
  their cap), so re-sweeping after a Rust change costs only the Rust side;
  a stale `target/release` binary aborts the run (`ALLOW_STALE_BIN=1`
  overrides), where "stale" spans cargo's whole dep-info list, not just
  `crates/**/*.rs` — `tamarin-prover/data/intruder_variants_{dh,bp}.spthy`
  are `include_str!`ed into the binary. An oracle whose baked git revision is
  not the submodule pin is refused up front (`ALLOW_ORACLE_REV_MISMATCH=1`
  overrides), the same policy `divergence_fixtures/capture.sh` applies to its
  captures. Documented residuals live in `sweep_expected.tsv` and report
  as LEDGERED — any bare DIFF/ERROR row is a regression, and an entry that
  has stopped excusing anything is called out on stderr (LEDGER-STALE /
  LEDGER-UNMATCHED / LEDGER-DUP) AND counted into the verdict, so it gets
  dropped rather than sitting in the ledger as a mask waiting for the file to
  regress under it. An entry names the one
  SYMPTOM it excuses (`stdout`, `stderr`, `rc`, `json`, `dot`, `timeout/kill`)
  in its 6th column, so a file ledgered for a stderr divergence still reports a
  fresh stdout regression beside it as DIFF. Three of the four ways to compare
  nothing are NO-COMPARE, which fails the sweep rather than counting as
  agreement — and "produced anything" is judged on what survives the
  normalizers, so two runs whose only bytes are lines `nerr` drops do not count
  as having agreed. `FAMILY=1` restricts to the per-sweep
  `*_family.txt` subset (one representative per divergence class, seconds on
  a warm cache) for inner-loop iteration; the full corpora are the milestone
  runs.

  **The fourth way is timeout/kill, and it is ledgerable.** A timeout is
  fenced off as ERROR before `nocompare_check` is reached, and `apply_ledger`
  rewrites DIFF *and* ERROR to LEDGERED, which `sweep_finish` counts as clean.
  `sweep_expected.tsv` currently carries 25 such rows (17 `pe oracle-timeout`,
  4 `pe capacity`, 3 `json capacity`, 1 `module capacity`). On the
  `oracle-timeout` 17 the port is never executed at all — the sweeps return on
  `hs>=124` before invoking `$RS_BIN` — and since `hs_run` caches a timeout
  together with its cap and serves it whenever the new cap is no larger, both
  the parallel pass and the 600 s serial retry return 124 instantly on every
  future run. `LEDGER-STALE` cannot rescue these either: it fires only when a
  row comes back OK, which a cached timeout never will. Read a green sweep as
  "the files it compared agree", and treat those 25 as uncovered rather than
  as passing.

## Web-gate internals (invoked by the gates, rarely by hand)

- **`web_crawl.py`** — crawls a running server into a response manifest.
- **`web_diff.py`** / **`web_normalize.py`** — semantic manifest diff and the
  normalizer it uses. Markup routes compare structurally; the `dot` and
  `text` routes compare byte for byte bar the env-volatile tokens, because
  the port serialises both verbatim and whitespace is content there — the
  `source`/`message` panes carry the pretty printer's own trailing spaces.

## Triage tools — when a gate reports a DIFF

- **`diff_proof_raw.sh`** — one file, per-lemma raw `--prove` diff; the first
  stop for isolating which lemma diverges.
- **`corpus_raw_diff.sh`** — per-lemma raw diff across the whole corpus.
  Superseded as a gate by `corpus_file_diff.sh`; still useful when you want
  lemma-level granularity in a sweep.

  Both auto-build with `cargo build --release --bin tamarin-prover`, and no
  such bin target exists — the package is `tamarin-prover`, the binary is
  `tamarin-rs`. Cargo answers `error: no bin target named 'tamarin-prover'`
  and both scripts `exit 2` before doing any work. Run
  `cargo build --release` yourself and pass `TAM_RS_NO_AUTO_BUILD=1`.

  Both also strip a *narrower* set than the gates do — three volatile lines,
  keeping `analyzed:` — so a diff confined to that line is an artefact of the
  triage tool, not a finding.
- **`compare_parity_tsv.py`** — diff two `corpus_raw_diff` TSVs to list
  regressions/improvements between two runs.
- **`rs_vs_rs_diff.sh`** — sweep TWO Rust binaries (pre/post refactor, via
  `PRE=`/`POST=`) over the corpus with no HS involved; proves a refactor
  behaviorally inert.  Applies `file_flags.tsv` per file, defaults to the
  parity corpus, and reports prover failures as `ERROR_*` rows rather than
  scoring identical failure output as agreement. **No verdict line, and it
  always exits 0** — the inertness argument needs agreement on every file, so
  check the row count against your list yourself. Its
  `=== needs attention ===` block lists
  `ERROR_BOTH`/`ERROR_ONE`/`TIMEOUT_ONE`/`NOFILE`/`EMPTY_BOTH` and omits
  `TIMEOUT_BOTH`, which is a file neither binary finished; look for it in the
  histogram.
- **`triage_diff_vs_hs.sh`** — 3-way follow-up for `rs_vs_rs_diff` DIFFs:
  did the refactor move RS toward or away from HS?
- **`diff_maude_io.sh`** — side-by-side HS↔RS Maude command/response trace
  for one lemma (needs the trace-instrumented builds).
- **`diff_aes_calls.sh`** — compare `apply_eq_store` call counts per labeled
  site between engines; deep-solver flow triage.
- **`corpus_full_trace_diff.sh`** + **`canonicalize_trace.py`** +
  **`diff_trace.py`** — canonicalized `[EXEC]` solver-trace diffing across
  the corpus; the most detailed comparison, for locating the exact solver
  step where two runs diverge.
- **`diff_proof_tree.sh`** + **`canon_proof_tree.py`** +
  **`corpus_diff_proof_trees.sh`** — STRUCTURAL proof-tree comparison from
  the pre-byte-parity era; superseded by the byte gates (identical bytes ⇒
  identical trees), only interesting when output diverges so grossly that
  byte diffs are unreadable.

## Maintenance & measurement

- **`bump_submodule.sh`** — submodule bump workflow: rebases
  `patches/tamarin-prover-fixes.patch`, rebuilds the oracle, remaps HS line
  cites across `crates/`, archives the three gate caches it knows about (see
  above — `.hs_canon_cache/` is not among them), and prints a 5-step
  re-certification checklist. `-h` prints its header; it and
  `divergence_fixtures/check.sh` are the only scripts here that answer one, so
  everywhere else the header comment is the interface.
- **`bench.sh`** — RS-vs-HS wall/RSS benchmark; emits the README's markdown
  tables.
- **`../prove_and_reverify.sh`** (repo root) — prove with tamarin-rs, re-check
  the emitted proofs with the Haskell prover; stdout is the re-verified proof
  file.

## Divergence fixtures — corners the corpus cannot reach

`divergence_fixtures/` covers observable behaviour that no theory under the
submodule's `examples/` tree exercises, so every corpus gate stays green
across a regression in it. These fixtures pin slice-level bytes — including
one deliberate divergence, which the MATCH-only corpus gates cannot express —
against oracle captures committed in-tree, so the check needs no oracle
binary.

- **`divergence_fixtures/capture.sh`** — records the oracle's bytes for every
  fixture into `divergence_fixtures/expected/`. It resolves the oracle inside
  `tamarin-prover-testing/` and **refuses any binary whose baked git revision
  differs from the submodule pin** (same policy as
  `crates/tamarin-server/tests/capture_haskell_fixtures.sh`): these bytes are
  the reference, so a capture from another revision would silently redefine
  what the port is checked against. `--record-rs` additionally re-records the
  port side of the deliberate-divergence fixture — never a side effect.
- **`divergence_fixtures/check.sh`** — runs only the port and compares against
  those captures. Cheap (~5 s for all 19: no oracle, no proving), so it fits
  anywhere — but it currently runs *nowhere* automatically: not in CI, not
  under `cargo test`, and by construction not reachable by any corpus gate.
  Run it by hand, next to `wf_gate.sh` and `pretty_gate.sh`.
- **`divergence_fixtures/fixtures.tsv`** — per fixture: which output slices are
  compared, whether the port must `match` the oracle or `diverge` from it, and
  the flags both engines get. Two slices exist, both load-time: `wf` =
  `wf_gate.sh`'s block and `theory` = `pretty_gate.sh`'s echo (several
  fixtures are cut from one theory load), and `slice()` dies on anything else.
  So "corners the corpus cannot reach" is covered for the two blocks a bare
  theory load prints, and not for the `--prove`, `--output-json`/`--output-dot`
  or interactive surfaces.

Today's fixtures, in manifest order:

- **`mixed_ac_wf`** — AC operands headed by *different* operators, rendered in
  a wellformedness message.
- **`pair_echo_order`** — two same-headed `pair` chains in one AC chain, whose
  order is decided below the head and is not by operand size.
- **`wf_user_ac_report`** — a user-declared `[AC]` symbol in a wellformedness
  message: its operand rank against the builtin AC operators, and its
  space-padded infix spelling.
- **`sapic_lowering`** — the SAPIC translation's `LNTerm` → parser-AST
  projection: infix `exp`, right-spine `pair` splitting.
- **`sapic_user_ac`** — a user-declared `[AC]` symbol inside a SAPIC process,
  reaching a `let`'s and an `if`'s derived rule names, generated restrictions
  and `process=` attributes.
- **`sapic_nullary_cond`** — a nullary function symbol inside a SAPIC
  conditional, reaching the derived rule and restriction names, the `process=`
  attribute and the AC-variant block.
- **`sapic_formula_terms`** — a SAPIC-generated restriction that fails the
  `Formula terms` check, to be picked out of two generated candidates.
- **`formula_terms_offenders`** — two offending lemmas sharing one `Formula
  terms` header, one of them naming two offenders, spelled by HS's `Show` for
  terms rather than by the pretty printer.
- **`wf_topic_interleave`** — a wellformedness topic that closes and reopens
  under a second header, because `formulaReports`' checks report per formula
  and not per topic. An earlier and a later check's entries bracket the run,
  so its position in the report is pinned as well as its internal order.
- **`guarded_name_collision`** — an inner binder sharing a name with an
  enclosing one, which stays guarded and keeps its `// safety formula` line.
- **`guarded_freshened_names`** — the names in the `unguarded variable(s) …`
  diagnostic, whose supply runs across the whole formula, against the pretty
  printer's own names for the same binders, whose supply is restored per
  quantifier. Lemmas only: the oracle dies while printing an unguardable
  restriction.
- **`mult_restricted_report`** — both triggers of the `Multiplication
  restriction of rules` check, one rule each: a product in a conclusion, and a
  reducible left-hand side whose abstraction orphans right-hand-side variables.
  The same rule is printed at two different widths in the two slices.
- **`ac_marker_collapse`** — a `tamXCA…`-named function, where the port
  deliberately diverges from upstream — see
  `~/upstream-bug-ac-marker-collapse.md`.
- **`dual_declared_names`** — one name declared BOTH as a NoEq funsym and as a
  user `[AC]` symbol: the prefix and `op{a}b` spellings resolve NoEq, the infix
  spelling stays AC, and a bare nullary name the NoEq constant.
- **`dual_declared_exp`** — the same collision against a symbol the BUILTINS
  contribute (`exp/2` under `diffie-hellman`), so prefix `exp(a,b)` renders
  `a^b` and is a reducible Formula-terms offender while infix `a exp b` is not.
- **`dual_declared_equations`** — an `equations:` left-hand side written prefix
  over such a name: the equation registers under the NoEq symbol and makes it
  reducible.
- **`naryapp_arity_folds`** — `naryOpApp`'s argument-list shapes: an arity-1
  head folding its commas into a right-associative pair (function and macro
  heads alike), an arity-0 head applied as `f()`, and a trailing comma.
- **`ac_prefix_arities`** — prefix and `op{t1}t2` applications of a user `[AC]`
  symbol, whose arity check is skipped: any argument count parses, and the
  singleton application collapses to its argument.
- **`positional_ac_prefix`** — the same name declared `[AC]` and then NoEq, with
  a use between the two declarations and a use after both: prefix resolution
  reads the signature built so far, so the two uses render differently.

All but `ac_marker_collapse` must reproduce the pinned oracle's bytes; that one
must NOT. `check.sh` asserts BOTH sides of it, so it goes red if the port
drifts, if the divergence disappears, or if it changes shape.

`bump_submodule.sh`'s checklist lists both scripts: `capture.sh` re-reads the
fixtures from the new oracle, and `git diff divergence_fixtures/expected/` is
then upstream behaviour moving under them.

## Licensing / attribution

- **`gen_license_headers.py`** — maintains the constant GPL notice on every
  file whose upstream citations resolve (no blame needed; `--check` for
  CI-style staleness, `--preview FILE` for one file). `--authors FILE`
  computes that file's pending-permission author list on demand
  (range-blame over its cited spans at the pinned submodule commit).
- **`extend_anchor_citations.py`** — rewrites bare `Foo.hs:162` citations
  into function-extent ranges (`Foo.hs:150-183, see line 162`) so blame
  scopes stay accurate.
- **`remap_hs_cites.py`** — remaps every HS line cite in crates/ comments
  across a submodule bump (`--old <pin> --new <pin> [--apply]`): pure line
  shifts applied mechanically, moved declarations re-anchored by name,
  ambiguous cites reported for a human pass. Run automatically by
  `bump_submodule.sh`.
- **`check_hs_cites.py`** — validates every `Foo.hs:N` cite in `crates/`
  comments against the pinned submodule and exits nonzero on a finding:
  MISSING / AMBIGUOUS (a bare basename that names two upstream files, so its
  line number is uncheckable) / RANGE / BLANK / COMMENT / SEELINE (a
  `see line N` outside the extent it annotates). Nothing else catches a cite
  that has drifted — `remap_hs_cites.py` reports ambiguity rather than
  failing on it — so this is the post-bump gate. `--crate NAME` and
  `--skip CLASS` are repeatable; `--crate tamarin-prover` and `--crate
  tamarin-export` are currently the only crates at zero findings.
- **`header_identities.json`** — email → GitHub-username map used by the
  header generator.

## Data files (tracked)

- **`file_flags.tsv`** — canonical per-file extra prover flags, applied
  identically to both engines; consumed by every gate, and folded into the
  cache key as a hash so two flag sets on one theory are distinct entries.
  Its whole vocabulary today is `--auto-sources` (22 files),
  `--stop-on-trace=seqdfs` (8), `--diff` (5) and `@cd` (1). Nothing else
  reaches the gates: no `-D`, so on the 32 corpus theories containing
  `#ifdef` both engines take the same branch on every run and the conditional
  bodies are dead to the byte, wf and pretty gates alike.
- **`parity_corpus.txt`** — the canonical 432-file gate corpus: the
  submodule's examples plus one repo-local fixture
  (`../../crates/tamarin-theory/tests/fixtures/nat_sort_regression.spthy`,
  the only Nat+reuse theory — no upstream example combines the two).
  Entries resolve against `CORPUS_ROOT`, so `../..`-relative paths reach
  files outside the submodule; the caches key on content, not path.
- **`parity_corpus_fast.txt`** — the 365-file CI subset: every parity file
  proving in ≤1.5 s (plus the fastest member of otherwise-absent families);
  sized so a GitHub runner finishes in minutes.
- **`ci_ref_fast.tsv`** — committed reference for `rs_ref_check.sh`: per file,
  an input key (theory sha + flags hash) and the sha256 of main's stripped
  `--prove` stdout.
- **`sweep_expected.tsv`** — the flag sweeps' residual ledger, applied
  mechanically by `apply_ledger` (see the sweeps above); its own header
  documents the column layout and every class.
- **`pe_family.txt`** / **`module_family.txt`** / **`json_family.txt`** — the
  `FAMILY=1` subsets, one representative per divergence class.
- **`websweep_residual.txt`** — the accepted web-parity residue ledger
  (witness-index family); consulted by hand on submodule bumps. No gate reads
  it: `web_parity.sh` does not match its rows against it, so unlike
  `sweep_expected.tsv` it cannot report a stale entry, and nothing fails
  because of one. Its only other use is as `pane_byte_check.sh`'s default
  `ALLOWLIST`, where it acts as a *selection* list rather than an exclusion
  one — pass that script an explicit corpus instead.
