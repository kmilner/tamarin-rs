# scripts/ — parity gates, caches, and triage tools

Every script compares the Rust port (`target/release/tamarin-rs`) against the
patched Haskell oracle (`../tamarin-prover-testing/`, built by
`./setup.sh testing`). Result TSVs land in `results/` (gitignored); the HS
reference caches live in `.hs_file_cache/`, `.hs_pretty_cache/`,
`.hs_sweep_cache/` and `.web_hs_cache/` (all gitignored). They are not keyed
alike: `.hs_sweep_cache/` keys on the theory sha PLUS the flag set, the oracle
binary's fingerprint and the maude path, so rebuilding the oracle invalidates
it by itself, while the other three key on the theory sha alone and must be
cleared by hand after a submodule bump or an oracle rebuild
(`bump_submodule.sh`'s checklist says so).
Most scripts take `ALLOWLIST=` (file of corpus-relative paths) to run a
subset, and `RS_PATH=`/`HS_PATH=` to point at other binaries.

## Primary gates — run these before trusting a change

- **`corpus_file_diff.sh`** — the ground-truth batch gate: byte-diffs full
  `--prove` stdout for all 432 corpus files against the HS cache (generating
  missing cache entries from the oracle). Slow (~30–60 min cold); run at
  milestones or with `ALLOWLIST=` for touched families.
- **`wf_gate.sh`** — fast (~72 s) wellformedness gate: diffs only the
  theory-load warning block against the batch cache, no proving. Run on every
  build.
- **`pretty_gate.sh`** — fast theory pretty-print gate: diffs the load-time
  `theory … end` echo against the oracle. Run when touching parsing or
  printing.
- **`web_parity.sh`** — interactive-mode gate: crawls both web servers per
  theory and diffs the responses — pane/JSON semantically, graph routes
  byte-for-byte. Run on server changes. `ALLOWLIST=` is REQUIRED (one
  corpus-relative path per line; `ALLOWLIST=seed` is the built-in 2-file smoke
  list, and the full cached set is the milestone sweep) — it used to fall back
  to the seed list whenever it was unset or misspelt, which turned a
  certification run into a 2-file one without saying anything. The exit status
  reports VACUITY, not divergence: `SKIP_*` rows and files that produced no row
  fail the run, while DIFF/MISSING rows are findings for the operator to triage
  against the residual ledger and leave the status alone.
- **`pane_byte_check.sh`** — byte-exact (not just semantic) check of the
  `main/message` + `main/rules` panes against the web cache. Run when byte
  fidelity of pane HTML matters.
- **`rs_ref_check.sh`** — CI parity gate: `check` compares one binary's
  stripped `--prove` output hashes against the committed reference
  `ci_ref_fast.tsv` (what the `rs-parity` CI job runs on every PR);
  `generate` rewrites that reference from a trusted build of main — manual,
  needed only after a deliberate output change, a submodule bump, or a Maude
  version change (the pinned version is recorded in the reference header and
  enforced).
- **`pe_sweep.sh` / `module_sweep.sh` / `json_sweep.sh`** — flag-parity
  sweeps for `--partial-evaluation`, `-m/--output-module`, and
  `--output-json`/`--output-dot`. Built on `sweep_common.sh`: oracle outputs
  are cached content-keyed under `.hs_sweep_cache/` (timeouts cached with
  their cap), so re-sweeping after a Rust change costs only the Rust side;
  a stale `target/release` binary aborts the run (`ALLOW_STALE_BIN=1`
  overrides). Documented residuals live in `sweep_expected.tsv` and report
  as LEDGERED — any bare DIFF/ERROR row is a regression, and an entry that
  has stopped excusing anything is called out on stderr (LEDGER-STALE /
  LEDGER-UNMATCHED / LEDGER-DUP) so it gets dropped. An entry names the one
  SYMPTOM it excuses (`stdout`, `stderr`, `rc`, `json`, `dot`, `timeout/kill`)
  in its 6th column, so a file ledgered for a stderr divergence still reports a
  fresh stdout regression beside it as DIFF. A row where neither side produced
  anything to compare is NO-COMPARE, which fails the sweep rather than counting
  as agreement — and "produced anything" is judged on what survives the
  normalizers, so two runs whose only bytes are lines `nerr` drops do not count
  as having agreed. `FAMILY=1` restricts to the per-sweep
  `*_family.txt` subset (one representative per divergence class, seconds on
  a warm cache) for inner-loop iteration; the full corpora are the milestone
  runs.

## Web-gate internals (invoked by the gates, rarely by hand)

- **`web_crawl.py`** — crawls a running server into a response manifest.
- **`web_diff.py`** / **`web_normalize.py`** — semantic manifest diff and the
  normalizer it uses.

## Triage tools — when a gate reports a DIFF

- **`diff_proof_raw.sh`** — one file, per-lemma raw `--prove` diff; the first
  stop for isolating which lemma diverges.
- **`corpus_raw_diff.sh`** — per-lemma raw diff across the whole corpus.
  Superseded as a gate by `corpus_file_diff.sh`; still useful when you want
  lemma-level granularity in a sweep.
- **`compare_parity_tsv.py`** — diff two `corpus_raw_diff` TSVs to list
  regressions/improvements between two runs.
- **`rs_vs_rs_diff.sh`** — sweep TWO Rust binaries (pre/post refactor, via
  `PRE=`/`POST=`) over the corpus with no HS involved; proves a refactor
  behaviorally inert.  Applies `file_flags.tsv` per file, defaults to the
  parity corpus, and reports prover failures as `ERROR_*` rows rather than
  scoring identical failure output as agreement.
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
  `patches/tamarin-prover-fixes.patch`, rebuilds the oracle, and lists the
  gate recipe to re-certify (caches must be regenerated after a bump).
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
  those captures. Cheap (no oracle, no proving), so it fits anywhere.
- **`divergence_fixtures/fixtures.tsv`** — per fixture: which output slices are
  compared (`wf` = `wf_gate.sh`'s block, `theory` = `pretty_gate.sh`'s echo;
  several are cut from one theory load), whether the port must `match` the
  oracle or `diverge` from it, and the flags both engines get.

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
  `--skip CLASS` are repeatable; `--crate tamarin-prover` is currently the
  only crate at zero findings.
- **`header_identities.json`** — email → GitHub-username map used by the
  header generator.

## Data files (tracked)

- **`file_flags.tsv`** — canonical per-file extra prover flags (`@cd`,
  defines, …); consumed by every gate.
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
- **`websweep_residual.txt`** — the accepted web-parity residue ledger
  (witness-index family); consulted on submodule bumps.
