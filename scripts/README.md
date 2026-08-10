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
| `.hs_file_cache/` | `corpus_file_diff.sh` | theory sha + flags hash + **oracle-binary fingerprint**; the oracle's exit status sits beside each entry as `.rc` |
| `.hs_pretty_cache/` | `pretty_gate.sh` and `wf_gate.sh` (either fills `.load.gz`; `pretty_gate.sh` derives `.theory.gz` from it) | theory sha + flags hash + **oracle-binary fingerprint** |
| `.web_hs_cache/` | `web_parity.sh` writes; `pane_byte_check.sh` reads | theory sha; the **oracle fingerprint** lives in a `.hs.fp` sidecar both scripts verify before reusing a manifest |
| `.hs_canon_cache/` | `diff_proof_raw.sh` (fingerprinted key); `corpus_raw_diff.sh`, `corpus_full_trace_diff.sh` (unfingerprinted key — entries are not exchanged between the two key forms) | theory sha + lemma + cache version (+ **oracle-binary fingerprint** for `diff_proof_raw.sh`) |
| `.hs_sweep_cache/` | the three flag sweeps | theory sha + every `#include`d file's sha + flags + **oracle-binary fingerprint** + maude path |

The oracle-binary fingerprint is `stat -c '%s.%Y'` of the HS binary
(`sweep_common.sh`'s recipe), so a rebuilt oracle — bump or patch rebuild
alike — turns every pre-rebuild entry into a clean MISS (or, for
`.web_hs_cache/`, a re-crawl) instead of a silently stale hit; nothing is
archived or wiped, and `bump_submodule.sh` deliberately leaves the caches
alone. `scripts/migrate_hs_cache_fp.sh` is the one-time rename of
pre-fingerprint entries onto the new keys. Two gaps remain: the
`corpus_raw_diff.sh` / `corpus_full_trace_diff.sh` key form carries no
fingerprint, so those triage tools keep serving pre-rebuild bytes; and every
cache except `.hs_sweep_cache/` keys an `#include`ing theory on the includer
alone, so an edit below `testParser/include/` leaves them serving the
pre-edit oracle.

## Primary gates — run these before trusting a change

- **`corpus_file_diff.sh`** — the ground-truth batch gate: byte-diffs full
  `--prove` stdout for all 432 corpus files against the HS cache (generating
  missing cache entries from the oracle). Slow (~30–60 min cold); run at
  milestones or with `ALLOWLIST=` for touched families. It also compares the
  two sides' EXIT STATUS: the oracle's rc is cached as `<key>.rc` beside its
  stdout, and identical bytes under a different status are `RC_DIFF`, a failing
  row (`RC_UNKNOWN` counts entries predating that channel and is not a
  failure). It is the heaviest thing here — `JOBS=4` oracles at `-N4 -M11g`
  plus four Rust provers, up to ~44 GB of GHC heap — and carries the same
  `oom_score_adj=1000` / `ulimit -v` 24 GiB prologue as the other gates, which
  every child inherits. What it lacks is a stale-binary or oracle-revision
  preflight, so check what the two binaries are before you trust the number,
  and lower `JOBS` on a constrained box rather than raising it.
  `ALLOWLIST` defaults to `scripts/parity_corpus.txt`, falling back to
  `$PREV_TSV`'s first column only when that file is missing too.
- **`wf_gate.sh`** — fast (~45 s over the whole corpus on 24 cores)
  wellformedness gate: diffs only the theory-load warning block, no proving.
  Run on every build. Its reference is `.hs_pretty_cache/`'s `<key>.load.gz`
  (the whole stripped load-time stdout), which its own PHASE 0 fills where
  missing — one cheap no-prove oracle load per file, shared with
  `pretty_gate.sh`, so a bump no longer costs a 30–60 min batch refill before
  this gate can compare anything.
- **`pretty_gate.sh`** — fast theory pretty-print gate (same ~45 s): diffs the
  load-time `theory … end` echo against the oracle. Run when touching parsing
  or printing. Its PHASE 0 fills the same `.load.gz` artifact and derives its
  `.theory.gz` slice from it; `NO_HS_FILL=1` skips the fill for a warm cache,
  and turns a cold one into an all-`SKIP` (failing) run. Both gates need the
  oracle binary even cache-warm — its fingerprint is part of the cache key —
  and exit 2 without one, `NO_HS_FILL=1` included. `wf_gate.sh` caps its fill
  separately (`HS_FILL_TIMEOUT`, 420 s) from the RS side's `FILE_TIMEOUT`
  (120 s); `pretty_gate.sh` uses one `FILE_TIMEOUT` (420 s) for both. Both
  DISCARD a timed-out load instead of caching partial stdout
  (the file SKIPs and is retried, so raising the cap needs no cache surgery),
  and skip `--diff` theories through the same sticky `<key>.nohs` marker, so
  the outcome does not depend on which gate ran first.

  All three carry their verdict in the exit status and repeat it on the last
  line (`verdict=`): nonzero on a DIFF, on any `SKIP_*` row (a file whose
  bytes were never compared, which a DIFF count of 0 cannot distinguish from
  a match), on `RC_DIFF` (`corpus_file_diff.sh` only: identical stdout,
  different exit status), and on `ROW-COUNT=rows/N` — all three count their
  file list up front, so a file that produced no row at all (a child killed
  by the OOM guard leaves no DIFF and no SKIP) still fails the run. A
  set-but-unreadable `ALLOWLIST` is `exit 2` in all three rather than a
  silent fall-through to the whole 432-file corpus, as is one that resolves to
  zero entries — the whole-run form of comparing nothing, which a `verdict=OK`
  over an empty histogram would otherwise read as a pass.
- **`web_parity.sh`** — interactive-mode gate: crawls both web servers per
  theory and diffs the responses — pane/JSON semantically, graph routes
  byte-for-byte. Run on server changes. `ALLOWLIST=` is REQUIRED (one
  corpus-relative path per line; `ALLOWLIST=seed` is the built-in 2-file smoke
  list, and the full cached set is the milestone sweep) — it used to fall back
  to the seed list whenever it was unset or misspelt, which turned a
  certification run into a 2-file one without saying anything. The verdict
  fails on DIVERGENCE and VACUITY both: DIFF/MISSING rows are matched
  mechanically against the machine-checked residue ledger
  `websweep_ledger.tsv` (documented rows rewrite to `LEDGERED` with their
  class; anything still DIFF/MISSING fails as `UNDOCUMENTED`), `SKIP_*` rows
  and files that produced no comparison row fail as vacuity, and ledger
  entries that excuse nothing (LEDGER-STALE / LEDGER-SHADOWED / a path that
  has left the corpus) fail the run too. `CAPPED_*` rows (a crawl truncated
  at MAX_NODES) are always printed on the verdict line and fail only under
  `FAIL_ON_CAPPED=1`. Its results TSV is 7 columns —
  `file url status hs_http rs_http kind class`, `class` being the ledger class
  of a `LEDGERED` row and `-` elsewhere. Cached HS manifests are reused only
  while both the crawl-plan stamp and the `.hs.fp` oracle-fingerprint sidecar
  match, so the first run after an oracle rebuild re-crawls the whole HS side.
  `WEB_LEDGER` picks another ledger, or `none` to run without one (which makes
  every DIFF undocumented by definition); an unreadable or malformed ledger is
  `exit 2` before any crawling, with file:line diagnostics. `ALLOWLIST` files
  may carry `#` comments and blank lines (both dropped), as they may for
  `pane_byte_check.sh`, which also collapses duplicates.
- **`pane_byte_check.sh`** — byte-exact (not just semantic) check of the
  `main/message` + `main/rules` panes against the web cache. Run when byte
  fidelity of pane HTML matters. The file list is REQUIRED (positional or
  `ALLOWLIST=`) — there is no default, because the old default was
  `websweep_residual.txt`, the set where a DIFF is *expected*. The verdict
  (exit status + `DONE_PANE_BYTE_CHECK` line) fails on DIFF, `MISSING_*`,
  any `SKIP_*` (including `SKIP_STALE_CACHE`, a cached manifest whose
  `.hs.fp` sidecar is absent or names another oracle binary), and on any
  shortfall against the expected two-rows-per-file count.
- **`rs_ref_check.sh`** — CI parity gate: `check` compares one binary's
  stripped `--prove` output hashes against the committed reference
  `ci_ref_fast.tsv` (what the `rs-parity` CI job runs on every PR), and also
  walks the reference in reverse so a row that never ran (shrunk allowlist,
  lost child) fails as `NOTRUN`; `generate` rewrites that reference from a
  trusted build of main — manual, needed only after a deliberate output
  change, a submodule bump, or a Maude version change (the pinned version is
  recorded in the reference header and enforced), and it now REQUIRES
  `--certified-by <gate-results>`: a saved oracle-gate log whose last
  `verdict=` reads OK, whose path/verdict plus the oracle fingerprint are
  stamped into the reference header. The reference still comes from main's
  own binary, so `check` is an RS-vs-RS self-consistency check, not an
  oracle comparison — and since it is the only parity gate CI runs besides
  the `divergence_fixtures` step, **no CI job can catch a general divergence
  from the Haskell prover**. Oracle parity is established locally, by the
  gates above; `--certified-by` is what ties a re-baseline back to them.
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

  **The fourth way is timeout/kill, and it reports as `UNCOMPARED`.** A
  timeout is fenced off as ERROR before `nocompare_check` is reached, so
  `apply_ledger` decides its fate — and a ledger-matched row that is ERROR, or
  whose entry names the `timeout/kill` symptom, terminates as `UNCOMPARED`
  rather than `LEDGERED`. Writing a timeout into `sweep_expected.tsv` therefore
  buys documentation, not agreement. `sweep_finish` lists up to 40 of them
  under `== n row(s) UNCOMPARED — a documented timeout/kill reached no verdict
  on them ==` and puts the count on the sentinel:
  `== DONE <sweep> <ts> verdict=<...> UNCOMPARED=<n> ==`, always present,
  `UNCOMPARED=0` on a run with none. It is deliberately NOT fatal — `verdict=`
  keeps its old meaning, so `grep -oE 'verdict=[^ ]+'` still works on these
  logs — and it puts "the files it compared agree" on the DONE line rather than
  leaving it to be inferred from the ledger. Today's ledger yields 25 such
  rows (pe 21, json 3, module 1). On the 17 `pe oracle-timeout` ones the port
  is never executed at all — the sweeps return on `hs>=124` before invoking
  `$RS_BIN` — and since `hs_run` caches a timeout together with its cap and
  serves it whenever the new cap is no larger, both the parallel pass and the
  600 s serial retry return 124 instantly on every future run; `LEDGER-STALE`
  cannot rescue them either, as it fires only when a row comes back OK. An
  UNDOCUMENTED timeout is unchanged: plain ERROR, counted into `DIFF/ERROR=n`,
  and the sweep fails.

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

  Both auto-build with `cargo build --release -p tamarin-prover` (the package;
  the binary it produces is `tamarin-rs`). `TAM_RS_NO_AUTO_BUILD=1` skips that
  and uses the binary as found.

  Both also strip a *narrower* set than the gates do — three volatile lines,
  keeping `analyzed:` — so a diff confined to that line is an artefact of the
  triage tool, not a finding.
- **`compare_parity_tsv.py`** — diff two `corpus_raw_diff` TSVs to list
  regressions/improvements between two runs.
- **`rs_vs_rs_diff.sh`** — sweep TWO Rust binaries (pre/post refactor, via
  `PRE=`/`POST=`) over the corpus with no HS involved; proves a refactor
  behaviorally inert.  Applies `file_flags.tsv` per file, defaults to the
  parity corpus, and reports prover failures as `ERROR_*` rows rather than
  scoring identical failure output as agreement. The verdict (exit status +
  `DONE_RS_VS_RS verdict=` line) fails on any DIFF and on every row that
  compared nothing — `ERROR_*`, `TIMEOUT_*` (including `TIMEOUT_BOTH`:
  "neither binary finished" is a statement about the cap, not evidence of
  inertness), `NOFILE`, `EMPTY_BOTH` — plus any allowlisted file that
  produced no row at all (checked as a set, so RESUME runs count correctly).
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
  cites across `crates/`, and prints the 6-step re-certification checklist
  (batch gate, web ladder, divergence fixtures, and — step 5 — re-capturing
  the tamarin-server HTTP fixtures, which re-stamps their `oracle_rev` and
  without which `cargo test -p tamarin-server` goes red). The gate caches are
  deliberately left alone (see the fingerprint note above — a rebuilt oracle
  turns every pre-bump entry into a MISS by key). `-h` prints its header; it
  and `divergence_fixtures/check.sh` are the only scripts here that answer one,
  so everywhere else the header comment is the interface.
- **`migrate_hs_cache_fp.sh`** — the ONE-TIME, idempotent re-keying of
  `.hs_file_cache/`, `.hs_pretty_cache/` and `.hs_canon_cache/` onto the
  fingerprint-bearing names (see the cache section above). `mv` only: it never
  runs the oracle and never writes cache content. Run it once, before the next
  gate run, or those gates regenerate everything from scratch. It exits 2 unless the checked-out oracle
  is the submodule pin — that premise is what makes adopting the old entries
  legitimate — with `ALLOW_ORACLE_REV_MISMATCH=1` to override and `DRY_RUN=1`
  to report without moving; `HS_PATH`, `MAUDE_PATH` and `CACHES` select what it
  looks at. Per cache it prints migrated / already / other-oracle / collided /
  unrecognised / failed counts, reports a leftover `.oracle_rev` stamp as safe
  to delete, and ends in `DONE_MIGRATE_HS_CACHE_FP verdict=OK|FAILED` (exit 1
  on a failed rename). Do not run `triage_diff_vs_hs.sh` before the migration:
  it still writes un-fingerprinted keys.
- **`capture_cli_refs.sh`** — captures the ORACLE's stdout for every row of
  `crates/tamarin-prover/tests/fixtures/cli_refs/cases.tsv`, which is the argv
  table `cli_e2e.rs`'s flag pins read as well — adding a pin is "add a row,
  re-run this". Deliberately serial and proving: the oracle's `--prove` output
  is nondeterministic under parallel load, and a flaky reference is worse than
  none. Writes `<name>.stdout` (raw bytes; both sides normalise build info,
  `analyzed:` and the processing time at comparison time) plus `CAPTURED.tsv`
  (oracle path and fingerprint, submodule pin, maude version, per-row byte
  counts), which the tests assert lists exactly the rows in `cases.tsv`, so a
  partial capture cannot pass as a complete one. Ends in
  `DONE_CAPTURE_CLI_REFS verdict=<...> captured=N/M`, nonzero on any row that
  is missing, empty, or fails its `relation` column. Env: `HS_PATH`, `MAUDE`,
  `FILE_TIMEOUT` (120 s), `ALLOW_ORACLE_REV_MISMATCH`.
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
  those captures. Cheap (~5 s for all 19: no oracle, no proving), which is why
  CI runs it: the `test` job's `Divergence fixtures` step builds
  `--profile ci --bin tamarin-rs`, prepends `/opt/maude` to `PATH` (the port's
  own probe does not read `MAUDE_PATH`) and invokes it with an absolute
  `RS_PATH`, so a drift on any fixture, a lost AC-marker divergence, or an
  `expected/oracle_rev` that is not the current submodule pin fails the build.
  It is not reachable by `cargo test` or by any corpus gate, so run it by hand
  too, next to `wf_gate.sh` and `pretty_gate.sh`.
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
  `--stop-on-trace=seqdfs` (8), `--diff` (5), `@cd` (1) and `-D` (4). 32 corpus
  theories contain `#ifdef`; the four `-D` rows put the DEFINED branch of
  `testParser/define.spthy` and three `thesis-LaraSchmid-evoting` theories in
  front of every gate that reads this file — and take their bare branch out of
  reach in exchange. The other 28 still prove one branch only. `-D` is a
  cmdargs `flagOpt`, so the value must be ATTACHED (`-D=A`, never `-D A`, which
  reads as a positional input file).
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
  `--prove` stdout. Its header records the maude version `check` enforces and,
  from the next `generate` on, the oracle fingerprint (`# oracle:`) and the
  `--certified-by` log and verdict (`# certified-by:`) that justified the
  re-baseline. A `file_flags.tsv` change makes the affected rows
  `INPUT_CHANGED` until it is regenerated — which the four new `-D` rows
  currently are.
- **`sweep_expected.tsv`** — the flag sweeps' residual ledger, applied
  mechanically by `apply_ledger` (see the sweeps above); its own header
  documents the column layout and every class. A `timeout/kill` entry
  documents a row rather than excusing it: those terminate as `UNCOMPARED`.
- **`pe_family.txt`** / **`module_family.txt`** / **`json_family.txt`** — the
  `FAMILY=1` subsets, one representative per divergence class.
- **`websweep_residual.txt`** — the accepted web-parity residue *path list*
  (witness-index family). No gate reads it any more: the machine-checked form
  is `websweep_ledger.tsv` below, and `pane_byte_check.sh` no longer defaults
  to this file (it was a *selection* list where a DIFF is expected, not a
  corpus to hold to byte parity).
- **`websweep_ledger.tsv`** — the web-parity residue ledger `web_parity.sh`
  applies mechanically (path / class / symptom / note): documented
  DIFF/MISSING rows report `LEDGERED`, entries that excuse nothing fail the
  verdict (LEDGER-STALE / LEDGER-SHADOWED / not-in-corpus), and a malformed
  ledger aborts the gate before it crawls anything. Its own header documents
  the columns and classes.
