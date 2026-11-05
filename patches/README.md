# Haskell oracle patch series

From the repository root, `./setup.sh testing` applies [`series`](series), in
order, to a worktree of the pinned `tamarin-prover` submodule. The submodule
stays pristine. The series targets upstream
`4c658fcf6653832d60ebdeec1d4d1cab4d4470c1`.

Each open PR has its own patch for tracking, including stacked PRs. A patch
contains only changes not already supplied by the pin or preceding patches.
Apply the whole series in order; individual files are not necessarily
standalone GitHub PR diffs.

| Patch / upstream PR | Parent PR | Scope |
|---|---|---|
| [#958](https://github.com/tamarin-prover/tamarin-prover/pull/958) — `tamarin-prover-pr-958.patch` | #954 (merged) | MSR proof correctness, induction, subterm witnesses and proof-method exhaustion. |
| [#964](https://github.com/tamarin-prover/tamarin-prover/pull/964) — `tamarin-prover-pr-964.patch` | #958 | Diff-mode macros, restrictions, sources and mirror correctness. |
| [#965](https://github.com/tamarin-prover/tamarin-prover/pull/965) — `tamarin-prover-pr-965.patch` | #964 | Diff rule correspondence, variant families and partial evaluation. |
| [#957](https://github.com/tamarin-prover/tamarin-prover/pull/957) — `tamarin-prover-pr-957.patch` | #952 (merged) | SAPIC destructor evaluation and progress translation. |
| [#959](https://github.com/tamarin-prover/tamarin-prover/pull/959) — `tamarin-prover-pr-959.patch` | #957 | SAPIC channel and state optimisations. |
| [#960](https://github.com/tamarin-prover/tamarin-prover/pull/960) — `tamarin-prover-pr-960.patch` | #959 | SAPIC scope, reserved names, inferred types and process/public-name export. |
| [#953](https://github.com/tamarin-prover/tamarin-prover/pull/953) — `tamarin-prover-pr-953.patch` | — | Tree-sitter grammar and heuristic parser fixes. |
| [#962](https://github.com/tamarin-prover/tamarin-prover/pull/962) — `tamarin-prover-pr-962.patch` | — | Per-lemma stop-on-trace method and precedence. |

## Patch provenance

These captured PR heads identify the checked-in source, not the current state
of the PRs.

| PR | Commit |
|---|---|
| #958 | `24d08b7ae378ddcef5287c20d4731bbd8b732ce7` |
| #964 | `eb5cbb71434d08c4aa7c3e42c270c35c3cd58864` |
| #965 | `051cfc4920dc4bf72ec539008d4f6a4e6b25c4c3` |
| #957 | `26e202e4948f53c0556cac6bdeefd7bbf700945a` |
| #959 | `d7e8ad8330eb92a8ca46faca328ddba304795fad` |
| #960 | `7d996b74b43d7694659e7e7365a3c8d6c86d4fc2` |
| #953 | `a50fb8bd76741be062e8631d633b649723ee5025` |
| #962 | `56ed389f3390771d3a1b1d1d49c74d18f447be38` |

## Integration constraints

Preserve these combinations when refreshing overlapping patches:

- #964's own changes start at parent `36892fd6` and end at `20415a09`;
  its captured head also merges develop. Keep #958's newer proof changes when
  combining that older parent with the series. Adapt diff formula-set
  operations to the pinned upstream `StoredFormulas` API.
- #957 retains both the MSR and SAPIC command-regression lists. #959 supplies
  the Yubikey baselines corresponding to its state translation.
- #953 retains guarded-formula and diff self-tests alongside parser self-tests.
  The tree-sitter regression walk excludes negative fixtures and includes
  `defaultoracle.spthy`.
- #962 preserves #965's printed diff-lemma attributes. Both saved-witness
  selection and subsequent search use the context-selected cut. Internal
  replacement searches force `CutNothing`, leaving solution selection to the
  combined proof.
- #962 retains #953's shared lemma-attribute grammar and whitespace handling.
  Generated grammar assets use `tree-sitter-cli@0.25.10 generate --abi 14`.

## Rust scope and validation

The oracle applies the entire series. Rust does not implement observational
equivalence (`--diff`): #964 and the diff portions of #965 and other PRs are
retained for tracking but excluded from Rust parity coverage. Shared trace-mode
changes, including #965's rule alignment, are ported and tested. ProVerif/DeepSec
export backends are also unported. Tree-sitter and manual changes remain
oracle-only; the upstream command-regression runner is reused directly.

Run the headline parity gates after building both provers:

```bash
./setup.sh testing
cargo build --release -p tamarin-prover
scripts/test.sh proof
scripts/test.sh web
```

Both commands fill or reuse Haskell caches and save fresh results under
`scripts/results/`. Read each run's final verdict: cache contents and focused
regression passes do not establish full parity. The proof corpus does not cover
every command-sidecar option, negative case or export round trip. CI covers
those separately with `scripts/test.sh regressions`, which discovers every
supported sidecar scenario in the patched tree and reuses upstream's assertions
and checked-in baselines. It reports diff-mode and unported-exporter exclusions
explicitly. This command needs only Rust and Maude; it prepares patched sources
without building Haskell or changing the oracle caches. See
[the corpus quick-start](../scripts/README.md) and
[regression coverage](../TESTING.md#upstream-regression-coverage).

## Maintaining the series

When a PR lands, bump the submodule, remove its line from `series`, and delete
its patch after checking dependent patches. `scripts/bump_submodule.sh --check`
identifies patches already present upstream or no longer applying cleanly.

To refresh a stacked PR, diff its parent head against its captured head, apply
that delta to the preceding series with a three-way merge, resolve overlaps,
and save the resulting incremental diff. Recheck descendants when a parent
head changes; shared changes must appear only once. Keep one patch per tracked
PR and update the provenance above.

Rebuild with `./setup.sh testing` after changing the pin or patch contents.
The gates select cache entries by oracle identity; leave older caches in place
so other checkouts can reuse them. Do not rebuild the oracle or edit producer
inputs during an active gate run.
