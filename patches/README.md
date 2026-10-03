# Haskell oracle patch series

From the repository root, `./setup.sh testing` applies the files listed in
[`series`](series), in order, to a worktree of the pinned `tamarin-prover`
submodule. The submodule itself stays
pristine. The series targets upstream
`da8787d5506e2d35bc1c92d7653bf6265fecbddb`.

Each PR has its own patch for tracking, including stacked PRs. A stacked
patch contains only its additions beyond the parent head listed below, rebased
onto the preceding patches in `series`. Apply the whole series in order;
individual files are not necessarily standalone GitHub PR diffs.

| Patch / upstream PR | Parent PR | Notes |
|---|---|---|
| [#882](https://github.com/tamarin-prover/tamarin-prover/pull/882) — `tamarin-prover-pr-882.patch` | — | Stored-formula normalisation, including the upstream always-normalise safeguards. |
| [#910](https://github.com/tamarin-prover/tamarin-prover/pull/910) — `tamarin-prover-pr-910.patch` | — | Parser and pretty-printer fixes for #904–#909; uses the pinned upstream `reserved` helper. |
| [#952](https://github.com/tamarin-prover/tamarin-prover/pull/952) — `tamarin-prover-pr-952.patch` | — | Shared command-regression runner. |
| [#954](https://github.com/tamarin-prover/tamarin-prover/pull/954) — `tamarin-prover-pr-954.patch` | #952 | MSR rule validation and partial evaluation. |
| [#958](https://github.com/tamarin-prover/tamarin-prover/pull/958) — `tamarin-prover-pr-958.patch` | #954 | MSR proof correctness. |
| [#964](https://github.com/tamarin-prover/tamarin-prover/pull/964) — `tamarin-prover-pr-964.patch` | #958 | Diff-mode macros, restrictions, sources, and mirror correctness. |
| [#965](https://github.com/tamarin-prover/tamarin-prover/pull/965) — `tamarin-prover-pr-965.patch` | #964 | Diff rule correspondence, variant families, and partial evaluation. |
| [#955](https://github.com/tamarin-prover/tamarin-prover/pull/955) — `tamarin-prover-pr-955.patch` | #952 | Replay saved proofs without exploring irrelevant unfinished branches. |
| [#957](https://github.com/tamarin-prover/tamarin-prover/pull/957) — `tamarin-prover-pr-957.patch` | #952 | SAPIC destructor evaluation and progress translation. |
| [#959](https://github.com/tamarin-prover/tamarin-prover/pull/959) — `tamarin-prover-pr-959.patch` | #957 | Sound SAPIC channel and state optimisations. |
| [#960](https://github.com/tamarin-prover/tamarin-prover/pull/960) — `tamarin-prover-pr-960.patch` | #959 | SAPIC scope, reserved names, and inferred types. |
| [#951](https://github.com/tamarin-prover/tamarin-prover/pull/951) — `tamarin-prover-pr-951.patch` | — | Avoid unnecessary diff-mirror evaluation. |
| [#956](https://github.com/tamarin-prover/tamarin-prover/pull/956) — `tamarin-prover-pr-956.patch` | — | Omit empty graph previews in diff proof subcases. |
| [#953](https://github.com/tamarin-prover/tamarin-prover/pull/953) — `tamarin-prover-pr-953.patch` | — | Tree-sitter grammar and heuristic parser fixes. |
| [#962](https://github.com/tamarin-prover/tamarin-prover/pull/962) — `tamarin-prover-pr-962.patch` | — | Per-lemma stop-on-trace method and precedence. |

## Patch provenance

These are the PR heads used to construct the incremental patches. They identify
the checked-in source, not the current state of the PRs.

| PR | Commit |
|---|---|
| #952 | `36521a4c9a295b9c99daebf70c7b5f295314639c` |
| #954 | `5ce1ac25d065f1213bfec4ac950916f71db8ee83` |
| #958 | `60662db8459363aedb00756d7873a5cca8f1402c` |
| #964 | `b21b0d42688c6c69856c9a0da03946a81f8415df` |
| #965 | `24c68b8f7a6ce19a413e7590d1e460585e456b41` |
| #955 | `07e0954738e96bd4a0c7c2f5bff38d4bfb11e4a3` |
| #957 | `7704372e6d51795deebb958be32dbe166ca22565` |
| #959 | `c54ffbbefde3ed75bdfc84eddf0fbf8f5a55e238` |
| #960 | `02d360028a1d413022c7469832ff98527d020ba2` |
| #951 | `6a8afffb2648f62f453f205348db63f7d89dc024` |
| #956 | `38f22e3f354835efe14f028d81c749cda746835d` |
| #953 | `438d6abe17d2206f286a389f7e13dbf9a4ce7e68` |
| #962 | `56ed389f3390771d3a1b1d1d49c74d18f447be38` |

## Integration constraints

Preserve these combinations when refreshing overlapping patches:

- #957 retains both the MSR and SAPIC common regression lists.
- #953 retains #964's diff self-tests alongside its parser self-tests. The
  tree-sitter regression walk keeps #952's negative-fixture exclusion, while
  including `defaultoracle.spthy`.
- #962 preserves #965's printed diff-lemma attributes and combines its
  context-selected search method with #955's whole-saved-proof extraction.
  The internal replacement prover forces `CutNothing` so the lemma attribute
  cannot cut individual unfinished branches before whole-proof extraction.
- #962 retains #953's shared lemma-attribute grammar and whitespace handling.
  Generated grammar assets use `tree-sitter-cli@0.25.10 generate --abi 14`;
  its corpus test uses `lemma_attrs` and covers a spaced `stop-on-trace =`.

## Rust scope and validation

The oracle applies the entire series, including diff-mode patches. Rust's
trace-proving and SAPIC changes are ported one commit per Haskell commit;
`Upstream-Commit` and `Upstream-PR` commit trailers provide the mapping.

Rust does not implement observational equivalence (`--diff`). PRs #951,
#956, #964 and #965, and the diff portions of #954, #955 and #962, remain
in this series for tracking but are excluded from Rust parity coverage.
ProVerif/DeepSec export backends are also unported. Upstream tree-sitter and
manual changes remain oracle-only; the #952 command-regression runner is
reused directly.

Run the headline parity gates after building both provers:

```bash
./setup.sh testing
cargo build --release -p tamarin-prover
scripts/test.sh proof
scripts/test.sh web
```

Both commands fill or reuse the Haskell caches and save fresh results under
`scripts/results/`. Cache contents and focused regression passes do not
establish full parity: read each run's final verdict. The proof corpus does
not cover every command-sidecar option, negative case or export round trip.
See [the corpus quick-start](../scripts/README.md) and
[regression coverage](../TESTING.md#upstream-regression-coverage).

## Maintaining the series

When a PR lands, bump the submodule, remove its line from `series`, and delete
its patch after checking dependent patches. `scripts/bump_submodule.sh --check`
identifies patches already present upstream or no longer applying cleanly.

To refresh a stacked PR, diff its parent head against its captured head, apply
that delta to the preceding series with a three-way merge, resolve overlaps,
and save the resulting incremental diff. Recheck descendants when a parent
head changes; shared changes must appear only once in the series. Keep one
patch per tracked PR and update the provenance above.

Rebuild with `./setup.sh testing` after changing the pin or patch contents.
The gates select cache entries by oracle identity; leave older caches in place
so other checkouts can reuse them. Do not rebuild the oracle or edit producer
inputs during an active gate run.
