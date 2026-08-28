# Haskell oracle patch series

`../setup.sh testing` applies the files listed in `series`, in order, to a
worktree of the pinned `tamarin-prover` submodule. The submodule itself stays
pristine.

| Patch | Upstream | Notes |
|---|---|---|
| `tamarin-prover-pr-882.patch` | [PR #882](https://github.com/tamarin-prover/tamarin-prover/pull/882) | Stored-formula normalisation. This retains the local always-normalise safeguards found by the parity corpus after the PR was opened. |
| `tamarin-prover-pr-910.patch` | [PR #910](https://github.com/tamarin-prover/tamarin-prover/pull/910) | Parser and pretty-printer fixes for issues #904–#909. |
| `tamarin-prover-pr-919.patch` | [PR #919](https://github.com/tamarin-prover/tamarin-prover/pull/919) | Preserve exponentiation grouping under user-defined AC operators. |
| `tamarin-prover-pr-920.patch` | [PR #920](https://github.com/tamarin-prover/tamarin-prover/pull/920) | Make `--parse-only` output round-trip. |

PR #922 is not listed because it is already part of the pinned upstream commit.

When a PR lands, bump the submodule, remove its line from `series`, and delete
its patch. `scripts/bump_submodule.sh --check` identifies patches that are
already present upstream or no longer apply cleanly.
