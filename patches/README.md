# Haskell oracle patch series

This branch tracks merged upstream Tamarin changes at
`a75fec7ff13cbfcbb0a67813afb16707e981c06e`. [`series`](series) is empty:
`./setup.sh testing` builds an oracle from the pristine submodule pin.

Pending upstream work lives on the stacked `bump-tamarin-prover-patches`
branch. Each open PR there has its own incremental patch, including stacked
PRs, so it can be tracked and removed when it merges.

## Validation

Build both provers, then run the headline parity gates and upstream command
regressions:

```bash
./setup.sh testing
cargo build --release -p tamarin-prover
scripts/test.sh proof
scripts/test.sh web
scripts/test.sh regressions
```

The proof and web gates fill or reuse oracle caches under `scripts/.gate_cache`.
The pin and patch contents identify the oracle generation; older caches stay
available to other checkouts. Rust binary changes do not invalidate Haskell
results. Read each run's final verdict to establish parity.

Rust excludes observational equivalence (`--diff`) and the unported
ProVerif/DeepSec exporters. Supported scenarios are selected individually from
upstream command sidecars, including negative cases and export round trips.
See [TESTING.md](../TESTING.md) and [scripts/README.md](../scripts/README.md).

## Maintaining the split

Update the submodule and port newly merged changes on `bump-tamarin-prover`.
Then rebase `bump-tamarin-prover-patches` on it, remove landed PR patches and
refresh the remaining incremental patches against their current PR heads.
Keep behavior specific to open PRs on the stacked branch.

Rebuild the oracle and recertify reference captures and both corpus gates after
changing the pin or patch contents. Do not edit producer inputs during a gate
run, and do not delete older cache generations.
