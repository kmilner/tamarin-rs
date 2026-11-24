# Haskell oracle patch series

This branch tracks merged upstream Tamarin changes at
`a75fec7ff13cbfcbb0a67813afb16707e981c06e`. [`series`](series) is empty:
`./setup.sh testing` builds an oracle from the pristine submodule pin.

When tracking pending upstream work, keep one incremental patch per PR in a
separate branch, including stacked PRs, so each patch can be removed on merge.

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

## Updating upstream

Update the submodule and port newly merged changes together. Pending behavior
belongs on a separate branch; remove merged patches and refresh remaining
patches when rebasing that branch onto the updated pin.

Rebuild the oracle and recertify reference captures and both corpus gates after
changing the pin or patch contents. Do not edit producer inputs during a gate
run, and do not delete older cache generations.
