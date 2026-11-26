# tamarin-prover (Rust port)

A Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/), a tool
for analysing security protocols. It aims to reproduce the Haskell prover's
output exactly, with faster proof search and lower memory use.

The port supports batch proving and the interactive web GUI, including SAPIC
and accountability. Observational equivalence (`--diff`) and ProVerif / DeepSec
exports are not yet implemented.

**Always reverify generated proofs with the Haskell tamarin-prover.** This port was
translated with extensive LLM assistance; don't rely on its results alone.
That said, for many theories it is still faster to prove using tamarin-rs and
verify the result with tamarin-prover than it is to prove directly in
tamarin-prover.

## Quick start

Build prerequisites: Rust, Node.js (22.12+ or 24+), npm, Git, Bash, and Make.
The default build uses Maude. The experimental proved-only and native backends can run supported theories
without a Maude executable. See the [backend coverage table](https://github.com/kmilner/tamarin-algebra/blob/main/lean/README.md#coverage-and-remaining-work)
and [Algebra backends](#algebra-backends) below.
Server-rendered graphs require Graphviz. See the [Tamarin installation instructions](https://tamarin-prover.com/manual/master/book/002_installation.html).


```bash
make install
tamarin-rs --prove theory.spthy
tamarin-rs interactive /path/to/theories
```

`make install` installs a release build to `~/.local/bin/tamarin-rs` by default, you may
have to add it to your PATH if it is not already (or just use the full path directly).

See the [build and development guide](docs/DEVELOPMENT.md) for custom install
paths, frontend development, and the Haskell test build.

## batch-tamarin

Set a [batch-tamarin](https://github.com/tamarin-prover/batch-tamarin) recipe's
`tamarin_versions.<alias>.path` to `tamarin-rs` or its full path. Its generated
`+RTS -N<cores> -RTS` arguments work automatically, setting the worker count
just like `--processors=<cores>`. The `-M<size>` RTS option is also accepted
as an alias for `--memory-limit` (see below); other RTS options are rejected.
batch-tamarin handles memory limits and timeouts itself. Tested with
batch-tamarin 1.2.0.

## Memory limits

For batch runs on Linux and macOS, `--memory-limit=<size>` (or `+RTS -M<size> -RTS`)
sets a threshold for the combined memory of the prover and its Maude helpers:
RSS on Linux, physical footprint on macOS. For example, `--memory-limit=4GiB`.
The job stops when sampled usage
exceeds the threshold. Usage can overshoot between samples; unfinished
proofs are lost. See [memory-limit behavior and limitations](docs/PERFORMANCE.md#memory-limits).

## Algebra backends

`--algebra-backend=maude` (the default) answers unification, matching,
normalization and variant queries with a Maude subprocess.
`--algebra-backend=proved-only`, in a build with
`--features lean-unification`, answers them in-process from a Lean library
whose exports are proved correct, and starts no Maude. It works in batch mode,
in `interactive` mode and in `variants` mode:

```bash
cargo build --release --features lean-unification
tamarin-rs --algebra-backend=proved-only --prove theory.spthy
tamarin-rs interactive --algebra-backend=proved-only /path/to/theories
```

`--algebra-backend=native`, in the same build, also starts no Maude. Every
query that the Maude backend hands to Maude is answered by proved code, and
every other query is answered exactly as on the Maude backend, by its Rust
front ends. It prints the same proofs as proved-only and is faster than
proved-only on theories with many unification queries.

Tamarin requires a theory's equations to be convergent and has always taken
the author's word for it. The native backend checks instead: a proved
certifier examines the theory's rewrite table. It accepts the tables of the
built-in theories; a table with user equations it may or may not accept.
Results over an accepted table rest on no assumption about the equations.
When it does not accept the table, the run goes ahead on the author's word,
as every Maude run does, and says so once per theory on stderr:

```
[Theory T] note: the equational theory's convergence was not certified by the proved checker; results assume the user-specified equations are convergent, as Maude-based Tamarin also assumes
```

The line never appears on the Maude backend, which has no certifier, and
`--quiet` drops it. Standard output is the same with and without it.
Parallel proof search (`--processors`) runs on both backends and prints the
same proofs for every worker count; a proved-only run shares one in-process
session among its workers instead of a pool of Maude processes (see
[parallel proof search](docs/PERFORMANCE.md#parallel-proof-search)).
[TESTING.md](TESTING.md#algebra-backends) describes the tests and the
regression gate that compares the two backends.

## Checking proofs

With the Haskell `tamarin-prover` installed, this helper proves a theory with
Rust and rechecks the result with Haskell:

```bash
./prove_and_reverify.sh theory.spthy > proof.spthy
```

Some theories need a patched Haskell build for proof replay; see
[compatibility notes](docs/STATUS.md#proof-reverification).

## Status and performance

- **Compatibility:** byte-identical batch output on a 432-file parity corpus,
  with stored-proof replay checked in both directions. See
  [coverage and remaining differences](docs/STATUS.md).
- **Performance:** The eight-theory x86_64 Linux benchmark measured a
  6.1–141× speedup over Tamarin 1.12.0 (median 35×) at 1, 4, and 16 cores. On one core,
  Rust used 58–96% less peak memory, with a median reduction of 93%. See
  [results and methodology](docs/PERFORMANCE.md).
- **Development:** `make check` runs formatting and Clippy; `make test` runs
  the Rust tests. See [TESTING.md](TESTING.md) for parity and browser tests,
  and the [script reference](scripts/README.md) for individual tools.

## License

All contributions are considered MIT-licensed by default. However, code derived
from Tamarin is GPL 3.0 and the upstream submodule and patches
are also GPL 3.0. As such, **the built binary is GPL 3.0.** See the
[licensing notes](docs/LICENSING.md) for details.
