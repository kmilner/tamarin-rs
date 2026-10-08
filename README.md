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
You will also need Maude to run the prover and Graphviz for server-rendered graphs,
see the [Tamarin manual installation instructions](https://tamarin-prover.com/manual/master/book/002_installation.html).


```bash
make install
tamarin-rs --prove theory.spthy
tamarin-rs interactive /path/to/theories
```

`make install` installs a release build to `~/.local/bin/tamarin-rs` by default, you may
have to add it to your PATH if it is not already (or just use the full path directly).

See the [build and development guide](docs/DEVELOPMENT.md) for custom install
paths, frontend development, and the Haskell test build.

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
- **Performance:** 4.6–116× faster than Tamarin 1.12.0 (median 23×) across the
  recorded eight-theory benchmark at 1–16 cores; 2.1–21× lower peak memory at
  one core. See [results and methodology](docs/PERFORMANCE.md).
- **Development:** `make check` runs formatting and Clippy; `make test` runs
  the Rust tests. See [TESTING.md](TESTING.md) for parity and browser tests,
  and the [script reference](scripts/README.md) for individual tools.

## License

All contributions are considered MIT-licensed by default. However, code derived
from Tamarin is GPL 3.0 and the upstream submodule and patches
are also GPL 3.0. As such, **the built binary is GPL 3.0.** See the
[licensing notes](docs/LICENSING.md) for details.
