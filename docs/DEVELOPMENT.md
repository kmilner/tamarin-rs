# Build and development guide

[Back to README](../README.md)

Commands below run from the repository root.

## Building

Building requires Rust, Node.js (22.12+ or 24+), npm, Git, and Bash. The default
installation workflow also uses Make.
Maude is needed to run the prover. Graphviz (`dot`, or `--with-dot=/path/to/dot`)
is needed for server-rendered SVG graphs; interactive graphs render in the browser.

`make` builds an optimized prover; `make install` also installs it:

```bash
make install                          # release build (including GUI), then install
~/.local/bin/tamarin-rs interactive /path/to/theories
```

This lets Cargo initialize missing sources and compile the frontend, then
installs only `~/.local/bin/tamarin-rs`. All GUI assets are embedded in the
binary, so it works from any directory and can be copied without the checkout,
Node.js, npm, or asset files. Maude and Graphviz remain external tools.
Add `~/.local/bin` to your `PATH` to invoke `tamarin-rs` by name.

Use `make install PREFIX=/custom/prefix` to change the installation directory.
`make` (or `make build`) builds without installing; `make debug` builds an
unoptimized binary in `target/debug/`. `make check` runs formatting and
Clippy; `make test` runs the Rust suite with the optimized `ci` profile.
`CARGO_TARGET_DIR=/path/to/build` selects the output directory for Make's Cargo
commands and its standalone frontend target.
Installation uses the executable path reported by Cargo, including when a build
target is selected through `CARGO_BUILD_TARGET` or Cargo's `build.target` setting.

To build without Make or installation:

```bash
cargo build --release                 # builds and embeds GUI → target/release/tamarin-rs
```

Cargo initializes the `tamarin-prover` submodule if it is missing, compiles the
frontend with npm, and embeds its output automatically. Existing submodule
checkouts are left untouched. The first build needs network access to fetch
missing sources and npm packages. It rebuilds the GUI when its sources,
configuration, or dependency lockfile change; an unchanged build reuses the
existing output. Generated files live
inside Cargo's build output directory, including when `CARGO_TARGET_DIR` is
set, leaving the submodule pristine. No separate GUI build is needed after
`cargo clean`. The release profile uses `lto = "fat"` and `codegen-units = 1`.

The submodule supplies the embedded GUI and intruder variants at build time,
and the example corpus at test time. `scripts/bump_submodule.sh`
automates updating its pin, checking patches, and rebuilding the oracle;
`--check` changes nothing.

## Frontend development

`make frontend` or `./setup.sh gui` builds a standalone frontend in
`target/gui/frontend/dist` for development. The Make target honors
`CARGO_TARGET_DIR`. These commands are optional: Cargo builds its own embedded
copy in its output directory. `make setup` explicitly initializes or updates
the submodule to the repository's pinned revision.

`--data-dir=/path/to/data` explicitly replaces the embedded assets for frontend
development. This directory must contain a complete GUI, with graph modules
either in `data/js` and `data/css` or a sibling `frontend/dist` directory.
An incomplete override is reported at startup. Normal use requires no
`--data-dir` option.

## Haskell oracle

Building the Haskell oracle is needed only for the parity gates, not for the
Rust build itself:

```
./setup.sh testing                   # patched oracle → tamarin-prover-testing/
```

This materialises a git worktree of the pinned commit at
`tamarin-prover-testing/`, applies the files in `patches/series` there (the
submodule itself stays untouched), and builds it with stack. When needed, the
testing worktree is reset to the current branch's pin; ignored `.stack-work/`
artifacts remain as the compiler cache. The parity scripts discover that
binary automatically; `HS_PATH=<binary>` overrides, and byte-identical copies
are verified against setup's fixed `.stack-work/` attestation.

## Repository layout

```
crates/            the Rust port (crate breakdown below)
scripts/           GUI build and browser tests, parity gates, benchmarks, and triage
tests/             wellformedness fixture corpus
patches/
  series                       ordered list of one Haskell patch per
                               not-yet-merged upstream PR
  tamarin-prover-pr-*.patch    patches applied to the testing oracle
tamarin-prover/    upstream submodule, pinned to a known-good commit and kept
                   PRISTINE — holds the canonical Haskell sources, the
                   examples/ corpus, and the web data/ assets
tamarin-prover-testing/   (untracked; created by ./setup.sh testing) patched
                   copy of the prover, built as the byte-parity oracle
target/            Rust build output (release binary under target/release/)
                   Cargo also builds and embeds the frontend under its build/ output
```

## Crate layout

The workspace crates under `crates/` (`tamarin-prover/` here is the binary
crate, distinct from the `tamarin-prover/` submodule at the repository root):

```
tamarin-build/          shared build-time initialization of the upstream submodule
tamarin-utils/          fresh-name state, pretty-printer, DAG/dot helpers, small util types
tamarin-term/           Term/LTerm/LNTerm, MaudeSig, Maude IPC, normalisation
tamarin-parser/         .spthy AST + lexer + parser + #include resolver
tamarin-theory/         elaborator, wellformedness, constraint system, solver, simplify, sources, replay
tamarin-sapic/          SAPiC process: frontend — translation to multiset-rewrite rules
tamarin-accountability/ accountability frontend — case tests → VC lemmas
tamarin-test-support/   maude resolution shared by every crate's maude-gated tests
tamarin-server/         interactive HTTP server (Axum)
tamarin-prover/         the binary: CLI parser + run dispatch
```

## Testing

`make check` runs formatting and workspace Clippy. `make test` runs the Rust
suites, including the server's asset and graph route tests. CI also runs a
Chromium test that copies only the binary to a temporary installation and
checks page loading and graph rendering from an unrelated working directory.

Parity against the Haskell prover is checked by `scripts/corpus_file_diff.sh`
for batch mode and `scripts/web_parity.sh` for the interactive UI. See
[TESTING.md](../TESTING.md) for the full verification ladder, the gate
environment reference, and the divergence-debugging toolbox.
