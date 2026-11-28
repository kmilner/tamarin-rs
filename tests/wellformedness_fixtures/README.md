# Wellformedness fixture corpus

Each `.spthy` file in this directory is a minimal theory designed to
target one of Tamarin's wellformedness check categories (a few
unavoidably trip a second check as collateral). The
companion `expected.txt` lists, for each fixture, the topic string(s)
`tamarin-prover` must emit when loading the theory — the `=`-underlined
headers inside its `WARNING: the following wellformedness checks
failed!` block. The differential runner treats that list as a subset of
the topics a fixture emits. A fixture can therefore emit more topics
than its line lists. The `reports/` directory holds the bytes of the
whole block for every fixture.

This corpus provides focused topic and byte-level coverage of
`Theory.Tools.Wellformedness`. Two harnesses consume it:

1. `cargo run -p tamarin-theory --example wellformedness_fixtures
   [-- <fixtures-dir>]` — the differential runner: every fixture must
   parse, the Rust checker must emit the expected topics and none of
   the fixture's `#!` negatives, and (unless `--no-tamarin` is passed)
   a `tamarin-prover` binary must emit them too, confirming the
   fixtures still shoot at the right targets. The oracle binary is
   `$TAMARIN`, defaulting to `tamarin-prover` on `PATH`.
2. `cargo test -p tamarin-theory --test wellformedness_fixture_reports`
   — the byte-level pin. This harness runs each fixture through
   `tamarin_theory::wellformedness::check_wellformedness`, the pass both
   production callers run. The rendered `/* WARNING … */` block must then
   equal `reports/<fixture>.report` byte for byte. Those `.report`
   files are captures of the pinned oracle's own block. This harness
   therefore holds the fixtures' *text* to upstream, and not only their
   topic names. It runs offline, and it needs no Maude. It also fails
   in these cases. The first is a fixture with no `.report` file. The
   second is a `.report` file for a fixture that does not exist. The
   third is a `.report` file whose `# source:` provenance line does not
   name the oracle. The last is an `expected.txt` roster that does not
   match the fixture directory: a `.spthy` file no line mentions, a
   line naming a file that does not exist, a `#!` line for a fixture no
   positive line lists, or a line that lists no topics. That roster is
   what harness 1 iterates, so this test keeps it honest inside the
   normal test suite.

The runner compares topic names after trimming trailing whitespace. Both Rust
and Haskell must satisfy every listed positive and negative expectation.
The Rust check uses the static wellformedness pass. The shared production
loader also checks rule variants and message derivability with Maude.

## `reports/`

This directory holds one `<fixture>.report` file per pinned fixture.
Each file starts with `#` provenance lines, and the expected block
follows them. Every file carries a
`# source:` line naming the oracle and capture flags. Captures disable
`Message Derivation Checks` with `--derivcheck-timeout=0`, matching the static
wellformedness pipeline tested here. Production callers run that dynamic check
separately with Maude.

Every fixture carries a `.report` file, so harness 2 pins the whole
block of every one of them.

The fixtures cover trace theories. The parser library can read diff theories,
but the CLI rejects `--diff` and the diff-theory wellformedness pass is unported.

To re-capture a report after a submodule bump, follow these steps.
Load the fixture through the pinned `tamarin-prover` build. You do not
need `--prove`, because the wellformedness checks print at load. Use `--derivcheck-timeout=0`, copy the `/* WARNING … */` block, and record
the oracle revision and flags in the `# source:` header.
For fatal findings such as unsupported products, use `-m=msr` to print
the report without attempting to prove the invalid theory. The multiplication
fixture also uses `--derivcheck-timeout=0`, so its capture needs no dynamic
section removed.

## Check categories

[`expected.txt`](expected.txt) lists the positive and negative topics checked
for each model. The matching file under [`reports/`](reports/) gives the full
diagnostic, including any additional topics that the model triggers. The
upstream pass defines the category titles in
[Wellformedness.hs](../../tamarin-prover/lib/theory/src/Theory/Tools/Wellformedness.hs). For example,
`quantifier_wrong_sort` requires the `Formula terms` topic, and its full
[report](reports/quantifier_wrong_sort.report) also checks `Formula guardedness`.
