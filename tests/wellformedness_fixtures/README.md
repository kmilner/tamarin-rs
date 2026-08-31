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

This corpus exists because the upstream `tamarin-prover/examples/` tree
contains hand-written, *passing* protocols — it does not exercise the
negative paths in `Theory.Tools.Wellformedness`. Two harnesses consume
it:

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

The runner's topic comparison has two rules:

- Topics compare modulo trailing whitespace — some Haskell titles carry
  a source-literal trailing space (e.g. `"Facts occur in the
  left-hand-side but not in any right-hand-side "`), which the
  comma-separated `expected.txt` cannot represent.
- The `Rule has no variants` and `Message Derivation Checks` topics are
  checked only against the tamarin binary. Both need a live Maude
  process that the runner does not spawn: the batch driver (`run.rs`)
  splices them into the pass's result afterwards. Each is covered by
  its own unit tests and by the corpus parity gates.

## `reports/`

This directory holds one `<fixture>.report` file per pinned fixture.
Each file starts with `#` provenance lines, and the expected block
follows them. The files use two provenance keys. Every file carries a
`# source:` line, and that line must name the oracle. Four files also
carry an `# omits:` line. Those four files need it because the
oracle's block ends with a `Message Derivation Checks` section.
Harness 2's pipeline does not produce that section. The production callers splice
that section in afterwards. It is a dynamic check, and it needs Maude.
`expected.txt` records the same difference for the differential runner.

Every fixture carries a `.report` file, so harness 2 pins the whole
block of every one of them.

The `Left rule`, `Right rule` and `Reserved prefixes` topics of HS
`checkWellformednessDiff` (Wellformedness.hs:1247-1264) have no fixture
here, because the port does not implement that pass: `run_batch`
refuses `--diff` (`crates/tamarin-prover/src/run.rs:2008-2012`),
`parse_theory` pins the parser AST's `is_diff` to `false`
(`crates/tamarin-parser/src/parser.rs:370-371`), and the internal
`theory::Theory` carries no `is_diff` at all. A `--diff` port adds
`diff_left_right_mismatch`, `diff_reserved_prefix` and
`diff_right_rule_mismatch` here, built from `theory::DiffTheory`, each
with an oracle-captured `.report` block.

To re-capture a report after a submodule bump, follow these steps.
Load the fixture through the pinned `tamarin-prover` build. You do not
need `--prove`, because the wellformedness checks print at load. Copy
the `/* WARNING … */` block. Drop any trailing
`Message Derivation Checks` section. Keep the `#` header.

## Check categories

The definitive topic strings live in the submodule at
`tamarin-prover/lib/theory/src/Theory/Tools/Wellformedness.hs` (grep
`underlineTopic`, plus the LHS-usage `topic` literal). Note the source
carries quirks verbatim — the diff-theory checks spell two of them
`Inexistant lemma actions` and `Restriction actions` where the
plain-theory ones say `Inexistent …`, and the non-diff guardedness
topic has a leading space, `" Formula guardedness"`. Categories no
fixture pins yet are marked *(unpinned)*:

- Check presence of the --prove/--lemma arguments in theory *(unpinned)*
- Reserved names
- Reserved prefixes *(unported — `checkWellformednessDiff`)*
- Special facts
- Fr facts must only use a fresh- or a msg-variable
- Fact capitalization issues *(unpinned)*
- Fact arity issues
- Fact multiplicity issues
- Fact usage *(unpinned)*
- Facts occur in the left-hand-side but not in any right-hand-side
- Fresh public constants
- Public constants with mismatching capitalization
- Variable with mismatching sorts or capitalization
- Quantifier sorts *(unpinned — `quantifier_wrong_sort` is pinned on
  `Formula terms`)*
- Unbound variables
- Multiplication restriction of rules
- Variants / Rule has no variants *(unpinned)*
- Lemma annotations
- Inexistent lemma actions *(unpinned)*
- Inexistent restriction actions *(unpinned)*
- Inexistant lemma actions / Restriction actions, diff theories *(unpinned)*
- Formula guardedness *(no fixture of its own. `quantifier_wrong_sort`
  also trips this check, and its `reports/` block pins it)*
- Formula terms
- Nat Sorts
- Subterm Convergence Warning
- Left rule / Right rule *(unported — `checkWellformednessDiff`)*

Each fixture is named after the category it targets.
