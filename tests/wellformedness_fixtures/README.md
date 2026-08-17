# Wellformedness fixture corpus

Each `.spthy` file in this directory is a minimal theory designed to
target one of Tamarin's wellformedness check categories (a few
unavoidably trip a second check as collateral). The
companion `expected.txt` lists, for each fixture, the topic string(s)
`tamarin-prover` must emit when loading the theory — the `=`-underlined
headers inside its `WARNING: the following wellformedness checks
failed!` block. The two topic-level harnesses treat that list as a
subset of the topics a fixture emits. A fixture can therefore emit
more topics than its line lists. The `reports/` directory holds the
bytes of the whole block for most fixtures.

This corpus exists because the upstream `tamarin-prover/examples/` tree
contains hand-written, *passing* protocols — it does not exercise the
negative paths in `Theory.Tools.Wellformedness`. Three harnesses consume
it:

1. `cargo test -p tamarin-parser --test wellformedness` — offline
   check that the Rust port (`tamarin_parser::wf::check_theory`) emits
   every expected topic for every fixture and none of its `#!`
   negatives. This check runs in the normal test suite, and it needs
   no tamarin binary. It also fails in three more cases. The first is
   a `.spthy` file that no `expected.txt` line mentions. The second is
   a `#!` line for a fixture that no `expected.txt` line lists. The
   third is a fixture that compares nothing after the harness drops
   the post-elaboration topics below.
2. `cargo run -p tamarin-parser --example wellformedness_fixtures
   [-- <fixtures-dir>]` — the differential runner: every fixture must
   parse, the Rust checker must emit the expected topics, and (unless
   `--no-tamarin` is passed) a `tamarin-prover` binary must emit them
   too, confirming the fixtures still shoot at the right targets. The
   oracle binary is `$TAMARIN`, defaulting to `tamarin-prover` on
   `PATH`.
3. `cargo test -p tamarin-theory --test wellformedness_fixture_reports`
   — the byte-level pin. This harness runs each fixture through three
   of the four `tamarin_theory::translated_wf` entry points, in the
   order that both production drivers call them. It does not call
   `prepend_wf_report`. The rendered `/* WARNING … */` block must then
   equal `reports/<fixture>.report` byte for byte. Those `.report`
   files are captures of the pinned oracle's own block. This harness
   therefore holds the fixtures' *text* to upstream, and not only their
   topic names. It runs offline, and it needs no Maude. It also fails
   in three more cases. The first is a fixture with neither a `.report`
   file nor a `NO_REPORT_EXPECTATION` entry. The second is a `.report`
   file for a fixture that no longer exists. The third is a `.report`
   file whose `# source:` provenance line does not name the oracle.

The two topic-level harnesses share two comparison rules:

- Topics compare modulo trailing whitespace — some Haskell titles carry
  a source-literal trailing space (e.g. `"Facts occur in the
  left-hand-side but not in any right-hand-side "`), which the
  comma-separated `expected.txt` cannot represent.
- `Formula terms` and `Multiplication restriction of rules` are checked
  only against the tamarin binary, and not against the Rust
  parser-level checker. A fixture that pins nothing else therefore
  depends on its `#!` negatives in the two topic-level harnesses. It
  also depends on its `reports/` block in harness 3.
  The HS `checkTerms` and `multRestrictedReport` passes both need the
  elaborated `MaudeSig` (reducible-funsym classification, and
  `abstractRule`'s irreducible symbols), so their ports live in
  `tamarin_theory::check_terms` and `tamarin_theory::mult_restricted`
  and run post-elaboration — spliced by
  `tamarin_theory::translated_wf`, which both the CLI (`run.rs`) and
  the web loader call. Each is covered by its own unit tests and by the
  corpus parity gates.

## `reports/`

This directory holds one `<fixture>.report` file per pinned fixture.
Each file starts with `#` provenance lines, and the expected block
follows them. The files use two provenance keys. Every file carries a
`# source:` line, and that line must name the oracle. Four files also
carry an `# omits:` line. Those four files need it because the
oracle's block ends with a `Message Derivation Checks` section.
Harness 3's pipeline does not produce that section. The drivers splice
that section in afterwards. It is a dynamic check, and it needs Maude.
`expected.txt` records the same difference for the topic-level
harnesses.

The three `diff_*` fixtures have no `.report` file. The harness lists
them in `NO_REPORT_EXPECTATION` with the reason. The reason is that
the port's `Left rule`, `Right rule` and `Reserved prefixes` bodies
are best-effort divergences from upstream. The code documents each of
them (see `wf::left_right_rule_report` and
`wf::reserved_prefix_report`). A pin here would hold a divergence in
place instead of holding the port to upstream. Each of the three
fixtures keeps a topic in `expected.txt` that the parser side reaches,
so harness 1 still compares something for them.

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
- Reserved prefixes
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
  also trips this check, so only its `reports/` block pins it.
  `expected.txt` cannot pin it, because the parser-only harness also
  reads that file)*
- Formula terms
- Nat Sorts
- Subterm Convergence Warning
- Left rule / Right rule (diff theories)

Each fixture is named after the category it targets.
