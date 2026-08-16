# Wellformedness fixture corpus

Each `.spthy` file in this directory is a minimal theory designed to
target one of Tamarin's wellformedness check categories (a few
unavoidably trip a second check as collateral). The
companion `expected.txt` lists, for each fixture, the topic string(s)
`tamarin-prover` must emit when loading the theory — the `=`-underlined
headers inside its `WARNING: the following wellformedness checks
failed!` block. The two topic-level harnesses treat that list as a
subset check, so a fixture may legitimately emit more. `reports/`
holds, for most fixtures, the whole block's bytes.

This corpus exists because the upstream `tamarin-prover/examples/` tree
contains hand-written, *passing* protocols — it does not exercise the
negative paths in `Theory.Tools.Wellformedness`. Three harnesses consume
it:

1. `cargo test -p tamarin-parser --test wellformedness` — offline
   check that the Rust port (`tamarin_parser::wf::check_theory`) emits
   every expected topic for every fixture and none of its `#!`
   negatives. Runs in the normal test suite; no tamarin binary needed.
   It also fails on a `.spthy` no `expected.txt` line mentions, a `#!`
   line for an unlisted fixture, and a fixture left comparing nothing
   once the post-elaboration topics below are dropped.
2. `cargo run -p tamarin-parser --example wellformedness_fixtures
   [-- <fixtures-dir>]` — the differential runner: every fixture must
   parse, the Rust checker must emit the expected topics, and (unless
   `--no-tamarin` is passed) a `tamarin-prover` binary must emit them
   too, confirming the fixtures still shoot at the right targets. The
   oracle binary is `$TAMARIN`, defaulting to `tamarin-prover` on
   `PATH`.
3. `cargo test -p tamarin-theory --test wellformedness_fixture_reports`
   — the byte-level pin: each fixture is run through the four
   `tamarin_theory::translated_wf` entry points, in the order both
   production drivers call them, and the rendered `/* WARNING … */`
   block must equal `reports/<fixture>.report` verbatim. Those files
   are captures of the pinned oracle's own block, so this is where the
   fixtures' *text* — not just their topic names — is held to upstream.
   Runs offline, needs no Maude. It also fails on a fixture with
   neither a `.report` file nor a `NO_REPORT_EXPECTATION` entry, a
   `.report` for a fixture that no longer exists, and a `.report` whose
   `# source:` provenance line does not name the oracle.

The two topic-level harnesses share two comparison rules:

- Topics compare modulo trailing whitespace — some Haskell titles carry
  a source-literal trailing space (e.g. `"Facts occur in the
  left-hand-side but not in any right-hand-side "`), which the
  comma-separated `expected.txt` cannot represent.
- `Formula terms` and `Multiplication restriction of rules` are checked
  only against the tamarin binary, not the Rust parser-level checker,
  so a fixture pinning nothing else rests on its `#!` negatives there
  and on its `reports/` block in harness 3.
  The HS `checkTerms` and `multRestrictedReport` passes both need the
  elaborated `MaudeSig` (reducible-funsym classification, and
  `abstractRule`'s irreducible symbols), so their ports live in
  `tamarin_theory::check_terms` and `tamarin_theory::mult_restricted`
  and run post-elaboration — spliced by
  `tamarin_theory::translated_wf`, which both the CLI (`run.rs`) and
  the web loader call. Each is covered by its own unit tests and by the
  corpus parity gates.

## `reports/`

One `<fixture>.report` per pinned fixture: leading `#` provenance
lines, then the expected block. Two provenance keys are in use —
`# source:`, which every file carries and which must name the oracle,
and `# omits:`, which four files carry because the oracle's block ends
with a `Message Derivation Checks` section that harness 3's pipeline
does not produce (it is the dynamic, Maude-backed check the drivers
splice afterwards; `expected.txt` documents the same asymmetry for the
topic-level harnesses).

The three `diff_*` fixtures have no `.report` and are listed in the
harness's `NO_REPORT_EXPECTATION` with their reason: the port's
`Left rule` / `Right rule` / `Reserved prefixes` bodies are documented
best-effort divergences (see `wf::left_right_rule_report` and
`wf::reserved_prefix_report`), so pinning them here would fix a
divergence in place rather than pin upstream. They keep a
parser-reachable topic in `expected.txt`, so harness 1 still compares
something for them.

To re-capture after a submodule bump: load the fixture through the
pinned `tamarin-prover` build (no `--prove` needed — wellformedness
prints at load), copy the `/* WARNING … */` block, drop any trailing
`Message Derivation Checks` section, and keep the `#` header.

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
- Formula guardedness *(no fixture of its own; `quantifier_wrong_sort`
  trips it as collateral, so only its `reports/` block pins it —
  `expected.txt`, which the parser-only harness also reads, cannot)*
- Formula terms
- Nat Sorts
- Subterm Convergence Warning
- Left rule / Right rule (diff theories)

Each fixture is named after the category it targets.
