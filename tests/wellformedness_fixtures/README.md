# Wellformedness fixture corpus

Each `.spthy` file in this directory is a minimal theory designed to
target one of Tamarin's wellformedness check categories (a few
unavoidably trip a second check as collateral). The
companion `expected.txt` lists, for each fixture, the topic string(s)
`tamarin-prover` must emit when loading the theory — the `=`-underlined
headers inside its `WARNING: the following wellformedness checks
failed!` block. Both harnesses treat that list as a subset check, so a
fixture may legitimately emit more.

This corpus exists because the upstream `tamarin-prover/examples/` tree
contains hand-written, *passing* protocols — it does not exercise the
negative paths in `Theory.Tools.Wellformedness`. Two harnesses consume
it:

1. `cargo test -p tamarin-parser --test wellformedness` — offline
   check that the Rust port (`tamarin_parser::wf::check_theory`) emits
   every expected topic for every fixture. Runs in the normal test
   suite; no tamarin binary needed.
2. `cargo run -p tamarin-parser --example wellformedness_fixtures
   [-- <fixtures-dir>]` — the differential runner: every fixture must
   parse, the Rust checker must emit the expected topics, and (unless
   `--no-tamarin` is passed) a `tamarin-prover` binary must emit them
   too, confirming the fixtures still shoot at the right targets. The
   oracle binary is `$TAMARIN`, defaulting to `tamarin-prover` on
   `PATH`.

Both harnesses share two comparison rules:

- Topics compare modulo trailing whitespace — some Haskell titles carry
  a source-literal trailing space (e.g. `"Facts occur in the
  left-hand-side but not in any right-hand-side "`), which the
  comma-separated `expected.txt` cannot represent.
- `Formula terms` and `Multiplication restriction of rules` are checked
  only against the tamarin binary, not the Rust parser-level checker.
  The HS `checkTerms` and `multRestrictedReport` passes both need the
  elaborated `MaudeSig` (reducible-funsym classification, and
  `abstractRule`'s irreducible symbols), so their ports live in
  `tamarin_theory::check_terms` and `tamarin_theory::mult_restricted`
  and run post-elaboration — spliced by
  `tamarin_theory::translated_wf`, which both the CLI (`run.rs`) and
  the web loader call. Each is covered by its own unit tests and by the
  corpus parity gates.

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
- Formula guardedness *(unpinned — `formula_unguarded` is pinned on
  `Formula terms`)*
- Formula terms
- Nat Sorts
- Subterm Convergence Warning
- Left rule / Right rule (diff theories)

Each fixture is named after the category it targets.
