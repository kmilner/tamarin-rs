# Wellformedness fixture corpus

Each `.spthy` file in this directory is a minimal theory designed to
trigger exactly one of Tamarin's wellformedness check categories. The
companion `expected.txt` lists, for each fixture, the topic string(s)
`tamarin-prover` emits when loading the theory (the underlined
`WARNING:` topic headers).

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
   `--no-tamarin` is passed) a `tamarin-prover` binary found on `PATH`
   must emit them too, confirming the fixtures still shoot at the
   right targets.

Both harnesses share two comparison rules:

- Topics compare modulo trailing whitespace — some Haskell titles carry
  a source-literal trailing space (e.g. `"Facts occur in the
  left-hand-side but not in any right-hand-side "`), which the
  comma-separated `expected.txt` cannot represent.
- `Formula terms` is checked only against the tamarin binary, not the
  Rust parser-level checker: the HS `checkTerms` pass needs the
  elaborated `MaudeSig` for reducible-funsym classification, so its
  port lives in `tamarin_theory::check_terms` and runs post-elaboration
  (wired in `tamarin-prover`'s `run.rs`), covered by its own unit tests
  and the corpus parity gates.

## Categories covered

The definitive topic strings live in the submodule at
`tamarin-prover/lib/theory/src/Theory/Tools/Wellformedness.hs` (grep
`underlineTopic`, plus the LHS-usage `topic` literal). Note the source
carries quirks verbatim — both the `Inexistant`/`Inexistent` spellings
and a leading-space `" Formula guardedness"` variant exist:

- Check presence of the --prove/--lemma arguments in theory
- Reserved names
- Reserved prefixes
- Special facts
- Fr facts must only use a fresh- or a msg-variable
- Fact capitalization issues
- Fact arity issues
- Fact multiplicity issues
- Fact usage
- Facts occur in the left-hand-side but not in any right-hand-side
- Fresh public constants
- Public constants with mismatching capitalization
- Variable with mismatching sorts or capitalization
- Quantifier sorts
- Unbound variables
- Multiplication restriction of rules
- Variants / Rule has no variants
- Lemma annotations
- Inexistant lemma actions
- Inexistent restriction actions
- Restriction actions
- Formula guardedness
- Formula terms
- Nat Sorts
- Subterm Convergence Warning
- Left rule / Right rule (diff theories)

Each fixture is named after the category it targets.
