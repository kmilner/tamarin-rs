# Wellformedness fixture corpus

Each `.spthy` file in this directory is a minimal theory designed to
trigger exactly one of Tamarin's wellformedness check categories. The
companion `expected.txt` lists, for each fixture, the topic string(s)
the official `tamarin-prover --parse-only` is expected to emit.

This corpus exists because the upstream `examples/` tree contains
hand-written, *passing* protocols — it does not exercise the negative
paths in `Theory.Tools.Wellformedness`. We use these fixtures to drive
both:

1. The Rust port of `checkWellformedness` once it lands.
2. Differential testing against `tamarin-prover` so that as we port each
   check, we can confirm it fires on the same fixtures Haskell does.

## Categories covered

The list of wellformedness topics emitted by Tamarin
(grep `underlineTopic` in `lib/theory/src/Theory/Tools/Wellformedness.hs`):

- Reserved names
- Reserved prefixes
- Special facts
- Fr facts must only use a fresh- or a msg-variable
- Fact capitalization issues
- Fact arity issues
- Fact multiplicity issues
- Fact usage
- Fresh public constants
- Public constants with mismatching capitalization
- Variable with mismatching sorts or capitalization
- Quantifier sorts
- Unbound variables
- Multiplication restriction of rules
- Variants / Rule has no variants
- Lemma annotations
- Inexistent lemma actions
- Inexistent restriction actions
- Restriction actions
- Formula guardedness
- Formula terms
- Nat Sorts
- Subterm Convergence Warning
- Left rule / Right rule (diff theories)
- Facts occur in left-hand-side but not in any right-hand-side

Each fixture is named after the category it targets.

## Running the fixtures

```
cargo run -p tamarin-parser --example wellformedness_check
```

(The runner is added once the wellformedness pass is ported.)
