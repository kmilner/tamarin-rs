# Solver branch state

The Haskell solver stacks its effects as:

```haskell
StateT System (FreshT (DisjT (Reader ProofContext)))
```

The order matters. A disjunction copies both the current `System` and the
current fresh-variable counter. Each arm then advances its own counter. A
continuation after the split must run once per arm, in arm order; a later
split forms a cross-product. Contradictory arms disappear without affecting
their siblings. Execution errors are separate from contradictions: a Maude
failure must propagate as `Err`, never as an empty case list or a contradictory
store. This also applies during equation simplification and source caching.

Rust represents those effects explicitly. A branch therefore carries its
system and its counter together. Code continuing a branch must use
`Reduction::new_inheriting`, not reconstruct the counter from
`bounds_max(system)`: temporary allocations made before the split may not be
present in the system, so recomputing the bound can rewind the counter.

Every split result (`SystemOutcome`, `GoalCases`, and the simplify/source
APIs) holds complete systems and counters, so the caller continues directly
from each branch. `continue_in_arms` runs the rest of an operation in every
branch and collects the completed ones.

When adding a split point, keep the operation that consumes its result close
to it. Do not install arm zero and silently leave sibling state elsewhere;
return all branches or immediately drive all of them through the same
continuation. Tests should cover nested splits, unequal per-arm fresh draws,
arm ordering, and contradictory nonzero arms.
