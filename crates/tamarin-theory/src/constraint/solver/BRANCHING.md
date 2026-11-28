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

A Rust `Reduction` owns the current system and its fresh-variable supply.
`Reduction::fork` copies both. A split returns each surviving system with
its next fresh index. `continue_in_arms` resumes those branches in order through
`Reduction::new_inheriting`. The inherited index matters because a branch may
already have allocated a temporary variable that never appeared in its system.

A linear result continues on the current reduction. A contradictory result
has no continuation. Code that receives several branches must return them or
apply its continuation to each one.
