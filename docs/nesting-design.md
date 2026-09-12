# Nesting design and scope

The practical acceptance case is an 8,192-level function application surviving
CLI parsing, translation, printing, reparsing and cleanup. It is a regression
target, not a depth cap or a guarantee of feasible arbitrary proof search at that
depth. See [TESTING.md](../TESTING.md#practical-nesting-target).

Term trees already lived on the heap before this branch. The stack risk comes
from recursive calls while parsing, traversing and releasing them; making those
continuations iterative is a separate decision from where the tree is stored.

Term depth, formula depth, process depth and proof-tree depth are separate axes.
A shallow formula or proof step can contain a very deep term. Changes to a
formula/process module therefore cannot be classified solely by the filename.

The ordinary rule-term path is `Parser::iterative_term`, then elaboration's
`term_to_lnterm` / `term_to_vterm`, internal term operations, and `pretty_term`
(document output) or `pretty_lnterm` (flat output), followed by AST and internal
term cleanup. `term_to_vterm` already uses guarded recursion: the design is
already a mixture of techniques. SAPIC shares conversion through
`term_to_sapic_term` and additionally traverses terms in `typing::type_with`.
Those term paths must survive reductions to surrounding formula/process walks.

## Decisions

| Area | Relation to the requirement | Decision |
| --- | --- | --- |
| Iterative term grammar and AST term walking/cleanup | Direct: delimiters, argument lists, failed parses and returned ASTs | Keep. Parsing plus AST destruction is approximately level on the measured ordinary corpus and faster on nested unary terms. |
| Internal term conversion, substitution, comparison and printing | Deep terms leave the parser and pass through these operations | Keep the shared traversals. Do not rewrite additional recursive helpers merely to make them iterative. |
| Internal term argument ownership | Last-owner destruction can happen during translation, proof search, errors, or on another thread | Keep provisionally. A sized shared owner permits iterative destruction even with racing final releases; a phase-local large stack cannot protect every later release. |
| Document construction, layout and destruction | Deep terms can produce deep documents despite shallow surrounding theory structure | Retain pending a measured smaller alternative. This machinery is part of the term output lifecycle, although its guarantees exceed that single case. |
| Formula/guarded-formula structure | Formula nesting is independent; atom payloads still contain deep terms | Separate structural ownership/traversal changes from atom-term operations before reducing them. Whole-file reverts are inappropriate. |
| SAPIC term typing and conversion | A shallow process action can contain a deep function term | Keep term-depth protection. |
| SAPIC process walks and ownership | Deep process structure is independent | Retain shared walks that reduce duplication or avoid repeated scope copying. Bespoke structural state machines remain candidates for separate simplification. |
| Proof search expansion and frontier re-expansion | Search depth is independent of function-term depth | Use guarded recursion in place of explicit parent machines. Preserve cuts, ordering, system retention, trace scopes, error behavior and existing deep-search tests. |
| Proof-tree ownership, status, printing and replay | Independent structural protection | Keep compact ownership/shared traversals. Replay uses guarded recursion with lexical trace scopes, preserving stored-case order and status contributions from every visit, including overwritten duplicate cases. |
| Large-stack entry points | Accommodate remaining recursive helpers and temporary values | Keep as a practical fallback, not as proof that arbitrary callers and returned values are protected. |

## Why storage affects proof performance

The old term arguments were an `Arc<[Term]>`. The current representation uses
an `Arc` owner containing a boxed slice, introducing another allocation and
indirection while reducing the measured term size from 48 to 40 bytes on the
benchmark target. Comparison, substitution and temporary destruction use this
representation throughout search. Iterative parsing alone does not impose that
cost. The measured full README comparison was about 4% slower overall with
approximately level memory; that result covers the broader branch, not an
isolated causal contribution from each change.

An earlier experiment retaining an Arc slice and guarding every release was
slower and used more memory. It does not rule out all coarse execution-boundary
alternatives. Conversely, a larger worker stack alone is not an equivalent
replacement for safe destruction of returned, shared terms.

## Limits and acceptance of simplifications

Guarded recursion uses the existing `ensure_sufficient_stack` helper. Its stack
switching depends on `stacker`/`psm` target support; unsupported targets execute
in place. It does not promise constant native-stack use or bounded total memory.
Keep this distinction explicit in test descriptions.

For each structural simplification, preserve the existing semantic tests and
exercise deep inputs, errors and cleanup. Measure representative whole proofs
before retaining a change in search paths. Do not infer an end-to-end win from
removed lines or a microbenchmark. Full proof/web parity remains necessary
before calling a changed solver implementation ready to merge.

An arena or term-ID representation could remove recursive ownership more
fundamentally, but would be a much larger change. It is not justified by the
current practical requirement. No new nesting limit or blanket guarantee that
all recursive operations are safe is introduced by this scope decision.
