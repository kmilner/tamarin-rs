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
| Formula/include grammar | Nesting is independent of function-term depth | Use guarded recursion while retaining indexed group disambiguation, lazy error alternatives, shared include state and active-path cycle detection. |
| Formula/guarded-formula structure | Formula nesting is independent; atom payloads still contain deep terms | Separate structural ownership/traversal changes from atom-term operations before reducing them. Whole-file reverts are inappropriate. |
| SAPIC term typing and conversion | A shallow process action can contain a deep function term | Use guarded cached inference, retaining mutation invalidation and both inference passes. Shared term walks and conversions remain protected. |
| SAPIC process grammar | Process nesting is independent; action terms still use the iterative term parser | Guard recursive productions, keeping flat composition iterative. Retain the small-stack success and error-cleanup tests. |
| SAPIC process walks and ownership | Deep process structure is independent | Retain shared walks that reduce duplication or avoid repeated scope copying. State-channel declaration reuses the mutable walker, including its branch-scoped copy-on-write state. Scalar formula polarity uses guarded recursion. |
| Proof search expansion and frontier re-expansion | Search depth is independent of function-term depth | Use guarded recursion in place of explicit parent machines. Preserve cuts, ordering, system retention, trace scopes, error behavior and existing deep-search tests. |
| Proof-tree ownership, status, printing and replay | Independent structural protection | Keep compact ownership/shared traversals. Replay uses guarded recursion with lexical trace scopes, preserving stored-case order and status contributions from every visit, including overwritten duplicate cases. |
| Large-stack entry points | Accommodate remaining recursive helpers and temporary values | Keep where remaining recursion needs the fallback; the entirely iterative SAPIC pre-report path and independently protected theory typing path need no additional wrappers. These boundaries do not prove that arbitrary callers and returned values are protected. |

## Why storage affects proof performance

The old term arguments were an `Arc<[Term]>`. The current representation uses
an `Arc` owner containing a boxed slice, adding a live allocation and an
indirection while reducing the measured term size from 48 to 40 bytes on the
benchmark target. Comparison, substitution and temporary destruction use this
representation throughout search. Iterative parsing alone does not impose that
cost. The measured full README comparison was about 4% slower overall with
approximately level memory; that result covers the broader branch, not an
isolated causal contribution from each change.

An extra live allocation does not necessarily mean an extra allocation call.
For a nonempty, exact-capacity input vector, the parent allocates an Arc slice,
copies the vector into it, then frees the vector. The current owner retains the
vector's buffer and allocates its small Arc payload. Both constructions make
two allocation calls, including the input vector. A spare-capacity vector may
add a shrinking reallocation in the current `into_boxed_slice` conversion.

Measured requested live storage for an application with literal children
(`Term<u64>`, 64-bit host; excludes allocator metadata and size-class rounding):

| Arity | Parent live bytes | Current live bytes | Parent / current live blocks |
| --- | ---: | ---: | ---: |
| 0 | 16 | 32 | 1 / 1 |
| 1 | 64 | 72 | 1 / 2 |
| 2 | 112 | 112 | 1 / 2 |
| 8 | 400 | 352 | 1 / 2 |

Thus the smaller child representation offsets the owner header at arity two
and reduces requested storage for wider applications. Layout and allocator
traffic alone cannot establish the effect on whole-proof performance.

A later safe prototype used `Option<Arc<OwnedArgs>>` to represent empty argument
lists without allocating. It retained the 40-byte term layout and eliminated
one 32-byte allocation per nullary application. Microbenchmarks improved for
nullary construction but slightly regressed for deep nonempty trees. A paired
CI-profile screening of NSPK3, keyless SSL injectivity, DNP3 and NAXOS proofs
showed matching output and median elapsed-time changes within 0.4% in either
direction (six runs per binary and case). This is not evidence of a release
performance gain, so the prototype was not retained. The proof candidate also
included the early invalid-induction-guard rejection; the timings are a
screening result, not isolated attribution of the empty-owner representation.

An earlier experiment retaining an Arc slice and guarding every release was
slower and used more memory. It does not rule out all coarse execution-boundary
alternatives. Conversely, a larger worker stack alone is not an equivalent
replacement for safe destruction of returned, shared terms.

## Ordinary-workload priority

The deep tests protect correctness, stack safety and cleanup. They are not a
requirement to minimize runtime at depths that the external Maude backend cannot
process practically. Prefer simpler implementations with better ordinary-proof
performance when those protections remain intact.

An indexed unifier with a pending-equation worklist made 8,192 successive
bindings much faster, but added costs to ordinary proofs. A four-way CI-profile
comparison isolated the previous unifier, the indexed worklist, and the worklist
without its index while keeping the other fixes. Across eight rotating runs per
binary and case, restoring the previous unifier ranged from 0.6% faster to 0.4%
slower than the fixed pre-change baseline on NSPK, keyless SSL injectivity, DNP3
and NAXOS. Removing only the index left NSPK 2.4% slower. All outputs matched.
These are screening measurements, not a general release-performance guarantee.

The production unifier therefore retains the previous idempotent accumulator,
revision reuse and guarded recursion. The indexed implementation remains only
as an independent test oracle. This deliberately accepts quadratic work for very
large sequences of bindings; stack safety does not depend on that optimization.

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

The shared-hash, SAPIC parser/state-walker and scalar-polarity simplifications
were screened against the immediately preceding branch version in the CI
profile. Six alternating runs per binary and proof gave median elapsed-time
changes of +1.0% for NAXOS, -0.4% for keyless SSL injectivity, -1.4% for DNP3
and +0.5% for NSPK. All 365 proof-corpus outputs and 593 web responses matched;
1,500 generated SAPIC parse cases also matched, including diagnostics. These
measurements support retaining the simpler implementations, but do not establish
a general performance gain. The affected crates' 686 tests and all-targets
Clippy checks passed, including the existing deep syntax and cleanup cases.

An eight-pair alternating batch screening of the security-device SAPIC example,
with state optimization enabled, measured parsing 1.9% faster and MSR translation
0.6% faster. The batches parsed 200 copies or translated 10 copies per invocation;
translation disabled derivation and no-deconstruction-chain checks. Output
matched in every run. This checks the changed SAPIC path without attributing
the whole timing difference to any single pass.

## Remaining reviewer suggestions

The follow-up experiments compared against the branch after the first five
simplifications. Retained candidates preserve the existing stack regressions;
guarded recursion does not imply constant native-stack memory.

| Candidate | Decision and reason |
| --- | --- |
| Shared compact/alternate term Debug | Rejected. Ten alternating benchmark pairs measured compact formatting about 4% slower for an eight-level unary term. The existing compact loop is small; alternate formatting already shares Rust's guarded formatter. |
| Remove `type_theory_env` phase wrapper | Retained. Typing, renaming and reconstruction are independently protected. The public entry test covers deep definitions, annotations, declared types and error cleanup on 256 KiB. |
| Recursive include expansion | Retained. Lexical source/lexer lifetimes remove parked parsers and rebinding, while state and output remain shared across files. Existing deep success, failure and cycle checks pass. |
| Cached recursive `type_with` | Retained. Local variables express both inference passes directly. Cache generation, invalidation, root exclusion, zip lengths and error order remain intact and match the independent reference. |
| Shared AST cloning kernel | Rejected after an interface sketch. Preserving existing child APIs and shallow fast paths requires adapters that largely replace the deleted loops. Rule, selector and proof nodes have different shallow-copy policies. Moving methods into a trait spreads that interface through callers; a macro instead hides the method protocol. Neither gives a clear holistic simplification. |
| Recursive Doc-building `pretty_term` | Retained. Removes the private traversal scheduler while preserving leaf/nullary fast paths, pair flattening and `pretty_app`. The targeted benchmark was about 2.7% faster. The flat direct writer and lazy Doc machinery remain unchanged. |
| Recursive formula grammar | Retained. Removes operator frames and manual alternative unwinding while preserving the delimiter index, lazy atom fallback, precedence and diagnostic selection. |
| Raw Haskell-style term rendering | Fixed with guarded child calls. The original renderer overflowed on an 8,192-level term on 256 KiB in an isolated reproduction; the reveal-oracle caller now has a deep regression test. JSON export is covered separately below. |

The raw-renderer guard cost about 10% in the same isolated unary-term benchmark
(50,000 renderings per sample). This is an explicit safety tradeoff, not a claim
about whole-proof cost. The formatting measurements are narrow screening results,
not universal speed guarantees.

After reverting the Debug prototype, six alternating CI-profile runs per binary
and proof measured NAXOS -1.5%, keyless SSL injectivity +1.9%, DNP3 -0.3% and
NSPK +0.4% median elapsed time. Eight alternating pairs of focused batches
measured SAPIC parsing +1.2%, state-enabled MSR translation +1.0% and parsing a
ten-file include chain +1.4%. The first two batches used the security-device
example as above; the include batch parsed 200 copies per invocation. These are
small costs retained for the code reduction and explicit safety improvement,
not evidence of a speedup. The retained changes remove 186 production lines.
All 365 proof outputs, 593 web responses, 6,000 generated term/formula/process
cases and 1,200 generated include/proof cases matched the preceding version.
The affected test suites, new small-stack caller/error regressions, practical
deep CLI lifecycle test and all-targets Clippy checks also passed.


## JSON export follow-up

Retained a lazy term variant in the private JSON representation. Graph structure
remains shallow; term nodes retain existing shared ownership and expand one
level at a time through the common JSON writer. A guard at the term entry
protects formatting recursion. This removes the separate recursive term-to-JSON
construction pass and avoids needing a second deep-tree destructor. The JSON
schema remains distinct from raw term text, as required by the output format.

The preceding public exporter overflowed on a 512-level unary term on a 256 KiB
stack. The replacement passes that export and writer-error cleanup, plus final
drop of an unrendered 8,192-level term on the same stack size. Pretty indentation
still makes unary-chain output quadratic in depth; stack growth does not remove
that output-size cost.

All 15 JSON tests and 11 CLI trace-output tests pass, including the existing
byte snapshots; all 593 compared web responses match, and all-targets Clippy
passes for theory and prover. Ten alternating pairs of 1,000 public exports measured median
elapsed changes of +3.2%, +2.4%, +0.1% and +2.2% at unary depths 0, 1, 8 and 16.
These are narrow screening measurements of a one-action graph with abbreviation,
compression and simplification disabled, not whole-proof performance claims.
The small measured cost is retained for removing a recursive ownership path and
protecting the public exporter without another traversal scheduler.
