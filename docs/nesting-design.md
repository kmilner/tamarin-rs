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

## Review scope and compatibility

Review the branch in three layers. The required term lifecycle includes parsing,
conversion, internal ownership, substitution/comparison and document output,
plus term consumers inside formulas, processes and proofs. Independent formula,
process and proof-tree nesting extends the original generated-term requirement.
Semantic and diagnostic compatibility checks isolate those refactors; they do
not automatically establish the best permanent behavior.

For example, invalid induction-guard rejection already exists in
`codespan-error-reporting`; retaining it protects a logical precondition rather
than adding a new nesting feature. Conversely, the retained Haskell SAPIC purity
classification has a known optimization discrepancy. Matching Haskell does not
make that discrepancy correct. SAPIC inference retains contextual public types; MSR translation erases tags,
while typed output resolves bound-variable snapshots. The connective representation review below
now deliberately canonicalizes singleton disjunctions while retaining existing
goal identities. These policy changes require expected results and consumer
analysis rather than being smuggled into traversal cleanup.

The commit series follows the dependency order below. Each checkpoint passes
`cargo check --workspace --all-targets`; those checks establish buildability,
not that intermediate checkpoints provide the completed branch's depth coverage.

1. Shared stack guard and test-stack fixture, including dependency declarations.
2. Internal term ownership, operations and their independent reference tests.
3. Document ownership, layout and shared lazy suffixes.
4. Surface parsing and AST lifecycle, including sibling walker test modules.
5. Formula ownership, scoped freshening and guarded normalization, together with
   dependent wellformedness, accountability and solver-test API consumers.
6. Internal process ownership and conversions, with mechanical adaptations of
   SAPIC consumers to the new child owner.
7. Theory checks and solver term transformations.
8. Proof search, replay and output lifecycle.
9. SAPIC shared traversal, branch-scoped state and translation.
10. Practical CLI acceptance coverage and design/testing documentation.

Tests stay with the implementation they protect. The later document-suffix fix
and regression cleanup are folded into these areas. This organization reduces
review scope per commit; it does not remove the independent nesting features.

### Test consolidation audit

The cleanup removed 592 net lines across source/test files and test dependency
plumbing without changing production algorithms. It replaced 111 repeated
thread-builder fixtures with one helper retaining explicit stack sizes and the
original panic payload. Twelve sibling files now hold large inline suites or
reference checks, preserving access to private implementation details.
Extracting pre-existing inline tests increases raw added/deleted diff counts
against the parent even though the resulting code is smaller; the 592-line
figure is a net reduction, not a reduction in raw additions. Review moved blocks
with `git diff --color-moved` when assessing the extraction.

Document transformations share a named case table. Blocking-choice and
nonblocking-output progress-depth scenarios share setup while retaining both
paths and their assertions. Redundant progress-set comparisons were removed
where existing ordered-vector comparisons were stronger. The recursive progress
oracle now obtains successors independently of the production successor walker.
A duplicate check of a guarded reference helper was replaced with a production
normalization versus reference comparison in the existing wide-case loop.

Bounded reference implementations, error cleanup, concurrency and distinct
shape/lifecycle checks remain. The saving primarily removes scaffolding, not
independent coverage. Final runs passed 1,593 unit tests across parser, SAPIC,
term, test-support, theory and utils, all four `deep_syntax` integration tests,
and workspace Clippy with warnings denied.
See [TESTING.md](../TESTING.md#keeping-nesting-tests-maintainable) for the policy
for extending these suites.

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
| Large-stack entry points | Accommodate remaining recursive helpers and temporary values | Keep where remaining recursion needs the fallback; the SAPIC pre-report and theory typing paths, whose shared process visitor now grows the stack independently, need no additional wrappers. These boundaries do not prove that arbitrary callers and returned values are protected. |

## Refreshed comparison against the parent (2026-09-14)

This measures the complete production branch against `codespan-error-reporting`
(`daafdef`), rather than the incremental effect of a recent simplification.
Both binaries use the release profile (fat LTO, one codegen unit), Rust 1.98.1,
and Maude 3.5.1 on the same Linux host. The branch executable was frozen from the
verified production tree at `135b401`; subsequent changes are test consolidation,
documentation and history organization.

The eight README proof examples ran in three pairs per worker count, with
alternating binary order and rotating example order. Both Rust and Maude used
one or four workers; derivation-check timeout was 30 seconds. Wall time uses a
blocking process wait with a separate watchdog, avoiding timeout-polling
quantization. Values below are medians in seconds; positive deltas mean slower.

| Example | Parent, 1 worker | Branch, 1 | Change | Parent, 4 workers | Branch, 4 | Change |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `NSPK3` | 0.374 | 0.381 | +1.9% | 0.282 | 0.278 | -1.6% |
| `Joux` | 4.059 | 4.259 | +4.9% | 3.930 | 4.203 | +7.0% |
| `stateverif_left_right` | 2.165 | 2.336 | +7.9% | 1.332 | 1.467 | +10.1% |
| `Yubikey` | 2.875 | 2.733 | -4.9% | 2.212 | 2.132 | -3.6% |
| `mixvote_SmHh-multi-session` | 3.016 | 3.202 | +6.2% | 1.313 | 1.377 | +4.9% |
| `gcm` | 6.385 | 6.965 | +9.1% | 2.612 | 2.733 | +4.6% |
| `wireguard` | 4.777 | 5.210 | +9.1% | 2.294 | 2.388 | +4.1% |
| `CCITT_X509_3` | 17.976 | 18.825 | +4.7% | 5.104 | 5.258 | +3.0% |

At 1 worker, the equal-weight geometric mean time change is **+4.8%**;
the change in the sum of example medians is +5.5%. The geometric mean
change in median peak process-tree RSS is +0.8%.

At 4 workers, the equal-weight geometric mean time change is **+3.5%**;
the change in the sum of example medians is +4.0%. The geometric mean
change in median peak process-tree RSS is -2.3%.

RSS was sampled every 20 ms and sums the prover and its Maude descendants;
it is a memory proxy that can count shared pages more than once and miss brief
peaks. These three-pair measurements are a workload screen, not confidence
intervals or a causal attribution to the term owner. In particular, small
percentage differences and parallel-run variation need more samples before
motivating implementation changes.

For each example and worker count, normalized theory/proof stdout matched
between binaries and across all repeats (96 successful runs). Only build
metadata, input paths and processing-time lines were excluded. Binary/input
hashes and raw measurements are retained locally under
`target/review-tmp/scope-performance-manifest.json` and `scope-performance/`.

## Why storage affects proof performance

The old term arguments were an `Arc<[Term]>`. The current representation uses
an `Arc` owner containing a boxed slice, adding a live allocation and an
indirection while reducing the measured term size from 48 to 40 bytes on the
benchmark target. Comparison, substitution and temporary destruction use this
representation throughout search. Iterative parsing alone does not impose that
cost. The refreshed parent comparison above measures the broader branch; it does
not isolate the causal contribution of this representation from other changes.

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


## Further simplification review

Six candidates were retained; none changes the intended Haskell semantics.

| Candidate | Decision |
| --- | --- |
| Free-constructor unification/matching arms | Combine the identical NoEq/List descent, preserving the separate AC/C cases. |
| Report term rebuilding | Share the existing `bind_lits` postorder scheduler through `fold_term`, with literal and completed-application callbacks. Newly inserted locations are not traversed. |
| Document spine composition | Share horizontal/vertical cursor and lazy-choice handling using a const-generic operation and an inline hint. The ownership helpers and lazy evaluator remain unchanged. |
| Pattern stripping | Use guarded recursive constructor mapping, preserving marker order and avoiding temporary binary-child vectors. |
| Empty-trace evaluation | Use guarded scalar recursion; evaluate each child before combining Booleans so later errors remain visible. |
| Maude list/term emission | Use direct rendering with a shared list loop and guards only on nonliteral children. This removes the private scheduler while keeping constant bookkeeping for list width. |
| Malformed formula diagnostics | Initially rejected a partial delimiter-cache prototype: repeated atom alternatives still dominated. The later coordinated group-recognition redesign below addresses both sources of repeated work. This behavior predates the branch. |

A naive shared Maude scheduler would add one pending close per list element;
that is worse than the original direct list path. A guarded renderer which checks
at every application also regressed the depth-one screening case. The retained
renderer instead handles literals directly and guards only nonliteral children.
Twelve alternating unary-term batches measured 26–29% faster at depths 0, 1, 8
and 16. Ten alternating list batches at widths 0, 1, 8, 128 and 4,096 were mostly
faster; the largest list of hash applications was about 4.6% slower. These isolated
measurements do not establish whole-proof speedups.

The first shared document loop used a runtime operation and measured up to about
3% slower in narrow construction/rendering batches. Compile-time specialization
plus an inline hint measured +1.0%, -3.5% and +1.0% for horizontal, vertical and
mixed cases, respectively (ten alternating pairs). This small cost range is
accepted for consolidating the ownership-sensitive loop, without replacing the
shared lazy evaluator or destructor.


The retained changes remove 125 implementation lines. All 365 proof-corpus
outputs and 593 web responses match the preceding branch version. The five
affected libraries pass 1,549 tests, including the new small-stack/error cases;
the practical deep CLI lifecycle, 11 trace-output tests and all-targets Clippy
also pass.

Six alternating CI-profile proof pairs measured NAXOS +1.6%, keyless SSL
injectivity +0.9%, DNP3 +0.5% and NSPK +3.9% median elapsed time. The larger NSPK
result did not persist: a longer sixteen-pair confirmation measured -0.6%,
with matching output. Both observations are retained here to make the short-run
variation explicit. Eight alternating focused
pairs measured SAPIC parsing +0.2%, state-enabled MSR translation -0.5%, and
parsing a ten-file include chain +0.4%. These measurements screen the combined
change; they do not attribute cost to any individual simplification.

## Formula group recognition and diagnostics

Formula parsing now keeps one formula-local record per parenthesis group:
its boundary state (unscanned, unclosed, or closed) and an optional term-parse
outcome. Recording unclosed groups prevents repeated delimiter scans. The term
grammar records failed group outcomes while unwinding, including their lexer
state, explicit-sort flag and delimiter-aware diagnostic. Both ordinary grouped
atoms and diagnostic retries can reuse failures.

When the boundary rules out a successful atom, diagnostic recognition may also
reuse successful group summaries. Those summaries retain only variable/nullary
heads needed for node-sort checks, never a nested AST. This avoids replacing
repeated parsing with repeated deep clones. Actual AST construction reuses only
failures. Both modes execute the same term grammar and relation parser, including
partial relation-token consumption and nested-list error attribution; there is
no separate approximate diagnostic grammar. Alternative ordering is unchanged.
Compile-time specialization keeps memoization out of ordinary ungrouped terms.

Expanded reference tests compare ASTs and full diagnostics for complete and
partial groups, relation continuations, quotes/comments, list errors and both
resolved and structural applications. Work-count regressions on 256 KiB stacks
cover 1,024/4,096/8,192 nested groups, including bodies that grow with group depth.

Six alternating optimized comparisons used identical dependencies, optimization
level 3, one codegen unit and fat LTO. At depth 4,096, unmatched openings improved
from 360 to 9 ms, a parenthesized bare term from 475 to 6 ms, and nested invalid
relations from 314 to 6 ms. Ordinary batches of 20,000 parses ranged from 1.7%
faster to 0.4% slower. Valid grouping at depth 4,096 rose from 2.4 to 3.2 ms;
depths 1,024 and 2,048 were approximately level. These focused measurements
support the malformed-input improvement, not a whole-proof performance claim.

## Surface equality and term positions

Surface-term equality reuses the AST child order with an explicit paired walk.
Protecting `Term::eq` itself covers duplicate rules and other derived comparisons
containing deep terms. A unary continuation stays inline without a heap worklist
allocation. Surface-term Debug grows the stack at recursive edges. A shared
pretty-depth budget retains derived formatting for ordinary trees and switches
deep subtrees to complete compact output.

Position enumeration and both occurrence searches share one preorder path walker;
only emitted results copy the path, and unary descent saves no sibling frame.
It preserves the binary AC convention used by enumeration and access, the n-ary convention used by occurrence searches,
reverse sibling order in `find_pos`, and pruning at matches. Ordinary lookup and
protected-ancestor lookup use loops. `find_all_subterms` reuses the existing term
walker and accumulates results directly while preserving short-circuit failure.

Access keeps the current normalized AC tail in a local owner while the loop
borrows its descendants; borrowing the raw argument suffix without normalization
would change behavior for noncanonical inputs. Replacement retains guarded
recursion: lexical reconstruction is simpler than a second owned rebuilding
machine and needs no large caller stack on supported stacker targets. This does
not remove the stacker dependency, which is also used by parsing, conversion and
proof search. The small
reference and deep regression cases are described in TESTING.md.

Validation against the pre-fix branch: 1,472 affected library tests pass, as do
Clippy on all affected targets, the practical deep CLI lifecycle and 11 trace
tests. The new duplicate-rule and position regressions also pass in debug builds.
All 365 proof-corpus outputs and 593 web responses match the pre-fix executable.

Six alternating pairs on the final executable measured NAXOS -0.3%, keyless SSL
injectivity +0.5%, DNP3 exists-trace -0.6%, and NSPK -1.7%, with matching output.
The focused unary helper screen at depths 4/16/64 measured `find_pos` 54–80%
faster. `find_subterm` measured +6%, approximately level, and -18%, respectively;
keeping unary continuations inline removed the larger worklist overhead seen
in the initial candidate. The shallow +6% is about five nanoseconds per call.
These helper comparisons compile the old reference locally and link the new
non-generic helper from the library, so code-generation boundaries also affect
the numbers. Guarded replacement measured 8–14% slower in isolation; it currently
has no in-repository production callers. These are performance screens, not
precise guarantees for other workloads or machines.

Twenty-four alternating parse-only pairs measured -0.5% for a fixture with
1,000 identical four-level rules and +2.3% for 10,000 such rules, with matching
output. An earlier eight-pair 1,000-rule screen measured +8.1%; that result did
not persist in the longer confirmation.

Nested `Rule` equality grows the stack at rule edges, covering left/right and
variant trees without adding work to ordinary rule comparisons. Rule Debug uses
the same guarded-edge design. Canonical substitution now
collects variable occurrence sets in one iterative pass, retaining the Haskell
distinction between indexed NoEq arguments and unordered AC/C operands. Its
stable comparison borrows occurrence sets instead of cloning them into sort
keys. Formula reconstruction keeps the current root as an unboxed value and
allocates `FormulaBox` only for actual parent-child edges; traversal, owned atom
mapping, and parser conversion no longer allocate a synthetic root box.

## Direct-call audit

The CLI acceptance path remains protected by `with_compiler_stack`, but an
adversarial 256 KiB caller-stack audit also exercised public-library entry
points outside that boundary. The resulting fixes share two low-level term
walkers. Read-only wellformedness scans, multiplication-node collection, name
collection and fresh-redundancy membership use the preorder walker with
short-circuiting or subtree pruning. Multiplication abstraction, variant
abstraction and graph abbreviation use one top-down iterative rewriter. Its
ordinary form rebuilds every visited application, preserving smart-constructor
normalization; its copy-on-write form retains graph abbreviation's unchanged
subtree sharing.

Surface `Formula` equality now compares paired nodes iteratively, and the
public formula-term mapper reconstructs formulas from an explicit task stack.
Raw nested AC flattening also uses a worklist. Small-stack regressions cover
these helpers together with the public multiplication report, variant
abstraction and abbreviation replacement. The multiplication report test found
and removed a separate recursive multiplication-node scan that a helper-only
test would have missed. Restriction elaboration passed the direct-call audit.
The initial quantifier-collection probe covered only unary nesting; later
left/right branching probes exposed an unprotected walk. Binder collection now
uses a preorder worklist, and natural-sort reporting guards its scoped traversal
of guarded formulas. Both public reports have 8,192-level branching regressions
on 256 KiB threads.

A follow-up trait audit found that derived comparison still recursed through
surface process branches, tactic selectors and parsed/internal proof trees, and
that derived Debug recursed through all of those plus surface terms, formulas
and nested rules. Process, selector and proof-tree comparison now use explicit
paired worklists. Recursive Debug implementations grow the stack at each
recursive entry. Alternate Debug also needs a shared pretty-depth budget:
Rust's nested indentation writers recurse outside these guards. After 16 nested
tree entries, subtrees render compactly, retaining every field and node. This
preserves ordinary pretty output without a second formatting engine or an
unbounded chain of padding writers. The thread-local budget restores on success,
formatting errors and panics. Adversarial branching and unary fixtures exercise
compact and alternate Debug on 256 KiB threads across all affected tree types.
The compact suffix uses default Debug options, including decimal rather than
hexadecimal numeric formatting; caller formatting flags stop at that boundary.

Rule-let capture avoidance collects replacement variables lazily at the first
non-shadowed quantifier, sharing that cache across the binding's restrictions.
Quantifier-free and immediately shadowed formulas need no replacement scan.
Variable collections use membership sets keyed by name, sort and index; type
annotations are excluded. Ground and non-overlapping replacements need no
alpha-renaming bookkeeping.

When capture avoidance is necessary, substitution uses one freshness supply
and one scoped traversal for the entire restriction. Original variable names
are collected once; replacement names are borrowed from the binding's cache.
A cursor per name/sort allocates the smallest available index without repeating
occupied-prefix searches. The traversal maps original bound identities to their
new indices and applies substitution only to free occurrences. Explicit scope
exits restore that map after nested binders and sibling branches. Inserted RHS
trees are never revisited. There are no per-binder body scans or renaming passes.

Fresh names avoid every original name in the restriction and every name already
generated there. Consequently their exact indices may differ from the previous
subtree-local policy; free variables, binding structure, annotations and reverse
binding-composition order are preserved. Repeated names in a single binder group
retain the previous left-to-right renaming behavior.

For one binding/restriction, work is expected linear in formula/term size,
replacement size and inserted output size (hash-table membership); binder width
and depth do not multiply body size. Multiple bindings still apply in reverse
source order, and copying an inserted RHS still costs its output size.
Tests compare 12,000 substitutions against the previous algorithm modulo bound
names, retain the lazy-cache and ground-substitution checks, and combine 8,192
wide binders, 8,192 nested conflicting scopes and a large body on a 256 KiB stack.
The original wide-binder parsing probe at 512/1,024/2,048 binders measured roughly
5/11/21 ms in debug, versus 101/381/1,524 ms before this redesign.
Additional public-parser probes grow binder count, replacement size and body
size together: from 512 to 4,096 variables, wide groups took 8–61 ms, nested
scopes 13–104 ms, and combined wide/deep scopes 13–117 ms. The ground-replacement
control took 3–25 ms. These are diagnostic debug timings, not corpus benchmarks.

## Lazy paragraph construction

Both `fsep` and `fcat` defer long flat suffixes as well as line-break alternatives.
Previously each selected break reconstructed the entire remaining flat suffix,
causing quadratic work even at a fixed narrow width. A raw `Suspend` continuation
now composes with nesting, beside/above, one-line filtering, sep and fill through
the existing evaluator. Layout's reduced `Deferred` nodes remain separate.
Both continuation kinds use the same iterative memoization and cleanup machinery.
Suffixes of at most 16 items retain direct construction to avoid overhead on
ordinary small documents; this bounded work does not grow with paragraph length.

Generated mixed documents compare against independent eager fill equations across
page, inline and one-line rendering. Tests also bound construction work for narrow
paragraphs and release deep unforced construction chains on 256 KiB stacks.
The public invalid-term diagnostic probe at 1,024/2,048/4,096 atoms improved from
about 1.13/4.58/>10 seconds to 26/54/108 milliseconds in debug builds. This is a
fixed-width paragraph improvement, not a universal linear bound for arbitrary
document choices and rendering widths.

## Guarded connective normalization

Smart conjunctions, smart disjunctions and stored disjunctions now use one
borrowed flattening iterator and one copy-on-write normalization operation.
Flattening and membership checks construct the replacement list on the first
change; unchanged prefixes stay borrowed. Owned smart-constructor calls can
reuse their original vector when the list is unchanged. The independent
structural-no-op predicates and their separately maintained rebuilding loops
have been removed from production.

The initial refactor retained three semantic policies. Conjunction absorbed False
and unwrapped singletons after deduplication. Smart disjunction absorbed True and
tested singleton length before deduplication, preserving `Disj [a]` for `[a, a]`.
Stored disjunction neither absorbed True nor unwrapped singletons. The later
representation review below replaces that asymmetry. The maximal-run prepass
still flattens before rebuilding descendants, using the shared iterator to avoid
quadratic copying of binary connective chains.

A bounded recursive normalization implementation serves as an independent test
oracle, updated to the chosen connective policy. Tests compare exact structure
and copy-on-write results for 4,000
generated formulas, including binders, constants, duplicates and mixed
connectives; they also check idempotence and stored formula/goal agreement.
Existing 8,192-level tests continue to exercise both association directions on
256 KiB stacks. The refactor removes 42 production lines including comments
and blank lines, or four lines when comments and blank lines are excluded.
A further 44 lines of an existing test oracle move to the test file. The simplification is removal
of independently maintained algorithms, not a large code-size reduction. Test
code grows to retain the oracle and exercise the shared policies independently.

The full theory suite passed 1,037 tests (one existing ignored test); the final
iterator cleanup also passed all 108 focused tests and all-targets Clippy.
Six alternating release-build pairs, with one prover and Maude worker, measured
median elapsed changes of +1.5% for NAXOS, -1.0% for keyless SSL injectivity,
+0.7% for DNP3's existence proof and +0.3% for NSPK. All measured proof outputs
matched. These are local screening results, not a general speedup claim.

Eight alternating microbenchmark pairs at widths 2, 8, 32 and 256 measured
smart constructors 17–37% faster and duplicate-list normalization 42–48% faster.
Already-normal flat lists ranged from 0.6% faster to 15% slower; the latter is
about 11 additional nanoseconds per two-element normalization. The small
no-change cost is accepted for shared transformation logic and cheaper changed
lists, with ordinary proof timings remaining the primary performance criterion.

The final release executable also matched all 365 fast-corpus proof outputs
and all 593 web responses across Tutorial, NSPK3 and the SAPIC channels example
against the pre-refactor executable; neither comparison had failures or caps.

## SAPIC inference design review

The two ordinary-function inference passes remain in their original order.
Typed terms from the first pass can be retained in the cache and reused by the
second pass. Separating propagation from construction at every function
application loses that reuse: the prototype passed semantic tests but repeated
inference work and allocated more input-type lists on nested functions. It was
rejected.

A narrower prototype selected construction once per complete inference call.
Ordinary term typing still built and reused typed subtrees in both passes;
rewrite-rule inference and event-type recording omitted their unused term
results. Both modes used the same inference algorithm and mutation invalidation,
and each cache belonged to one mode throughout its lifetime. This saved
allocations but added 33 production lines, including an optional term result and
construction mode throughout the visitor. It was also rejected: it did not
simplify the design, and ordinary-workload measurements showed no benefit.
The original production algorithm is retained.

Rebuilding later from the final environment would change occurrence-specific
annotations. In the polymorphic list `[x, f(x)]`, where `f` requires type `a`,
the first `x` remains untyped even though the environment learns `x: a` while
visiting `f(x)`. A focused regression assertion now pins this behavior. Both
passes, their error order, and effective-mutation cache invalidation remain
necessary for the existing Haskell-compatible behavior.

Both prototypes passed the existing typing tests. The narrower prototype passed
all 98 SAPIC tests; its type-only inference also matched 3,000 generated reference
cases for inferred types and final variable/function environments, including
failures. Both of its construction modes passed the 20,000-level ordinary-function
and polymorphic-list tests on 256 KiB stacks. Those prototype-specific tests and
production changes were not retained.

Separate timing and allocation probes compared unary terms at depths 1, 8, 64
and 1,024, with absent types, newly learned types and already-known types, plus
polymorphic lists. Six rotating release-optimized timing runs per variant found
the broad split 45–101% slower for ordinary functions at depths 8 and 64.
The narrower prototype's type-only calls were 5–23% faster for ordinary functions
and 29–73% faster for polymorphic lists. Its ordinary typed-function calls ranged
from 3.1% faster to 3.5% slower. Allocation counting was measured separately: an
untyped depth-8 function chain went from 82 to 66 allocations for a discarded
result, while typed-result calls stayed at 82; the broad split needed 139.

Six alternating full-release pairs measured the narrower prototype at +1.9% for
GJM contract proofs, -0.2% for state-verification proofs, +3.9% for Yubikey typed
output, and +1.7% for the non-SAPIC NSPK control. The Yubikey difference was about
2.6 ms; these local measurements do not establish a general regression, but
also do not demonstrate an ordinary-workload win to justify added complexity.
All measured outputs matched. The narrower prototype additionally matched all
365 fast-corpus proof outputs, 166 typed/MSR module outputs across 83 SAPIC
theories, and 593 web responses. The retained implementation, with its new
regression assertion, passes all 98 SAPIC tests and all-targets Clippy.

### Type annotations at the MSR boundary

Occurrence-time annotations are retained internally by inference, but erased
when the checked process enters MSR translation. The typed-output follow-up
below separately resolves bound-variable annotations for presentation. They must not be
part of lock/state identity or substitution keys. Erasure shares the existing
iterative process conversion and term rewrite machinery; unchanged term
subtrees retain their shared allocation. It covers terms, standalone binders,
match-variable sets, free variables in formulas, and location annotations.
Formula-bound variables, process names and back-substitutions are preserved.
Synthetic state-channel binders also remain untyped, and let translation no
longer needs duplicate typed/untyped substitution entries. Parser-stage process
inlining still handles source annotations before inference and is unchanged.

The pinned Haskell implementation (revision
`573a43953195d83e62fdbe32fc98253031bca60f`) exhibits a concrete failure:

```spthy
theory TypedLock
begin
functions: f(a):a
process:
  new s;
  lock s;
  out(f(s));
  unlock s;
  event Done()
lemma reaches_done:
  exists-trace "Ex #i. Done() @ i"
end
```

Haskell and the previous Rust version reject this with `Unannotated unlock`.
Haskell's `-m=spthytyped` output contains `lock s.1:a` and `unlock s.1`:
postorder inference visits the unlock before learning the type from `f`, then
lock annotation compares the complete typed terms. Both explicit `new s:a`
and untyped `functions: f/1` controls prove successfully in Haskell. The boundary
fix makes those spellings equivalent for MSR translation.

Rebuilding all annotations from the final environment is not a substitute for
this boundary. Haskell's `typeWith` deliberately ignores the prior environment
type for public variables. With `f(a):a, g(b):b`, the accepted output
`out(<f($s:a), g($s:b)>)` gives one public variable two contextual types.
The Haskell export code also consumes type annotations for ProVerif binders
and parameters, and the final function/event environments for headers and
queries. The boundary change leaves inference and contextual public types intact
instead of imposing a new global typing rule. The follow-up below resolves
bound-variable presentation separately; MSR correctness is independent of it.

Generated MSR rule names and `process=` attributes now describe the erased
process, so type-bearing names can change. Saved proof scripts that explicitly
refer to those names may need regeneration. Typing failures and typed theory
output are unchanged. The separately documented pure-state criterion issue
remains deferred; erasure fixes state identity, not that optimization policy.

Validation: all 1,753 workspace unit tests, all-targets Clippy, 22 SAPIC/output
CLI tests and 14 Haskell oracle tests pass (one heavyweight oracle probe remains
ignored). A parameterized translation test compares typed and untyped function
signatures across seven process shapes, with state optimization both enabled
and disabled; it also checks complete tag erasure and retained typing errors.
The existing deep process pipeline test includes the lowering boundary.
All four executable lock variants (inferred, explicit, untyped and contextual
public types) prove their reachability lemma. Across 83 SAPIC theories, all
typed outputs match the pre-change executable byte-for-byte. Of their MSR
outputs, 71 match byte-for-byte; the remaining 12 match in rule bodies and
restrictions after accounting for generated names, attributes and whitespace.
Three alternating release pairs at one and four workers compared NSPK3,
stateverif_left_right and Yubikey (36 runs). Aggregate geometric-mean runtime
changes were +0.84% and -0.76%, respectively. The two SAPIC workloads ranged
from -1.95% to +1.34%; the non-SAPIC control ranged from -1.63% to +1.46%.
These short local measurements show no clear ordinary-workload regression.
All proof outputs match after the expected generated rule-header changes;
Yubikey differs only in its two synthetic state-channel declarations and
corresponding printed variants. No builds or tests ran during timing.
Investigation artifacts are under `target/review-tmp/typing-annotations/`.

### Consistent bound-variable annotations in typed output

`type_theory_env` now resolves each renamed bound variable to its final inferred
per-process type after inference succeeds. The original lock example therefore
prints `new s.1:a`, `lock s.1:a` and `unlock s.1:a`. Public variables preserve
their contextual types, including different tags for `f($s:a)` and `g($s:b)`.
Quantifier-bound indices and reverse renamings remain unchanged. The final
variable environment is authoritative; use-site annotations do not become new
constraints, and this pass does not infer types from previously skipped formulas.

Normalization happens before that process's variable environment is cleared
for the next process. Process definitions use the same operation before their
synthetic input wrapper is removed, keeping formal parameters and their uses
consistent. This is a presentation pass, not a whole-theory inference fixed
point: function and event environments, inference order and typing errors are
unchanged. MSR translation still erases the raw inference result directly,
without paying for an intermediate presentation pass.

Typed-output normalization and MSR erasure share `process_walk::rewrite_variables`.
It covers ordinary terms, standalone binders, pattern match sets, free variables
in formulas and parsed locations, preserving unchanged shared term subtrees.
One replacement callback distinguishes the two policies; neither consumer has
its own process/term traversal or new cache.

Tests share a ten-process table covering lock/state operations, let/input
patterns, formulas, locations, branches and shadowed binders. They check final
bound types, retained public types, identical inference environments and
identical erased processes. The existing deep definition test now includes a
later untyped use and checks both the body and explicit/implicit formals after
normalization on a 256 KiB native stack.

All 1,754 workspace unit tests, all-targets Clippy and 22 SAPIC/output CLI tests
pass. Across 83 theories, all MSR outputs remain byte-identical; 81 typed outputs
also match, while `basic/typing.spthy` and `States/canauth.spthy` differ only in
resolved bound-variable annotations and their layout. The changed basic typing
output reparses and retypes successfully. CANauth already fails that round trip
in the baseline: inferred process formals are printed alongside stale calls
without arguments. A minimal reproduction and follow-up are recorded in the
untracked design note; this separate process-call representation issue is not
changed by annotation normalization. Artifacts are under
`target/review-tmp/typed-output/`.

Three alternating release pairs across NSPK3, stateverif_left_right and Yubikey
at one and four workers (36 proof runs) retained byte-identical outputs.
Geometric-mean runtime changes were +1.83% and -1.45%; the non-SAPIC control
varied by +2.69% and -1.45%, so these runs show no clear proof-time regression.
Seven alternating pairs per typed-output workload measured median differences
of -0.44 ms for Yubikey, +0.58 ms for CANauth, +1.38 ms for basic/typing and
+5.23 ms for 5G-AKA (-0.63%, +0.88%, +2.08% and +6.28%, respectively).
The extra presentation pass has a modest absolute cost; the simple shared
implementation is retained without another traversal mode or cache. Builds,
tests and the two timing suites did not overlap.

## Removing redundant collections in progress, canonicalization and state declaration

Progress successor enumeration returns `(position, borrowed subprocess)` pairs.
The left-first DFS emits each position once in lexicographic order, so a vector
preserves the old set order without sorting or resolving paths back into nodes.
`pf_from`, progress initialization and the internal CNF traversal are infallible;
`pf` still validates
caller-supplied positions. The inverse map visits source positions in ascending
order and keeps the first entry for each target, preserving the old sorted
`(target, source)` relation's minimum-source rule without materializing that
relation or intermediate flattened sets.

Canonical substitution borrows range terms in domain order. Its occurrence-map
keys are exactly the sorted, deduplicated range variables, so they replace the
separate variable walk while preserving stable occurrence ties. Reconstruction
feeds the substitution constructor directly, without temporary range/result
vectors. AC/C normalization and variable sorts retain their existing policies.

State declaration keeps its bound-name scope as `LVar`, the projection already
used for every membership check. It no longer reconstructs that projection at
each node. The annotation entry point collects bound states once and passes
them to declaration; the unused free-state collection is removed. Purity
classification, branch scope, annotation updates and fresh-name order are
unchanged, including the intentionally retained Haskell purity behavior.

Together these changes remove 36 production lines (24 excluding blank lines and
comments), excluding test-only adapters and reference checks. They remove
intermediate representations without introducing traversal modes or guards.

Validation includes all 98 SAPIC and 292 term unit tests, with a focused rerun
of the final three canonicalization tests, plus all-targets Clippy and formatting.
Generated progress comparisons check successor order and pointer identity,
CNF results, inverse selection against the sorted reference relation, and
invalid external positions. State reference comparisons include differently
typed copies of the same bound name; existing small-stack tests remain in place.
All 365 fast-corpus proof outputs and 166 typed/MSR outputs across 83 SAPIC
theories match the pre-change binary.

Six alternating before/after timing pairs per workload, with one prover/Maude
worker and identical outputs, gave median wall-time changes of +0.8% for OPC-UA
progress translation, -1.1% for the locations/state AC example, +2.0% for Yubikey
MSR output, and -1.1% for the NSPK proof. This small ordinary-workload sample
shows no clear overall performance gain; the justification is less redundant
work and simpler production code, with the observed timing spread recorded.

## Commit-review follow-up

Guard matching uses guarded depth-first recursion. Each candidate substitution is
combined with its prefix only when entering that branch, so a wide AC fanout
retains one combined prefix per active depth instead of one per pending sibling.
Formula term mapping, BFS level transformation and scalar state purity likewise
use guarded constructor/scalar recursion; their previous private frame machines
provided no sharing benefit. Partial-evaluation term abstraction reuses the common
term rewriter. The purity policy itself is unchanged.

Process position lookup is a loop. Read-only process visitors grow the stack while
preserving combinator left/self/right order, and variable collection reuses that
visitor. Proof Debug follows the shared bounded pretty policy; status and node
counting share a borrowed preorder iterator. Generic term, formula and process
owners drain pending siblings in traversal order even during a payload panic.

Singleton document fill is an identity only for normalized input. Raw mid-line
nests require the original fill equations. Shared document nodes cache a
conservative normalization predicate; mutable construction cursors invalidate it.
Lazy construction plans separately cache the root and mid-line cases without
forcing alternatives. The predicate follows the filled left spine, preserving
constant fill work when 128 or 1,024 unary wrappers surround either a two-item
eager paragraph or a 20-item suspended paragraph. Raw mid-line nests still use
the original normalization equations.

Negated equivalence is an intentional semantic correction: the two negated
implication arms are disjoined, not conjoined. Previously `not (T <=> F)` became
false in the Rust parent as well as this branch. Independent Boolean truth tables
now check both polarities and the lemma/restriction system consumers. Haskell
revision `573a43953195d83e62fdbe32fc98253031bca60f` was subsequently confirmed
to share the bug: `not (T <=> F)` is falsified for both all-traces and exists-trace
lemmas, while `(T & not F) | (not T & F)` verifies in both modes. All four pass
wellformedness checks. The Haskell `convert` Iff arm always uses `gconj`; under
negative polarity it needs `gdisj`. The Rust executable verifies all four.
The standalone upstream report is saved outside the repository as
`negated-equivalence-bug.md`; run artifacts are in
`target/review-tmp/typed-output/`. Other deferred semantic policies remain separate.

### Validation of the commit-review fixes

All 1,750 workspace unit tests pass, as do workspace Clippy (`--all-targets`,
`-D warnings`), the three consolidated parser lifecycle cases, active replay
trace-scope restoration, and the 8,192-level CLI open/render/reparse lifecycle.
Each of the ten amended commits was checked with `cargo check --workspace
--all-targets` in an isolated worktree. The cleanup-order fixture additionally
keeps two pending siblings live at a payload panic.

The final release was compared with the frozen pre-fix branch production binary
(the `cc7cb58` production implementation) using the same eight README examples,
three alternating pairs per example, and both one and four workers. All 96
normalized stdout results match. Geometric means of per-example median ratios:

| Workers | Elapsed time change | Process-tree peak RSS change |
| --- | ---: | ---: |
| 1 | -0.6% | +0.0% |
| 4 | -0.1% | -0.8% |

These small differences are consistent with roughly unchanged ordinary performance,
not evidence of a broad speedup. This is an incremental comparison with the
pre-fix branch, separate from the earlier comparison with `codespan-error-reporting`.
The final manifest and measurements are under ignored
`target/review-tmp/review-fixes-final-performance*`. An earlier timing run used
the conservative document classifier before its lazy-plan refinement and is
retained separately; it is not the result reported here.

The tiny negative-Iff theory is checked separately because its verdict changes
intentionally: both all-traces and exists-trace `not (T <=> F)` now verify, while
all-traces `T <=> F` remains falsified, without wellformedness warnings.


## Canonical connective representation and solver history

The representation review deliberately changes the old singleton policy. Both
`gconj` and `gdisj` now flatten same-kind connectives, absorb their annihilator,
deduplicate in encounter order and unwrap a singleton **after** deduplication.
Thus `gdisj([a, a])`, `gdisj([a, False])` and `gconj([a, a])` all return `a`.
Normalization applies these rules to children at every depth. It does not sort
alternatives, rename variables or attempt general Boolean equivalence.

This removes the `DisjStep`/`disj_run` summary machine and its shape bookkeeping
from conversion and smart rewrites. Both reuse the common maximal-run flattening
machinery; no growing binary prefix is rebuilt. The list normalizer no longer
needs a third semantic policy or a separate singleton-decision result.

### What the pinned Haskell actually does

The checked source and installed Haskell 1.13.0 executable both identify revision
`573a43953195d83e62fdbe32fc98253031bca60f`.

- `Theory/Constraint/System/Guarded.hs`, `gconj`/`gdisj` (lines 415–437), flatten
  and test for a singleton before applying stable `nub`. Consequently BOTH
  constructors can leave duplicate-induced singleton wrappers. Their definitions
  are shorter, but this policy is not idempotent. Rust had already changed
  conjunction; it now makes disjunction consistent with it.
- `Solver/Reduction.hs`, `insertFormula` (lines 427–493), records a top-level
  conjunction in `sSolvedFormulas` before decomposing its children. Rust already
  had this behavior. The earlier explanation that conjunction decomposition lost
  all processing history was incomplete: no new history store is necessary.
- `Solver/Simplify.hs`, `insertImpliedFormulas` (lines 406–419), checks structural
  membership in the open and solved stores before insertion. Haskell generally
  preserves connective constructors during substitution. The pinned source has
  no `normaliseGuarded`, `normaliseDisjList` or `normaliseStoredFormula` functions;
  earlier Rust comments attributing these normalization helpers to Haskell were
  inaccurate. They are Rust's storage-normalization machinery.

### Logical formulas versus pending goal identity

Newly inserted formulas use canonical logical form. A top-level conjunction is
recorded by the existing solved-formula mechanism before its children are
processed. Saturation compares **both** new instances and open/solved store keys
in that same canonical form. A retained disjunction wrapper therefore cannot
make an already-known instance fire again.

An existing disjunction goal is still a list of alternatives. Substitution may
make two alternatives identical, leaving a single conjunction to process. Its
stored formula must retain the root `Disj` wrapper until the goal is retired;
otherwise its formula key and goal key diverge. Both stores normalize that list
with the same operation, and all children use ordinary canonical formulas.
Only this root wrapper is preserved, including a singleton `True` alternative.

Saturation membership and insertion membership intentionally have different
roles. Solving a goal first records its enclosing disjunction as solved, then
inserts the selected alternative's obligations. Canonically comparing the
alternative with that just-recorded wrapper inside the inserter would skip the
work. The inserter therefore keeps structural membership; canonical keys belong
to saturation's check of already-known instances. No new state field, lifetime,
substitution path or branch-cloning rule is introduced.

Tests exercise duplicate and differently wrapped source instances, saturation
before/after goal solving, and substitution collapsing two conjunction
alternatives. Both explicit goal solving and atom valuation must retire the
old goal while still inserting the selected action and Last constraints.
Generated reference checks assert canonical and stored fixed points and keep
formula/goal lists synchronized. Existing small-stack conversion, normalization,
Boolean truth-table and branching solver tests remain applicable.

### Validation of the representation change

All 1,752 workspace unit tests and all-targets Clippy pass. The Haskell solver
integration suite passes all 14 enabled tests (the hour-plus corpus probe remains
ignored). A warning-free duplicate-conjunction theory has the same Haskell/Rust
results: both existence lemmas verify in two steps and the deliberately false
universal lemma is falsified in two. TAK1's selected `session_key_establish`
lemma verifies in 17 steps in Haskell, the prior Rust build and the new build;
its unselected secrecy lemma is not covered by this check.

The change removes 205 lines from `guarded.rs`, including 163 nonblank lines
that are not line comments. Solver comment cleanup removes another 86 net lines.
Two parameterized integration fixtures add coverage for the processing-history
and pending-goal lifecycle; existing generated tests use the new policy.

Eight ordinary example theories, three alternating pairs each, with one and four
workers produce 96 matching normalized stdout results, including proof output.
Geometric-mean median runtime changes against `f6fd5c3` are
+0.18% (one worker) and +0.48% (four workers); process-tree peak
RSS changes are +0.18% and +0.92%, respectively. These are roughly flat
ordinary-workload results, not a broad speedup claim. Timing runs were isolated
from builds and tests. Artifacts, binary/input hashes and per-example measurements
are under `target/review-tmp/connective-design/`.
