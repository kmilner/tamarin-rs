# Verified algebra for Tamarin

This Lake package specifies the algebra operations that Tamarin currently asks Maude to perform.
Rust links selected Lean kernels in-process with the `lean-unification` feature. The goal is to run
the prover with no Maude binary and let developers replace the search algorithms under fixed
correctness and completion contracts. Today, native-only mode completes some full protocol proofs.
General simultaneous AC unification, normalization and variant generation are still in progress.

## Run the experimental backend

The native link supports host builds on x86_64 GNU Linux. Use elan/Lake, a C toolchain and GNU `ar`,
`nm` and `objcopy`. The package pins the Lean version. [Toolchain](lean-toolchain)

From the repository root, build and run a proof that needs a witness shared across two substitution
images.

```sh
cargo build --release --features lean-unification
target/release/tamarin-rs --algebra-backend=native-only --prove crates/tamarin-prover/tests/fixtures/native_shared_offset.spthy
```

| Backend | Behavior |
| --- | --- |
| `maude` | Default without the feature. Uses the existing Rust fast paths and starts Maude. |
| `hybrid` | Default with the feature. Uses supported Lean operations and delegates other queries to Maude. |
| `native-only` | Supports library, batch and variants requests. Skips all Maude discovery and subprocesses. Unsupported queries and native failures produce errors. Interactive mode and the installation self-test currently reject this setting. |

A native-only failure is shared across session handles. Batch checks the session before publishing
output. Library callers that recover from algebra errors must likewise call
`MaudeHandle::check_backend_status` before using their results. Native-only requires
`TAM_RS_NO_LEAN_UNIFY`, `TAM_RS_VERIFY_LEAN_UNIFY` and `TAM_RS_VERIFY_REDUCE_NF` to be unset.
[Backend selection](../crates/tamarin-term/src/algebra_backend.rs) ·
[No-Maude CLI tests](../crates/tamarin-prover/tests/native_backend.rs)

## What an implementation must prove

Ordinary unification operates modulo the declared free, binary commutative (C) and
associative-commutative (AC) symbols, collectively called B. Pure AC preserves multiplicities and
has no unit. Additional equations such as XOR cancellation participate in rewriting and variants.
[Algebra](Tamarin/Algebra.lean) · [Rewriting modulo B](Tamarin/Rewriting.lean)

- **Unification.** Every returned substitution must solve all the equations. Every sorted solution,
  including a nonground one, must factor through a returned answer using one shared substitution on
  all observed variables. A complete empty set proves the conjunction impossible. Unsupported input,
  interruption and resource exhaustion are separate outcomes. Each export also has a completion
  obligation on its advertised domain. [Unification contract](Tamarin/Unification.lean) ·
  [Whole-problem contract](Tamarin/WholeContract.lean)
- **Matching.** Only the designated pattern variables may bind. Each match preserves the rigid
  subject, and one substitution accounts for every occurrence across the query.
  [Matching contract](Tamarin/Matching.lean)
- **Reduction and variants.** A normal form must be reachable and globally irreducible modulo B. For
  variants, a single substitution must explain the normalized values of the entire query tuple.
  Where Rust reconstructs values by normalizing again, Lean also requires that those values are
  recoverable. A finite rule table alone gives no guarantee of termination, confluence or finitely
  many variants. [Rewriting and variants](Tamarin/Rewriting.lean) ·
  [Reconstruction](Tamarin/VariantReconstruction.lean)

**For an optimization**, change the candidate and its proof. CI checks the actual exported functions
against their contracts, audits dependencies and export names, rejects unchecked overrides, and
rechecks the compiled Lean environment. Local builds compile the runtime and allow unproved
experiments. Require the `lean-spec` check in branch protection to enforce this before merge.
The graph completion contract reads packets through the fixed `TamarinWire.lean` definition.
An optimizer can replace the executable decoder without changing which packets require answers.
Changes to the semantic contract, wire format or acceptance harness need separate review.
[Runtime candidates](TamarinRuntime/) · [Exports](TamarinRuntime.lean) ·
[Proof obligations and audit](TamarinCI.lean) · [Mutation tests](Tests/check_audit.py)

## What crosses the Rust–Lean boundary

For native-only ordinary unification, Rust first submits the original conjunction before factoring.
It sends declarations for the symbols used in the query, a shared graph of numeric term rows, and
pairs of equation roots. One AC row holds references to all its children, including repeated
occurrences. Lean checks arities, child sorts and backward references. The graph export decides
identity and closed clashes. For homogeneous AC queries, Lean counts occurrences in those same
equation roots and returns witness slots per variable per answer. Every reference to a shared
child contributes its full multiplicity. For residual worklist equations, Rust sends the column ID
of each operand occurrence and retains the corresponding terms locally. Lean validates and counts
the IDs. Rust reconciles every returned arm with the original operands and pending equations
before reporting a complete result.
For an operand query of 2–64 equations, Lean selects row indices using the original
pairs of root IDs. It discards identities and keeps one occurrence of each remaining
equation up to symmetry. A second pass compares equalities inside a shared free or AC context
and selects the original rows. The residual solver repeats row selection when decomposition
exposes another duplicate. Variables occurring solely in discarded rows still get an
image in every answer. In one 23-equation GDH query, this exposes a three-factor
equation and its image under a shared context. All 20 unifiers agree with Maude up
to fresh naming. [Row selection and caller projection](Tamarin/OperandRefinement.lean) ·
[Selection under shared contexts](Tamarin/ContextRowSelection.lean)

Equations outside the matrix stay in the residual worklist. For a variable equation, Rust sends the selected variable’s ID, the opposite
root kind, the two root sorts and the opposite term’s variable IDs. Lean derives the occurs check
and chooses a sorted binding, identity or clash. For a rigid pair, Rust sends each root’s kind and symbol ID with its ordered
immediate-child IDs. Lean checks the two rows, including multiplicities, and selects identity,
clash, free decomposition, C alignment or AC cancellation. When cancellation and ordinary
bindings leave open AC equations, Rust batches equations at one head and calls the same
homogeneous solver through the operand export. It reserves names locally from the original query,
pending terms and accumulated bindings, including witnesses confined to another variable’s image.
[Rigid-step worklist proof](Tamarin/ResidualRigidWorklist.lean) · [Variable-step contract](Tamarin/ResidualVariable.lean) · [Lazy binding refinement](Tamarin/ResidualVariableWorklist.lean) ·
[Residual action contract](Tamarin/Residual.lean) · [Worklist semantics](Tamarin/ResidualSearch.lean) ·
[Rust encoder](../crates/tamarin-term/src/lean_unification/whole.rs) ·
[Fixed graph wire format](TamarinWire.lean) · [Flat-row proof](Tamarin/WholeLayout.lean) ·
[C bridge](../crates/tamarin-term/native/lean_unification.c)

Rust retains full term identities and concrete caller names. For witness-bearing answers, every
occurrence of a slot in an answer must receive the same fresh name. Distinct live slots must receive
distinct names of their declared sorts, disjoint from the caller’s scope. Rust may reorder C or AC
children after renaming. The projection theorem permits this reordering modulo B, requires exact
identity outside the original domain and allows identical projected answers to be returned once. Other answers can reuse
slot numbers. Rust’s substitution adapter checks that a uniform index shift fits, using gaps in the
caller’s scope when necessary. The whole-problem export takes no freshness argument.
[Caller freshening theorem](Tamarin/CallerFreshening.lean) ·
[Rust allocator](../crates/tamarin-term/src/subst_vfresh.rs)

On the factored matrix path, Rust proposes a substitution θ and residual equations. Composing θ
with any residual solution must solve the original equations. Every original solution ρ must
also solve the residual and agree with ρ ∘ θ on every original variable. Lean proves these
properties by checking three root lists in one graph. The residual variable
IDs also index the matrix columns. Slot allocation reserves variables from all three lists.
If the original equations do not directly justify the proposed bindings, the checker replays
single bindings, exposes matching free heads and compares the result modulo C/AC. Exhausting
the replay budget defers the proposal. CI requires acceptance for the direct sorted-binding
fragment and a chain whose second elimination specializes the first binding.
[Factoring laws](Tamarin/FactoredUnification.lean) · [Checker](TamarinRuntime/FactorCheck.lean) · [Guaranteed fragment](Tamarin/FactorAdmission.lean)

For completed homogeneous answers, Lean tags each row with its column and renumbers witness slots
in first-use order across all arms. Projection succeeds even for a complete clash (zero arms).
Rust assigns the ordinals unused local indices. On the checked factored path it composes the
residual answer with θ and writes one binding per original variable. This includes identities so
a variable shared with another image stays shared when the caller freshens that arm. Lean proves
that interpreting the tagged packet, composing and opening this table gives a complete set on
the original equations for any valid caller allocation. The proof allows AC factors in any order.
[Tagged packet semantics](Tamarin/ProjectedBindings.lean) · [Local allocation](Tamarin/OrdinalAllocation.lean) ·
[Caller opening theorem](Tamarin/DenseOpening.lean)

Rust still supplies the graph and column-to-variable mapping and implements the modeled binding
operations. Other paths can still trust Rust free factoring, including early failures. The residual
worklist, caches, C bridge and Lean toolchain also remain trusted.
[Graph-to-matrix refinement](Tamarin/GraphMatrixRefinement.lean) · [Joint contract](Tamarin/GraphUnification.lean)

CI compares proof runs against Maude because branch order and redundant instances can affect
Tamarin’s proof search even when two answer sets cover the same solutions.
[Reference encoding](Tamarin/TermEncoding.lean) ·
[Fresh substitution representation](Tamarin/FreshSubstitution.lean) ·
[Proof comparisons](../crates/tamarin-prover/tests/lean_unification.rs)

## Coverage and remaining work

The replacement targets four algebra commands. The upstream Haskell process adapter emits
`unify in MSG`, `match in MSG`, `reduce` and `get variants in MSG`. Rust emits the same
four. Existence checks project the answers from unification or matching. Restriction
matching can first make caller variables rigid. Rule closure packs terms into a single
variant request so that all positions share a substitution. Installation probes and module
initialization are separate from these algebra operations.
[Upstream command builders](../tamarin-prover/lib/term/src/Term/Maude/Process.hs#L194) ·
[Rust adapter](../crates/tamarin-term/src/maude_proc.rs) · [Packed rule queries](../crates/tamarin-theory/src/tools/rule_variants.rs#L125)

The input domain comes from the declarations and equations emitted for the active signature.
It includes the DH, bilinear pairing, multiset, natural-number and XOR operators, user-declared
free and AC operators, and their permitted combinations. The rule table combines user-supplied
rules with the enabled builtin equations. An ordinary unification or matching query uses the
declared C/AC axioms. Reduction and variants also use the active rewrite equations.
[Rust module printer](../crates/tamarin-term/src/maude_print.rs#L344) ·
[Active equations](../crates/tamarin-term/src/maude_sig.rs#L285) ·
[Upstream signature](../tamarin-prover/lib/term/src/Term/Maude/Signature.hs#L187)

| Operation | Native coverage today | Next milestone |
| --- | --- | --- |
| Free and commutative unification | Free factoring, binary C orientations, identity modulo B and ground clashes. On the residual worklist, Lean compares rigid heads and child IDs, checks variable bindings, sorts and occurrences, and justifies free decomposition and C branching against the whole pending conjunction. | Verify operand interning and the driver’s complete traversal of every live branch. |
| Simultaneous AC unification | Lean checks free factors, counts original variables or compound operand occurrences, and projects matrix answers. Nested residuals preserve sharing across C splits and AC operators. Ground matches constrain other equations. Subtracting two rows can expose a rigid factor-count clash. An indivisible occurrence can split a residual product even with several open variables on either side. | Verify Rust’s worklist transitions and operand interning against the term-level refinement. Extend branching to further open constraints. |
| Directional matching | Free, binary C and AC constructors may nest. Sorted bindings are shared across equations, including supported source node bindings. Native-only keeps open subject variables rigid and can refute repeated AC variables by counting remaining factors before partition search. | Admit more query roots and establish first-match compatibility for ambiguous source queries. |
| Reduction | Pair projections, selected constructor rules, AC unit and cancellation, DH power towers and signed exponent products. Native-only lifts supported reductions through any declared free symbol absent from the active rule heads. At binary AC roots it can instantiate the RHS when every match yields the same normal value. | Extend positive rewriting to proper AC subproducts and multi-step results at active heads. |
| Variants | Native-only joins positional destructors, flat XORs of Fresh variables and received-base DH powers on shared inputs. It specializes binary AC unit/cancellation families and positional destructor families to stable caller operands, including shared variables and constructor terms. Cancellation also supports two distinct Fresh variables and a Msg variable. Packed observations can include closed AC reductions with a unique normal value and free constructors around uniformly reducible terms. | Lift variant families through free constructors and compose them with outer operations when operands can narrow. Extend narrowing to arbitrary active equations, DH to unrestricted exponents, and ordering compatibility to joined answers in hybrid mode. |

Run the generated coverage test from the repository root.

```sh
cargo test --profile ci -p tamarin-term --features lean-unification --test spec_coverage -- --nocapture
```

Lean generates sorted terms through five syntax nodes for two signatures, plain AC with a
free hash and XOR with the same hash. The test exercises all four public operations,
including shared captures in conjunctions and packed variant observations. Lean marks
mandatory cases from constructor normality, incompatible matching heads and ground AC
multiset equality. CI fails if native-only defers one of those cases or returns an answer
that contradicts the expectation. Every reduction in the bounded grammar must complete.
The test checks that wrapping a term in hash wraps its normal form in the same hash.
This follows from the [free constructor reduction theorem](Tamarin/ConstructorReduction.lean).
Packed queries consisting of ground or constructor-only slots in these two presentations must
admit the identity substitution. A ground slot may rewrite before its value is reconstructed.
The [observation proof](Tamarin/ObservationRepresentative.lean) requires a unique normal value
modulo C/AC for that slot. Other slots may still constrain shared variables.
Binary cancellation observations with constructor-only operands are also mandatory in the
bounded tuples alongside other such observations or identity slots.
Exploratory cases can gain coverage freely. The report
prints the smallest generated deferral by syntax size for each theory and operation.
Setting `MAUDE_PATH` also replays those witnesses against an independent Maude handle.
The report counts syntactic requests in this bounded grammar. Protocol regressions
separately exercise ordering and proof search.
[Lean generator and expectations](Tests/NativeCoverage.lean) ·
[Public API check](../crates/tamarin-term/tests/spec_coverage.rs)

For flat directional matching, a singleton image retains the literal’s sort and a product takes
the AC operator’s result sort. Lean proves exact coverage after this sort check. In `x+x+y`
against `a+a+b+c`, a Fresh variable `x` can bind a Fresh `a` and a Msg variable `y` can bind
`b+c`. Rust sends one sort word per distinct variable and literal only when a variable has a
narrower sort than the operator. [Sorted matcher refinement](Tamarin/SortedMatchRefinement.lean)

Tamarin reads each directional substitution in variable order, following the upstream map
representation. A unique supported match stays native regardless of its number of bindings.
Native-only sorts distinct alternatives lexicographically by their binding lists after restoring
the caller’s variables. Hybrid existence checks also stay native on supported queries.
Source refinement chooses the first alternative, so ordered hybrid calls use Maude for newly
covered ambiguous cases. Lean proves that two complete matchers agree on the least value of
any ordered key that respects equality modulo the axioms on the pattern variables. Adopting
such a selection rule in a caller also requires checking its effect on proof search.
[Order and side-equation proofs](Tamarin/MatchOrder.lean) · [Upstream source selection](../tamarin-prover/lib/theory/src/Theory/Constraint/Solver/Sources.hs#L279)

If every subject is ground, every ordinary solution has ground images on the pattern variables.
The C/AC axioms preserve variable occurrences, so exact matching follows from a complete
ordinary unifier restricted to the original domain. Native-only uses this for closed comparisons
interleaved with variable captures and restores the caller’s rigid variables afterward. If a capture
shares a variable with another pattern, native-only substitutes its ground image
before enumerating AC partitions and retains the binding in every answer. This
immediately rules out `x+y = 9a, x = 10a`, where `na` denotes `n` copies of `a`.
[Ground-subject proof](Tamarin/Matching.lean) · [Closed comparisons](Tamarin/MatchGroundGuards.lean)

For distinct atoms, matching `H(x+y)+x` against `H(a+b+c)+a+b` forces
`x=a+b, y=c`. At each AC head the matcher flattens occurrences of that symbol and cancels
closed factors with multiplicity. The linked selector admits up to 64 remaining subject
occurrences and 4,096 selections. Before enumerating partitions for a repeated variable,
Lean checks that some residual factor occurs at least as often as that variable. For example,
`x+x+y` cannot match nine distinct rigid factors. If only variables remain, the same check
can refute a match beyond the selector's width limit. CI permits a stronger guard if it
proves every rejected residual has no match and still rejects the required multiplicity
failures. [Guard contract](Tamarin/CollectorMultiplicityMatching.lean)

Exhausting the shared 100,000-unit open-search budget defers the entire query.
Lean relates completed selections, partitions and C alignments to the original matching
equation. Rust prepares their inputs, traverses alternatives and reconstructs substitutions.
[Recursive matching](Tamarin/RecursiveACMatch.lean) · [Canonical representatives](Tamarin/CanonicalTree.lean) · [Restriction proof fixture](../crates/tamarin-prover/tests/fixtures/native_nested_ac_guard.spthy)

For a single AC operator and variables of its result sort, Lean proves that every sorted solution
of the simultaneous equations factors through one answer and one shared substitution. Any basis
spanning all nonnegative solutions suffices. CI checks the actual numeric export, including its
completion domain. A nonzero coefficient determines one coordinate after the others are chosen.
The budget allows 16,384 assignments to the remaining coordinates and retains separate limits for
intermediate candidates and output. For example, `11x = 13y` checks 352 assignments and returns one
shared witness, repeated 13 times in `x` and 11 times in `y`. [Enumeration proof](Tamarin/ACPlane.lean) · [Factorization proof](Tamarin/ACBasisComplete.lean) ·
[Packet contract](Tamarin/HomogeneousContract.lean) · [Executable](TamarinRuntime/Homogeneous.lean)

A bit mask on each suffix records the coordinates its generators can still cover. The selector
stops a branch when those bits and the already covered bits leave a coordinate missing. Lean proves
equality with exhaustive enumeration, including answer order. On a replay of 568 YubiKey
unification requests, 557 reached selection after skipping identities. Both selectors produced
the same 723 arms. With bases prepared in advance, median selection and packet construction
fell from 3.00 to 2.58 ms per replay across six batches of 120 passes. Through the linked C shim, the full 557-request replay took a median 493 ms across six runs.
Sharing basis coordinates cut one captured matrix from 81.9 s to 0.63 ms. [Selection proof](Tamarin/ACCoverage.lean) ·
[YubiKey model](../tamarin-prover/examples/csf26-ac/fast/Yubikey_multiset.spthy)

The YubiKey multiset model completes in native-only mode with the same source cases and six proof
trees as Maude. When generating a destructor rule, Tamarin needs the instantiated arguments and
one conclusion. The native path returns both in one answer with shared variables. The theorem
covers a single active variable-result rule with constructor patterns, including nested C/AC and
repeated variables. Free factoring can also expose a pure AC system that the checked matrix path can solve.
In five warmed, alternating single-worker runs of this proof in the optimized `ci` profile,
median wall time was 2.02 s with Rust counting operands and 2.11 s with verified graph counting.
[Observed application proof](Tamarin/ObservedNarrowing.lean) · [Corpus regression](../crates/tamarin-prover/tests/lean_unification.rs)

Independent repeated observations remain a separate variant query. For
`[x, unionUD(x), unionUD(x)]`, Maude prints distinct factors in the split arm. When `x = a+b`,
both projections can also yield `a`. The Lean audit proves that Maude’s two printed arms do not
cover this tuple under the general variant contract. [Counterexample](Tests/CorrelatedVariantsAudit.lean)

The operand lifting proof covers arbitrary sorted terms. For example, in
`x + f(y) = z + f(w)`, one arm equates `x` with `z` and `y` with `w`. The two exchange arms
keep `y` and `w` independent. A single substitution must reconcile every column and every equation
in an arm. For a nested call, Lean derives the matrix from the transmitted IDs and interprets
each returned column tag as its corresponding term. The union of these branches has exactly
the parent state’s solutions on all observed variables, including earlier bindings.
When a matrix search defers, native-only can split on a supported ground-sided AC equation,
including one exposed under a constructor. Each match becomes binding equations in the same
branch as the earlier bindings and all pending constraints.
For distinct atoms `a,b`, this gives the unique solution `x=b, y=a, z=a` for
`x+y=a+b, x+a=z+b`. A completed empty match closes the branch.
[Operand batch proof](Tamarin/OperandBatch.lean) · [Tagged residuals](Tamarin/ProjectedOperands.lean) ·
[Ground match split](Tamarin/GroundMatchBranch.lean) ·
[Native adapter](../crates/tamarin-term/src/lean_unification/operands.rs) ·
[Maude AC unifier](https://github.com/maude-lang/Maude/blob/eee00f5b0bea3a7da2b9e9f5bf1e83ce3cd1fa9f/src/ACU_Theory/ACU_UnificationSubproblem2.cc#L427-L573)

For `X + A = Y + B₁ + … + Bₙ` with indivisible factors, the pivot solver tries each
occurrence that can equal `A`. The remaining alternatives bind `Y` to `A` or to `A + W`
with a nonempty remainder shared with `X`. The linked Lean candidate emits equations for
these alternatives when the matrix and ground match paths defer. Up to 32 opposing factors
are supported. On the residual worklist, the more general split selects one indivisible
factor `A` from either side and one of up to 64 opposing occurrences `B`. Either
`B = A`, or `B = A + W` for a nonempty remainder `W` which also occurs on the other
side of the remaining equation. All other equations and earlier bindings constrain
both branches. Rust sends the linked selector the occurrence count and retains the terms.
[Residual split proof](Tamarin/ACOwnerPivot.lean) · [Pivot proof](Tamarin/ACPivot.lean) · [Packet interpretation](Tamarin/ACPivotDecode.lean) · [Row subtraction](Tamarin/ACRowElimination.lean)

Runtime search is bounded. The whole-problem encoder has size and depth limits, the C worklist caps
work items and answers, and the flat matcher limits candidate assignments and joins. The residual solver charges each occurrence
of a substituted term before building the result, including substitutions into earlier bindings.
Branches share these charges, a C orientation budget and up to 64 additional matrix calls per query.
Within that query, repeated matrix inputs reuse Lean's numeric packet, including a deferral.
Rust decodes it again using the current symbol and reserved names. The packet cache retains at
most 65,536 words of keys and results. DH reduction can check every subgroup of a product with up
to ten factors. Larger products can finish through a whole-product rewrite or an irreducibility
check. A search that exhausts its budget defers the entire query. In hybrid mode it can fall
back to Maude. Native-only reports an error if its other paths cannot
complete the query. The exact supported shapes and boundary cases are executable in the native-only
test suite. [Native operation tests](../crates/tamarin-term/tests/native_backend.rs)

Full native proofs have matched Maude for the upstream TLS handshake, NSLPK3, NSPK3, multiset
counter, number-subterm examples and several XOR examples. In `xor2`, `a XOR b` and `b XOR c`
share a Fresh input. The four variants account for neither pair cancelling, either pair
cancelling, or all three inputs coinciding. The three-edge triangle in `xor3` gives five variants,
and the four-edge cycle in `xor-basic` gives twelve. All three reproduce Maude’s source cases
and complete proofs. The wider XORs in `xor4` and `xor5` give 16 and 28 joint variants.
Native-only reproduces their 11- and 16-step proofs and all three proofs in `testConstructor`.

For a flat XOR of Fresh operands, Lean selects the leaves with odd multiplicity. For variant
generation, it enumerates disjoint pairs among the remaining variables. A pair shares a
Fresh witness, and each unpaired variable survives in the output. Rust sorts and deduplicates
the decoded arms so callers can rely on their order regardless of how Lean enumerates them. The linked implementation
admits up to nine odd variables per observation (2,620 variants at nine). Reduction has
no matching-width limit. When several observations share variables, a joined row can be
discarded if another row specializes to every one of its images and output terms modulo AC.
This comparison preserves any redex created by the specialization. The matching kernel receives
only the number of odd variables. Rust supplies their identities and allocates witnesses.
[Normal forms](Tamarin/XorFlatNormal.lean) · [Variant completeness](Tamarin/XorFlatVariants.lean) · [Witness scope](Tamarin/XorFlatScope.lean) ·
[Row subsumption](Tamarin/VariantJoinSubsumption.lean)

The active-rule check also covers `Pub XOR Fresh` in the responder rule of `NSLPK3xor`.
Native-only reproduces Maude’s rule closure and ten refined source cases through
`R_1`. The same check applies to user-declared AC operators. If each operand remains one
factor under every sorted substitution, the backend tests all subbags of two or more
operand positions against the active left-hand sides. It uses ordinary sorted unification,
with separate variable scopes for the rule and caller. A live unifier or an unfinished
search blocks the identity conclusion. For concrete binary reduction, directional matching
binds only rule variables and checks both operand orders. Rules with embedded literal
names still have query-local wire identities. The generic rule matcher uses declared
nullary symbols for constants shared with a query.
[AC rule exclusion](Tamarin/ACUnifierExclusion.lean) · [Root reduction proof](Tamarin/ACRootReduction.lean) · [Native AC reducer](../crates/tamarin-term/src/lean_unification/constructor_variants/ac_root_reduce.rs)

For `I_2`, both variables in `Msg XOR Msg` can introduce new factors. Lean generates
the identity and nonidentity variants by splitting active rule factors across the two
variables, allowing a rule variable to expand into a product. Each row shares witnesses
between both inputs and the reduced value. The completeness proof partitions normalized
factors into shared, left-only and right-only sets. CI checks the exported family against
all seven possible shapes modulo AC. The dispatcher recognizes the three active equations
and their unit, including for a user-declared AC operator. An additional rule at that head
disables this path. [Row generator](TamarinRuntime/BinaryCancellation.lean) ·
[Classification](Tamarin/BinaryXorClassification.lean) · [Wire contract](Tamarin/BinaryCancellationPacket.lean)

Native-only completes all four proofs in `NSLPK3xor` with the same proof trees as Maude
and 11 refined source cases. Printed rule-variant order and witness names differ. During
proof search a variable can occur on both sides of an ordinary match. Lean models the
subject occurrence as a rigid atom of the same sort, while the pattern occurrence remains
bindable. Rust keeps the original subject terms in the bindings. At a commutative head,
equality across the two sides can eliminate an alignment only for a ground common child.
[Matching refinement](Tamarin/RigidSubject.lean) · [Protocol regression](../crates/tamarin-prover/tests/lean_unification.rs)

The upstream `features/xor/CRxor` model now runs entirely in native-only mode. For
its ternary query, coincident Fresh images cancel and leave the message unchanged.
For distinct Fresh images, the message may contain either, both or neither, with or
without other factors. These nine variants share witnesses across the input images
and the normal value. CI checks all nine for any admitted cancellation presentation
and allows the executable to reorder or repeat rows. The Rust oracle tests exercise
both built-in XOR and a user-declared operator. [Classification](Tamarin/MixedCancellationClassification.lean) ·
[Packet contract](Tamarin/MixedCancellationPacket.lean) · [Joined observations](Tamarin/MixedCancellationJoined.lean)

Both the built-in presentation and the user-declared `csf26-ac/fast/CRxor` run
without Maude. For each, native-only matches Maude's precomputation output (seven
raw and seven refined cases) and all three lemma verdicts at 364, 11 and 10
steps. Four proof leaves print a different local timepoint index.
`CH07` still defers during rule closure. Its first variant query includes a cancellation
sum inside a hash, then uses that hash twice inside another sum.
For other AC theories, the narrowing specification shows how complete ordinary
unifiers lift rewrites on proper subproducts and states sufficient conditions for a
finite search to cover all reachable normal forms. An executable general search remains
open. [AC narrowing](Tamarin/RootNarrowing.lean) · [Completeness conditions](Tamarin/NarrowingFrontier.lean)

Broader deployment still requires checking the Rust representation against its Lean model
and carrying native-only failure handling through interactive proof publication. The live
cancellation theorem assumes a well-formed active equation table. Rust checks the three
equations at the cancellation head and checks the declared unit. Library callers that
construct a signature by hand still supply well-formed equations at unrelated heads.
[Corpus regressions](../crates/tamarin-prover/tests/lean_unification.rs) ·
[Specification counterexamples](Tests/SpecAudit.lean)

The upstream DH message-deduction example uses a single variant query containing
`x`, `y`, `(g^x)^y` and `inv(y)`, where both exponents are Fresh. The active equations
give the normal power `g^(x*y)` for every normalized substitution. Rust can therefore
use the identity substitution for the whole tuple and reconstruct its values by reduction.
For a received message `Y`, Lean classifies every normalized input to `Y^r` into seven
branches when the exponent remains a single positive factor under normalized substitution.
This includes Fresh variables and stable constructor terms such as `hash(pair(a,b))`.
Signed factor counts establish uniqueness modulo AC. Rust checks the active DH equations,
reads the base images directly from Lean and reconstructs values by reduction. CAV13’s DH
example, SignedDH and STS-MAC complete in native-only mode.
[Power variants](Tamarin/DHPeerComplete.lean) · [Executable contract](Tamarin/DHPeerPrograms.lean) · [Product uniqueness](Tamarin/DHProductUnique.lean)

Native-only combines local variant families by unifying their images of shared inputs.
It reopens witnesses apart and checks that all instantiated images and predicted values
are still normal. A proved redex eliminates that row. An unresolved live row or the
4,096-pair search limit defers the whole query. The join theorem applies to any complete
local families and ordinary unifiers. A leaf sees only its own application. Before inserting
identity images for other tuple variables, Rust renames the leaf’s images and normal value
together to avoid capturing an unrelated input. Lean proves this extension preserves every
normalized assignment. Two independent projections `fst(x), snd(y)` yield four variants,
while `fst(x), snd(x)` yield two. A received DH power `Y^r` paired with `r XOR s` gives 14
variants in either observation order. Nested open projections such as `fst(snd(x))` and
the mixed tuple `fst(Y), Y^a, a XOR b` still defer. [Leaf extension](Tamarin/VariantJoinLeaf.lean) · [Native join](../crates/tamarin-term/src/lean_unification/constructor_variants/variant_join.rs)

A complete operation family on distinct formal arguments also serves calls with fixed terms,
narrower sorts, and repeated variables. Native-only unifies all actual operands with each
freshened row, retains normal joint instances, and projects back to the caller variables.
The adapter checks each surviving pair in both directions for subsumption of all inputs and
predicted outputs by one sorted match. Lean proves that empty match sets for those comparisons
imply pairwise irredundancy. The Rust loop that constructs the comparisons is part of the trust boundary. For example, `'a' XOR m` has four variants, and `m XOR m` has one.
The specialization theorem works for any arity and rewrite presentation. Its operand
hypothesis requires normality under every normalized substitution. A nested operation that
can narrow needs its own variant family. [Specialization and uniqueness](Tamarin/VariantSpecialization.lean) ·
[Row subsumption](Tamarin/VariantJoinSubsumption.lean)

In both upstream
NAXOS examples, `Y^r`, `Y^h` and `Z^h` with `h = hash(pair(a,r))` yield 105 joint
variants. Native-only completes source precomputation with nine rules and eleven refined
source cases. It reproduces Maude’s full `eCK_key_secrecy` proof in each model, with
134 steps for `csf12` and 136 for `ake/dh`. Native-only also reproduces the 15-step
falsification of `eCK_PFS_key_secrecy` in the separate `NAXOS_eCK_PFS` model. A tuple
can include a uniformly reducible tower such as `(g^a)^b` alongside a narrowing power
such as `Y^r`. Its original variables remain observable even if a reduction erases one.
All nine models in the upstream `ake/dh` directory have identical native and Maude source
precomputation output. Eight also reproduce Maude’s complete proof output. The remaining
model, `UM_one_pass_attack`, reaches a rigid-context match beyond the native work budget
during proof search. The first 354 proof states agree. All 20 rigid-context queries
captured from Maude across the two one-pass models agree on replay, but native search
builds a 65,544-node term at the next split. The source of that growth is still open.
Its sibling `UM_one_pass_fix` completes both proofs.
The general tuple join runs in native-only mode. Ordered hybrid queries outside the earlier supported families still use Maude.
In `experiments/A-GDH2`, a received base is raised to two Fresh exponents.
The linked Lean kernel receives just the factor count. It enumerates which occurrences
cancel in the old exponent, preserving multiplicity even if two factors coincide.
Both nested powers and products within a power are admitted. The eight-factor limit
bounds the current enumeration. The caller-level theorem covers every width for which
a candidate returns an answer. Two distinct factors give
15 variants, two identical factors give 11, and three distinct factors give 31.
Native-only reproduces the entire closed theory, including the rule with 2,401 joint
variants. Full source precomputation exceeded a three-minute native run. A smaller
received-base model verifies the tower identity and reachability through proof search.
[Tower caller proof](Tamarin/DHTowerCaller.lean) · [Normalization and grouping](Tamarin/DHTowerNormal.lean) · [Tower regression](../crates/tamarin-prover/tests/fixtures/native_positive_tower.spthy)

In `sp14/GDH`, a rule observes both `g^Y` and `(g^Y)^r`. The unrestricted Msg exponent
`Y` can be the unit or contain an inverse of the stable positive factor `r`. The linked
kernel returns six substitution templates without receiving either term. Lean proves
that one binding accounts for every occurrence, including bare `Y*r` and flat
`g^(Y*r)`. Rust checks admissibility and instantiates the templates on the original
terms. The fixed CI check evaluates the emitted packet inside Lean's kernel and accepts
reordered or repeated valid images. Rust removes duplicate answers. Opaque bases can
mention `Y`, including `hash(Y)` when the live theory has no rule at the hash root.
Native-only reproduces the closed theory and all 11 refined source cases.
The same closure and source comparison also passes on `sp14/STR` and `sp14/STR_signed`,
with 11 and 17 refined source cases respectively. The reference GDH precomputation sends 22 reductions, 22 unifications and 18 variant
queries. Native-only sends none. The two-party reachability run with `-D=executable2`
also reproduces the 87-step Maude proof tree at depth 12. At depth 14, proof search
chooses a different disjunction. Replaying with row selection disabled produces the
same divergence. Native-only finishes the depth-18 search with 3,973 steps, compared
with 4,428 for Maude. Both searches hit the depth bound. Both unbounded runs exceeded
150 seconds. At depth 20, both backends verify two-party reachability in 20 steps.
The printed proofs agree apart from one locally numbered split case. The native run
solves a 16-equation query with two coupled products and an equality repeated under
an inverse. All 84 substitutions agree with Maude up to witness naming and with an
independent enumeration of factor multiplicities. Repeating one of the Msg variables on the
right of the second product gives 24 distinct substitutions after projection. Replacing one position in the three product templates with another input of the same
sort gave 27 test cases. All matched Maude, including two families of 204. Equal flat-product answers can be recognized from the witness sorts and their occurrences
across every input image. [Witness incidence proof](Tamarin/FlatAnswerIncidence.lean)

For three-party reachability, both backends reach depth 20 with an incomplete result and exceed 150 seconds
at depth 24. A smaller regression proves reachability for both `Y = one` and `Y = inv(r)` in all three backends.
[Exponent caller proof](Tamarin/DHExponentCaller.lean) · [Exponent regression](../crates/tamarin-prover/tests/fixtures/native_shared_exponent.spthy)

[Join proof](Tamarin/VariantJoinFamily.lean) · [Normality filter](Tamarin/VariantJoinSelect.lean) · [Tuple reconstruction](Tamarin/VariantJoinPacked.lean) · [Corpus tests](../crates/tamarin-prover/tests/lean_unification.rs)

One depth-18 equation is `a*b*b*c = d*X`, with `a,b,c,d` of sort Fresh. A Fresh
image occupies one position. Choosing the position for `d` fixes the whole remainder
for `X`. The two occurrences of `b` give the same substitution, leaving three
distinct answers. The same linked selector works in either orientation, preserves
other equations sharing these variables, and takes only occurrence counts.
[Positional unification proof](Tamarin/OneOpenPivot.lean)

### Proposed cross-query reuse

Today each AC unification can reuse a numeric matrix packet across its own branches.
The packet disappears when the query finishes. Session-wide reuse is a later roadmap
item, pending measurement and design review.

1. **Measure the opportunity.** On GDH and the wider proof corpus, count repeated
   matrix inputs *between* queries, separately from hits within one query. Weight
   repetitions by measured kernel time and simulate byte limits. Compare the projected
   savings with lookup, copying and contention costs before choosing a cache size.
2. **Keep the solver pure.** Start with one bounded, in-memory cache per theory session
   for the homogeneous operand kernel. Key it by its full numeric input (width and ordered
   occurrence rows). Store completed, immutable packets of column tags and witness
   ordinals, including a completed empty family. Rebuild all terms and fresh names in
   the current caller. Only publish a packet after a successful complete return.
3. **Prove the invariant.** For every stored entry `(k, p)`, the linked pure kernel on
   `k` returns exactly `some p`. Prove that lookup, insertion and eviction preserve
   this property, and that a hit reproduces the packet, arm order and caller-visible
   result. Keep the existing query-local accounting. Charge a session-cache hit just
   as the corresponding local miss would have been charged, and check cancellation on hits. For the same inputs, work budget
   and cancellation observations, the result must be independent of cache history.
4. **Check the adapter.** Own the shared packet bytes in Rust and compare full keys
   on collisions. Run misses outside the cache lock. Concurrent insertions for one
   key must yield the same packet. Test cold, warm, evicted and concurrent runs with
   different caller scopes, cancellation and tight budgets. Compare whole-proof time,
   memory, verdicts and branch order before enabling reuse.

## Verification and measurement

From this directory, these commands recheck the compiled proofs, run the whole-query examples and
exercise the fixed contract against incorrect candidates.

```sh
lake build TamarinCI
lake env leanchecker TamarinCI
lake env lean Tests/WholeProblem.lean
lake env lean Tests/ACRowElimination.lean
lake env lean --run Tests/ACPivot.lean
lake env lean Tests/FactoredUnification.lean
lake env lean Tests/FactorReplay.lean
lake env lean Tests/GraphUnification.lean
lake env lean Tests/AnswerProjection.lean
lake env lean Tests/OperandCounts.lean
lake env lean Tests/OperandUnification.lean
lake env lean Tests/ProjectedOperands.lean
lake env lean Tests/SortedMatch.lean
lake env lean Tests/OpenMatchSelect.lean
lake env lean Tests/CompoundPartitions.lean
lake env lean Tests/OpenMatch.lean
lake env lean Tests/MatchOrder.lean
lake env lean Tests/NestedTreeMatch.lean
lake env lean Tests/CanonicalTree.lean
lake env lean Tests/RecursiveACMatch.lean
lake env lean Tests/StableDH.lean
lake env lean Tests/DHProductUnique.lean
lake env lean Tests/VariantJoin.lean
python3 Tests/check_audit.py
```

Run `lake env lean --run Tests/DHTower.lean` to check all emitted tower rows against
independent generators and small signed exponent assignments.
`lake env lean --run Tests/DHExponent.lean` replays shared exponents before and after
multiplication against integer addition on three independent atoms.
For an independent count-based stress test of flat matching, run
`lake env lean --run Tests/MatchingStress.lean`. CI also checks variable capture, missing branches,
malformed packets, interruption and counterexamples involving rewrite rules.
[Stress test](Tests/MatchingStress.lean) · [Specification audit](Tests/ExistingSpecAudit.lean) ·
[Full CI commands](../.github/workflows/ci.yml)

From the repository root, the first command tests native operations without a Maude binary. The
remaining commands use Maude as an oracle. Set `MAUDE_PATH` to its executable when needed.

```sh
cargo test --profile ci -p tamarin-term --features lean-unification --test native_backend
cargo test --profile ci -p tamarin-term --features lean-unification --lib native_oracle_
TAM_RS_VERIFY_LEAN_UNIFY=1 cargo test --profile ci -p tamarin-term --features lean-unification --lib -- --test-threads=1
cargo test --profile ci -p tamarin-prover --features lean-unification --test lean_unification --test native_backend
```

For performance work, unset the oracle and native-disable switches, then run the flat AC benchmark.
It checks answers against Maude and reports cold and warm query times including dispatch, encoding
and conversion.

```sh
cargo run --profile ci -p tamarin-term --features lean-unification --example lean_unification_bench -- 1000
```

The benchmark above measures the hybrid path. A separate native-only measurement used the same
32 distinct factors on both sides of one equation, with 500 calls per run and seven alternating
warmed runs in the optimized `ci` profile. Compact AC rows reduced the packet from 228 to 138
words, median Rust encoding from 9.94 to 7.17 µs, C input copying from 1.50 to 0.89 µs, and the
complete kernel call including encoding from 184 to 65 µs. Full native-only proof output matched
on `counter`, `xor` and `NumberSubtermTests`, with median elapsed times moving by less than 3%.
[Hybrid benchmark source](../crates/tamarin-term/examples/lean_unification_bench.rs)

On `ake/dh/NAXOS_eCK_PFS`, median elapsed time for the full proof was 4.12 s in
native-only mode and 3.43 s with Maude. Each measurement used five fresh processes
after a warm-up, with one worker. Both backends found the same 15-step trace.

On `experiments/A-GDH2`, generating the closed theory took a median of 1.15 s
native-only and 15.09 s with Maude across three fresh, single-worker runs per backend
after warm-up on the final build, during local verification. This measures rule variants
and theory closure, before source saturation.

On the captured 16-equation GDH query, native unification took about 0.35 s after
context selection and query-local packet reuse, down from 3.52 s with the initial
owner split. Maude took about 7 ms. These are medians of three calls per backend in
the optimized `ci` profile with a fresh handle per call, excluding handle startup.

On `sp14/GDH`, source precomputation took 1.25 s native-only and 1.32 s with Maude
(medians of seven alternating fresh single-worker runs after warm-up). The ranges
overlapped at 1.21–1.68 s and 1.20–1.60 s respectively.

The flat AC matcher prunes assignments using the minimum remaining number of subject
positions, weighted by variable multiplicity. On five supported matching workloads,
the compiled Lean kernel ran 2.27× to 14.14× faster than the previous candidate.
These are medians of seven 16-query batches, including packet conversion and excluding
Rust and FFI. [Matcher proof](Tamarin/FlatMatchCandidateProofs.lean)
