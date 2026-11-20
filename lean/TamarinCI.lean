import Tamarin
import Tamarin.ReductionSignatureExtension
import Tamarin.CheckedReductionPacket
import Tamarin.TableConfluence
import Tamarin.CheckedVariantsPacket
import Tamarin.TotalUnifyPacket
import Tamarin.TotalMatchPacket
import Tamarin.SignatureExtension
import Tamarin.MatchingSignatureExtension
import Tamarin.UnavailableSort
import Tamarin.VariantSortRestriction
import Tamarin.ACMatchPacket
import Tamarin.ACMatchAnswerPacket
import Tamarin.ACPagePacket
import Tamarin.ACSortedBagPacket
import Tamarin.TotalFreeVariants
import Tamarin.ProjectedRuleMatches
import Tamarin.ACMatchSortedBags
import Tamarin.ACBagAnswers
import Tamarin.ACBagSearch
import Lean

/-- The proof-only CI target also pins the total AC reference at its two
source-level interfaces. Neither obligation has a successful-run premise. -/
theorem Tamarin.referenceHomogeneous_correct {s : Tamarin.Signature} (f : s.ACSym)
    (rows : List Tamarin.ACSystem.Row) (sorted : ∀ v ∈ Tamarin.ACSystem.variables rows,
      v.sort = s.acSort f) (avoid : List Tamarin.Variable) :
    (Tamarin.Outcome.complete (Tamarin.ACSystem.Reference.solve f rows sorted avoid)).CorrectIn
      (Tamarin.ACSystem.problem f rows) avoid :=
  Tamarin.ACSystem.Reference.correct f rows sorted avoid

namespace Tamarin
/-- Mandatory completion on the actual entry point for every simultaneous
free/C/AC problem, including kind-level inputs and caller-reserved names. -/
theorem referenceMixed_total {s : Signature}
    [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (p : Problem s) (avoid : List Variable) :
    ∃ answers, MixedUnification.unify? p avoid = some answers ∧
      (Outcome.complete answers).CorrectIn p avoid :=
  ⟨_,rfl,MixedUnification.unify_correct rfl⟩

/-- Every representable, arity-correct query yields a fully decoded complete
family on its declared signature. Malformed input has a separate status. -/
theorem exportedTotalUnify_correct : TotalUnifyWire.Packet.Correct Executable.totalUnify :=
  TotalUnifyWire.Packet.correct

theorem exportedFactorRefutes_correct : TotalUnifyWire.RefutationCorrect Executable.factorRefutes :=
  FactorRefutation.correct

/-- Extra constructors available to the caller cannot restore a solution. -/
theorem exportedFactorRefutes_ambient {ds ns es} (hit : Executable.factorRefutes ds ns es = true) :
    ∃ d p, TotalUnifyWire.input ds ns es = some ⟨d,p⟩ ∧
      ∀ extra : Signature, ¬ (SignatureExtension.query extra p).Satisfiable := by
  obtain ⟨d,p,dec,unsat⟩ := exportedFactorRefutes_correct ds ns es hit
  have empty : (Outcome.complete []).CorrectIn p [] :=
    ⟨(complete_empty_iff _).mpr unsat, by simp [Outcome.answers], by simp [Outcome.answers]⟩
  exact ⟨d,p,dec,fun extra => (complete_empty_iff _).mp
    (SignatureExtension.correctIn extra p [] empty).mathematical⟩

/-- Forced operand equalities may expose a clash after free decomposition.
The verdict rules out the caller's original conjunction before the additions. -/
theorem exportedFactorRefutes_forced {ds ns es} {d : TotalUnifyWire.Dictionary}
    {p added : Problem d.sig} (decoded : TotalUnifyWire.input ds ns es = some ⟨d,added ++ p⟩)
    (forced : ACForcedEquations.Forced p added) (hit : Executable.factorRefutes ds ns es = true) :
    ¬ p.Satisfiable := by
  obtain ⟨_,_,dec,refuted⟩ := exportedFactorRefutes_correct ds ns es hit
  rw [decoded] at dec
  cases dec
  exact fun ⟨σ,sol⟩ => refuted ⟨σ,(forced.prepend.solutions σ).mp sol⟩

theorem exportedTotalMatch_correct : TotalMatchWire.Correct Executable.totalMatch :=
  TotalMatchWire.correct

/-- Exact matching coverage in the caller's entire signature, even when
only the declarations occurring in the terms crossed the wire. -/
theorem exportedTotalMatch_ambient {ds ns es d p} (ids)
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩) :
    ∃ answers, TotalUnifyWire.Packet.Decodes p (Executable.totalMatch ds ns es ids) answers ∧
      ∀ extra : Signature, Matching.Complete (SignatureExtension.query extra p) (TotalMatchWire.Bindable ids)
        (answers.map (SignatureExtension.liftSubst extra)) := by
  obtain ⟨answers,hp,ok⟩ := exportedTotalMatch_correct.valid _ _ _ _ _ _ decoded
  exact ⟨answers,hp,fun extra => SignatureExtension.matching extra p ok⟩

theorem exportedCheckedReduce_correct : CheckedReductionWire.Correct Executable.checkedReduce :=
  CheckedReductionWire.correct

theorem exportedCheckedVariants_correct : CheckedVariantsWire.Correct Executable.checkedVariants :=
  CheckedVariantsWire.correct

/-- Constructor definitions have a complete family for every valid tuple
over the ambient name universe, independent of any frontier or output budget. -/
theorem exportedDefinitionVariants_complete {ds ns es roots n d rs q}
    (h : TableWire.input ds ns es roots = some ⟨d,rs,q⟩)
    (cls : ConstantDefinitions.Presentation rs) (sorts : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) :
    CheckedVariantsWire.Decodes rs q (Executable.checkedVariants ds ns es roots n) :=
  exportedCheckedVariants_correct.definitions_complete _ _ _ _ _ _ _ _ h cls sorts

/-- Additional caller symbols cannot change the unique normal form of a
concrete request under a range-restricted active table. -/
theorem exportedCheckedReduce_ambient {ds ns es root n d t rs}
    (h : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (admitted : CheckedReductionWire.admitted rs t n)
    (bound : ReferenceReduction.Bound rs)
    (completes : CheckedReduction.run rs (CheckedReductionWire.fuel rs t n) t ≠ none) :
    ∃ u, CheckedReductionWire.Decodes d (Executable.checkedReduce ds ns es root n) u ∧
      ∀ extra : Signature, MaudeOperations.ReductionReply (Rewriting.ruleRoot (SignatureExtension.query extra rs))
        (SignatureExtension.embed extra t) (SignatureExtension.embed extra u) := by
  rcases exportedCheckedReduce_correct.valid _ _ _ _ _ _ _ _ h with ⟨u,packet,reply⟩ | ⟨_,_,_,stop⟩
  · exact ⟨u,packet,fun extra => SignatureExtension.reduction extra rs bound t u reply⟩
  · exact (stop.elim (fun bad => by simp [bad] at admitted) completes).elim

/-- A sorted table of constructor definitions must return a decodable unique
normal form on every input, independently of the host's fuel and work limits. -/
theorem exportedDefinitionReduce_ambient {ds ns es root n d t rs}
    (h : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (cls : ConstantDefinitions.Presentation rs)
    (typed : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) :
    ∃ u, CheckedReductionWire.Decodes d (Executable.checkedReduce ds ns es root n) u ∧
      ∀ extra : Signature, MaudeOperations.ReductionReply (Rewriting.ruleRoot (SignatureExtension.query extra rs))
        (SignatureExtension.embed extra t) (SignatureExtension.embed extra u) := by
  have sorted := (DefinitionCertificate.sorted_iff cls).mpr typed
  have ok := (ConstantDefinitions.accepts_iff rs).mpr cls
  rcases exportedCheckedReduce_correct.valid _ _ _ _ _ _ _ _ h with ⟨u,packet,reply⟩ | ⟨_,reject,_⟩
  · exact ⟨u,packet,fun extra => SignatureExtension.reduction extra rs (ConstantDefinitions.bound ok) t u reply⟩
  · simp [CheckedReductionWire.definitions,ok,sorted] at reject

/-- Constructor-pattern projections complete on every arity-correct observation,
including kind-level contexts and arbitrary extensions of the caller signature. -/
theorem exportedDestructorReduce_ambient {ds ns es root n d t rs}
    (h : TableWire.input ds ns es #[root] = some ⟨d,rs,[t]⟩) (cls : DestructorTable.Presentation rs)
    (typed : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) :
    ∃ u, CheckedReductionWire.Decodes d (Executable.checkedReduce ds ns es root n) u ∧
      ∀ extra : Signature, MaudeOperations.ReductionReply (Rewriting.ruleRoot (SignatureExtension.query extra rs))
        (SignatureExtension.embed extra t) (SignatureExtension.embed extra u) := by
  have sorted := cls.sorted_iff.mpr typed
  rcases exportedCheckedReduce_correct.valid _ _ _ _ _ _ _ _ h with ⟨u,packet,reply⟩ | ⟨_,_,reject,_⟩
  · exact ⟨u,packet,fun extra => SignatureExtension.reduction extra rs (TableDecrease.bound cls.decreasing) t u reply⟩
  · simp [CheckedReductionWire.destructors,(DestructorTable.accepts_iff rs).mpr cls,sorted] at reject

/-- Filtering witnesses of an unavailable sort preserves coverage on actual
module substitutions, including all the values of a packed query. -/
theorem checkedVariants_withoutNat {s : Signature} {R : Rewriting.Root s} {q rows}
    (reply : CheckedVariants.Reply R q rows) (ρ : Substitution s)
    (clean : ∀ v, Rewriting.Observed q v → UnavailableSort.marked .nat (ρ.image v) = false)
    (normal : Rewriting.Normalized R ρ) (values : List (Term s))
    (forms : Rewriting.Aligned (fun t u => Rewriting.NormalForm R (ρ.apply t) u) q values) :
    ∃ a ∈ rows.filter (VariantSortRestriction.allowed q), a.Covers R q ρ values :=
  VariantSortRestriction.complete_on_module reply.toVariantReply ρ clean normal values forms

/-- The active-table reference supplies all four operations. Its hypotheses
are properties of the presentation emitted by the caller. -/
def referenceActiveTable {s : Signature}
    [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (rules : List (Equation s)) (bound : ReferenceReduction.Bound rules)
    (canonical : MaudeOperations.CanonicalPresentation (Rewriting.ruleRoot rules))
    (finite : MaudeOperations.FiniteVariantProperty (Rewriting.ruleRoot rules)) :
    MaudeOperations.Reference s rules := TableNarrowing.reference bound canonical finite

/-- The packet dictionary may contain only the query's symbols. Every
representable query still covers caller solutions involving other symbols. -/
theorem exportedTotalUnify_ambient {ds ns es d p}
    (decoded : TotalUnifyWire.input ds ns es = some ⟨d,p⟩)
    (fits : TotalUnifyWire.Packet.Representable p ((MixedUnification.verified (s := d.sig)).solve p trivial [])) :
    ∃ answers, TotalUnifyWire.Packet.Decodes p (Executable.totalUnify ds ns es) answers ∧
      ∀ extra : Signature, (Outcome.complete (answers.map (SignatureExtension.liftSubst extra))).CorrectIn
        (SignatureExtension.query extra p) [] := by
  rcases exportedTotalUnify_correct.valid _ _ _ _ _ decoded with ⟨answers,hp,ok⟩ | ⟨_,bad⟩
  · exact ⟨answers,hp,fun extra => SignatureExtension.correctIn extra p [] ok⟩
  · exact (bad fits).elim

theorem referenceOperandSplit_correct {s : Signature} [DecidableEq s.ACSym] [DecidableEq (Term s)]
    (f : s.ACSym) (selected pending : Problem s) (hs : OperandBatch.Reference.SortedAt f selected)
    (observe avoid : List Variable) (bindings ρ : Substitution s) :
    Residual.Denotes (· ∈ observe) (selected ++ pending) bindings ρ ↔
      ∃ child ∈ OperandBatch.Reference.splitProblem f selected hs pending observe avoid bindings,
        Residual.Denotes (· ∈ observe) child bindings ρ :=
  OperandBatch.Reference.splitProblem_correct f selected hs pending _ (.refl _) observe avoid bindings ρ
end Tamarin

/-- Required CI witness for the actual exported functions, with a type owned
by the specification. Deleting or weakening a candidate theorem cannot remove
this obligation. Ordinary runtime builds do not import this module. -/
theorem Tamarin.exportedBackend_correct : Tamarin.FlatACBackend.Correct
    { equal := Tamarin.Executable.flatACEqual,
      residual := Tamarin.Executable.flatACResidual } :=
  Tamarin.CandidateProofs.correct

/-- Directional matching must have exact coverage. Pin the reused residual
export to that stronger contract as well as its unification contract. -/
theorem Tamarin.exportedMatching_correct {sig : Tamarin.Signature}
    (decode : UInt64 → sig.Atom) (v : Tamarin.Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64)
    (ht : tail.toList ≠ []) (hr : rhs.toList ≠ [])
    (h : Tamarin.Executable.flatACResidual tail rhs = (2 :: rest).toArray)
    (hs : Tamarin.HasSort (Tamarin.FlatAC.term f (rest.map decode)) v.sort) :
    Tamarin.Matching.Complete
      (Tamarin.FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode))
      (fun _ => True) [Tamarin.Substitution.binding v (Tamarin.FlatAC.term f (rest.map decode)) hs] :=
  Tamarin.Matching.residual_complete Tamarin.exportedBackend_correct decode v f tail rhs rest ht hr h hs

theorem Tamarin.exportedMatching_failure {sig : Tamarin.Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (v : Tamarin.Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (live : ∀ a ∈ tail.toList ++ rhs.toList, encode (decode a) = some a)
    (hr : rhs.toList ≠ [])
    (h : Tamarin.Executable.flatACResidual tail rhs = #[1]) :
    Tamarin.Matching.Complete
      (Tamarin.FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode))
      (fun _ => True) [] :=
  Tamarin.Matching.residual_failure Tamarin.exportedBackend_correct decode encode v f tail rhs live hr h

/-- A numeric success packet may describe a forced image of an incompatible
sort. The adapter's empty answer is complete for matching and unification. -/
theorem Tamarin.exportedResidual_wrongSort {sig : Tamarin.Signature}
    (decode : UInt64 → sig.Atom) (v : Tamarin.Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64)
    (ht : tail.toList ≠ []) (hr : rhs.toList ≠ [])
    (h : Tamarin.Executable.flatACResidual tail rhs = (2 :: rest).toArray)
    (wrong : ¬ Tamarin.Subsort (Tamarin.FlatAC.term f (rest.map decode)).rootSort v.sort) :
    let p := Tamarin.FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode)
    Tamarin.CompleteSet p [] ∧ Tamarin.Matching.Complete p (fun _ => True) [] := by
  have hc := Tamarin.Matching.residual_wrong_sort Tamarin.exportedBackend_correct
    decode v f tail rhs rest ht hr h wrong
  refine ⟨hc, Tamarin.Matching.of_ground_unification _ _ ?_ hc (by simp) (by simp)⟩
  intro e he
  obtain rfl := List.mem_singleton.mp he
  exact Tamarin.FlatAC.term_not_occurs f _ (by simpa using hr)

/-- Pin the actual multi-variable matching export to the complete row denotation. -/
theorem Tamarin.exportedFlatMatcher_correct (n : UInt64) (occ tail rhs : Array UInt64)
    (rows : List (List UInt64)) :
    rows ∈ (Tamarin.Executable.flatACMatch n occ tail rhs).toList.map (fun answer => answer.toList.map Array.toList) ↔
    rows.length = n.toNat ∧ (∀ row ∈ rows, row ≠ [] ∧ List.Sublist row rhs.toList) ∧
      (Tamarin.FlatMatchSearch.expand rows (occ.toList.map UInt64.toNat) ++ tail.toList).Perm rhs.toList :=
  Tamarin.FlatMatchCandidateProofs.exported n occ tail rhs rows

namespace Tamarin

theorem exportedACBagMatch_correct : Matching.ACMatchPacket.Correct Matching.ACBagSearch.Within
    Executable.acBagMatch :=
  Matching.ACMatchPacket.runWith_correct _ _ Matching.ACBagSearch.run_correct.exact
    Matching.ACBagSearch.run_correct.completes

theorem exportedACBagAnswers_correct : Matching.ACMatchPacket.FamilyCorrect Matching.ACBagAnswers.Within
    Executable.acBagAnswers :=
  Matching.ACMatchPacket.runAnswersWith_correct _ _ Matching.ACBagAnswers.run_correct.sound_complete
    Matching.ACBagAnswers.run_correct.shape Matching.ACBagAnswers.run_correct.completes

theorem exportedACBagPage_correct : Matching.ACPagePacket.Correct Executable.acBagPage :=
  Matching.ACPagePacket.run_correct

theorem exportedACBagTypedMatch_correct : Matching.ACSortedBagPacket.Correct Executable.acBagTypedMatch :=
  Matching.ACSortedBagPacket.runWith_correct _ Matching.ACSortedBagSearch.run_correct.exact
    Matching.ACSortedBagSearch.run_correct.completes

theorem exportedMatchSizeExcludes_correct :
    Matching.Prefilter.SizeExclusion Executable.matchSizeExcludes :=
  Matching.Prefilter.size_exclusion_correct

theorem exportedLinearACMatch_correct : Matching.LinearAC.Correct Executable.matchSizeExcludes :=
  Matching.LinearAC.correct

theorem exportedOperandRefine_correct : OperandRefinement.Correct Executable.operandRefine :=
  OperandRefinement.correct

theorem exportedOperandRefine_semantic : OperandRefinement.Semantic Executable.operandRefine :=
  OperandRefinement.semantic exportedOperandRefine_correct

theorem exportedOperandRefine_projected : OperandRefinement.Projected Executable.operandRefine :=
  OperandRefinement.projected exportedOperandRefine_semantic

theorem exportedACPivot_correct : ACPivot.Packet.Correct Executable.acPivot := ACPivot.Packet.correct

/-- Replacing a single equation by the complete family emitted at the ABI
preserves the complete-set contract on the caller’s entire conjunction. -/
theorem exportedACPivot_semantic {sig : Signature} (q : ACPivot.Query sig)
    {caller : Problem sig} (present : ACPivot.Presentation q caller)
    {size : UInt64} (width : size.toNat = q.operands.length) (bound : size.toNat ≤ 32)
    {rows : Array (Array UInt64)} (ran : Executable.acPivot size = some rows)
    (atom : AtomicACPair.Atomic q.f q.a) (each : ∀ b ∈ q.operands, AtomicACPair.Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (w : Variable) (hw : w.sort = sig.acSort q.f)
    (fresh : ¬ q.problem.Occurs w) (answers : Array UInt64 → List (Substitution sig))
    (branches : ∀ row ∈ rows, ∀ p, ACPivot.Packet.interpret q w row = some p → CompleteSet p (answers row)) :
    CompleteSet caller (rows.toList.flatMap answers) := by
  apply present.complete
  apply ACPivot.Packet.complete exportedACPivot_correct q width bound ran atom each sy w hw fresh answers
  intro c
  have nz : 0 < size.toNat := by simp [width, ACPivot.Query.operands]
  have spec := exportedACPivot_correct size
  simp only [nz, bound, and_self, ↓reduceIte] at spec
  obtain ⟨rs,hr,mem⟩ := spec
  obtain rfl := Option.some.inj (ran.symm.trans hr)
  rw [width] at mem
  have decoded := ACPivot.Packet.interpret_words q w (width ▸ bound) c
  exact ACPivot.Packet.interpreted_complete q w (width ▸ bound) c _ _ decoded
    (branches _ ((mem _).mpr ⟨c,rfl⟩) _ decoded)

/-- A bare local call may omit all unrelated input variables. Its whole
opened answer must avoid those keys before the caller adds their identities. -/
theorem variantJoinLeaf_complete : Rewriting.VariantJoin.LeafSemantic :=
  Rewriting.VariantJoin.leafSemantic

open Rewriting Rewriting.RootNarrowing in
theorem rootNarrowing_csu {s : Signature} {R : Root s} (p : Schema R) (q : Term s)
    (apart : ∀ w, p.lhs.Occurs w → ¬q.Occurs w) {rows} (csu : CompleteSet (p.problem q) rows)
    (ρ : Substitution s) (u : Term s) :
    (∀ μ ∈ rows, StepModulo R (μ.apply q) (μ.apply p.rhs)) ∧
    ((∃ τ : Substitution s, EquivB (ρ.apply q) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs)) ↔
      ∃ μ ∈ rows, Fits q ρ u μ (μ.apply p.rhs)) :=
  ⟨fun _ mem => p.replay q csu mem,p.lift_iff q apart csu ρ u⟩

open Rewriting Rewriting.RootNarrowing in
theorem acNarrowingCoversSubbag {s : Signature} [DecidableEq s.ACSym] {R : Root s} (p : Schema R)
    (q : Term s) (f : s.ACSym) (z : Variable) (sort : z.sort = s.acSort f) (fresh : ¬p.lhs.Occurs z)
    (apart : ∀ v, (p.extend f z).lhs.Occurs v → ¬q.Occurs v) {bare extended}
    (bc : CompleteSet (p.problem q) bare) (ec : CompleteSet ((p.extend f z).problem q) extended)
    (ρ τ : Substitution s) (typed : HasSort (ρ.apply q) (s.acSort f))
    (hit : DHProduct.Subbag f (τ.apply p.lhs) (ρ.apply q)) :
    ∃ u, StepModulo R (ρ.apply q) u ∧
      ((EquivB (ρ.apply q) (τ.apply p.lhs) ∧ EquivB u (τ.apply p.rhs) ∧
        ∃ μ ∈ bare, Fits q ρ u μ (μ.apply p.rhs)) ∨
       ∃ rest, EquivB (ρ.apply q) (.ac f (τ.apply p.lhs) rest) ∧ EquivB u (.ac f (τ.apply p.rhs) rest) ∧
         ∃ μ ∈ extended, Fits q ρ u μ (μ.apply (p.extend f z).rhs)) :=
  p.subbag_lift q f z sort fresh apart bc ec ρ τ typed hit

open Rewriting Rewriting.RootNarrowing in
theorem narrowingFrontier_complete {s : Signature} (rules : List (Equation s)) (t : Term s)
    (states kept : List (VariantJoin.Row s (VariantJoin.LocalKey t) Unit)) (answers : List (Variant s))
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (certificate : Certificate rules t states kept answers) : CompleteVariants (ruleRoot rules) [t] answers :=
  certificate.complete vars

open Rewriting Rewriting.ConstructorVariants in
theorem acPairUnifierExclusion_stable {s : Signature} (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (a b : Term s)
    (ha : AtomicACPair.Atomic f a) (hb : AtomicACPair.Atomic f b)
    (na : StableVariants.Stable (ruleRoot rules) a) (nb : StableVariants.Stable (ruleRoot rules) b)
    (closed : ∀ r ∈ rules, head r.lhs = .ac f →
      2 < (Cancellation.flatten f r.lhs).length ∨ ACUnifierExclusion.Refuted (.ac f a b) r.lhs) :
    StableVariants.Stable (ruleRoot rules) (.ac f a b) :=
  ACUnifierExclusion.pairStable rules apps f a b ha hb na nb closed

theorem exportedACSubgroupUnifierExclusion_stable :
    Rewriting.ACUnifierExclusion.StableSubgroups Executable.acSubgroups :=
  Rewriting.ACUnifierExclusion.stableSubgroups ACSubgroups.correct

open Rewriting Rewriting.ConstructorVariants Rewriting.ACUnifierExclusion Cancellation in
/-- The reducer supplies normality only at the current term. Every proper
subgroup comes from the same checked occurrence selector as stable queries. -/
theorem exportedACSubgroupUnifierExclusion_normal {s : Signature} [DecidableEq s.ACSym]
    (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (whole : Term s) {width : UInt64} {rows} (ran : Executable.acSubgroups width = some rows)
    (read : UInt64 → Term s) (piece : List UInt64 → Term s)
    (packed : Represents f whole (((List.range width.toNat).map Nat.toUInt64).map read))
    (children : ∀ i ∈ (List.range width.toNat).map Nat.toUInt64,
      flatten f (read i) = [classOf (read i)] ∧ Normal (ruleRoot rules) (read i))
    (parts : ∀ row : List UInt64, row.toArray ∈ rows → Represents f (piece row) (row.map read))
    (bucket : ∀ row : List UInt64, row.toArray ∈ rows → ∀ r ∈ rules, head r.lhs = .ac f →
      row.length < (flatten f r.lhs).length ∨ Refuted (piece row) r.lhs) :
    Normal (ruleRoot rules) whole := by
  simpa only [Substitution.apply_identity] using
    pointwiseSubgroups ACSubgroups.correct rules apps f whole ran read piece Substitution.identity
      packed (by simpa only [Substitution.apply_identity] using children) parts bucket

open Rewriting Rewriting.ConstructorVariants Rewriting.ACUnifierExclusion Cancellation in
theorem acPairUnifierExclusion_normal {s : Signature} (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (a b : Term s)
    (ha : flatten f a = [classOf a]) (hb : flatten f b = [classOf b])
    (na : Normal (ruleRoot rules) a) (nb : Normal (ruleRoot rules) b)
    (bucket : ∀ r ∈ rules, head r.lhs = .ac f →
      2 < (flatten f r.lhs).length ∨ Refuted (.ac f a b) r.lhs) :
    Normal (ruleRoot rules) (.ac f a b) := by
  simpa only [Substitution.apply_identity] using pairAt rules apps f a b Substitution.identity
    (by simpa using ha) (by simpa using hb) (by simpa using na) (by simpa using nb) bucket

theorem exportedJoinSelection_correct : Rewriting.VariantJoin.Select.Correct Executable.selectJoinedVariants :=
  Rewriting.VariantJoin.Select.correct

theorem exportedJoinSelection_semantic : Rewriting.VariantJoin.Select.Semantic Executable.selectJoinedVariants :=
  Rewriting.VariantJoin.Select.exact_call exportedJoinSelection_correct

theorem exportedDHExponentImages_correct : Rewriting.DHExponent.Packet.Correct (Executable.dhExponentImages ()) :=
  Rewriting.DHExponent.Packet.of_accepts (by decide +kernel)

/-- Each shared-exponent program refines the caller's simultaneous variant query. -/
theorem exportedDHExponentImages_complete : Rewriting.DHExponent.Caller.Semantic (Executable.dhExponentImages ()) :=
  Rewriting.DHExponent.Caller.certified exportedDHExponentImages_correct

theorem exportedDHTowerImages_correct : Rewriting.DHTower.Packet.Correct Executable.dhTowerImages :=
  Rewriting.DHTower.Packet.correct

theorem exportedDHTowerImages_semantic : Rewriting.DHTower.Packet.Semantic Executable.dhTowerImages :=
  Rewriting.DHTower.Packet.semantic exportedDHTowerImages_correct

/-- Every returned row decodes to the certified base. Reopening those rows
in the caller's scope gives complete, reconstructible variants of the tuple. -/
theorem exportedDHTowerImages_complete : Rewriting.DHTower.Caller.Semantic Executable.dhTowerImages :=
  Rewriting.DHTower.Caller.certified exportedDHTowerImages_correct

theorem exportedDHPeerImages_correct : Rewriting.DHPeer.Programs.Correct Executable.dhPeerImages :=
  Rewriting.DHPeer.Programs.candidate_correct

theorem exportedDHPeerImages_ordered : Rewriting.DHPeer.Programs.Ordered Executable.dhPeerImages :=
  Rewriting.DHPeer.Programs.candidate_ordered

/-- High-level guarantees for the base images produced by the linked function. -/
theorem exportedDHPeerImages_semantic : Rewriting.DHPeer.Programs.Semantic Executable.dhPeerImages :=
  Rewriting.DHPeer.Programs.certified exportedDHPeerImages_correct

/-- The same linked packet also certifies compound stable exponent factors. -/
theorem exportedDHPeerImages_factorSemantic : Rewriting.DHPeer.Programs.FactorSemantic Executable.dhPeerImages :=
  Rewriting.DHPeer.Programs.certifiedFactor exportedDHPeerImages_correct

theorem exportedSignedGraph_correct : SignedGraph.Correct Executable.signedGraphVariants ∧
    SignedGraph.Total Executable.signedGraphVariants :=
  ⟨SignedGraph.run_correct, SignedGraph.run_total⟩

theorem exportedReductionGraph_correct : ReductionGraph.Correct Executable.reductionGraph :=
  ReductionGraph.correct

theorem exportedReductionGraph_semantic : ReductionGraph.Semantic Executable.reductionGraph :=
  ReductionGraph.completed exportedReductionGraph_correct

theorem exportedACSubgroups_correct : ACSubgroups.Correct Executable.acSubgroups := ACSubgroups.correct

theorem exportedOpenMatchSelect_correct : OpenMatchSelect.Correct Executable.openMatchSelect :=
  OpenMatchSelect.run_correct

theorem exportedCollectorPossible_correct : CollectorMultiplicity.Admissible Executable.collectorPossible :=
  CollectorMultiplicity.of_correct CollectorMultiplicity.run_correct

theorem exportedOneOpenPivot_semantic : OneOpenPivot.Semantic Executable.openMatchSelect :=
  OneOpenPivot.semantic exportedOpenMatchSelect_correct

theorem exportedACOwnerPivot_semantic : ACOwnerPivot.Semantic Executable.openMatchSelect :=
  ACOwnerPivot.semantic exportedOpenMatchSelect_correct

theorem exportedOpenMatch_correct : OpenMatch.Correct Executable.openMatchSelect :=
  OpenMatch.correct exportedOpenMatchSelect_correct

theorem exportedCompoundPartitions_correct : CompoundPartitions.Correct Executable.flatACMatch :=
  CompoundPartitions.correct exportedFlatMatcher_correct

theorem exportedOpenMatchAdapter_correct :
    OpenMatchAdapter.Correct Executable.openMatchSelect Executable.flatACMatch :=
  OpenMatchAdapter.correct exportedOpenMatchSelect_correct exportedCompoundPartitions_correct

theorem exportedSortedACMatch_correct : SortedMatch.Correct Executable.sortedACMatch Executable.flatACMatch :=
  SortedMatch.run_correct _

theorem exportedSortedMatcher_semantic : SortedMatchRefinement.Correct Executable.sortedACMatch :=
  SortedMatchRefinement.correct exportedSortedACMatch_correct exportedFlatMatcher_correct

/-- Pin variable cancellation to the same equality/difference exports as flat
ground unification. A candidate may reorder the excess word occurrences. -/
theorem exportedCancellation_semantic {sig : Signature} (f : sig.ACSym)
    (σ : Substitution sig) (decode : UInt64 → Variable) (big small : Array UInt64)
    (rest : List UInt64) (left right : List (FlatMatching.Leaf sig))
    (hb : big.toList ≠ []) (hs : small.toList ≠ [])
    (packet : (rest = [] ∧ Executable.flatACEqual big small = 2) ∨
      Executable.flatACResidual small big = (2 :: rest).toArray) :
    let var : UInt64 → FlatMatching.Leaf sig := fun i => .inl (decode i)
    EquivB (σ.apply (FlatMatching.pattern f (big.toList.map var ++ left)))
      (σ.apply (FlatMatching.pattern f (small.toList.map var ++ right))) ↔
      ((rest.map var ++ left).flatMap (FlatMatching.parts f σ)).Perm
        (right.flatMap (FlatMatching.parts f σ)) := by
  apply FlatCancellation.cancel_variables
  · rcases packet with ⟨rfl, h⟩ | h
    · exact (exportedBackend_correct.equal_words big small hb hs).mp h
    · exact exportedBackend_correct.residual_difference small big rest h
  · simp [hb]
  · simp [hs]

theorem exportedCancelCommon_correct : CommonCancellation.Correct Executable.cancelCommon :=
  CancelCommonCandidateProofs.correct

theorem exportedLinearACMatch_packet : Matching.LinearAC.PacketCorrect Executable.cancelCommon
    Executable.matchSizeExcludes :=
  Matching.LinearAC.packet_correct exportedCancelCommon_correct exportedLinearACMatch_correct

theorem exportedACRowClash {sig : Signature} {pivot target : ACRowElimination.Row UInt64}
    {f : sig.ACSym} {get : UInt64 → Term sig} {p : Problem sig} {a b : Equation sig}
    (pa : a ∈ p) (pb : b ∈ p) (ra : ACRowElimination.Represents pivot f get a)
    (rb : ACRowElimination.Represents target f get b) (l r : List UInt64)
    (out : Executable.cancelCommon (target.lhs ++ pivot.rhs).toArray (target.rhs ++ pivot.lhs).toArray =
      #[l.toArray,r.toArray]) (atoms : ∀ i ∈ l ++ r, AtomicACPair.Atomic f (get i))
    (width : l.length ≠ r.length) : ¬ p.Satisfiable :=
  ACRowElimination.cancel_refutes exportedCancelCommon_correct pa pb ra rb l r out atoms width

/-- Pin the ABI entry to equivalence of the original and residual equations
after arbitrary instantiation, including substitutions into open compounds. -/
theorem exportedCancelCommon_semantic {sig : Signature} (decode : UInt64 → Term sig)
    (f : sig.ACSym) (lhs rhs : Array UInt64) :
    ∃ left right : List UInt64, Executable.cancelCommon lhs rhs = #[left.toArray, right.toArray] ∧
      ∀ σ, ACResidual.Holds f σ (lhs.toList.map decode) (rhs.toList.map decode) ↔
        ACResidual.Holds f σ (left.map decode) (right.map decode) :=
  ACResidual.run_correct exportedCancelCommon_correct decode f lhs rhs

theorem exportedSeededCancellation_correct : OpenMatch.SeededCancellationCorrect Executable.cancelCommon :=
  OpenMatch.seeded_correct exportedCancelCommon_correct

theorem exportedOpenMatchCancellation_correct : OpenMatchCancellation.Correct Executable.cancelCommon :=
  OpenMatchCancellation.correct exportedCancelCommon_correct

/-- Pin direct cancellation of closed free factors to exact directional
matching, including impossible and wrong-sort residuals. -/
theorem exportedCompoundMatching_correct {sig : Signature} (f : sig.ACSym)
    (v : Variable) (d : UInt64 → Term sig) (tail subject : Array UInt64) (s : Term sig)
    (decoded : ACRepresentation.decode f (subject.toList.map d) = some s)
    (free : ∀ i ∈ tail.toList ++ subject.toList, CompoundMatching.FreeGround (d i))
    (unique : ∀ i ∈ tail.toList, ∀ j ∈ subject.toList, d i = d j → i = j) :
    ∃ l r : List UInt64, Executable.cancelCommon tail subject = #[l.toArray, r.toArray] ∧
      CompoundMatching.AnswersCorrect [⟨ACRepresentation.fold f (.var v) (tail.toList.map d), s⟩] v
        (if l = [] then ACRepresentation.decode f (r.map d) else none) :=
  CompoundMatching.matching_correct exportedCancelCommon_correct f v d tail subject s decoded free unique

theorem exportedGroundDecision_correct :
    Rewriting.GroundVariantDecision.Correct Executable.groundVariant :=
  GroundVariantCandidateProofs.correct

theorem exportedRuleReduction_correct :
    Rewriting.RuleReduction.Correct Executable.reduceRuleSlot :=
  RuleReductionCandidateProofs.correct

theorem exportedRuleReduction_semantic {sig : Signature} (rules : List (Equation sig))
    (d : sig.FreeSym) (p ys : Fin (sig.arity d) → Term sig)
    (slot w : UInt64) (keys subjects : Array UInt64) (key : UInt64 → Variable) (subject : UInt64 → Term sig)
    (ok : Executable.reduceRuleSlot slot keys subjects = #[w])
    (present : (⟨.free d p, .var (key slot)⟩ : Equation sig) ∈ rules)
    (apps : ∀ r ∈ rules, Rewriting.ConstructorVariants.Application r.lhs)
    (resultSort : Subsort (key slot).sort (sig.outputSort d))
    (absent : ∀ f ∈ Rewriting.ConstructorVariants.operators (subject w),
      f ∉ Rewriting.ConstructorVariants.ruleHeads rules)
    (shape : ∀ i, Rewriting.RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) (p i) (ys i))
    (live : ∀ i a j b, (i, a) ∈ keys.toList.zip subjects.toList →
      (j, b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j)
    (typed : ∀ k v, (k, v) ∈ keys.toList.zip subjects.toList →
      HasSort (sig := sig) (subject v) (key k).sort) :
    Rewriting.NormalForm (Rewriting.ruleRoot rules) (.free d ys) (subject w) :=
  Rewriting.RuleReduction.normalForm exportedRuleReduction_correct rules d p ys slot w
    keys subjects key subject ok present apps resultSort absent shape live typed

theorem exportedGroundRuleReduction_semantic {sig : Signature} (rules : List (Equation sig))
    (d : sig.FreeSym) (p ys : Fin (sig.arity d) → Term sig)
    (rhs : Term sig) (slot w : UInt64) (keys subjects : Array UInt64) (key : UInt64 → Variable) (subject : UInt64 → Term sig)
    (ok : Executable.reduceRuleSlot slot keys subjects = #[w])
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (apps : ∀ r ∈ rules, Rewriting.ConstructorVariants.Application r.lhs)
    (ground : rhs.Ground) (resultSort : HasSort rhs (sig.outputSort d))
    (absent : ∀ f ∈ Rewriting.ConstructorVariants.operators rhs,
      f ∉ Rewriting.ConstructorVariants.ruleHeads rules)
    (shape : ∀ i, Rewriting.RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) (p i) (ys i))
    (live : ∀ i a j b, (i, a) ∈ keys.toList.zip subjects.toList →
      (j, b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j)
    (typed : ∀ k v, (k, v) ∈ keys.toList.zip subjects.toList →
      HasSort (sig := sig) (subject v) (key k).sort) :
    Rewriting.NormalForm (Rewriting.ruleRoot rules) (.free d ys) rhs :=
  Rewriting.RuleReduction.groundNormalForm exportedRuleReduction_correct rules d p ys rhs slot w
    keys subjects key subject ok present apps ground resultSort absent shape live typed

theorem exportedCommOrientations_correct : Commutative.Correct Executable.commOrientations :=
  CommutativeCandidateProofs.correct

theorem exportedNestedTreeMatch_correct :
    NestedTreeMatch.Correct Executable.openMatchSelect Executable.flatACMatch Executable.commOrientations :=
  NestedTreeMatch.correct exportedOpenMatchSelect_correct exportedCompoundPartitions_correct exportedCommOrientations_correct

theorem exportedRecursiveACMatch_correct :
    RecursiveACMatch.Correct Executable.openMatchSelect Executable.flatACMatch
      Executable.commOrientations Executable.cancelCommon :=
  RecursiveACMatch.correct exportedOpenMatchSelect_correct exportedCompoundPartitions_correct
    exportedCommOrientations_correct exportedCancelCommon_correct

theorem exportedOpenSubjectMatch_correct :
    Matching.RigidSubject.SearchCorrect Executable.openMatchSelect Executable.flatACMatch
      Executable.commOrientations Executable.cancelCommon :=
  Matching.RigidSubject.of_recursive exportedRecursiveACMatch_correct

theorem exportedSeededMatch_correct :
    RecursiveACMatch.SeededCorrect Executable.openMatchSelect Executable.flatACMatch
      Executable.commOrientations Executable.cancelCommon :=
  RecursiveACMatch.seeded_correct exportedRecursiveACMatch_correct

theorem exportedSpecializedSeedMatch_correct :
    RecursiveACMatch.SpecializedSeedCorrect Executable.openMatchSelect Executable.flatACMatch
      Executable.commOrientations Executable.cancelCommon :=
  RecursiveACMatch.specialized_seed_correct exportedRecursiveACMatch_correct

theorem exportedACSubgroupNormal :
    ACSubgroups.Normality Executable.acSubgroups Executable.openMatchSelect
      Executable.flatACMatch Executable.commOrientations Executable.cancelCommon :=
  ACSubgroups.normal exportedACSubgroups_correct exportedRecursiveACMatch_correct

theorem exportedACSubproductSuccessors :
    Rewriting.ACSubproductReduction.Successors Executable.acSubgroups :=
  Rewriting.ACSubproductReduction.successors_iff exportedACSubgroups_correct

/-- A binary root match against the active AC equations has one observable
normal value across both alignments and all matching rule instances. -/
theorem exportedBinaryACReduction_semantic :
    Rewriting.ACRootReduction.Semantic Executable.openMatchSelect Executable.flatACMatch
        Executable.commOrientations Executable.cancelCommon :=
  Rewriting.ACRootReduction.semantic exportedRecursiveACMatch_correct

theorem exportedBinaryACReduction_empty :
    Rewriting.ACRootReduction.EmptySemantic Executable.openMatchSelect Executable.flatACMatch
        Executable.commOrientations Executable.cancelCommon :=
  Rewriting.ACRootReduction.emptySemantic exportedRecursiveACMatch_correct

theorem exportedCommOrientations_bound : Commutative.BranchBound Executable.commOrientations :=
  CommutativeCandidateProofs.bound

/-- Unconditional linear-variable fragment, including the e-map variable
query from NumberSubtermTests. The reference solver freshens whole answers. -/
theorem exportedCommutative_linear {sig : Signature} (l : Commutative.Linear sig)
    (key : Head sig → UInt64) (p : UInt8) (hp : Commutative.Priority l.query p)
    (avoid : List Variable) :
    (Outcome.complete (l.solve Executable.commOrientations key p avoid)).CorrectIn l.query.problem avoid :=
  l.correct exportedCommOrientations_correct key p hp avoid

/-- Pin the scalar ABI to complete answers for the entire system, including
caller scope. A branch continuation must establish its own completeness. -/
theorem exportedCommutative_semantic {sig : Signature} (q : Commutative.Query sig)
    (key : Head sig → UInt64) (p : UInt8) (hp : Commutative.Priority q p)
    (avoid : List Variable) (answers : Bool → List (Substitution sig)) :
    let word := Commutative.headCode key
    let bs := Commutative.orientations (Executable.commOrientations
      (word q.a) (word q.b) (word q.c) (word q.d) p)
    (∀ b ∈ bs, (Outcome.complete (answers b)).CorrectIn (q.branch b) avoid) →
      (Outcome.complete (bs.flatMap answers)).CorrectIn q.problem avoid :=
  fun h => Commutative.assemble q _ answers avoid
    (Commutative.run_solves exportedCommOrientations_correct q key p hp) h

theorem exportedAtomicACPair_semantic {sig : Signature} (q : AtomicACPair.Query sig)
    (admitted : q.Admitted) (key : Head sig → UInt64) (p : UInt8) (hp : q.Priority p)
    (avoid : List Variable) (answers : Bool → List (Substitution sig)) :
    let word := Commutative.headCode key
    let bs := Commutative.orientations (Executable.commOrientations
      (word q.a) (word q.b) (word q.c) (word q.d) p)
    (∀ b ∈ bs, (Outcome.complete (answers b)).CorrectIn (q.branch b) avoid) →
      (Outcome.complete (bs.flatMap answers)).CorrectIn q.problem avoid :=
  AtomicACPair.assemble exportedCommOrientations_correct q admitted key p hp avoid answers

/-- The caller can allocate finite branch-local slot names. This obligation
applies to decoded witness-bearing packets independently of the allocator. -/
theorem callerAllocated_complete {sig : Signature} {ι : Type} (r : Request sig) (arms : List ι)
    (raw out : ι → Substitution sig)
    (assign : (i : ι) → CallerFreshening.Allocation (CallerFreshening.sources r.problem (raw i)))
    (rep : ∀ i ∈ arms, CallerFreshening.RepresentsMod r.problem (raw i) (out i) (assign i))
    (fresh : ∀ i ∈ arms, CallerFreshening.Avoids r (raw i) (assign i))
    (complete : CompleteSet r.problem (arms.map raw)) :
    (Outcome.complete (arms.map out)).CorrectIn r.problem r.avoid :=
  (CallerFreshening.refinement_mod r arms raw out assign rep fresh).preserves_correct complete

theorem exportedCheckFactors_correct : FactorCheck.Correct Executable.checkFactors :=
  FactorCheck.run_correct

theorem exportedCheckFactors_chain : FactorAdmission.ChainRequired Executable.checkFactors :=
  FactorAdmission.run_chain

theorem exportedCheckFactors_required : FactorAdmission.Required Executable.checkFactors :=
  FactorAdmission.run_required

/-- A checked factor followed by any complete residual solver covers every
solution of the original equations, provided residual witnesses avoid the
variables still visible through the factor. -/
theorem exportedCheckFactors_lift {s : Signature} (g : FactoredAC.Input s)
    {p q : Problem s} {θ : Substitution s} {arms : List (Substitution s)} {reserved : List Variable}
    (layout : g.Represents p θ q)
    (hit : Executable.checkFactors g.decls g.nodes g.original g.bindings g.residual = true)
    (answers : (Outcome.complete arms).CorrectIn q reserved)
    (kept : FactoredUnification.Protected p q θ reserved) :
    CompleteSet p (arms.map fun σ => σ.compose θ) := by
  obtain ⟨_, _, _, fact⟩ := g.checked_factor exportedCheckFactors_correct layout hit
  exact FactoredUnification.lift_complete fact answers kept

/-- With no residual equations, the proposed substitution alone is a complete
family. Every original solution instantiates it on all query variables. -/
theorem exportedCheckFactors_solved {s : Signature} (g : FactoredAC.Input s)
    {p : Problem s} {θ : Substitution s} (layout : g.Represents p θ [])
    (hit : Executable.checkFactors g.decls g.nodes g.original g.bindings g.residual = true) :
    CompleteSet p [θ] := by
  obtain ⟨_, _, _, fact⟩ := g.checked_factor exportedCheckFactors_correct layout hit
  constructor
  · intro σ hσ
    obtain rfl := List.mem_singleton.mp hσ
    intro e he
    simpa only [Substitution.apply_compose, Substitution.apply_identity] using
      fact.forward .identity (by simp [Problem.Solves]) e he
  · intro ρ sol
    exact ⟨θ, List.mem_singleton_self _, ρ, fact.stable ρ sol⟩

/-- Certify the actual request-wide export for every caller freshness scope. -/
theorem exportedWholeUnify_correct : WholeProblem.Correct Executable.wholeUnify :=
  MixedSizeWhole.correct

theorem exportedWholeUnify_mixedRequired : MixedSizeWhole.Required Executable.wholeUnify :=
  MixedSizeWhole.required

theorem exportedVariantOverlap_correct : VariantOverlapGraph.Correct Executable.variantOverlapAgrees :=
  ACSpanWhole.correct

theorem exportedVariantOverlap_spanRequired : ACSpanWhole.Required Executable.variantOverlapAgrees :=
  ACSpanWhole.required

theorem exportedVariantOverlap_compatible {s : Signature} {I : Type} {R : Rewriting.Root s}
    (c : WholeProblem.Codec s) (ids : List I) (p q : Rewriting.RootNarrowing.State s I)
    {ds ns es raw} (decoded : Whole.Wire.decodeProblem ds ns es = some raw)
    (represented : CheckedFactoring.Rows c (VariantOverlapGraph.equations ids p.input q.input
      (p.value ()) (q.value ())) raw) (hit : Executable.variantOverlapAgrees ds ns es = true) :
    Rewriting.RootNarrowing.CompatibleValues R p q :=
  (exportedVariantOverlap_correct.semantic c ids _ _ _ _ ds ns es raw decoded represented hit).compatible

/-- An accepted free-factor packet followed by a completed homogeneous matrix
run certifies the answers to the original query, including caller materialization. -/
theorem exportedFactoredAC_correct :
    FactoredAC.Correct Executable.checkFactors Homogeneous.solve :=
  FactoredAC.correct exportedCheckFactors_correct Homogeneous.solve_correct

theorem exportedFactoredGraph_correct :
    FactoredAC.GraphCorrect Executable.checkFactors Executable.wholeUnify :=
  FactoredAC.graph_correct exportedCheckFactors_correct exportedWholeUnify_correct

/-- The graph caller supplies column identities. Every coefficient follows from
the same equation roots used by the whole-problem and factor contracts. -/
theorem exportedGraphHomogeneous_correct : GraphUnification.Correct Executable.graphHomogeneousUnify :=
  GraphUnification.run_correct

theorem exportedGraphACFeasible_correct : ACFeasibility.Correct Executable.graphACFeasible :=
  ACFeasibility.run_correct

theorem exportedCheckedGraphHomogeneous_correct :
    GraphUnification.Checked Executable.checkFactors Executable.graphHomogeneousUnify :=
  GraphUnification.checked_correct exportedCheckFactors_correct exportedGraphHomogeneous_correct

/-- The payload consumed by Rust has explicit column IDs and dense witness IDs. -/
theorem exportedMaskedOperand_correct : MaskedOperands.Correct Executable.maskedOperandUnify :=
  MaskedOperands.run_correct

theorem exportedOperandUnify_refines : OperandUnification.Refines
    Executable.operandUnify Homogeneous.solve :=
  OperandUnification.run_refines OperandCounts.run_correct Homogeneous.solve

theorem exportedForcedOperandClasses_correct : ForcedOperandClasses.Correct Executable.forcedOperandClasses :=
  ForcedOperandClasses.run_correct

theorem exportedForcedOperandClasses_source : ForcedOperandClasses.Source Executable.forcedOperandClasses :=
  ForcedOperandClasses.source_of_correct exportedForcedOperandClasses_correct

theorem exportedAnswerProjection_correct : AnswerProjection.Correct Executable.projectAnswers :=
  AnswerProjection.project_correct

theorem exportedMatrixAnswers_project : ProjectionCompletion.MatrixTotal
    Homogeneous.solve Executable.projectAnswers :=
  ProjectionCompletion.matrix_total exportedAnswerProjection_correct

theorem exportedOperandAnswers_project : ProjectionCompletion.OperandTotal
    Executable.operandUnify Executable.projectAnswers :=
  ProjectionCompletion.operand_total exportedOperandUnify_refines exportedMatrixAnswers_project

theorem exportedGraphAnswers_project : ProjectionCompletion.GraphTotal
    Executable.graphHomogeneousUnify Executable.projectAnswers :=
  ProjectionCompletion.graph_total exportedAnswerProjection_correct

theorem exportedProjectedBindings_correct : ProjectedBindings.Checked Executable.checkFactors
    Executable.graphHomogeneousUnify Executable.projectAnswers :=
  ProjectedBindings.checked_correct exportedCheckedGraphHomogeneous_correct exportedAnswerProjection_correct

/-- Optimizing the matrix kernel must preserve its interpretation on compound operands. -/
theorem exportedOperandLifting_correct : OperandAbstraction.PacketLifting Homogeneous.solve :=
  OperandAbstraction.packet_complete Homogeneous.solve_correct

theorem exportedNestedACLifting_correct : OperandAbstraction.NestedLifting Homogeneous.solve :=
  OperandAbstraction.nested_lifting Homogeneous.solve_correct

theorem exportedProjectedOperands_correct : ProjectedOperands.Correct
    Executable.operandUnify Executable.projectAnswers :=
  ProjectedOperands.correct exportedOperandUnify_refines exportedNestedACLifting_correct
    exportedAnswerProjection_correct

/-- Dropping a flat projected answer with the same incidence key as a
retained answer preserves instantiation on all original input variables. -/
theorem flatAnswerKeys_cover {sig : Signature} {inputs : List Variable} {σ τ : Substitution sig}
    (p : Problem sig) (domain : ∀ v, p.Occurs v → v ∈ inputs)
    (a : FlatAnswerIncidence.View inputs σ) (b : FlatAnswerIncidence.View inputs τ)
    (key : FlatAnswerIncidence.SameKey a b) :
    Substitution.InstanceOn p.Occurs σ τ ∧ Substitution.InstanceOn p.Occurs τ σ :=
  FlatAnswerIncidence.covers p domain a b key

theorem exportedResidualRigid_correct : ResidualRigid.Correct Executable.residualRigid :=
  ResidualRigid.run_correct

theorem exportedContextRowSelection_semantic :
    ContextRowSelection.Semantic Executable.residualRigid Executable.cancelCommon Executable.operandRefine :=
  ContextRowSelection.semantic exportedResidualRigid_correct exportedCancelCommon_correct exportedOperandRefine_correct

theorem exportedResidualRigid_rejectsMalformed : ResidualRigid.RejectsMalformed Executable.residualRigid :=
  ResidualRigid.run_rejectsMalformed

theorem exportedResidualVariable_correct : ResidualVariable.Correct Executable.residualVariable :=
  ResidualVariable.run_correct

theorem exportedResidualVariable_rejectsMalformed : ResidualVariable.RejectsMalformed Executable.residualVariable :=
  ResidualVariable.run_rejectsMalformed

theorem exportedXorOdd_correct (count : UInt64) :
    Executable.xorOdd count = true ↔ count.toNat % 2 = 1 := by
  simp [Executable.xorOdd, RuntimeCandidate.xorOdd, ← UInt64.toNat_inj, UInt64.toNat_mod]

/-- The same scalar kernel also decides parity for arbitrary normalized
messages under a validated AC presentation with unit and cancellation. -/
theorem exportedACParityReduction : Rewriting.BinaryXor.Reduction Executable.xorOdd :=
  Rewriting.BinaryXor.reduction exportedXorOdd_correct

open Rewriting in
theorem binaryACParityClassification {sig : Signature} (T : BinaryXor.Table sig) {a b out : Term sig}
    (ha : BinaryXor.Good T a) (hb : BinaryXor.Good T b) (nf : NormalForm T.R (.ac T.f a b) out) :
    ∃ shape, BinaryXor.Instance T a b out shape :=
  BinaryXor.classify T ha hb nf

/-- The count of each operand in the original nonempty XOR is encoded without
truncation. The selected operands can be emitted in any order. Their XOR is
exactly the normal form under the entire active table, including when none
or just one survives. -/
theorem exportedXorOdd_normalForms {sig : Signature} [DecidableEq (Term sig)]
    (T : Rewriting.FreshXor.Flat.Table sig) (a b : Term sig) (xs ys : List (Term sig))
    (fresh : ∀ t ∈ a::b::xs, HasSort t .fresh) (normal : ∀ t ∈ a::b::xs, Rewriting.Normal T.R t)
    (distinct : ys.Nodup) (count : Term sig → UInt64)
    (exactCount : ∀ t, (count t).toNat = (a::b::xs).count t)
    (selected : ∀ t, t ∈ ys ↔ Executable.xorOdd (count t) = true) (u : Term sig) :
    Rewriting.NormalForm T.R (T.value (a::b::xs)) u ↔ EquivB u (T.value ys) := by
  apply T.normalForm_iff fresh normal distinct
  intro t
  have h := (selected t).trans (exportedXorOdd_correct (count t))
  rw [exactCount] at h
  by_cases mem : t ∈ ys
  · rw [distinct.count_of_mem mem, h.mp mem]
  · rw [List.count_eq_zero.mpr mem]
    have := mt h.mpr mem
    omega

theorem exportedXorBranches_correct : Rewriting.FreshXor.BranchCorrect Executable.xorBranches :=
  Rewriting.FreshXor.candidate_correct

theorem exportedXorMatchings_correct : XorMatchings.Correct Executable.xorMatchings :=
  XorMatchings.correct

theorem exportedBinaryCancellationRows_correct :
    Rewriting.BinaryXor.RowsCorrect (Executable.binaryCancellationRows ()) :=
  Rewriting.BinaryXor.candidate_rows

theorem exportedMixedCancellationRows_correct :
    Rewriting.MixedCancellation.RowsCorrect (Executable.mixedCancellationRows ()) :=
  Rewriting.MixedCancellation.candidate_rows

open Rewriting Rewriting.MixedCancellation in
theorem exportedMixedCancellationVariants_live {sig : Signature} (q : Query sig)
    (caller : Term sig) (layout : EquivB caller q.term)
    (rules : List (Equation sig)) (presentation : RulePresentation.Same q.table.rules rules)
    (arms : List (Variant sig))
    (all : ∀ row ∈ Executable.mixedCancellationRows (), ∃ a ∈ arms, PacketArm q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ Executable.mixedCancellationRows (), PacketArm q row a) :
    CompleteVariants (ruleRoot rules) [caller] arms ∧ ∀ a ∈ arms, a.Reconstructible (ruleRoot rules) [caller] :=
  (presentation.variants [caller] arms).mp
    (CompleteVariants.presented (packetFamily_complete q _ exportedMixedCancellationRows_correct arms all only) layout)

open Rewriting Rewriting.MixedCancellation Rewriting.VariantJoin in
theorem joinedCancellationVariants_packed {sig : Signature} {A : Type} {keys : List Variable}
    (T : BinaryXor.Table sig) (op : A → Term sig) (admit : ∀ a, Observation T (op a))
    (rows : List (Row sig (Key keys) A)) (exactRows : Exact T.R Subtype.val op rows)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal T.R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (stable : ∀ t, .inr t ∈ slots → StableVariants.Representative T.R t (n t)) :
    CompleteVariants T.R (slots.map (packedInput op)) (packRows rows typed slots n) ∧
      ∀ a ∈ packRows rows typed slots n, a.Reconstructible T.R (slots.map (packedInput op)) :=
  MixedCancellation.packed T op admit rows exactRows typed normal slots used scope n stable

open Rewriting Rewriting.BinaryXor in
theorem exportedBinaryCancellationVariants_complete {sig : Signature} (q : Query sig) (arms : List (Variant sig))
    (all : ∀ row ∈ Executable.binaryCancellationRows (), ∃ a ∈ arms, PacketArm q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ Executable.binaryCancellationRows (), PacketArm q row a) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] :=
  packetFamily_complete q _ exportedBinaryCancellationRows_correct arms all only

open Rewriting Rewriting.BinaryXor in
theorem exportedBinaryCancellationVariants_live {sig : Signature} (q : Query sig)
    (rules : List (Equation sig)) (presentation : RulePresentation.Same q.table.rules rules)
    (arms : List (Variant sig))
    (all : ∀ row ∈ Executable.binaryCancellationRows (), ∃ a ∈ arms, PacketArm q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ Executable.binaryCancellationRows (), PacketArm q row a) :
    CompleteVariants (ruleRoot rules) [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible (ruleRoot rules) [q.term] :=
  (presentation.variants [q.term] arms).mp (exportedBinaryCancellationVariants_complete q arms all only)

open Rewriting Rewriting.BinaryXor in
theorem binaryXorVariants_complete {sig : Signature} (q : Query sig) (arms : List (Variant sig))
    (all : ∀ sh, ∃ a ∈ arms, Decodes q sh a) (only : ∀ a ∈ arms, ∃ sh, Decodes q sh a) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] :=
  complete q arms all only

open Rewriting Rewriting.BinaryXor Rewriting.VariantJoin in
theorem binaryXorLeaf_exact {sig : Signature} (q : Query sig) (arms : List (Variant sig))
    (all : ∀ sh, ∃ a ∈ arms, Decodes q sh a) (only : ∀ a ∈ arms, ∃ sh, Decodes q sh a)
    {I : Type} (ids : I → Variable) (scope : ∀ v, q.term.Occurs v → ∃ i, ids i = v)
    (rows : List (Row sig I Unit))
    (opens : ∀ a ∈ arms, ∃ out ∈ rows, DecodesLeaf q.table.R q.term ids a out)
    (comesFrom : ∀ out ∈ rows, ∃ a ∈ arms, DecodesLeaf q.table.R q.term ids a out) :
    Exact q.table.R ids (fun _ => q.term) rows ∧ ∀ out ∈ rows,
      (∀ i, HasSort (out.input i) (ids i).sort) ∧ out.IsNormal q.table.R :=
  q.leaf arms all only ids scope rows opens comesFrom

open Rewriting Rewriting.BinaryXor Rewriting.VariantJoin in
theorem joinedBinaryXorVariants_packed {sig : Signature} {A : Type} {keys : List Variable}
    (T : Table sig) (op : A → Term sig) (admit : ∀ a, ∃ l r, op a = .ac T.f l r ∧
      ∀ ρ : Substitution sig, Normalized T.R ρ → Good T (ρ.apply l) ∧ Good T (ρ.apply r))
    (rows : List (Row sig (Key keys) A)) (exactRows : Exact T.R Subtype.val op rows)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal T.R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (stable : ∀ t, .inr t ∈ slots → StableVariants.Representative T.R t (n t)) :
    CompleteVariants T.R (slots.map (packedInput op)) (packRows rows typed slots n) ∧
      ∀ a ∈ packRows rows typed slots n, a.Reconstructible T.R (slots.map (packedInput op)) :=
  BinaryXor.packed T op admit rows exactRows typed normal slots used scope n stable

open Rewriting Rewriting.FreshXor.Flat in
theorem exportedFlatXorVariants_complete {sig : Signature} {width : UInt64} (q : Query sig width.toNat)
    {rows} (ran : Executable.xorMatchings width = some rows) (arms : List (Variant sig))
    (all : ∀ row ∈ rows, ∃ a ∈ arms, Decodes q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ rows, Decodes q row a) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] :=
  exported_complete q exportedXorMatchings_correct ran arms all only

open Rewriting Rewriting.FreshXor.Flat in
theorem decodedFlatXorVariant_scope {sig : Signature} {n} {q : Query sig n} {p : Fin n → Fin n}
    (w : Naming q p) (avoid : List Variable) (fresh : w.FreshFor avoid) :
    w.arm.Safe [q.term] avoid ∧ ∀ v, w.subst.apply (w.subst.image v) = w.subst.image v :=
  w.scope avoid fresh

theorem exportedXorVariants_semantic {sig : Signature} (q : Rewriting.FreshXor.Query sig)
    (slots : List Rewriting.FreshXor.Slot) (sum : .sum ∈ slots) (avoid : List Variable)
    (fresh : q.witness ∉ avoid) :
    q.Admissible slots avoid (q.decode slots (Executable.xorBranches (decide (q.x = q.y)))) :=
  q.correct _ exportedXorBranches_correct slots sum avoid fresh

theorem exportedXorVariants_reconstructible {sig : Signature} (q : Rewriting.FreshXor.Query sig)
    (slots : List Rewriting.FreshXor.Slot) (answer)
    (hm : answer ∈ q.decode slots (Executable.xorBranches (decide (q.x = q.y)))) :
    answer.Reconstructible q.table.R (slots.map q.input) := by
  apply q.reconstruct slots _ _ answer hm
  rw [exportedXorBranches_correct]
  by_cases e : q.x = q.y <;> simp [e]

open Rewriting Rewriting.VariantJoin in
/-- Project joined XOR rows back onto the original tuple. Shared input variables
and repeated observations use the same substitution in every position. -/
theorem joinedXorVariants_packed {sig : Signature} {A : Type} {keys : List Variable}
    (T : FreshXor.Table sig) (op : A → Term sig) (admit : ∀ a, FreshXor.Observation T.f (op a))
    (rows : List (Row sig (Key keys) A)) (exactRows : Exact T.R Subtype.val op rows)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal T.R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (stable : ∀ t, .inr t ∈ slots → StableVariants.Representative T.R t (n t)) :
    CompleteVariants T.R (slots.map (packedInput op)) (packRows rows typed slots n) ∧
      ∀ answer ∈ packRows rows typed slots n, answer.Reconstructible T.R (slots.map (packedInput op)) :=
  exactRows.packedRepresentatives (ConstructorVariants.constructor_normal T.rules T.apps).1
    typed normal slots used scope n stable fun ρ hn a _ _ => (admit a).unique ρ hn

open Rewriting Rewriting.VariantJoin in
/-- Packed flat XOR operations may have any arity ≥ 2, repeat variables across
operations and share stable observers. Pruning can discard an intermediate
row only when a more general row covers its inputs and every output. -/
theorem joinedFlatXorVariants_packed {sig : Signature} {A : Type} {keys : List Variable}
    (T : FreshXor.Flat.Table sig) (op : A → Term sig) (admit : ∀ a, FreshXor.Flat.Observation T (op a))
    (rows kept : List (Row sig (Key keys) A)) (exactRows : Exact T.R Subtype.val op rows)
    (subset : ∀ r ∈ kept, r ∈ rows) (measure : Row sig (Key keys) A → Nat)
    (removed : ∀ r ∈ rows, r ∉ kept → ∃ p ∈ rows, measure p < measure r ∧ p.Subsumes r)
    (typed : ∀ r ∈ kept, r.Sorted) (normal : ∀ r ∈ kept, r.IsNormal T.R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (stable : ∀ t, .inr t ∈ slots → StableVariants.Representative T.R t (n t)) :
    CompleteVariants T.R (slots.map (packedInput op)) (packRows kept typed slots n) ∧
      ∀ answer ∈ packRows kept typed slots n, answer.Reconstructible T.R (slots.map (packedInput op)) := by
  have vars := (ConstructorVariants.constructor_normal T.rules T.apps).1
  exact (exactRows.prunedByRank vars subset measure removed).packedRepresentatives vars
    typed normal slots used scope n stable fun ρ hn a _ _ => (admit a).unique ρ hn

theorem exportedXorReduction_semantic {sig : Signature} (T : Rewriting.FreshXor.Table sig)
    {a b : Term sig} (ha : HasSort a .fresh) (hb : HasSort b .fresh)
    (na : Rewriting.Normal T.R a) (nb : Rewriting.Normal T.R b)
    (same : Bool) (he : same = true ↔ a = b) :
    Rewriting.NormalForm T.R (.ac T.f a b)
      (if Executable.xorBranches same &&& 1 == 0 then T.zero else .ac T.f a b) :=
  Rewriting.FreshXor.selected_normalForm T ha hb na nb exportedXorBranches_correct same he

theorem exportedRigidAllocation_correct : RigidAllocation.PacketCorrect Executable.rigidAllocation :=
  RigidAllocationCandidateProofs.correct

theorem exportedRigidAllocation_semantic {sig : Signature}
    (q : RigidAllocation.Query sig) (ground : ∀ v, ¬ q.a.Occurs v)
    (reversed : Bool) (avoid : List Variable) (d : RigidAllocation.Decoder q avoid) :
    ∃ answers : List (Substitution sig),
      ((Executable.rigidAllocation reversed).toList.map
        (fun arm => RigidAllocation.decodeArm q (d.slot arm) arm)).Perm
        (answers.map fun σ => some (FreshAnswer.encode [q.x,q.y,q.z] σ).bindings) ∧
      (Outcome.complete answers).CorrectIn (q.problemOriented reversed) avoid ∧
      ∀ σ ∈ answers, RigidAllocation.ClosedRanges q avoid σ :=
  RigidAllocation.packet_correctIn exportedRigidAllocation_correct q ground reversed avoid d

/-- The dependent variable cannot own a factor containing itself. Check the
filtered, instantiated ABI rows and a shared fresh range on the original query. -/
theorem exportedDependentAllocation_semantic {sig : Signature} (q : DependentAllocation.Query sig)
    (reverse swap : Bool) (avoid : List Variable) (d : RigidAllocation.DecoderFor q.f q.problem.Occurs avoid) :
    ∃ answers : List (Substitution sig),
      ((Executable.rigidAllocation reverse).toList.filterMap (fun arm =>
        DependentAllocation.decodeArm q (d.slot arm) arm)).Perm
        (answers.map fun σ => (FreshAnswer.encode [q.x,q.y,q.z] σ).bindings) ∧
      (Outcome.complete answers).CorrectIn (q.oriented reverse swap) avoid ∧
      ∀ σ ∈ answers, q.Closed avoid σ :=
  DependentAllocation.packet_correct exportedRigidAllocation_correct q reverse swap avoid d

theorem exportedSharedOffset_correct : SharedOffset.PacketCorrect Executable.sharedOffset :=
  SharedOffsetCandidateProofs.correct

theorem exportedSharedOffset_semantic {sig : Signature} (q : SharedOffset.Query sig)
    (a b : UInt64) (atom : UInt64 → sig.Atom) (ha : atom a = q.a) (hb : atom b = q.b)
    (slot : UInt64 → Variable) (typed : ∀ w, (slot w).sort = sig.acSort q.f)
    (avoid : List Variable) (fresh : ∀ w, slot w ∉ avoid ++ [q.x, q.y]) :
    ∃ answers : List (Substitution sig),
      ((Executable.sharedOffset a b).toList.map (SharedOffset.decodeArm q atom slot)).Perm
        (answers.map fun σ => some (FreshAnswer.encode [q.x, q.y] σ).bindings) ∧
      (Outcome.complete answers).CorrectIn (SharedOffset.problem q.f q.x q.y q.a q.b) avoid ∧
      ∀ σ ∈ answers, SharedOffset.ClosedRanges q avoid σ :=
  SharedOffset.packet_correctIn exportedSharedOffset_correct q a b atom ha hb slot typed avoid fresh

theorem exportedCompoundOffset_semantic {sig : Signature}
    (q : CompoundOffset.Query sig) (avoid : List Variable) (d : CompoundOffset.Decoder q avoid)
    (a b : UInt64) (term : UInt64 → Term sig) (ha : term a = q.a) (hb : term b = q.b) :
    ∃ answers : List (Substitution sig),
      ((Executable.sharedOffset a b).toList.map (d.decodeArm term)).Perm
        (answers.map fun σ => some (FreshAnswer.encode d.keys σ).bindings) ∧
      (Outcome.complete answers).CorrectIn q.problem avoid ∧
      ∀ σ ∈ answers, ∀ v ∈ d.keys, ∀ t, (σ.image v).Occurs t → ¬ q.problem.Occurs t ∧ t ∉ avoid :=
  CompoundOffset.packet_correctIn exportedSharedOffset_correct q avoid d a b term ha hb

theorem exportedACFactorExclusion_correct :
    Rewriting.ACFactorExclusion.Correct Executable.excludeACFactors :=
  Rewriting.ACFactorExclusion.correct

theorem exportedRootExclusion_correct : Rewriting.RootExclusion.Correct Executable.excludeRoot :=
  Rewriting.RootExclusion.correct

theorem exportedUniformReduction_correct :
    Rewriting.UniformReduction.Correct Executable.reduceRuleSlot Executable.excludeRoot :=
  Rewriting.UniformReduction.correct exportedRuleReduction_correct exportedRootExclusion_correct

theorem exportedPowerNormalization_correct :
    Rewriting.PowerNormalization.Correct Executable.reduceRuleSlot Executable.excludeRoot :=
  Rewriting.PowerNormalization.correct exportedRuleReduction_correct exportedRootExclusion_correct

/-- The very same exported exclusion decision certifies a normal product
after all sorted normal instantiations, including repeated or equal factors. -/
theorem exportedStableAC_semantic {s : Signature} [DecidableEq s.ACSym]
    (rules : List (Equation s)) (apps : ∀ r ∈ rules, Rewriting.ConstructorVariants.Application r.lhs)
    (f : s.ACSym) (query : Term s) (code : Head s → UInt64)
    (rows : Array (Array UInt64)) (heads : Array UInt64)
    (factors : ∀ t ∈ ACRepresentation.flatten f query, Rewriting.StableVariants.Stable (Rewriting.ruleRoot rules) t)
    (fixed : ∀ t ∈ ACRepresentation.flatten f query, ∀ ρ : Substitution s,
      Rewriting.ConstructorVariants.head (ρ.apply t) ≠ .ac f ∧
      code (Rewriting.ConstructorVariants.head (ρ.apply t)) ∈ heads)
    (buckets : Rewriting.StableVariants.Buckets rules f code rows)
    (ok : Executable.excludeACFactors rows heads = true) :
    Rewriting.StableVariants.Stable (Rewriting.ruleRoot rules) query :=
  Rewriting.StableVariants.acExcluded rules apps f query code rows heads factors fixed buckets
    exportedACFactorExclusion_correct ok

theorem exportedConstructorVariant_correct :
    Rewriting.ConstructorVariants.DecisionCorrect Executable.constructorVariant :=
  ConstructorVariantCandidateProofs.correct

theorem exportedConstructorVariant_semantic {sig : Signature}
    (rules : List (Equation sig)) (query : List (Term sig)) (roots used : Array UInt64)
    (encode : Head sig → UInt64) (apps : ∀ r ∈ rules, Rewriting.ConstructorVariants.Application r.lhs)
    (hr : ∀ f ∈ Rewriting.ConstructorVariants.ruleHeads rules, encode f ∈ roots.toList)
    (hu : ∀ t ∈ query, ∀ f ∈ Rewriting.ConstructorVariants.operators t, encode f ∈ used.toList)
    (ok : Executable.constructorVariant roots used = true) (avoid : List Variable) :
    let answer : Rewriting.Variant sig := ⟨Substitution.identity, query⟩
    MaudeOperations.VariantReply (Rewriting.ruleRoot rules) query avoid [answer] := by
  apply MaudeOperations.VariantReply.singleton_iff.mpr
  obtain ⟨complete, safe⟩ := Rewriting.ConstructorVariants.encoded_identity
    exportedConstructorVariant_correct rules query roots used encode apps hr hu ok avoid
  exact ⟨complete, safe, Rewriting.VariantReconstruction.constructors rules query apps
    (fun t ht f hf hm => (exportedConstructorVariant_correct roots used).mp ok _ (hu t ht f hf) (hr f hm))
    (complete.1 _ (List.mem_singleton_self _))⟩

/-- The mask actually consumed by Rust must yield a complete and safe answer
set for the freshened rule taken from the active table. -/
theorem exportedOpenNarrowing_correct {sig : Signature} (s : Rewriting.OpenNarrowing.Schema sig)
    (rules : List (Equation sig)) (original : s.Index → Term sig) (rhs : Variable)
    (π : VariablePermutation)
    (apps : ∀ r ∈ rules, Rewriting.ConstructorVariants.Application r.lhs)
    (present : (⟨.free s.d original, .var rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, Rewriting.ConstructorVariants.head r.lhs = .free s.d →
      r = ⟨.free s.d original, .var rhs⟩)
    (patterns : ∀ i, s.p i = (π.subst sig).apply (original i)) (result : s.z = π.forward rhs)
    (constructors : ∀ i, ∀ f ∈ Rewriting.ConstructorVariants.operators (s.p i),
      f ∉ Rewriting.ConstructorVariants.ruleHeads rules)
    (q : List (Option s.Index)) (hq : none ∈ q) (avoid : List Variable)
    (fresh : ∀ v, s.Local v → v ∉ avoid ∧ ¬ ∃ i, s.x i = v) :
    ∃ answers, s.decode q (Executable.pairingVariants true) = some answers ∧
      s.Admissible (Rewriting.ruleRoot rules) q avoid answers ∧
      ∀ a ∈ answers, a.Reconstructible (Rewriting.ruleRoot rules) (q.map s.input) := by
  have good := s.table_correct rules original rhs π apps present only patterns result constructors q hq avoid fresh
  refine ⟨_, ?_, good, fun a ha => Rewriting.VariantReconstruction.openTable s rules original rhs π
    apps present only patterns result q (good.1.1 a ha)⟩
  have mask : Executable.pairingVariants true = 3 := PairingCandidateProofs.correct.openMask
  rw [mask]; rfl

/-- A value-carrying answer observes one result and any argument images. -/
theorem exportedObservedNarrowing_correct {sig : Signature} {P : Term sig → Prop}
    (s : Rewriting.OpenNarrowing.Schema sig P)
    (rules : List (Equation sig)) (original : s.Index → Term sig) (rhs : Variable)
    (π : VariablePermutation)
    (apps : ∀ r ∈ rules, Rewriting.ConstructorVariants.Application r.lhs)
    (present : (⟨.free s.d original, .var rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, Rewriting.ConstructorVariants.head r.lhs = .free s.d →
      r = ⟨.free s.d original, .var rhs⟩)
    (patterns : ∀ i, s.p i = (π.subst sig).apply (original i)) (result : s.z = π.forward rhs)
    (constructors : ∀ i, ∀ f ∈ Rewriting.ConstructorVariants.operators (s.p i),
      f ∉ Rewriting.ConstructorVariants.ruleHeads rules)
    (indices : List s.Index) (avoid : List Variable)
    (fresh : ∀ v, s.Local v → v ∉ avoid ∧ ¬ ∃ i, s.x i = v) :
    let q := s.observations indices
    ∃ answers, s.decode q (Executable.pairingVariants true) = some answers ∧
      s.Admissible (Rewriting.ruleRoot rules) q avoid answers := by
  refine ⟨_, ?_, s.observed_table rules original rhs π apps present only patterns result constructors
    indices avoid fresh⟩
  rw [show Executable.pairingVariants true = 3 from PairingCandidateProofs.correct.openMask]
  rfl

/-- The actual variant mask is interpreted on the freshened ground-result
rule and specialized query supplied by the bridge. -/
theorem exportedGroundNarrowing_correct {sig : Signature} (s : Rewriting.GroundNarrowing.Plan sig)
    (rules : List (Equation sig)) (original : Fin (sig.arity s.d) → Term sig)
    (rename : VariablePermutation) (q : List (Option (Term sig))) (dom : s.Domain rules q)
    (present : (⟨.free s.d original, s.rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, Rewriting.ConstructorVariants.head r.lhs = .free s.d →
      r = ⟨.free s.d original, s.rhs⟩)
    (renamed : ∀ i, s.pat i = (rename.subst sig).apply (original i))
    (vs avoid : List Variable) (π : VariablePermutation)
    (inventory : ∀ v, v ∈ vs ↔ Rewriting.Observed (q.map s.input) v)
    (fresh : ∀ v ∈ vs, ∀ w, (s.solution.image v).Occurs w → π.forward w ∉ vs ++ avoid)
    (holes anchors deps : Array UInt64) (rigid : Bool) (encode : Variable → UInt64)
    (ready : Rewriting.GroundVariantDecision.Admitted holes anchors deps rigid)
    (holesLive : ∀ v i, s.hole v = some i → encode v ∈ holes.toList)
    (depsLive : ∀ i, (¬ ∃ v, s.hole v = some i) → ∀ v, (s.arg i).Occurs v → encode v ∈ deps.toList) :
    ∃ answers, s.decode q vs π (Executable.groundVariant holes anchors deps rigid) = some answers ∧
      s.Admissible (Rewriting.ruleRoot rules) q avoid answers ∧
      ∀ a ∈ answers, a.Reconstructible (Rewriting.ruleRoot rules) (q.map s.input) := by
  obtain ⟨answers, decoded, good⟩ := s.table_correct rules original rename q dom present only renamed
    vs avoid π inventory fresh (s.separated_of_ids holes deps encode ready.2.2.1 holesLive depsLive) _
    ((exportedGroundDecision_correct holes anchors deps rigid).1.mpr ready)
  exact ⟨answers, decoded, good, fun a ha => Rewriting.VariantReconstruction.groundTable s rules
    original rename q dom present only renamed (good.1.1 a ha)⟩

theorem exportedFlatMatcher_semantic {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64) (f : sig.ACSym)
    (n : UInt64) (vars : Fin n.toNat → Variable) (occ : List (Fin n.toNat))
    (tail rhs : Array UInt64) (live : ∀ id ∈ tail.toList ++ rhs.toList, encode (decode id) = some id)
    (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs.toList.map decode, Subsort (sig.atomSort a) (sig.acSort f))
    (hi : Function.Injective vars) (ho : ∀ i, i ∈ occ)
    (hq : FlatMatching.queryLeaves vars occ (tail.toList.map decode) ≠ [])
    (hr : rhs.toList ≠ []) :
    let out := (Executable.flatACMatch n (occ.map (fun i => UInt64.ofNat i.val)).toArray tail rhs).toList.map
      (fun answer => answer.toList.map (fun row => row.toList.map decode))
    ∃ hout : ∀ rows ∈ out, FlatMatching.admissibleRows (n := n.toNat) (rhs.toList.map decode) rows,
      Matching.Complete
        [⟨FlatMatching.pattern f (FlatMatching.queryLeaves vars occ (tail.toList.map decode)),
          FlatAC.term f (rhs.toList.map decode)⟩] (fun _ => True)
        (FlatMatching.answersFrom f vars (rhs.toList.map decode) hv hs out hout) :=
  FlatMatchCandidateProofs.semantic decode encode f n vars occ tail rhs live hv hs hi ho hq hr

end Tamarin

/-- The pairing exports must satisfy the semantic variant/normalization
contract, including completeness and fresh output safety. -/
theorem Tamarin.exportedPairing_correct : Tamarin.PairingBackend.Correct
    { variants := Tamarin.Executable.pairingVariants,
      project := Tamarin.Executable.pairingProject } :=
  Tamarin.PairingCandidateProofs.correct

/-- Existing native exports instantiate the shared theory contracts. -/
theorem Tamarin.exportedPairing_sharedCorrect : Tamarin.PairingBackend.SharedCorrect
    { variants := Tamarin.Executable.pairingVariants,
      project := Tamarin.Executable.pairingProject } :=
  Tamarin.exportedPairing_correct.shared

/-- Every substitution decoded by the shared pairing contract determines all packed values modulo B. -/
theorem Tamarin.exportedPairing_reconstruction (q : List Tamarin.Pairing.PTerm) (σ : Tamarin.Pairing.PSubst) :
    (Tamarin.Pairing.referenceVariant q σ).Reconstructible Tamarin.Pairing.root q :=
  Tamarin.Rewriting.VariantReconstruction.pairing q σ

/-- Required semantic correctness and completion for the reflexive recipe. -/
theorem Tamarin.exportedReflexive_correct : Tamarin.ReflexiveBackend.Correct
    { solve := Tamarin.Executable.reflexiveUnify } :=
  Tamarin.ReflexiveCandidateProofs.correct

/-- Pin the reference nonground conversion to the existing output-boundary
contract. It is not yet an ABI export or a proof of the Rust reifiers. -/
theorem Tamarin.referenceFreshening_refines {sig : Tamarin.Signature}
    (request : Tamarin.Request sig) (answers : List (Tamarin.Substitution sig)) :
    Tamarin.OutputRefinement request answers
      (answers.map (Tamarin.FreshAnswer.freshen request.problem request.avoid)) :=
  Tamarin.FreshAnswer.output_refinement request answers

/-- The reference term boundary must preserve every well-sorted input exactly,
and checked decoding must reject terms outside the declared sort. This still
requires a faithful Rust identity table and a validated memory-layout adapter. -/
theorem Tamarin.referenceTermEncoding_roundTrip {sig : Tamarin.Signature}
    (codec : Tamarin.SignatureEncoding sig) (t : Tamarin.Term sig)
    (s : Tamarin.SortId) (h : Tamarin.HasSort t s) :
    Tamarin.TermEncoding.decodeChecked codec s (Tamarin.TermEncoding.encode codec t) = some t :=
  Tamarin.TermEncoding.decodeChecked_encode codec t s h

theorem Tamarin.referenceTermDecoding_correct {sig : Tamarin.Signature}
    (codec : Tamarin.SignatureEncoding sig) (s : Tamarin.SortId)
    (raw : Tamarin.NumericTerm) (t : Tamarin.Term sig) :
    Tamarin.TermEncoding.decodeChecked codec s raw = some t ↔
      Tamarin.TermEncoding.decode codec raw = some t ∧ Tamarin.HasSort t s :=
  Tamarin.TermEncoding.decodeChecked_iff codec s raw t

theorem Tamarin.referenceACFlattening_correct {sig : Tamarin.Signature}
    [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Tamarin.Term sig)
    (h : Tamarin.HasSort t (sig.acSort f)) :
    ∃ u, Tamarin.ACRepresentation.decode f (Tamarin.ACRepresentation.flatten f t) = some u ∧
      Tamarin.EquivB u t ∧ Tamarin.HasSort u (sig.acSort f) :=
  Tamarin.ACRepresentation.flatten_typed_correct f t h

/-- Fixed-width conversion preserves the entire reference tree, and failure
means exactly that an ID or arity is unrepresentable. -/
theorem Tamarin.referenceWordPacking_correct (t : Tamarin.NumericTerm) (w : Tamarin.WordTerm) :
    Tamarin.WordEncoding.term t = some w ↔ w.toNumeric = t :=
  Tamarin.WordEncoding.term_iff t w

theorem Tamarin.referenceWordPacking_failure (t : Tamarin.NumericTerm) :
    Tamarin.WordEncoding.term t = none ↔ ¬ Tamarin.WordEncoding.Fits t :=
  Tamarin.WordEncoding.term_none_iff t

theorem Tamarin.referenceSignatureTable_roundTrip (table : Tamarin.SignatureTable)
    (ht : table.Fits) (t : Tamarin.Term table.signature) (s : Tamarin.SortId)
    (hs : Tamarin.HasSort t s) (hv : ∀ v, t.Occurs v → v.id < UInt64.size) :
    ∃ w, Tamarin.WordEncoding.encode table.encoding t = some w ∧
      Tamarin.WordEncoding.decode table.encoding s w = some t :=
  table.word_roundTrip ht t s hs hv

/-!
CI audit of project declarations, including private helpers and
helpers outside the Tamarin namespace. Keep this in the root module so it
sees every specification and runtime import.
Only Lean's standard logical axioms are allowed. In particular, `sorryAx`,
custom solver axioms, and native-evaluation proof shortcuts fail CI verification.
Unchecked executable replacements (`implemented_by`, `extern`, and value
initializers) and unsafe project definitions are also forbidden: otherwise a
correct logical function could execute different code without invalidating
any correctness theorem.
Checked `csimp` equalities remain available for compiler optimizations.
The C ABI symbol mapping is pinned to the definitions named by the export
correctness/completion theorems. Adding an ABI entry requires reviewing both.
Bundled Init/Std/Lean definitions remain trusted, along with the Lean compiler,
runtime, and Rust/C FFI. This is not a sandbox against malicious metaprograms.
-/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let expectedExports : List (Name × Name) := [
    (``Tamarin.Executable.flatACEqual, `tamarin_flat_ac_equal),
    (``Tamarin.Executable.flatACResidual, `tamarin_flat_ac_residual),
    (``Tamarin.Executable.pairingVariants, `tamarin_pairing_variants),
    (``Tamarin.Executable.pairingProject, `tamarin_pairing_project),
    (``Tamarin.Executable.reflexiveUnify, `tamarin_reflexive_unify),
    (``Tamarin.Executable.acPivot, `tamarin_ac_pivot),
    (``Tamarin.Executable.selectJoinedVariants, `tamarin_select_joined_variants),
    (``Tamarin.Executable.dhExponentImages, `tamarin_dh_exponent_images),
    (``Tamarin.Executable.dhTowerImages, `tamarin_dh_tower_images),
    (``Tamarin.Executable.dhPeerImages, `tamarin_dh_peer_images),
    (``Tamarin.Executable.signedGraphVariants, `tamarin_signed_graph_variants),
    (``Tamarin.Executable.reductionGraph, `tamarin_reduction_graph),
    (``Tamarin.Executable.acSubgroups, `tamarin_ac_subgroups),
    (``Tamarin.Executable.openMatchSelect, `tamarin_open_match_select),
    (``Tamarin.Executable.acBagMatch, `tamarin_ac_bag_match),
    (``Tamarin.Executable.acBagAnswers, `tamarin_ac_bag_answers),
    (``Tamarin.Executable.acBagPage, `tamarin_ac_bag_page),
    (``Tamarin.Executable.acBagTypedMatch, `tamarin_ac_bag_typed_match),
    (``Tamarin.Executable.matchSizeExcludes, `tamarin_match_size_excludes),
    (``Tamarin.Executable.collectorPossible, `tamarin_collector_possible),
    (``Tamarin.Executable.sortedACMatch, `tamarin_sorted_ac_match),
    (``Tamarin.Executable.flatACMatch, `tamarin_flat_ac_match),
    (``Tamarin.Executable.checkedReduce, `tamarin_checked_reduce),
    (``Tamarin.Executable.factorRefutes, `tamarin_factor_refutes),
    (``Tamarin.Executable.totalUnify, `tamarin_total_unify),
    (``Tamarin.Executable.totalMatch, `tamarin_total_match),
    (``Tamarin.Executable.checkedVariants, `tamarin_checked_variants),
    (``Tamarin.Executable.wholeUnify, `tamarin_whole_unify),
    (``Tamarin.Executable.variantOverlapAgrees, `tamarin_variant_overlap_agrees),
    (``Tamarin.Executable.checkFactors, `tamarin_check_factors),
    (``Tamarin.Executable.graphHomogeneousUnify, `tamarin_graph_homogeneous_unify),
    (``Tamarin.Executable.graphACFeasible, `tamarin_graph_ac_feasible),
    (``Tamarin.Executable.operandRefine, `tamarin_operand_refine),
    (``Tamarin.Executable.maskedOperandUnify, `tamarin_masked_operand_unify),
    (``Tamarin.Executable.operandUnify, `tamarin_operand_unify),
    (``Tamarin.Executable.forcedOperandClasses, `tamarin_forced_operand_classes),
    (``Tamarin.Executable.projectAnswers, `tamarin_project_answers),
    (``Tamarin.Executable.xorBranches, `tamarin_xor_branches),
    (``Tamarin.Executable.xorMatchings, `tamarin_xor_matchings),
    (``Tamarin.Executable.mixedCancellationRows, `tamarin_mixed_cancellation_rows),
    (``Tamarin.Executable.binaryCancellationRows, `tamarin_binary_cancellation_rows),
    (``Tamarin.Executable.xorOdd, `tamarin_xor_odd),
    (``Tamarin.Executable.residualRigid, `tamarin_residual_rigid),
    (``Tamarin.Executable.residualVariable, `tamarin_residual_variable),
    (``Tamarin.Executable.commOrientations, `tamarin_comm_orientations),
    (``Tamarin.Executable.rigidAllocation, `tamarin_rigid_allocation),
    (``Tamarin.Executable.sharedOffset, `tamarin_shared_offset),
    (``Tamarin.Executable.cancelCommon, `tamarin_cancel_common),
    (``Tamarin.Executable.groundVariant, `tamarin_ground_variant),
    (``Tamarin.Executable.reduceRuleSlot, `tamarin_reduce_rule_slot),
    (``Tamarin.Executable.excludeACFactors, `tamarin_exclude_ac_factors),
    (``Tamarin.Executable.excludeRoot, `tamarin_exclude_root),
    (``Tamarin.Executable.constructorVariant, `tamarin_constructor_variant)]
  for (name, symbol) in expectedExports do
    unless getExportNameFor? env name == some symbol do
      throwError "Required verified export {name} must map to {symbol}"
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    let fromTrustedModule := match env.getModuleIdxFor? name with
      | none => false
      | some idx =>
        let root := moduleNames[idx.toNat]!.getRoot
        root == `Init || root == `Std || root == `Lean
    if !fromTrustedModule || (`Tamarin).isPrefixOf (privateToUserName name) then
      checked := checked + 1
      if let some symbol := getExportNameFor? env name then
        unless expectedExports.contains (name, symbol) do
          throwError "Unapproved project export {name} maps to {symbol}"
      if let some replacement := Compiler.getImplementedBy? env name then
        throwError "{name} has unchecked implemented_by replacement {replacement}"
      if isExtern env name then
        throwError "{name} has unchecked extern implementation"
      if let some initializer := getInitFnNameFor? env name then
        throwError "{name} has unchecked runtime initializer {initializer}"
      if info.isUnsafe then
        throwError "{name} is an unsafe project declaration"
      for ax in ← collectAxioms name do
        unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
          throwError "{name} depends on unapproved axiom {ax}"
  if checked == 0 then
    throwError "No Tamarin declarations found by the axiom audit"
  logInfo m!"Axiom and executable-replacement audit passed for {checked} project declarations"
