import Tamarin.MaskedSelection
import Tamarin.IndivisibleOperandProjection
import Tamarin.ProjectionCompletion

namespace Tamarin.MaskedOperands
open ACBasis Homogeneous

abbrev Kernel := UInt64 → UInt64 → Array (Array UInt64) → Option Answers

def Input (width bits : UInt64) (sides : Array (Array UInt64)) :=
  OperandCounts.Admitted width sides ∧ bits.toNat < 2^width.toNat ∧
    GraphUnification.Nontrivial (OperandUnification.matrix width sides).toList

/-- The wire verdict, term semantics and completion domain are independent of
generator order, search strategy and choice of witness ordinals. -/
structure Correct (solver : Kernel) : Prop where
  valid : ∀ w bits sides raw, solver w bits sides = some raw → Input w bits sides ∧
    AnswerProjection.Shape w raw ∧ ∀ a ∈ raw.toList, IndivisibleOperands.keeps (IndivisibleOperands.wordMask w bits) a = true
  semantic : ∀ {sig : Signature} [DecidableEq sig.ACSym] (f : sig.ACSym) (w bits : UInt64)
    (rows : List (OperandBatch.Row w.toNat)) (used : ∀ i, i ∈ OperandBatch.used rows)
    (term : Fin w.toNat → Term sig) (typed : ∀ i, HasSort (term i) (sig.acSort f)),
    IndivisibleOperands.SoundMask f term (IndivisibleOperands.wordMask w bits) →
    ∀ {selected : Problem sig}, OperandBatch.Represents f term rows selected →
    ∀ (pending original : Problem sig), original.Perm (selected ++ pending) →
    ∀ raw, solver w bits (OperandBatch.sides rows) = some raw →
    ∀ observe bindings, ProjectedOperands.Interprets f rows used term typed pending original raw observe bindings
  completes : ∀ w bits sides, Input w bits sides → ∀ rs,
    readRows w.toNat (OperandUnification.matrix w sides).toList = some rs →
    Within rs → (generate rs).length ≤ 64 →
    (OutputWithin (generate rs) ∨ WorkBound (generate rs) (IndivisibleOperands.wordMask w bits) ≤ 131072) →
    (solver w bits sides).isSome

private theorem emitted {w bits sides raw} (result : run w bits sides = some raw) :
    Input w bits sides ∧ IndivisibleOperands.Emitted w bits (OperandUnification.matrix w sides) raw := by
  cases count : OperandCounts.run w sides with
  | none => simp [run,count] at result
  | some m =>
    obtain ⟨admitted, eq⟩ := (OperandCounts.run_correct ..).mp count
    change m = OperandUnification.matrix w sides at eq
    subst m
    generalize hm : OperandUnification.matrix w sides = m at count ⊢
    by_cases input : bits.toNat < 2^w.toNat ∧ GraphUnification.hasConstraint m.toList = true
    · refine ⟨⟨admitted,input.1,(GraphUnification.hasConstraint_iff _).mp (hm ▸ input.2)⟩,?_⟩
      cases read : readRows w.toNat m.toList with
      | none => simp [run,count,read,input.1,input.2,guard] at result
      | some rs =>
        cases found : boundedBasis rs with
        | none => simp [run,count,read,found,input.1,input.2,guard] at result
        | some gs =>
          have eq := (bounded_spec _).1 _ found
          subst gs
          generalize hg : generate rs = gs at found ⊢
          by_cases small : gs.length ≤ 64
          · refine ⟨rs,read,by simpa only [hg] using small,?_⟩
            rw [hg]
            cases sel : takeSelections gs (wordMask w.toNat bits) 131072 with
            | none =>
              by_cases fit : fitsOutput gs = true <;>
                simp [run,count,read,found,input.1,input.2,small,sel,fit,guard,failure] at result
              exact result.symm
            | some pair =>
              obtain ⟨rest,js⟩ := pair
              have h : (js.map (arm gs)).toArray = raw := by
                simpa [run,count,read,found,input.1,input.2,small,sel,guard] using result
              rw [←h,takeSelections_eq _ _ sel]
              simp [emit,List.filter_map,Function.comp_def]
              rfl
          · simp [run,count,read,found,input.1,input.2,small,guard,failure] at result
    · simp [run,count,input,guard,failure] at result

/-- A replaceable solver with this contract supplies a complete packet to the
same checked projection consumed by the C shim. -/
theorem projection_total {solver project} (checked : Correct solver)
    (projection : AnswerProjection.Correct project) {w bits sides raw}
    (result : solver w bits sides = some raw) : (project w raw).isSome := by
  have admitted : AnswerProjection.Admitted w raw := ⟨(checked.valid _ _ _ _ result).2.1,
    AnswerProjection.keys_fit _⟩
  rw [(projection w raw _).mpr ⟨admitted,rfl⟩]
  rfl

theorem run_correct : Correct run where
  valid := by
    intro w bits sides raw result
    obtain ⟨input,rs,_,_,out⟩ := emitted result
    refine ⟨input,⟨input.1.1,input.1.2.1,?_⟩,?_⟩ <;> intro a ha <;> rw [out] at ha
    · simp at ha
      exact ProjectionCompletion.shaped_emit (generate rs) a (by simpa using ha.1)
    · simp at ha
      exact ha.2
  semantic := by
    intro sig _ f w bits rows used term typed mask selected layout pending original partition raw result observe bindings
    obtain ⟨input,out⟩ := emitted result
    exact IndivisibleOperands.interprets f w bits rows used term typed mask layout pending original partition
      input.1 input.2.2 out observe bindings
  completes := by
    intro w bits sides input rs read within small budget
    have count := (OperandCounts.run_correct w sides _).mpr ⟨input.1,rfl⟩
    change OperandCounts.run w sides = some (OperandUnification.matrix w sides) at count
    have found := (bounded_spec rs).2 within
    generalize hg : generate rs = gs at found small budget
    have active : GraphUnification.hasConstraint (OperandUnification.matrix w sides).toList = true := (GraphUnification.hasConstraint_iff _).mpr input.2.2
    cases sel : takeSelections gs (wordMask w.toNat bits) 131072 with
    | some result =>
      obtain ⟨remaining,js⟩ := result
      simp [run,count,read,active,input.2.1,found,small,sel,guard]
    | none =>
      rcases budget with legacy | bound
      · have fits : fitsOutput gs = true := by
          simpa [fitsOutput,OutputWithin,Coverage.packetFits_iff] using legacy
        simp [run,count,read,active,input.2.1,found,small,sel,fits,guard]
      · have possible := takeSelections_complete gs (wordMask w.toNat bits) bound
        simp [sel] at possible

end Tamarin.MaskedOperands
