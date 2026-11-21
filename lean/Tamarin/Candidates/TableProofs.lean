import TamarinRuntime.Candidates.Table
import Tamarin.CheckedVariantsPacket
import Tamarin.CheckedReductionPacket

namespace Tamarin.TableCandidateProofs

theorem reduction : GeneralReductionWire.Correct TableCandidate.reduce := GeneralReductionWire.correct

theorem malformed : GeneralVariantsWire.Malformed TableCandidate.variants := by
  intro ds ns es roots fuel bad
  simp [TableCandidate.variants, GeneralVariantsWire.run, bad]

/-- Every binding row represents a genuine variant of the decoded original tuple,
including when the caller supplied a noncanonical table. -/
theorem sound : GeneralVariantsWire.Sound TableCandidate.variants := by
  intro ds ns es roots d rs q fuel decoded
  simp only [TableCandidate.variants,GeneralVariantsWire.run,decoded]
  split
  · next accepted =>
      cases found : GeneralVariants.run (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm) fuel.toNat with
      | none =>
        dsimp only
        split <;> first | exact .inl rfl | exact .inr (.inl rfl)
      | some rows =>
        dsimp only
        have scope := (CheckedReduction.rangeBound_iff _).mp (Bool.and_eq_true_iff.mp accepted).1
        cases check : GeneralVariants.replay (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm) fuel.toNat rows with
        | retry => exact .inr (.inl rfl)
        | conflict => exact .inl rfl
        | ready =>
          cases packet : TableAmbient.emit q rows with
          | none => exact .inr (.inl rfl)
          | some out =>
            have sound := GeneralVariants.sound_on_success found
            exact .inr (.inr ⟨rows,by simpa [packet] using TableAmbient.emit_correct packet,sound,
              GeneralVariants.replay_reconstructs scope sound check,fun can => GeneralVariants.correct scope can found⟩)
  · exact .inl rfl

/-- A canonical table yields a complete reply or a retry, including when an
intermediate family cannot be packed. -/
theorem progress : GeneralVariantsWire.Progress TableCandidate.variants := by
  intro ds ns es roots d rs q fuel decoded bound can
  simp only [TableCandidate.variants,GeneralVariantsWire.run,decoded,(CheckedReduction.rangeBound_iff _).mpr bound,
    GeneralVariants.nonvariable can,Bool.and_self,ite_true]
  cases found : GeneralVariants.run (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm) fuel.toNat with
  | none => exact .inr ⟨by simp [GeneralVariants.no_conflicting_rules bound can],.inl rfl⟩
  | some rows =>
    dsimp only
    cases check : GeneralVariants.replay (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm) fuel.toNat rows with
    | conflict => exact (GeneralVariants.replay_no_conflict bound can _ _ _ check).elim
    | retry => exact .inr ⟨rfl,.inr ⟨rows,rfl,.inl check⟩⟩
    | ready =>
      cases packet : TableAmbient.emit q rows with
      | none => exact .inr ⟨rfl,.inr ⟨rows,rfl,.inr packet⟩⟩
      | some out => exact .inl ⟨rows,by simpa [packet] using TableAmbient.emit_correct packet,GeneralVariants.correct bound can found⟩

end Tamarin.TableCandidateProofs
