import Tamarin.GraphUnification
import Tamarin.AnswerProjection
import Tamarin.OperandUnification

namespace Tamarin.ProjectionCompletion
open Homogeneous

theorem shaped_emit {width : UInt64} (gs : List (ACBasis.Vec width.toNat))
    (a : Arm) (ha : a ∈ (emit gs).toList) :
    a.size = width.toNat ∧ ∀ row ∈ a.toList, row ≠ #[] := by
  simp only [emit, List.toList_toArray, List.mem_map, Coverage.coveringSelections_eq] at ha
  obtain ⟨js, hj, rfl⟩ := ha
  have cov : ∀ i, ∃ j ∈ js, 0 < gs.get j i := of_decide_eq_true (List.mem_filter.mp hj).2
  refine ⟨by simp [arm], ?_⟩
  intro row hrow
  simp only [arm, Array.toList_ofFn, List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  obtain ⟨j, hmem, hpos⟩ := cov i
  have member : j.val.toUInt64 ∈ js.flatMap (fun k => List.replicate (gs.get k i) k.val.toUInt64) := by
    exact List.mem_flatMap.mpr ⟨j, hmem, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩
  intro empty
  have := congrArg Array.toList empty
  simp_all

private theorem shaped {width : UInt64} {m out} (h : solve width m = some out) :
    AnswerProjection.Shape width out := by
  by_cases size : (0 < width ∧ width ≤ 32) ∧ m.size ≤ 128
  · cases rd : readRows width.toNat m.toList with
    | none => simp [solve, rd, guard, size] at h
    | some rs =>
      cases basis : answerBasis rs with
      | none => simp [solve, rd, basis, guard, size] at h
      | some gs =>
        by_cases fits : fitsOutput gs = true
        · have emitted : emit gs = out := by simpa [solve, rd, basis, fits, guard, size] using h
          exact ⟨size.1.1, size.1.2, emitted ▸ shaped_emit gs⟩
        · simp [solve, rd, basis, fits, guard, size] at h; contradiction
  · simp [solve, guard, size] at h; contradiction

abbrev Project := UInt64 → Answers → Option Answers

/-- Every completed matrix answer, including a proved clash, survives projection. -/
def MatrixTotal (solver : UInt64 → Matrix → Option Answers) (project : Project) : Prop :=
  ∀ n m out, solver n m = some out → (project n out).isSome

def GraphTotal (solver : GraphUnification.Kernel) (project : Project) : Prop :=
  ∀ n sym s ds ns es out, solver n sym s ds ns es = some out → (project n out).isSome

theorem matrix_total {project : Project} (verified : AnswerProjection.Correct project) :
    MatrixTotal solve project := by
  intro n m out returned
  have admitted : AnswerProjection.Admitted n out := ⟨shaped returned, AnswerProjection.keys_fit _⟩
  have projected := (verified n out _).mpr ⟨admitted, rfl⟩
  rw [projected]
  rfl

theorem graph_total {project : Project} (verified : AnswerProjection.Correct project) :
    GraphTotal GraphUnification.run project := by
  intro n sym s ds ns es out returned
  cases built : GraphMatrix.build n sym s ds ns es with
  | none => simp [GraphUnification.run, GraphUnification.runWith, built] at returned
  | some m =>
    cases active : GraphUnification.hasConstraint m.toList with
    | false => simp [GraphUnification.run, GraphUnification.runWith, built, active, guard, failure] at returned
    | true =>
      apply matrix_total verified n m out
      simpa [GraphUnification.run, GraphUnification.runWith, built, active, guard] using returned

/-- Reconciliation receives a projected packet for every completed operand search. -/
def OperandTotal (run : OperandUnification.Kernel) (project : Project) : Prop :=
  ∀ width sides out, run width sides = some out → (project width out).isSome

theorem operand_total {run solve project} (refines : OperandUnification.Refines run solve)
    (total : MatrixTotal solve project) : OperandTotal run project := by
  intro width sides out h
  exact total width _ out ((refines ..).mp h).2.2

end Tamarin.ProjectionCompletion
