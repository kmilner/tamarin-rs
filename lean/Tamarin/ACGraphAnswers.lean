import TamarinRuntime.ACGraphAnswers
import Tamarin.ACRayPacket
import Tamarin.ACPrincipalRay

namespace Tamarin.GraphAnswers
open Homogeneous

private theorem previous : Homogeneous.Correct (RayPacket.solve @ACBasis.PrincipalRay.run) :=
  RayPacket.correct ACBasis.PrincipalRay.run_sound

theorem returned {w m out} (hit : solve w m = some out) :
    RayPacket.solve @ACBasis.PrincipalRay.run w m = some out ∨ Homogeneous.solveUpTo 64 w m = some out := by
  cases h : RayPacket.solve @ACBasis.PrincipalRay.run w m with
  | some a => exact .inl (by simpa [solve,h] using hit)
  | none =>
    right
    by_cases wide : 32 < w
    · simpa [solve,h,wide] using hit
    · simp [solve,h,wide] at hit

/-- Every completed route emits a full family in the shape accepted by projection. -/
theorem emitted {w m out} (hit : solve w m = some out) :
    0 < w ∧ w ≤ RayPacket.maxWidth ∧ ∃ gs : List (ACBasis.Vec w.toNat), emit gs = out := by
  rcases returned hit with prev | wide
  · cases old : Homogeneous.solve w m with
    | some a =>
      have eq : a = out := by simpa [RayPacket.solve,old] using prev
      obtain ⟨_,gs,bounds,_,_,_,em⟩ := solveUpTo_returned old
      exact ⟨bounds.1,UInt64.le_trans bounds.2.1 (by decide),gs,em.trans eq⟩
    | none =>
      obtain ⟨_,v,bounds,_,_,_,em⟩ := RayPacket.returned (by simpa [RayPacket.solve,old] using prev)
      exact ⟨bounds.1,bounds.2.1,[coordinates v],em⟩
  · obtain ⟨_,gs,bounds,_,_,_,em⟩ := solveUpTo_returned wide
    exact ⟨bounds.1,UInt64.le_trans bounds.2.1 (by decide),gs,em⟩

theorem principal (w m) (floor : RayPacket.Admitted @ACBasis.PrincipalRay.Within w m) :
    (solve w m).isSome := by
  have ok := RayPacket.completes ACBasis.PrincipalRay.run_sound ACBasis.PrincipalRay.run_complete w m floor
  simp [solve,ok]

theorem correct : CorrectUpTo 64 solve where
  malformed := by
    intro w m bad
    simp [solve,previous.malformed w m bad,(solveUpTo_correct 64).malformed w m bad]
  completes := by
    intro w m floor
    by_cases wide : 32 < w
    · simp [solve,wide,(solveUpTo_correct 64).completes w m floor]
    · have old : Homogeneous.Admitted w m := ⟨floor.1,UInt64.not_lt.mp wide,floor.2.2⟩
      simp [solve,previous.completes w m old]
  semantic := by
    intro s f rows avoid n fr m input out done w inj typed fresh
    rcases returned done with old|general
    · exact previous.semantic f rows avoid n fr m input out old w inj typed fresh
    · exact (solveUpTo_correct 64).semantic f rows avoid n fr m input out general w inj typed fresh

end Tamarin.GraphAnswers
