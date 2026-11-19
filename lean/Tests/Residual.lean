import Tamarin.CancelCommonCandidateProofs
import Tamarin.ResidualRigidWorklist
import Tamarin.ResidualVariableWorklist
import TamarinRuntime

/-! A different elimination order can meet the same fixed contract. This
candidate always inspects the right operand first, including equal-sort aliases. -/
namespace ResidualAudit
open Tamarin Residual

private def reverseCode (code : UInt8) := if code = 3 then 4 else if code = 4 then 3 else code

private def rightFirst : Kernel := fun l r e h fl fr o =>
  reverseCode (step r l e h fr fl o)

private theorem flipInput {s : Signature} {a b : Term s} {l r h fl fr o}
    (i : Input a b l r h fl fr o) : Input b a r l h fr fl o := by
  cases i with
  | vars => exact .vars ..
  | left v t rigid typed o occ => exact .right v _ rigid typed o occ
  | right v t rigid typed o occ => exact .left v _ rigid typed o occ
  | different a b ra rb ne => exact .different _ _ rb ra ne.symm
  | atom => exact .atom ..
  | free => exact .free ..
  | comm => exact .comm ..
  | ac => exact .ac ..

private theorem flipAction {s : Signature} {a b : Term s} {code} (h : Justified code a b) :
    Justified (reverseCode code) b a := by
  cases h with
  | defer => exact .defer ..
  | clash bad => exact .clash (fun σ he => bad σ he.symm)
  | discard e => exact .discard e.symm
  | bindLeft v t typed absent => exact .bindRight v _ typed absent
  | bindRight v t typed absent => exact .bindLeft v _ typed absent
  | positional => exact .positional ..
  | orientations => exact .orientations ..

example : Correct rightFirst := by
  intro s a b l r h fl fr o i e identical sound
  obtain ⟨ok, completes⟩ := step_correct (flipInput i) e (fun he => identical he.symm)
    (fun he => (sound he).symm)
  refine ⟨flipAction ok, fun he => ?_⟩
  have nz := completes he
  unfold rightFirst reverseCode
  split
  · decide
  · split
    · decide
    · exact nz

example : step 0 0 false false true true false = 3 ∧
    rightFirst 0 0 false false true true false = 4 := by decide

/-- The outer binding x ↦ slot can remain observable after x and slot
disappear from the worklist. If a later split reuses slot for an inner
operand fixed to an atom, the outer answer loses its free parameter. -/
example {s : Signature} (x slot : Variable) (atom : s.Atom)
    (bindings : Substitution s) (image : bindings.image x = .var slot) :
    Denotes (· = x) [] bindings bindings ∧
    ¬ Denotes (· = x) [⟨.var slot, .atom atom⟩] bindings bindings := by
  constructor
  · refine ⟨.identity, by simp [Problem.Solves], fun v _ => ?_⟩
    rw [Substitution.apply_identity]
    exact .refl _
  · rintro ⟨δ, solves, observe⟩
    have outer := observe x rfl
    rw [image] at outer
    have inner : EquivB (δ.image slot) (.atom atom) := solves _ (List.mem_singleton_self _)
    have heads := (outer.trans inner).head_eq
    contradiction

end ResidualAudit

-- Witness IDs are local, so an unrelated variable can have the largest word.
-- Being the opposite root gives identity. Being under a constructor is a cycle.
#guard Tamarin.Executable.residualVariable false 7 2 0 2 #[7] == 2
#guard Tamarin.Executable.residualVariable false 7 2 2 2 #[18446744073709551615, 7, 7] == 1
#guard Tamarin.Executable.residualVariable true 7 2 4 2 #[18446744073709551615] == 4
#guard Tamarin.Executable.residualVariable false 7 1 0 2 #[8] == 4
#guard Tamarin.Executable.residualVariable false 7 1 0 0 #[8] == 1
#guard Tamarin.Executable.residualVariable false 7 4 1 4 #[] == 3
#guard Tamarin.Executable.residualVariable true 7 2 0 2 #[] == 255
#guard Tamarin.Executable.residualVariable false 7 2 1 2 #[0] == 255
#guard Tamarin.Executable.residualVariable false 7 2 0 1 #[7] == 255
#guard Tamarin.Executable.residualVariable false 7 2 5 2 #[] == 255

namespace ResidualVariableAudit
open Tamarin

private def x : Variable := ⟨17, .fresh⟩
private def y : Variable := ⟨17, .msg⟩
private def put (v : Variable) := WholeProblem.sortWord v.sort

-- The actual export binds y to x. Resuming suspended entries can reorder
-- them, but applies this binding to the entire remaining stack and all earlier images.
example {s : Signature} (observed : Variable → Prop) (p resumed : Problem s) (h : p.Perm resumed)
    (θ ρ : Substitution s) :
    let β := Substitution.binding y (.var x) (.widen (.var x) Subsort.fresh_msg)
    Residual.Denotes observed (⟨.var x,.var y⟩ :: p.substitute θ) θ ρ ↔
      Residual.Denotes observed (resumed.substitute (β.compose θ)) (β.compose θ) ρ := by
  have transition := ResidualVariable.worklist (solve := Executable.residualVariable)
    ResidualVariable.run_correct x (.var y) (.var y) put (by
      intro w live equal
      have hw : w = y := by simpa [Term.variables] using live
      subst w
      contradiction) #[2] (List.Perm.refl _) false observed p resumed h θ ρ
  change ResidualVariable.Transition (Executable.residualVariable false 1 1 0 2 #[2])
    (.var x) (.var y) observed p resumed θ ρ at transition
  have bindRight : Executable.residualVariable false 1 1 0 2 #[2] = 4 := by decide +kernel
  rw [bindRight] at transition
  obtain ⟨key, eq, typed, solved⟩ := transition
  cases eq
  exact solved

end ResidualVariableAudit


namespace ResidualRigidAudit
open Tamarin
private abbrev step := Executable.residualRigid

-- The same numeric head can belong to two different categories.
#guard step 1 17 #[] 2 17 #[] == 1
#guard step 2 17 #[4,5] 2 23 #[4,5] == 1
#guard step 2 17 #[4,5] 2 17 #[5,4] == 5
#guard step 2 17 #[] 2 17 #[] == 2
#guard step 3 0 #[7,9] 3 0 #[9,7] == 6
#guard step 4 0 #[1,1,2] 4 0 #[1,2,2] == 0
#guard step 4 18446744073709551615 #[1,1,2] 4 18446744073709551615 #[1,1,2] == 2
#guard step 0 0 #[] 0 0 #[] == 255
#guard step 1 0 #[1] 2 1 #[] == 255
#guard step 3 0 #[1] 3 0 #[1] == 255
#guard step 4 0 #[1] 4 0 #[1] == 255
#guard step 2 0 #[1] 2 0 #[1,2] == 255

private def x {s : Signature} : Term s := .var ⟨0,.msg⟩
private def y {s : Signature} : Term s := .var ⟨1,.msg⟩
private def child {s : Signature} : Term s → UInt64
  | .var v => v.id.toUInt64
  | _ => 0
private def operand {s : Signature} (id : UInt64) : Term s := if id = 1 then y else x

-- The real classifier and cancellation kernel reduce 2x+y = x+2y to x=y,
-- retaining every pending equation and all observations of prior bindings.
example {s : Signature} (f : s.ACSym) (observed : Variable → Prop) (p : Problem s)
    (θ ρ : Substitution s) :
    Residual.Denotes observed (⟨.ac f x (.ac f x y), .ac f x (.ac f y y)⟩ :: p) θ ρ ↔
    Residual.Denotes observed (⟨x,y⟩ :: p) θ ρ := by
  let a : ResidualRigid.View s := .ac f x x [y]
  let b : ResidualRigid.View s := .ac f x y [y]
  have h := ResidualRigid.worklist (solve := Executable.residualRigid) ResidualRigid.run_correct a b
    (fun _ => 0) (fun _ _ => rfl) child (fun i => some (operand i)) (by
      intro t ht
      have ht : t = x ∨ t = y := by
        simp [a,b,ResidualRigid.View.args] at ht
        grind
      rcases ht with rfl | rfl <;> rfl) observed p θ ρ
  change ResidualRigid.Transition 0 a b observed p θ ρ at h
  obtain ⟨g,hg,_,cancel⟩ := h
  change Head.ac f = Head.ac g at hg
  obtain rfl := Head.ac.inj hg
  obtain ⟨ls,rs,packet,eq⟩ := cancel Executable.cancelCommon CancelCommonCandidateProofs.correct
    operand #[0,0,1] #[0,1,1] rfl rfl
  have expect : Executable.cancelCommon #[0,0,1] #[0,1,1] = #[#[0],#[1]] := by cbv
  rw [expect] at packet
  have rows := congrArg (fun arr : Array (Array UInt64) => arr.toList.map Array.toList) packet
  change [[0], [1]] = [ls,rs] at rows
  simp only [List.cons.injEq, and_true] at rows
  obtain ⟨rfl,rfl⟩ := rows
  simpa [Residual.withFactors, ACRepresentation.decode, ACRepresentation.fold, operand, a, b, ResidualRigid.View.term] using eq

end ResidualRigidAudit
