import Tamarin.ProjectedOperands
import Tamarin.FlatAnswerIncidence
import TamarinRuntime

/-! A repeated compound operand shares x with a second column. The input groups
the sum differently from the occurrence packet, and the reader reverses factors. -/
namespace Tamarin.ProjectedOperandsTests
open OperandBatch Homogeneous

private def sig : Signature where
  FreeSym := Unit
  CSym := Empty
  ACSym := Unit
  Atom := Empty
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort := Empty.elim
  acSort _ := .msg
  atomSort := Empty.elim

private instance : DecidableEq sig.ACSym := inferInstanceAs (DecidableEq Unit)
private def x : Variable := ⟨4,.msg⟩
private def y : Variable := ⟨5,.msg⟩
private def z : Variable := ⟨6,.msg⟩
private def k : Variable := ⟨7,.msg⟩
private def hash : Term sig := .free () (fun _ => .var x)
private def lookup (i : Fin 3) : Term sig := if i = 0 then hash else if i = 1 then .var x else .var y
private theorem typed (i : Fin 3) : HasSort (lookup i) (sig.acSort ()) := by
  unfold lookup
  split
  · exact .free _ _ (fun _ => .var x)
  · split
    · exact .var x
    · exact .var y

private def rows : List (Row 3) := [(⟨0,[0,1]⟩,⟨2,[]⟩)]
private def eqn : Equation sig := ⟨.ac () (.ac () hash (.var x)) hash, .var y⟩
private def pendingEq : Equation sig := ⟨.var z, .var x⟩
private def retained : Substitution sig := .binding k (.var z) (.var z)
private theorem layout : Represents () lookup rows [eqn] := by
  apply Represents.cons
  · change [hash,hash,.var x].Perm [hash,.var x,hash]
    exact List.Perm.cons _ (List.Perm.swap _ _ [])
  · exact List.Perm.refl _
  · exact .nil

private def raw : Answers := #[#[#[1], #[0], #[0,1,1]]]
private def tagged : Answers := #[#[#[0,0], #[1,1], #[2,1,0,0]]]
private def order : ProjectedBindings.Order := ⟨List.reverse, List.reverse_perm⟩
private def name (i : UInt64) : Variable := ⟨i.toNat,.msg⟩
private def reconciled : Problem sig := [
  ⟨.var (name 0),hash⟩, ⟨.var (name 1),.var x⟩,
  ⟨.ac () (.var (name 0)) (.ac () (.var (name 0)) (.var (name 1))),.var y⟩]

-- These are the two public exports on a single completed worklist step.
example : Executable.operandUnify 3 (sides rows) = some raw := by decide +kernel
private theorem projected : Executable.projectAnswers 3 raw = some tagged := by
  apply (AnswerProjection.project_correct ..).mpr
  refine ⟨⟨?_, AnswerProjection.keys_fit _⟩, ?_⟩
  · unfold AnswerProjection.Shape
    decide
  · decide +kernel

-- Pin the branch constructed from column tags, exactly one local name per
-- live ordinal, every multiplicity, and the untouched pending equation.
example (ρ : Substitution sig) :
    Residual.Denotes (· ∈ [k]) [pendingEq,eqn] retained ρ ↔
    Residual.Denotes (· ∈ [k]) (reconciled ++ [pendingEq]) retained ρ := by
  have cert : ProjectedOperands.Correct Executable.operandUnify Executable.projectAnswers :=
    ProjectedOperands.correct (OperandUnification.run_refines OperandCounts.run_correct _)
      (OperandAbstraction.nested_lifting Homogeneous.solve_correct) AnswerProjection.project_correct
  have split := cert () 3 rows (by decide) lookup typed layout [pendingEq] [pendingEq,eqn]
    (List.Perm.swap _ _ []) raw (by decide +kernel) tagged projected
    [k] retained name order (fun _ _ _ _ h => UInt64.toNat_inj.mp (congrArg Variable.id h)) (by intros; rfl)
    (by
      intro j hj
      have inUse : ProjectedBindings.ordinals tagged = [0,1,1,0,0] := rfl
      have h : j = 0 ∨ j = 1 := by
        simp [inUse] at hj
        exact hj.elim Or.inl (fun h => h.elim Or.inr Or.inl)
      rcases h with rfl | rfl <;> decide)
  have output : ProjectedOperands.readArm lookup () name order tagged[0] = some reconciled := rfl
  change ProjectedOperands.readArm lookup () name order #[#[0,0], #[1,1], #[2,1,0,0]] = some reconciled at output
  simpa [tagged, output] using split.2 ρ

private def sample (a b c : Variable) : Nat → FlatAnswerIncidence.Image sig
  | 0 => .product () a a [b,c]
  | _ => .product () c b []

-- b and c have identical columns, yet remain separate witnesses, and a
-- occurs twice in one image. Relabel and reorder them all simultaneously.
example : (([x,y,z].map (FlatAnswerIncidence.column 2 (sample x y z))).Perm
    ([z,k,y].map (FlatAnswerIncidence.column 2 (sample y k z)))) := by decide
example : [x,y,z].map (FlatAnswerIncidence.column 2 (sample x y z)) =
    [(.msg,[0,0]),(.msg,[0,1]),(.msg,[0,1])] := by decide
example : FlatAnswerIncidence.column 2 (sample x y z) y ≠
    FlatAnswerIncidence.column 2 (sample x y y) y := by decide
example : FlatAnswerIncidence.column 2 (sample x y z) x ≠
    FlatAnswerIncidence.column 2 (sample ⟨x.id,.fresh⟩ y z) ⟨x.id,.fresh⟩ := by decide

end Tamarin.ProjectedOperandsTests
