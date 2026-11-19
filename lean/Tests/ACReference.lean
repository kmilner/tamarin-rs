import Tamarin.ACReferenceBranch

namespace Tamarin.ACReferenceTests
open ACSystem

private abbrev sig : Signature where
  FreeSym := Nat
  arity := fun _ => 1
  CSym := Nat
  ACSym := Nat
  Atom := Nat
  inputSort := fun _ _ => .msg
  outputSort := fun _ => .msg
  cSort := fun _ => .msg
  acSort := fun _ => .msg
  atomSort := fun _ => .pub

private def v (i : Nat) : Variable := ⟨i,.msg⟩
private abbrev f : sig.ACSym := 0
private def twice : Row := ⟨⟨v 0,[v 0]⟩,⟨v 1,[]⟩⟩
private def balanced : Row := ⟨⟨v 0,[v 1]⟩,⟨v 2,[v 3]⟩⟩

#guard (Reference.solve f [] (by decide) []).length == 1
#guard (Reference.solve f [twice,⟨twice.rhs,twice.lhs⟩] (by decide) [v 2]).any fun σ =>
  match σ.image (v 0) with
  | .var w => ![v 0,v 1,v 2].contains w && σ.image (v 1) == .ac f (.var w) (.var w)
  | _ => false
#guard (Reference.solve f [twice, ⟨⟨v 1,[v 1]⟩,⟨v 0,[]⟩⟩] (by decide) []).isEmpty
#guard (Reference.solve f [balanced] (by decide) []).length == 7

-- A repeated open operand across two syntactically different presentations.
-- Observe a variable present only in an old binding and keep a sibling equation.
private def h : Term sig := .free 3 fun _ => .var (v 5)
private def left : Term sig := .ac f h (.atom 2)
private def right : Term sig := .ac f (.atom 2) h
private def selected : Problem sig := [⟨left,right⟩,⟨right,left⟩]
private def pending : Problem sig := [⟨.var (v 12),.atom 2⟩]
private def bound : Substitution sig :=
  .binding (v 6) (.var (v 30)) (.var _)
private theorem sorted : OperandBatch.Reference.SortedAt f selected := by
  have sl : HasSort left .msg := Term.checkSort_sound _ _ (by decide)
  have sr : HasSort right .msg := Term.checkSort_sound _ _ (by decide)
  intro e he
  rcases List.mem_cons.mp he with rfl | tail
  · exact ⟨sl,sr⟩
  · obtain rfl := List.mem_singleton.mp tail
    exact ⟨sr,sl⟩
private def children :=
  OperandBatch.Reference.splitProblem f selected sorted pending [v 6] [v 40] bound

-- Equal occurrences use the same column. A tautological matrix assigns
-- one independent parameter per operand, and both equations share it.
#guard match children with
  | [[a,b,p]] =>
    a.rhs == h && b.rhs == .atom 2 && p.lhs == .var (v 12) && p.rhs == .atom 2 &&
      a.lhs != b.lhs && [a,b].all fun e =>
        match e.lhs with | .var w => w.id > 40 | _ => false
  | _ => false

end Tamarin.ACReferenceTests
