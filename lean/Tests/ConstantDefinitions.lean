import Tamarin.DefinitionCertificate

namespace Tamarin.ConstantDefinitions.Tests

private abbrev sig : Signature where
  FreeSym := Nat
  CSym := Unit
  ACSym := Unit
  Atom := Nat
  arity f := if f = 2 then 1 else 0
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .msg

private def key : Term sig := .free 0 Fin.elim0
private def second : Term sig := .free 1 Fin.elim0
private def a : Term sig := .atom 10
private def b : Term sig := .atom 20
private def add : Term sig → Term sig → Term sig := .ac ()
private def swap : Term sig → Term sig → Term sig := .comm ()
private def wrap (t : Term sig) : Term sig := .free 2 (fun _ => t)
private def defs : Problem sig :=
  [⟨key,add a (add a b)⟩,⟨key,add (add b a) a⟩,⟨second,swap a b⟩,⟨second,swap b a⟩]

#guard accepts defs
#guard !accepts ([⟨key,add a a⟩,⟨key,add a b⟩] : Problem sig)
#guard !accepts ([⟨key,add a (wrap second)⟩,⟨second,b⟩] : Problem sig)
#guard !accepts ([⟨key,.var ⟨22,.msg⟩⟩] : Problem sig)
#guard !accepts ([⟨wrap a,b⟩] : Problem sig)
#guard !accepts ([⟨swap a b,b⟩] : Problem sig)

-- A competitor can invalidate the class even if it is never picked first.
-- The contradiction here uses only the pairwise mathematical contract.
example : ¬ Presentation ([⟨key,a⟩,⟨key,b⟩] : Problem sig) := by
  intro spec
  have eq := spec.coherent ⟨key,a⟩ (by simp) ⟨key,b⟩ (by simp) rfl
  cases eq.head_eq

example : Presentation defs := (accepts_iff defs).mp (by decide_cbv)

-- Compare reordered wide definitions and reject a missing copy without
-- constructing the AC partitions of either right side.
private def wide (xs : List Nat) : Term sig := xs.foldr (fun i t => add (.atom i) t) a
private def operands := List.range 64
#guard accepts ([⟨key,wide operands⟩,⟨key,wide operands.reverse⟩] : Problem sig)
#guard !accepts ([⟨key,wide operands⟩,⟨key,wide (operands.drop 1)⟩] : Problem sig)

-- Even an ill-sorted surrounding application retains its rigid Node variable.
private def node : Term sig := .var ⟨12,.node⟩
private def input := wrap (add key (swap node second))
private def output := wrap (add (add a (add a b)) (swap node (swap a b)))
example : MaudeOperations.ReductionReply (Rewriting.ruleRoot defs) input output :=
  reductionReply (rs := defs) (by decide_cbv) (by decide_cbv) input

example : MaudeOperations.Reference sig defs :=
  DefinitionCertificate.reference ((accepts_iff defs).mp (by decide_cbv))
    ((DefinitionCertificate.sorted_iff ((accepts_iff defs).mp (by decide_cbv))).mp (by decide_cbv))

end Tamarin.ConstantDefinitions.Tests
