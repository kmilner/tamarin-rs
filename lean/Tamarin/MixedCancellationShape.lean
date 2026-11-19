import Tamarin.BinaryXorShapes

/-! Ternary cancellation with two Fresh operands and one Msg operand. -/
namespace Tamarin.Rewriting.MixedCancellation
open BinaryXor
variable {sig : Signature}

inductive Shape where
  | diagonal
  | separate (left right residual : Bool)
  deriving DecidableEq, Repr

def pick {α : Type} (flag : Bool) (a : α) : List α := if flag then [a] else []

def operands {α : Type} (l r tail : Bool) (a b m : α) : List α :=
  pick l a ++ pick r b ++ pick tail m

def Shape.images (sh : Shape) (T : Table sig) (a b m : Term sig) :
    Term sig × Term sig × Term sig × Term sig :=
  match sh with
  | .diagonal => (a,a,m,m)
  | .separate l r tail =>
    (a,b,T.value (operands l r tail a b m),T.value (operands (!l) (!r) tail a b m))

structure Instance (T : Table sig) (a b x out : Term sig) (sh : Shape) : Prop where
  witnesses : ∃ h i j, (HasSort h .fresh ∧ Normal T.R h) ∧
    (HasSort i .fresh ∧ Normal T.R i) ∧ Good T j ∧
    let p := sh.images T h i j
    EquivB a p.1 ∧ EquivB b p.2.1 ∧ EquivB x p.2.2.1 ∧ EquivB out p.2.2.2

end Tamarin.Rewriting.MixedCancellation
