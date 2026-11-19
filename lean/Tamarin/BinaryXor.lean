import Tamarin.XorFlatInvariant

/-! Shapes of the normalized images and observable value for a binary
sum in an exponent-two commutative group, represented by AC and rewriting. -/
namespace Tamarin.Rewriting.BinaryXor
variable {sig : Signature}
abbrev Table := FreshXor.Flat.Table

inductive Shape where
  | disjoint | unitLeft | unitRight | same | leftContains | rightContains | overlap
  deriving DecidableEq, Repr

def Shape.images (sh : Shape) (T : Table sig) (h i j : Term sig) : Term sig × Term sig × Term sig :=
  match sh with
  | .disjoint => (i,j,.ac T.f i j)
  | .unitLeft => (T.zero,j,j)
  | .unitRight => (i,T.zero,i)
  | .same => (h,h,T.zero)
  | .leftContains => (.ac T.f h i,h,i)
  | .rightContains => (h,.ac T.f h j,j)
  | .overlap => (.ac T.f h i,.ac T.f h j,.ac T.f i j)

def Good (T : Table sig) (t : Term sig) := HasSort t .msg ∧ Normal T.R t

structure Instance (T : Table sig) (a b out : Term sig) (sh : Shape) : Prop where
  witnesses : ∃ h i j : Term sig, Good T h ∧ Good T i ∧ Good T j ∧
    EquivB a (sh.images T h i j).1 ∧ EquivB b (sh.images T h i j).2.1 ∧ EquivB out (sh.images T h i j).2.2

end Tamarin.Rewriting.BinaryXor
