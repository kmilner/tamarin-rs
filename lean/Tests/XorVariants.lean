import TamarinCI

namespace Tamarin.XorVariantsTests
open Rewriting FreshXor
open Pairing (signature PTerm)

private def zero : PTerm := .free (.other 0 0) Fin.elim0
private def plus (a b : PTerm) : PTerm := .ac 0 a b
private def u : Variable := ⟨1,.msg⟩
private def v : Variable := ⟨2,.msg⟩
private def builtin : List (Equation signature) := [
  ⟨plus (.var u) (.var u),zero⟩,
  ⟨plus (.var u) zero,.var u⟩,
  ⟨plus (.var u) (plus (.var u) (.var v)),.var v⟩]

private def table : Table signature where
  rules := builtin
  f := 0
  fSort := rfl
  zero := zero
  zeroFree := ⟨_,_,rfl⟩
  zeroGround := fun _ ⟨i,_⟩ => Fin.elim0 i
  zeroSort := .free _ _ (fun i => Fin.elim0 i)
  zeroAbsent := by
    simp [zero,builtin,plus,ConstructorVariants.operators, ConstructorVariants.ruleHeads,
      ConstructorVariants.head,headModel,Model.eval,List.ofFn_zero]
    change ¬ (Head.free (.other 0 0) : Head signature) ∈ [.ac 0, .ac 0, .ac 0]
    simp
  apps := by intro r hr; simp [builtin] at hr; rcases hr with rfl | rfl | rfl <;> trivial
  param := u
  paramSort := rfl
  duplicate := List.mem_cons_self ..
  bucket := by
    intro r hr _
    simp [builtin] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨u,rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨u,v,rfl⟩))
  freeSort := by intro g; change SortId.msg ≠ .fresh; decide
  commSort := by intro g; change SortId.msg ≠ .fresh; decide
  acSort := by intro g; change SortId.msg ≠ .fresh; decide

private def query (same : Bool) : Query signature where
  table := table
  x := ⟨0,.fresh⟩
  y := ⟨if same then 0 else 1,.fresh⟩
  witness := ⟨2,.fresh⟩
  sx := rfl
  sy := rfl
  sw := rfl
  wx := by decide
  wy := by cases same <;> decide

-- With compound factors on both sides, an AC equality can hold even though
-- neither binary alignment works. The atomicity premise is essential.
example :
    let a : PTerm := .atom (0,.msg)
    let b : PTerm := .atom (1,.msg)
    let c : PTerm := .atom (2,.msg)
    EquivB (plus (plus a b) c) (plus a (plus b c)) ∧
      ¬ ((EquivB (plus a b) a ∧ EquivB c (plus b c)) ∨
         (EquivB (plus a b) (plus b c) ∧ EquivB c a)) := by
  intro a b c
  refine ⟨.ac_assoc .., ?_⟩
  rintro (⟨bad,_⟩ | ⟨_,bad⟩) <;> cases bad.head_eq

-- Evaluate observations under a finite valuation. Keeping equal summands in
-- a raw result distinguishes a missed XOR rewrite from the actual zero.
private inductive Value where
  | name (id : Nat) | zero | rawXor (lo hi : Nat) | invalid
  deriving BEq, Repr

private def observe (env : Variable → Nat) : PTerm → Value
  | .var w => .name (env w)
  | .free (.other 0 0) _ => .zero
  | .ac 0 (.var a) (.var b) =>
    .rawXor (min (env a) (env b)) (max (env a) (env b))
  | _ => .invalid

private def normal (x y : Nat) : Slot → Value
  | .left => .name x
  | .right => .name y
  | .sum => if x == y then .zero else .rawXor (min x y) (max x y)

private def packs : Nat → List (List Slot)
  | 0 => [[]]
  | n+1 => (packs n).flatMap fun r => [Slot.left, .right, .sum].map (· :: r)

def stress : IO Unit := do
  -- Compare with every function on these small finite domains. The oracle
  -- knows only the involution law and does not recursively build pairings.
  let rec maps (domain : List UInt64) : Nat → List (List UInt64)
    | 0 => [[]]
    | k + 1 => (maps domain k).flatMap fun tail => domain.map (· :: tail)
  for width in [1,2,3,4,5] do
    let domain := (List.range width).map Nat.toUInt64
    let some actual := Executable.xorMatchings width.toUInt64
      | throw (IO.userError s!"unsupported XOR width {width}")
    let expected := (maps domain width).filter fun row => domain.all fun i =>
      ((row[i.toNat]?).bind fun j => row[j.toNat]?) == some i
    unless expected.all (fun row => actual.contains row.toArray) &&
        actual.all (fun row => expected.contains row.toList) do
      throw (IO.userError s!"XOR choices disagree with the involution oracle at width {width}")
  let mut checked := 0
  for same in [false,true] do
    let q := query same
    let mask := Executable.xorBranches same
    for slots in ([1,2,3,4,5].flatMap packs).filter (·.contains .sum) do
      let answers := q.decode slots mask
      for arm in answers do
        let .name x := observe Variable.id (arm.subst.image q.x)
          | throw (IO.userError "left image lost its Fresh sort")
        let .name y := observe Variable.id (arm.subst.image q.y)
          | throw (IO.userError "right image lost its Fresh sort")
        unless arm.values.map (observe Variable.id) == slots.map (normal x y) do
          throw (IO.userError s!"unsound symbolic XOR tuple in mask {mask}")
      for x in [:4] do for y in [:4] do
        if same && x != y then continue
        let covers := answers.any fun arm => (List.range 4).any fun w =>
          let env := fun (var : Variable) => if var == q.x then x else if var == q.y then y else w
          observe env (arm.subst.image q.x) == .name x &&
            observe env (arm.subst.image q.y) == .name y &&
            arm.values.map (observe env) == slots.map (normal x y)
        unless covers do throw (IO.userError s!"lost solution {x},{y} in mask {mask}")
        checked := checked + 1
  IO.println s!"{checked} complete XOR tuples checked"

end Tamarin.XorVariantsTests

def main := Tamarin.XorVariantsTests.stress
