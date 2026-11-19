import TamarinCI
import Tamarin.FiniteOccurs
import Tamarin.RigidAllocation

namespace Tamarin.RigidAllocationTests
open Pairing (PTerm PSubst signature)

private def box (t : PTerm) : PTerm := .free (.other 80 1) (fun _ => t)

-- The offending occurrence may be buried below AC, C, and free symbols.
-- The extra residual may itself be any term, including an open one.
example (x : Variable) (r : PTerm) (σ : PSubst) :
    let a : PTerm := .ac 1 (.comm 2 r (box (.var x))) r
    ¬ EquivB (σ.image x) (σ.apply a) ∧ ¬ EquivB (σ.image x) (.ac 0 r (σ.apply a)) := by
  dsimp only
  have h : FiniteOccurs.Proper x (.ac 1 (.comm 2 r (box (.var x))) r : PTerm) :=
    ⟨Or.inl (Or.inr ⟨0, rfl⟩), by intro e; cases e⟩
  exact ⟨FiniteOccurs.not_equiv h σ, FiniteOccurs.not_equiv_ac_swap h σ 0 r⟩

example (x : Variable) : ¬ FiniteOccurs.Proper x (.var x : PTerm) := fun h => h.2 rfl

-- If the allocated rigid child contains the flexible variable assigned to it,
-- both the singleton and positive-remainder orientation fail the occurs check.
example (t r : PTerm) : ¬ EquivB t (box t) ∧ ¬ EquivB t (.ac 0 r (box t)) := by
  constructor <;> intro e
  all_goals
    have h := e.eval_eq (weightModel signature) (fun _ => 1)
    simp [Model.eval, box] at h <;> omega

-- Aliasing x and z changes x+y=z+a to a forced singleton y=a.
example (x y a : PTerm) (σ : PSubst) :
    EquivB (σ.apply (.ac 0 x y)) (σ.apply (.ac 0 x a)) ↔ EquivB (σ.apply y) (σ.apply a) :=
  ⟨EquivB.ac_cancel_left (sig := signature) 0, fun h => EquivB.ac_congr (sig := signature) 0 (.refl _) h⟩

-- Sorting is independent of numeric IDs: a Fresh variable cannot absorb
-- two Msg factors, regardless of the variable names or the chosen witnesses.
example (v : Variable) (hv : v.sort = .fresh) (σ : PSubst) (a b : PTerm) :
    ¬ EquivB (σ.image v) (.ac 0 a b) := by
  intro e
  have h := Term.rootSort_le (σ.sorted v)
  rw [Term.rootSort_equiv e, hv] at h
  cases h

-- A replacement may reverse the enumeration and choose different positive
-- names independently in each branch, including the largest unsigned ID.
example : RigidAllocation.PacketCorrect (fun _ =>
    #[RigidAllocation.longY 9 8, RigidAllocation.shortY 18446744073709551615,
      RigidAllocation.longX 8 9, RigidAllocation.shortX 42]) := by
  intro _
  refine ⟨42, 18446744073709551615, 8, 9, 9, 8, ?_⟩
  dsimp only; decide

private abbrev msg (id : Nat) : Variable := ⟨id,.msg⟩
-- The matched occurrence is the middle B. Its two identical neighbors
-- survive in their original order, with the caller's correlated tail.
private def pivot : ACPivot.Query signature where
  f := 0
  x := msg 1
  y := msg 2
  a := box (.var (msg 3))
  b := .atom (8,.msg)
  bs := [.atom (9,.msg),.atom (8,.msg)]
  tail := [⟨.var (msg 2),.var (msg 3)⟩]

example : ACPivot.Packet.interpret pivot (msg 7) #[1,1,5,0,2,4,6] =
    some (⟨pivot.a,.atom (9,.msg)⟩ ::
      ⟨.var (msg 1),.ac 0 (.var (msg 2)) (.ac 0 pivot.b pivot.b)⟩ :: pivot.tail) := rfl

example : ACPivot.Packet.interpret pivot (msg 7) #[2,2,1,3,0,3,4,5,6] =
    some (⟨.var pivot.y,.ac 0 pivot.a (.var (msg 7))⟩ ::
      ⟨.var pivot.x,.ac 0 (.var (msg 7)) pivot.product⟩ :: pivot.tail) := rfl

example : ACPivot.Packet.interpret pivot (msg 7) #[2,1,1,0,4,7] = none := rfl
example : ACPivot.Packet.interpret pivot (msg 7) #[2,0,0,4,5,6] = none := rfl
example : ACPivot.Packet.interpret pivot (msg 7) #[2,1,1,0] = none := rfl

-- Pull the second equation to the front, reverse its orientation and
-- regroup the wide side with the open operand at the end.
private def reversedPivot : Equation signature :=
  ⟨.ac 0 pivot.product (.var pivot.y), .ac 0 pivot.a (.var pivot.x)⟩
private def original : Problem signature := pivot.tail ++ [reversedPivot]

private theorem reordered : ACPivot.Presentation pivot original := by
  apply ACPivot.Presentation.of_flatten reversedPivot
  · exact List.Perm.swap ..
  · right
    exact ⟨List.Perm.swap _ _ [], List.perm_middle (l₁ := pivot.operands) (l₂ := [])⟩

example (answers : List PSubst) (h : CompleteSet pivot.problem answers) :
    CompleteSet original answers := reordered.complete h

private abbrev ambient : Variable := ⟨1,.fresh⟩
private abbrev sample : RigidAllocation.Query signature where
  f := 0
  x := msg 1
  y := msg 2
  z := msg 3
  a := box (.var ambient)
  xy := by decide
  xz := by decide
  yz := by decide
  sx := rfl
  sy := rfl
  sz := rfl
  sa := .free _ _ (fun _ => .widen (.var _) .fresh_msg)
  outside := by
    rintro v ⟨_, h⟩
    change v = ambient at h
    subst v; decide
  factor := fun _ => rfl

private theorem unobserved (v : Variable)
    (h : v ≠ msg 1 ∧ v ≠ msg 2 ∧ v ≠ msg 3 ∧ v ≠ ambient) : ¬ sample.problem.Occurs v := by
  rw [sample.occurs]
  rintro (hx | hy | hz | ⟨_, ha⟩)
  · exact h.1 hx
  · exact h.2.1 hy
  · exact h.2.2.1 hz
  · exact h.2.2.2 ha

private def slots (_flip shared : Bool) : sample.Slots shared where
  u := msg 83
  v := msg 84
  su := rfl
  sv := rfl
  distinct := fun _ => by decide
  outsideU := unobserved _ (by decide)
  outsideV := unobserved _ (by decide)

-- The mathematical fragment includes a nonground rigid tree. Its ambient
-- variable shares an index with x but has a different sort. Every branch
-- preserves that variable and its correlation with the copy under the box.
example : CompleteSet sample.problem (sample.answers slots) := sample.complete slots

example (flip shared : Bool) :
    let σ := sample.answer flip shared (slots flip shared)
    σ.image ambient = .var ambient ∧ σ.apply (box (.var ambient)) = box (.var ambient) :=
  ⟨sample.at_a_var flip shared _ ⟨0, rfl⟩, sample.apply_a flip shared _⟩

-- Witness indices may coincide with caller indices of another sort. Full
-- variable identities still have to avoid the caller in either orientation.
private def reserved : List Variable := [⟨83,.fresh⟩, ambient, msg 7]
example (reversed : Bool) :
    (Outcome.complete (sample.answers slots)).CorrectIn (sample.problemOriented reversed) reserved :=
  sample.correctIn slots reversed reserved (fun _ _ => by change msg 83 ∉ reserved ∧ msg 84 ∉ reserved; decide)

example : ¬ FreshFor sample.problem [msg 83] (sample.answer false true (slots false true)) := by
  intro fresh
  exact fresh sample.x ((sample.occurs _).mpr (Or.inl rfl)) (msg 83)
    (Or.inr rfl) (unobserved _ (by decide)) (by simp)

-- An empty row cannot stand for a missing residual. A compact branch uses
-- a different pattern with all three images present.
example (slot : UInt64 → Variable) : RigidAllocation.decodeArm sample slot #[#[], #[1], #[1]] = none := rfl

private abbrev Bag := Nat × Nat
private abbrev Assignment := Bag × Bag × Bag

private def add (u v : Bag) : Bag := (u.1 + v.1, u.2 + v.2)
private def size (u : Bag) := u.1 + u.2

private def bags (bound : Nat) : List Bag :=
  (List.range (bound + 1)).flatMap fun a =>
    ((List.range (bound + 1 - a)).filter fun b => 0 < a + b).map fun b => (a, b)

/-- Independent denotation of the equation, via multiplicity of each atom. -/
private def expected (domain : List Bag) (a : Bag) : List Assignment :=
  domain.flatMap fun x => domain.flatMap fun y =>
    (domain.filter fun z => add x y == add z a).map fun z => (x,y,z)

-- Each positive slot denotes one nonempty multiset for the entire arm.
-- A literal is always interpreted through the reserved slot zero.
private def environments (domain : List Bag) : List UInt64 → List (List (UInt64 × Bag))
  | [] => [[]]
  | k :: ks => (environments domain ks).flatMap fun env => domain.map fun b => (k,b) :: env

private def evalRow (literal : Bag) (env : List (UInt64 × Bag)) (row : List UInt64) : Option Bag :=
  row.foldlM (init := (0,0)) fun total slot => do
    let value ← if slot == 0 then some literal else env.lookup slot
    return add total value

private def decoded (packet : Array (Array (Array UInt64))) (literal : Bag)
    (domain : List Bag) (bound : Nat) : IO (Std.HashSet Assignment) := do
  let mut actual := ∅
  for arm in packet do
    let [x, y, z] := arm.toList.map Array.toList | throw (IO.userError s!"expected three rows: {arm}")
    if x.isEmpty || y.isEmpty || z.isEmpty then throw (IO.userError s!"empty AC term: {arm}")
    let slots := ((x ++ y ++ z).filter (· != 0)).eraseDups
    -- The concrete ABI permits two branch-local witnesses, with arbitrary IDs.
    if slots.length > 2 then throw (IO.userError s!"too many witness slots: {arm}")
    for env in environments domain slots do
      let some a := evalRow literal env x | throw (IO.userError s!"bad x row: {x}")
      let some b := evalRow literal env y | throw (IO.userError s!"bad y row: {y}")
      let some c := evalRow literal env z | throw (IO.userError s!"bad z row: {z}")
      if size a ≤ bound && size b ≤ bound && size c ≤ bound then actual := actual.insert (a,b,c)
  return actual

def run : IO Unit := do
  let bound := 6
  let domain := bags bound
  let mut compared := 0
  let mut solutions := 0
  for literal in [(1,0), (0,1)] do
    let oracle := expected domain literal
    for reverse in [false, true] do
      let packet := Executable.rigidAllocation reverse
      let actual ← decoded packet literal domain bound
      unless actual.size == oracle.length && oracle.all actual.contains do
        throw (IO.userError s!"reverse={reverse}, literal={literal}, missing={oracle.find? (!actual.contains ·)}, expected={oracle.length}, actual={actual.size}, packet={packet}")
      compared := compared + domain.length ^ 3
      solutions := solutions + actual.size
  unless compared == 78732 && solutions > 0 do throw (IO.userError "incomplete allocation corpus")
  IO.println s!"{compared} bounded assignments, {solutions} solutions across both rigid factors and equation orientations"

end Tamarin.RigidAllocationTests

def main : IO Unit := Tamarin.RigidAllocationTests.run
