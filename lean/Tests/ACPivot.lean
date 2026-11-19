import TamarinCI

/-! Compare the linked pivot equations to direct addition of two atom counts.
Neither the reference equation nor the evaluator uses the branch proof. -/
namespace Tamarin.ACPivotStress

private abbrev Bag := Nat × Nat

private def plus (a b : Bag) : Bag := (a.1 + b.1, a.2 + b.2)

private def sum (factors : List Bag) : Bag := factors.foldl plus (0,0)

private def atoms : List Bag := [(1,0),(0,1)]

private def products : List Bag := (List.range 4).flatMap fun a =>
  ((List.range (4 - a)).filter (fun b => 0 < a + b)).map fun b => (a,b)

private def vectors : Nat → List (List Bag)
  | 0 => [[]]
  | n + 1 => atoms.flatMap fun a => (vectors n).map (a :: ·)

private def holds (slots : Array Bag) (row : Array UInt64) : Option Bool := do
  let k :: size :: rest := row.toList | none
  let l := rest.take size.toNat
  let j :: r := rest.drop size.toNat | none
  guard (!l.isEmpty && !r.isEmpty)
  let get := fun (i : UInt64) => slots[i.toNat]?
  return (← get k) == sum (← l.mapM get) && (← get j) == sum (← r.mapM get)

def check : IO Unit := do
  let mut checked := 0
  let mut solutions := 0
  for n in [1:5] do
    let some rows := Executable.acPivot n.toUInt64 | throw (IO.userError "pivot deferred")
    for bs in vectors n do
      for a in atoms do
        for x in products do
          for y in products do
            let expected := plus x a == plus y (sum bs)
            let mut covered := false
            -- Any nonempty common remainder is a subbag of Y.
            for w in products do
              let slots := #[x,a,y,w] ++ bs.toArray
              for row in rows do
                let some hit := holds slots row | throw (IO.userError s!"invalid row {row}")
                covered := covered || hit
            unless covered == expected do
              throw (IO.userError s!"pivot disagrees on X={x}, A={a}, Y={y}, B={bs}")
            checked := checked + 1
            if covered then solutions := solutions + 1
  IO.println s!"{checked} AC pivot assignments checked, {solutions} solutions"

/-- With a single open variable, the selected occurrence supplies A and all
other occurrences must supply X. Compare that positional decoding against
the original equation for every two-atom input, including repeated factors. -/
def checkSingle : IO Unit := do
  let mut checked := 0
  for n in [2:7] do
    let some rows := Executable.openMatchSelect 1 n.toUInt64 | throw (IO.userError "selector deferred")
    for bs in vectors n do
      let observations ← rows.mapM fun row => do
        let some (a :: x) := row.toList.mapM (fun i => bs[i.toNat]?) |
          throw (IO.userError s!"invalid occurrence in {row}")
        return (a, sum x)
      for a in atoms do
        for p in [:n+1] do
          for q in [:n+1] do
            let x := (p,q)
            let expected := plus x a == sum bs
            unless observations.contains (a,x) == expected do
              throw (IO.userError s!"one-open pivot disagrees on X={x}, A={a}, B={bs}")
            checked := checked + 1
  IO.println s!"{checked} one-open AC pivot assignments checked"

private def term (id : Nat) : Pairing.PTerm := .var ⟨id,.msg⟩

private def count (env : Variable → Bag) : Pairing.PTerm → Bag
  | .var v => env v
  | .ac _ u v => plus (count env u) (count env v)
  | _ => (0,0)

private def ownerQuery (repeatOwner : Bool) : ACOwnerPivot.Query Pairing.signature where
  f := 0
  rigid := .var ⟨0,.fresh⟩
  loose := term 1
  first := term 2
  second := term 3
  rest := if repeatOwner then [term 2] else []
  tail := [⟨term 4,term 3⟩]

/-- Evaluate the actual decoded branch equations on a bounded two-colour
model. Both owners may contain positive excess. One owner can occur twice
and a separate pending equation observes the other owner's assignment. -/
def checkOwners : IO Unit := do
  let mut checked := 0
  for repeatOwner in [false,true] do
    let q := ownerQuery repeatOwner
    let some packet := Executable.openMatchSelect 1 q.operands.length.toUInt64 |
      throw (IO.userError "owner selector deferred")
    let arms := (OpenMatchSelect.decoded packet).flatMap (ACOwnerPivot.interpret q (fun _ => true) (fun _ => ⟨5,.msg⟩))
    for a in atoms do
      for b in products do
        for c in products do
          let total := if repeatOwner then sum [b,c,b] else plus b c
          let rest := (total.1 - a.1, total.2 - a.2)
          for x in [rest,plus rest (1,0)] do
            for d in [c,plus c (1,0)] do
              let expected := plus a x == total && d == c
              let hit := products.any fun w =>
                let env := fun (v : Variable) => ([a,x,b,c,d,w][v.id]?).getD (0,0)
                arms.any fun arm => arm.work.all fun e => count env e.lhs == count env e.rhs
              unless expected == hit do
                throw (IO.userError s!"owner split disagrees on A={a}, L={x}, B={b}, C={c}, D={d}, repeat={repeatOwner}")
              checked := checked + 1
  IO.println s!"{checked} AC owner splits with shared variables checked"

end Tamarin.ACPivotStress

def main : IO Unit := do
  Tamarin.ACPivotStress.check
  Tamarin.ACPivotStress.checkSingle
  Tamarin.ACPivotStress.checkOwners
