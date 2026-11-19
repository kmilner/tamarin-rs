import TamarinRuntime
import Tamarin.DHTowerPacket

/-! An oracle for small DH exponent products, independent of the signed-list
classification. Use ordinary bounded integer multiplicities for two atoms.
Check real packet programs against concrete base and output exponents. -/
open Tamarin Tamarin.Rewriting Tamarin.Rewriting.DHTower.Packet Tamarin.Rewriting.DHPeer

private abbrev Vec := Int × Int
private def plus (x y : Vec) : Vec := (x.1+y.1, x.2+y.2)
private def minus (x : Vec) : Vec := (-x.1,-x.2)

private def exponent (xs : List Vec) (p n : Vec) : Image → Option Vec
  | .var .pos => some p
  | .var .neg => some n
  | .var (.factor i) => xs[i]?
  | .mul a b => return plus (← exponent xs p n a) (← exponent xs p n b)
  | .inv a => (exponent xs p n a).map minus
  | _ => none

private def positive (x : Vec) : Vec := (max 0 x.1,max 0 x.2)
private def bag (xs : List Vec) := xs.foldl plus (0,0)

/-- Match the base image and check that the row consumes precisely the
available inverse factors. Each successful replay must yield the real sum. -/
private def fits (xs : List Vec) (old : Vec) (t : Image) : Bool := Id.run do
  let .pow (.var .base) e := t | return false
  let out := plus old (bag xs)
  if e == .var .pos then return positive (minus old) == positive (minus out)
  let p := positive old
  let n := positive (minus out)
  let rec has (v : Arg) : Image → Bool
    | .var k => k == v
    | .pow a b | .mul a b => has v a || has v b
    | .inv a => has v a
    | _ => false
  -- A residual variable is a nonempty product.
  if has .pos e != (p != (0,0)) || has .neg e != (n != (0,0)) then return false
  return exponent xs p n e == some old

private def leaves : Image → List Image
  | .mul a b => leaves a ++ leaves b
  | x => [x]

/-- Interpreting each occurrence as a distinct generator exposes invented
factors even when the two-atom assignment oracle would alias two positions.
A normalized exponent contains at most one inverse product. Every incoming
generator can occur once on its negative side and neither witness can move
between sides. Product association and the order of factors are immaterial. -/
private def admissible (width : Nat) : Image → Bool
  | .var .peer | .neutral | .pow (.var .base) (.var .pos) => true
  | .pow (.var .base) exp => Id.run do
    let mut pos := false
    let mut inverse := false
    for t in leaves exp do
      match t with
      | .var .pos =>
        if pos then return false
        pos := true
      | .inv magnitude =>
        if inverse then return false
        inverse := true
        let mut neg := false
        let mut selected : List Nat := []
        for term in leaves magnitude do
          match term with
          | .var .neg =>
            if neg then return false
            neg := true
          | .var (.factor i) =>
            if i ≥ width || selected.contains i then return false
            selected := i :: selected
          | _ => return false
        if selected.isEmpty then return false
      | _ => return false
    return inverse
  | _ => false

def main : IO Unit := do
  -- With a repeated occurrence or a nested inverse an extra row can be
  -- invisible to an existential coverage check that retains the good rows.
  let f : Image := .var (.factor 0)
  for bad in [Expr.pow (.var .base) (.inv (.mul f f)), .pow (.var .base) (.inv (.inv (.inv f))),
      .pow (.var .base) (.mul (.var .neg) (.inv f)), .pow (.var .base) (.inv (.var (.factor 9)))] do
    if admissible 2 bad then throw <| IO.userError "unexpected extra tower row accepted"
  let mut rowChecks := 0
  for width in [2:9] do
    let some rows := Executable.dhTowerImages width.toUInt64 | throw <| IO.userError "missing width"
    for r in rows do
      let some t := decode r | throw <| IO.userError "bad packet"
      unless admissible width t do throw <| IO.userError s!"spurious row at width {width}: {r}"
      rowChecks := rowChecks + 1
  let mut checks := 0
  for width in [2:7] do
    let some rows := Executable.dhTowerImages width.toUInt64 | throw <| IO.userError "missing width"
    let some images := rows.toList.mapM decode | throw <| IO.userError "bad packet"
    for mask in [:2^width] do
      let xs := (List.range width).map fun i => if mask.testBit i then ((0,1) : Vec) else (1,0)
      for a in [:11] do
        for b in [:11] do
          let old : Vec := (Int.ofNat a - 5,Int.ofNat b - 5)
          unless images.any (fits xs old) do throw <| IO.userError s!"uncovered: {xs}, {old}"
          checks := checks + 1
  IO.println s!"{checks} signed DH tower assignments covered and {rowChecks} emitted rows checked against independent generators"
