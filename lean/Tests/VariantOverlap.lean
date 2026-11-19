import TamarinRuntime

namespace Tamarin.VariantOverlapTests
open Whole Executable

private def decls : Array UInt64 :=
  #[2,0,1,2,2, 3,1,2,2,2,2, 4,2,2,2,2,2]

private def nodes : Array (Array UInt64) :=
  #[#[0,0,2],#[0,1,2],#[1,0,2],#[1,1,2],#[2,0,0],#[2,0,1],
    #[3,1,0,1],#[4,2,0,1],#[4,2,0,0],#[4,2,1,1]]

-- Inputs x_left = y_right determine common contexts, including repeated uses.
#guard variantOverlapAgrees decls nodes #[0,1,4,5]
#guard variantOverlapAgrees decls nodes #[0,1,8,9]
#guard variantOverlapAgrees decls nodes #[0,0,1,1,6,6]
-- The same variable ID in two independent output rows may take different values.
#guard !variantOverlapAgrees decls nodes #[0,0]
#guard !variantOverlapAgrees decls nodes #[0,1,0,0]
#guard !variantOverlapAgrees decls nodes #[0,0,1]
#guard !variantOverlapAgrees decls nodes #[100,100]
#guard variantOverlapAgrees decls nodes #[2,2]
-- Equality of corresponding unary free applications determines their arguments.
#guard variantOverlapAgrees decls nodes #[4,5,0,1]
-- A commutative application may have been matched in the opposite orientation.
#guard !variantOverlapAgrees decls nodes #[6,6,0,0]
#guard !variantOverlapAgrees decls nodes #[7,7,0,0]

-- The two output positions are determined under different AC symbols.
-- Each pair of observations recovers one value by 2*(a+b) - (a+2b).
private def twoHeads : Array UInt64 :=
  #[4,0,2,2,2,2, 4,1,2,2,2,2, 2,2,2,2,2,2]
private def twoHeadNodes : Array (Array UInt64) :=
  #[#[0,0,2],#[0,1,2],#[0,2,2],#[0,3,2],
    #[4,0,0,1],#[4,0,0,1,1],#[4,1,2,3],#[4,1,2,3,3],#[2,2,0,2]]
#guard variantOverlapAgrees twoHeads twoHeadNodes #[4,4,5,5,6,6,7,7,8,8]
#guard !variantOverlapAgrees twoHeads twoHeadNodes #[4,4,5,5,6,6,8,8]

-- Instantiate the original graph into a finite part of the free/C/AC algebra.
-- Both variables range independently over two distinct atoms in each row.
private def ground (tree : Tree) (bits : Nat) : Tree := match tree with
  | .leaf 0 id _ => .leaf 1 ((bits / 2^id.toNat) % 2).toUInt64 2
  | .leaf k id s => .leaf k id s
  | .app k id xs => .app k id (xs.map fun a => ground a bits)

def stress : IO Unit := do
  let some ds := declarations decls.toList | throw <| IO.userError "invalid declarations"
  let some raw := decodeNodes ds nodes | throw <| IO.userError "invalid node table"
  let concrete := (Array.range 4).map fun bits => raw.map fun t => (canonical (ground t bits)).key
  let mut masks := #[]
  for i in [:nodes.size] do
    for j in [:nodes.size] do
      let mut mask : Nat := 0
      for l in [:4] do
        for r in [:4] do
          if concrete[l]![i]! == concrete[r]![j]! then mask := mask ||| (1 <<< (4*l+r))
      masks := masks.push mask
  let mut accepted := 0
  for input in [:masks.size] do
    let l := (input / nodes.size).toUInt64
    let r := (input % nodes.size).toUInt64
    for output in [:masks.size] do
      let a := (output / nodes.size).toUInt64
      let b := (output % nodes.size).toUInt64
      if variantOverlapAgrees decls nodes #[l,r,a,b] then
        unless masks[input]! &&& masks[output]! == masks[input]! do
          throw <| IO.userError s!"agreement fails on independent assignments for {l},{r} ⇒ {a},{b}"
        accepted := accepted + 1
  IO.println s!"Checked {masks.size * masks.size} overlap implications on 16 independent assignment pairs ({accepted} accepted)."

end Tamarin.VariantOverlapTests

def main := Tamarin.VariantOverlapTests.stress
