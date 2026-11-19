import Tamarin.ACSortedBagSearch

open Tamarin.Matching
open ACBagSearch (Rows)
open ACSortedBagSearch (Limits)

private def wide : Rows := [([0,1], (List.range 64).map Nat.toUInt64)]

set_option maxRecDepth 4096 in
example : ACBagSearch.Within wide := by
  refine ⟨by decide,by decide,by decide,by decide,?_⟩
  intro a ha
  refine ⟨1,?_,by decide⟩
  have bounded : ∀ b ∈ wide.flatMap Prod.snd, ∀ r ∈ wide, r.2.count b ≤ 1 := by decide
  exact bounded a ha

private def check (rows : Rows) (limits : Limits) (expected : Bool) : IO Unit := do
  unless ACSortedBagSearch.run rows limits == some expected do
    throw (IO.userError s!"wrong sorted AC decision for {rows}, {limits}; expected {expected}")

/-- Independent, exhaustive assignments to both keys. The small reference
subjects never contain more than two copies of either possible factor. -/
private def reference (rows : Rows) (limits : Limits) : Bool :=
  let bags : List (List UInt64) := (List.range 3).flatMap fun i =>
    (List.range 3).map fun j => List.replicate i 7 ++ List.replicate j 9
  bags.any fun x => bags.any fun y =>
    let image k := if k == 0 then x else y
    rows.all fun (keys,target) => decide ((keys.flatMap image).Perm target) && keys.all fun k =>
      !(image k).isEmpty && limits.all fun (j,allowed) =>
        k != j || match image k with | [a] => allowed.contains a | _ => false

def main : IO Unit := do
  -- A full enumeration would have to examine 2^64 assignments.
  check wide [(0,[63])] true
  check wide [(0,[64])] false
  check wide [(0,[])] false
  check wide [(0,[17,23]),(0,[23,31])] true
  check wide [(0,[17]),(0,[23])] false
  check wide [(0,[17]),(1,[23])] false
  check wide [(99,[])] true
  -- A repeated key is replayed once per occurrence and retains the same
  -- single factor in every row. Distinct narrow keys can select the same ID.
  check [([0,0,1],[7,7,9]),([1,0],[9,7])] [(0,[7]),(1,[9])] true
  check [([0,0,1],[7,7,9]),([1,0],[9,9])] [(0,[7]),(1,[9])] false
  check [([0,1],[7,7])] [(0,[7]),(1,[7])] true
  check [([0],[7,7])] [(0,[7])] false
  check [([0],[7,9])] [(0,[7,9])] false
  check [([0],[])] [(0,[7])] false
  check [] [(0,[])] true
  let patterns : List (List UInt64) := [[],[0],[1,1],[0,1],[0,0,1]]
  let subjects : List (List UInt64) := [[],[7],[9,7],[7,7,9],[9,9]]
  let rows := patterns.flatMap fun lhs => subjects.map (lhs,·)
  let restrictions : List Limits := [[],[(0,[])],[(0,[7])],[(1,[7,9])],[(0,[7,9]),(1,[9])],
    [(0,[7,9]),(0,[7]),(2,[])]]
  for a in rows do
    for b in rows do
      for lim in restrictions do
        check [a,b] lim (reference [a,b] lim)
  IO.println "Typed AC bag decisions: 3,750 exhaustive constrained two-row cases and 64-factor existence"
