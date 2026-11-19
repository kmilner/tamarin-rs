import TamarinRuntime.ACBagSearch

namespace Tamarin.Matching.ACBagAnswers
open ACBagSearch

abbrev Arm := List (List UInt64)
abbrev Batch := List (UInt64 × List (List Nat))
abbrev Pick := List (UInt64 × List Nat)

/-- Full local counts, retaining distinctions that a Boolean support mask may discard. -/
def choices (rows : Rows) (keys : List UInt64) (a : UInt64) : List (List Nat) :=
  ((balancedColumns rows keys a).map fun v => keys.map v).eraseDups

def product : Batch → List Pick
  | [] => [[]]
  | (a,columns) :: rest =>
    let tails := product rest
    columns.flatMap fun v => tails.map ((a,v) :: ·)

def atKey {α : Type} (ks : List UInt64) (vs : List α) (fallback : α) (k : UInt64) :=
  vs[ks.idxOf k]?.getD fallback

def decode (ks : List UInt64) (arm : Arm) (k : UInt64) : List UInt64 :=
  atKey ks arm [] k

def materialize (ks : List UInt64) (pick : Pick) : Arm :=
  ks.map fun k => pick.flatMap fun (a,col) => List.replicate (atKey ks col 0 k) a

def family (ks : List UInt64) (layers : Batch) : List Arm :=
  ((product layers).map (materialize ks)).filter fun arm => arm.all (!·.isEmpty)

/-- Charge the product after each individual column has been checked but
before generating any combinations. Each used key occurs in some row, so all
bags in one arm together fit in the sum of the subject occurrence counts. -/
def collect (rows : Rows) (ks as : List UInt64) : Option (List Arm) :=
  let layers := as.map fun a => (a,choices rows ks a)
  let count := (layers.map fun entry => entry.2.length).prod
  if count = 0 then some [] else
  let words := 1 + ks.length * (1 + as.length) + (rows.map fun r => r.2.length).sum
  if count ≤ 4096 && count * words ≤ 65536 then some (family ks layers)
  else none

def run (rows : Rows) : Option (List Arm) := do
  let (ks,as) ← inventories rows
  collect rows ks as

end Tamarin.Matching.ACBagAnswers
