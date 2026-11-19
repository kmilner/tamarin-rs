import Std
namespace Tamarin.Matching.ACBagSearch

abbrev Rows := List (List UInt64 × List UInt64)
abbrev Column := UInt64 → Nat

def equations (rows : Rows) (a : UInt64) :=
  rows.map fun (keys,items) => (keys,items.count a)

def largest (eqs : List (List UInt64 × Nat)) := eqs.foldr (fun eq n => max eq.2 n) 0

/-- A coordinate can never exceed the total multiplicity required by a
row containing its key. Enumerate one rigid factor at a time. -/
def vectors (b : Nat) : List UInt64 → List Column
  | [] => [fun _ => 0]
  | k :: ks =>
    let tails := vectors b ks
    (List.range (b+1)).flatMap fun n => tails.map fun v => fun i => if i = k then n else v i

/-- Only the set of keys made nonempty by a local solution affects any
other rigid factor. Keep one copy of each such support. -/
def options (rows : Rows) (keys : List UInt64) (a : UInt64) : List (List UInt64) :=
  let eqs := equations rows a
  let good := (vectors (largest eqs) keys).filter fun v =>
    eqs.all fun (ks,n) => (ks.map v).sum == n
  (good.map fun v => keys.filter fun k => 0 < v k).eraseDups

def supports (rows : Rows) (keys : List UInt64) : List UInt64 → List (List UInt64)
  | [] => [[]]
  | a :: rest =>
    let tail := supports rows keys rest
    if tail.isEmpty then [] else
      ((options rows keys a).flatMap fun now => tail.map fun prior =>
        keys.filter fun k => now.contains k || prior.contains k).eraseDups

def run (rows : Rows) : Option Bool :=
  if rows.length ≤ 64 && (rows.map (fun r => r.1.length + r.2.length)).sum ≤ 4096 then
    let keys := (rows.flatMap Prod.fst).eraseDups
    let atoms := (rows.flatMap Prod.snd).eraseDups
    if keys.length ≤ 5 && atoms.length ≤ 128 then
      if atoms.all (fun a => (largest (equations rows a) + 1)^keys.length ≤ 256) then
        some ((supports rows keys atoms).any (fun support => keys.all support.contains))
      else none
    else none
  else none

end Tamarin.Matching.ACBagSearch
