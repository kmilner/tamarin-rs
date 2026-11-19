import TamarinRuntime.ACBagAnswers

namespace Tamarin.Matching.ACSortedBagSearch
open ACBagSearch ACBagAnswers

/-- Every entry restricts a key to a singleton drawn from its allowed factors.
Repeated entries for a key intersect their whitelists. -/
abbrev Limits := List (UInt64 × List UInt64)

def narrow (limits : Limits) (k : UInt64) := limits.any fun rule => rule.1 == k

def allows (limits : Limits) (k a : UInt64) := limits.all fun rule =>
  rule.1 != k || rule.2.contains a

def options (ks restricted compatible : List UInt64) (columns : List (List Nat)) : List (List UInt64) :=
  let valid := columns.filter fun col => restricted.all fun k =>
    let n := atKey ks col 0 k
    n == 0 || (n == 1 && compatible.contains k)
  (valid.map fun col => ks.filter fun k => 0 < atKey ks col 0 k).eraseDups

/-- The only cross-factor information is which keys already have a value.
Narrow keys may receive a factor from at most one layer. -/
def supports (limits : Limits) (ks restricted : List UInt64) : Batch → List (List UInt64)
  | [] => [[]]
  | (a,cols) :: rest =>
    let tail := supports limits ks restricted rest
    if tail.isEmpty then [] else
    let compatible := restricted.filter fun k => allows limits k a
    let localOptions := options ks restricted compatible cols
    (localOptions.flatMap fun now =>
      (tail.filter fun prior => restricted.all (fun k => !(now.contains k && prior.contains k))).map
        fun prior => ks.filter fun k => now.contains k || prior.contains k).eraseDups

def run (rows : Rows) (limits : Limits) : Option Bool := do
  let (ks,as) ← inventories rows
  let restricted := ks.filter (narrow limits)
  let layers := as.map fun a => (a,choices rows ks a)
  return (supports limits ks restricted layers).any fun s => ks.all s.contains

end Tamarin.Matching.ACSortedBagSearch
