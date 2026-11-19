namespace Tamarin.BinaryCancellationCandidate

/-- A flattened AC rule. Slot zero denotes the declared constant. Positive
slots denote rule-local message variables shared by both sides. -/
private structure Rule where
  lhs : List Nat
  rhs : List Nat

private abbrev Row := List Nat × List Nat × List Nat

/-- Every distribution of the specialized rule factors across the two
query variables is an ordinary AC unifier when both sides are nonempty. -/
private def partitions : List Nat → List (List Nat × List Nat)
  | [] => [([], [])]
  | x :: xs => (partitions xs).flatMap fun (l,r) => [(x::l,r),(l,x::r)]

/-- Also try expanding one rule variable by an independent factor.
Repeated occurrences must expand together in the left and right sides. -/
private def narrow (rule : Rule) : List Row :=
  let vars := (rule.lhs.filter (· != 0)).eraseDups
  let fresh := rule.lhs.foldl max 0 + 1
  (none :: vars.map some).flatMap fun split =>
    let apply := fun (xs : List Nat) =>
      xs.flatMap fun x => if split == some x then [x,fresh] else [x]
    let value := apply rule.rhs
    (partitions (apply rule.lhs)).filterMap fun (l,r) =>
      if l.isEmpty || r.isEmpty then none else some (l,r,value)

/-- Give one bit each to shared, left-only and right-only factors. A row
with two witnesses in the same region is subsumed by a single witness.
The declared constant represents the empty bag only in normal images. -/
private def packet (row : Row) : Option (Array UInt64) := do
  let (l,r,v) := row
  let role := fun (n : Nat) =>
    if l.contains n then (if r.contains n then 1 else 2) else 4
  let vars := ((l ++ r).filter (· != 0)).eraseDups
  guard ((vars.map role).eraseDups.length == vars.length)
  let encode := fun (xs : List Nat) => do
    if xs == [0] then return (0 : UInt64)
    guard (!xs.isEmpty && xs.all vars.contains && xs.eraseDups.length == xs.length)
    return (xs.map role).sum.toUInt64
  return #[← encode l, ← encode r, ← encode v]

/-- The identity and root narrowings for the validated active presentation.
The term-level completeness theorem certifies this bounded search for these
equations. The exported contract only constrains the resulting family. -/
def rows : Array (Array UInt64) :=
  let rules : List Rule := [⟨[1,1],[0]⟩, ⟨[1,0],[1]⟩, ⟨[1,1,2],[2]⟩]
  let identity : Row := ([1],[2],[1,2])
  ((identity :: rules.flatMap narrow).filterMap packet).eraseDups.toArray

/-- For distinct Fresh images the message can contain any subset of the two
atomic factors and an independent remainder. Adding both Fresh inputs toggles
their two bits. When the Fresh images coincide, they cancel for every message. -/
def mixedRows : Array (Array UInt64) :=
  let separate := (List.range 8).map fun n =>
    let message := n.toUInt64
    #[1, 2, message, message ^^^ 3]
  (#[#[1, 1, 4, 4]] ++ separate.toArray)

end Tamarin.BinaryCancellationCandidate
