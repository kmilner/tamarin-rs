import TamarinRuntime.Interface
import TamarinRuntime.Algorithm
import TamarinRuntime.FlatMatch

namespace Tamarin.RuntimeCandidate

/-- Candidate-owned selection. Changing either operation requires updating
its proofs in Tamarin.CandidateProofs before CI can accept the candidate. -/
@[inline] def backend : FlatACBackend where
  equal := fun lhs rhs => Executable.classify lhs.toList rhs.toList
  residual := fun tail rhs => (Executable.residual tail.toList rhs.toList).toArray

@[inline] def pairing : PairingBackend where
  variants := fun hasProjection => if hasProjection then 3 else 1
  project := fun first => if first then 1 else 2

@[inline] def reflexive : ReflexiveBackend where
  solve := fun recognized => if recognized then 2 else 0

/-- Enumerate assignments using one subject atom per variable. -/
def singletons (rhs : List UInt64) : Nat → List (List (List UInt64))
  | 0 => [[]]
  | n + 1 =>
    let rest := singletons rhs n
    rhs.flatMap fun atom => rest.map ([atom] :: ·)

def previousSlot : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

/-- Number of uses of each query-local variable. Dropping slot zero also
renumbers the remaining slots for the next recursive step. -/
def weights : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, occ => occ.count 0 :: weights n (occ.filterMap previousSlot)

/-- Each image uses its length in subject positions on every occurrence.
Enumerate only assignments whose total length fills the remaining subject. -/
def fitting (images : List (Nat × List UInt64)) : List Nat → Nat → List (List (List UInt64))
  | [], room => if room = 0 then [[]] else []
  | w :: ws, room => images.flatMap fun row =>
    let cost := w * row.1
    if cost ≤ room then (fitting images ws (room - cost)).map (row.2 :: ·) else []

/-- Use the earliest occurrence of the first atom. A subsequence beginning
with that atom can always use the new head, even for interleaved duplicates. -/
def images : List UInt64 → List (List UInt64)
  | [] => [[]]
  | a :: as =>
    let tail := images as
    tail.filter (fun row => row.head? != some a) ++ tail.map (a :: ·)

def partitionMatch (n : Nat) (occ : List Nat) (tail rhs : List UInt64) : List (List (List UInt64)) :=
  let domain := (images rhs).filter (fun row => !row.isEmpty)
  let sized := domain.map fun row => (row.length, row)
  (fitting sized (weights n occ) (rhs.length - tail.length)).filter fun rows =>
    decide ((FlatMatchSearch.expand rows occ ++ tail).Perm rhs)

/-- AC has no unit. When the subject just fits, each observed image is a
singleton. The export contract also covers malformed occurrence tables. -/
def flatMatch (n : Nat) (occ : List Nat) (tail rhs : List UInt64) : List (List (List UInt64)) :=
  if ∀ i ∈ occ, i < n then
    if occ.length + tail.length > rhs.length then []
    else if occ.length + tail.length = rhs.length ∧ ∀ i ∈ List.range n, i ∈ occ then
      (singletons rhs.eraseDups n).filter fun rows => decide ((FlatMatchSearch.expand rows occ ++ tail).Perm rhs)
    else partitionMatch n occ tail rhs
  else partitionMatch n occ tail rhs

@[inline] def flatMatcher : FlatMatchBackend where
  run := flatMatch

/-- Rows bind the two observed variables in input order; 0 is an opaque
branch-local slot, independent of both request-local atom IDs. -/
def sharedOffset (a b : UInt64) : Array (Array (Array UInt64)) :=
  #[#[#[b, 0], #[a, 0]], #[#[b], #[a]]]

/-- For x+y=z+a distribute the one rigid occurrence into x or y. The
two longer branches retain its nonempty remainder as a separate witness. -/
def rigidAllocation (_reversed : Bool) : Array (Array (Array UInt64)) :=
  #[#[#[0], #[1], #[1]], #[#[1], #[0], #[1]],
    #[#[0, 1], #[2], #[1, 2]], #[#[2], #[0, 1], #[1, 2]]]

/-- Zero is the unknown head of a variable. After a rigid clash the
other orientation can still solve the equation. -/
def commOrientations (a b c d : UInt64) (priority : UInt8) : UInt8 :=
  let compatible := fun x y : UInt64 => x == 0 || y == 0 || x == y
  let direct := compatible a c && compatible b d
  let crossed := compatible a d && compatible b c
  if direct then
    if !crossed || priority == 1 || priority == 3 then 1
    else if priority == 2 then 2 else 3
  else if crossed then 2 else 0

def xorOdd (count : UInt64) : Bool := count % 2 == 1

/-- The diagonal is always reachable; the irreducible open XOR also occurs
when the input variables are distinct. -/
def xorBranches (same : Bool) : UInt8 := if same then 2 else 3

/-- An AC rewrite may consume any submultiset. Exclude a rule only when
one of its required rigid heads occurs nowhere among the subject factors. -/
def excludeACFactors (rows : Array (Array UInt64)) (heads : Array UInt64) : Bool :=
  rows.all fun row => row.any fun k => k != 0 && !heads.contains k

def constructorVariant (roots used : Array UInt64) : Bool :=
  used.all (fun id => !(roots.contains id))

/-- Match the occurrence table for one concrete root reduction. Agreement at
each repeated key is required even when that key is absent from the RHS. -/
def reduceRuleSlot (slot : UInt64) (keys subjects : Array UInt64) : Array UInt64 :=
  let rows := keys.toList.zip subjects.toList
  if keys.size = subjects.size ∧ ∀ row ∈ rows, rows.lookup row.1 = some row.2 then
    match rows.lookup slot with
    | some value => #[value]
    | none => #[]
  else #[]

/-- Root specialization requires independent flexible arguments and a
consistent slot for each captured ambient term. -/
def groundVariant (holes anchors deps : Array UInt64) (rigid : Bool) : UInt8 :=
  if rigid && decide holes.toList.Nodup && decide anchors.toList.Nodup &&
      holes.all (fun v => !(deps.contains v)) then 3 else 0

/-- Merge two sorted occurrence inventories, keeping exactly the unpaired
occurrences. Each iteration consumes at least one input head. -/
def cancelSorted (lhs rhs leftRev rightRev : List UInt64) : List UInt64 × List UInt64 :=
  match lhs, rhs with
  | [], ys => (leftRev.reverse, rightRev.reverseAux ys)
  | xs, [] => (leftRev.reverseAux xs, rightRev.reverse)
  | x :: xs, y :: ys =>
    if x = y then cancelSorted xs ys leftRev rightRev
    else if x < y then cancelSorted xs (y :: ys) (x :: leftRev) rightRev
    else cancelSorted (x :: xs) ys leftRev (y :: rightRev)
termination_by lhs.length + rhs.length

def cancelCommon (lhs rhs : Array UInt64) : Array (Array UInt64) :=
  let (l, r) := cancelSorted (lhs.toList.mergeSort Executable.atomLE)
    (rhs.toList.mergeSort Executable.atomLE) [] []
  #[l.toArray, r.toArray]

/-- A zero pattern word imposes no constraint on that argument. -/
def excludeRoot (rows : Array (Array UInt64)) (args : Array UInt64) : Bool :=
  rows.all fun row => row.size == args.size &&
    !row.isEqv args (fun required actual => required == 0 || required == actual)

end Tamarin.RuntimeCandidate
