import TamarinRuntime.Homogeneous

/-! Numeric signed-product expressions and the finite branch layouts used by
the semantic specification and the bounded in-process backend. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open ACBasis
variable {n : Nat}

inductive Expr (n : Nat) where
  | input (i : Fin n)
  | unit
  | mul (a b : Expr n)
  | inv (a : Expr n)

def add (a b : Vec n) : Vec n := fun i => a i + b i

def Expr.weights (negative : Fin n → Bool) : Expr n → Vec n × Vec n
  | .input i => if negative i then (fun _ => 0,spike i 1) else (spike i 1,fun _ => 0)
  | .unit => (fun _ => 0,fun _ => 0)
  | .inv a => (a.weights negative).swap
  | .mul a b => (add (a.weights negative).1 (b.weights negative).1,
    add (a.weights negative).2 (b.weights negative).2)

abbrev Constraint (n : Nat) := Expr n × Expr n

def row (signs : Fin n → Bool) (eq : Constraint n) : ACBasis.Row n :=
  let l := eq.1.weights signs
  let r := eq.2.weights signs
  .ofWeights (add l.1 r.2) (add r.1 l.2)

def profiles : (n : Nat) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n+1 => [false,true].flatMap fun b => (profiles n).map fun tail => Fin.cases b tail

abbrev Column (basis : (Fin n → Bool) → List (Vec n)) :=
  (d : Fin n → Bool) × Fin (basis d).length

def columns (basis : (Fin n → Bool) → List (Vec n)) : List (Column basis) :=
  (profiles n).flatMap fun d => (List.finRange (basis d).length).map fun j => ⟨d,j⟩

local instance : DecidableEq (Fin n → Bool) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext,congrFun⟩

/-- One coordinate of a symbolic answer, split into its two signs.
Repeated occurrences of a column refer to the same witness in every coordinate. -/
def slots (basis : (Fin n → Bool) → List (Vec n)) (active : List (Column basis))
    (i : Fin n) (negative : Bool) : List (Column basis) :=
  (profiles n).flatMap fun d =>
    if d i = negative then (List.finRange (basis d).length).flatMap fun j =>
      if (⟨d,j⟩ : Column basis) ∈ active then List.replicate ((basis d).get j i) (⟨d,j⟩ : Column basis) else []
    else []

def graphBasis (graph : List (Expr n × Fin n)) (d : Fin n → Bool) : List (Vec n) :=
  generate (graph.map fun p => row d (p.1,.input p.2))

end Tamarin.Rewriting.DHPeer.SignedMatrix

namespace Tamarin.SignedGraph
open Rewriting.DHPeer.SignedMatrix ACBasis

/-- Postfix programs use 0 for unit, 1 for inverse, 2 for product, and 3+i
for input i. Observations cannot refer to output coordinates. -/
def step (m k : Nat) (stack : List (Expr (m+k))) (word : UInt64) : Option (List (Expr (m+k))) :=
  match word.toNat, stack with
  | 0, xs => some (.unit :: xs)
  | 1, x :: xs => some (.inv x :: xs)
  | 2, y :: x :: xs => some (.mul x y :: xs)
  | i+3, xs => if h : i < m then some (.input ⟨i,by omega⟩ :: xs) else none
  | _, _ => none

def decode (m k : Nat) (words : Array UInt64) : Option (Expr (m+k)) := do
  let [e] ← words.toList.foldlM (step m k) [] | none
  return e

def graph (m : Nat) (obs : Array (Array UInt64)) := (List.finRange obs.size).mapM fun i => do
  let e ← decode m obs.size obs[i]
  return (e, (⟨m+i.val,by omega⟩ : Fin (m+obs.size)))

local instance {n} : DecidableEq (Fin n → Bool) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext,congrFun⟩

def encode {n} (basis : (Fin n → Bool) → List (Vec n)) (all : List (Column basis))
    (active : List (Column basis)) : List Nat :=
  let side (i : Fin n) (d : Bool) :=
    let entries := slots basis active i d
    entries.length :: entries.map all.idxOf
  (List.finRange n).flatMap fun i => side i false ++ side i true

def packet {n} (basis : (Fin n → Bool) → List (Vec n)) : Option (Array UInt64) := do
  let all := columns basis
  guard (all.length ≤ 12)
  let arms := 2 ^ all.length
  let weight := (all.map fun g => total ((basis g.1).get g.2)).sum
  guard (2 + arms * (2*n + weight) ≤ 65536)
  let selections := FlatMatchSearch.sublists all
  let words := 1 :: selections.length :: selections.flatMap (encode basis all)
  guard (words.all (· < UInt64.size))
  return (words.map Nat.toUInt64).toArray

def table {n} (qs : List (Expr n × Fin n)) :=
  (profiles n).mapM fun d => do
    let gs ← Homogeneous.boundedBasis (qs.map fun (p : Expr n × Fin n) => row d (p.1,.input p.2))
    return (d,gs)

/-- Complete only when every sign profile has a verified finite basis and
the entire family fits the response. [0] is an ordinary resource deferral. -/
def candidate (inputs : UInt64) (obs : Array (Array UInt64)) : Option (Array UInt64) := do
  guard (inputs.toNat + obs.size ≤ 8 && obs.size > 0 && obs.all fun p => p.size ≤ 256)
  let qs ← graph inputs.toNat obs
  let bs ← table qs
  packet (fun d => (bs.lookup d).getD [])

def run (inputs : UInt64) (obs : Array (Array UInt64)) := (candidate inputs obs).getD #[0]

end Tamarin.SignedGraph
