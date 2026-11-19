import TamarinRuntime.WholeSyntax

/-! Candidate for the request-wide unification interface. The packet
contract uses TamarinWire independently of the candidate decoder. -/
namespace Tamarin.Whole

namespace Tree

/- Prefix codes have disjoint leaf, application and end-of-children tags.
The tail argument avoids repeated concatenation. -/
mutual
  def emit : Tree → List UInt64 → List UInt64
    | .leaf k i s, tail => 0 :: k :: i :: s :: tail
    | .app k i args, tail => 1 :: k :: i :: emitArgs args (2 :: tail)
  def emitArgs : List Tree → List UInt64 → List UInt64
    | [], tail => tail
    | t :: ts, tail => emit t (emitArgs ts tail)
end

def key (t : Tree) := t.emit []

instance : BEq Tree := ⟨fun a b => a.key == b.key⟩

end Tree

def parts (id : UInt64) (t : Tree) : List Tree :=
  match t with
  | .app 4 j xs => if id = j then xs else [t]
  | _ => [t]

def order (xs : List Tree) : List Tree :=
  xs.mergeSort (fun a b => decide (a.key ≤ b.key))

def make (kind id : UInt64) (args : List Tree) : Tree :=
  if kind = 4 then .app kind id (order (args.flatMap (parts id)))
  else if kind = 3 then .app kind id (order args)
  else .app kind id args

mutual
  def canonical : Tree → Tree
    | .leaf k i s => .leaf k i s
    | .app k i args => make k i (canonicalArgs args)
  def canonicalArgs : List Tree → List Tree
    | [] => []
    | t :: ts => canonical t :: canonicalArgs ts
end

mutual
  def ground : Tree → Bool
    | .leaf k _ _ => k == 1
    | .app _ _ xs => groundArgs xs
  def groundArgs : List Tree → Bool
    | [] => true
    | a :: as => ground a && groundArgs as
end

/-- A single impossible ground equation refutes the entire conjunction. A
nonground difference can still have solutions. -/
def classify : List (Tree × Tree) → UInt64
  | [] => 2
  | (a,b) :: rest =>
    if canonical a == canonical b then classify rest
    else if ground a && ground b then 1
    else if classify rest == 1 then 1 else 0

def run (decls : Array UInt64) (nodes : Array (Array UInt64)) (equations : Array UInt64) :
    Array (Array UInt64) :=
  match decodeProblem decls nodes equations with
  | some p => #[#[classify p]]
  | none => #[#[0]]

/-- Refine a deferred classification using the original graph and its decoded roots. -/
def runRefining (refutes : Array (Array UInt64) → Array UInt64 → List (Tree × Tree) → Bool)
    (decls : Array UInt64) (nodes : Array (Array UInt64)) (equations : Array UInt64) :
    Array (Array UInt64) :=
  match decodeProblem decls nodes equations with
  | none => #[#[0]]
  | some rows =>
    let status := classify rows
    if status = 0 && refutes nodes equations rows then #[#[1]] else #[#[status]]

end Tamarin.Whole
