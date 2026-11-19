import Std

/-! Fixed packet interpretation for ordinary unification modulo free, C and AC
symbols. A node can refer only to earlier nodes. All identities and
declarations are local to the request. -/
namespace Tamarin.Whole

inductive Tree where
  | leaf (kind id sort : UInt64)
  | app (kind id : UInt64) (args : List Tree)
  deriving Repr

structure Decl where
  kind : UInt64
  id : UInt64
  output : UInt64
  inputs : List UInt64
  deriving Repr

def declarations : List UInt64 → Option (List Decl)
  | [] => some []
  | kind :: id :: arity :: output :: rest => do
    let inputs := rest.take arity.toNat
    guard (inputs.length = arity.toNat && output ≤ 4 && inputs.all (· ≤ 4))
    guard (kind == 2 || ((kind == 3 || kind == 4) && inputs == [output, output]))
    let tail ← declarations (rest.drop arity.toNat)
    guard (!tail.any (fun d => d.kind == kind && d.id == id))
    return ⟨kind, id, output, inputs⟩ :: tail
  | _ => none
termination_by xs => xs.length
decreasing_by simp; omega

def subsort (actual expected : UInt64) : Bool :=
  actual == expected || (expected == 2 && (actual == 0 || actual == 1 || actual == 4))

def decodeNode (decls : List Decl) (prior : Array (Tree × UInt64))
    (row : Array UInt64) : Option (Tree × UInt64) := do
  match row.toList with
  | kind :: id :: rest =>
    if kind ≤ 1 then
      let [s] := rest | none
      guard (s ≤ 4)
      return (.leaf kind id s, s)
    else
      let d ← decls.find? (fun d => d.kind == kind && d.id == id)
      let children ← rest.mapM (fun i => prior[i.toNat]?)
      if kind == 4 then
        -- Declarations check that both binary inputs have the output sort.
        -- Every occurrence in the flat row must satisfy that same sort.
        guard (children.length ≥ 2 && children.all (fun c => subsort c.2 d.output))
      else
        guard (children.length = d.inputs.length)
        guard ((children.zip d.inputs).all (fun (c, expected) => subsort c.2 expected))
      return (.app kind id (children.map Prod.fst), d.output)
  | _ => none

def decodeNodes (decls : List Decl) (nodes : Array (Array UInt64)) : Option (Array Tree) := do
  let table ← nodes.foldlM (fun prior row => do
    let t ← decodeNode decls prior row
    return prior.push t) #[]
  return table.map Prod.fst

def readEquations (trees : Array Tree) : List UInt64 → Option (List (Tree × Tree))
  | [] => some []
  | i :: j :: rest => do
    let lhs ← trees[i.toNat]?
    let rhs ← trees[j.toNat]?
    return (lhs, rhs) :: (← readEquations trees rest)
  | [_] => none

def Wire.decodeProblem (decls : Array UInt64) (nodes : Array (Array UInt64)) (equations : Array UInt64) :=
  do
    let ds ← declarations decls.toList
    let ts ← decodeNodes ds nodes
    readEquations ts equations.toList

end Tamarin.Whole
