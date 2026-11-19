import TamarinRuntime.Whole

/-! Check a proposed free factor and residual system against the original
request. All three systems use pairs of roots in a single declared graph.
Bounds on free decomposition limit work; unresolved shells remain equations. -/
namespace Tamarin.FactorCheck
open Whole

abbrev Equations := List (Tree × Tree)

def expose : Nat → Tree → Tree → Equations
  | n + 1, a@(.app 2 f xs), b@(.app 2 g ys) =>
    if f == g && xs.length == ys.length then
      (xs.zip ys).flatMap fun (x,y) => expose n x y
    else [(a,b)]
  | _, a, b => [(a,b)]

def same (a b : Tree × Tree) : Bool :=
  (a.1 == b.1 && a.2 == b.2) || (a.1 == b.2 && a.2 == b.1)

def supported (qs : Equations) (e : Tree × Tree) : Bool :=
  e.1 == e.2 || qs.any (same e)

def lookup (bs : Equations) (t : Tree) : Tree :=
  match bs.find? (fun e => e.1 == t) with
  | some (_, u) => u
  | none => t

mutual
  def applyBindings (bs : Equations) : Tree → Tree
    | .leaf k v s => if k = 0 then lookup bs (.leaf k v s) else .leaf k v s
    | .app k f xs => .app k f (applyChildren bs xs)
  def applyChildren (bs : Equations) : List Tree → List Tree
    | [] => []
    | x :: xs => applyBindings bs x :: applyChildren bs xs
end

def substitute (bs qs : Equations) := qs.map fun (a,b) => (applyBindings bs a, applyBindings bs b)

def rootSort (ds : List Decl) : Tree → Option UInt64
  | .leaf _ _ s => some s
  | .app k f _ => (ds.find? (fun d => d.kind == k && d.id == f)).map (·.output)

def sortedBinding (ds : List Decl) : Tree × Tree → Bool
  | (.leaf 0 _ s, rhs) => (rootSort ds rhs).any (fun t => subsort t s)
  | _ => false

/-- Tamarin rebuilds substituted applications modulo their declared C or AC
attributes. Free argument order and multiplicities are retained. -/
def canonicalRows (es : Equations) : Equations :=
  es.map fun (a,b) => (canonical a, canonical b)

mutual
  private def spendTree : Tree → Nat → Option Nat
    | _, 0 => none
    | .leaf .., n + 1 => some n
    | .app _ _ args, n + 1 => spendChildren args n
  private def spendChildren : List Tree → Nat → Option Nat
    | [], n => some n
    | t :: ts, n => (spendTree t n).bind (spendChildren ts)
end

/-- A local expansion limit also bounds work when a substitution repeatedly
duplicates a previously shared subtree. Exhaustion defers the proposal. -/
def replayFits (es : Equations) : Bool :=
  (es.foldlM (fun n (a,b) => (spendTree a n).bind (spendTree b)) 8192).isSome

private def isVariable : Tree → Bool
  | .leaf 0 _ _ => true
  | _ => false

mutual
  private def mentions (key : Tree) : Tree → Bool
    | t@(.leaf ..) => t == key
    | .app _ _ xs => mentionsAny key xs
  private def mentionsAny (key : Tree) : List Tree → Bool
    | [] => false
    | x :: xs => mentions key x || mentionsAny key xs
end

/-- Prefer to eliminate a variable in the proposed domain. Both sides of an
equation are considered, so the order of a pair of aliases is immaterial. -/
def nextBinding (flat goals : Equations) : Option (Tree × Tree) :=
  let candidate (k t : Tree) := isVariable k && goals.any (fun e => e.1 == k) && !mentions k t
  flat.findSome? fun (a,b) =>
    if candidate a b then some (a,b) else if candidate b a then some (b,a) else none

/-- Replay a sequence of explicitly justified bindings. A binding need not
already have its final right side: later substitutions can expose free heads
and can flatten or reorder a product in an earlier image. -/
def replay : Nat → Equations → Equations → Bool
  | 0, _, _ => false
  | n + 1, active, goals =>
    if replayFits (active ++ goals) then
      let flat := (canonicalRows active).flatMap fun (a,b) => expose 128 a b
      let wanted := canonicalRows goals
      if wanted.all (supported flat) then true
      else match nextBinding flat wanted with
        | none => false
        | some e => supported flat e && replay n (substitute [e] flat) (substitute [e] wanted)
    else false

/-- A replayed proposal must preserve the whole original conjunction in
both directions after applying the final simultaneous factor. -/
def checkReplay (ds : List Decl) (p bs q : Equations) : Bool :=
  if replayFits (p ++ bs ++ q) then
    let substOriginal := substitute bs p
    if replayFits substOriginal then
      let derived := (canonicalRows substOriginal).flatMap fun (a,b) => expose 128 a b
      let residual := canonicalRows q
      bs.all (sortedBinding ds) &&
        (bs.map Prod.fst).isEqv (bs.map Prod.fst).eraseDups (· == ·) &&
        bs.all (fun e => applyBindings bs e.2 == e.2) &&
        q.all (fun e => applyBindings bs e.1 == e.1 && applyBindings bs e.2 == e.2) &&
        replay 128 p bs && derived.all (supported residual) && residual.all (supported derived)
    else false
  else false

def direct (ds : List Decl) (p bs q : Equations) : Bool :=
  let flat := p.flatMap fun (a,b) => expose 128 a b
  let derived := substitute bs flat
  bs.all (sortedBinding ds) &&
    (bs.map Prod.fst).isEqv (bs.map Prod.fst).eraseDups (· == ·) &&
    bs.all (fun e => applyBindings bs e.2 == e.2 && flat.any (same e)) &&
    q.all (fun e => applyBindings bs e.1 == e.1 && applyBindings bs e.2 == e.2) &&
    derived.all (supported q) && q.all (supported derived)

def check (ds : List Decl) (p bs q : Equations) : Bool :=
  direct ds p bs q || checkReplay ds p bs q

def runWith (validate : List Decl → Equations → Equations → Equations → Bool) (decls : Array UInt64) (nodes : Array (Array UInt64))
    (original bindings residual : Array UInt64) : Bool := Id.run do
  let some ds := declarations decls.toList | return false
  let some ts := decodeNodes ds nodes | return false
  let some p := readEquations ts original.toList | return false
  let some bs := readEquations ts bindings.toList | return false
  let some q := readEquations ts residual.toList | return false
  return validate ds p bs q

def run := runWith check

end Tamarin.FactorCheck
