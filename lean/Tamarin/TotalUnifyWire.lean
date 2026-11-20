import Tamarin.MixedUnification
import Tamarin.WordEncoding
import TamarinWire

/-! The ordinary-unification packet uses a per-query symbol dictionary.
Decode an arity-correct DAG without assigning a sort to the root of each
application. Sorting is imposed on substitution images by the unifier. -/
namespace Tamarin.TotalUnifyWire
open Whole

def sortCode : SortId → UInt64
  | .pub => 0 | .fresh => 1 | .msg => 2 | .node => 3 | .nat => 4

def sortOf (n : UInt64) : SortId :=
  if n == 0 then .pub else if n == 1 then .fresh else if n == 2 then .msg
  else if n == 3 then .node else .nat

theorem sortOf_code (s : SortId) : sortOf (sortCode s) = s := by cases s <;> decide

def decl (ds : List Decl) (k id : UInt64) :=
  ds.find? (fun d => d.kind == k && d.id == id)

abbrev Symbol (ds : List Decl) (k : UInt64) := { id : UInt64 // (decl ds k id).isSome }

private def resolve (ds : List Decl) (k id : UInt64) : Option (Symbol ds k) :=
  if h : (decl ds k id).isSome then some ⟨id,h⟩ else none

def info {ds k} (f : Symbol ds k) := (decl ds k f.val).get f.property

structure Dictionary where
  decls : List Decl
  atoms : List (UInt64 × SortId)

abbrev Dictionary.sig (d : Dictionary) : Signature where
  FreeSym := Symbol d.decls 2
  CSym := Symbol d.decls 3
  ACSym := Symbol d.decls 4
  Atom := { a : UInt64 × SortId // a ∈ d.atoms }
  arity f := (info f).inputs.length
  inputSort f i := sortOf ((info f).inputs.get i)
  outputSort f := sortOf (info f).output
  cSort f := sortOf (info f).output
  acSort f := sortOf (info f).output
  atomSort a := a.val.2

private def atom (d : Dictionary) (id : UInt64) (s : SortId) : Option d.sig.Atom :=
  if h : (id,s) ∈ d.atoms then some ⟨(id,s),h⟩ else none

def leaf (d : Dictionary) (k id arg : UInt64) : Option (Term d.sig) := do
  guard (arg ≤ 4)
  if k == 0 then return .var ⟨id.toNat,sortOf arg⟩
  if k == 1 then return .atom (← atom d id (sortOf arg))
  none

def app (d : Dictionary) (k id : UInt64) (children : List (Term d.sig)) :
    Option (Term d.sig) := do
  if k == 2 then
    let f ← resolve d.decls 2 id
    if h : children.length = d.sig.arity f then
      return .free f fun i => children.get ⟨i.val,h.symm ▸ i.isLt⟩
    else none
  else if k == 3 then
    let f ← resolve d.decls 3 id
    let [l,r] := children | none
    return .comm f l r
  else if k == 4 then
    let f ← resolve d.decls 4 id
    let l :: r :: rs := children | none
    return .ac f l (ACRepresentation.fold f r rs)
  else none

def node (d : Dictionary) (prior : Array (Term d.sig)) (row : Array UInt64) := do
  let k :: id :: tail := row.toList | none
  if k ≤ 1 then
    let [arg] := tail | none
    leaf d k id arg
  else
    app d k id (← tail.mapM (fun (i : UInt64) => prior[i.toNat]?))

def equations {s : Signature} (ts : Array (Term s)) : List UInt64 → Option (Problem s)
  | [] => some []
  | i :: j :: rest => do return ⟨← ts[i.toNat]?,← ts[j.toNat]?⟩ :: (← equations ts rest)
  | [_] => none

def graph (decls : Array UInt64) (nodes : Array (Array UInt64)) :
    Option ((d : Dictionary) × Array (Term d.sig)) := do
  let ds ← declarations decls.toList
  let atoms := nodes.toList.filterMap fun row => match row.toList with
    | [1,id,s] => some (id,sortOf s)
    | _ => none
  let d : Dictionary := ⟨ds,atoms.eraseDups⟩
  let ts ← nodes.foldlM (fun acc r => do return acc.push (← node d acc r)) #[]
  return ⟨d,ts⟩

def input (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Option ((d : Dictionary) × Problem d.sig) := do
  let ⟨d,ts⟩ ← graph decls nodes
  return ⟨d,← equations ts roots.toList⟩

/-- Postorder triples. The third word is a sort for a leaf and a child
count for an application. Only natural-number fields need checked packing. -/
structure Token where
  kind : UInt64
  id : UInt64
  arg : UInt64
  deriving DecidableEq

def Token.words (t : Token) := [t.kind,t.id,t.arg]

def write {d : Dictionary} : Term d.sig → Option (List Token)
  | .var v => do return [⟨0,← WordEncoding.pack v.id,sortCode v.sort⟩]
  | .atom a => some [⟨1,a.val.1,sortCode a.val.2⟩]
  | .free f args => do
    let code ← (List.finRange _).mapM fun i => write (args i)
    return code.flatten ++ [⟨2,f.val,← WordEncoding.pack (d.sig.arity f)⟩]
  | .comm f l r => do return (← write l) ++ (← write r) ++ [⟨3,f.val,2⟩]
  | .ac f l r => do return (← write l) ++ (← write r) ++ [⟨4,f.val,2⟩]

def binding {d : Dictionary} (σ : Substitution d.sig) (v : Variable) : Option (Array UInt64) := do
  return ((← WordEncoding.pack v.id) :: sortCode v.sort :: (← write (σ.image v)).flatMap Token.words).toArray

def arm {d : Dictionary} (vs : List Variable) (σ : Substitution d.sig) : Option (List (Array UInt64)) := do
  return #[] :: (← vs.mapM (binding σ))

def pack {d : Dictionary} (p : Problem d.sig) (answers : List (Substitution d.sig)) :
    Option (Array (Array UInt64)) := do
  return (#[1] :: (← answers.mapM (arm p.variables.eraseDups)).flatten).toArray

def run (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots : Array UInt64) :
    Array (Array UInt64) :=
  (do
    let ⟨d,p⟩ ← input decls nodes roots
    pack p ((MixedUnification.verified (s := d.sig)).solve p trivial [])).getD #[#[0]]

theorem app_free {d : Dictionary} (f : d.sig.FreeSym) (args : Fin (d.sig.arity f) → Term d.sig) :
    app d 2 f.val (List.ofFn args) = some (.free f args) := by
  simp [app,resolve,f.property,List.get_eq_getElem,List.getElem_ofFn]

theorem app_comm {d : Dictionary} (f : d.sig.CSym) (l r : Term d.sig) :
    app d 3 f.val [l,r] = some (.comm f l r) := by simp [app,resolve,f.property]

theorem app_ac {d : Dictionary} (f : d.sig.ACSym) (l r : Term d.sig) :
    app d 4 f.val [l,r] = some (.ac f l r) := by simp [app,resolve,f.property,ACRepresentation.fold]

theorem leaf_var {d : Dictionary} (id : UInt64) (s : SortId) :
    leaf d 0 id (sortCode s) = some (.var ⟨id.toNat,s⟩) := by cases s <;> rfl

theorem leaf_atom {d : Dictionary} (a : d.sig.Atom) :
    leaf d 1 a.val.1 (sortCode a.val.2) = some (.atom a) := by
  rcases a with ⟨⟨i,k⟩,h⟩
  cases k <;> simp [leaf,atom,sortCode,sortOf,h,guard]

end Tamarin.TotalUnifyWire
