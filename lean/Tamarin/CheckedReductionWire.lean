import Tamarin.CheckedReduction
import Tamarin.ConstantDefinitions
import Tamarin.TableDecrease
import Tamarin.TableWire

/-! One observation root followed by oriented rule pairs. Status 1 carries a
unique normal form, 2 is an unfinished search or an inadmissible rule table,
and 0 denotes a malformed or unrepresentable packet. -/
namespace Tamarin.CheckedReductionWire
open TotalUnifyWire

def fuel {s : Signature} (rules : Problem s) (t : Term s) (fallback : UInt64) :=
  (TableDecrease.budget rules t).getD fallback.toNat

/-- Rust invokes this eager fallback after its cheaper graph searches. The
reference solver and its eventual-completion theorem are independent of the
host's resource policy. -/
def admitted {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (rs : Problem s) (t : Term s) (fallback : UInt64) : Bool :=
  CheckedReduction.rangeBound rs && TableDecrease.sorted rs &&
    CheckedReduction.affordable rs (fuel rs t fallback) 100000 t

/-- This class has a structural normalizer for every term, including a term
whose AC product is too wide for enumerating contextual rewrite successors. -/
def definitions {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (rs : Problem s) : Bool := ConstantDefinitions.accepts rs && TableDecrease.sorted rs

def emit {d : Dictionary} (u : Term d.sig) : Array (Array UInt64) :=
  match write u with
  | none => #[#[0]]
  | some ts => #[#[1],(ts.flatMap Token.words).toArray]

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (pairs : Array UInt64) (root : UInt64) (fallback : UInt64) :
    Array (Array UInt64) :=
  match TableWire.input ds ns pairs #[root] with
  | some ⟨_,rs,[t]⟩ =>
    if definitions rs then emit (ConstantDefinitions.expand rs t) else
    if !admitted rs t fallback then #[#[2]] else
    match CheckedReduction.run rs (fuel rs t fallback) t with
    | none => #[#[2]]
    | some u => emit u
  | _ => #[#[0]]

end Tamarin.CheckedReductionWire
