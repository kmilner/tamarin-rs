import Tamarin.TotalUnifyWire
import Tamarin.ReferenceMatching

/-! Directional matching uses the same term dictionary and postfix answer
rows as ordinary unification. Variables in match images retain their input
identities. The scope selects bindable variables by their dictionary IDs. -/
namespace Tamarin.TotalMatchWire
open TotalUnifyWire

def domain {s : Signature} (p : Problem s) (ids : Array UInt64) : List Variable :=
  p.variables.filter fun v => ids.any fun i => i.toNat == v.id

def run (decls : Array UInt64) (nodes : Array (Array UInt64)) (roots ids : Array UInt64) :
    Array (Array UInt64) :=
  (do
    let ⟨d,p⟩ ← input decls nodes roots
    pack p ((ReferenceMatching.matcher d.sig).run p trivial (domain p ids))).getD #[#[0]]

end Tamarin.TotalMatchWire
