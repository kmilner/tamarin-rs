import Tamarin.TotalUnifyWire

/-! Active rewrite tables and ordered observation tuples share one validated
term DAG and one symbol dictionary. Each rule contributes two root indices. -/
namespace Tamarin.TableWire

def input (decls : Array UInt64) (nodes : Array (Array UInt64))
    (pairs observed : Array UInt64) :
    Option ((d : TotalUnifyWire.Dictionary) × List (Equation d.sig) × List (Term d.sig)) := do
  let ⟨d,ts⟩ ← TotalUnifyWire.graph decls nodes
  let rules ← TotalUnifyWire.equations ts pairs.toList
  let terms ← observed.toList.mapM fun id => ts[id.toNat]?
  return ⟨d,rules,terms⟩

end Tamarin.TableWire
