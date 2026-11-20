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

/-- All observation tuples over this packet share one dictionary and rule table. -/
theorem withoutObservations {ds ns es roots d rs q}
    (decoded : input ds ns es roots = some ⟨d,rs,q⟩) :
    input ds ns es #[] = some ⟨d,rs,[]⟩ := by
  unfold input at decoded ⊢
  cases graph : TotalUnifyWire.graph ds ns with
  | none => simp [graph] at decoded
  | some graphPair =>
    obtain ⟨dict,terms⟩ := graphPair
    cases eqs : TotalUnifyWire.equations terms es.toList with
    | none => simp [graph,eqs] at decoded
    | some rules =>
      cases obs : roots.toList.mapM (fun (i : UInt64) => terms[i.toNat]?) with
      | none => simp [graph,eqs,obs] at decoded
      | some qs =>
        simp [graph,eqs,obs] at decoded
        obtain ⟨rfl,h⟩ := decoded
        cases eq_of_heq h
        simp [eqs]

end Tamarin.TableWire
