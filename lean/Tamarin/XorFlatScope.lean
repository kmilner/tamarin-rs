import Tamarin.XorFlatVariants

/-! Fresh-name hygiene is a property of the decoded row. The numeric matching
kernel does not need caller names, their indices, or the avoid set. -/
namespace Tamarin.Rewriting.FreshXor.Flat
variable {sig : Signature} {n : Nat} {q : Query sig n} {p : Fin n → Fin n}

private theorem occurs_in_fold (f : sig.ACSym) (a : Term sig) (xs : List (Term sig))
    (v : Variable) (h : (ACRepresentation.fold f a xs).Occurs v) : ∃ t ∈ a::xs, t.Occurs v := by
  induction xs generalizing a with
  | nil => exact ⟨a,List.mem_cons_self,h⟩
  | cons b bs ih =>
    rcases h with ha | hb
    · exact ⟨a,List.mem_cons_self,ha⟩
    · obtain ⟨t,ht,hv⟩ := ih b hb
      exact ⟨t,List.mem_cons_of_mem _ ht,hv⟩

/-- It is sufficient for newly allocated names to avoid the query and outer
scope. Names retained from the query may occur in the outer scope. -/
def Naming.FreshFor (w : Naming q p) (avoid : List Variable) : Prop :=
  ∀ v ∈ q.vars, w.name v = v ∨ (w.name v ∉ q.vars ∧ w.name v ∉ avoid)

theorem Naming.scope (w : Naming q p) (avoid : List Variable) (h : w.FreshFor avoid) :
    w.arm.Safe [q.term] avoid ∧ ∀ v, w.subst.apply (w.subst.image v) = w.subst.image v := by
  have ok (v : Variable) (hv : v ∈ q.vars) : Observed [q.term] (w.name v) ∨ w.name v ∉ avoid := by
    rcases h v hv with eq | outside
    · rw [eq]; exact .inl ((q.observed v).mpr hv)
    · exact .inr outside.2
  constructor
  · constructor
    · intro v no
      exact congrArg Term.var (w.outside v (mt (q.observed v).mpr no))
    · intro v obs u occurs
      change u = w.name v at occurs
      exact occurs ▸ ok v ((q.observed v).mp obs)
    · intro t ht u occurs
      obtain rfl := List.mem_singleton.mp ht
      change (q.table.value w.leaves).Occurs u at occurs
      cases eq : w.leaves with
      | nil =>
        rw [eq] at occurs
        exact False.elim (q.table.zeroGround u occurs)
      | cons a as =>
        rw [eq] at occurs
        obtain ⟨t,ht,hu⟩ := occurs_in_fold q.table.f a as u occurs
        rw [← eq] at ht
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
        exact hu ▸ ok (q.key i) (q.present i)
  · intro v
    apply congrArg Term.var
    change w.name (w.name v) = w.name v
    by_cases hv : v ∈ q.vars
    · rcases h v hv with fixed | outside
      · rw [fixed]; exact fixed
      · exact w.outside _ outside.1
    · rw [w.outside v hv]; exact w.outside v hv

end Tamarin.Rewriting.FreshXor.Flat
