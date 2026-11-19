import Tamarin.Rewriting
import Tamarin.SortClash

/-! Transport a singleton variant query to any structurally equivalent
representative while keeping the same substitutions and returned values. -/
namespace Tamarin.Rewriting
variable {sig : Signature}

theorem NormalForm.equiv_input {R : Root sig} {t s u : Term sig} (e : EquivB t s)
    (f : NormalForm R t u) : NormalForm R s u :=
  ⟨(Reduces.basis e.symm).trans f.1,f.2.1,fun k hs =>
    f.2.2 k (Term.checkSort_sound _ _ ((SortClash.check_equiv e k).symm ▸ Term.checkSort_complete hs))⟩

theorem CompleteVariants.presented {R : Root sig} {source t : Term sig} {arms : List (Variant sig)}
    (family : CompleteVariants R [source] arms ∧ ∀ a ∈ arms, a.Reconstructible R [source])
    (layout : EquivB t source) :
    CompleteVariants R [t] arms ∧ ∀ a ∈ arms, a.Reconstructible R [t] := by
  have forms (ρ : Substitution sig) (vs : List (Term sig)) :
      Aligned (fun s u => NormalForm R (ρ.apply s) u) [t] vs ↔
      Aligned (fun s u => NormalForm R (ρ.apply s) u) [source] vs := by
    cases vs with
    | nil => rfl
    | cons u us =>
      exact and_congr ⟨NormalForm.equiv_input (layout.subst ρ.image),
        NormalForm.equiv_input (layout.symm.subst ρ.image)⟩ Iff.rfl
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro arm ha
    have hs := family.1.1 arm ha
    exact ⟨hs.1,(forms _ _).mpr hs.2⟩
  · intro ρ hn vs nf
    obtain ⟨arm,ha,δ,nd,obs,vals⟩ := family.1.2 ρ hn vs ((forms _ _).mp nf)
    refine ⟨arm,ha,δ,nd,?_,vals⟩
    intro v hv
    obtain ⟨s,mem,occ⟩ := hv
    obtain rfl := List.mem_singleton.mp mem
    exact obs v ⟨_,List.mem_cons_self,(layout.occurs_iff v).mp occ⟩
  · intro arm ha vs nf
    exact family.2 arm ha vs ((forms _ _).mp nf)

end Tamarin.Rewriting
