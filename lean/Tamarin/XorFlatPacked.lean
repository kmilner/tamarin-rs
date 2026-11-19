import Tamarin.XorFlatVariants
import Tamarin.VariantJoinPacked

/-! Uniqueness for each flat XOR in a packed query after one simultaneous
  instantiation, allowing arbitrarily many repeated and shared operands. -/
namespace Tamarin.Rewriting.FreshXor.Flat
variable {sig : Signature}

/-- A packed operation can be a variable or a flat xor of Fresh variables,
represented in any order or parenthesization modulo B. -/
inductive Observation (T : Table sig) : Term sig → Prop where
  | name (v : Variable) : Observation T (.var v)
  | sum (x y : Variable) (rest : List Variable) (fresh : ∀ v ∈ x::y::rest, v.sort = .fresh)
      {t} (layout : EquivB t (T.value ((x::y::rest).map Term.var))) : Observation T t

theorem Observation.unique {T : Table sig} {t : Term sig} (obs : Observation T t)
    (ρ : Substitution sig) (hn : Normalized T.R ρ) {u v : Term sig}
    (hu : NormalForm T.R (ρ.apply t) u) (hv : NormalForm T.R (ρ.apply t) v) : EquivB u v := by
  classical
  cases obs with
  | name w => exact (normal_reduces_equiv hu.1 (hn w)).symm.trans (normal_reduces_equiv hv.1 (hn w))
  | sum x y rest fresh layout =>
    let xs := (x::y::rest).map ρ.image
    let key (i : Fin xs.length) := xs[i.val]
    obtain ⟨p,inv,keep,nd⟩ := XorMatchings.exists_fitting key
    have indexed : (List.finRange xs.length).map key = xs := by
      simp only [List.finRange, List.map_ofFn, Function.comp_def, key]
      exact List.ofFn_getElem
    have same (t) := (indexed ▸ (XorMatchings.fixed_parity key p inv keep t)).symm
    have eq : EquivB (ρ.apply t) (T.value xs) := by
      have h : EquivB (ρ.apply t) (ρ.apply (T.value ((x::y::rest).map Term.var))) := layout.subst ρ.image
      rw [Table.subst_value, List.map_map] at h
      exact h
    have forms {s} (h : NormalForm T.R (ρ.apply t) s) : NormalForm T.R (T.value xs) s :=
      ⟨(Reduces.basis eq.symm).trans h.1, h.2.1, fun sort hs =>
        h.2.2 sort (Term.checkSort_sound _ _ ((SortClash.check_equiv eq sort).symm ▸ Term.checkSort_complete hs))⟩
    have sorted : ∀ s ∈ xs, HasSort s .fresh := by
      intro s hs; obtain ⟨v, here, rfl⟩ := List.mem_map.mp hs
      exact fresh v here ▸ ρ.sorted v
    have normal : ∀ s ∈ xs, Normal T.R s := by
      intro s hs; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hs
      exact hn v
    have law := T.normalForm_iff sorted normal nd same
    exact ((law u).mp (forms hu)).trans ((law v).mp (forms hv)).symm

end Tamarin.Rewriting.FreshXor.Flat
