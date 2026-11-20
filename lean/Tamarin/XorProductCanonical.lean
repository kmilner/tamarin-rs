import Tamarin.XorProductPaths
import Tamarin.SortedACNormalAlgebra

/-! Uniqueness for exponent-two cancellation rows on normalized substitutions.
The opaque XOR factors may have any constructor head and may themselves
originate in other active theories. -/
namespace Tamarin.Rewriting.BinaryXor
open Cancellation ConstructorVariants NormalAlgebra
variable {sig : Signature} (T : Table sig)

private theorem normal_pure {t : Term sig} (nt : Normal T.R t) : T.PureFrom (fun _ => True) t := by
  classical
  intro k hk
  rw [FreshXor.Flat.Table.bag,DHProduct.classes] at hk
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hk
  exact .inr ⟨x,trivial,((DHProduct.subgroup_normal_iff T.f t).mp nt).1 x hx,rfl⟩

/-- Every instance of an XOR root redex belongs to the message sort, even
when the surrounding context contains arguments of other sorts. -/
theorem redex_typed
    (typed : ∀ r ∈ T.rules, head r.lhs = .ac T.f → HasSort r.lhs .msg)
    {p q : Term sig} (atHead : head p = .ac T.f) (step : T.R p q) : HasSort p .msg := by
  obtain ⟨r,hr,σ,rfl,rfl⟩ := step
  rw [instance_head r (T.apps r hr) σ] at atHead
  exact (typed r hr atHead).subst σ.image σ.sorted

theorem uniqueRow (r : Equation sig) (hr : r ∈ T.rules) (atHead : head r.lhs = .ac T.f)
    (typed : HasSort r.lhs .msg) : UniqueRow T.rules r := by
  intro σ hn a b na nb
  apply unique_of_pure T (typed.subst σ.image σ.sorted) _ na nb
  have pure (v : Variable) := normal_pure T (hn v)
  rcases T.inventory r hr atHead with rfl | ⟨v,rfl⟩ | ⟨u,v,rfl⟩ | ⟨u,v,rfl⟩
  · exact (T.pure_ac ..).mpr ⟨pure _,pure _⟩
  · change T.PureFrom _ (.ac T.f (σ.image _) (σ.apply T.zero))
    rw [T.toTable.fixes_zero σ]
    exact (T.pure_ac ..).mpr ⟨pure _,T.pure_zero⟩
  · exact (T.pure_ac ..).mpr ⟨pure _,(T.pure_ac ..).mpr ⟨pure _,pure _⟩⟩
  · exact (T.pure_ac ..).mpr ⟨(T.pure_ac ..).mpr ⟨pure _,pure _⟩,pure _⟩

private noncomputable def parity : SortedAC.ProductInvariant T.f T.R := by
  classical
  exact {
    rel := fun a b => ∀ k, k ≠ T.zeroClass → a.count k % 2 = b.count k % 2
    ofPerm := fun p k _ => congrArg (· % 2) (p.count_eq k)
    symm := fun h k ne => (h k ne).symm
    trans := fun h i k ne => (h k ne).trans (i k ne)
    append := by
      intro a b c d h i k ne
      have l := h k ne
      have r := i k ne
      simp only [List.count_append]
      omega
    distinguish := fun tx ty nx ny h => normal_eq T ⟨tx,nx⟩ ⟨ty,ny⟩ h }

/-- An XOR on arbitrary normal values has a reachable normal representative
and is associative and commutative at the common kind. -/
noncomputable def product [DecidableEq sig.ACSym]
    (typed : ∀ r ∈ T.rules, head r.lhs = .ac T.f → HasSort r.lhs .msg) :
    NormalAlgebra.Product T.f T.R :=
  (parity T).product T.fSort (redex_typed T typed) (k := 2) (by
    intro x y tx ty nx ny
    obtain ⟨u,gu,path⟩ := sorted_paths T x y ⟨tx,nx⟩ ⟨ty,ny⟩
    have pure := (T.pure_ac x y).mpr ⟨pure_good T ⟨tx,nx⟩,pure_good T ⟨ty,ny⟩⟩
    exact ⟨u,gu.1,path,gu.2,(T.reduces_kept path.reduces pure).2⟩)

end Tamarin.Rewriting.BinaryXor
