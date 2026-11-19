import Tamarin.VariantJoinPacked

/-! Lift a shared substitution and its correlated family of operation results
through the caller's simultaneous renaming and ordered observation layout. -/
namespace Tamarin.Rewriting.DHExponent.Caller
open VariantJoin
variable {sig : Signature} {A K : Type} {keys : List Variable} {rules : List (Equation sig)}

def row (keys : List Variable) (σ : K → Substitution sig) (value : K → A → Term sig) (k : K) :
    Row sig (Key keys) A := ⟨fun i => (σ k).image i.val,value k⟩

theorem pack (arms : List K) (σ : K → Substitution sig) (op : A → Term sig) (value : K → A → Term sig)
    (typed : ∀ a, HasSort (op a) (op a).rootSort)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (images : ∀ k ∈ arms, Normalized (ruleRoot rules) (σ k))
    (symbolic : ∀ k ∈ arms, ∀ a, NormalForm (ruleRoot rules) ((σ k).apply (op a)) (value k a))
    (classify : ∀ (ρ : Substitution sig), Normalized (ruleRoot rules) ρ → ∀ outputs : A → Term sig,
      (∀ a, NormalForm (ruleRoot rules) (ρ.apply (op a)) (outputs a)) →
      ∃ k ∈ arms, ∃ δ : Substitution sig, Normalized (ruleRoot rules) δ ∧
        (∀ i : Key keys, EquivB (ρ.image i.val) (δ.apply ((σ k).image i.val))) ∧
        ∀ a, EquivB (outputs a) (δ.apply (value k a)))
    (unique : ∀ (ρ : Substitution sig), Normalized (ruleRoot rules) ρ → ∀ a u v,
      NormalForm (ruleRoot rules) (ρ.apply (op a)) u → NormalForm (ruleRoot rules) (ρ.apply (op a)) v → EquivB u v)
    (rows : List (Row sig (Key keys) A))
    (allRows : ∀ k ∈ arms, ∃ r ∈ rows, (row keys σ value k).Relabels r)
    (onlyRows : ∀ r ∈ rows, ∃ k ∈ arms, (row keys σ value k).Relabels r)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (repr : Term sig → Term sig)
    (uniform : ∀ t, .inr t ∈ slots → StableVariants.Representative (ruleRoot rules) t (repr t))
    (scope : ∀ v, v ∈ keys ↔ Observed (slots.map (packedInput op)) v)
    (avoid : List Variable) (fresh : ∀ r ∈ rows, ∀ v, r.Uses v → v ∉ keys ++ avoid) :
    ∃ sorted : ∀ r ∈ rows, r.Sorted,
      let query := slots.map (packedInput op)
      let answers := packRows rows sorted slots repr
      CompleteVariants (ruleRoot rules) query answers ∧ ∀ a ∈ answers,
        a.Reconstructible (ruleRoot rules) query ∧ a.Safe query avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  have localRows : Exact (ruleRoot rules) Subtype.val op (arms.map (row keys σ value)) := by
    intro ρ hn outputs ny
    constructor
    · intro actual
      obtain ⟨k,hk,δ,hd,inputs,values⟩ := classify ρ hn outputs actual
      exact ⟨_,List.mem_map_of_mem (f := row keys σ value) hk,δ,hd,inputs,values⟩
    · rintro ⟨_,mem,δ,_,fits⟩ a
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
      apply form_of_instance hn (typed a) (δ := δ) (σ := σ k) _ (symbolic k hk a) (fits.values a) (ny a)
      intro v occ
      exact fits.inputs ⟨v,(scope v).mpr ⟨_,List.mem_map_of_mem (f := packedInput op) (used a),occ⟩⟩
  have rel := localRows.relabel (out := rows)
    (fun _ hm => by obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm; exact allRows k hk)
    (fun r hm => by obtain ⟨k,hk,h⟩ := onlyRows r hm; exact ⟨_,List.mem_map_of_mem hk,h⟩)
  have sorted (r) (hm : r ∈ rows) : r.Sorted := by
    obtain ⟨k,_,rel⟩ := onlyRows r hm
    exact rel.sorted (fun i => (σ k).sorted i.val)
  have normal (r) (hm : r ∈ rows) : r.IsNormal (ruleRoot rules) := by
    obtain ⟨k,hk,rel⟩ := onlyRows r hm
    exact rel.normal.mp ⟨fun i => images k hk i.val, fun a => (symbolic k hk a).2.1⟩
  obtain ⟨hc,hr⟩ := rel.packedRepresentatives vars sorted normal slots used (fun v => (scope v).mpr) repr uniform unique
  refine ⟨sorted,hc,fun a m => ⟨hr _ m,?_⟩⟩
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp m
  exact r.val.packedRepresentative_safe (sorted _ r.property) op slots avoid repr
    (fun t ht => (uniform t ht).variables) scope (fresh _ r.property)

end Tamarin.Rewriting.DHExponent.Caller
