import Tamarin.DHSignedBlocks

/-! Soundness of the signed matrix templates. Each active witness is itself
a factor, with exactly the sign and weight of its generator in each coordinate. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open ACBasis Cancellation Balance Classical
variable {n : Nat} {sig : Signature}

private theorem column_counts (basis : (Fin n → Bool) → List (Vec n)) (active)
    (branch : active ∈ FlatMatchSearch.sublists (columns basis)) (g : Column basis) (i : Fin n) (d : Bool) :
    (slots basis active i d).count g =
      if g.1 i = d ∧ g ∈ active then (basis g.1).get g.2 i else 0 := by
  classical
  let mag (g : Column basis) : Vec n := if g ∈ active then (basis g.1).get g.2 else fun _ => 0
  let bag (g : Column basis) := if g ∈ active then [g] else []
  let b : Blocks basis Sigma.fst mag := {
    active := active, branch := branch, bag := bag
    selected := fun g => by by_cases h : g ∈ active <;> simp [bag,h]
    conformal := by
      intro g k h
      simp only [bag] at h
      split at h <;> simp_all
    counts := by
      rintro ⟨d,j⟩
      by_cases h : (⟨d,j⟩ : Column basis) ∈ active
      · have coeff (k : Fin (basis d).length) :
            (bag ⟨d,k⟩).count ⟨d,j⟩ = spike j 1 k := by
          by_cases he : k = j
          · subst k; simp [bag,h,spike]
          · have ne : (⟨d,k⟩ : Column basis) ≠ ⟨d,j⟩ := by simpa using he
            by_cases mem : (⟨d,k⟩ : Column basis) ∈ active <;> simp [bag,mem,ne,spike,he]
        funext i
        simp only [mix,coeff,dot_spike,Nat.mul_one]
        simp [mag,h]
      · have zero (k : Fin (basis d).length) : (bag ⟨d,k⟩).count ⟨d,j⟩ = 0 := by
          by_cases he : k = j
          · subst k; simp [bag,h]
          · have ne : (⟨d,k⟩ : Column basis) ≠ ⟨d,j⟩ := by simpa using he
            by_cases mem : (⟨d,k⟩ : Column basis) ∈ active <;> simp [bag,mem,ne]
        funext i
        simp [mag,h,mix,dot,total,zero,List.sum_eq_zero_iff_forall_eq_nat] }
  have eq := b.coordinate_count i d g
  have singleton (xs : List (Column basis)) (live : ∀ x ∈ xs, x ∈ active) :
      xs.flatMap bag = xs := by
    induction xs with
    | nil => rfl
    | cons y ys ih => simp [bag,live y List.mem_cons_self,show ys.flatMap bag = ys from
          ih (fun x hx => live x (List.mem_cons_of_mem _ hx))]
  change ((slots basis active i d).flatMap bag).count g = _ at eq
  rw [singleton _ (fun _ h => (slot_properties h).1)] at eq
  by_cases ha : g ∈ active <;> by_cases hd : g.1 i = d <;> simpa [mag,ha,hd] using eq

/-- Each finite branch satisfies every simultaneous equation at all normal
endpoints. Witness names can be selected afresh by the caller. -/
theorem template_sound [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Inventory E) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (system : List (Constraint n))
    (basis : (Fin n → Bool) → List (Vec n)) (valid : ∀ d, BasisCorrect (system.map (row d)) (basis d))
    (active) (branch : active ∈ FlatMatchSearch.sublists (columns basis))
    (name : Column basis → Variable) (inj : Function.Injective name) (sort : ∀ g, (name g).sort = .msg)
    (value : Expr n → Term sig)
    (normal : ∀ eq ∈ system, ∀ e, e = eq.1 ∨ e = eq.2 →
      NormalForm (ruleRoot T.rules) (e.term s (template s basis active name)) (value e)) :
    ∀ eq ∈ system, EquivB (value eq.1) (value eq.2) := by
  classical
  let env := template s basis active name
  let cls (g : Column basis) := classOf (sig := sig) (.var (name g))
  have inject : Function.Injective cls := fun _ _ eq => inj (Head.var.inj (Quotient.exact eq).head_eq)
  have reps (k : Class sig) : ∃ d x, Generates (basis d) x ∧
      ∀ i, read s (ruleRoot T.rules) k (env i) = some (signed d x i) := by
    by_cases occurs : ∃ g ∈ active, cls g = k
    · obtain ⟨g,hg,rfl⟩ := occurs
      refine ⟨g.1,(basis g.1).get g.2,⟨spike g.2 1,?_⟩,?_⟩
      · funext i; simp [mix,dot_spike]
      have count (xs : List (Column basis)) : (xs.map cls).count (cls g) = xs.count g := by
        induction xs with
        | nil => rfl
        | cons j js ih =>
          by_cases same : j = g
          · subst j; simp [ih]
          · have ne : cls j ≠ cls g := fun h => same (inject h)
            simp [ih,same,ne]
      intro i
      rw [template_read s _ (ConstructorVariants.constructor_normal _ inventory.1).1 basis active name i (cls g)]
      change some ((((slots basis active i false).map cls).count (cls g) : Int) - _) = _
      rw [count,count,column_counts _ _ branch,column_counts _ _ branch]
      cases h : g.1 i <;> simp [hg,signed,h]
    · let d := fun _ : Fin n => false
      refine ⟨d,fun _ => 0,⟨fun _ => 0,?_⟩,?_⟩
      · funext i; simp [mix,dot,total,List.sum_eq_zero_iff_forall_eq_nat]
      intro i
      have count (neg : Bool) : ((slots basis active i neg).map cls).count k = 0 := by
        apply List.count_eq_zero.mpr
        rintro h
        obtain ⟨g,hg,eq⟩ := List.mem_map.mp h
        exact occurs ⟨g,(slot_properties hg).1,eq⟩
      rw [template_read s _ (ConstructorVariants.constructor_normal _ inventory.1).1 basis active name i k]
      change some ((((slots basis active i false).map cls).count k : Int) - _) = _
      rw [count,count]
      rfl
  let d := fun k => (reps k).choose
  let x := fun k => (reps k).choose_spec.choose
  have h k := (reps k).choose_spec.choose_spec
  exact (normalForms_iff inventory env system d x (fun k => (h k).2) basis valid value
    (fun i => (template_normal mul inv unit basis active name inj sort i).1) normal).mpr (fun k => (h k).1)

end Tamarin.Rewriting.DHPeer.SignedMatrix
