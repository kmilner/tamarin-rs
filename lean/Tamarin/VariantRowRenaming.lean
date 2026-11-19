import Tamarin.VariantAntichain

/-! On a finite observation vector, two sorted rows are instances of one
another exactly when the same sort-preserving renaming takes every input
and every output of the first row to the second modulo B. -/
namespace Tamarin.Rewriting.VariantJoin
variable {s : Signature} {I A : Type}

-- A compound term or atom weighs more than any variable. A proper sort
-- narrowing also increases the weight of a variable. Both C and AC preserve it.
private def weightModel (s : Signature) : Model s where
  Carrier := Nat
  atom := fun _ => 2
  free := fun _ args => (List.ofFn args).sum + 2
  comm := fun _ a b => a + b + 2
  ac := fun _ a b => a + b + 2
  comm_swap := by intros; omega
  ac_swap := by intros; omega
  ac_assoc := by intros; omega

private def rank (v : Variable) : Nat := if v.sort = .msg then 0 else 1
private def weight (t : Term s) : Nat := (weightModel s).eval rank t

private theorem image_weight (σ : Substitution s) (v : Variable) :
    rank v ≤ weight (σ.image v) ∧
    (rank v = weight (σ.image v) → ∃ w, σ.image v = .var w ∧ w.sort = v.sort) := by
  have sub := Term.rootSort_le (σ.sorted v)
  cases h : σ.image v with
  | var w =>
    rw [h] at sub
    change Subsort w.sort v.sort at sub
    have prop {a b : SortId} (sa : Subsort a b) :
        (if b = .msg then 0 else 1 : Nat) ≤ (if a = .msg then 0 else 1) ∧
        ((if b = .msg then 0 else 1 : Nat) = (if a = .msg then 0 else 1) → a = b) := by
      cases sa <;> simp
    exact ⟨(prop sub).1,fun eq => ⟨w,rfl,(prop sub).2 eq⟩⟩
  | atom | free | comm | ac =>
    simp only [weight,Model.eval,weightModel,rank]
    split <;> omega

private theorem sums {n : Nat} (a b : Fin n → Nat) (le : ∀ i, a i ≤ b i) :
    (List.ofFn a).sum ≤ (List.ofFn b).sum ∧
    ((List.ofFn a).sum = (List.ofFn b).sum → ∀ i, a i = b i) := by
  induction n with
  | zero => exact ⟨by simp,fun _ i => nomatch i⟩
  | succ n ih =>
    obtain ⟨tl,same⟩ := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => le i.succ)
    have hd := le 0
    simp only [List.ofFn_succ,List.sum_cons]
    refine ⟨by omega,fun eq i => Fin.cases (by omega) (same (by omega)) i⟩

private theorem increases (σ : Substitution s) (t : Term s) :
    weight t ≤ weight (σ.apply t) ∧ (weight t = weight (σ.apply t) →
      ∀ v, t.Occurs v → rank v = weight (σ.image v)) := by
  induction t with
  | var v => exact ⟨(image_weight σ v).1,fun eq _ h => h ▸ eq⟩
  | atom a => exact ⟨Nat.le_refl _,fun _ _ h => h.elim⟩
  | free f args ih =>
    let w := fun i => weight (args i)
    let u := fun i => weight (σ.apply (args i))
    obtain ⟨le,same⟩ := sums w u (fun i => (ih i).1)
    change (List.ofFn w).sum + 2 ≤ (List.ofFn u).sum + 2 ∧ _
    refine ⟨by omega,fun eq v ⟨i,h⟩ => (ih i).2 (same ?_ i) v h⟩
    change (List.ofFn w).sum + 2 = (List.ofFn u).sum + 2 at eq
    omega
  | ac f a b ia ib | comm f a b ia ib =>
    have al := ia.1
    have bl := ib.1
    change weight a + weight b + 2 ≤ weight (σ.apply a) + weight (σ.apply b) + 2 ∧
      (weight a + weight b + 2 = weight (σ.apply a) + weight (σ.apply b) + 2 → _)
    exact ⟨by omega,fun eq v h => h.elim (ia.2 (by omega) v) (ib.2 (by omega) v)⟩

private theorem variable_at {a b : Term s} {σ δ : Substitution s}
    (l : EquivB b (σ.apply a)) (r : EquivB a (δ.apply b)) {v : Variable} (hv : a.Occurs v) :
    ∃ w, σ.image v = .var w ∧ w.sort = v.sort := by
  have la : weight b = weight (σ.apply a) := l.eval_eq _ _
  have lb : weight a = weight (δ.apply b) := r.eval_eq _ _
  obtain ⟨al,same⟩ := increases σ a
  have bl := (increases δ b).1
  exact (image_weight σ v).2 (same (by omega) v hv)

private def name (σ : Substitution s) (v : Variable) : Variable :=
  match σ.image v with
  | .var w => w
  | _ => v

private theorem row_map {p q : Row s I A} {σ δ : Substitution s}
    (fit : Fits p q.input q.value σ) (back : Fits q p.input p.value δ) :
    (∀ v, p.Uses v → σ.image v = .var (name σ v) ∧ (name σ v).sort = v.sort) ∧
    (∀ w, q.Uses w → ∃ v, p.Uses v ∧ name σ v = w) := by
  have maps v (hv : p.Uses v) : σ.image v = .var (name σ v) ∧ (name σ v).sort = v.sort := by
    have toVar : ∃ w, σ.image v = .var w ∧ w.sort = v.sort := by
      rcases hv with ⟨i,h⟩ | ⟨a,h⟩
      · exact variable_at (fit.inputs i) (back.inputs i) h
      · exact variable_at (fit.values a) (back.values a) h
    obtain ⟨w,hw,hs⟩ := toVar
    simpa [name,hw] using hs
  refine ⟨maps,?_⟩
  intro w hw
  have find {l r : Term s} (eq : EquivB r (σ.apply l)) (occ : r.Occurs w)
      (used : ∀ v, l.Occurs v → p.Uses v) : ∃ v, p.Uses v ∧ name σ v = w := by
    obtain ⟨v,hv,h⟩ := σ.occurs_in_image l w ((eq.occurs_iff w).mp occ)
    have use := used v hv
    rw [(maps v use).1] at h
    exact ⟨v,use,h.symm⟩
  rcases hw with ⟨i,h⟩ | ⟨a,h⟩
  · exact find (fit.inputs i) h (fun _ hv => .inl ⟨i,hv⟩)
  · exact find (fit.values a) h (fun _ hv => .inr ⟨a,hv⟩)

private theorem injective_on (xs : List Variable) (nd : xs.Nodup) (f g : Variable → Variable)
    (onto : ∀ w ∈ xs, ∃ v ∈ xs, g (f v) = w) :
    ∀ v ∈ xs, ∀ w ∈ xs, f v = f w → v = w := by
  intro v hv w hw image
  apply Classical.byContradiction
  intro ne
  have sub : xs ⊆ (xs.erase v).map (g ∘ f) := by
    intro t ht
    obtain ⟨x,hx,hit⟩ := onto t ht
    by_cases e : x = v
    · subst x
      exact List.mem_map.mpr ⟨w,(List.mem_erase_of_ne (Ne.symm ne)).mpr hw,(congrArg g image).symm.trans hit⟩
    · exact List.mem_map.mpr ⟨x,(List.mem_erase_of_ne e).mpr hx,hit⟩
  have h := nd.length_le_of_subset sub
  rw [List.length_map,List.length_erase_of_mem hv] at h
  have pos := List.length_pos_of_mem hv
  omega

/-- A single allocation on the finite occurring source variables suffices.
All other variables are unrestricted. Mutual subsumption guarantees both
injectivity and exact sort preservation, even with repeated AC factors. -/
theorem Row.relabels_of_mutual {p q : Row s I A} (sources : List Variable) (nd : sources.Nodup)
    (scope : ∀ v, v ∈ sources ↔ p.Uses v) (pq : p.Subsumes q) (qp : q.Subsumes p) :
    p.Relabels q := by
  obtain ⟨σ,fit⟩ := pq
  obtain ⟨δ,back⟩ := qp
  obtain ⟨maps,onto⟩ := row_map fit back
  have inv := (row_map back fit).2
  have inj := injective_on sources nd (name σ) (name δ) (by
    intro w hw
    obtain ⟨u,hu,uw⟩ := inv w ((scope w).mp hw)
    obtain ⟨v,hv,vu⟩ := onto u hu
    exact ⟨v,(scope v).mpr hv,vu ▸ uw⟩)
  have on (t : Term s) (used : ∀ v, t.Occurs v → p.Uses v) :
      t.subst (fun v => .var (name σ v)) = σ.apply t :=
    Term.subst_eq_of_agree _ _ _ (fun v hv => (maps v (used v hv)).1.symm)
  apply Row.Relabels.of_allocation sources ⟨name σ,fun v hv => (maps v ((scope v).mp hv)).2,inj⟩
    (fun v => (scope v).mpr)
  · intro i; exact (on _ (fun _ h => .inl ⟨i,h⟩)) ▸ (fit.inputs i).symm
  · intro a; exact (on _ (fun _ h => .inr ⟨a,h⟩)) ▸ (fit.values a).symm

private theorem distinct_inventory (xs : List Variable) :
    ∃ ys : List Variable, ys.Nodup ∧ ∀ v, v ∈ ys ↔ v ∈ xs := by
  induction xs with
  | nil => exact ⟨[],List.nodup_nil,fun _ => Iff.rfl⟩
  | cons x xs ih =>
    obtain ⟨ys,nd,mem⟩ := ih
    by_cases h : x ∈ ys
    · refine ⟨ys,nd,?_⟩
      intro v; rw [List.mem_cons,← mem]; exact ⟨Or.inr,fun e => e.elim (fun eq => eq ▸ h) id⟩
    · exact ⟨x::ys,List.nodup_cons.mpr ⟨h,nd⟩,fun v => by simp [mem]⟩

/-- For finite observation vectors the equivalence classes in
`Exact.irredundant_perm` are precisely whole-row alpha-renaming classes
modulo B. The enumeration can contain repeated input or output slots. -/
theorem Row.instanceClass_eq_iff_relabels (ins : List I) (outs : List A)
    (ki : ∀ i, i ∈ ins) (ko : ∀ o, o ∈ outs) (p q : Row s I A) :
    p.instanceClass = q.instanceClass ↔ p.Relabels q := by
  constructor
  · intro eq
    let vars := (ins.flatMap (fun i => (p.input i).variables)) ++
      outs.flatMap (fun o => (p.value o).variables)
    obtain ⟨xs,nd,scope⟩ := distinct_inventory vars
    have m : ∀ v, v ∈ xs ↔ p.Uses v := by
      intro v
      rw [scope]
      simp only [vars,List.mem_append,List.mem_flatMap,Term.mem_variables,Row.Uses]
      exact or_congr ⟨fun ⟨i,_,h⟩ => ⟨i,h⟩,fun ⟨i,h⟩ => ⟨i,ki i,h⟩⟩
        ⟨fun ⟨a,_,h⟩ => ⟨a,h⟩,fun ⟨a,h⟩ => ⟨a,ko a,h⟩⟩
    exact p.relabels_of_mutual xs nd m (Quotient.exact eq).1 (Quotient.exact eq).2
  · rintro ⟨π,ls,rs⟩
    apply Quotient.sound
    have inv {a b : Term s} (e : EquivB ((π.subst s).apply a) b) :
        EquivB a ((π.inverse.subst s).apply b) := by
      have h := e.subst (π.inverse.subst s).image
      change EquivB ((π.inverse.subst s).apply ((π.subst s).apply a)) _ at h
      rwa [π.inverse_apply] at h
    exact ⟨⟨π.subst s,fun i => (ls i).symm,fun i => (rs i).symm⟩,
      ⟨π.inverse.subst s,fun i => inv (ls i),fun i => inv (rs i)⟩⟩

end Tamarin.Rewriting.VariantJoin
