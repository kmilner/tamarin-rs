import Tamarin.MixedUnification

/-! A Tamarin module can omit TamNat entirely. A sorted instance cannot
remove the occurrence of that sort from a witness by substituting for it. -/
namespace Tamarin.UnavailableSort
variable {s : Signature}

private def markers (s : Signature) (k : SortId) : Model s where
  Carrier := Bool
  atom a := s.atomSort a == k
  free f args := (s.outputSort f == k) || (List.ofFn args).any id
  comm f l r := (s.cSort f == k) || l || r
  ac f l r := (s.acSort f == k) || l || r
  comm_swap := by intros; simp [Bool.or_comm,Bool.or_left_comm]
  ac_swap := by intros; simp [Bool.or_comm,Bool.or_left_comm]
  ac_assoc := by intros; simp [Bool.or_comm,Bool.or_left_comm]

def marked (k : SortId) (t : Term s) : Bool :=
  (markers s k).eval (fun v => v.sort == k) t

private theorem root_marked (t : Term s) (k : SortId) (h : t.rootSort = k) : marked k t := by
  cases t <;> simp_all [Term.rootSort,marked,markers,Model.eval]

private theorem occurrence (t : Term s) {v : Variable} (occ : t.Occurs v) (σ : Substitution s)
    (k : SortId) (h : marked k (σ.image v)) : marked k (σ.apply t) := by
  induction t with
  | var u => exact occ ▸ h
  | atom a => contradiction
  | free f args ih =>
    obtain ⟨i,hi⟩ := occ
    apply Bool.or_eq_true_iff.mpr (.inr _)
    exact List.any_eq_true.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,ih i hi⟩
  | comm f a b ia ib | ac f a b ia ib =>
    rcases occ with h|h
    · exact Bool.or_eq_true_iff.mpr (.inl (Bool.or_eq_true_iff.mpr (.inr (ia h))))
    · exact Bool.or_eq_true_iff.mpr (.inr (ib h))

def noNatWitness (p : Problem s) (σ : Substitution s) := p.variables.all fun v =>
  (σ.image v).variables.all (fun w => w.sort != .nat)

/-- Substitution cannot erase an occurrence of a Nat variable modulo B.
Any instance with Nat-free observed images therefore factors through a row
with no Nat witness in any observed image. -/
theorem clean_images (vs : List Variable) (ρ σ δ : Substitution s)
    (clean : ∀ v ∈ vs, marked .nat (ρ.image v) = false)
    (agree : ∀ v ∈ vs, EquivB (ρ.image v) (δ.apply (σ.image v))) :
    vs.all (fun v => (σ.image v).variables.all (fun w => w.sort != .nat)) := by
  refine List.all_eq_true.mpr (fun v hv => List.all_eq_true.mpr (fun w hw => ?_))
  by_cases eq : w.sort = .nat
  case neg => simpa using eq
  exfalso
  have sort := Term.rootSort_le (δ.sorted w)
  rw [eq] at sort
  have nat_only {k : SortId} (h : Subsort k .nat) : k = .nat := by cases h; rfl
  have root := nat_only sort
  have got := occurrence (σ.image v) ((Term.mem_variables ..).mp hw) δ .nat (root_marked _ _ root)
  have same := (agree v hv).eval_eq (markers s .nat) (fun i => i.sort == .nat)
  change marked .nat (ρ.image v) = marked .nat (δ.apply (σ.image v)) at same
  rw [clean v hv,got] at same
  contradiction

/-- For any Nat-free caller solution the filtered family has exactly the same
instance test. Dropping an arm with a Nat witness cannot hide a solution. -/
theorem filterNat_iff (p : Problem s) {rows : List (Substitution s)} (hc : CompleteSet p rows)
    (ρ : Substitution s) (clean : ∀ v, p.Occurs v → marked .nat (ρ.image v) = false) :
    p.Solves ρ ↔ ∃ σ ∈ rows.filter (noNatWitness p), Substitution.InstanceOn p.Occurs ρ σ := by
  rw [hc.solves_iff]
  constructor
  · rintro ⟨σ,hs,δ,agree⟩
    refine ⟨σ,List.mem_filter.mpr ⟨hs,?_⟩,δ,agree⟩
    exact clean_images p.variables ρ σ δ (fun v hv => clean v ((p.mem_variables _).mp hv))
      (fun v hv => agree v ((p.mem_variables _).mp hv))
  · rintro ⟨σ,hm,agree⟩
    exact ⟨σ,(List.mem_filter.mp hm).1,agree⟩

end Tamarin.UnavailableSort
