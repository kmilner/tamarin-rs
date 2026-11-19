import Tamarin.Matching

/-! Check the ground comparisons of a directional conjunction before
allocating search state for the equations that can supply bindings. -/
namespace Tamarin.Matching
variable {sig : Signature}

/-- An arbitrary partition and order are allowed. Only the pattern in each
guard needs to be ground. Rigid occurrences in the subject cannot bind. -/
theorem checked_guards {p guards rest : Problem sig} (parts : p.Perm (guards ++ rest))
    (closed : ∀ e ∈ guards, e.lhs.Ground) (pass : Bool)
    (checked : pass = true ↔ ∀ e ∈ guards, EquivB e.lhs e.rhs)
    (bindable : Variable → Prop) (answers : List (Substitution sig))
    (solve : pass = true → Complete rest bindable answers) :
    Complete p bindable (if pass then answers else []) := by
  have obs (v) : Observed p v ↔ Observed rest v := by
    constructor
    · rintro ⟨e,h,occ⟩
      rcases List.mem_append.mp (parts.mem_iff.mp h) with g | r
      · exact False.elim (closed e g v occ)
      · exact ⟨e,r,occ⟩
    · rintro ⟨e,h,occ⟩
      exact ⟨e,parts.mem_iff.mpr (List.mem_append_right _ h),occ⟩
  have matched (σ : Substitution sig) : Matches p σ ↔ pass = true ∧ Matches rest σ := by
    constructor
    · intro all
      refine ⟨checked.mpr (fun e h => ?_),fun e h => all e (parts.mem_iff.mpr (List.mem_append_right _ h))⟩
      simpa only [(closed e h).apply_eq σ] using all e (parts.mem_iff.mpr (List.mem_append_left _ h))
    · rintro ⟨yes,remaining⟩ e h
      rcases List.mem_append.mp (parts.mem_iff.mp h) with g | r
      · rw [(closed e g).apply_eq σ]; exact checked.mp yes e g
      · exact remaining e r
  have sameScope (σ : Substitution sig) : Scoped p bindable σ ↔ Scoped rest bindable σ := by
    simp only [Scoped,obs]
  cases yes : pass with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply (empty_iff p bindable).mpr
    rintro ⟨σ,h,_⟩
    exact Bool.noConfusion (yes.symm.trans ((matched σ).mp h).1)
  | true =>
    simp only [↓reduceIte]
    constructor
    · intro σ h
      obtain ⟨hm,hs⟩ := (solve yes).sound σ h
      exact ⟨(matched σ).mpr ⟨yes,hm⟩,(sameScope σ).mpr hs⟩
    · intro ρ h hs
      obtain ⟨σ,mem,agree⟩ := (solve yes).covers ρ ((matched ρ).mp h).2 ((sameScope ρ).mp hs)
      exact ⟨σ,mem,fun v hv => agree v ((obs v).mp hv)⟩

end Tamarin.Matching
