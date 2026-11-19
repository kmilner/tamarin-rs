import Tamarin.MatchingConjunction

/-! Free constructors preserve positional matching modulo B, even when their
children contain C or AC operators. All child equations share one substitution. -/
namespace Tamarin.Matching
variable {sig : Signature}

private noncomputable def child (f : sig.FreeSym) (i : Fin (sig.arity f))
    (t : Term sig) : Term sig := by
  classical
  exact match t with
    | .free g args => if h : f = g then args (h ▸ i) else .var ⟨0, .msg⟩
    | _ => .var ⟨0, .msg⟩

private theorem child_congr (f : sig.FreeSym) (i : Fin (sig.arity f))
    {s t : Term sig} (h : EquivB s t) : EquivB (child f i s) (child f i t) := by
  classical
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free g a b h _ =>
    by_cases he : f = g
    · subst g; simpa [child] using h i
    · simp only [child, he, ↓reduceDIte]; exact .refl _
  | comm_congr | ac_congr | comm_swap | ac_swap | ac_assoc => exact .refl _

theorem free_equiv_iff (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig) :
    EquivB (.free f a) (.free f b) ↔ ∀ i, EquivB (a i) (b i) := by
  constructor
  · intro h i; simpa [child] using child_congr f i h
  · exact EquivB.free f a b

def children (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig) : Problem sig :=
  List.ofFn fun i => ⟨a i, b i⟩

/-- Replacing a free application anywhere in a matching conjunction by its
children preserves both the matching predicate and the observed domain. -/
theorem free_complete_iff (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig)
    (rest : Problem sig) (bindable : Variable → Prop) (answers : List (Substitution sig)) :
    Complete (⟨.free f a, .free f b⟩ :: rest) bindable answers ↔
      Complete (children f a b ++ rest) bindable answers := by
  have hm (σ : Substitution sig) : Matches (⟨.free f a, .free f b⟩ :: rest) σ ↔
      Matches (children f a b ++ rest) σ := by
    simp [Matches, children, List.mem_append, or_imp, forall_and, free_equiv_iff,
      Substitution.apply, Term.subst]
  have ho : Observed (⟨.free f a, .free f b⟩ :: rest) = Observed (children f a b ++ rest) := by
    funext v; apply propext
    simp [Observed, children, List.mem_append, or_and_right, exists_or, Term.Occurs]
    grind
  have hsc (σ : Substitution sig) : Scoped (⟨.free f a, .free f b⟩ :: rest) bindable σ ↔
      Scoped (children f a b ++ rest) bindable σ := by simp only [Scoped, ho]
  constructor <;> intro h
  · exact ⟨fun σ hs => ⟨(hm σ).mp (h.sound σ hs).1, (hsc σ).mp (h.sound σ hs).2⟩,
      fun ρ hh hs => ho ▸ h.covers ρ ((hm ρ).mpr hh) ((hsc ρ).mpr hs)⟩
  · exact ⟨fun σ hs => ⟨(hm σ).mpr (h.sound σ hs).1, (hsc σ).mpr (h.sound σ hs).2⟩,
      fun ρ hh hs => ho.symm ▸ h.covers ρ ((hm ρ).mp hh) ((hsc ρ).mp hs)⟩

end Tamarin.Matching
