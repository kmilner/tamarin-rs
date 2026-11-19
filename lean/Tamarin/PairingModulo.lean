import Tamarin.PairingVariants

/-! Compatibility with the ambient AC theory. A projection cannot acquire or
lose a pair at its root merely by reassociating or permuting union operands.
Normal forms are consequently unique modulo B, including when rewriting and
AC rearrangement are interleaved. -/
namespace Tamarin.Pairing

def isPair : PTerm → Bool
  | .free .pair _ => true
  | _ => false

theorem isPair_equiv {a b : PTerm} (h : EquivB a b) : isPair a = isPair b := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b _ _ => cases f <;> rfl
  | comm_congr _ _ _ _ _ => rfl
  | ac_congr _ _ _ _ _ => rfl
  | comm_swap _ _ _ => rfl
  | ac_swap _ _ _ => rfl
  | ac_assoc _ _ _ _ => rfl

theorem not_pair_iff (t : PTerm) :
    (∀ args, t ≠ .free .pair args) ↔ isPair t = false := by
  cases t with
  | free f args => cases f <;> simp [isPair]
  | _ => simp [isPair]

theorem projection_congr (first : Bool) {a b : PTerm} (h : EquivB a b) :
    EquivB (projection first a) (projection first b) := by
  cases first <;> exact .free _ _ _ (fun _ => h)

theorem project_congr (first : Bool) {a b : PTerm} (h : EquivB a b) :
    EquivB (project first a) (project first b) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact .trans ih ik
  | free f a b h _ =>
    cases f with
    | pair => cases first <;> exact h _
    | fst => exact projection_congr first (.free _ _ _ h)
    | snd => exact projection_congr first (.free _ _ _ h)
    | other id n => exact projection_congr first (.free _ _ _ h)
  | comm_congr f h k _ _ => exact projection_congr first (.comm_congr f h k)
  | ac_congr f h k _ _ => exact projection_congr first (.ac_congr f h k)
  | comm_swap f a b => exact projection_congr first (.comm_swap f a b)
  | ac_swap f a b => exact projection_congr first (.ac_swap f a b)
  | ac_assoc f a b c => exact projection_congr first (.ac_assoc f a b c)

theorem normalize_equiv {a b : PTerm} (h : EquivB a b) :
    EquivB (normalize a) (normalize b) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact .trans ih ik
  | free f a b _ ih =>
    cases f with
    | pair =>
      simp only [normalize]
      rw [pair_eta (fun i => normalize (a i)), pair_eta (fun i => normalize (b i))]
      exact .free _ _ _ ih
    | fst => exact project_congr true (ih 0)
    | snd => exact project_congr false (ih 0)
    | other id n => exact EquivB.free (sig := signature) (.other id n) _ _ ih
  | comm_congr f _ _ ih ik => exact .comm_congr f ih ik
  | ac_congr f _ _ ih ik => exact .ac_congr f ih ik
  | comm_swap f a b => exact .comm_swap f _ _
  | ac_swap f a b => exact .ac_swap f _ _
  | ac_assoc f a b c => exact .ac_assoc f _ _ _

theorem normal_free_pair (args : Fin 2 → PTerm) :
    Normal (.free .pair args) ↔ Normal (args 0) ∧ Normal (args 1) := by
  constructor
  · exact normal_pair_children
  · intro h; rw [← pair_eta args]; exact .pair h.1 h.2

theorem normal_fst (a : PTerm) : Normal (fst a) ↔ Normal a ∧ isPair a = false := by
  constructor
  · intro h
    have inv : ∀ t, Normal t → match t with
        | .free .fst args => Normal (args 0) ∧ isPair (args 0) = false
        | _ => True := by
      intro t ht
      cases ht with
      | @fst a ha hn => exact ⟨ha, (not_pair_iff a).mp hn⟩
      | _ => trivial
    exact inv _ h
  · intro h; exact .fst h.1 ((not_pair_iff a).mpr h.2)

theorem normal_snd (a : PTerm) : Normal (snd a) ↔ Normal a ∧ isPair a = false := by
  constructor
  · intro h
    have inv : ∀ t, Normal t → match t with
        | .free .snd args => Normal (args 0) ∧ isPair (args 0) = false
        | _ => True := by
      intro t ht
      cases ht with
      | @snd a ha hn => exact ⟨ha, (not_pair_iff a).mp hn⟩
      | _ => trivial
    exact inv _ h
  · intro h; exact .snd h.1 ((not_pair_iff a).mpr h.2)

theorem normal_ac (f : Nat) (a b : PTerm) :
    Normal (.ac f a b) ↔ Normal a ∧ Normal b := by
  constructor
  · intro h; cases h with | ac _ ha hb => exact ⟨ha, hb⟩
  · intro h; exact .ac f h.1 h.2

theorem normal_comm (f : Nat) (a b : PTerm) :
    Normal (.comm f a b) ↔ Normal a ∧ Normal b := by
  constructor
  · intro h; cases h with | comm _ ha hb => exact ⟨ha, hb⟩
  · intro h; exact .comm f h.1 h.2

theorem normal_other (id n : Nat) (args : Fin n → PTerm) :
    Normal (.free (.other id n) args) ↔ ∀ i, Normal (args i) := by
  constructor
  · intro h; cases h with | other _ _ _ hn => exact hn
  · exact .other id n args

/-- Normality is stable under AC rearrangement: the syntactic normal forms
have no projection redex in any B-equivalent representative either. -/
theorem normal_equiv {a b : PTerm} (h : EquivB a b) : Normal a ↔ Normal b := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b h ih =>
    cases f with
    | pair => simp only [normal_free_pair, ih]
    | fst =>
      rw [← unary_eta a, ← unary_eta b]
      change Normal (fst (a 0)) ↔ Normal (fst (b 0))
      simp only [normal_fst, ih 0, isPair_equiv (h 0)]
    | snd =>
      rw [← unary_eta a, ← unary_eta b]
      change Normal (snd (a 0)) ↔ Normal (snd (b 0))
      simp only [normal_snd, ih 0, isPair_equiv (h 0)]
    | other id n => simp only [normal_other, ih]
  | comm_congr f _ _ ih ik => simp only [normal_comm, ih, ik]
  | ac_congr f _ _ ih ik => simp only [normal_ac, ih, ik]
  | comm_swap f a b => simp only [normal_comm, and_comm]
  | ac_swap f a b => simp only [normal_ac, and_comm]
  | ac_assoc f a b c => simp only [normal_ac, and_assoc]

/-- Rewrite modulo B. The context constructors make contextual closure
explicit, including contexts containing both pairing and multiset symbols. -/
inductive ReducesModulo : PTerm → PTerm → Prop where
  | basis {a b} : EquivB a b → ReducesModulo a b
  | rewrite {a b} : Reduces a b → ReducesModulo a b
  | trans {a b c} : ReducesModulo a b → ReducesModulo b c → ReducesModulo a c
  | free (f : Symbol) (a b : Fin (signature.arity f) → PTerm)
      (h : ∀ i, ReducesModulo (a i) (b i)) : ReducesModulo (.free f a) (.free f b)
  | comm (f : Nat) {a b c d} : ReducesModulo a c → ReducesModulo b d →
      ReducesModulo (.comm f a b) (.comm f c d)
  | ac (f : Nat) {a b c d} : ReducesModulo a c → ReducesModulo b d →
      ReducesModulo (.ac f a b) (.ac f c d)

theorem reducesModulo_normalize {a b : PTerm} (h : ReducesModulo a b) :
    EquivB (normalize a) (normalize b) := by
  induction h with
  | basis h => exact normalize_equiv h
  | rewrite h => rw [reduces_normalize h]; exact .refl _
  | trans _ _ ih ik => exact .trans ih ik
  | free f a b _ ih =>
    cases f with
    | pair =>
      simp only [normalize]
      rw [pair_eta (fun i => normalize (a i)), pair_eta (fun i => normalize (b i))]
      exact .free _ _ _ ih
    | fst => exact project_congr true (ih 0)
    | snd => exact project_congr false (ih 0)
    | other id n => exact EquivB.free (sig := signature) (.other id n) _ _ ih
  | ac f _ _ ih ik => exact .ac_congr f ih ik
  | comm f _ _ ih ik => exact .comm_congr f ih ik

theorem normal_unique_modulo {t a b : PTerm}
    (ha : ReducesModulo t a) (hb : ReducesModulo t b)
    (na : Normal a) (nb : Normal b) : EquivB a b := by
  have h := (reducesModulo_normalize ha).symm.trans (reducesModulo_normalize hb)
  simpa only [normal_fixed na, normal_fixed nb] using h

/-- The exact representative-level variant coverage previously proved is
stronger than coverage modulo B. AC canonicalization may change representatives
at the boundary, while one shared instantiation must still cover every term. -/
def CoversModulo (q : List PTerm) (ρ σ : PSubst) : Prop :=
  ∃ δ : PSubst, Normalized δ ∧
    (∀ v, Observed q v → EquivB (ρ.image v) (δ.apply (σ.image v))) ∧
    ∀ t ∈ q, EquivB (normalize (ρ.apply t)) (δ.apply (normalize (σ.apply t)))

theorem covers_modulo {q : List PTerm} {ρ σ : PSubst} (h : Covers q ρ σ) :
    CoversModulo q ρ σ := by
  obtain ⟨δ, hn, hv, ht⟩ := h
  refine ⟨δ, hn, ?_, ?_⟩
  · intro v h; rw [hv v h]; exact .refl _
  · intro t h; rw [ht t h]; exact .refl _

/-- Semantic variant validity and coverage modulo the combined theory. The
normal value remains irreducible in every B-equivalent representative. -/
def CompleteVariantsModulo (q : List PTerm) (answers : List PSubst) : Prop :=
  (∀ σ ∈ answers, Normalized σ ∧ ∀ t ∈ q,
    ReducesModulo (σ.apply t) (normalize (σ.apply t)) ∧
    ∀ u, EquivB (normalize (σ.apply t)) u → Normal u) ∧
  ∀ ρ, Normalized ρ → ∃ σ ∈ answers, CoversModulo q ρ σ

theorem complete_variants_modulo {q : List PTerm} {answers : List PSubst}
    (h : CompleteVariants q answers) : CompleteVariantsModulo q answers := by
  constructor
  · intro σ hσ
    refine ⟨h.1 σ hσ, ?_⟩
    intro t _
    refine ⟨.rewrite (normalize_reduces _), ?_⟩
    intro u hu; exact (normal_equiv hu).mp (normalize_normal _)
  · intro ρ hρ
    obtain ⟨σ, hσ, hc⟩ := h.2 ρ hρ
    exact ⟨σ, hσ, covers_modulo hc⟩

end Tamarin.Pairing
