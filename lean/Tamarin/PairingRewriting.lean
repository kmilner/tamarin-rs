import Tamarin.PairingModulo
import Tamarin.NormalizeDriver

/-! The projection specialization inhabits the shared rewriting/variant
semantics. Arbitrarily many uninterpreted free/C/AC declarations may surround
its two root rules; no further rewrite equations are assumed. -/
namespace Tamarin.Pairing

def root (t u : PTerm) : Prop := ∃ a b : PTerm,
  (t = fst (pair a b) ∧ u = a) ∨ (t = snd (pair a b) ∧ u = b)

private def ruleX : Variable := ⟨0, .msg⟩
private def ruleY : Variable := ⟨1, .msg⟩

/-- The actual equation table, interpreted by the shared rule machinery. -/
def rules : List (Equation signature) :=
  [⟨fst (pair (.var ruleX) (.var ruleY)), .var ruleX⟩,
   ⟨snd (pair (.var ruleX) (.var ruleY)), .var ruleY⟩]

theorem ruleRoot_implies_root {t u : PTerm} (h : Rewriting.ruleRoot rules t u) : root t u := by
  obtain ⟨r, hr, σ, rfl, rfl⟩ := h
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨σ.image ruleX, σ.image ruleY, Or.inl ⟨?_, rfl⟩⟩
    simp only [Substitution.apply, subst_fst, subst_pair, Term.subst]
  · refine ⟨σ.image ruleX, σ.image ruleY, Or.inr ⟨?_, rfl⟩⟩
    simp only [Substitution.apply, subst_snd, subst_pair, Term.subst]

private theorem free_children {f : Symbol} {args : Fin (signature.arity f) → PTerm}
    {s : SortId} (h : HasSort (sig := signature) (.free f args) s) : ∀ i, HasSort (args i) .msg := by
  have hc := Term.checkSort_complete h
  simp only [Term.checkSort, Bool.and_eq_true, List.all_eq_true] at hc
  intro i; exact Term.checkSort_sound _ _ (hc.2 i (List.mem_finRange i))

/-- On well-sorted inputs the projection specialization is exactly the finite
rule table, not an additional trusted interpretation of the built-in names. -/
theorem root_iff_ruleRoot {t u : PTerm} {s : SortId} (ht : HasSort t s) :
    root t u ↔ Rewriting.ruleRoot rules t u := by
  constructor
  · intro h
    obtain ⟨a, b, h | h⟩ := h
    · rcases h with ⟨ht', hu'⟩; subst t; subst u
      have hs := pair_children (free_children ht 0)
      let σ := parameters ruleX ruleY a b (hs 0) (hs 1)
      refine ⟨⟨fst (pair (.var ruleX) (.var ruleY)), .var ruleX⟩, by simp [rules], σ, ?_, ?_⟩
      · simp [Substitution.apply, σ, parameters, ruleX, ruleY, Term.subst]
      · simp [Substitution.apply, σ, parameters, ruleX, ruleY, Term.subst]
    · rcases h with ⟨ht', hu'⟩; subst t; subst u
      have hs := pair_children (free_children ht 0)
      let σ := parameters ruleX ruleY a b (hs 0) (hs 1)
      refine ⟨⟨snd (pair (.var ruleX) (.var ruleY)), .var ruleY⟩, by simp [rules], σ, ?_, ?_⟩
      · simp [Substitution.apply, σ, parameters, ruleX, ruleY, Term.subst]
      · simp [Substitution.apply, σ, parameters, ruleX, ruleY, Term.subst]
  · exact ruleRoot_implies_root

theorem root_not_normal {t u : PTerm} (h : root t u) : ¬ Normal t := by
  obtain ⟨a, b, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    intro hn; have := (normal_fst _).mp hn; cases this.2
  · rcases h with ⟨rfl, rfl⟩
    intro hn; have := (normal_snd _).mp hn; cases this.2

theorem normal_free_children {f : Symbol} {args : Fin (signature.arity f) → PTerm}
    (h : Normal (.free f args)) : ∀ i, Normal (args i) := by
  cases f with
  | pair =>
    have hn := (normal_free_pair _).mp h
    intro i; refine Fin.cases hn.1 (fun j => ?_) i
    have : j = 0 := Subsingleton.elim j 0; subst j; exact hn.2
  | fst =>
    rw [← unary_eta args] at h
    intro i; have : i = 0 := Subsingleton.elim i 0; subst i
    exact ((normal_fst _).mp h).1
  | snd =>
    rw [← unary_eta args] at h
    intro i; have : i = 0 := Subsingleton.elim i 0; subst i
    exact ((normal_snd _).mp h).1
  | other id n => exact (normal_other id n args).mp h

theorem step_not_normal {t u : PTerm} (h : Rewriting.Step root t u) : ¬ Normal t := by
  induction h with
  | root h => exact root_not_normal h
  | free f args i h ih => exact fun hn => ih (normal_free_children hn i)
  | comm_left f c h ih => exact fun hn => ih ((normal_comm _ _ _).mp hn).1
  | comm_right f c h ih => exact fun hn => ih ((normal_comm _ _ _).mp hn).2
  | ac_left f c h ih => exact fun hn => ih ((normal_ac _ _ _).mp hn).1
  | ac_right f c h ih => exact fun hn => ih ((normal_ac _ _ _).mp hn).2

theorem normal_free_of_children {f : Symbol} {args : Fin (signature.arity f) → PTerm}
    (hc : ∀ i, Normal (args i)) (hr : ∀ u, ¬ root (.free f args) u) : Normal (.free f args) := by
  cases f with
  | pair => exact (normal_free_pair _).mpr ⟨hc 0, hc 1⟩
  | other id n => exact .other id n _ hc
  | fst =>
    rw [← unary_eta args]
    apply Normal.fst (hc 0)
    intro children he
    apply hr (children 0)
    refine ⟨children 0, children 1, Or.inl ⟨?_, rfl⟩⟩
    rw [pair_eta, ← he]
    congr; exact (unary_eta args).symm
  | snd =>
    rw [← unary_eta args]
    apply Normal.snd (hc 0)
    intro children he
    apply hr (children 1)
    refine ⟨children 0, children 1, Or.inr ⟨?_, rfl⟩⟩
    rw [pair_eta, ← he]
    congr; exact (unary_eta args).symm

theorem normal_or_step (t : PTerm) : Normal t ∨ ∃ u, Rewriting.Step root t u := by
  classical
  induction t with
  | var v => exact Or.inl (.var v)
  | atom a => exact Or.inl (.atom a)
  | free f args ih =>
    by_cases hc : ∀ i, Normal (args i)
    · by_cases hr : ∃ u, root (.free f args) u
      · obtain ⟨u, hu⟩ := hr; exact Or.inr ⟨u, .root hu⟩
      · exact Or.inl (normal_free_of_children hc (fun u hu => hr ⟨u, hu⟩))
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hc
      rcases ih i with hn | ⟨u, hu⟩
      · exact False.elim (hi hn)
      · exact Or.inr ⟨_, .free f args i hu⟩
  | comm f a b ia ib =>
    rcases ia with ha | ⟨u, hu⟩
    · rcases ib with hb | ⟨u, hu⟩
      · exact Or.inl (.comm f ha hb)
      · exact Or.inr ⟨_, .comm_right f a hu⟩
    · exact Or.inr ⟨_, .comm_left f b hu⟩
  | ac f a b ia ib =>
    rcases ia with ha | ⟨u, hu⟩
    · rcases ib with hb | ⟨u, hu⟩
      · exact Or.inl (.ac f ha hb)
      · exact Or.inr ⟨_, .ac_right f a hu⟩
    · exact Or.inr ⟨_, .ac_left f b hu⟩

theorem normal_iff_rewriting (t : PTerm) : Normal t ↔ Rewriting.Normal root t := by
  constructor
  · intro hn u ⟨a, b, ha, hs, _⟩
    exact step_not_normal hs ((normal_equiv ha).mp hn)
  · intro hn
    rcases normal_or_step t with h | ⟨u, hu⟩
    · exact h
    · exact False.elim (hn u ⟨t, u, .refl _, hu, .refl _⟩)

theorem step_reduces {t u : PTerm} (h : Rewriting.Step root t u) : Reduces t u := by
  induction h with
  | root h =>
    obtain ⟨a, b, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩; exact .fst _ _
    · rcases h with ⟨rfl, rfl⟩; exact .snd _ _
  | free f args i h ih =>
    apply Reduces.free
    intro j; by_cases he : j = i
    · subst j; simpa using ih
    · simp only [he, ↓reduceIte]; exact .refl _
  | comm_left f c h ih => exact .comm f ih (.refl _)
  | comm_right f c h ih => exact .comm f (.refl _) ih
  | ac_left f c h ih => exact .ac f ih (.refl _)
  | ac_right f c h ih => exact .ac f (.refl _) ih

theorem reduces_rewriting {t u : PTerm} (h : Reduces t u) : Rewriting.Reduces root t u := by
  induction h with
  | refl t => exact .basis (.refl _)
  | trans h k ih ik => exact .trans ih ik
  | free f a b h ih => exact Rewriting.Reduces.free (sig := signature) (root := root) f a b ih
  | comm f h k ih ik => exact .comm f ih ik
  | ac f h k ih ik => exact .ac f ih ik
  | fst a b => exact .step ⟨_, _, .refl _, .root ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩, .refl _⟩
  | snd a b => exact .step ⟨_, _, .refl _, .root ⟨a, b, Or.inr ⟨rfl, rfl⟩⟩, .refl _⟩

theorem rewriting_reducesModulo {t u : PTerm} (h : Rewriting.Reduces root t u) :
    ReducesModulo t u := by
  induction h with
  | basis h => exact .basis h
  | step h =>
    obtain ⟨a, b, ha, hs, hb⟩ := h
    exact .trans (.basis ha) (.trans (.rewrite (step_reduces hs)) (.basis hb))
  | trans h k ih ik => exact .trans ih ik
  | free f a b h ih => exact .free f a b ih
  | comm f h k ih ik => exact .comm f ih ik
  | ac f h k ih ik => exact .ac f ih ik

theorem normalize_normalForm (t : PTerm) : Rewriting.NormalForm root t (normalize t) :=
  ⟨reduces_rewriting (normalize_reduces t),
    (normal_iff_rewriting _).mp (normalize_normal t), fun _ hs => normalize_sorted hs⟩

theorem normalForm_of_reduces {t u : PTerm} (h : Reduces t u) (hn : Normal u) :
    Rewriting.NormalForm root t u := by
  refine ⟨reduces_rewriting h, (normal_iff_rewriting _).mp hn, ?_⟩
  intro s hs
  have he := (reduces_normalize h).trans (normal_fixed hn)
  rw [← he]; exact normalize_sorted hs

/-- The specialization is an instance of the same verified driver that other
admitted rewrite theories can use. The current reference reducer finishes in
one call; alternate strategies may supply a decreasing rank instead. -/
def referenceNormalizer : Rewriting.Normalizer root (fun _ => True) :=
  Rewriting.rankedNormalizer root (fun t => .done (normalize t)) (fun _ => 0)
    normalize_normalForm (fun _ => True.intro)

def referenceVariant (q : List PTerm) (σ : PSubst) : Rewriting.Variant signature :=
  ⟨σ, q.map (fun t => normalize (σ.apply t))⟩

theorem variants_refine {q : List PTerm} {answers : List PSubst}
    (h : CompleteVariants q answers) :
    Rewriting.CompleteVariants root q (answers.map (referenceVariant q)) := by
  constructor
  · intro answer ha
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp ha
    refine ⟨fun v => (normal_iff_rewriting _).mp (h.1 σ hσ v), ?_⟩
    exact Rewriting.aligned_map _ q _ (fun t _ => normalize_normalForm (σ.apply t))
  · intro ρ hρ values hv
    obtain ⟨σ, hσ, δ, hn, hagree, hvalues⟩ := h.2 ρ
      (fun v => (normal_iff_rewriting _).mpr (hρ v))
    refine ⟨referenceVariant q σ, List.mem_map.mpr ⟨σ, hσ, rfl⟩,
      δ, (fun v => (normal_iff_rewriting _).mp (hn v)), ?_, ?_⟩
    · intro v hv; rw [hagree v hv]; exact .refl _
    · apply Rewriting.Aligned.map_right hv
      intro t ht u hu
      have he := normal_unique_modulo (rewriting_reducesModulo hu.1)
        (.rewrite (normalize_reduces (ρ.apply t)))
        ((normal_iff_rewriting _).mpr hu.2.1) (normalize_normal _)
      rw [hvalues t ht] at he
      exact he

private theorem reduces_occurs {a b : PTerm} (red : Reduces a b) (w : Variable) :
    b.Occurs w → a.Occurs w := by
  induction red with
  | refl => exact id
  | trans _ _ ih ik => exact fun hw => ih (ik hw)
  | free _ _ _ _ ih => rintro ⟨i, hi⟩; exact ⟨i, ih i hi⟩
  | ac _ _ _ ih ik | comm _ _ _ ih ik => exact Or.imp ih ik
  | fst => exact fun hw => ⟨0, occurs_pair.mpr (Or.inl hw)⟩
  | snd => exact fun hw => ⟨0, occurs_pair.mpr (Or.inr hw)⟩

theorem safe_refine {q : List PTerm} {avoid : List Variable} {σ : PSubst}
    (h : OutputSafe q avoid σ) : (referenceVariant q σ).Safe q avoid := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro t ht w hw
  obtain ⟨input, hi, rfl⟩ := List.mem_map.mp ht
  have occurs := reduces_occurs (normalize_reduces (σ.apply input)) w hw
  obtain ⟨v, hv, hr⟩ := σ.occurs_in_image input w occurs
  exact h.2.1 v ⟨input, hi, hv⟩ w hr

end Tamarin.Pairing
