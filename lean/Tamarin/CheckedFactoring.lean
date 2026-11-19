import Tamarin.FactorInterpretation
import Tamarin.FactoredUnification
import Tamarin.WholeContract

/-! Refine an accepted shared-graph factoring certificate to sorted Tamarin
substitutions. The representation conditions describe concrete terms and
images, independently of which assignments solve the equations. -/
namespace Tamarin.CheckedFactoring
open Cancellation Whole WholeProblem FactorCheck FactorInterpretation
variable {sig : Signature}

structure Rows (c : Codec sig) (p : Problem sig) (rows : Equations) : Prop where
  layout : RowLayout (encodeRows c p) rows
  faithful : Faithful c p

/-- On each variable observed by the original query the factor table returns
the caller's substitution image, up to flattening the same AC symbol. -/
structure Bindings (c : Codec sig) (p : Problem sig) (θ : Substitution sig)
    (bs : Equations) : Prop where
  live : ∀ v, p.Occurs v → Live c (θ.image v)
  images : ∀ v, p.Occurs v → Layout (encode c (θ.image v)) (lookup bs (encode c (.var v)))

private theorem layout_solves (c : Codec sig) (ρ : Substitution sig)
    (m : Interpretation (Value sig)) (apps : m.app = (model c ρ).app)
    {xs ys : Equations} (h : RowLayout xs ys) : m.Solves xs ↔ m.Solves ys := by
  induction h with
  | nil => rfl
  | cons l r _ ih =>
    simp only [Interpretation.Solves, List.forall_mem_cons] at ih ⊢
    rw [eval_layout_with c ρ m apps l, eval_layout_with c ρ m apps r, ih]

private theorem rows_solves_with (c : Codec sig) {p : Problem sig} {xs : Equations}
    (h : Rows c p xs) (ρ : Substitution sig) (m : Interpretation (Value sig))
    (apps : m.app = (model c ρ).app) (atoms : m.leaf 1 = (model c ρ).leaf 1)
    (variables : ∀ v, p.Occurs v → m.eval (encode c (.var v)) = .semantic (classOf (ρ.image v))) :
    m.Solves xs ↔ p.Solves ρ := by
  rw [← layout_solves c ρ m apps h.layout]
  have sides (e) (he : e ∈ p) :=
    And.intro (eval_encode_with c ρ m apps atoms e.lhs (h.faithful e he).1
      (fun v hv => variables v ⟨e,he,Or.inl hv⟩))
      (eval_encode_with c ρ m apps atoms e.rhs (h.faithful e he).2
      (fun v hv => variables v ⟨e,he,Or.inr hv⟩))
  constructor
  · intro sol e he
    have eq := sol _ (List.mem_map_of_mem (f := fun e : Equation sig => (encode c e.lhs, encode c e.rhs)) he)
    exact Quotient.exact (Value.semantic.inj (((sides e he).1).symm.trans (eq.trans (sides e he).2)))
  · intro sol u hu
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hu
    exact ((sides e he).1).trans ((congrArg Value.semantic (Quotient.sound (sol e he))).trans (sides e he).2.symm)

private theorem live_original_var (c : Codec sig) {p : Problem sig} (hp : Faithful c p)
    {v : Variable} (hv : p.Occurs v) : Live c (.var v) := by
  have sub {t : Term sig} (ht : Live c t) (hv : t.Occurs v) : Live c (.var v) := by
    induction t with
    | var w => obtain rfl := hv; exact ht
    | atom => exact False.elim hv
    | free f a ih => obtain ⟨i,hi⟩ := hv; exact ih i (ht.2 i) hi
    | comm f a b ia ib | ac f a b ia ib =>
      rcases hv with h | h
      · exact ia ht.2.1 h
      · exact ib ht.2.2 h
  obtain ⟨e,he,l | r⟩ := hv
  · exact sub (hp e he).1 l
  · exact sub (hp e he).2 r

private theorem leaf_layout {a b : Tree} (h : Layout a b) (k i s : UInt64)
    (ha : a = .leaf k i s) : b = .leaf k i s := by
  induction h with
  | refl => exact ha
  | trans _ _ ih ij => exact ij (ih ha)
  | child | flatten => contradiction

/-- A sparse substitution as variable/image equations. The domain can be an
overapproximation (explicit identity images are harmless). -/
def bindingProblem (θ : Substitution sig) (keys : List Variable) : Problem sig :=
  keys.map fun v => ⟨.var v, θ.image v⟩

private theorem lookup_layout (c : Codec sig) (θ : Substitution sig) (keys : List Variable)
    {bs : Equations} (rows : Rows c (bindingProblem θ keys) bs) (v : Variable)
    (live : Live c (.var v)) :
    (v ∈ keys → Layout (encode c (θ.image v)) (lookup bs (encode c (.var v)))) ∧
    (v ∉ keys → lookup bs (encode c (.var v)) = encode c (.var v)) := by
  induction keys generalizing bs with
  | nil =>
    obtain ⟨layout,_⟩ := rows
    cases layout
    exact ⟨by simp, by intros; rfl⟩
  | cons w ws ih =>
    obtain ⟨layout, faithful⟩ := rows
    cases layout with
    | cons lhs rhs rest =>
      have hl := leaf_layout lhs 0 (c.vars.put w) (sortWord w.sort) rfl
      subst_vars
      have smaller : Rows c (bindingProblem θ ws) _ :=
        ⟨rest, fun e he => faithful e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hit,miss⟩ := ih smaller
      have hw := (faithful _ List.mem_cons_self).1
      by_cases eq : w = v
      · subst w
        refine ⟨fun _ => ?_, by simp⟩
        simpa [lookup, encode] using rhs
      · have sep : c.vars.put w ≠ c.vars.put v := by
          intro ids
          have hw : c.vars.get (c.vars.put w) = some w := hw
          have hv : c.vars.get (c.vars.put v) = some v := live
          exact eq (Option.some.inj (hw.symm.trans ((congrArg c.vars.get ids).trans hv)))
        simp [lookup, encode, sep, Ne.symm eq] at hit miss ⊢
        exact ⟨hit, miss⟩

/-- Ordinary root-by-root encoding of the finite binding table suffices.
The only requirement away from the transmitted keys is the usual identity
default for a finite substitution. -/
theorem Bindings.of_rows {c : Codec sig} {p : Problem sig} {θ : Substitution sig} {bs : Equations}
    (fp : Faithful c p) (keys : List Variable) (rows : Rows c (bindingProblem θ keys) bs)
    (outside : ∀ v, v ∉ keys → θ.image v = .var v) : Bindings c p θ bs where
  live v hv := by
    by_cases h : v ∈ keys
    · exact (rows.faithful _ (List.mem_map_of_mem (f := fun u => (⟨.var u, θ.image u⟩ : Equation sig)) h)).2
    · rw [outside v h]
      exact live_original_var c fp hv
  images v hv := by
    obtain ⟨hit,miss⟩ := lookup_layout c θ keys rows v (live_original_var c fp hv)
    by_cases h : v ∈ keys
    · exact hit h
    · rw [outside v h, miss h]
      exact .refl _

theorem Rows.solves {c : Codec sig} {p : Problem sig} {xs : Equations}
    (h : Rows c p xs) (ρ : Substitution sig) : (model c ρ).Solves xs ↔ p.Solves ρ :=
  rows_solves_with c h ρ _ rfl rfl (fun _ hv => eval_encode c ρ _ (live_original_var c h.faithful hv))

private theorem bound_image {c : Codec sig} {p : Problem sig} {θ : Substitution sig}
    {bs : Equations} (h : Bindings c p θ bs) (ρ : Substitution sig) {v : Variable} (hv : p.Occurs v) :
    ((model c ρ).bind bs).eval (encode c (.var v)) = .semantic (classOf ((ρ.compose θ).image v)) := by
  change (model c ρ).eval (lookup bs (encode c (.var v))) = _
  exact (eval_layout c ρ (h.images v hv)).symm.trans (eval_encode c ρ _ (h.live v hv))

theorem factoring (c : Codec sig) {ds original bindings residual} {p q : Problem sig}
    {θ : Substitution sig} (valid : Valid ds original bindings residual)
    (hp : Rows c p original) (hb : Bindings c p θ bindings) (hq : Rows c q residual) :
    FactoredUnification.Factoring p q θ where
  forward σ sol := (rows_solves_with c hp (σ.compose θ) ((model c σ).bind bindings) rfl rfl
    (fun _ hv => bound_image hb σ hv)).mp (valid.lift _ ((hq.solves σ).mpr sol))
  residual ρ sol := (hq.solves ρ).mp (((valid.equivalent _).mp ((hp.solves ρ).mpr sol)).2)
  stable ρ sol v hv := by
    have bindingsSolved := ((valid.equivalent _).mp ((hp.solves ρ).mpr sol)).1
    have image := bound_image hb ρ hv
    rw [Interpretation.bind_eq _ bindingsSolved] at image
    exact Quotient.exact (Value.semantic.inj ((eval_encode c ρ _ (live_original_var c hp.faithful hv)).symm.trans image))

end Tamarin.CheckedFactoring
