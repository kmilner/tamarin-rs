import Tamarin.Residual

/-! An ordinary residual substitution is shared by the entire worklist.
The denotation also observes bindings for variables erased from the remainder,
including variables in other operand images. -/
namespace Tamarin.Residual
variable {sig : Signature} (observed : Variable → Prop)

/-- A continuation δ must solve every remaining equation and instantiate
the accumulated images of all observed variables with the same substitution.
Fresh internal variables can remain outside the observation set. -/
def Denotes (p : Problem sig) (θ ρ : Substitution sig) : Prop :=
  ∃ δ, p.Solves δ ∧ ∀ v, observed v → EquivB (ρ.image v) (δ.apply (θ.image v))

theorem start (p : Problem sig) (live : ∀ v, p.Occurs v → observed v) (ρ : Substitution sig) :
    Denotes observed p .identity ρ ↔ p.Solves ρ := by
  constructor
  · rintro ⟨δ, hd, agree⟩
    intro e he
    exact (e.lhs.subst_equiv _ _ (fun v hv => agree v (live v ⟨e, he, .inl hv⟩))).trans
      ((hd _ he).trans (e.rhs.subst_equiv _ _ (fun v hv => agree v (live v ⟨e, he, .inr hv⟩))).symm)
  · intro h
    exact ⟨ρ, h, fun _ _ => .refl _⟩

theorem leaf (θ ρ : Substitution sig) :
    Denotes observed [] θ ρ ↔ Substitution.InstanceOn observed ρ θ := by
  constructor
  · rintro ⟨δ, _, h⟩; exact ⟨δ, h⟩
  · rintro ⟨δ, h⟩; exact ⟨δ, by simp [Problem.Solves], h⟩

theorem equivalent {p q : Problem sig} (h : ∀ δ, p.Solves δ ↔ q.Solves δ)
    (θ ρ : Substitution sig) : Denotes observed p θ ρ ↔ Denotes observed q θ ρ := by
  simp only [Denotes, h]

/-- Reordering pending equations includes suspending an open AC equation
until a sibling produces a binding or proves a clash. -/
theorem perm {p q : Problem sig} (h : p.Perm q) (θ ρ : Substitution sig) :
    Denotes observed p θ ρ ↔ Denotes observed q θ ρ :=
  equivalent observed (fun _ => by simp only [Problem.Solves, h.mem_iff]) θ ρ

theorem discard {a b : Term sig} (h : EquivB a b) (p : Problem sig) (θ ρ : Substitution sig) :
    Denotes observed (⟨a,b⟩ :: p) θ ρ ↔ Denotes observed p θ ρ :=
  equivalent observed (fun δ => by simp [Problem.Solves, Substitution.apply, h.subst δ.image]) θ ρ

theorem clash {a b : Term sig} (bad : ∀ δ : Substitution sig, ¬ EquivB (δ.apply a) (δ.apply b))
    (p : Problem sig) (θ ρ : Substitution sig) : ¬ Denotes observed (⟨a,b⟩ :: p) θ ρ :=
  fun ⟨δ, h, _⟩ => bad δ (h _ (List.mem_cons_self ..))

theorem positional (f : sig.FreeSym) (xs ys : Fin (sig.arity f) → Term sig)
    (p : Problem sig) (θ ρ : Substitution sig) :
    Denotes observed (⟨.free f xs, .free f ys⟩ :: p) θ ρ ↔
      Denotes observed (Matching.children f xs ys ++ p) θ ρ :=
  equivalent observed (fun δ => by
    simp [Problem.Solves, Matching.children, Substitution.apply, Term.subst,
      Matching.free_equiv_iff, or_imp, forall_and]) θ ρ

theorem orient {run} (hc : Commutative.Correct run) (q : Commutative.Query sig)
    (key : Head sig → UInt64) (p : UInt8) (hp : Commutative.Priority q p)
    (θ ρ : Substitution sig) :
    let k := Commutative.headCode key
    Denotes observed q.problem θ ρ ↔ ∃ b ∈ Commutative.orientations (run (k q.a) (k q.b) (k q.c) (k q.d) p),
      Denotes observed (q.branch b) θ ρ := by
  constructor
  · rintro ⟨δ, hd, agree⟩
    obtain ⟨b, hb, h⟩ := (Commutative.run_solves hc q key p hp δ).mp hd
    exact ⟨b, hb, δ, h, agree⟩
  · rintro ⟨b, hb, δ, hd, agree⟩
    exact ⟨δ, (Commutative.run_solves hc q key p hp δ).mpr ⟨b, hb, hd⟩, agree⟩

/-- Both empty sides discharge an equation. Exactly one empty side closes
a branch in the non-unital AC theory. -/
def withFactors (f : sig.ACSym) (lhs rhs : List (Term sig)) (p : Problem sig) :
    Option (Problem sig) :=
  match ACRepresentation.decode f lhs, ACRepresentation.decode f rhs with
  | none, none => some p
  | some a, some b => some (⟨a,b⟩ :: p)
  | _, _ => none

private theorem factors_denote (f : sig.ACSym) (lhs rhs : List (Term sig)) (p : Problem sig)
    (θ ρ : Substitution sig) :
    (∃ q ∈ withFactors f lhs rhs p, Denotes observed q θ ρ) ↔
      ∃ δ, ACResidual.Holds f δ lhs rhs ∧ p.Solves δ ∧
        ∀ v, observed v → EquivB (ρ.image v) (δ.apply (θ.image v)) := by
  cases hl : ACRepresentation.decode f lhs <;> cases hr : ACRepresentation.decode f rhs <;>
    simp [withFactors, ACResidual.Holds, hl, hr, Denotes, Problem.Solves, and_assoc]

theorem cancel {run} (hc : CommonCancellation.Correct run) (decode : UInt64 → Term sig)
    (f : sig.ACSym) (lhs rhs : Array UInt64) (p : Problem sig) (θ ρ : Substitution sig) :
    ∃ left right : List UInt64, run lhs rhs = #[left.toArray, right.toArray] ∧
      ((∃ q ∈ withFactors f (lhs.toList.map decode) (rhs.toList.map decode) p, Denotes observed q θ ρ) ↔
        ∃ q ∈ withFactors f (left.map decode) (right.map decode) p, Denotes observed q θ ρ) := by
  obtain ⟨l, r, packet, eq⟩ := ACResidual.run_correct hc decode f lhs rhs
  exact ⟨l, r, packet, by simp only [factors_denote, eq]⟩

theorem bind (v : Variable) (t : Term sig) (ht : HasSort t v.sort) (ho : ¬ t.Occurs v)
    (p : Problem sig) (θ ρ : Substitution sig) :
    let β := Substitution.binding v t ht
    Denotes observed (⟨.var v,t⟩ :: p) θ ρ ↔ Denotes observed (p.substitute β) (β.compose θ) ρ := by
  let β := Substitution.binding v t ht
  constructor
  · rintro ⟨δ, hd, agree⟩
    refine ⟨δ, VariableElimination.eliminate_complete v t ht p δ hd, fun w hw => ?_⟩
    have factor := Substitution.binding_factor v t ht δ (hd _ (List.mem_cons_self ..))
    have lifted := (θ.image w).subst_equiv δ.image (δ.compose β).image (fun u _ => factor u)
    exact (agree w hw).trans ((Substitution.apply_compose δ β (θ.image w)) ▸ lifted)
  · rintro ⟨δ, hd, agree⟩
    refine ⟨δ.compose β, VariableElimination.eliminate_sound v t ht ho p δ hd, fun w hw => ?_⟩
    rw [Substitution.apply_compose]
    exact agree w hw

theorem swap (a b : Term sig) (p : Problem sig) (θ ρ : Substitution sig) :
    Denotes observed (⟨a,b⟩ :: p) θ ρ ↔ Denotes observed (⟨b,a⟩ :: p) θ ρ :=
  equivalent observed (fun δ => by
    simp only [Problem.Solves, List.forall_mem_cons]
    exact and_congr ⟨EquivB.symm, EquivB.symm⟩ Iff.rfl) θ ρ

/-- A completed finite search, independent of traversal order. Each transition
must preserve the union of its children and finish every live child. An empty
child list requires the local state to be impossible under every substitution. -/
inductive Finished (observed : Variable → Prop) : Problem sig → Substitution sig → List (Substitution sig) → Prop where
  | done (θ : Substitution sig) : Finished observed [] θ [θ]
  | step {p : Problem sig} {θ : Substitution sig}
      (children : List (Problem sig × Substitution sig × List (Substitution sig)))
      (transition : ∀ ρ, Denotes observed p θ ρ ↔ ∃ c ∈ children, Denotes observed c.1 c.2.1 ρ)
      (closed : ∀ c ∈ children, Finished observed c.1 c.2.1 c.2.2) :
      Finished observed p θ (children.flatMap fun c => c.2.2)

theorem Finished.exactLeaves {p : Problem sig} {θ answers} (h : Finished observed p θ answers)
    (ρ : Substitution sig) : Denotes observed p θ ρ ↔ ∃ σ ∈ answers, Denotes observed [] σ ρ := by
  induction h with
  | done => simp
  | step children transition _ ih =>
    rw [transition]
    constructor
    · rintro ⟨c, hc, hp⟩
      obtain ⟨σ, hs, hd⟩ := (ih c hc).mp hp
      exact ⟨σ, List.mem_flatMap.mpr ⟨c, hc, hs⟩, hd⟩
    · rintro ⟨σ, hs, hd⟩
      obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp hs
      exact ⟨c, hc, (ih c hc).mpr ⟨σ, hm, hd⟩⟩

theorem complete (p : Problem sig) (answers : List (Substitution sig))
    (finished : Finished p.Occurs p .identity answers) : CompleteSet p answers := by
  constructor
  · intro σ hs
    exact (start p.Occurs p (fun _ h => h) σ).mp ((finished.exactLeaves _ σ).mpr ⟨σ, hs, (leaf p.Occurs σ σ).mpr (Substitution.instanceOn_refl _ _)⟩)
  · intro ρ hr
    obtain ⟨σ, hs, hl⟩ := (finished.exactLeaves _ ρ).mp ((start p.Occurs p (fun _ h => h) ρ).mpr hr)
    obtain ⟨δ, h⟩ := (leaf p.Occurs σ ρ).mp hl
    exact ⟨σ, hs, δ, h⟩

end Tamarin.Residual
