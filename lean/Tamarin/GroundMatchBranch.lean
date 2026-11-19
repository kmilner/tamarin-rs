import Tamarin.GroundSideUnification
import Tamarin.ResidualSearch

/-! Split a residual conjunction on a complete match against a ground subject.
A branch introduces ordinary equations for the entire ground binding table.
One continuation solves those equations together with all remaining constraints. -/
namespace Tamarin.GroundMatchBranch
variable {sig : Signature}

def bindings (keys : List Variable) (arm : Substitution sig) : Problem sig :=
  keys.map fun v => ⟨.var v, arm.image v⟩

private theorem binds_iff {p : Problem sig} {arm : Substitution sig}
    {keys : List Variable} (domain : ∀ v, v ∈ keys ↔ p.Occurs v)
    (ground : arm.GroundOn p.Occurs) (δ : Substitution sig) :
    (bindings keys arm).Solves δ ↔ Substitution.AgreesOn p.Occurs δ arm := by
  constructor
  · intro h v hv
    have eq := h _ (List.mem_map_of_mem (f := fun v => Equation.mk (.var v) (arm.image v))
      ((domain v).mpr hv))
    change EquivB (δ.image v) (δ.apply (arm.image v)) at eq
    rwa [(ground v hv).apply_eq δ] at eq
  · intro h e he
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
    change EquivB (δ.image v) (δ.apply (arm.image v))
    rw [(ground v ((domain v).mp hv)).apply_eq δ]
    exact h v ((domain v).mp hv)

private theorem append_iff (p q : Problem sig) (δ : Substitution sig) :
    (p ++ q).Solves δ ↔ p.Solves δ ∧ q.Solves δ := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left q he), fun e he => h e (List.mem_append_right p he)⟩
  · rintro ⟨hp,hq⟩ e he
    exact (List.mem_append.mp he).elim (hp e) (hq e)

/-- Includes an empty matcher result, branches with zero bindings, shared variables
between selected and pending equations, and arbitrary nonground continuations. -/
theorem solves_iff {p : Problem sig} {arms : List (Substitution sig)}
    (hc : Matching.Complete p (fun _ => True) arms)
    (subjects : ∀ e ∈ p, e.rhs.Ground)
    (keys : Substitution sig → List Variable)
    (domain : ∀ arm ∈ arms, ∀ v, v ∈ keys arm ↔ p.Occurs v)
    (pending : Problem sig) (δ : Substitution sig) :
    (p ++ pending).Solves δ ↔ ∃ arm ∈ arms, (bindings (keys arm) arm ++ pending).Solves δ := by
  have h := hc.groundSide subjects
  have hg (arm) (ha : arm ∈ arms) := (hc.sound arm ha).1.groundOn subjects
  constructor
  · intro all
    obtain ⟨chosen, rest⟩ := (append_iff ..).mp all
    obtain ⟨arm,ha,τ,factors⟩ := h.covers δ chosen
    refine ⟨arm, ha, (append_iff ..).mpr ⟨(binds_iff (domain arm ha) (hg arm ha) δ).mpr ?_, rest⟩⟩
    intro v hv
    have eq := factors v hv
    change EquivB (δ.image v) (τ.apply (arm.image v)) at eq
    rwa [((hg arm ha) v hv).apply_eq τ] at eq
  · rintro ⟨arm,ha,hbranch⟩
    obtain ⟨bound, rest⟩ := (append_iff ..).mp hbranch
    have agrees := (binds_iff (domain arm ha) (hg arm ha) δ).mp bound
    apply (append_iff ..).mpr
    refine ⟨p.solves_instance (h.sound arm ha) ⟨.identity, ?_⟩, rest⟩
    intro v hv
    simpa [Substitution.compose, Substitution.apply_identity] using agrees v hv

theorem denotes_iff {p : Problem sig} {arms : List (Substitution sig)}
    (hc : Matching.Complete p (fun _ => True) arms)
    (subjects : ∀ e ∈ p, e.rhs.Ground) (keys : Substitution sig → List Variable)
    (domain : ∀ arm ∈ arms, ∀ v, v ∈ keys arm ↔ p.Occurs v)
    (observed : Variable → Prop) (pending : Problem sig) (θ ρ : Substitution sig) :
    Residual.Denotes observed (p ++ pending) θ ρ ↔
      ∃ arm ∈ arms, Residual.Denotes observed (bindings (keys arm) arm ++ pending) θ ρ := by
  constructor
  · rintro ⟨δ, hs, agree⟩
    obtain ⟨arm,ha,hr⟩ := (solves_iff hc subjects keys domain pending δ).mp hs
    exact ⟨arm,ha,δ,hr,agree⟩
  · rintro ⟨arm,ha,δ,hs,agree⟩
    exact ⟨δ,(solves_iff hc subjects keys domain pending δ).mpr ⟨arm,ha,hs⟩,agree⟩

/-- The selected equation can occur anywhere and the ground subject can be on either side. -/
theorem at_equation {original pending : Problem sig} (e : Equation sig) (flip : Bool)
    (split : original.Perm (e :: pending)) {arms : List (Substitution sig)}
    (hc : Matching.Complete [Matching.orient (fun _ => flip) e] (fun _ => True) arms)
    (ground : (Matching.orient (fun _ => flip) e).rhs.Ground)
    (keys : Substitution sig → List Variable)
    (domain : ∀ arm ∈ arms, ∀ v, v ∈ keys arm ↔ Problem.Occurs [Matching.orient (fun _ => flip) e] v)
    (observed : Variable → Prop) (θ ρ : Substitution sig) :
    Residual.Denotes observed original θ ρ ↔
      ∃ arm ∈ arms, Residual.Denotes observed (bindings (keys arm) arm ++ pending) θ ρ := by
  rw [Residual.perm observed split]
  refine Iff.trans ?_ (denotes_iff hc (by simpa using ground) keys domain observed pending θ ρ)
  apply Residual.equivalent
  intro δ
  cases flip
  · rfl
  · simp only [Matching.orient, ite_true, List.singleton_append, Problem.Solves,
      List.forall_mem_cons]
    exact and_congr ⟨EquivB.symm, EquivB.symm⟩ Iff.rfl

end Tamarin.GroundMatchBranch
