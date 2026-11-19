import Tamarin.MatchingFree
import Tamarin.LinearACMatch
import Tamarin.ContextualReduction

namespace Tamarin.Matching.Projected
variable {sig : Signature}

/-- All instances of a rule's right side at a directional matching problem.
The subject variables are rigid, including names shared with the rule. -/
def Produces (p : Problem sig) (rhs out : Term sig) : Prop :=
  ∃ σ, Matches p σ ∧ EquivB (σ.apply rhs) out

/-- A positional split is optional at every free node. Commutative and AC
constraints can be left intact for a complete directional solver. -/
inductive Split : Term sig → Term sig → Problem sig → Prop where
  | keep (p t : Term sig) : Split p t [⟨p, t⟩]
  | free (f : sig.FreeSym) (ps ts : Fin (sig.arity f) → Term sig)
      (rows : Fin (sig.arity f) → Problem sig) (children : ∀ i, Split (ps i) (ts i) (rows i)) :
      Split (.free f ps) (.free f ts) (List.ofFn rows).flatten

theorem Split.exact {p t : Term sig} {rows} (h : Split p t rows) (σ : Substitution sig) :
    Matches rows σ ↔ EquivB (σ.apply p) t := by
  induction h with
  | keep => simp [Matches]
  | free f ps ts rows _ ih =>
    change Matches (List.ofFn rows).flatten σ ↔ EquivB (.free f _) (.free f ts)
    rw [free_equiv_iff]
    constructor
    · intro hm i
      apply (ih i).mp
      exact fun e he => hm e (List.mem_flatten.mpr ⟨rows i,List.mem_ofFn.mpr ⟨i,rfl⟩,he⟩)
    · intro hm e he
      obtain ⟨g,hg,he⟩ := List.mem_flatten.mp he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
      exact (ih i).mpr (hm i) e he

/-- Components invisible to the RHS contribute exactly one existence check.
The caller may use arbitrary matching algorithms for either side. -/
theorem factor {live erased : Problem sig} {rhs out : Term sig}
    (apart : Independent live erased) (visible : ∀ v, rhs.Occurs v → Observed live v) :
    Produces (live ++ erased) rhs out ↔ Produces live rhs out ∧ ∃ τ, Matches erased τ := by
  constructor
  · rintro ⟨σ,hm,hr⟩
    exact ⟨⟨σ,fun e he => hm e (List.mem_append_left _ he),hr⟩,
      ⟨σ,fun e he => hm e (List.mem_append_right _ he)⟩⟩
  · rintro ⟨⟨σ,hs,hr⟩,τ,ht⟩
    refine ⟨merge live σ τ,merge_matches hs ht (fun v hp hq => (apart v hp hq).elim),?_⟩
    apply EquivB.trans _ hr
    apply rhs.subst_equiv
    intro v hv
    simp [merge, visible v hv, EquivB.refl]

theorem complete_values {live : Problem sig} {rhs out : Term sig} {answers}
    (hc : Complete live (fun _ => True) answers) (visible : ∀ v, rhs.Occurs v → Observed live v) :
    Produces live rhs out ↔ ∃ σ ∈ answers, EquivB (σ.apply rhs) out := by
  constructor
  · rintro ⟨τ,hm,hr⟩
    let r := merge live τ Substitution.identity
    have same : Substitution.AgreesOn (Observed live) r τ := by
      intro v hv
      simp [r,merge,hv,EquivB.refl]
    have scope : Scoped live (fun _ => True) r := by
      intro v hv
      have absent : ¬ Observed live v := fun h => hv ⟨h,trivial⟩
      simp [r,merge,absent,Substitution.identity]
    obtain ⟨σ,hσ,agrees⟩ := hc.covers r (matches_of_agrees hm same) scope
    refine ⟨σ,hσ,EquivB.trans ?_ hr⟩
    exact rhs.subst_equiv _ _ fun v hv =>
      (agrees v (visible v hv)).symm.trans (same v (visible v hv))
  · rintro ⟨σ,hσ,hr⟩
    exact ⟨σ,(hc.sound σ hσ).1,hr⟩

/-- Exact root outcomes for one rule, including all failures. Components
may be regrouped or deduplicated and the returned values compared modulo B. -/
theorem rule_values {r : Equation sig} {subject out : Term sig} {rows live : Problem sig}
    {erased : List (Problem sig)} {answers}
    (split : Split r.lhs subject rows)
    (partition : ∀ e, e ∈ rows ↔ e ∈ live ++ erased.flatten)
    (apart : Independent live erased.flatten) (separate : erased.Pairwise Independent)
    (visible : ∀ v, r.rhs.Occurs v → Observed live v) (hc : Complete live (fun _ => True) answers) :
    (∃ σ : Substitution sig, EquivB (σ.apply r.lhs) subject ∧ EquivB (σ.apply r.rhs) out) ↔
      (∃ σ ∈ answers, EquivB (σ.apply r.rhs) out) ∧ (∀ g ∈ erased, ∃ τ, Matches g τ) := by
  have rowEq (σ : Substitution sig) : EquivB (σ.apply r.lhs) subject ↔
      Matches (live ++ erased.flatten) σ :=
    (split.exact σ).symm.trans (matches_iff_of_same_pairs partition σ)
  simp only [rowEq]
  change Produces (live ++ erased.flatten) r.rhs out ↔ _
  rw [factor apart visible, complete_values hc visible, LinearAC.independent_exists erased separate]

open Rewriting ConstructorVariants

/-- The successor graph can mix complete match families with projections.
It needs the exact output relation for each eligible rule. -/
theorem root_iff (rules : List (Equation sig)) (subject out : Term sig)
    (apps : ∀ r ∈ rules, Application r.lhs) (returns : Equation sig → Term sig → Prop)
    (exactValues : ∀ r ∈ rules, ∀ _ : head r.lhs = head subject,
      (∃ σ : Substitution sig, EquivB (σ.apply r.lhs) subject ∧ EquivB (σ.apply r.rhs) out) ↔
        returns r out) :
    ContextualReduction.AtRoot (ruleRoot rules) subject out ↔
      ∃ r ∈ rules, head r.lhs = head subject ∧ returns r out := by
  constructor
  · rintro ⟨_,_,eq,⟨r,hr,σ,rfl,rfl⟩,value⟩
    have hd := (instance_head r (apps r hr) σ).symm.trans eq.head_eq.symm
    exact ⟨r,hr,hd,(exactValues r hr hd).mp ⟨σ,eq.symm,value⟩⟩
  · rintro ⟨r,hr,hd,ret⟩
    obtain ⟨σ,eq,value⟩ := (exactValues r hr hd).mpr ret
    exact ⟨_,_,eq.symm,⟨r,hr,σ,rfl,rfl⟩,value⟩

end Tamarin.Matching.Projected
