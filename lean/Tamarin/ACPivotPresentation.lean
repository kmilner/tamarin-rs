import Tamarin.ACPivotDecode

/-! Moving the selected equality to the front, orienting it, and grouping
flattened operands do not change which substitutions solve the caller's
conjunction or which variables its answers must cover. -/
namespace Tamarin.ACPivot
variable {sig : Signature}

structure Presentation (q : Query sig) (caller : Problem sig) : Prop where
  present : ∃ e : Equation sig, caller.Perm (e :: q.tail) ∧
    ((EquivB e.lhs q.lhs ∧ EquivB e.rhs q.rhs) ∨ (EquivB e.rhs q.lhs ∧ EquivB e.lhs q.rhs))

namespace Presentation
variable {q : Query sig} {caller : Problem sig}

private theorem ac_equiv_of_slots [DecidableEq sig.ACSym] (f : sig.ACSym) (input grouped : Term sig)
    (slots : List (Term sig)) (ordered : (ACRepresentation.flatten f input).Perm slots)
    (decoded : ACRepresentation.decode f slots = some grouped) : EquivB input grouped := by
  obtain ⟨t,ht,he⟩ := ACRepresentation.flatten_correct f input
  exact he.symm.trans (ACRepresentation.decode_perm f ordered t grouped ht decoded)

/-- The narrow and wide input vectors may be permuted or grouped under the
same AC symbol. The caller may select its equation at any index and in either
orientation. Multiplicities and the other equations are preserved. -/
theorem of_flatten [DecidableEq sig.ACSym] (e : Equation sig) (pending : caller.Perm (e :: q.tail))
    (vectors :
      let narrow := [.var q.x, q.a]
      let wide := .var q.y :: q.operands
      (((ACRepresentation.flatten q.f e.lhs).Perm narrow ∧ (ACRepresentation.flatten q.f e.rhs).Perm wide) ∨
       ((ACRepresentation.flatten q.f e.rhs).Perm narrow ∧ (ACRepresentation.flatten q.f e.lhs).Perm wide))) :
    Presentation q caller := by
  refine ⟨e,pending,?_⟩
  rcases vectors with ⟨l,r⟩ | ⟨r,l⟩
  · exact .inl ⟨ac_equiv_of_slots q.f _ q.lhs _ l rfl,ac_equiv_of_slots q.f _ q.rhs _ r rfl⟩
  · exact .inr ⟨ac_equiv_of_slots q.f _ q.lhs _ r rfl,ac_equiv_of_slots q.f _ q.rhs _ l rfl⟩

private theorem transports {a b l r : Term sig} (al : EquivB a l) (br : EquivB b r)
    (σ : Substitution sig) : EquivB (σ.apply a) (σ.apply b) ↔ EquivB (σ.apply l) (σ.apply r) :=
  ⟨fun h => ((al.subst σ.image).symm.trans h).trans (br.subst σ.image),
   fun h => ((al.subst σ.image).trans h).trans (br.subst σ.image).symm⟩

theorem solves_iff (present : Presentation q caller) (σ : Substitution sig) :
    caller.Solves σ ↔ q.problem.Solves σ := by
  obtain ⟨⟨l,r⟩,move,sides⟩ := present.present
  have moved : caller.Solves σ ↔ Problem.Solves (⟨l,r⟩ :: q.tail) σ :=
    ⟨fun h e he => h e (move.mem_iff.mpr he),fun h e he => h e (move.mem_iff.mp he)⟩
  rw [moved,Query.problem,Query.solves_cons,Query.solves_cons]
  apply and_congr_left
  intro _
  rcases sides with ⟨a,b⟩|⟨b,a⟩
  · exact transports a b σ
  · exact Iff.trans ⟨EquivB.symm,EquivB.symm⟩ (transports b a σ)

theorem occurs_iff (present : Presentation q caller) (v : Variable) :
    caller.Occurs v ↔ q.problem.Occurs v := by
  obtain ⟨⟨l,r⟩,move,sides⟩ := present.present
  have moved : caller.Occurs v ↔ Problem.Occurs (⟨l,r⟩ :: q.tail) v :=
    ⟨fun ⟨e,h,occ⟩ => ⟨e,move.mem_iff.mp h,occ⟩,fun ⟨e,h,occ⟩ => ⟨e,move.mem_iff.mpr h,occ⟩⟩
  rw [moved,Query.problem,Query.occurs_cons,Query.occurs_cons]
  rcases sides with ⟨a,b⟩|⟨b,a⟩
  · exact or_congr (or_congr (a.occurs_iff v) (b.occurs_iff v)) Iff.rfl
  · exact or_congr ((or_congr (a.occurs_iff v) (b.occurs_iff v)).trans or_comm) Iff.rfl

theorem complete (present : Presentation q caller) {answers : List (Substitution sig)}
    (cs : CompleteSet q.problem answers) : CompleteSet caller answers := by
  refine ⟨fun σ h => (present.solves_iff σ).mpr (cs.sound σ h),?_⟩
  intro ρ hρ
  obtain ⟨σ,hs,δ,fit⟩ := cs.covers ρ ((present.solves_iff ρ).mp hρ)
  exact ⟨σ,hs,δ,fun v h => fit v ((present.occurs_iff v).mp h)⟩

theorem correctIn (present : Presentation q caller) {avoid : List Variable} {answers : List (Substitution sig)}
    (cs : (Outcome.complete answers).CorrectIn q.problem avoid) :
    (Outcome.complete answers).CorrectIn caller avoid := by
  refine ⟨present.complete cs.mathematical,?_,?_⟩
  · intro σ hs v h
    exact cs.domain σ hs v fun hv => h ((present.occurs_iff v).mpr hv)
  · intro σ hs v hv u hu outside
    exact cs.fresh σ hs v ((present.occurs_iff v).mp hv) u hu fun h => outside ((present.occurs_iff u).mpr h)

end Presentation
end Tamarin.ACPivot
