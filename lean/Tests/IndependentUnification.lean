import Tamarin.IndependentUnification

namespace Tamarin.IndependentUnification.Tests
variable {sig : Signature}

private def reflexive (v : Variable) : Problem sig := [⟨.var v,.var v⟩]

private theorem observed (v w : Variable) : (reflexive (sig := sig) v).Occurs w ↔ w = v := by
  simp [reflexive,Problem.Occurs,Term.Occurs]

private theorem solves (v : Variable) (s : Substitution sig) : (reflexive v).Solves s := by
  intro e he
  obtain rfl := List.mem_singleton.mp he
  exact .refl _

private def v (id : Nat) : Variable := ⟨id,.msg⟩

private def arm (x : Nat) : Substitution sig := .binding (v x) (.var (v 2)) (.var (v 2))

private theorem local_complete (x : Nat) : CompleteSet (reflexive (v x)) [arm (sig := sig) x] := by
  constructor
  · exact fun s _ => solves _ s
  · intro s _
    refine ⟨_,List.mem_singleton_self _,Substitution.binding (v 2) (s.image (v x)) (s.sorted (v x)),?_⟩
    intro w hw
    obtain rfl := (observed _ _).mp hw
    simpa [arm,Substitution.compose,Substitution.binding,Substitution.apply,Term.subst] using
      EquivB.refl (s.image (v x))

private theorem disjoint : Apart (reflexive (sig := sig) (v 0)) (reflexive (v 1)) := by
  intro w h k
  have eq := ((observed _ _).1 h).symm.trans ((observed _ _).1 k)
  exact (by decide : v 0 ≠ v 1) eq

/-- Both equations are independent, and both local solvers may return the
same name for their arbitrary witness. Naively merging them loses the identity
solution, even though the resulting substitution solves both equations. -/
example : let p := reflexive (sig := sig) (v 0)
    let q := reflexive (sig := sig) (v 1)
    let bad := Rewriting.VariantJoin.choose p.Occurs (arm 0) (arm 1)
    (p ++ q).Solves bad ∧ ¬ Covers (p ++ q) [bad] := by
  classical
  dsimp only
  let p := reflexive (sig := sig) (v 0)
  let q := reflexive (sig := sig) (v 1)
  have h0 : p.Occurs (v 0) := (observed _ _).2 rfl
  have h1 : q.Occurs (v 1) := (observed _ _).2 rfl
  have out : ¬p.Occurs (v 1) := fun h => disjoint _ h h1
  have any (s : Substitution sig) : (p ++ q).Solves s := by
    intro e he
    rcases List.mem_append.mp he with l | r
    · exact solves _ s e l
    · exact solves _ s e r
  refine ⟨any _,?_⟩
  intro covers
  obtain ⟨s,hs,d,hd⟩ := covers .identity (any _)
  obtain rfl := List.mem_singleton.mp hs
  have o0 : (p ++ q).Occurs (v 0) := ⟨_,List.mem_append_left _ (List.mem_singleton_self _),Or.inl rfl⟩
  have o1 : (p ++ q).Occurs (v 1) := ⟨_,List.mem_append_right _ (List.mem_singleton_self _),Or.inr rfl⟩
  have l : EquivB (.var (v 0)) (d.image (v 2)) := by
    simpa [Rewriting.VariantJoin.choose,Substitution.compose,h0,p,arm,Substitution.binding,
      Substitution.apply,Term.subst,Substitution.identity] using hd _ o0
  have r : EquivB (.var (v 1)) (d.image (v 2)) := by
    simpa [Rewriting.VariantJoin.choose,Substitution.compose,out,p,arm,Substitution.binding,
      Substitution.apply,Term.subst,Substitution.identity] using hd _ o1
  exact (by decide : v 0 ≠ v 1) (((l.trans r.symm).occurs_iff (v 0)).mp rfl)

/-- The reference allocation recovers a complete answer under any caller
scope even with these colliding local names and reversed equation order. -/
example (avoid : List Variable) : let p := reflexive (sig := sig) (v 0)
    let q := reflexive (sig := sig) (v 1)
    (Outcome.complete (freshProduct p q avoid [arm 0] [arm 1])).CorrectIn (q ++ p) avoid :=
  freshProduct_correct List.perm_append_comm disjoint avoid (local_complete 0) (local_complete 1)

end Tamarin.IndependentUnification.Tests
