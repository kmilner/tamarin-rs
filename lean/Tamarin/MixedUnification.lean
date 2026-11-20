import Tamarin.MixedComponentEncoding

namespace Tamarin.MixedUnification
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

open ComponentEncoding (SlotPair)

private def pairs : List (Term s) → List (SlotPair s)
  | [] => []
  | x :: xs => xs.map (fun y => (x,y)) ++ pairs xs

/-- Reopen the original equations when a terminal branch forces two previously
distinct source slots to agree. Each recursive call removes a pair from a
finite source inventory. Internal Hilbert-basis witnesses never enter it. -/
private def drive (p : Problem s) (todo : List (SlotPair s)) : RigidBranches.Certified p := by
  apply RigidBranches.refineWith p
  intro child
  match ComponentEncoding.branch child todo with
  | none => exact ⟨none,by simp⟩
  | some stage =>
    let visit (z : {i // i ∈ stage.reopen}) :=
      have lt : (todo.filter (· != z.val)).length < todo.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨z.val,stage.subset z.property,by simp⟩
      drive (⟨z.val.1,z.val.2⟩ :: child) (todo.filter (· != z.val))
    match RigidBranches.collect (fun z => (visit z).val) stage.reopen.attach with
    | none => exact ⟨none,by simp⟩
    | some joined =>
      refine ⟨some (stage.rows ++ joined.val),?_⟩
      rintro _ ⟨⟩
      constructor
      · intro θ hm e he
        rcases List.mem_append.mp hm with left | right
        · exact stage.sound θ left e he
        · obtain ⟨z,_,ans,hs,mem⟩ := joined.property.2 θ right
          exact ((visit z).property ans hs).sound θ mem e (List.mem_cons_of_mem _ he)
      · intro ρ sol
        rcases stage.covers ρ sol with ⟨θ,hθ,μ,agree⟩ | ⟨z,hz,eq⟩
        · exact ⟨θ,List.mem_append_left _ hθ,μ,agree⟩
        · let i := (⟨z,hz⟩ : {t // t ∈ stage.reopen})
          obtain ⟨ans,hs,sub⟩ := joined.property.1 i (List.mem_attach ..)
          have extended : Problem.Solves (⟨z.1,z.2⟩ :: child) ρ := by
            exact List.forall_mem_cons.mpr ⟨eq,sol⟩
          obtain ⟨θ,hθ,μ,agree⟩ := ((visit i).property ans hs).covers ρ extended
          refine ⟨θ,List.mem_append_right _ (sub hθ),μ,?_⟩
          rintro v ⟨e,he,hv⟩
          exact agree v ⟨e,List.mem_cons_of_mem _ he,hv⟩
termination_by todo.length
decreasing_by exact lt

def solve? (p : Problem s) : Option (List (UnifierSorts.Template s)) :=
  match reconstruct? p with
  | some rows => some rows
  | none => (drive p (pairs (inventory p))).val

theorem solve_correct {p : Problem s} {rows} (hr : solve? p = some rows) :
    UnifierSorts.CompleteTemplates p rows := by
  unfold solve? at hr
  split at hr
  next h => cases hr; exact reconstruct_correct h
  next => exact (drive p _).property _ hr

theorem completes_singleDefinition (p : Problem s) (h : SingleDefinition (purify p).constraints) :
    (solve? p).isSome := by
  obtain ⟨rows,hr⟩ := Option.isSome_iff_exists.mp (reconstructs_singleDefinition p h)
  simp [solve?,hr]

/-- Rigid branching followed by AC combination must return a family whenever
each resulting component frontier closes by constructor agreement or clash. -/
theorem completes_constructorFrontiers (p : Problem s)
    (closed : ∀ c ∈ (RigidBranches.refineProblem p).val, ComponentEncoding.ConstructorFrontier c) :
    (solve? p).isSome := by
  unfold solve?
  split
  next => rfl
  next =>
    rw [drive]
    apply RigidBranches.refineWith_completes
    intro child hc
    obtain ⟨stage,hr,empty⟩ := ComponentEncoding.branch_closed child (pairs (inventory p)) (closed child hc)
    split
    next h => rw [hr] at h; contradiction
    next st eq =>
      rw [hr] at eq; cases eq
      dsimp only
      split
      next h =>
        exfalso
        apply Option.isSome_iff_ne_none.mp _ h
        apply RigidBranches.collect_completes
        simp [empty]
      next => rfl

/-- Refine a complete raw answer with all admissible sorts and fresh caller names. -/
def unify? (p : Problem s) (avoid : List Variable) : Option (List (Substitution s)) :=
  (solve? p).map (fun rows => UnifierSorts.solve p rows avoid)

theorem unify_correct {p : Problem s} {avoid answers} (h : unify? p avoid = some answers) :
    (Outcome.complete answers).CorrectIn p avoid := by
  obtain ⟨rows,hr,rfl⟩ := Option.map_eq_some_iff.mp h
  exact UnifierSorts.correct p rows (solve_correct hr) avoid

end Tamarin.MixedUnification
