import Tamarin.CallerFreshening
import Tamarin.ACResidual
import Tamarin.ResidualSearch
import Tamarin.VariablePermutation
import TamarinRuntime.OperandRefinement

/-! The operand solver selects indices into the caller's equation array.
IDs refer to whole operands. Symmetry of an equation never rearranges the
factors inside an AC operand. -/
namespace Tamarin.OperandRefinement

abbrev Row := UInt64 × UInt64
abbrev Kernel := Array UInt64 → Array UInt64

def wire (rows : List Row) := rows.flatMap fun (l,r) => [l,r]

private def unordered (r : Row) : Row := if r.1 ≤ r.2 then r else (r.2,r.1)

private theorem orientation {a b : Row} (h : unordered a = unordered b) :
    a = b ∨ a = (b.2,b.1) := by
  rcases a with ⟨x,y⟩
  rcases b with ⟨z,w⟩
  unfold unordered at h
  split at h <;> split at h <;> cases h <;> simp

/-- Each unordered non-reflexive equation is represented once. The solver
can keep either orientation, pick any occurrence, and reorder the result. -/
def Correct (run : Kernel) : Prop :=
  ∀ rows : List Row, rows.length ≤ UInt64.size →
    ∃ kept : List (Nat × Row),
      run (wire rows).toArray = (kept.map fun (i,_) => i.toUInt64).toArray ∧
      kept.length ≤ rows.length ∧
      (∀ i r, (i,r) ∈ kept → rows[i]? = some r ∧ r.1 ≠ r.2) ∧
      (kept.map (unordered ∘ Prod.snd)).Nodup ∧
      ∀ r ∈ rows, r.1 ≠ r.2 → ∃ i k, (i,k) ∈ kept ∧ (r = k ∨ r = (k.2,k.1))

private def chosen (start : Nat) (seen : List Row) : List Row → List (Nat × Row)
  | [] => []
  | r :: rs =>
    if r.1 = r.2 ∨ unordered r ∈ seen then chosen (start+1) seen rs
    else (start,r) :: chosen (start+1) (unordered r :: seen) rs

private theorem outputs (start : Nat) (seen : List Row) (rs : List Row) :
    OperandRefinementCandidate.select start seen (wire rs) = (chosen start seen rs).map (fun (i,_) => i.toUInt64) := by
  induction rs generalizing start seen with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨l,r⟩
    change (if l = r ∨ unordered (l,r) ∈ seen then _ else _) = _
    simp only [chosen]
    split <;> simp_all <;> exact ih ..

private theorem length_bound (start : Nat) (seen : List Row) (rs : List Row) :
    (chosen start seen rs).length ≤ rs.length := by
  induction rs generalizing start seen with
  | nil => simp [chosen]
  | cons r rs ih =>
    simp only [chosen,List.length_cons]; split
    · exact Nat.le_succ_of_le (ih ..)
    · exact Nat.succ_le_succ (ih ..)

private theorem at_index {rs : List Row} {start i : Nat} {seen : List Row} {r : Row}
    (h : (i,r) ∈ chosen start seen rs) :
    ∃ j, i = start+j ∧ rs[j]? = some r ∧ r.1 ≠ r.2 := by
  induction rs generalizing start seen with
  | nil => simp [chosen] at h
  | cons a rs ih =>
    have later {next} (mem : (i,r) ∈ chosen (start+1) next rs) :
        ∃ j, i = start+j ∧ (a::rs)[j]? = some r ∧ r.1 ≠ r.2 := by
      obtain ⟨j,eq,atj,ne⟩ := ih mem
      exact ⟨j+1,by omega,atj,ne⟩
    simp only [chosen] at h
    split at h
    · exact later h
    · rename_i test
      rcases List.mem_cons.mp h with eq|tail
      · cases eq; exact ⟨0,by simp,rfl,fun eq => test (.inl eq)⟩
      · exact later tail

private theorem classes (start : Nat) (seen : List Row) (rs : List Row) (key : Row) :
    key ∈ (chosen start seen rs).map (unordered ∘ Prod.snd) ↔
      key ∉ seen ∧ ∃ r ∈ rs, r.1 ≠ r.2 ∧ unordered r = key := by
  induction rs generalizing start seen with
  | nil => simp [chosen]
  | cons a rs ih =>
    simp only [chosen]; split
    · rename_i test
      rw [ih]
      constructor
      · rintro ⟨unused,r,mem,ne,eq⟩
        exact ⟨unused,r,.tail _ mem,ne,eq⟩
      · rintro ⟨unused,r,mem,ne,eq⟩
        rcases List.mem_cons.mp mem with rfl|h
        · exact False.elim (test.elim ne (fun h => unused (eq ▸ h)))
        · exact ⟨unused,r,h,ne,eq⟩
    · rename_i test
      have distinct := not_or.mp test
      simp only [List.map_cons, List.mem_cons, Function.comp_apply,ih]
      by_cases eq : unordered a = key
      · rw [← eq]
        exact ⟨fun _ => ⟨distinct.2,a,.inl rfl,distinct.1,rfl⟩,fun _ => .inl rfl⟩
      · constructor
        · rintro (e|⟨unused,r,h,ne,code⟩)
          · exact False.elim (eq e.symm)
          · exact ⟨fun h => unused (.inr h),r,.inr h,ne,code⟩
        · rintro ⟨unused,r,(rfl|h),ne,code⟩
          · exact False.elim (eq code)
          · exact .inr ⟨fun h => h.elim (fun e => eq e.symm) unused,r,h,ne,code⟩

private theorem unique (start : Nat) (seen : List Row) (rs : List Row) :
    ((chosen start seen rs).map (unordered ∘ Prod.snd)).Nodup := by
  induction rs generalizing start seen with
  | nil => simp [chosen]
  | cons a rs ih =>
    simp only [chosen]; split
    · exact ih ..
    · apply List.nodup_cons.mpr
      exact ⟨fun h => (classes .. |>.mp h).1 List.mem_cons_self,ih ..⟩

theorem correct : Correct OperandRefinementCandidate.keep := by
  intro rs _
  refine ⟨chosen 0 [] rs,?_,length_bound ..,?_,unique ..,?_⟩
  · simp [OperandRefinementCandidate.keep,outputs]
  · intro i r h
    obtain ⟨j,eq,atj,ne⟩ := at_index h
    simpa [eq] using And.intro atj ne
  · intro r hr ne
    have hm := (classes 0 [] rs (unordered r)).mpr ⟨by simp,r,hr,ne,rfl⟩
    obtain ⟨⟨i,k⟩,mem,eq⟩ := List.mem_map.mp hm
    exact ⟨i,k,mem,orientation eq.symm⟩


variable {sig : Signature}

/-- Interning need only identify equal operands modulo B. A table is local
to the query and can assign any IDs to its full operand terms. -/
def Encodes (p : Problem sig) (id : Term sig → UInt64) (lookup : UInt64 → Term sig) : Prop :=
  ∀ e ∈ p, EquivB e.lhs (lookup (id e.lhs)) ∧ EquivB e.rhs (lookup (id e.rhs))

def rowOf (id : Term sig → UInt64) (e : Equation sig) : Row := (id e.lhs,id e.rhs)

def reduced (p : Problem sig) (indices : Array UInt64) : Problem sig :=
  indices.toList.filterMap fun i => p[i.toNat]?

private theorem included {p : Problem sig} {out} {e : Equation sig} (h : e ∈ reduced p out) : e ∈ p := by
  obtain ⟨_,_,atRow⟩ := List.mem_filterMap.mp h
  exact List.mem_of_getElem? atRow

private def Holds (lookup : UInt64 → Term sig) (σ : Substitution sig) (r : Row) :=
  EquivB (σ.apply (lookup r.1)) (σ.apply (lookup r.2))

private theorem interprets {p : Problem sig} {id lookup} (table : Encodes p id lookup) {e : Equation sig}
    (mem : e ∈ p) (σ : Substitution sig) :
    EquivB (σ.apply e.lhs) (σ.apply e.rhs) ↔ Holds lookup σ (rowOf id e) := by
  obtain ⟨l,r⟩ := table _ mem
  have le := l.subst σ.image
  have re := r.subst σ.image
  exact ⟨fun h => le.symm.trans (h.trans re),fun h => le.trans (h.trans re.symm)⟩

/-- The same retained equations work for every sorted substitution, including
ones that split AC operands or identify previously distinct terms. -/
theorem solves_iff {run : Kernel} (hc : Correct run) (p : Problem sig) (bound : p.length ≤ UInt64.size)
    (id : Term sig → UInt64) {lookup} (table : Encodes p id lookup) (σ : Substitution sig) :
    p.Solves σ ↔ (reduced p (run (wire (p.map (rowOf id))).toArray)).Solves σ := by
  obtain ⟨kept,out,_,valid,_,covers⟩ := hc (p.map (rowOf id)) (by simpa)
  rw [out]
  constructor
  · exact fun h e mem => h e (included mem)
  intro h e mem
  apply (interprets table mem σ).mpr
  by_cases same : id e.lhs = id e.rhs
  · change EquivB (σ.apply (lookup (id e.lhs))) (σ.apply (lookup (id e.rhs)))
    rw [same]; exact .refl _
  obtain ⟨i,k,hik,orient⟩ := covers (rowOf id e) (List.mem_map_of_mem mem) same
  have got := (valid i k hik).1
  rw [List.getElem?_map] at got
  obtain ⟨d,di,typed⟩ := Option.map_eq_some_iff.mp got
  have hi : i < UInt64.size := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp di).choose bound
  have keptD : d ∈ reduced p (kept.map fun (j,_) => j.toUInt64).toArray := by
    apply List.mem_filterMap.mpr ⟨i.toUInt64,?_,?_⟩
    · simp only
      exact List.mem_map_of_mem (f := fun (j,_) => j.toUInt64) hik
    · simpa only [UInt64.toNat_ofNat_of_lt' hi] using di
  have holds := (interprets table (List.mem_of_getElem? di) σ).mp (h d keptD)
  rw [typed] at holds
  rcases orient with eq|eq
  · exact eq ▸ holds
  · rw [eq]; exact EquivB.symm holds

/-- The caller observes the original variables throughout solving and
projection. A variable occurring only in a deleted reflexive constraint may
have any image in the eventual solution. -/
def Semantic (run : Kernel) : Prop :=
  ∀ {s : Signature} (p : Problem s), p.length ≤ UInt64.size →
    ∀ (id : Term s → UInt64) (lookup : UInt64 → Term s), Encodes p id lookup →
    let out := run (wire (p.map (rowOf id))).toArray
    let q := reduced p out
    (∀ i ∈ out.toList, i.toNat < p.length) ∧ out.size ≤ p.length ∧
    (∀ observed θ ρ, Residual.Denotes observed p θ ρ ↔ Residual.Denotes observed q θ ρ) ∧
    ∀ avoid answers, (Outcome.complete answers).CorrectIn q (p.variables ++ avoid) →
      (Outcome.complete answers).CorrectIn p avoid

theorem semantic {run : Kernel} (hc : Correct run) : Semantic run := by
  intro s p bound id lookup table out q
  obtain ⟨kept,packet,length,valid,_,_⟩ := hc (p.map (rowOf id)) (by simpa)
  have eq := solves_iff hc p bound id table
  refine ⟨?_,?_,fun obs θ ρ => Residual.equivalent obs eq θ ρ,?_⟩
  · intro i hi
    change i ∈ (run _).toList at hi
    rw [packet,List.toList_toArray] at hi
    obtain ⟨⟨j,k⟩,mem,rfl⟩ := List.mem_map.mp hi
    have lt := (List.getElem?_eq_some_iff.mp (valid j k mem).1).choose
    simp only [List.length_map] at lt
    simpa only [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le lt bound)] using lt
  · change (run _).size ≤ _
    rw [packet]; simpa using length
  · intro avoid answers solved
    apply ACResidual.lift_complete p q avoid p.variables answers eq _ _ solved
    · rintro v ⟨e,mem,occ⟩; exact ⟨e,included mem,occ⟩
    · exact fun v occ _ => (Problem.mem_variables ..).mpr occ


/-- Project each reduced answer onto all original variables. An unconstrained
variable erased with a reflexive row receives an explicit identity image and
participates in the same simultaneous renaming as the rest of its arm.
The caller may remove a projected answer when a retained answer covers it
on every input variable with a single instantiation. -/
def Projected (run : Kernel) : Prop :=
  ∀ {s : Signature} (request : Request s), request.problem.length ≤ UInt64.size →
    ∀ (id : Term s → UInt64) (lookup : UInt64 → Term s), Encodes request.problem id lookup →
    let p := request.problem
    let q := reduced p (run (wire (p.map (rowOf id))).toArray)
    ∀ (answers : List (Substitution s)),
      (Outcome.complete answers).CorrectIn q (p.variables ++ request.avoid) →
      ∀ (out : Substitution s → Substitution s)
        (names : (σ : Substitution s) → CallerFreshening.Allocation (CallerFreshening.sources p σ)),
        (∀ σ ∈ answers, CallerFreshening.RepresentsMod p σ (out σ) (names σ)) →
        (∀ σ ∈ answers, CallerFreshening.Avoids request σ (names σ)) →
        ∀ returned, (∀ σ ∈ returned, σ ∈ answers.map out) →
          (∀ σ ∈ answers.map out, ∃ τ ∈ returned, Substitution.InstanceOn p.Occurs σ τ) →
          (Outcome.complete returned).CorrectIn p request.avoid

theorem projected {run : Kernel} (checked : Semantic run) : Projected run := by
  intro s request bound tag lookup table p q answers raw out names rep fresh returned retained covers
  have whole := (checked p bound tag lookup table).2.2.2 request.avoid answers raw
  have projected := (CallerFreshening.refinement_mod request answers _ out names rep fresh).preserves_correct
    (by simpa using (show CompleteSet request.problem answers from whole.mathematical))
  refine ⟨⟨fun σ h => projected.mathematical.sound σ (retained σ h), ?_⟩,
    fun σ h => projected.domain σ (retained σ h), fun σ h => projected.fresh σ (retained σ h)⟩
  intro ρ solves
  obtain ⟨σ, mem, inst⟩ := projected.mathematical.covers ρ solves
  obtain ⟨τ, kept, next⟩ := covers σ mem
  exact ⟨τ, kept, Substitution.instanceOn_trans p.Occurs inst next⟩

end Tamarin.OperandRefinement
