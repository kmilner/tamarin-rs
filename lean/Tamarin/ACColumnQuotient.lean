import TamarinRuntime.ACColumnQuotient
import Tamarin.ACRationalCone
import Tamarin.ACDirectFeasibility

namespace Tamarin.ACFeasibility.ColumnQuotient
open ACBasis
variable {n k : Nat}

/-- Every input signature occurs among the representatives, including signatures
whose hashes collide. Equality of the complete profile controls membership. -/
private theorem collected (key : Fin n → Profile) (xs : List (Fin n))
    (seen : Std.HashSet Profile) (stored : List (Fin n))
    (inv : ∀ i, key i ∈ seen ↔ ∃ s ∈ stored, key s = key i) (i : Fin n)
    (present : i ∈ xs ∨ key i ∈ seen) : ∃ s ∈ collect key xs seen stored, key s = key i := by
  induction xs generalizing seen stored with
  | nil =>
    simp only [List.not_mem_nil,false_or] at present
    simpa only [collect,List.mem_reverse] using (inv i).mp present
  | cons x xs ih =>
    by_cases inSet : seen.contains (key x) = true <;> simp only [collect,inSet,ite_true]
    · apply ih seen stored inv
      have prior := Std.HashSet.contains_iff_mem.mp inSet
      rcases present with inp | old
      · rcases List.mem_cons.mp inp with rfl | m
        · exact .inr prior
        · exact .inl m
      · exact .inr old
    · apply ih
      · intro j
        simp only [Std.HashSet.mem_insert,beq_iff_eq,inv,List.mem_cons]
        grind
      · simp only [Std.HashSet.mem_insert,beq_iff_eq]
        rcases present with inp | old
        · rcases List.mem_cons.mp inp with rfl | m
          · exact .inr (.inl rfl)
          · exact .inl m
        · exact .inr (.inr old)

theorem covers (rs : List (Row n)) (i : Fin n) :
    ∃ j : Fin (representatives rs).length, profile rs ((representatives rs).get j) = profile rs i := by
  obtain ⟨s,mem,eq⟩ := collected (profile rs) (List.finRange n) ∅ [] (by simp)
    i (.inl (List.mem_finRange i))
  obtain ⟨j,rfl⟩ := List.get_of_mem mem
  exact ⟨j,eq⟩

private theorem coeff {rs : List (Row n)} {i j : Fin n} (eq : profile rs i = profile rs j)
    {r : Row n} (m : r ∈ rs) : r.pos i = r.pos j ∧ r.neg i = r.neg j := by
  induction rs with
  | nil => contradiction
  | cons s rs ih =>
    simp only [profile,List.map_cons,List.cons.injEq,Prod.mk.injEq] at eq
    rcases List.mem_cons.mp m with rfl | member
    · exact eq.1
    · exact ih eq.2 member

/-- Fixed representatives for a coverage obligation, specified solely by
column equality in left-to-right input order. -/
def reference {n} (rs : List (Row n)) : List (Fin n) :=
  (List.finRange n).eraseDupsBy (fun i j => profile rs i == profile rs j)

theorem representatives_eq (rs : List (Row n)) : representatives rs = reference rs := by
  let key := profile rs
  have loop (xs : List (Fin n)) (seen : Std.HashSet Profile) (stored : List (Fin n))
      (inv : ∀ i, key i ∈ seen ↔ ∃ s ∈ stored, key s = key i) :
      collect key xs seen stored = List.eraseDupsBy.loop (fun i j => key i == key j) xs stored := by
    induction xs generalizing seen stored with
    | nil => rfl
    | cons x xs ih =>
      have agree : seen.contains (key x) = stored.any (fun j => key x == key j) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Std.HashSet.contains_iff_mem,inv,List.any_eq_true,beq_iff_eq]
        exact exists_congr (fun s => and_congr_right (fun _ => eq_comm))
      cases e : seen.contains (key x) with
      | true => simp only [collect,List.eraseDupsBy.loop,←agree,e,ite_true]; exact ih _ _ inv
      | false =>
        simp only [collect,List.eraseDupsBy.loop,←agree,e,Bool.false_eq_true,ite_false]
        apply ih
        intro j
        simp only [Std.HashSet.mem_insert,beq_iff_eq,inv,List.mem_cons]
        grind
  exact loop _ ∅ [] (by simp)

/-- Move every source coordinate to a target coordinate having its
coefficient profile. Contributions with the same destination add. -/
private theorem push_solution (src : List (Row n)) (dst : List (Row k)) (f : Fin n → Fin k)
    (preserves : ∀ r ∈ dst, ∃ s ∈ src, ∀ i, r.pos (f i) = s.pos i ∧ r.neg (f i) = s.neg i)
    (x : Vec n) (hx : SystemHolds src x) :
    SystemHolds dst (mix (fun i => spike (f i) 1) x) := by
  intro r member
  obtain ⟨s,m,eq⟩ := preserves r member
  apply (Row.pullback_iff ..).mp
  rw [Row.pullback,Row.ofWeights_holds]
  simp only [dot_spike,Nat.mul_one]
  rw [show (fun i => r.pos (f i)) = s.pos from funext (fun i => (eq i).1),
      show (fun i => r.neg (f i)) = s.neg from funext (fun i => (eq i).2)]
  exact hx s m

private theorem hit {a b} (f : Fin a → Fin b) (j : Fin b) {x : Vec a}
    (live : ∀ i, 0 < x i) (i : Fin a) (tgt : f i = j) :
    0 < mix (fun t => spike (f t) 1) x j := by
  exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,by simpa [spike,tgt] using live i⟩

private theorem joint {k} (rs : List (Row k)) (touch : ∀ j : Fin k, ∃ x, SystemHolds rs x ∧ 0 < x j) :
    Feasible rs := by
  classical
  let g (j : Fin k) := (touch j).choose
  have sol j : SystemHolds rs (g j) ∧ 0 < g j j := (touch j).choose_spec
  refine ⟨mix g (fun _ => 1),fun r hr => Cone.mix_holds r g (fun j => (sol j).1 r hr) _,fun j => ?_⟩
  exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,by simpa using (sol j).2⟩

/-- Existence of a positive solution depends only on the set of column
profiles. For each target coordinate separately take a representative
map hitting it. Adding the resulting solutions yields simultaneous positivity. -/
theorem restrict_iff (rs : List (Row n)) (rep : Fin k → Fin n)
    (covered : ∀ i, ∃ j, profile rs (rep j) = profile rs i) :
    Feasible (rs.map (restrict rep)) ↔ Feasible rs := by
  classical
  let cls (i : Fin n) := (covered i).choose
  have matchCol i : profile rs (rep (cls i)) = profile rs i := (covered i).choose_spec
  constructor
  · rintro ⟨x,hx,pos⟩
    apply joint; intro i
    let f (j : Fin k) := if j = cls i then i else rep j
    have eq j : profile rs (f j) = profile rs (rep j) := by
      by_cases h : j = cls i <;> simp [f,h,matchCol]
    refine ⟨_,push_solution _ _ f (fun r m => ⟨_,List.mem_map_of_mem m,fun j => coeff (eq j) m⟩) x hx,?_⟩
    exact hit f i pos (cls i) (by simp [f])
  · rintro ⟨x,hx,pos⟩
    apply joint; intro j
    let f (i : Fin n) := if i = rep j then j else cls i
    have eq i : profile rs (rep (f i)) = profile rs i := by
      by_cases h : i = rep j <;> simp [f,h,matchCol]
    refine ⟨_,push_solution _ _ f ?_ x hx,hit f j pos (rep j) (by simp [f])⟩
    rintro _ m
    obtain ⟨r,member,rfl⟩ := List.mem_map.mp m
    exact ⟨r,member,fun i => coeff (eq i) member⟩

theorem feasible_iff (rs : List (Row n)) : Feasible (compressed rs) ↔ Feasible rs := by
  apply restrict_iff
  simpa [List.get_eq_getElem] using covers rs

theorem run_sound (solve : {k : Nat} → List (Row k) → Option Bool)
    (sound : ∀ {k : Nat} (rows : List (Row k)) b, solve rows = some b → (b = true ↔ Feasible rows))
    (rs : List (Row n)) {b} (result : run solve rs = some b) : b = true ↔ Feasible rs := by
  by_cases ok : n ≤ 4096 ∧ rs.length ≤ 64
  · by_cases smaller : (representatives rs).length < n
    · exact (sound (compressed rs) b (by simpa [run,ok,smaller,guard,compressed] using result)).trans (feasible_iff rs)
    · simp [run,ok,smaller,guard,failure] at result
  · simp [run,ok,guard,failure] at result

/-- A solver with a fixed input-only domain inherits it on the reference
quotient whenever at least one column is shared. -/
def Within (domain : {k : Nat} → List (Row k) → Prop) (rs : List (Row n)) : Prop :=
  (n ≤ 4096 ∧ rs.length ≤ 64) ∧ (reference rs).length < n ∧ domain (projected rs (reference rs))

theorem run_complete (solve : {k : Nat} → List (Row k) → Option Bool)
    (domain : {k : Nat} → List (Row k) → Prop)
    (complete : ∀ {k : Nat} (rows : List (Row k)), domain rows → (solve rows).isSome)
    (rs : List (Row n)) (h : Within domain rs) : (run solve rs).isSome := by
  obtain ⟨bounds,smaller,admitted⟩ := h
  unfold run
  rw [representatives_eq rs]
  simpa [guard,bounds,smaller] using complete _ admitted

section

private def group (i : Fin 48) := min i.val 3

private def equation (p q : Nat → Nat) (disjoint : ∀ j, p j = 0 ∨ q j = 0) : Row 48 :=
  ⟨fun i => p (group i),fun i => q (group i),fun i => disjoint (group i)⟩

private def source : List (Row 48) :=
  [equation (fun j => if j = 3 then 1 else 0) (fun j => if j = 2 then 1 else 0)
      (by intro j; by_cases h : j = 3 <;> simp [h]),
   equation (fun j => if j = 2 then 2 else 0) (fun j => if j < 2 then 1 else 0)
      (by intro j; by_cases h : j = 2 <;> simp [h]),
   equation (fun j => if j = 0 then 1 else 0) (fun j => if j = 1 then 1 else 0)
      (by intro j; by_cases h : j = 0 <;> simp [h])]

/-- Forty-five columns share a profile. The final equation distinguishes
two columns that the first two equations treat identically. The direct
test fails on all 48 original columns and succeeds on the four classes. -/
theorem wide_three_rows : direct source = none ∧ (reference source).length = 4 ∧
    run (@direct) source = some true := by
  have reps : reference source = [0,1,2,3] := by decide
  refine ⟨by decide,by rw [reps]; rfl,?_⟩
  unfold run
  rw [representatives_eq source,reps]
  decide

end
end Tamarin.ACFeasibility.ColumnQuotient
