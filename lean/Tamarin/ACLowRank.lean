import TamarinRuntime.ACLowRank
import Tamarin.ACTwoRowFeasibility
import Tamarin.ACRowReductionCoverage

namespace Tamarin.ACFeasibility.LowRank
open ACBasis
variable {n : Nat}

/-- All three-by-three minors of the original signed matrix vanish. This
standard rank criterion includes zero and dependent rows in any order, and
has no implementation-dependent pivots, size budget or coefficient bound. -/
def Within (rs : List (Row n)) : Prop :=
  ∀ p ∈ rs, ∀ q ∈ rs, ∀ r ∈ rs, ∀ i j k : Fin n,
    let a := RowReduction.Reference.signed
    a p i * (a q j * a r k - a q k * a r j) -
      a p j * (a q i * a r k - a q k * a r i) +
      a p k * (a q i * a r j - a q j * a r i) = 0

private def det (a b c : Fin n → Int) (i j k : Fin n) : Int :=
  a i * (b j * c k - b k * c j) - a j * (b i * c k - b k * c i) + a k * (b i * c j - b j * c i)

/-- A family generated over the rationals by any pair of profiles meets the
rank-two criterion. Nonzero per-row denominators avoid a rational wire format. -/
theorem Within.of_span (rs : List (Row n)) (a b : Fin n → Int)
    (generate : ∀ r ∈ rs, ∃ d u v : Int, d ≠ 0 ∧
      ∀ i, d * RowReduction.Reference.signed r i = u * a i + v * b i) : Within rs := by
  intro p hp q hq r hr i j k
  let s := @RowReduction.Reference.signed n
  obtain ⟨d,x,y,dp,hp⟩ := generate p hp
  obtain ⟨e,z,w,dq,hq⟩ := generate q hq
  obtain ⟨f,u,v,dr,hr⟩ := generate r hr
  have scale : d * e * f * det (s p) (s q) (s r) i j k =
    det (fun t => d * s p t) (fun t => e * s q t) (fun t => f * s r t) i j k := by
    simp only [det]; grind
  change det (s p) (s q) (s r) i j k = 0
  have h : d * e * f * det (s p) (s q) (s r) i j k = 0 := by
    rw [scale]
    simp only [det,s,hp,hq,hr]
    grind
  exact (Int.mul_eq_zero.mp h).resolve_left (Int.mul_ne_zero (Int.mul_ne_zero dp dq) dr)

private theorem pivot_some {rs : List (Row n)} {weight} {p j} (h : pivot rs weight = some (p,j)) :
    p ∈ rs ∧ weight p j ≠ 0 := by
  obtain ⟨r,hr,got⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i,atIndex,eq⟩ := Option.map_eq_some_iff.mp got
  cases eq
  exact ⟨hr,by simpa using List.find?_some atIndex⟩

private theorem pivot_none {rs : List (Row n)} {weight} (h : pivot rs weight = none) :
    ∀ r ∈ rs, ∀ i, weight r i = 0 := by
  intro r hr i
  have miss := List.findSome?_eq_none_iff.mp h r hr
  have empty := Option.map_eq_none_iff.mp miss
  simpa using List.find?_eq_none.mp empty i (List.mem_finRange i)

private def eval (is : List (Fin n)) (v : Fin n → Int) (x : Vec n) :=
  (is.map (fun i => v i * (x i : Int))).sum

private theorem eval_row (is : List (Fin n)) (r : Row n) (x : Vec n) :
    eval is (coeff r) x =
      (((is.map (fun i => r.pos i * x i)).sum : Nat) : Int) - (is.map (fun i => r.neg i * x i)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [eval,List.map_cons,List.sum_cons,Int.natCast_add,Int.natCast_mul] at ih ⊢
    rw [ih]; simp only [coeff]; grind

private theorem holds_iff (r : Row n) (x : Vec n) :
    r.Holds x ↔ eval (List.finRange n) (coeff r) x = 0 := by
  rw [eval_row]
  simp [Row.Holds,dot,total,List.finRange,List.map_ofFn,Function.comp_def,Int.sub_eq_zero]
  omega

private theorem linear (is : List (Fin n)) (p q r : Row n) (d u v : Int) (x : Vec n)
    (col : ∀ i, d * coeff r i = u * coeff p i + v * coeff q i) :
    d * eval is (coeff r) x = u * eval is (coeff p) x + v * eval is (coeff q) x := by
  induction is with
  | nil => simp [eval]
  | cons i is ih =>
    have term := congrArg (· * (x i : Int)) (col i)
    simp only [eval,List.map_cons,List.sum_cons,Int.mul_add] at ih ⊢
    grind

/-- A verified integer span certificate preserves each individual equation
for every assignment, and hence preserves strictly positive feasibility. -/
theorem span_holds (p q r : Row n) (d u v : Int) (nz : d ≠ 0)
    (col : ∀ i, d * coeff r i = u * coeff p i + v * coeff q i)
    (x : Vec n) (hp : p.Holds x) (hq : q.Holds x) : r.Holds x := by
  have h := linear (List.finRange n) p q r d u v x col
  rw [(holds_iff ..).mp hp,(holds_iff ..).mp hq] at h
  simp only [Int.mul_zero,Int.add_zero] at h
  exact (holds_iff ..).mpr ((Int.mul_eq_zero.mp h).resolve_left nz)

def Basis.rows : Basis n → List (Row n)
  | .zero => []
  | .line p => [p]
  | .plane p q => [p,q]

private def checkedRow (p q r : Row n) (j k : Fin n) : Prop :=
  ∀ i, minor p q j k * coeff r i = minor r q j k * coeff p i + minor p r j k * coeff q i

private theorem rank_check {rs : List (Row n)} (within : Within rs)
    {p q r : Row n} (hp : p ∈ rs) (hq : q ∈ rs) (hr : r ∈ rs) (j k : Fin n) :
    checkedRow p q r j k := by
  intro i
  have eq := within p hp q hq r hr j k i
  change coeff p j * (coeff q k * coeff r i - coeff q i * coeff r k) -
    coeff p k * (coeff q j * coeff r i - coeff q i * coeff r j) +
    coeff p i * (coeff q j * coeff r k - coeff q k * coeff r j) = 0 at eq
  unfold minor
  grind

/-- A zero row vanishes on every vector; any row in the retained signed
span vanishes on the same solutions. This equivalence precedes positivity. -/
theorem selected_iff {rs : List (Row n)} {basis} (h : select rs = some basis) (x : Vec n) :
    SystemHolds basis.rows x ↔ SystemHolds rs x := by
  cases hp : pivot rs coeff with
  | none =>
    have eq := pivot_none hp
    have z : basis = .zero := by simpa [select,hp,eq_comm] using h
    subst basis
    constructor
    · intro _ r hr
      have holds := linear (List.finRange n) r r r 1 0 0 x (fun i => by simp [eq r hr i])
      apply (holds_iff ..).mpr
      simpa using holds
    · simp [SystemHolds,Basis.rows]
  | some pj =>
    obtain ⟨p,j⟩ := pj
    obtain ⟨pm,pnz⟩ := pivot_some hp
    cases hq : pivot rs (fun r => minor p r j) with
    | none =>
      have eq := pivot_none hq
      have z : basis = .line p := by simpa [select,hp,hq,eq_comm] using h
      subst basis
      simp only [Basis.rows,SystemHolds,List.forall_mem_singleton]
      refine ⟨fun hold r hr => span_holds p p r (coeff p j) (coeff r j) 0 pnz (fun i => ?_) x hold hold,
        fun all => all p pm⟩
      have := eq r hr i
      unfold minor at this
      grind
    | some qk =>
      obtain ⟨q,k⟩ := qk
      obtain ⟨qm,dnz⟩ := pivot_some hq
      by_cases checked : ∀ r ∈ rs, checkedRow p q r j k
      · have test : (rs.all fun r => (List.finRange n).all fun i =>
          minor p q j k * coeff r i == minor r q j k * coeff p i + minor p r j k * coeff q i) = true := by
          simpa [List.all_eq_true,checkedRow] using checked
        have z : basis = .plane p q := by simpa [select,hp,hq,test,guard,eq_comm] using h
        subst basis
        simp [Basis.rows,SystemHolds]
        exact ⟨fun ⟨holdsP,holdsQ⟩ r hr => span_holds p q r _ _ _ dnz (checked r hr) x holdsP holdsQ,
          fun all => ⟨all p pm,all q qm⟩⟩
      · have test : (rs.all fun r => (List.finRange n).all fun i =>
          minor p q j k * coeff r i == minor r q j k * coeff p i + minor p r j k * coeff q i) = false := by
          simpa [Bool.eq_false_iff,List.all_eq_true,checkedRow] using checked
        simp [select,hp,hq,test,guard,failure] at h

theorem select_complete (rs : List (Row n)) (within : Within rs) : (select rs).isSome := by
  cases hp : pivot rs coeff with
  | none => simp [select,hp]
  | some pj =>
    obtain ⟨p,j⟩ := pj
    cases hq : pivot rs (fun r => minor p r j) with
    | none => simp [select,hp,hq]
    | some qk =>
      obtain ⟨q,k⟩ := qk
      have test : (rs.all fun r => (List.finRange n).all fun i =>
          minor p q j k * coeff r i == minor r q j k * coeff p i + minor p r j k * coeff q i) = true := by
        simp only [List.all_eq_true,List.mem_finRange,forall_const,beq_iff_eq]
        exact fun r hr => rank_check within (pivot_some hp).1 (pivot_some hq).1 hr j k
      simp [select,hp,hq,test,guard]

theorem run_sound {rs : List (Row n)} {b} (got : run rs = some b) : b = true ↔ Feasible rs := by
  obtain ⟨basis,selected,rfl⟩ := Option.map_eq_some_iff.mp got
  have reduced : Feasible basis.rows ↔ Feasible rs :=
    exists_congr fun x => and_congr_left (fun _ => selected_iff selected x)
  apply Iff.trans _ reduced
  cases basis with
  | zero =>
    exact ⟨fun _ => ⟨fun _ => 1,by simp [Basis.rows,SystemHolds],by simp⟩,fun _ => rfl⟩
  | line p =>
    simpa [Basis.verdict,Basis.rows,Feasible,SystemHolds] using TwoRow.decidePair_iff p p
  | plane p q => exact TwoRow.decidePair_iff p q

theorem run_complete (rs : List (Row n)) (within : Within rs) : (run rs).isSome := by
  simpa [run] using select_complete rs within

end Tamarin.ACFeasibility.LowRank
