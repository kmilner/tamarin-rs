import Tamarin.ACColumnQuotient

/-! Original variables in the same coefficient class remain separate
coordinates when generating AC unifiers. A quotient generator prescribes
only their sum. Every weak distribution across the class is a generator. -/
namespace Tamarin.ACBasis.Distributed
open ACFeasibility.ColumnQuotient
variable {n k : Nat}

/-- Total multiplicity assigned to each class. -/
def aggregate {k} : {n : Nat} → (Fin n → Fin k) → Vec n → Vec k
  | 0, _, _ => fun _ => 0
  | _+1, f, x =>
    let tail := aggregate (fun i => f i.succ) (fun i => x i.succ)
    fun j => (if j = f 0 then x 0 else 0) + tail j

theorem aggregate_monotone (f : Fin n → Fin k) {x y : Vec n} (le : ∀ i, x i ≤ y i) :
    ∀ j, aggregate f x j ≤ aggregate f y j := by
  induction n with
  | zero => simp [aggregate]
  | succ n ih =>
    intro j
    have e := ih (fun i => f i.succ) (fun i => le i.succ) j
    simp only [aggregate]; split <;> first | exact Nat.add_le_add (le 0) e | omega

theorem aggregate_strict (f : Fin n → Fin k) {x y : Vec n} (le : ∀ i, x i ≤ y i)
    (i : Fin n) (less : x i < y i) : aggregate f x (f i) < aggregate f y (f i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [aggregate,ite_true]
      exact Nat.add_lt_add_of_lt_of_le less (aggregate_monotone _ (fun i => le i.succ) _)
    | succ i =>
      have strict := ih (fun t => f t.succ) (fun t => le t.succ) i less
      simp only [aggregate]
      split <;> first | exact Nat.add_lt_add_of_le_of_lt (le 0) strict | omega

private theorem aggregate_zero (g : Fin n → Fin k) : aggregate g (fun _ => 0) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j; simp [aggregate,ih (fun i => g i.succ)]

theorem nonzero_iff (f : Fin n → Fin k) (x : Vec n) :
    (∃ j, 0 < aggregate f x j) ↔ ∃ i, 0 < x i := by
  constructor
  · rintro ⟨j,h⟩
    apply Classical.byContradiction; intro absent
    simp only [not_exists] at absent
    have e : x = fun _ => 0 := funext (fun i => by have := absent i; omega)
    simp [e,aggregate_zero] at h
  · rintro ⟨i,hi⟩
    exact ⟨f i,by simpa only [aggregate_zero f] using aggregate_strict f (fun _ => Nat.zero_le _) i hi⟩

/-- Every subvector of the class totals can be distributed under the
coordinatewise capacities of the given original vector. -/
theorem take_below (f : Fin n → Fin k) (x : Vec n) (z : Vec k)
    (le : ∀ j, z j ≤ aggregate f x j) :
    ∃ w, (∀ i, w i ≤ x i) ∧ aggregate f w = z := by
  induction n generalizing z with
  | zero =>
    exact ⟨Fin.elim0,fun i => i.elim0,funext (fun j => (Nat.eq_zero_of_le_zero (le j)).symm)⟩
  | succ n ih =>
    let head := min (x 0) (z (f 0))
    let remain (j : Fin k) := if j = f 0 then z j-head else z j
    have enough (j) : remain j ≤ aggregate (fun i => f i.succ) (fun i => x i.succ) j := by
      have full := le j
      by_cases h : j = f 0 <;> simp [aggregate,remain,h,head] at full ⊢ <;> omega
    obtain ⟨v,cap,eq⟩ := ih (fun i => f i.succ) (fun i => x i.succ) remain enough
    refine ⟨prepend head v,Fin.cases (Nat.min_le_left ..) cap,?_⟩
    funext j
    change (if j = f 0 then head else 0) + aggregate (fun i => f i.succ) v j = z j
    rw [eq]
    by_cases h : j = f 0 <;> simp [remain,h,head] <;> omega

private theorem aggregate_mix (f : Fin n → Fin k) (x : Vec n) :
    aggregate f x = mix (fun i => spike (f i) 1) x := by
  induction n with
  | zero => funext j; simp [aggregate,mix,dot,total]
  | succ n ih =>
    funext j
    have tail := congrFun (ih (fun i => f i.succ) (fun i => x i.succ)) j
    simp only [aggregate,mix,dot,total,List.ofFn_succ,List.sum_cons] at tail ⊢
    rw [tail]
    by_cases h : j = f 0 <;> simp [spike,h]

/-- A map from original to quotient coordinates may be chosen freely as
long as all coefficients are preserved in every equation. -/
theorem holds_iff (rs : List (Row n)) (rep : Fin k → Fin n) (f : Fin n → Fin k)
    (same : ∀ r ∈ rs, ∀ i, r.pos (rep (f i)) = r.pos i ∧ r.neg (rep (f i)) = r.neg i)
    (x : Vec n) : SystemHolds (rs.map (restrict rep)) (aggregate f x) ↔ SystemHolds rs x := by
  have row (r : Row n) (member : r ∈ rs) :
      (restrict rep r).Holds (aggregate f x) ↔ r.Holds x := by
    rw [aggregate_mix,←Row.pullback_iff,Row.pullback,Row.ofWeights_holds]
    simp only [restrict,dot_spike,Nat.mul_one]
    rw [show (fun i => r.pos (rep (f i))) = r.pos from funext (fun i => (same r member i).1),
        show (fun i => r.neg (rep (f i))) = r.neg from funext (fun i => (same r member i).2)]
    rfl
  constructor
  · intro h r m; exact (row r m).mp (h _ (List.mem_map_of_mem m))
  · rintro h _ member
    obtain ⟨r,m,rfl⟩ := List.mem_map.mp member
    exact (row r m).mpr (h r m)

theorem irreducible_iff (rs : List (Row n)) (rep : Fin k → Fin n) (f : Fin n → Fin k)
    (same : ∀ r ∈ rs, ∀ i, r.pos (rep (f i)) = r.pos i ∧ r.neg (rep (f i)) = r.neg i)
    (x : Vec n) : Irreducible rs x ↔ Irreducible (rs.map (restrict rep)) (aggregate f x) := by
  let h := holds_iff rs rep f same
  constructor
  · rintro ⟨sol,nz,minimal⟩
    refine ⟨(h _).mpr sol,(nonzero_iff ..).mpr nz,?_⟩
    intro z hz znz le
    obtain ⟨w,cap,rfl⟩ := take_below f x z le
    rw [minimal w ((h _).mp hz) ((nonzero_iff ..).mp znz) cap]
  · rintro ⟨sol,nz,minimal⟩
    refine ⟨(h _).mp sol,(nonzero_iff ..).mp nz,?_⟩
    intro y hy ynz below
    have eq := minimal _ ((h _).mpr hy) ((nonzero_iff ..).mpr ynz) (aggregate_monotone _ below)
    funext i
    have le := below i
    apply Classical.byContradiction; intro ne
    have lt := aggregate_strict f below i (by omega)
    rw [eq] at lt
    omega

/-- A checked grouping of input indices suffices for lifting generation.
No injectivity or ordering assumption is needed for membership. -/
theorem generate_iff (rs : List (Row n)) (rep : Fin k → Fin n) (f : Fin n → Fin k)
    (profiles : ∀ i, profile rs (rep (f i)) = profile rs i) (x : Vec n) :
    x ∈ generate rs ↔ aggregate f x ∈ generate (rs.map (restrict rep)) := by
  rw [mem_generate,mem_generate]
  apply irreducible_iff
  intro r hr i
  exact Prod.mk.inj (List.map_inj_left.mp (profiles i) r hr)

/-- Each full generator belongs to precisely the fiber given by its class
sums, including fibers of neutral quotient columns. -/
theorem compressed_generate (rs : List (Row n))
    (cls : Fin n → Fin (representatives rs).length)
    (profiles : ∀ i, profile rs ((representatives rs).get (cls i)) = profile rs i)
    (x : Vec n) :
    x ∈ generate rs ↔ ∃ q ∈ generate (compressed rs), aggregate cls x = q := by
  have fiber : (∃ q ∈ generate (compressed rs), aggregate cls x = q) ↔ aggregate cls x ∈ generate (compressed rs) := ⟨fun ⟨_,m,e⟩ => e ▸ m, fun m => ⟨_,m,rfl⟩⟩
  rw [fiber]
  have eq := generate_iff rs (representatives rs).get cls profiles x
  simpa [compressed,projected,show (representatives rs).get =
    (fun j : Fin (representatives rs).length => (representatives rs)[j.val]) from rfl] using eq

end Tamarin.ACBasis.Distributed
