import Std

/-! Breadth-first enumeration with subsumption at layer boundaries. A finite
reachable covering family proves termination without a supplied depth bound.
Search stores each layer once and checks the live frontier against earlier rows. -/
namespace Tamarin.VariantLayers
variable {α : Type}

inductive Reachable (seed : α) (next : α → List α) : α → Prop where
  | seed : Reachable seed next seed
  | child {p} : Reachable seed next p → ∀ q ∈ next p, Reachable seed next q

structure Layers (α : Type) where
  earlier : List α
  frontier : List α

def Layers.rows (l : Layers α) := l.frontier ++ l.earlier

def start (p : α) : Layers α := ⟨[],[p]⟩

def extend (next : α → List α) (l : Layers α) : Layers α :=
  ⟨l.rows,l.frontier.flatMap next⟩

def after (seed : α) (next : α → List α) : Nat → Layers α
  | 0 => start seed
  | k+1 => extend next (after seed next k)

theorem persists {seed : α} {next : α → List α} {k m : Nat} (h : k ≤ m) {p}
    (hp : p ∈ (after seed next k).rows) : p ∈ (after seed next m).rows := by
  induction h with
  | refl => exact hp
  | step _ ih => exact List.mem_append_right _ ih

theorem reached {seed : α} {next : α → List α} (k : Nat) {p} (h : p ∈ (after seed next k).rows) :
    Reachable seed next p := by
  induction k generalizing p with
  | zero =>
    obtain rfl : p = seed := by simpa [after,Layers.rows,start] using h
    exact .seed
  | succ k ih =>
    rcases List.mem_append.mp h with child|old
    · obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp child
      exact .child (ih (List.mem_append_left _ hq)) _ hp
    · exact ih old

private theorem appears {seed : α} {next : α → List α} {p} (h : Reachable seed next p) :
    ∃ k, p ∈ (after seed next k).frontier := by
  induction h with
  | seed => exact ⟨0,List.mem_cons_self⟩
  | child _ q member ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨k+1,List.mem_flatMap.mpr ⟨_,hk,member⟩⟩

private theorem together (seed : α) (next : α → List α) (xs : List α)
    (h : ∀ x ∈ xs, Reachable seed next x) : ∃ k, ∀ x ∈ xs, x ∈ (after seed next k).rows := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons x xs ih =>
    obtain ⟨i,hi⟩ := appears (h x List.mem_cons_self)
    obtain ⟨j,hj⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨max i j,?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl|later
    · exact persists (Nat.le_max_left ..) (List.mem_append_left _ hi)
    · exact persists (Nat.le_max_right ..) (hj a later)

def closed (covers : α → α → Bool) (next : α → List α) (l : Layers α) : Bool :=
  l.frontier.all fun p => (next p).all fun c => l.rows.any fun r => covers r c

private theorem expanded {seed : α} {next : α → List α} (k : Nat) {p} (h : p ∈ (after seed next k).earlier) :
    ∀ c ∈ next p, c ∈ (after seed next k).rows := by
  induction k with
  | zero => contradiction
  | succ k ih =>
    intro c hc
    rcases List.mem_append.mp h with frontier|old
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p,frontier,hc⟩)
    · exact List.mem_append_right _ (ih old c hc)

structure ClosedRows (seed : α) (next : α → List α) (covers : α → α → Bool) (rows : List α) : Prop where
  seeded : seed ∈ rows
  reachable : ∀ p ∈ rows, Reachable seed next p
  closed : ∀ p ∈ rows, ∀ c ∈ next p, ∃ q ∈ rows, covers q c = true

private theorem stopped {seed : α} {next : α → List α} {covers : α → α → Bool}
    (refl : ∀ p, covers p p = true) (k : Nat) {l} (atLayer : l = after seed next k)
    (stop : closed covers next l = true) : ClosedRows seed next covers l.rows := by
  subst l
  refine ⟨persists (k := 0) (Nat.zero_le k) (List.mem_cons_self (a := seed)), fun _ => reached k,?_⟩
  intro p hp c hc
  rcases List.mem_append.mp hp with front|old
  · exact List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp stop p front) c hc)
  · exact ⟨c,expanded k old c hc,refl c⟩

/-- Here every member of the finite basis is reachable, and together they
cover all reachable nodes. Its cardinality and discovery depths need not be known. -/
def FiniteBasis (seed : α) (next : α → List α) (covers : α → α → Bool) :=
  ∃ xs : List α, (∀ x ∈ xs, Reachable seed next x) ∧ ∀ p, Reachable seed next p → ∃ x ∈ xs, covers x p = true

private theorem eventually_closed {seed : α} {next : α → List α} {covers : α → α → Bool}
    (basis : FiniteBasis seed next covers) : ∃ k, closed covers next (after seed next k) = true := by
  obtain ⟨xs,reach,generates⟩ := basis
  obtain ⟨k,hk⟩ := together seed next xs reach
  refine ⟨k,List.all_eq_true.mpr fun p hp => List.all_eq_true.mpr fun c hc => ?_⟩
  obtain ⟨g,hg,cover⟩ := generates c (.child (reached k (List.mem_append_left _ hp)) c hc)
  exact List.any_eq_true.mpr ⟨g,hk g hg,cover⟩

private def untilClosed (seed : α) (next : α → List α) (covers : α → α → Bool) (refl : ∀ p, covers p p = true)
    (basis : FiniteBasis seed next covers) (l : Layers α) (k : Nat) (atLayer : l = after seed next k)
    (bound : k ≤ (eventually_closed basis).choose) : {rows // ClosedRows seed next covers rows} :=
  if h : closed covers next l then ⟨l.rows,stopped refl k atLayer h⟩
  else untilClosed seed next covers refl basis (extend next l) (k+1) (congrArg (extend next) atLayer) (by
    apply Nat.lt_of_le_of_ne bound
    intro exactDepth
    exact h (by rw [atLayer,exactDepth]; exact (eventually_closed basis).choose_spec))
termination_by (eventually_closed basis).choose - k
decreasing_by
  have less : k < (eventually_closed basis).choose := Nat.lt_of_le_of_ne bound (fun e => h (by
    rw [atLayer,e]; exact (eventually_closed basis).choose_spec))
  omega

def search (seed : α) (next : α → List α) (covers : α → α → Bool) (refl : ∀ p, covers p p = true)
    (basis : FiniteBasis seed next covers) : {rows // ClosedRows seed next covers rows} :=
  untilClosed seed next covers refl basis (start seed) 0 rfl (Nat.zero_le _)

end Tamarin.VariantLayers
