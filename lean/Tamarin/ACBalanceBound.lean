import Tamarin.ACBasisComplete

/-! Position-independent bound for primitive homogeneous balance equations.
Order occurrences so a nonpositive partial sum takes a nonnegative step
and a positive partial sum takes a nonpositive step. Within a minimal
zero-sum sequence no partial sum can repeat before its final step. -/
namespace Tamarin.ACBasis.BalanceBound
variable {α : Type}

def mass (w : α → Int) (xs : List α) := (xs.map w).sum

private theorem mass_perm (w : α → Int) {xs ys : List α} (p : xs.Perm ys) : mass w xs = mass w ys := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simpa [mass] using ih
  | swap => simp [mass]; omega
  | trans _ _ ih kh => exact ih.trans kh

private def starts (w : α → Int) (a : Int) : List α → List Int
  | [] => []
  | x :: xs => a :: starts w (a+w x) xs

private theorem positive_mass (w : α → Int) (xs : List α) (each : ∀ x ∈ xs, 0 < w x) (nonempty : xs ≠ []) :
    0 < mass w xs := by
  have nonnegative (l : List α) (ok : ∀ x ∈ l, 0 < w x) : 0 ≤ mass w l := by
    induction l with
    | nil => simp [mass]
    | cons a as ih =>
      have h := ok a List.mem_cons_self
      have t := ih fun x hx => ok x (List.mem_cons_of_mem _ hx)
      change 0 ≤ w a + mass w as
      omega
  cases xs with
  | nil => contradiction
  | cons a as =>
    have h := each a List.mem_cons_self
    have t := nonnegative as fun x hx => each x (List.mem_cons_of_mem _ hx)
    change 0 < w a + mass w as
    omega

private theorem choose_step (w : α → Int) (a : Int) (xs : List α) (h : xs ≠ []) (endAt : a + mass w xs = 0) :
    ∃ x ∈ xs, (a ≤ 0 ∧ 0 ≤ w x) ∨ (0 < a ∧ w x ≤ 0) := by
  apply Classical.byContradiction
  intro none
  by_cases sign : a ≤ 0
  · have neg := positive_mass (fun x => -w x) xs (fun x hx => by
      have n : ¬0 ≤ w x := fun p => none ⟨x,hx,.inl ⟨sign,p⟩⟩
      omega) h
    have reverse (l : List α) : mass (fun x => -w x) l = -mass w l := by
      induction l with
      | nil => rfl
      | cons x l ih =>
        change -w x + mass _ l = -(w x + mass w l)
        omega
    rw [reverse] at neg
    omega
  · have pos := positive_mass w xs (fun x hx => by
      have n : ¬w x ≤ 0 := fun p => none ⟨x,hx,.inr ⟨by omega,p⟩⟩
      omega) h
    omega

private theorem bounded_order [DecidableEq α] (w : α → Int) (M : Nat) (xs : List α) (a : Int)
    (inside : -(M : Int) < a ∧ a ≤ M) (weights : ∀ x ∈ xs, -(M : Int) ≤ w x ∧ w x ≤ M)
    (endAt : a + mass w xs = 0) :
    ∃ ys, xs.Perm ys ∧ ∀ b ∈ starts w a ys, -(M : Int) < b ∧ b ≤ M := by
  by_cases empty : xs = []
  · subst xs; exact ⟨[],.nil,fun _ h => by contradiction⟩
  obtain ⟨x,here,sign⟩ := choose_step w a xs empty endAt
  have p := List.perm_cons_erase here
  have size := p.length_eq
  have one := weights x here
  have sum : mass w xs = w x + mass w (xs.erase x) := mass_perm w p
  obtain ⟨zs,perm,ok⟩ := bounded_order w M (xs.erase x) (a+w x) (by rcases sign with h|h <;> constructor <;> omega)
    (fun i hi => weights i (p.symm.subset (List.mem_cons_of_mem _ hi))) (by omega)
  exact ⟨x::zs,p.trans (perm.cons x),fun b h => (List.mem_cons.mp h).elim (fun e => e ▸ inside) (ok b)⟩
termination_by xs.length
decreasing_by simp at size; omega

private theorem start_prefix {w : α → Int} {xs : List α} {a b : Int} (seen : b ∈ starts w a xs) :
    ∃ p q, xs = p ++ q ∧ q ≠ [] ∧ a + mass w p = b := by
  induction xs generalizing a with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp seen with rfl | atTail
    · exact ⟨[],x::xs,rfl,by simp,by simp [mass]⟩
    · obtain ⟨p,q,eq,live,hit⟩ := ih atTail
      exact ⟨x::p,q,by simp [eq],live,by change a + (w x + mass w p) = b; omega⟩

/-- A repeated start state supplies a proper nonempty balanced sublist. -/
private theorem repeat_segment {w : α → Int} {xs : List α} {a : Int} (repeats : ¬(starts w a xs).Nodup) :
    ∃ part, part.Sublist xs ∧ part ≠ [] ∧ part.length < xs.length ∧ mass w part = 0 := by
  induction xs generalizing a with
  | nil => exact False.elim (repeats .nil)
  | cons x xs ih =>
    by_cases seen : a ∈ starts w (a+w x) xs
    · obtain ⟨p,q,eq,live,hit⟩ := start_prefix seen
      subst xs
      refine ⟨x::p,(List.sublist_append_left p q).cons_cons _,by simp,?_,?_⟩
      · have := List.length_pos_iff.mpr live
        simp only [List.length_cons,List.length_append]; omega
      · change w x + mass w p = 0; omega
    · have bad : ¬(starts w (a+w x) xs).Nodup := fun nd => repeats (List.nodup_cons.mpr ⟨seen,nd⟩)
      obtain ⟨p,sub,live,small,zero⟩ := ih bad
      exact ⟨p,sub.cons _,live,by simp; omega,zero⟩

private theorem starts_length (w : α → Int) (a : Int) (xs : List α) : (starts w a xs).length = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [starts,ih]

theorem small_balanced [DecidableEq α] (w : α → Int) (M : Nat) (pos : 0 < M) (xs : List α)
    (nonempty : xs ≠ []) (balanced : mass w xs = 0)
    (bound : ∀ x ∈ xs, -(M : Int) ≤ w x ∧ w x ≤ M) :
    ∃ ys, ys ≠ [] ∧ ys.length ≤ 2*M ∧ mass w ys = 0 ∧ ∀ x, ys.count x ≤ xs.count x := by
  by_cases short : xs.length ≤ 2*M
  · exact ⟨xs,nonempty,short,balanced,fun _ => Nat.le_refl _⟩
  obtain ⟨zs,perm,within⟩ := bounded_order w M xs 0 (by constructor <;> omega) bound (by omega)
  let states := starts w 0 zs
  let interval := (List.range (2*M)).map fun (i : Nat) => (i : Int) + 1 - M
  have inside : states ⊆ interval := by
    intro b hb
    have h := within b hb
    apply List.mem_map.mpr
    exact ⟨(b + M - 1).toNat,List.mem_range.mpr (by omega),by omega⟩
  have duplicate : ¬states.Nodup := by
    intro nd
    have le := nd.length_le_of_subset inside
    simp only [states,starts_length,interval,List.length_map,List.length_range] at le
    exact short (perm.length_eq ▸ le)
  obtain ⟨p,sub,live,smaller,zero⟩ := repeat_segment duplicate
  obtain ⟨ys,yl,yn,yz,cnt⟩ := small_balanced w M pos p live zero (fun x hx => bound x (perm.symm.subset (sub.subset hx)))
  exact ⟨ys,yl,yn,yz,fun x => Nat.le_trans (cnt x) (by rw [perm.count_eq x]; exact sub.count_le x)⟩
termination_by xs.length
decreasing_by have := perm.length_eq; omega

private theorem dot_cons {n : Nat} (p : Vec n) (j : Fin n) (xs : List (Fin n)) :
    dot p (j::xs).count = p j + dot p xs.count := by
  have count (i : Fin n) : (j::xs).count i = spike j 1 i + xs.count i := by
    by_cases e : i = j
    · subst i; simp [spike]; omega
    · simp [spike,e,Ne.symm e]
  rw [funext count]
  simp only [dot,Nat.mul_add,total_add]
  change dot p (spike j 1) + _ = _
  simp [dot_spike]

private theorem mass_eq {n : Nat} (r : Row n) (xs : List (Fin n)) :
    mass (fun i => (r.pos i : Int) - r.neg i) xs = (dot r.pos xs.count : Int) - dot r.neg xs.count := by
  induction xs with
  | nil => simp [mass,dot,total]
  | cons j xs ih =>
    change ((r.pos j : Int) - r.neg j) + mass _ xs = _
    rw [dot_cons,dot_cons,ih]
    omega

/-- In particular a generator search never needs a coordinate exceeding
twice the maximum absolute coefficient. The dominated solution uses only
occurrences of the given solution, preserving correlations across coordinates. -/
theorem dominated_compact {n : Nat} (r : Row n) (x : Vec n) (balance : r.Holds x)
    (nonzero : ∃ i, 0 < x i) :
    ∃ y : Vec n, r.Holds y ∧ (∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ (∀ i, y i ≤ 2*r.cap) := by
  let xs := (List.finRange n).flatMap fun i => List.replicate (x i) i
  have original : xs.count = x := funext fun i => by
    simpa [xs,List.mem_finRange] using ACSystem.parts_count _ (List.nodup_finRange n) x i
  let w := fun i => (r.pos i : Int) - r.neg i
  have balanced : mass w xs = 0 := by rw [mass_eq,original,show dot r.pos x = dot r.neg x from balance]; omega
  have pos : 0 < r.cap := List.le_max_of_mem (show 1 ∈ 1 :: (List.ofFn r.pos ++ List.ofFn r.neg) from List.mem_cons_self)
  have small i : -(r.cap : Int) ≤ w i ∧ w i ≤ r.cap := by
    have l : r.pos i ≤ r.cap := List.le_max_of_mem (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
    have h : r.neg i ≤ r.cap := List.le_max_of_mem (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
    dsimp [w]; omega
  have nz : xs ≠ [] := by
    obtain ⟨i,hi⟩ := nonzero
    rw [←original] at hi
    intro he
    simp [he] at hi
  obtain ⟨ys,live,bound,zero,sub⟩ := small_balanced w r.cap pos xs nz balanced (fun i _ => small i)
  have holds : r.Holds ys.count := by
    rw [mass_eq] at zero
    unfold Row.Holds
    omega
  refine ⟨ys.count,holds,?_,(original ▸ sub),fun i => Nat.le_trans (List.count_le_length ..) bound⟩
  cases ys with
  | nil => contradiction
  | cons j js => exact ⟨j,by simp⟩

end Tamarin.ACBasis.BalanceBound
