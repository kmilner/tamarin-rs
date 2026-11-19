import TamarinRuntime.CollectorMultiplicity
import Std.Data.HashMap.Lemmas

namespace Tamarin.CollectorMultiplicity

/-- One necessary condition for a partition into nonempty variable images.
Several collectors may pass this individual test using the same class. -/
def Possible (occ residual : List UInt64) : Prop :=
  ∀ i ∈ occ, ∃ j ∈ residual, occ.count i ≤ residual.count j

def Correct (test : Kernel) := ∀ occ residual, test occ residual = true ↔ Possible occ.toList residual.toList

private structure Tracks (s : Tally) (xs : List UInt64) : Prop where
  counts : ∀ k, s.counts.getD k 0 = xs.count k
  upper : ∀ k, xs.count k ≤ s.largest
  attained : 0 < s.largest → ∃ k, xs.count k = s.largest

private theorem tracks_push {s xs} (ok : Tracks s xs) (key : UInt64) :
    Tracks (increment s key) (xs ++ [key]) := by
  simp only [increment,ok.counts]
  constructor
  · intro j
    by_cases e : key = j <;> simp [Std.HashMap.getD_insert,e,ok.counts,List.count_append]
  · intro j
    have upper := ok.upper j
    by_cases e : key = j <;> simp [e,List.count_append] <;> omega
  · intro _
    by_cases grew : s.largest ≤ xs.count key + 1
    · exact ⟨key,by simp [List.count_append,Nat.max_eq_right grew]⟩
    · obtain ⟨k,hk⟩ := ok.attained (by omega)
      have ne : key ≠ k := fun e => by subst k; omega
      exact ⟨k,by simp [List.count_append,ne,hk,Nat.max_eq_left (by omega : xs.count key + 1 ≤ s.largest)]⟩

private theorem tracks_fold (todo : List UInt64) (before : List UInt64) (s : Tally) (ok : Tracks s before) :
    Tracks (todo.foldl increment s) (before ++ todo) := by
  induction todo generalizing before s with
  | nil => simpa using ok
  | cons k tail ih => simpa using ih (before ++ [k]) _ (tracks_push ok k)

private theorem tracks (xs : Array UInt64) : Tracks (xs.foldl increment ⟨∅,0⟩) xs.toList := by
  have empty : Tracks ⟨∅,0⟩ [] := ⟨by simp,by simp,by simp⟩
  simpa only [Array.foldl_toList,List.nil_append] using tracks_fold xs.toList [] _ empty

private theorem bound_iff (l r : Array UInt64) :
    largestCount l ≤ largestCount r ↔ Possible l.toList r.toList := by
  have L := tracks l
  have R := tracks r
  constructor
  · intro bound k hk
    have pos := List.count_pos_iff.mpr hk
    have up : l.toList.count k ≤ largestCount l := L.upper k
    obtain ⟨j,hit⟩ := R.attained (show 0 < largestCount r by omega)
    change r.toList.count j = largestCount r at hit
    exact ⟨j,List.count_pos_iff.mp (by omega),by omega⟩
  · intro possible
    by_cases pos : 0 < largestCount l
    · obtain ⟨j,hit⟩ := L.attained pos
      obtain ⟨k,_,hk⟩ := possible j (List.count_pos_iff.mp (hit ▸ pos))
      have up : r.toList.count k ≤ largestCount r := R.upper k
      change l.toList.count j = largestCount l at hit
      omega
    · omega

theorem run_correct : Correct run := by
  intro l r
  rw [← bound_iff]
  have cap : largestCount r ≤ r.size := by
    by_cases pos : 0 < largestCount r
    · obtain ⟨k,hit⟩ := (tracks r).attained pos
      change r.toList.count k = largestCount r at hit
      rw [← hit,← Array.length_toList]
      exact List.count_le_length
    · omega
  have nonempty (h : 0 < r.size) : 0 < largestCount r := by
    obtain ⟨k,hk⟩ := List.exists_mem_of_length_pos (l := r.toList) (by simpa using h)
    exact Nat.lt_of_lt_of_le (List.count_pos_iff.mpr hk) ((tracks r).upper k)
  by_cases small : r.size < largestCount l
  · simp [run,small]; omega
  · simp [run,small]
    intro one
    by_cases zero : largestCount l = 0
    · omega
    · have := nonempty (by omega); omega

end Tamarin.CollectorMultiplicity
