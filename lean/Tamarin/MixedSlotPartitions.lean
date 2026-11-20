import Tamarin.MixedLocalAnswers

/-! A finite partition of the source slots can represent the exact equality
relation induced by any solution modulo B. The partition ranges over input
slots alone and is independent of the size of their instantiated terms. -/
namespace Tamarin.MixedUnification
variable {s : Signature}
namespace Constraint

def slots (c : Constraint s) := c.out :: (match c with
  | .atom .. => [] | .free _ _ xs => List.ofFn xs | .comm _ _ a b | .ac _ _ a b => [a,b])

def rename (k : Nat → Nat) : Constraint s → Constraint s
  | .atom i a => .atom (k i) a
  | .free i f xs => .free (k i) f (k ∘ xs)
  | .comm i f a b => .comm (k i) f (k a) (k b)
  | .ac i f a b => .ac (k i) f (k a) (k b)

theorem slots_rename (k) (c : Constraint s) : (c.rename k).slots = c.slots.map k := by
  cases c <;> simp [slots,rename,out,List.map_ofFn,Function.comp_def]

theorem rename_holds (k) (c : Constraint s) (W : Nat → Term s) : (c.rename k).Holds W ↔ c.Holds (W ∘ k) := by
  cases c <;> rfl

theorem holds_congr (c : Constraint s) {V W : Nat → Term s}
    (eq : ∀ i ∈ c.slots, EquivB (V i) (W i)) (h : c.Holds V) : c.Holds W := by
  apply (eq _ List.mem_cons_self).symm.trans (h.trans _)
  cases c with
  | atom => exact .refl _
  | free => exact .free _ _ _ fun i => eq _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  | ac | comm =>
    first | apply EquivB.comm_congr | apply EquivB.ac_congr
    all_goals apply eq; simp [slots]
end Constraint

namespace SlotPartitions

/-- Extend a partition with a singleton or join a class already represented.
Keeping only representatives avoids enumerating multiple names for one class. -/
def choices : List Nat → List (Nat → Nat)
  | [] => [id]
  | i :: is => (choices is).flatMap fun k =>
    (i :: is.filter (fun j => k j == j)).map fun j x => if x = i then j else k x

theorem covers (is : List Nat) (distinct : is.Nodup) (V : Nat → Term s) :
    ∃ k ∈ choices is, (∀ i ∈ is, k i ∈ is ∧ k (k i) = k i ∧ EquivB (V i) (V (k i))) ∧
      ∀ i ∈ is, ∀ j ∈ is, EquivB (V i) (V j) → k i = k j := by
  classical
  induction is with
  | nil => exact ⟨_,List.mem_singleton_self _,by simp,by simp⟩
  | cons i is ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp distinct
    obtain ⟨k,hk,rep,same⟩ := ih nd
    have extend {x : Nat} (hx : x ∈ is) : x ≠ i := fun e => fresh (e ▸ hx)
    by_cases found : ∃ j ∈ is, EquivB (V i) (V j)
    · obtain ⟨j,hj,eq⟩ := found
      obtain ⟨mem,fix,atJ⟩ := rep j hj
      refine ⟨_,List.mem_flatMap.mpr ⟨_,hk,List.mem_map_of_mem (List.mem_cons_of_mem i
        (List.mem_filter.mpr ⟨mem,beq_iff_eq.mpr fix⟩))⟩,?_,?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with ex | mx
        · subst x; simp [extend mem,fix,List.mem_cons_of_mem i mem,eq.trans atJ]
        · obtain ⟨hm,hf,he⟩ := rep x mx
          simp [extend mx,extend hm,hf,List.mem_cons_of_mem i hm,he]
      · intro x hx y hy e
        rcases List.mem_cons.mp hx with ex|mx <;> rcases List.mem_cons.mp hy with ey|my
        all_goals try subst x
        all_goals try subst y
        · rfl
        · simpa [extend my] using same j hj y my (eq.symm.trans e)
        · simpa [extend mx] using same x mx j hj (e.trans eq)
        · simp [extend mx,extend my,same x mx y my e]
    · refine ⟨_,List.mem_flatMap.mpr ⟨_,hk,List.mem_map_of_mem (List.mem_cons_self (a := i))⟩,?_,?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with ex | mx
        · subst x; simp [EquivB.refl]
        · obtain ⟨hm,hf,he⟩ := rep x mx
          simp [extend mx,extend hm,List.mem_cons_of_mem i hm,hf,he]
      · intro x hx y hy e
        rcases List.mem_cons.mp hx with ex|mx <;> rcases List.mem_cons.mp hy with ey|my
        all_goals try subst x
        all_goals try subst y
        · rfl
        · exact (found ⟨_,my,e⟩).elim
        · exact (found ⟨_,mx,e.symm⟩).elim
        · simp [extend mx,extend my,same x mx y my e]

end SlotPartitions
end Tamarin.MixedUnification
