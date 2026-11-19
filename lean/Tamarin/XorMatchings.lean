import TamarinRuntime.XorMatchings

/-! A cancellation choice is an involution on the input positions. A fixed
point survives and each orbit of size two cancels. This contract places no
restriction on the enumeration algorithm or answer order. -/
namespace Tamarin.XorMatchings
open XorMatchingCandidate

private structure Bounded (n : Nat) (f : Nat → Nat) : Prop where
  inv : ∀ i, f (f i) = i
  outside : ∀ i, n ≤ i → f i = i

private theorem Bounded.lt {n f} (h : Bounded n f) {i} (hi : i < n) : f i < n := by
  by_cases ge : n ≤ f i
  · have e := (h.outside (f i) ge).symm.trans (h.inv i)
    omega
  · omega

private theorem Bounded.extend {n f} (h : Bounded n f) : Bounded (n+1) f :=
  ⟨h.inv,fun i hi => h.outside i (by omega)⟩

private theorem Bounded.pair {n f} (h : Bounded n f) {k} (hk : k < n) (fixed : f k = k) :
    Bounded (n+1) (pair f n k) := by
  have fn := h.outside n (Nat.le_refl _)
  constructor
  · intro i
    by_cases ni : i = n
    · subst i; simp [XorMatchingCandidate.pair, Nat.ne_of_lt hk]
    by_cases ki : i = k
    · subst i; simp [XorMatchingCandidate.pair, Nat.ne_of_lt hk]
    have nn : f i ≠ n := fun eq => ni ((h.inv i).symm.trans ((congrArg f eq).trans fn))
    have nk : f i ≠ k := fun eq => ki ((h.inv i).symm.trans ((congrArg f eq).trans fixed))
    simp [XorMatchingCandidate.pair,ni,ki,nn,nk,h.inv]
  · intro i hi
    simp [XorMatchingCandidate.pair,show i ≠ n by omega,show i ≠ k by omega,h.outside i (by omega)]

private theorem enumerate_iff (n : Nat) (f : Nat → Nat) : f ∈ enumerate n ↔ Bounded n f := by
  induction n generalizing f with
  | zero =>
    simp only [enumerate, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨fun _ => rfl,fun _ _ => rfl⟩
    · intro h; exact funext fun i => h.outside i (Nat.zero_le _)
  | succ n ih =>
    simp only [enumerate,List.mem_flatMap,List.mem_cons,List.mem_map,List.mem_filter,List.mem_range,beq_iff_eq]
    constructor
    · rintro ⟨g,hg,rfl|⟨k,⟨hk,hf⟩,rfl⟩⟩
      · exact (ih _ |>.mp hg).extend
      · exact (ih _ |>.mp hg).pair hk hf
    · intro h
      by_cases fixed : f n = n
      · have hg : Bounded n f := ⟨h.inv, fun i hi => by
          by_cases eq : i = n
          · simpa [eq] using fixed
          · exact h.outside i (by omega)⟩
        exact ⟨f,(ih f).mpr hg,.inl rfl⟩
      · let k := f n
        have hk : k < n := by
          have lt := h.lt (Nat.lt_succ_self n)
          change f n < n; omega
        have fk : f k = n := h.inv n
        let g := fun i => if i = n ∨ i = k then i else f i
        have hg : Bounded n g := by
          constructor
          · intro i
            by_cases e : i = n ∨ i = k
            · simp [g,e]
            · have ne : f i ≠ n := fun eq => e (.inr ((h.inv i).symm.trans (congrArg f eq)))
              have ke : f i ≠ k := fun eq => e (.inl ((h.inv i).symm.trans ((congrArg f eq).trans fk)))
              simp [g,e,ne,ke,h.inv]
          · intro i hi
            by_cases eq : i = n
            · simp [g,eq]
            · simp [g,eq,show i ≠ k by omega,h.outside i (by omega)]
        refine ⟨g,(ih g).mpr hg,.inr ⟨k,⟨hk,by simp [g]⟩,funext fun i => ?_⟩⟩
        by_cases eq : i = n
        · simp [XorMatchingCandidate.pair,eq,k]
        by_cases ek : i = k
        · simp [XorMatchingCandidate.pair,ek,Nat.ne_of_lt hk,fk]
        · simp [XorMatchingCandidate.pair,g,eq,ek]

def Encodes {n : Nat} (f : Fin n → Fin n) (row : Array UInt64) : Prop :=
  row = Array.ofFn fun i => (f i).val.toUInt64

/-- Widths 1 through 9 must succeed. A candidate may support more widths
as long as each successful call meets the same two-way coverage condition. -/
def Correct (run : UInt64 → Option (Array (Array UInt64))) : Prop :=
  ∀ width, (1 ≤ width.toNat → width.toNat ≤ 9 → (run width).isSome = true) ∧
    ∀ rows, run width = some rows → ∀ row,
      row ∈ rows ↔ ∃ f : Fin width.toNat → Fin width.toNat, (∀ i, f (f i) = i) ∧ Encodes f row

theorem correct : Correct XorMatchingCandidate.run := by
  intro width
  unfold XorMatchingCandidate.run
  split
  · refine ⟨by simp_all, ?_⟩
    intro _ eq row
    cases eq
    simp only [List.mem_toArray,List.mem_map]
    constructor
    · rintro ⟨g,hg,rfl⟩
      have h := (enumerate_iff _ _).mp hg
      let f := fun i : Fin width.toNat => (⟨g i,h.lt i.isLt⟩ : Fin width.toNat)
      exact ⟨f,fun i => Fin.ext (h.inv i),rfl⟩
    · rintro ⟨f,inv,rfl⟩
      let g := fun i => if h : i < width.toNat then (f ⟨i,h⟩).val else i
      refine ⟨g,(enumerate_iff _ _).mpr ⟨?_,?_⟩,?_⟩
      · intro i
        by_cases hi : i < width.toNat
        · simpa [g,hi,(f ⟨i,hi⟩).isLt] using congrArg Fin.val (inv ⟨i,hi⟩)
        · simp [g,hi]
      · intro i hi; simp [g,Nat.not_lt.mpr hi]
      · congr 1; funext i; simp [g,i.isLt]
  · rename_i outside
    exact ⟨fun lo hi => False.elim (outside ⟨lo,hi⟩),by simp⟩

end Tamarin.XorMatchings
