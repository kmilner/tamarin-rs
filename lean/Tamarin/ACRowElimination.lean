import Tamarin.AtomicACPair
import Tamarin.CommonCancellation

/-! Exact row subtraction for simultaneous ordinary AC constraints. The
operands may be arbitrary terms. Each B-class in a substitution's flattened
images supplies one additive multiplicity, including factors introduced by
instantiating a message variable with a product. -/
namespace Tamarin.ACRowElimination
open Cancellation
variable {sig : Signature} {α : Type}

structure Row (α : Type) where
  lhs : List α
  rhs : List α

def weight (w : α → Nat) (xs : List α) : Nat := (xs.map w).sum

def Balanced (r : Row α) (w : α → Nat) := weight w r.lhs = weight w r.rhs

/-- The algebraic identity target = pivot + reduced as signed rows, expressed
using only nonnegative operand occurrences. Repeated IDs count repeatedly. -/
def Certificate (pivot target reduced : Row α) : Prop :=
  (target.lhs ++ pivot.rhs ++ reduced.rhs).Perm (target.rhs ++ pivot.lhs ++ reduced.lhs)

theorem Certificate.balanced_iff {pivot target reduced : Row α} (cert : Certificate pivot target reduced)
    (w : α → Nat) (keep : Balanced pivot w) : Balanced target w ↔ Balanced reduced w := by
  have perm_sum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
    induction h with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap a b xs => simp only [List.sum_cons]; omega
    | trans _ _ ih ik => exact ih.trans ik
  have total := perm_sum (cert.map w)
  simp only [List.map_append,List.sum_append] at total
  unfold Balanced weight at *
  omega

noncomputable def multiplicity (f : sig.ACSym) (σ : Substitution sig) (get : α → Term sig)
    (k : Class sig) (i : α) : Nat := by
  classical exact (flatten f (σ.apply (get i))).count k

def Holds (r : Row α) (f : sig.ACSym) (get : α → Term sig) (σ : Substitution sig) : Prop :=
  ∀ k, Balanced r (multiplicity f σ get k)

theorem Certificate.holds_iff {pivot target reduced : Row α} (cert : Certificate pivot target reduced)
    (f : sig.ACSym) (get : α → Term sig) (σ : Substitution sig) (keep : Holds pivot f get σ) :
    Holds target f get σ ↔ Holds reduced f get σ :=
  forall_congr' (fun k => cert.balanced_iff _ (keep k))

/-- The exact two output rows returned by the linked cancellation kernel
certify subtraction, independently of their ordering and the request alphabet. -/
theorem certificate_of_cancel {run} (ok : CommonCancellation.Correct run) (pivot target : Row UInt64)
    (l r : List UInt64) (packet : run (target.lhs ++ pivot.rhs).toArray (target.rhs ++ pivot.lhs).toArray =
      #[l.toArray,r.toArray]) : Certificate pivot target ⟨l,r⟩ := by
  obtain ⟨c,l',r',out,pl,pr,_⟩ := ok (target.lhs ++ pivot.rhs).toArray (target.rhs ++ pivot.lhs).toArray
  rw [packet] at out
  simp at out
  obtain ⟨rfl,rfl⟩ := out
  exact (pl.append_right r).trans ((by simpa [List.append_assoc] using (List.perm_append_comm (l₁ := l) (l₂ := r)).append_left c :
    ((c ++ l) ++ r).Perm ((c ++ r) ++ l)).trans (pr.append_right l).symm)

/-- Flat rows may be in a different order or association from the terms
passed by the caller. Decoding requires a nonempty side on a term equation. -/
structure Represents (r : Row α) (f : sig.ACSym) (get : α → Term sig) (eq : Equation sig) : Prop where
  lhs : ∃ t, ACRepresentation.decode f (r.lhs.map get) = some t ∧ EquivB eq.lhs t
  rhs : ∃ t, ACRepresentation.decode f (r.rhs.map get) = some t ∧ EquivB eq.rhs t

theorem singleton (f : sig.ACSym) (get : α → Term sig) (a b : α) :
    Represents ⟨[a],[b]⟩ f get ⟨get a,get b⟩ :=
  ⟨⟨_,rfl,.refl _⟩,⟨_,rfl,.refl _⟩⟩

theorem pair (f : sig.ACSym) (get : α → Term sig) (a b c d : α) :
    Represents ⟨[a,b],[c,d]⟩ f get ⟨.ac f (get a) (get b),.ac f (get c) (get d)⟩ :=
  ⟨⟨_,rfl,.refl _⟩,⟨_,rfl,.refl _⟩⟩

private theorem decoded_count (f : sig.ACSym) (get : α → Term sig) (σ : Substitution sig)
    (k : Class sig) {xs : List α} {t : Term sig} (h : ACRepresentation.decode f (xs.map get) = some t) :
    weight (multiplicity f σ get k) xs = multiplicity f σ id k t := by
  cases xs with
  | nil => cases h
  | cons a as =>
    obtain rfl : t = ACRepresentation.fold f (get a) (as.map get) := (Option.some.inj h).symm
    induction as generalizing a with
    | nil => simp [weight,multiplicity,ACRepresentation.fold]
    | cons b bs ih =>
      have tail := ih b rfl
      unfold weight at tail ⊢
      simp only [List.map_cons,List.sum_cons] at tail ⊢
      rw [tail]
      classical
      change _ + _ = (flatten f (.ac f _ _)).count k
      rw [flatten_ac,List.count_append]
      rfl

theorem Represents.holds_iff {r : Row α} {f : sig.ACSym} {get : α → Term sig} {eq : Equation sig}
    (repr : Represents r f get eq) (σ : Substitution sig) :
    Holds r f get σ ↔ EquivB (σ.apply eq.lhs) (σ.apply eq.rhs) := by
  classical
  obtain ⟨⟨l,hl,el⟩,⟨s,hs,es⟩⟩ := repr
  have separated := fun k => And.intro (decoded_count f get σ k hl) (decoded_count f get σ k hs)
  have basis : EquivB (σ.apply eq.lhs) (σ.apply eq.rhs) ↔ EquivB (σ.apply l) (σ.apply s) :=
    ⟨fun h => (el.subst σ.image).symm.trans (h.trans (es.subst σ.image)),
      fun h => (el.subst σ.image).trans (h.trans (es.subst σ.image).symm)⟩
  rw [basis]
  constructor
  · intro all
    apply equiv_of_flatten_perm f
    apply List.perm_iff_count.mpr
    intro k
    exact (separated k).1.symm.trans ((all k).trans (separated k).2)
  · intro h k
    exact (separated k).1.trans (((flatten_equiv f h).count_eq k).trans (separated k).2.symm)

/-- A shorter side consisting of single factors cannot equal a longer
side: every operand contributes at least one factor after substitution. -/
theorem impossible_width (r : Row α) (f : sig.ACSym) (get : α → Term sig)
    (atoms : ∀ i ∈ r.lhs, AtomicACPair.Atomic f (get i)) (width : r.lhs.length < r.rhs.length)
    (σ : Substitution sig) : ¬Holds r f get σ := by
  classical
  let factors (i : α) := flatten f (σ.apply (get i))
  have total (k : Class sig) (xs : List α) :
      weight (multiplicity f σ get k) xs = (xs.flatMap factors).count k := by
    induction xs with
    | nil => rfl
    | cons a as ih =>
      simpa [weight,List.count_append,multiplicity,factors] using ih
  have lower (xs : List α) : xs.length ≤ (xs.flatMap factors).length := by
    induction xs with
    | nil => exact Nat.le_refl _
    | cons i is ih =>
      have pos : 0 < (factors i).length := by
        apply List.length_pos_iff.mpr
        intro h
        have eq := fold_flatten f (σ.apply (get i))
        change fold f (factors i) = _ at eq
        rw [h] at eq; contradiction
      simp only [List.length_cons,List.flatMap_cons,List.length_append]; omega
  have left (xs : List α) (atomic : ∀ i ∈ xs, AtomicACPair.Atomic f (get i)) :
      (xs.flatMap factors).length = xs.length := by
    induction xs with
    | nil => rfl
    | cons a as ih =>
      rw [List.flatMap_cons,show factors a = [_] from atomic a List.mem_cons_self σ]
      simp [ih (fun i hi => atomic i (List.mem_cons_of_mem _ hi))]
  intro h
  have pairs : (r.lhs.flatMap factors).Perm (r.rhs.flatMap factors) := List.perm_iff_count.mpr fun k =>
    (total k r.lhs).symm.trans ((h k).trans (total k r.rhs))
  have bound := lower r.rhs
  rw [← pairs.length_eq,left r.lhs atoms] at bound
  omega

/-- A width clash detected in any two conjuncts refutes the whole input.
Only returned words with actual singleton images may count as rigid operands. -/
theorem cancel_refutes {run} (ok : CommonCancellation.Correct run) {pivot target : Row UInt64}
    {f : sig.ACSym} {get : UInt64 → Term sig} {p : Problem sig} {a b : Equation sig}
    (pa : a ∈ p) (pb : b ∈ p) (ra : Represents pivot f get a) (rb : Represents target f get b)
    (l r : List UInt64) (out : run (target.lhs ++ pivot.rhs).toArray (target.rhs ++ pivot.lhs).toArray =
      #[l.toArray,r.toArray]) (atoms : ∀ i ∈ l ++ r, AtomicACPair.Atomic f (get i))
    (width : l.length ≠ r.length) : ¬ p.Satisfiable := by
  rintro ⟨σ,sol⟩
  have hp := (ra.holds_iff σ).mpr (sol a pa)
  have ht := (rb.holds_iff σ).mpr (sol b pb)
  have hr := ((certificate_of_cancel ok pivot target l r out).holds_iff f get σ hp).mp ht
  by_cases h : l.length < r.length
  · exact impossible_width ⟨l,r⟩ f get (fun i hi => atoms i (List.mem_append_left r hi)) h σ hr
  · exact impossible_width ⟨r,l⟩ f get (fun i hi => atoms i (List.mem_append_right l hi)) (by dsimp; omega) σ
      (fun k => (hr k).symm)

/-- Row subtraction can refute the original system without materializing a
unit or creating a residual equation. This applies equally when several
different syntactic operands instantiate to the same B-class. -/
theorem refute {pivot old new : Row α} {f : sig.ACSym} {get : α → Term sig} {p e : Equation sig}
    (cert : Certificate pivot old new) (rp : Represents pivot f get p) (re : Represents old f get e)
    (refuted : ∀ σ, ¬ Holds new f get σ) (tail : Problem sig) : ¬Problem.Satisfiable (p :: e :: tail) := by
  rintro ⟨σ,sol⟩
  have ps := (rp.holds_iff σ).mpr (sol _ List.mem_cons_self)
  have os := (re.holds_iff σ).mpr (sol _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact refuted σ ((cert.holds_iff f get σ ps).mp os)

/-- Empty rows belong to the arithmetic certificate, never to the term
signature. One empty side and one nonempty side rule out every solution. -/
theorem empty_side (f : sig.ACSym) (get : α → Term sig) (σ : Substitution sig) (a : α) (xs : List α) :
    ¬Holds ⟨a :: xs,[]⟩ f get σ := by
  classical
  cases eq : flatten f (σ.apply (get a)) with
  | nil => have h := fold_flatten f (σ.apply (get a)); rw [eq] at h; contradiction
  | cons k ks =>
    intro all
    have h := all k
    change weight _ (a::xs) = 0 at h
    simp only [weight,List.map_cons,List.sum_cons] at h
    have pos : 0 < multiplicity f σ get k a := by simp [multiplicity,eq]
    omega

/-- Exactly the same pointwise solutions, through arbitrary shared terms
and any remaining problem. Coverage of variables discarded by a replacement
is a separate substitution-projection obligation. -/
theorem replace {pivot old new : Row α} {f : sig.ACSym} {get : α → Term sig} {p e d : Equation sig}
    (cert : Certificate pivot old new) (rp : Represents pivot f get p) (re : Represents old f get e)
    (rd : Represents new f get d) (tail : Problem sig) (σ : Substitution sig) :
    Problem.Solves (p :: e :: tail) σ ↔ Problem.Solves (p :: d :: tail) σ := by
  simp only [Problem.Solves,List.forall_mem_cons]
  constructor
  · rintro ⟨hp,he,rest⟩
    exact ⟨hp,(rd.holds_iff σ).mp ((cert.holds_iff f get σ ((rp.holds_iff σ).mpr hp)).mp ((re.holds_iff σ).mpr he)),rest⟩
  · rintro ⟨hp,hd,rest⟩
    exact ⟨hp,(re.holds_iff σ).mp ((cert.holds_iff f get σ ((rp.holds_iff σ).mpr hp)).mpr ((rd.holds_iff σ).mpr hd)),rest⟩

/-- Keeping both original equations and adding the derived one avoids losing
any original observable variable. Extra rows can be used to prune or to
supply an ordinary free or C decomposition early. -/
theorem add_derived {pivot old new : Row α} {f : sig.ACSym} {get : α → Term sig} {p e d : Equation sig}
    (cert : Certificate pivot old new) (rp : Represents pivot f get p) (re : Represents old f get e)
    (rd : Represents new f get d) (tail : Problem sig) (σ : Substitution sig) :
    Problem.Solves (p :: e :: tail) σ ↔ Problem.Solves (d :: p :: e :: tail) σ := by
  constructor
  · intro sol eq mem
    rcases List.mem_cons.mp mem with rfl|h
    · exact (replace cert rp re rd tail σ |>.mp sol) _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact sol _ h
  · exact fun sol eq mem => sol eq (List.mem_cons_of_mem _ mem)

/-- Two product equations with arbitrary shared operands P and Q. The
second equation can be replaced by an equation involving only the four
offsets. P and Q need not be distinct, variables, or indivisible. -/
theorem shared (f : sig.ACSym) (p q a b c d : Term sig) (tail : Problem sig) (σ : Substitution sig) :
    Problem.Solves (⟨.ac f p a,.ac f q b⟩ :: ⟨.ac f p c,.ac f q d⟩ :: tail) σ ↔
    Problem.Solves (⟨.ac f p a,.ac f q b⟩ :: ⟨.ac f c b,.ac f a d⟩ :: tail) σ := by
  apply replace (get := id) _ (pair f id p a q b) (pair f id p c q d) (pair f id c b a d)
  classical
  apply List.perm_iff_count.mpr
  intro k
  simp only [List.count_append,List.count_cons,List.count_nil]
  omega

/-- If the direct pairing of offsets is impossible, indivisibility forces
the other pairing. The remaining common operands must then agree. -/
theorem shared_forced (f : sig.ACSym) (p q a b c d : Term sig)
    (hc : AtomicACPair.Atomic f c) (hb : AtomicACPair.Atomic f b)
    (forbidden : ∀ σ : Substitution sig, ¬EquivB (σ.apply c) (σ.apply a))
    (tail : Problem sig) (σ : Substitution sig) :
    Problem.Solves (⟨.ac f p a,.ac f q b⟩ :: ⟨.ac f p c,.ac f q d⟩ :: tail) σ ↔
    Problem.Solves (⟨p,q⟩ :: ⟨a,b⟩ :: ⟨c,d⟩ :: tail) σ := by
  rw [shared]
  simp only [Problem.Solves,List.forall_mem_cons]
  constructor
  · rintro ⟨pivot,offsets,rest⟩
    rcases (AtomicACPair.equiv_iff f _ _ _ _ (hc σ) (hb σ)).mp offsets with ⟨impossible,_⟩|⟨cd,ba⟩
    · exact False.elim (forbidden σ impossible)
    · exact ⟨EquivB.ac_cancel_right f (pivot.trans (.ac_congr _ (.refl _) ba)),ba.symm,cd,rest⟩
  · rintro ⟨pq,ab,cd,rest⟩
    exact ⟨.ac_congr f pq ab,(EquivB.ac_congr f cd ab.symm).trans (.ac_swap ..),rest⟩

/-- Carry a complete unifier family back through a transformation, keeping
every variable visible in the original problem. -/
theorem complete_of_equivalent {p q : Problem sig} {answers : List (Substitution sig)}
    (same : ∀ σ, p.Solves σ ↔ q.Solves σ) (observed : ∀ v, p.Occurs v → q.Occurs v)
    (csu : CompleteSet q answers) : CompleteSet p answers where
  sound μ hm := (same μ).mpr (csu.sound μ hm)
  covers ρ sol := by
    obtain ⟨μ,hm,δ,agree⟩ := csu.covers ρ ((same ρ).mp sol)
    exact ⟨μ,hm,δ,fun v h => agree v (observed v h)⟩

theorem shared_forced_occurs (f : sig.ACSym) (p q a b c d : Term sig) (tail : Problem sig) (v : Variable) :
    Problem.Occurs (⟨.ac f p a,.ac f q b⟩ :: ⟨.ac f p c,.ac f q d⟩ :: tail) v ↔
    Problem.Occurs (⟨p,q⟩ :: ⟨a,b⟩ :: ⟨c,d⟩ :: tail) v := by
  simp [Problem.Occurs,Term.Occurs]; grind

end Tamarin.ACRowElimination
