import Tamarin.DHProductBalance

/-! Uniqueness of the reduced signed representation, counted by B class. -/
namespace Tamarin.Rewriting.DHPeer.Balance
open ConstructorVariants Cancellation
variable {sig : Signature}

/-- All leaves of this nonempty product are irreducible opaque factors. -/
def Plain [DecidableEq sig.ACSym] (s : Symbols sig) (R : Root sig) (t : Term sig) : Prop :=
  ∀ u ∈ ACRepresentation.flatten s.mul t, Normal R u ∧ head u ≠ .free s.inv ∧ head u ≠ .free s.one

noncomputable def bag (s : Symbols sig) : Option (Term sig) → List (Class sig)
  | none => []
  | some t => Cancellation.flatten s.mul t

def assemble (s : Symbols sig) : Option (Term sig) → Option (Term sig) → Term sig
  | none, none => s.product.one
  | some p, none => p
  | none, some n => s.product.inv n
  | some p, some n => s.product.mul p (s.product.inv n)

structure Canonical [DecidableEq sig.ACSym] (s : Symbols sig) (R : Root sig)
    (t : Term sig) (p n : Option (Term sig)) : Prop where
  value : EquivB t (assemble s p n)
  positive : ∀ a, p = some a → Plain s R a
  negative : ∀ a, n = some a → Plain s R a
  disjoint : ∀ k ∈ bag s n, k ∉ bag s p

noncomputable section
open Classical

private theorem leafRead (s : Symbols sig) (R : Root sig) (k : Class sig) (t : Term sig)
    (alienH : head t ≠ .ac s.mul) (h : Normal R t ∧ head t ≠ .free s.inv ∧ head t ≠ .free s.one) :
    read s R k t = some (([classOf t].count k : Nat) : Int) := by
  rw [read_alien s R k t alienH h.2.1 h.2.2]
  by_cases eq : classOf t = k <;> simp [alien,h.1,eq]

theorem Plain.read_count [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig} {t}
    (plain : Plain s R t) (k : Class sig) :
    read s R k t = some (((Cancellation.flatten s.mul t).count k : Nat) : Int) := by
  induction t with
  | ac f a b ia ib =>
    by_cases eq : s.mul = f
    · subst f
      have pa : Plain s R a := fun u hu => plain u (by simp [ACRepresentation.flatten,hu])
      have pb : Plain s R b := fun u hu => plain u (by simp [ACRepresentation.flatten,hu])
      simp [read,ia pa,ib pb,plus,Cancellation.flatten_ac]
    · have one := plain (.ac f a b) (by simp [ACRepresentation.flatten,eq])
      simpa [Cancellation.flatten,eq] using leafRead s R k (.ac f a b)
        (fun h => eq (Head.ac.inj h).symm) one
  | var | atom | free | comm =>
    exact leafRead s R k _ (by intro h; cases h) (plain _ List.mem_cons_self)

theorem Canonical.read_count [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig} {t p n}
    (c : Canonical s R t p n) (k : Class sig) :
    read s R k t = some (((bag s p).count k : Int) - ((bag s n).count k : Int)) := by
  rw [equiv s R k c.value]
  cases p with
  | none =>
    cases n with
    | none => simp [assemble,bag]
    | some n => simp [assemble,bag,(c.negative n rfl).read_count,minus]
  | some p =>
    cases n with
    | none => simp [assemble,bag,(c.positive p rfl).read_count]
    | some n => simp [assemble,bag,(c.positive p rfl).read_count,(c.negative n rfl).read_count,plus,minus,Int.sub_eq_add_neg]

private theorem bag_nonempty (s : Symbols sig) (t : Term sig) : bag s (some t) ≠ [] := by
  intro emp
  have h := Cancellation.fold_flatten s.mul t
  simp [bag] at emp
  rw [emp] at h
  simp [Cancellation.fold] at h

private theorem bag_equiv (s : Symbols sig) {a b : Option (Term sig)}
    (h : (bag s a).Perm (bag s b)) : Option.Rel EquivB a b := by
  cases a with
  | none =>
    cases b with
    | none => constructor
    | some b => exact False.elim (bag_nonempty s b ((List.perm_nil.mp h.symm)))
  | some a =>
    cases b with
    | none => exact False.elim (bag_nonempty s a (List.perm_nil.mp h))
    | some b => exact .some (Cancellation.equiv_of_flatten_perm s.mul h)

theorem assemble_equiv (s : Symbols sig) {p n q m : Option (Term sig)}
    (pos : (bag s p).Perm (bag s q)) (neg : (bag s n).Perm (bag s m)) :
    EquivB (assemble s p n) (assemble s q m) := by
  have ep := bag_equiv s pos
  have en := bag_equiv s neg
  cases ep <;> cases en
  · apply EquivB.ac_congr <;> first | assumption | exact .free _ _ _ (fun _ => by assumption)
  · assumption
  · exact .free _ _ _ (fun _ => by assumption)
  · exact .refl _

theorem Canonical.injective [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig} {t u p n q m}
    (ct : Canonical s R t p n) (cu : Canonical s R u q m)
    (same : ∀ k, read s R k t = read s R k u) : EquivB t u := by
  have part (k) : (bag s p).count k = (bag s q).count k ∧ (bag s n).count k = (bag s m).count k := by
    have balance := same k
    rw [ct.read_count,cu.read_count,Option.some.injEq] at balance
    have separate {a b : List (Class sig)} (h : ∀ j ∈ a, j ∉ b) :
        a.count k = 0 ∨ b.count k = 0 := by
      by_cases mem : k ∈ a
      · exact .inr (List.count_eq_zero.mpr (h k mem))
      · exact .inl (List.count_eq_zero.mpr mem)
    rcases separate ct.disjoint with a|a <;> rcases separate cu.disjoint with b|b <;> omega
  exact ct.value.trans ((assemble_equiv s
    (List.perm_iff_count.mpr fun k => (part k).1)
    (List.perm_iff_count.mpr fun k => (part k).2)).trans cu.value.symm)

private theorem inv_term {s : Symbols sig} {t : Term sig} (h : head t = .free s.inv) :
    ∃ n, t = s.product.inv n := by
  cases t <;> cases h
  rename_i xs
  let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  refine ⟨xs i,congrArg (Term.free s.inv) (funext (fun j => congrArg xs (Fin.ext ?_)))⟩
  have := j.isLt; have := s.invArity; change j.val = 0; omega

private theorem unit_term {s : Symbols sig} {t : Term sig} (h : head t = .free s.one) :
    t = s.product.one := by
  cases t <;> cases h
  exact congrArg (Term.free s.one) (funext fun i => Fin.elim0 (s.oneArity ▸ i))

private theorem plainOfBag [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig} {a}
    (ha : Normal R a) (noneInv : ∀ n, classOf (s.product.inv n) ∉ Cancellation.flatten s.mul a)
    (noneUnit : classOf s.product.one ∉ Cancellation.flatten s.mul a) : Plain s R a := by
  intro t ht
  have present : classOf t ∈ Cancellation.flatten s.mul a := by
    rw [DHProduct.classes]; exact List.mem_map_of_mem ht
  refine ⟨((DHProduct.subgroup_normal_iff s.mul a).mp ha).1 _ ht,?_,?_⟩
  · intro h; obtain ⟨n,rfl⟩ := inv_term h; exact noneInv n present
  · intro h; exact noneUnit (unit_term h ▸ present)

/-- Normality splits an arbitrary exponent into disjoint positive and negative
products, allowing either side to be empty. Additional rules can only narrow
the class of possible irreducible exponents. -/
theorem decompose [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig}
    (presentation : DHProduct.Presentation s.product R)
    (inversePlain : ∀ n, HasSort (s.product.inv n) .msg → Normal R (s.product.inv n) → Plain s R n)
    {t : Term sig} (ht : HasSort t .msg) (hn : Normal R t) : ∃ p n, Canonical s R t p n := by
  by_cases unit : EquivB t s.product.one
  · exact ⟨none,none,unit,by simp,by simp,by simp [bag]⟩
  have clean := DHProduct.clean_of_normal presentation ht hn unit
  by_cases inv : ∃ v, classOf (s.product.inv v) ∈ Cancellation.flatten s.mul t
  · obtain ⟨v,hm⟩ := inv
    rw [DHProduct.classes] at hm
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hm
    have eq' : EquivB w (s.product.inv v) := Quotient.exact eq
    have typed := ACRepresentation.flatten_hasSort s.mul t (s.mulSort ▸ ht) w hw
    have msg : HasSort w .msg := s.mulSort ▸ typed
    have typInv := Term.checkSort_sound _ _ ((SortClash.check_equiv eq' .msg) ▸ Term.checkSort_complete msg)
    have normInv := (normal_equiv R eq').mp (((DHProduct.subgroup_normal_iff s.mul t).mp hn).1 w hw)
    have nv := inversePlain v typInv normInv
    rcases DHProduct.extract s.mul s.mulSort t w ht hn hw with all | ⟨p,someP,_,pNorm⟩
    · exact ⟨none,some v,all.trans eq',by simp,fun n h => by cases h; exact nv,by simp [bag]⟩
    · have shape := someP.trans (EquivB.ac_congr _ (.refl _) eq')
      have perm := Cancellation.flatten_equiv s.mul shape
      rw [Cancellation.flatten_ac] at perm
      let ps := Cancellation.flatten s.mul p
      let neg := classOf (s.product.inv v)
      change (Cancellation.flatten s.mul t).Perm (ps ++ [neg]) at perm
      have nunit : classOf s.product.one ∉ ps := fun h => clean.noUnit (perm.mem_iff.mpr (List.mem_append_left _ h))
      have ninv (n) : classOf (s.product.inv n) ∉ ps := by
        intro mem
        have move := (List.perm_cons_erase mem).append_right [neg]
        apply clean.oneInverse n v (ps.erase (classOf (s.product.inv n)))
        exact perm.trans (move.trans ((List.perm_append_comm (l₁ := ps.erase (classOf (s.product.inv n))) (l₂ := [neg])).cons _))
      refine ⟨some p,some v,shape,fun a h => by cases h; exact plainOfBag pNorm ninv nunit,
        fun a h => by cases h; exact nv,?_⟩
      intro k hk hp
      exact clean.disjoint v (perm.mem_iff.mpr (by simp [neg])) k hk (perm.mem_iff.mpr (List.mem_append_left _ hp))
  · refine ⟨some t,none,.refl _,fun a h => ?_,by simp,by simp [bag]⟩
    cases h; exact plainOfBag hn (fun n h => inv ⟨n,h⟩) clean.noUnit

/-- A defined initial reading and canonical normal outputs suffice for uniqueness
on every reduction path, without a confluence assumption about other rules. -/
theorem normal_unique [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Inventory E) (presentation : DHProduct.Presentation s.product (ruleRoot T.rules))
    (inversePlain : ∀ n, HasSort (s.product.inv n) .msg → Normal (ruleRoot T.rules) (s.product.inv n) →
      Plain s (ruleRoot T.rules) n)
    {x a b : Term sig} (hx : ∀ k, ∃ n, read s (ruleRoot T.rules) k x = some n)
    (ha : HasSort a .msg) (hb : HasSort b .msg) (na : Normal (ruleRoot T.rules) a) (nb : Normal (ruleRoot T.rules) b)
    (pathA : Reduces (ruleRoot T.rules) x a) (pathB : Reduces (ruleRoot T.rules) x b) : EquivB a b := by
  obtain ⟨_,_,ca⟩ := decompose presentation inversePlain ha na
  obtain ⟨_,_,cb⟩ := decompose presentation inversePlain hb nb
  apply ca.injective cb
  intro k
  obtain ⟨n,hn⟩ := hx k
  exact (inventory.reduces k pathA n hn).trans (inventory.reduces k pathB n hn).symm

end
end Tamarin.Rewriting.DHPeer.Balance
