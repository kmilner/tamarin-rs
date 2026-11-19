import Tamarin.DHProduct
import Tamarin.SortClash
import Tamarin.FiniteOccurs

/-! Normality of a signed product from the active multiplication patterns.
The single-inverse bound uses occurrences, so two identical inverses violate
it just as two different inverses do. -/
namespace Tamarin.Rewriting.DHProduct
open Cancellation
variable {s : Signature}

/-- Unit, two inverses, and a common positive/negative factor are precisely
the conflicts tested here. Individual factors must also be normal. -/
structure Clean (a : Ops s) (xs : List (Class s)) : Prop where
  noUnit : classOf a.one ∉ xs
  oneInverse : ∀ n m rest, ¬xs.Perm (classOf (a.inv n) :: classOf (a.inv m) :: rest)
  disjoint : ∀ n, classOf (a.inv n) ∈ xs → ∀ k ∈ Cancellation.flatten a.mult n, k ∉ xs

theorem Clean.part {a : Ops s} {xs ys tail : List (Class s)} (h : Clean a xs)
    (perm : xs.Perm (ys ++ tail)) : Clean a ys where
  noUnit := fun mem => h.noUnit (perm.mem_iff.mpr (List.mem_append_left _ mem))
  oneInverse n m rest p := h.oneInverse n m (rest ++ tail) (perm.trans (p.append_right tail))
  disjoint n hn k hk occupied := h.disjoint n (perm.mem_iff.mpr (List.mem_append_left _ hn))
    k hk (perm.mem_iff.mpr (List.mem_append_left _ occupied))

/-- The seven active multiplication left sides can be grouped by the
conflict their positive and negative factors necessarily contain. Extra
applications outside this head are unrestricted. -/
inductive MulPattern (a : Ops s) : Term s → Prop where
  | unit (x) : MulPattern a (a.mul x a.one)
  | cancel (x) : MulPattern a (a.mul x (a.inv x))
  | inverses (x y) : MulPattern a (a.mul (a.inv x) (a.inv y))
  | inside (x y) : MulPattern a (a.mul (a.inv (a.mul x y)) y)
  | cancelRest (x y) : MulPattern a (a.mul x (a.mul (a.inv x) y))
  | inversesRest (x y z) : MulPattern a (a.mul (a.inv x) (a.mul (a.inv y) z))
  | insideRest (x y z) : MulPattern a (a.mul (a.inv (a.mul x y)) (a.mul y z))

private theorem nonempty_factors (f : s.ACSym) (t : Term s) : ∃ k, k ∈ Cancellation.flatten f t := by
  have h := Cancellation.fold_flatten f t
  cases hx : Cancellation.flatten f t with
  | nil => simp [hx,Cancellation.fold] at h
  | cons a as => exact ⟨a,List.mem_cons_self⟩

/-- Every instance of a multiplication pattern violates the criterion.
Pattern variables may denote arbitrary nonempty products. -/
theorem MulPattern.conflict {a : Ops s} {t : Term s} (p : MulPattern a t)
    (unit : Cancellation.flatten a.mult a.one = [classOf a.one])
    (inv : ∀ n, Cancellation.flatten a.mult (a.inv n) = [classOf (a.inv n)]) :
    ¬ Clean a (Cancellation.flatten a.mult t) := by
  intro c
  cases p with
  | unit x =>
    apply c.noUnit
    simp [Ops.mul,flatten_ac,unit]
  | inverses x y =>
    apply c.oneInverse x y []
    simp [Ops.mul,flatten_ac,inv]
  | inversesRest x y z =>
    apply c.oneInverse x y (Cancellation.flatten a.mult z)
    simp [Ops.mul,flatten_ac,inv]
  | cancel x =>
    obtain ⟨k,hk⟩ := nonempty_factors a.mult x
    exact c.disjoint x (by simp [Ops.mul,flatten_ac,inv]) k hk (by simp [Ops.mul,flatten_ac,inv,hk])
  | cancelRest x y =>
    obtain ⟨k,hk⟩ := nonempty_factors a.mult x
    exact c.disjoint x (by simp [Ops.mul,flatten_ac,inv]) k hk (by simp [Ops.mul,flatten_ac,inv,hk])
  | inside x y =>
    obtain ⟨k,hk⟩ := nonempty_factors a.mult y
    apply c.disjoint (a.mul x y) (by simp [Ops.mul,flatten_ac,inv]) k
    · simp [Ops.mul,flatten_ac,hk]
    · simp [Ops.mul,flatten_ac,inv,hk]
  | insideRest x y z =>
    obtain ⟨k,hk⟩ := nonempty_factors a.mult y
    apply c.disjoint (a.mul x y) (by simp [Ops.mul,flatten_ac,inv]) k
    · simp [Ops.mul,flatten_ac,hk]
    · simp [Ops.mul,flatten_ac,inv,hk]

theorem Clean.normal [DecidableEq s.ACSym] {a : Ops s} {R : Root s} {t : Term s}
    (c : Clean a (Cancellation.flatten a.mult t))
    (unit : Cancellation.flatten a.mult a.one = [classOf a.one])
    (inv : ∀ n, Cancellation.flatten a.mult (a.inv n) = [classOf (a.inv n)])
    (children : ∀ u ∈ ACRepresentation.flatten a.mult t, Normal R u)
    (inventory : ∀ p q, ConstructorVariants.head p = .ac a.mult → R p q → MulPattern a p) :
    Normal R t := by
  apply subgroup_normal _ _ children
  intro p q hd sub fire
  obtain ⟨rest,perm⟩ := sub
  exact (inventory p q hd fire).conflict unit inv (c.part perm)

/-- In the syntactic theory inversion is a unary free symbol, hence it is
larger than each of its argument's factors. -/
theorem factor_nodes [DecidableEq s.ACSym] (f : s.ACSym) (t z : Term s)
    (mem : z ∈ ACRepresentation.flatten f t) : FiniteOccurs.nodes z ≤ FiniteOccurs.nodes t := by
  induction t with
  | ac g a b ia ib =>
    by_cases eq : f = g
    · subst g
      change _ ≤ FiniteOccurs.nodes a + FiniteOccurs.nodes b + 1
      rcases List.mem_append.mp (by simpa [ACRepresentation.flatten] using mem) with h|h
      · have := ia h; omega
      · have := ib h; omega
    · obtain rfl : z = .ac g a b := by simpa [ACRepresentation.flatten,eq] using mem
      exact Nat.le_refl _
  | _ => obtain rfl := List.mem_singleton.mp mem; exact Nat.le_refl _

structure Presentation (a : Ops s) (R : Root s) : Prop where
  multSort : s.acSort a.mult = .msg
  invFactor : ∀ n, Cancellation.flatten a.mult (a.inv n) = [classOf (a.inv n)]
  unitFactor : Cancellation.flatten a.mult a.one = [classOf a.one]
  invCongr : ∀ {n m}, EquivB n m → EquivB (a.inv n) (a.inv m)
  invChild : ∀ n, HasSort (a.inv n) .msg → HasSort n .msg
  invLarger : ∀ n, FiniteOccurs.nodes n < FiniteOccurs.nodes (a.inv n)
  unitRule : ∀ x, HasSort x .msg → R (a.mul x a.one) x
  joinRule : ∀ x y, HasSort x .msg → HasSort y .msg → R (a.mul (a.inv x) (a.inv y)) (a.inv (a.mul x y))
  roots : CancellationRoots a R

private theorem sort_of_equiv {t u : Term s} (h : EquivB t u) (ht : HasSort t .msg) : HasSort u .msg :=
  Term.checkSort_sound _ _ ((SortClash.check_equiv h .msg) ▸ Term.checkSort_complete ht)

private theorem typed_factor [DecidableEq s.ACSym] {f : s.ACSym} (hs : s.acSort f = .msg)
    {whole t : Term s} (typed : HasSort whole .msg) (mem : classOf t ∈ Cancellation.flatten f whole) :
    HasSort t .msg := by
  rw [classes] at mem
  obtain ⟨u,hu,eq⟩ := List.mem_map.mp mem
  exact sort_of_equiv (Quotient.exact eq) (hs ▸ ACRepresentation.flatten_hasSort f whole (hs ▸ typed) u hu)

/-- Exclusion of root rules at every multiplication subbag suffices for the
signed-factor conditions, including when alien factors can still rewrite. -/
theorem clean_of_blocked [DecidableEq s.ACSym] {a : Ops s} {R : Root s}
    (T : Presentation a R) {e : Term s} (typed : HasSort e .msg)
    (blocked : ∀ x y, Subbag a.mult (a.mul x y) e → ∀ out, ¬R (a.mul x y) out)
    (nonunit : ¬EquivB e a.one) : Clean a (Cancellation.flatten a.mult e) := by
  classical
  let xs := Cancellation.flatten a.mult e
  have exposed {z : Term s} (hz : classOf z ∈ xs) (atom : Cancellation.flatten a.mult z = [classOf z]) :
      Subbag a.mult z e := ⟨xs.erase (classOf z), by rw [atom]; exact List.perm_cons_erase hz⟩
  constructor
  · intro hz
    rcases (exposed hz T.unitFactor).context with eq|⟨rem,eq⟩
    · exact nonunit eq
    · have sort := (Term.checkSort_complete (sort_of_equiv eq typed))
      change (_ && _ && rem.checkSort (s.acSort a.mult)) = true at sort
      simp only [Bool.and_eq_true] at sort
      have hrem := Term.checkSort_sound _ _ sort.2
      have selected := Cancellation.flatten_equiv a.mult (eq.trans (.ac_swap _ _ _))
      exact blocked rem a.one ⟨[],by simpa [Ops.mul] using selected⟩ _ (T.unitRule rem (T.multSort ▸ hrem))
  · intro n m rest perm
    have typedInv (z : Term s) (h : classOf (a.inv z) ∈ xs) := T.invChild z (typed_factor T.multSort typed h)
    apply blocked (a.inv n) (a.inv m) ⟨rest,by simpa [Ops.mul,flatten_ac,T.invFactor] using perm⟩
    apply T.joinRule
    · exact typedInv n (perm.mem_iff.mpr (by simp))
    · exact typedInv m (perm.mem_iff.mpr (by simp))
  · intro n neg k hk live
    rw [classes] at hk
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hk
    let inv := classOf (a.inv n)
    let key := classOf z
    have different : key ≠ inv := by
      intro eq
      have := FiniteOccurs.nodes_equiv (Quotient.exact eq)
      have := factor_nodes a.mult n z hz
      have := T.invLarger n
      omega
    have only := List.perm_cons_erase (l := xs) neg
    have inRest : key ∈ xs.erase inv := (List.mem_cons.mp (only.mem_iff.mp live)).resolve_left different
    have perm := only.trans ((List.perm_cons_erase inRest).cons inv)
    have atomZ := atom_factors a.mult n z hz
    have nsort := T.invChild n (typed_factor T.multSort typed neg)
    have zsort := typed_factor T.multSort typed live
    obtain ⟨t,ht,el⟩ := ACRepresentation.flatten_correct a.mult n
    obtain ⟨pre,post,listEq⟩ := List.mem_iff_append.mp hz
    have pn : (ACRepresentation.flatten a.mult n).Perm (z :: (pre ++ post)) := by
      rw [listEq]; exact List.perm_middle
    cases tail : pre ++ post with
    | nil =>
      rw [tail] at pn
      have same := el.symm.trans (ACRepresentation.decode_perm a.mult pn t z ht rfl)
      have replace : inv = classOf (a.inv z) := Quotient.sound (T.invCongr same)
      have sub : Subbag a.mult (a.mul z (a.inv z)) e := by
        refine ⟨(xs.erase inv).erase key, ?_⟩
        rw [show Cancellation.flatten a.mult e = xs from rfl,show Cancellation.flatten a.mult (a.mul z (a.inv z)) = [key,classOf (a.inv z)] by simp [Ops.mul,flatten_ac,T.invFactor,atomZ,key]]
        rw [← replace]
        exact perm.trans (.swap key inv _)
      exact blocked _ _ sub _ (T.roots.direct z zsort)
    | cons v vs =>
      rw [tail] at pn
      let w := ACRepresentation.fold a.mult v vs
      have same := (el.symm.trans (ACRepresentation.decode_perm a.mult pn t (.ac a.mult z w) ht rfl)).trans (.ac_swap _ _ _)
      have replace : inv = classOf (a.inv (a.mul w z)) := Quotient.sound (T.invCongr same)
      have each := ACRepresentation.flatten_hasSort a.mult n (T.multSort ▸ nsort)
      have wsort : HasSort w .msg := T.multSort ▸ ACRepresentation.fold_hasSort _ _ _
        (each v (pn.mem_iff.mpr (by simp))) (fun x hx => each x (pn.mem_iff.mpr (by simp [hx])))
      have sub : Subbag a.mult (a.mul (a.inv (a.mul w z)) z) e := by
        refine ⟨(xs.erase inv).erase key, ?_⟩
        rw [show Cancellation.flatten a.mult e = xs from rfl,show Cancellation.flatten a.mult
          (a.mul (a.inv (a.mul w z)) z) = [classOf (a.inv (a.mul w z)),key] by
            simp [Ops.mul,flatten_ac,T.invFactor,atomZ,key]]
        rw [← replace]; exact perm
      exact blocked _ _ sub _ (T.roots.inside w z wsort zsort)

/-- Every non-unit normal exponent satisfies the signed-product conditions.
This direction only needs presence of the simplifying equations, so holds
even with additional active rules. -/
theorem clean_of_normal [DecidableEq s.ACSym] {a : Ops s} {R : Root s}
    (T : Presentation a R) {e : Term s} (typed : HasSort e .msg) (normal : Normal R e)
    (nonunit : ¬EquivB e a.one) : Clean a (Cancellation.flatten a.mult e) :=
  clean_of_blocked T typed (fun _ _ sub out =>
    ((subgroup_normal_iff a.mult e).mp normal).2 _ out rfl sub) nonunit

/-- A fresh factor with no counterpart inside an inverse leaves the signed
product irreducible. Distinct variable names alone would not imply this
absence in a concrete normalized instance. -/
theorem Clean.extend [DecidableEq s.ACSym] {a : Ops s} {e r : Term s}
    (c : Clean a (Cancellation.flatten a.mult e)) (atom : Cancellation.flatten a.mult r = [classOf r])
    (unit : ¬EquivB r a.one) (inv : ∀ n, ¬EquivB r (a.inv n))
    (clear : ¬ Opposite a e r) : Clean a (Cancellation.flatten a.mult (a.mul e r)) := by
  classical
  let xs := Cancellation.flatten a.mult e
  let k := classOf r
  have ne (n) : classOf (a.inv n) ≠ k := fun eq => inv n (Quotient.exact eq).symm
  change Clean a (Cancellation.flatten a.mult (.ac a.mult e r))
  rw [flatten_ac,atom]
  change Clean a (xs ++ [k])
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    · exact c.noUnit h
    · exact unit (Quotient.exact (List.mem_singleton.mp h)).symm
  · intro n m rest perm
    have p := ((List.perm_append_comm (l₁ := [k]) (l₂ := xs)).trans perm).erase k
    have hn : ¬ (classOf (a.inv n) == k) = true := fun eq => ne n (of_decide_eq_true eq)
    have hm : ¬ (classOf (a.inv m) == k) = true := fun eq => ne m (of_decide_eq_true eq)
    exact c.oneInverse n m (rest.erase k) (by simpa [List.erase_cons,hn,hm] using p)
  · intro n hinv u hu matched
    have original : classOf (a.inv n) ∈ xs := (List.mem_append.mp hinv).resolve_right
      (fun h => ne n (List.mem_singleton.mp h))
    rcases List.mem_append.mp matched with old | new
    · exact c.disjoint n original u hu old
    · obtain rfl := List.mem_singleton.mp new
      change classOf (a.inv n) ∈ Cancellation.flatten a.mult e at original
      rw [classes] at original hu
      obtain ⟨neg,hm,h⟩ := List.mem_map.mp original
      obtain ⟨factor,hk,eq⟩ := List.mem_map.mp hu
      exact clear ⟨neg,hm,n,Quotient.exact h,factor,hk,Quotient.exact eq⟩

end Tamarin.Rewriting.DHProduct
