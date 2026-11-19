import Tamarin.DHProduct

/-! Binary views of an ordinary AC subject. Each operand occurrence goes to
one side. A view keeps both sides nonempty, including at the kind level. -/
namespace Tamarin.ACSplits
open ACRepresentation
variable {s : Signature}

private def partitions {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
    let tail := partitions xs
    tail.map (fun (l, r) => (x :: l, r)) ++ tail.map (fun (l, r) => (l, x :: r))

private theorem partitions_sound {α : Type} (xs : List α) {l r}
    (h : (l, r) ∈ partitions xs) : xs.Perm (l ++ r) := by
  induction xs generalizing l r with
  | nil =>
    obtain ⟨rfl,rfl⟩ : l = [] ∧ r = [] := by simpa [partitions] using h
    exact .nil
  | cons x xs ih =>
    rcases List.mem_append.mp h with hl | hr
    · obtain ⟨⟨a,b⟩, hm, eq⟩ := List.mem_map.mp hl
      cases eq
      exact (ih hm).cons x
    · obtain ⟨⟨a,b⟩, hm, eq⟩ := List.mem_map.mp hr
      cases eq
      exact List.perm_cons_append_cons x (ih hm)

private theorem partitions_cover {α β : Type} (key : α → β) (xs : List α) {l r : List β}
    (h : (xs.map key).Perm (l ++ r)) :
    ∃ a b, (a,b) ∈ partitions xs ∧ (a.map key).Perm l ∧ (b.map key).Perm r := by
  classical
  induction xs generalizing l r with
  | nil =>
    have e := h.symm.eq_nil
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp e
    exact ⟨[],[],by simp [partitions],.nil,.nil⟩
  | cons x xs ih =>
    rcases List.mem_append.mp (h.mem_iff.mp List.mem_cons_self) with hl | hr
    · have put := List.perm_cons_erase hl
      have rest := (h.trans (put.append_right r)).cons_inv
      obtain ⟨a,b,hm,ha,hb⟩ := ih rest
      exact ⟨x::a,b,List.mem_append_left _ (List.mem_map.mpr ⟨(a,b),hm,rfl⟩),
        (ha.cons _).trans put.symm,hb⟩
    · have put := List.perm_cons_erase hr
      have move := List.perm_cons_append_cons (key x) (List.Perm.refl (l ++ r.erase (key x)))
      have rest := (h.trans ((put.append_left l).trans move.symm)).cons_inv
      obtain ⟨a,b,hm,ha,hb⟩ := ih rest
      exact ⟨a,x::b,List.mem_append_right _ (List.mem_map.mpr ⟨(a,b),hm,rfl⟩),
        ha,(hb.cons _).trans put.symm⟩

private theorem foldClasses (f : s.ACSym) (xs : List (Term s)) :
    Cancellation.fold f (xs.map Cancellation.classOf) = (decode f xs).map Cancellation.classOf := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, Cancellation.fold, ih]
    cases xs <;> rfl

def splits [DecidableEq s.ACSym] (f : s.ACSym) (t : Term s) : List (Term s × Term s) :=
  (partitions (flatten f t)).filterMap fun (l,r) => do
    return (← decode f l, ← decode f r)

theorem sound [DecidableEq s.ACSym] (f : s.ACSym) (t : Term s) {a b}
    (member : (a,b) ∈ splits f t) : EquivB t (.ac f a b) := by
  obtain ⟨⟨l,r⟩, part, vals⟩ := List.mem_filterMap.mp member
  cases hl : decode f l <;> cases hr : decode f r <;> simp [hl,hr] at vals
  obtain ⟨rfl,rfl⟩ := vals
  obtain ⟨u,hu,eu⟩ := flatten_correct f t
  obtain ⟨v,hv,ev⟩ := decode_append f l r _ _ hl hr
  exact eu.symm.trans ((decode_perm f (partitions_sound _ part) _ _ hu hv).trans ev)

theorem complete [DecidableEq s.ACSym] (f : s.ACSym) {t a b : Term s}
    (eq : EquivB t (.ac f a b)) :
    ∃ l r, (l,r) ∈ splits f t ∧ EquivB a l ∧ EquivB b r := by
  have bags := Cancellation.flatten_equiv f eq
  rw [Rewriting.DHProduct.classes f t, Cancellation.flatten_ac] at bags
  obtain ⟨ls,rs,part,hl,hr⟩ := partitions_cover Cancellation.classOf _ bags
  have side {xs : List (Term s)} {v : Term s}
      (perm : (xs.map Cancellation.classOf).Perm (Cancellation.flatten f v)) :
      ∃ u, decode f xs = some u ∧ EquivB v u := by
    have e := Cancellation.fold_perm f perm
    rw [foldClasses, Cancellation.fold_flatten] at e
    cases h : decode f xs with
    | none => simp [h] at e
    | some u =>
      have same : Cancellation.classOf u = Cancellation.classOf v := by simpa [h] using e
      exact ⟨u,rfl, Quotient.exact same.symm⟩
  obtain ⟨l,dl,el⟩ := side hl
  obtain ⟨r,dr,er⟩ := side hr
  exact ⟨l,r,List.mem_filterMap.mpr ⟨(ls,rs),part,by simp [dl,dr]⟩,el,er⟩

end Tamarin.ACSplits
