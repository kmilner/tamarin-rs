import Tamarin.DHProductUnique

/-! A positive exponent product may cancel any submultiset of negative factors in
a received power. The mask ranges over occurrences, so two exponent positions
may be equal after substitution without losing multiplicity. -/
namespace Tamarin.Rewriting.DHTower
open DHPeer Cancellation
variable {α β : Type} {sig : Signature}

/-- Select occurrences in order. Complete branch packets use an exact-length mask. -/
def select : List Bool → List α → List α
  | b :: bs, x :: xs => if b then x :: select bs xs else select bs xs
  | _, _ => []

def remaining (mask : List Bool) (xs : List α) := select (mask.map Bool.not) xs

theorem select_map (f : α → β) (mask : List Bool) (xs : List α) :
    select mask (xs.map f) = (select mask xs).map f := by
  induction mask generalizing xs with
  | nil => rfl
  | cons b bs ih => cases xs <;> cases b <;> simp [select,ih]

theorem select_perm {mask : List Bool} {xs : List α} (width : mask.length = xs.length) :
    xs.Perm (select mask xs ++ remaining mask xs) := by
  induction mask generalizing xs with
  | nil => cases xs <;> simp_all [select,remaining]
  | cons b bs ih =>
    cases xs with
    | nil => simp at width
    | cons x xs =>
      have ihPerm :=  ih (Nat.succ.inj width : bs.length = xs.length)
      cases b with
      | true => simpa [select,remaining] using ihPerm.cons x
      | false =>
        simpa [select,remaining] using (ihPerm.cons x).trans
          (List.perm_middle (a := x) (l₁ := select bs xs) (l₂ := remaining bs xs)).symm

/-- Maximal cancellation in two finite bags, with multiplicities and both remainders. -/
structure Split (xs negative : List α) (mask : List Bool) (left : List α) : Prop where
  width : mask.length = xs.length
  negative_decomposition : negative.Perm (select mask xs ++ left)
  maximal : ∀ x ∈ remaining mask xs, x ∉ left

theorem split_exists [DecidableEq α] (xs neg : List α) :
    ∃ mask left, Split xs neg mask left := by
  induction xs generalizing neg with
  | nil => exact ⟨[],neg,rfl,.refl _,by simp [remaining,select]⟩
  | cons x xs ih =>
    by_cases found : x ∈ neg
    · obtain ⟨m,left,s⟩ := ih (neg.erase x)
      exact ⟨true :: m,left,by simp [s.width],(List.perm_cons_erase found).trans (s.negative_decomposition.cons _),
        by simpa [remaining,select] using s.maximal⟩
    · obtain ⟨m,left,s⟩ := ih neg
      refine ⟨false :: m,left,by simp [s.width],s.negative_decomposition,?_⟩
      intro a h
      rcases List.mem_cons.mp h with rfl|h
      · exact fun present => found (s.negative_decomposition.mem_iff.mpr (List.mem_append_right _ present))
      · exact s.maximal a h

/-- A reduced signed bag is determined by its net counts. -/
private theorem reduced_unique [DecidableEq α] {p n q m : List α}
    (c₁ : ∀ k ∈ n, k ∉ p) (c₂ : ∀ k ∈ m, k ∉ q)
    (balance : ∀ k, (p.count k : Int) - n.count k = (q.count k : Int) - m.count k) :
    p.Perm q ∧ n.Perm m := by
  have counts (k) : p.count k = q.count k ∧ n.count k = m.count k := by
    have exclusive {ns ps : List α} (c : ∀ k ∈ ns, k ∉ ps) : ns.count k = 0 ∨ ps.count k = 0 := by
      by_cases h : k ∈ ns
      · exact .inr (List.count_eq_zero.mpr (c k h))
      · exact .inl (List.count_eq_zero.mpr h)
    have h := balance k
    rcases exclusive c₁ with hn|hp <;> rcases exclusive c₂ with hm|hq <;> omega
  exact ⟨List.perm_iff_count.mpr (fun k => (counts k).1),List.perm_iff_count.mpr (fun k => (counts k).2)⟩

/-- The two independently reduced endpoints determine the surviving positive
and negative factors exactly. The incoming list need not be pairwise distinct. -/
theorem Split.outputs [DecidableEq α] {xs neg left pos outPos outNeg : List α} {mask}
    (split : Split xs neg mask left)
    (before : ∀ k ∈ neg, k ∉ pos) (after : ∀ k ∈ outNeg, k ∉ outPos)
    (balance : ∀ k, (outPos.count k : Int) - outNeg.count k =
      (pos.count k : Int) - neg.count k + xs.count k) :
    outPos.Perm (pos ++ remaining mask xs) ∧ outNeg.Perm left := by
  apply reduced_unique after
  · intro k h included
    rcases List.mem_append.mp included with old|new
    · exact before k (split.negative_decomposition.mem_iff.mpr (List.mem_append_right _ h)) old
    · exact split.maximal k new h
  · intro k
    have hx := (select_perm split.width).count_eq k
    have hn := split.negative_decomposition.count_eq k
    have h := balance k
    simp only [List.count_append] at hx hn ⊢
    omega

/-- Optional multiplication is used only to assemble nonempty term factors.
The unit appears at the end exactly when both positive and negative lists are empty. -/
def append (s : Symbols sig) : Option (Term sig) → Option (Term sig) → Option (Term sig)
  | some a,some b => some (s.product.mul a b)
  | none,b => b
  | a,none => a

theorem bag_append (s : Symbols sig) (a b : Option (Term sig)) :
    Balance.bag s (append s a b) = Balance.bag s a ++ Balance.bag s b := by
  cases a <;> cases b <;> simp [append,Balance.bag,DHProduct.Ops.mul,Symbols.product,Cancellation.flatten_ac]

noncomputable section
open Classical

private theorem bag_rel (s : Symbols sig) {a b : Option (Term sig)}
    (h : (Balance.bag s a).Perm (Balance.bag s b)) : Option.Rel EquivB a b := by
  have nonempty (t : Term sig) : Balance.bag s (some t) ≠ [] := by
    intro he
    have hf := Cancellation.fold_flatten s.mul t
    change Cancellation.flatten s.mul t = [] at he
    rw [he] at hf; cases hf
  cases a with
  | none => cases b with
    | none => exact .none
    | some b => exact False.elim (nonempty b (List.perm_nil.mp h.symm))
  | some a => cases b with
    | none => exact False.elim (nonempty a (List.perm_nil.mp h))
    | some b => exact .some (Cancellation.equiv_of_flatten_perm s.mul h)

theorem assemble_congr (s : Symbols sig) {p n p' n' : Option (Term sig)}
    (hp : (Balance.bag s p).Perm (Balance.bag s p'))
    (hn : (Balance.bag s n).Perm (Balance.bag s n')) :
    EquivB (Balance.assemble s p n) (Balance.assemble s p' n') := by
  cases bag_rel s hp <;> cases bag_rel s hn
  · apply EquivB.ac_congr <;> first | assumption | exact .free _ _ _ (fun _ => by assumption)
  · assumption
  · exact .free _ _ _ (fun _ => by assumption)
  · exact .refl _

def packed (s : Symbols sig) (ts : List (Term sig)) := ACRepresentation.decode s.mul ts

private theorem bag_packed (s : Symbols sig) (ts : List (Term sig)) :
    Balance.bag s (packed s ts) = ts.flatMap (Cancellation.flatten s.mul) := by
  cases ts with
  | nil => rfl
  | cons x xs =>
    change Cancellation.flatten s.mul (ACRepresentation.fold s.mul x xs) = _
    induction xs generalizing x with
    | nil => simp [ACRepresentation.fold]
    | cons y ys ih => simp [ACRepresentation.fold,Cancellation.flatten_ac,ih]

theorem bag_factors (s : Symbols sig) (ts : List (Term sig)) (positive : ∀ t ∈ ts, Factor s t) :
    Balance.bag s (packed s ts) = ts.map classOf := by
  rw [bag_packed]
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.flatMap_cons,(positive t List.mem_cons_self).single,
      ih (fun a h => positive a (List.mem_cons_of_mem _ h))]

theorem select_mem {m : List Bool} {xs : List α} {x : α} (h : x ∈ select m xs) : x ∈ xs := by
  induction m generalizing xs with
  | nil => cases h
  | cons b bs ih =>
    cases xs with
    | nil => cases h
    | cons y ys => cases b with
      | false => exact List.mem_cons_of_mem _ (ih h)
      | true =>
        rcases List.mem_cons.mp h with rfl|later
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih later)

/-- Each present remainder is a legal normalized witness for a Msg parameter. -/
def Witness (s : Symbols sig) (R : Root sig) (o : Option (Term sig)) : Prop :=
  ∀ a, o = some a → HasSort a .msg ∧ Normal R a ∧ ConstructorVariants.head a ≠ .free s.one

private theorem component_witnesses [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s}
    (E : ExtraTable T) {t p n} (ht : HasSort t .msg) (hn : Normal (ruleRoot T.rules) t)
    (rep : Balance.Canonical s (ruleRoot T.rules) t p n) :
    Witness s (ruleRoot T.rules) p ∧ Witness s (ruleRoot T.rules) n := by
  have hs := Term.checkSort_sound _ _ (SortClash.check_equiv rep.value .msg ▸ Term.checkSort_complete ht)
  have norm := (normal_equiv _ rep.value).mp hn
  have nonunit {u : Term sig} (plain : Balance.Plain s (ruleRoot T.rules) u) :
      ConstructorVariants.head u ≠ .free s.one := by
    intro h
    have eq := DHPeer.nullary s.oneArity h
    subst u
    exact (plain _ List.mem_cons_self).2.2 rfl
  have invN {u : Term sig} (h : Normal (ruleRoot T.rules) (s.product.inv u)) :
      Normal (ruleRoot T.rules) u := normal_free_child s.inv _ h
        ⟨0,by rw [s.invArity]; decide⟩
  cases p with
  | none =>
    refine ⟨by simp [Witness],?_⟩
    cases n with
    | none => simp [Witness]
    | some n =>
      intro _ h; cases h
      exact ⟨E.presentation.invChild _ hs,invN norm,nonunit (rep.negative _ rfl)⟩
  | some p => cases n with
    | none => exact ⟨fun _ h => by cases h; exact ⟨hs,norm,nonunit (rep.positive _ rfl)⟩,by simp [Witness]⟩
    | some n =>
      change HasSort (Term.ac s.mul p (s.product.inv n)) .msg at hs
      have hh := Term.checkSort_complete hs
      simp only [Term.checkSort,Bool.and_eq_true,s.mulSort] at hh
      have ns := normal_ac_children _ norm
      exact ⟨fun _ h => by cases h; exact ⟨Term.checkSort_sound _ _ hh.1.2,ns.1,nonunit (rep.positive _ rfl)⟩,
        fun _ h => by cases h; exact ⟨E.presentation.invChild _ (Term.checkSort_sound _ _ hh.2),
          invN ns.2,nonunit (rep.negative _ rfl)⟩⟩

/-- Algebraic meaning of every actually normalized product of an old exponent
and a list of positive factors. It gives the exact input and output term
schemas modulo B, using genuine residual terms from the two normal forms. -/
theorem classify_product {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Balance.Inventory E) (ts : List (Term sig)) {added old out : Term sig}
    (pack : packed s ts = some added) (positive : ∀ t ∈ ts, Factor s t)
    (normalFactors : ∀ t ∈ ts, Normal (ruleRoot T.rules) t)
    (typed : HasSort old .msg) (norm : Normal (ruleRoot T.rules) old)
    (outTyped : HasSort out .msg) (nf : Normal (ruleRoot T.rules) out)
    (path : Reduces (ruleRoot T.rules) (s.product.mul old added) out) :
    ∃ mask pos leftNeg, mask.length = ts.length ∧
      EquivB old (Balance.assemble s pos (append s (packed s (select mask ts)) leftNeg)) ∧
      EquivB out (Balance.assemble s (append s pos (packed s (remaining mask ts))) leftNeg) ∧
      (∀ k ∈ Balance.bag s leftNeg, k ∉ (remaining mask ts).map classOf) ∧
      Witness s (ruleRoot T.rules) pos ∧ Witness s (ruleRoot T.rules) leftNeg := by
  classical
  obtain ⟨pos,neg,oldRep⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) typed norm
  obtain ⟨outP,outN,newRep⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) outTyped nf
  obtain ⟨m,left,part⟩ := split_exists (ts.map classOf) (Balance.bag s neg)
  have each {x : Term sig} (hx : x ∈ ts) (k : Class sig) :
      Balance.read s (ruleRoot T.rules) k x = some ((([classOf x].count k : Nat) : Int)) := by
    have f := positive x hx
    rw [Balance.read_alien s _ k x f.nonMul f.nonInv f.nonUnit]
    by_cases h : classOf x = k <;> simp [Balance.alien,normalFactors x hx,h]
  have addRead (k) : Balance.read s (ruleRoot T.rules) k added = some (((ts.map classOf).count k : Nat) : Int) := by
    cases ts with
    | nil => cases pack
    | cons a as =>
      obtain rfl : added = ACRepresentation.fold s.mul a as := (Option.some.inj pack).symm
      have foldRead (a : Term sig) (as : List (Term sig))
          (facts : ∀ x ∈ a::as, Balance.read s (ruleRoot T.rules) k x = some ((([classOf x].count k : Nat) : Int))) :
          Balance.read s (ruleRoot T.rules) k (ACRepresentation.fold s.mul a as) =
            some ((((a::as).map classOf).count k : Nat) : Int) := by
        induction as generalizing a with
        | nil => exact facts a List.mem_cons_self
        | cons b bs ih =>
          change Balance.read s _ k (s.product.mul a (ACRepresentation.fold s.mul b bs)) = _
          rw [Balance.read_mul,facts a List.mem_cons_self,ih b (fun x hx => facts x (List.mem_cons_of_mem _ hx))]
          apply congrArg some
          change _ + _ = ((([classOf a] ++ (b::bs).map classOf).count k : Nat) : Int)
          rw [List.count_append, Int.natCast_add]
      exact foldRead a as (fun x hx => each hx k)
  have balance (k) := inventory.reduces k path _ (by
    rw [Balance.read_mul,oldRep.read_count,addRead]
    rfl)
  have counts (k) := Option.some.inj ((newRep.read_count k).symm.trans (balance k))
  obtain ⟨pPerm,nPerm⟩ := part.outputs oldRep.disjoint newRep.disjoint counts
  have selected := bag_factors s (select m ts) (fun t h => positive t (select_mem h))
  have rest := bag_factors s (remaining m ts) (fun t h => positive t (select_mem h))
  have hSel := select_map classOf m ts
  have hRest := select_map classOf (m.map Bool.not) ts
  change remaining m (ts.map classOf) = (remaining m ts).map classOf at hRest
  refine ⟨m,pos,outN,by simpa using part.width,oldRep.value.trans (assemble_congr _ (.refl _) ?_),
    newRep.value.trans (assemble_congr _ ?_ (.refl _)),?_,
    (component_witnesses E typed norm oldRep).1,(component_witnesses E outTyped nf newRep).2⟩
  · rw [bag_append,selected,← hSel]
    exact part.negative_decomposition.trans (List.Perm.append_left _ nPerm.symm)
  · rw [bag_append,rest,← hRest]
    exact pPerm
  · intro k hk hm
    exact part.maximal k (hRest ▸ hm) (nPerm.mem_iff.mp hk)

end
end Tamarin.Rewriting.DHTower
