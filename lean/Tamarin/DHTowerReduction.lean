import Tamarin.DHTower

/-! Replay a cancellation mask using the active Tamarin rewrite equations.
Every selected occurrence is grouped into one nonempty term before firing
the shared cancellation root. Extra factors need no syntactic restrictions
for the reduction to hold. -/
namespace Tamarin.Rewriting.DHTower
open DHPeer Cancellation ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s}

def sorted (x : Option (Term sig)) : Prop := ∀ u, x = some u → HasSort u .msg

theorem packed_sorted {ts : List (Term sig)} (hs : ∀ t ∈ ts, HasSort t .msg) :
    sorted (packed s ts) := by
  intro t ht
  cases ts with
  | nil => cases ht
  | cons a as =>
    cases ht
    exact s.mulSort ▸ ACRepresentation.fold_hasSort _ _ _ (s.mulSort ▸ hs a List.mem_cons_self)
      (fun u hu => s.mulSort ▸ hs u (List.mem_cons_of_mem _ hu))

theorem packed_factors_normal {E : ExtraTable T} (mul : MulBucket E) {ts : List (Term sig)} {prod}
    (pack : packed s ts = some prod) (factors : ∀ x ∈ ts, Factor s x)
    (norm : ∀ x ∈ ts, Normal (ruleRoot T.rules) x) :
    Normal (ruleRoot T.rules) prod ∧ head prod ≠ .free s.one := by
  classical
  have bag := bag_factors s ts factors
  rw [pack] at bag
  change Cancellation.flatten s.mul prod = ts.map classOf at bag
  have absent (u : Term sig) (no : ∀ t ∈ ts, ¬ EquivB t u) : classOf u ∉ ts.map classOf := by
    rintro mem
    obtain ⟨a,h,eq⟩ := List.mem_map.mp mem
    exact no a h (Quotient.exact eq)
  have noInv (u) := absent (s.product.inv u) (fun a h eq => (factors a h).nonInv eq.head_eq)
  have noUnit := absent s.product.one (fun a h eq => (factors a h).nonUnit eq.head_eq)
  have clean : DHProduct.Clean s.product (Cancellation.flatten s.mul prod) := by
    rw [bag]
    exact ⟨noUnit,fun n _ _ perm => noInv n (perm.mem_iff.mpr List.mem_cons_self),
      fun n h => False.elim (noInv n h)⟩
  constructor
  · apply clean.normal E.presentation.unitFactor E.presentation.invFactor _ mul.inventory
    intro child hc
    have mem : classOf child ∈ Cancellation.flatten s.mul prod := by
      rw [DHProduct.classes]; exact List.mem_map_of_mem hc
    obtain ⟨x,h,eq⟩ := List.mem_map.mp (bag ▸ mem)
    exact (normal_equiv _ (Quotient.exact eq)).mp (norm x h)
  · intro unit
    obtain rfl : prod = s.product.one := nullary s.oneArity unit
    exact noUnit (bag ▸ List.mem_cons_self)

private theorem powCongr {a b c d : Term sig} (ha : EquivB a b) (hc : EquivB c d) :
    EquivB (s.power a c) (s.power b d) := by apply EquivB.free; intro i; split <;> assumption

private theorem powRed {a b c d : Term sig} (ha : Reduces (ruleRoot T.rules) a b)
    (hc : Reduces (ruleRoot T.rules) c d) : Reduces (ruleRoot T.rules) (s.power a c) (s.power b d) := by
  apply Reduces.free; intro i; split <;> assumption

private theorem triple {a b c : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) (hc : HasSort c .msg) :
    ∀ i : Fin 3, HasSort (if i = 0 then a else if i = 1 then b else c) .msg := by
  intro i; split <;> first | assumption | split <;> assumption

private theorem tower_rule {a b c : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) (hc : HasSort c .msg) :
    Reduces (ruleRoot T.rules) (s.power (s.power a b) c) (s.power a (s.product.mul b c)) :=
  T.fire .tower _ (triple ha hb hc)

private theorem mul_sorted {a b : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) :
    HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ ha) (s.mulSort ▸ hb)

private theorem inv_sorted {a : Term sig} (ha : HasSort a .msg) : HasSort (s.product.inv a) .msg := by
  rw [← s.invSort]; apply HasSort.free; intro i; simpa [s.invInput] using ha

/-- One replay of the selected, nonempty cancellation group. The positive
and negative extras are normalized witnesses in a concrete classification,
but arbitrary well-sorted Msg terms already suffice for reachability. -/
theorem cancel_selected (E : ExtraTable T) (pos neg : Option (Term sig)) {r : Term sig}
    (hp : sorted pos) (hn : sorted neg) (hr : HasSort r .msg) :
    Reduces (ruleRoot T.rules)
      (s.product.mul (Balance.assemble s pos (append s (some r) neg)) r)
      (Balance.assemble s pos neg) := by
  have laws := E.presentation.roots.laws
  cases pos with
  | none => cases neg with
    | none => exact laws.cancel r hr
    | some n =>
      exact (Reduces.basis (.ac_congr _ (E.presentation.invCongr (.ac_swap _ r n)) (.refl _))).trans
        (laws.cancelInside n r (hn n rfl) hr)
  | some p => cases neg with
    | none => exact laws.cancelWith p r (hp p rfl) hr
    | some n =>
      exact (Reduces.basis (.ac_congr _ (.ac_congr _ (.refl _) (E.presentation.invCongr (.ac_swap _ r n)))
        (.refl _))).trans (laws.cancelBoth p n r (hp p rfl) (hn n rfl) hr)

/-- Firing the selected cancellation leaves every untaken occurrence available,
even when several occurrences later instantiate to the same term. -/
theorem cancel_and_append (E : ExtraTable T) (pos neg rest : Option (Term sig)) {r : Term sig}
    (hp : sorted pos) (hn : sorted neg) (hr : HasSort r .msg) (hs : sorted rest) :
    let total := (append s (some r) rest).getD r
    Reduces (ruleRoot T.rules)
      (s.product.mul (Balance.assemble s pos (append s (some r) neg)) total)
      (Balance.assemble s (append s pos rest) neg) := by
  have cancels := cancel_selected E pos neg hp hn hr
  cases rest with
  | none =>
    cases pos <;> exact cancels
  | some a =>
    refine (Reduces.basis (EquivB.ac_assoc s.mul _ r a).symm).trans
      ((Reduces.ac s.mul cancels (.basis (.refl a))).trans ?_)
    cases pos with
    | none => cases neg with
      | none => exact .step ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule a (hs a rfl)),.refl _⟩
      | some n => exact .basis (.ac_swap ..)
    | some p => cases neg with
      | none => exact .basis (.refl _)
      | some n =>
        exact .basis ((EquivB.ac_assoc _ _ _ _).trans ((EquivB.ac_congr _ (.refl _) (.ac_swap ..)).trans
          (EquivB.ac_assoc _ _ _ _).symm))

/-- If the reduced exponent is the unit the power contracts to its base. -/
def powerResult (s : Symbols sig) (b : Term sig) (pos neg : Option (Term sig)) : Term sig :=
  match pos,neg with
  | none,none => b
  | _,_ => s.power b (Balance.assemble s pos neg)

theorem replay_mask (E : ExtraTable T) {b added : Term sig} (ts : List (Term sig)) (m : List Bool)
    (pos neg : Option (Term sig)) (pack : packed s ts = some added) (width : m.length = ts.length)
    {r : Term sig} (take : packed s (select m ts) = some r) (factor : ∀ t ∈ ts, Factor s t)
    (types : ∀ t ∈ ts, HasSort t .msg) (hp : sorted pos) (hn : sorted neg) (hb : HasSort b .msg) :
    let rest := packed s (remaining m ts)
    let e := Balance.assemble s pos (append s (some r) neg)
    Reduces (ruleRoot T.rules) (s.power (s.power b e) added)
      (powerResult s b (append s pos rest) neg) := by
  let rest := packed s (remaining m ts)
  let e := Balance.assemble s pos (append s (some r) neg)
  have hr := packed_sorted (s := s) (fun t hm => types t (select_mem hm)) r take
  have ha := packed_sorted types added pack
  have hRest : sorted rest := packed_sorted (fun t hm => types t (select_mem hm))
  have rbag := bag_factors s (select m ts) (fun t hm => factor t (select_mem hm))
  have restBag : Balance.bag s rest = (remaining m ts).map classOf := bag_factors _ _ (fun t hm => factor t (select_mem hm))
  have allBag := bag_factors s ts factor
  rw [take] at rbag
  rw [pack] at allBag
  have total := (select_perm width).map classOf
  rw [List.map_append,← rbag,← restBag,← bag_append] at total
  let full := (append s (some r) rest).getD r
  have grouped : EquivB added full := by
    apply Cancellation.equiv_of_flatten_perm s.mul
    refine (allBag ▸ total : (Balance.bag s (some added)).Perm (Balance.bag s (append s (some r) rest))) |>.trans ?_
    dsimp only [full]; cases rest <;> exact .refl _
  have he : HasSort e .msg := by
    cases pos with
    | none => cases neg with
      | none => exact inv_sorted hr
      | some n => exact inv_sorted (mul_sorted hr (hn n rfl))
    | some p => cases neg with
      | none => exact mul_sorted (hp p rfl) (inv_sorted hr)
      | some n => exact mul_sorted (hp p rfl) (inv_sorted (mul_sorted hr (hn n rfl)))
  refine (tower_rule hb he ha).trans ((powRed (.basis (.refl b))
    ((Reduces.basis (.ac_congr _ (.refl _) grouped)).trans (cancel_and_append E pos neg rest hp hn hr hRest))).trans ?_)
  cases append s pos rest with
  | some p => cases neg <;> exact .basis (.refl _)
  | none => cases neg with
    | none => exact T.fire .expOne _ (triple hb hb hb)
    | some n => exact .basis (.refl _)

end Tamarin.Rewriting.DHTower
