import Tamarin.DHTowerCoverage
import Tamarin.DHTowerNormal
import Tamarin.DHTowerPacket

/-! Interpret a row actually returned by the native tower entry point
against both the old received base and the observed normal power value. -/
namespace Tamarin.Rewriting.DHTower.Packet
open DHPeer Cancellation
variable {α : Type} {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem select_sub (m : List Bool) (xs : List α) : (select m xs).Sublist xs := by
  induction m generalizing xs with
  | nil => exact List.nil_sublist _
  | cons b bs ih =>
    cases xs with
    | nil => exact .slnil
    | cons x xs => cases b <;> first | exact (ih xs).cons x | exact (ih xs).cons_cons x

def env (Y base p n : Term sig) (factor : Nat → Term sig) : Arg → Term sig
  | .peer => Y | .base => base | .pos => p | .neg => n | .factor i => factor i

private theorem product_flatten (s : Symbols sig) (e : Arg → Term sig) (t : Image) (js : List Nat) :
    flatten s.mul ((js.foldl (fun a j => Expr.mul a (.var (.factor j))) t).eval s e) =
      flatten s.mul (t.eval s e) ++ js.flatMap (fun j => flatten s.mul (e (.factor j))) := by
  induction js generalizing t with
  | nil => simp
  | cons j js ih => simp [ih,Expr.eval,flatten_ac,List.append_assoc]

private theorem packed_flatten (s : Symbols sig) (a : Term sig) (xs : List (Term sig)) :
    flatten s.mul (ACRepresentation.fold s.mul a xs) = (a::xs).flatMap (flatten s.mul) := by
  induction xs generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b xs ih => simp [ACRepresentation.fold,flatten_ac,ih]

private theorem product_equiv (s : Symbols sig) (e : Arg → Term sig) (i : Nat) (js : List Nat) :
    EquivB ((product i js).eval s e) (ACRepresentation.fold s.mul (e (.factor i)) (js.map (fun j => e (.factor j)))) := by
  apply equiv_of_flatten_perm s.mul
  simp only [product,product_flatten, packed_flatten,List.flatMap_cons,List.flatMap_map]
  exact .refl _

private theorem magnitude (s : Symbols sig) {x y : Term sig} (eq : EquivB x y) (z : Option (Term sig)) :
    let actual := if z.isSome then s.product.mul (z.getD s.product.one) x else x
    EquivB actual ((append s (some y) z).getD s.product.one) := by
  cases z with
  | none => exact eq
  | some z => exact (EquivB.ac_congr s.mul (.refl _) eq).trans (.ac_swap s.mul _ _)

theorem cancel_eval (factor : Nat → Term sig) (Y b : Term sig) (p n : Option (Term sig))
    (i : Nat) (js : List Nat) :
    let e := env Y b (p.getD s.product.one) (n.getD s.product.one) factor
    EquivB (s.power b (Balance.assemble s p (append s (packed s ((i::js).map factor)) n)))
      ((cancel (product i js) p.isSome n.isSome).eval s e) := by
  intro e
  have mag := (magnitude s (product_equiv s e i js) n).symm
  apply EquivB.free
  intro j
  change EquivB (if j.val = 0 then b else _) (if j.val = 0 then b else _)
  split
  · exact .refl _
  · cases p <;> cases n
    all_goals first
      | exact EquivB.free _ _ _ (fun _ => mag)
      | exact EquivB.ac_congr s.mul (.refl _) (EquivB.free _ _ _ (fun _ => mag))

/-- A packet row predicts both observable terms with one assignment to its
witness slots. Cancellation uses the same selected input occurrences in
the old base and the complement in the power value. -/
inductive Predicts (s : Symbols sig) (R : Root sig) (width : Nat) (factor : Nat → Term sig)
    (Y added : Term sig) : Image → Term sig → Prop where
  | unchanged {out} (h : EquivB out (s.power Y added)) : Predicts s R width factor Y added (.var .peer) out
  | neutral {out} (h : EquivB Y s.neutralTerm) (v : EquivB out s.neutralTerm) :
      Predicts s R width factor Y added .neutral out
  | tower {b e out} (h : EquivB Y (s.power b e)) (v : EquivB out (s.power b (s.product.mul e added)))
      (sb : HasSort b .msg) (nb : Normal R b) (se : HasSort e .msg) (ne : Normal R e) :
      Predicts s R width factor Y added (.pow (.var .base) (.var .pos)) out
  | cancelled {t out mask b pos neg i js} (sz : mask.length = width)
      (sel : select mask (List.range width) = i :: js)
      (image : t = cancel (product i js) pos.isSome neg.isSome)
      (sb : HasSort b .msg) (nb : Normal R b) (wp : Witness s R pos) (wn : Witness s R neg)
      (h : EquivB Y (t.eval s (env Y b (pos.getD s.product.one) (neg.getD s.product.one) factor)))
      (v : EquivB out (powerResult s b (append s pos (packed s (remaining mask ((List.range width).map factor)))) neg)) :
      Predicts s R width factor Y added t out

theorem classify_linked {run : Kernel} (ok : Correct run)
    {width : UInt64} {rows} (ran : run width = some rows)
    (inventory : Balance.Inventory E) (pow : PowerBucket T) (mul : MulBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (factor : Nat → Term sig)
    {Y added out : Term sig} (pack : packed s ((List.range width.toNat).map factor) = some added)
    (f : ∀ i < width.toNat, Factor s (factor i)) (n : ∀ i < width.toNat, Normal (ruleRoot T.rules) (factor i))
    (ty : ∀ i < width.toNat, HasSort (factor i) .msg)
    (sy : HasSort Y .msg) (ny : Normal (ruleRoot T.rules) Y)
    (nf : NormalForm (ruleRoot T.rules) (s.power Y added) out) :
    ∃ row ∈ rows, ∃ t, decode row = some t ∧ Predicts s (ruleRoot T.rules) width.toNat factor Y added t out := by
  obtain ⟨_,emits⟩ := ok.describes width rows ran
  have any (P : Term sig → Prop) (h : ∀ i < width.toNat, P (factor i)) :
      ∀ t ∈ (List.range width.toNat).map factor, P t := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact h i (List.mem_range.mp hi)
  suffices ∃ t, Allowed width.toNat t ∧ Predicts s (ruleRoot T.rules) width.toNat factor Y added t out by
    obtain ⟨t,ht,p⟩ := this
    obtain ⟨row,hm,hd⟩ := (emits t).mpr ht
    exact ⟨row,hm,t,hd,p⟩
  cases classify_power inventory pow mul unit _ pack (any _ f) (any _ n) (any _ ty) sy ny nf with
  | unchanged h => exact ⟨_,.inl rfl,.unchanged h⟩
  | neutral h v => exact ⟨_,.inr (.inl rfl),.neutral h v⟩
  | tower b e sb nb se ne h v => exact ⟨_,.inr (.inr (.inl rfl)),.tower h v sb nb se ne⟩
  | cancel m widthM b r take p z sb nb wp wn base value =>
    rw [select_map] at take
    cases sel : select m (List.range width.toNat) with
    | nil => rw [sel] at take; contradiction
    | cons i js =>
      rw [sel] at take
      have sub := select_sub m (List.range width.toNat)
      rw [sel] at sub
      refine ⟨_,.inr (.inr (.inr ⟨i,js,sub,p.isSome,z.isSome,rfl⟩)),.cancelled (by simpa using widthM) sel rfl sb nb wp wn ?_ value⟩
      have eq := cancel_eval (s := s) factor Y b p z i js
      rw [take] at eq
      exact base.trans eq

/-- The caller can supply a nested tower with products in any exponent.
This obligation is for every normal result under the live theory, independently
of normalization strategy and traversal order. -/
def Semantic (run : Kernel) : Prop :=
  ∀ {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T} {width : UInt64}
    {rows} (_ : run width = some rows)
    (_ : Balance.Inventory E) (_ : PowerBucket T) (_ : MulBucket E) (_ : InverseBucket E)
    (_ : Normal (ruleRoot T.rules) s.product.one) (factor : Nat → Term sig)
    (Y first firstGroup : Term sig) (tail groups : List (Term sig))
    (_ : (List.range width.toNat).map factor = first :: tail)
    (_ : ∀ r ∈ first :: tail, HasSort r .msg ∧ Normal (ruleRoot T.rules) r ∧ Factor s r)
    (_ : ∀ g ∈ firstGroup :: groups, ∃ part, packed s part = some g ∧ ∀ r ∈ part, r ∈ first :: tail)
    (_ : (flatten s.mul (ACRepresentation.fold s.mul firstGroup groups)).Perm
      (flatten s.mul (ACRepresentation.fold s.mul first tail)))
    (_ : HasSort Y .msg) (_ : Normal (ruleRoot T.rules) Y) (out : Term sig)
    (_ : NormalForm (ruleRoot T.rules) (Spine.tower s Y firstGroup groups) out),
    ∃ row ∈ rows, ∃ t, decode row = some t ∧
      Predicts s (ruleRoot T.rules) width.toNat factor Y (ACRepresentation.fold s.mul first tail) t out

theorem semantic {run : Kernel} (ok : Correct run) : Semantic run := by
  intro sig s T E width rows ran inventory pow mul inv unit f Y first fg tail groups flat facts grouping layout sy ny out nf
  have flatNF := (grouped_tower_iff inventory pow mul inv unit Y fg first groups tail sy ny facts grouping layout out).mp nf
  have each (i) (hi : i < width.toNat) := facts (f i) (flat ▸ List.mem_map_of_mem (f := f) (List.mem_range.mpr hi))
  apply classify_linked ok ran inventory pow mul unit f (Y := Y)
    (by rw [flat]; rfl) (fun i hi => (each i hi).2.2) (fun i hi => (each i hi).2.1)
    (fun i hi => (each i hi).1) sy ny flatNF

end Tamarin.Rewriting.DHTower.Packet
