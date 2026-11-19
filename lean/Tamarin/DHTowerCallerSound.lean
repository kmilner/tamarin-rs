import Tamarin.DHTowerCallerDefs

/-! Construct the symbolic caller variants for the tower packets. -/
namespace Tamarin.Rewriting.DHTower.Caller
open DHPeer
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem lift_symbolic {peer : Variable} (peersort : peer.sort = .msg)
    (first : Term sig) (rest : List (Term sig)) (ty : ∀ t ∈ first :: rest, HasSort t .msg)
    (outside : ∀ t ∈ first :: rest, ¬t.Occurs peer)
    (a : Tuple.Template sig peer)
    (flat : SoundImage s (ruleRoot T.rules) (ACRepresentation.fold s.mul first rest) a.base a.value) :
    Normal (ruleRoot T.rules) a.base ∧
      NormalForm (ruleRoot T.rules) (a.subst.apply (Spine.tower s (.var peer) first rest)) a.value := by
  have same (t) (ht : t ∈ first :: rest) : a.subst.apply t = t :=
    Substitution.binding_apply_of_not_occurs peer a.base t a.typed (outside t ht)
  have unchanged : rest.map a.subst.apply = rest := List.map_congr_left (fun t h => same t (List.mem_cons_of_mem _ h)) |>.trans rest.map_id
  rw [Tuple.apply_tower,same first List.mem_cons_self,unchanged]
  change Normal _ a.base ∧ NormalForm _ (Spine.tower s (a.subst.image peer) first rest) a.value
  rw [show a.subst.image peer = a.base from Substitution.binding_image_self ..]
  exact ⟨flat.1,Spine.from_flat rest (peersort ▸ a.typed) (ty _ List.mem_cons_self) (fun t h => ty t (List.mem_cons_of_mem _ h)) flat.2⟩

private theorem parameterSorted (q : Query sig) (i : Slot) (used : Bool) : sorted (parameter sig used (q.var i)) := by
  cases used with
  | false => simp [parameter,sorted]
  | true => intro t h; cases h; exact q.typed i

private theorem appendSorted {a b : Option (Term sig)} (ha : sorted a) (hb : sorted b) :
    sorted (append s a b) := by
  cases a with
  | none => cases b <;> exact hb
  | some a => cases b with
    | none => exact ha
    | some b => intro t h; cases h; exact s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ ha _ rfl) (s.mulSort ▸ hb _ rfl)

theorem Recipe.baseTyped (q : Query sig) (s : Symbols sig) (r : Recipe) :
    HasSort (r.base q s) (q.var .peer).sort := by
  rw [q.sorted .peer]; change HasSort _ .msg
  cases r with
  | unchanged => exact q.typed _
  | neutral => rw [← s.neutralSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.neutralArity ▸ i)
  | tower => exact powerSorted (q.typed _) (q.typed _)
  | cancel m p n =>
    exact powerSorted (q.typed .base) (signedSorted (parameterSorted q .pos p)
      (appendSorted (packed_sorted (fun t hm => q.sortedFactors t (select_mem hm))) (parameterSorted q .neg n)))

def template (q : Query sig) (s : Symbols sig) (r : Recipe) (_ : r.Valid q.fs.length) :
    Tuple.Template sig (q.var .peer) :=
  ⟨r.base q s,r.baseTyped q s,r.value q s⟩

theorem symbolic (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (neutral : Normal (ruleRoot T.rules) s.neutralTerm)
    (q : Query sig) (normal : ∀ t ∈ q.fs, Normal (ruleRoot T.rules) t) (factor : ∀ t ∈ q.fs, Factor s t)
    (r : Recipe) (valid : r.Valid q.fs.length) :
    let a := template q s r valid
    Normal (ruleRoot T.rules) a.base ∧ NormalForm (ruleRoot T.rules) (a.subst.apply (q.op s)) a.value := by
  apply lift_symbolic (q.sorted .peer) q.first q.rest q.sortedFactors q.independent
  have initial := fresh_prefix pow mul neutral q.fs (show packed s q.fs = some (q.added s) from rfl)
    q.sortedFactors normal factor (q.var .peer) (q.var .base) (q.var .pos) (q.typed .peer) (q.typed .base) (q.typed .pos)
  cases r with
  | unchanged => exact initial.1
  | neutral => exact initial.2.1
  | tower => exact initial.2.2
  | cancel m p n =>
    have chosen : select m q.fs ≠ [] := by
      intro h
      have eq := select_map q.factor m (List.range q.fs.length)
      rw [q.factorList,h] at eq
      exact valid.2 (List.map_eq_nil_iff.mp eq.symm)
    obtain ⟨u,take⟩ : ∃ u, packed s (select m q.fs) = some u := by
      cases ht : select m q.fs with
      | nil => exact False.elim (chosen ht)
      | cons x xs => exact ⟨_,rfl⟩
    have apart (t) (ht : t ∈ q.fs) (k : Slot) (w : q.witness (q.var k)) : ¬EquivB t (q.symbolic k) := by
      intro e
      have occ : t.Occurs (q.var k) := by cases t <;> cases e.head_eq; rfl
      exact q.disjoint t ht _ occ w
    have h := fresh_cancel pow mul inv unit q.fs m (q.var .base) (q.var .pos) (q.var .neg) p n
      (q.typed .base) (q.typed .pos) (q.typed .neg)
      (fun h => by have e := q.distinct _ _ h; cases e)
      (fun t ht => ⟨apart t ht .pos (.inr (.inl rfl)),apart t ht .neg (.inr (.inr rfl))⟩)
      q.sortedFactors normal factor valid.1 (show packed s q.fs = some (q.added s) from rfl) take
    change SoundImage s _ _ (Recipe.base q s (.cancel m p n)) (Recipe.value q s (.cancel m p n))
    simpa only [SoundImage,Recipe.base,Recipe.value,take,Names.symbolic] using h

end Tamarin.Rewriting.DHTower.Caller
