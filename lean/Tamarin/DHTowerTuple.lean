import Tamarin.DHTowerFlatten
import Tamarin.VariantJoinPacked

/-! Lift a family of single-peer images and symbolic operation values to a
complete caller tuple. Specializing an arm changes only its private witnesses.
All the other observed variables share a single original assignment. -/
namespace Tamarin.Rewriting.DHTower.Tuple
open VariantJoin
variable {sig : Signature}

/-- Only the peer can be specialized in the substitution domain. A base
image may itself refer to several caller variables and several witnesses. -/
structure Template (sig : Signature) (peer : Variable) where
  base : Term sig
  typed : HasSort base peer.sort
  value : Term sig

def Template.subst {peer : Variable} (t : Template sig peer) : Substitution sig :=
  .binding peer t.base t.typed

def Template.row {peer : Variable} (keys : List Variable) (t : Template sig peer) : Row sig (Key keys) Unit :=
  ⟨fun i => t.subst.image i.val,fun _ => t.value⟩

theorem Template.normalized {R : Root sig} {peer : Variable} (t : Template sig peer)
    (vars : Normalized R Substitution.identity) (base : Normal R t.base) : Normalized R t.subst := by
  intro v; change Normal R (if v = peer then _ else _)
  split <;> first | exact base | exact vars v

/-- For a concrete caller assignment, replace exactly the arm-private names
with the classifier's witnesses. The classifier only has to explain the base
and the single result, irrespective of how many other slots the caller uses. -/
def Factors {R : Root sig} {peer : Variable} (templates : List (Template sig peer))
    (privateName : Variable → Prop) (op : Term sig) : Prop :=
  ∀ (ρ : Substitution sig), Normalized R ρ → ∀ out, NormalForm R (ρ.apply op) out →
    ∃ t ∈ templates, ∃ w : Substitution sig, (∀ v, privateName v → Normal R (w.image v)) ∧
      let δ := choose privateName w ρ
      EquivB (ρ.image peer) (δ.apply t.base) ∧ EquivB out (δ.apply t.value)

private theorem exact_rows {rules : List (Equation sig)} {peer : Variable} {keys : List Variable}
    (ts : List (Template sig peer)) (privateName : Variable → Prop)
    (apart : ∀ v ∈ keys, ¬privateName v) (op : Term sig) (typed : HasSort op op.rootSort)
    (includes : ∀ v, op.Occurs v → v ∈ keys)
    (symbolic : ∀ t ∈ ts, NormalForm (ruleRoot rules) (t.subst.apply op) t.value)
    (classify : Factors (R := ruleRoot rules) ts privateName op) :
    Exact (ruleRoot rules) Subtype.val (fun _ : Unit => op) (ts.map (Template.row keys)) := by
  classical
  intro ρ hn values ny
  constructor
  · intro actual
    obtain ⟨t,ht,w,nw,base,out⟩ := classify ρ hn _ (actual ())
    let δ := choose privateName w ρ
    have normal : Normalized (ruleRoot rules) δ := by
      intro v; change Normal _ (if privateName v then _ else _)
      split <;> first | exact nw _ (by assumption) | exact hn v
    refine ⟨_,List.mem_map_of_mem (f := Template.row keys) ht,δ,normal,?_,?_⟩
    · intro i; by_cases key : i.val = peer
      · simpa [Template.row,Template.subst,Substitution.binding,key,δ] using base
      · change EquivB (ρ.image i.val) (δ.apply (t.subst.image i.val))
        simp [Template.subst,Substitution.binding,key,Substitution.apply,Term.subst,δ,choose,apart _ i.property,EquivB.refl]
    · intro a; cases a; exact out
  · rintro ⟨_,hr,δ,_,fits⟩ a
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
    cases a
    apply form_of_instance hn typed (δ := δ) (σ := t.subst) _ (symbolic t ht) (fits.values ()) (ny ())
    intro v h
    exact fits.inputs ⟨v,includes v h⟩

private theorem apply_power (s : DHPeer.Symbols sig) (ρ : Substitution sig) (b e : Term sig) :
    ρ.apply (s.power b e) = s.power (ρ.apply b) (ρ.apply e) := by
  apply congrArg (Term.free s.pow); funext i
  change ρ.apply (if _ then _ else _) = (if _ then _ else _)
  split <;> rfl

theorem apply_tower (s : DHPeer.Symbols sig) (ρ : Substitution sig)
    (b e : Term sig) (rest : List (Term sig)) :
    ρ.apply (Spine.tower s b e rest) = Spine.tower s (ρ.apply b) (ρ.apply e) (rest.map ρ.apply) := by
  induction rest generalizing b e with
  | nil => exact apply_power s ρ b e
  | cons r rs ih =>
    change ρ.apply (Spine.tower s (s.power b e) r rs) = _
    rw [ih,apply_power]; rfl

/-- Discharge the tuple's uniqueness premise directly for the input tower,
including arbitrary normalized caller assignments. Stability of the exponent
observations suffices here. Their positive-factor shape is used by the local
branch classifier, independently of this reconstruction argument. -/
theorem unique_instances {s : DHPeer.Symbols sig} {T : DHPeer.Table s} {E : DHPeer.ExtraTable T}
    (pow : DHPeer.PowerBucket T) (inv : DHPeer.Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    (peer : Variable) (sort : peer.sort = .msg) (first : Term sig) (rest : List (Term sig))
    (types : ∀ t ∈ first :: rest, HasSort t .msg)
    (stable : ∀ t ∈ first :: rest, StableVariants.Stable (ruleRoot T.rules) t)
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) (u v : Term sig) :
    NormalForm (ruleRoot T.rules) (ρ.apply (Spine.tower s (.var peer) first rest)) u →
    NormalForm (ruleRoot T.rules) (ρ.apply (Spine.tower s (.var peer) first rest)) v → EquivB u v := by
  rw [apply_tower]
  apply Spine.unique pow inv unit
  · rw [← apply_tower]
    apply HasSort.subst _ ρ.image ρ.sorted
    exact (Spine.tower_typed s rest (sort ▸ HasSort.var peer) (types first List.mem_cons_self)
      (fun t h => types t (List.mem_cons_of_mem _ h))).1
  · exact Spine.defined_tower s _ _ (hn _) (stable _ List.mem_cons_self ρ hn)
      (fun t h => by obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h; exact stable x (List.mem_cons_of_mem _ hx) ρ hn)

/-- Any complete enumeration of the single-power templates can be reordered,
opened in one fresh range per row, and packed back into the original tuple
of repeated powers and uniformly represented observations. These conditions
also permit deduplication modulo a simultaneous sort-preserving renaming. -/
theorem complete {rules : List (Equation sig)} {peer : Variable} {keys : List Variable}
    (ts : List (Template sig peer)) (privateName : Variable → Prop)
    (apart : ∀ v ∈ keys, ¬privateName v) (op : Term sig) (typed : HasSort op op.rootSort)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (symbolic : ∀ t ∈ ts, Normal (ruleRoot rules) t.base ∧
      NormalForm (ruleRoot rules) (t.subst.apply op) t.value)
    (classify : Factors (R := ruleRoot rules) ts privateName op)
    (unique : ∀ (ρ : Substitution sig), Normalized (ruleRoot rules) ρ → ∀ u v,
      NormalForm (ruleRoot rules) (ρ.apply op) u → NormalForm (ruleRoot rules) (ρ.apply op) v → EquivB u v)
    (rows : List (Row sig (Key keys) Unit))
    (allRows : ∀ t ∈ ts, ∃ r ∈ rows, (t.row keys).Relabels r)
    (onlyRows : ∀ r ∈ rows, ∃ t ∈ ts, (t.row keys).Relabels r)
    (slots : List (Sum Unit (Term sig))) (used : Sum.inl () ∈ slots)
    (representative : Term sig → Term sig)
    (uniform : ∀ t, .inr t ∈ slots → StableVariants.Representative (ruleRoot rules) t (representative t))
    (scope : ∀ v, v ∈ keys ↔ Observed (slots.map (packedInput (fun _ : Unit => op))) v)
    (avoid : List Variable) (fresh : ∀ r ∈ rows, ∀ v, r.Uses v → v ∉ keys ++ avoid) :
    ∃ typedRows : ∀ r ∈ rows, r.Sorted,
      let q := slots.map (packedInput (fun _ : Unit => op))
      let answers := packRows rows typedRows slots representative
      CompleteVariants (ruleRoot rules) q answers ∧ ∀ a ∈ answers,
        a.Reconstructible (ruleRoot rules) q ∧ a.Safe q avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  let operation (_ : Unit) := op
  have includes (v) (h : op.Occurs v) := (scope v).mpr ⟨_,List.mem_map_of_mem (f := packedInput operation) used,h⟩
  have localRows := exact_rows ts privateName apart op typed includes (fun t m => (symbolic t m).2) classify
  have rel := localRows.relabel (out := rows)
    (fun _ hm => by obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm; exact allRows t ht)
    (fun r hm => by obtain ⟨t,ht,relabel⟩ := onlyRows r hm; exact ⟨_,List.mem_map_of_mem ht,relabel⟩)
  have sorted (r) (hm : r ∈ rows) : r.Sorted := by
    obtain ⟨t,_,relabel⟩ := onlyRows r hm
    exact relabel.sorted (fun i => t.subst.sorted i.val)
  have normal (r) (hm : r ∈ rows) : r.IsNormal (ruleRoot rules) := by
    obtain ⟨t,ht,relabel⟩ := onlyRows r hm
    exact relabel.normal.mp ⟨fun i => t.normalized vars (symbolic t ht).1 i.val,
      fun _ => (symbolic t ht).2.2.1⟩
  obtain ⟨hc,hr⟩ := rel.packedRepresentatives vars sorted normal slots (fun _ => used) (fun v => (scope v).mpr)
    representative uniform (fun ρ h _ => unique ρ h)
  refine ⟨sorted,hc,fun a m => ⟨hr _ m,?_⟩⟩
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp m
  exact row.val.packedRepresentative_safe (sorted _ row.property) operation slots avoid representative
    (fun t h => (uniform t h).variables) scope (fresh _ row.property)

end Tamarin.Rewriting.DHTower.Tuple
