import Tamarin.VariantJoinRenaming
import Tamarin.StableVariants

/-! A joined row has a value for each distinct operation and an image for
each caller variable. Turn those images into a finite substitution and
reinsert values in the original tuple, with arbitrary ordering, repeats,
and additional stable observations. -/
namespace Tamarin.Rewriting.VariantJoin
variable {sig : Signature} {A : Type} {R : Root sig} {keys : List Variable}

abbrev Key (keys : List Variable) := {v : Variable // v ∈ keys}

def Row.Sorted (row : Row sig (Key keys) A) : Prop :=
  ∀ i, HasSort (row.input i) i.val.sort

theorem Row.Sorted.join {B : Type} {l : Row sig (Key keys) A} (hl : l.Sorted)
    (r : Row sig (Key keys) B) (μ : Substitution sig) : (join l r μ).Sorted :=
  fun i => (hl i).subst μ.image μ.sorted

theorem Row.Relabels.sorted {l r : Row sig (Key keys) A} (label : l.Relabels r)
    (sorted : l.Sorted) : r.Sorted := by
  obtain ⟨π,inputs,_⟩ := label
  intro i
  have h := (sorted i).subst (π.subst sig).image (π.subst sig).sorted
  exact Term.checkSort_sound _ _ (SortClash.check_equiv (inputs i) _ ▸ Term.checkSort_complete h)

def Row.project (row : Row sig (Key keys) A) (typed : row.Sorted) : Substitution sig where
  image v := if h : v ∈ keys then row.input ⟨v,h⟩ else .var v
  support := keys
  outside := by intro v absent; simp [absent]
  sorted := by intro v; split; exact typed _; exact .var _

theorem Row.project_key (row : Row sig (Key keys) A) (typed : row.Sorted) (i : Key keys) :
    (row.project typed).image i.val = row.input i := by simp [Row.project,i.property]

theorem Row.project_normal (row : Row sig (Key keys) A) (typed : row.Sorted)
    (vars : Normalized R Substitution.identity) (normal : row.IsNormal R) :
    Normalized R (row.project typed) := by
  intro v
  change Normal R (if h : v ∈ keys then row.input ⟨v,h⟩ else .var v)
  split
  · exact normal.1 _
  · exact vars v

/-- Left slots select a jointly solved operation. Right slots are stable
terms, including separately observed variables and constructor expressions. -/
def packedInput (op : A → Term sig) : Sum A (Term sig) → Term sig := Sum.elim op id

def Row.packedValue (row : Row sig (Key keys) A) (typed : row.Sorted) (normalValue : Term sig → Term sig := id) :
    Sum A (Term sig) → Term sig := Sum.elim row.value ((row.project typed).apply ∘ normalValue)

def Row.pack (row : Row sig (Key keys) A) (typed : row.Sorted) (slots : List (Sum A (Term sig)))
    (normalValue : Term sig → Term sig := id) : Variant sig :=
  ⟨row.project typed,slots.map (row.packedValue typed normalValue)⟩

def packRows (rows : List (Row sig (Key keys) A)) (typed : ∀ row ∈ rows, row.Sorted)
    (slots : List (Sum A (Term sig))) (normalValue : Term sig → Term sig := id) : List (Variant sig) :=
  rows.attach.map fun r => r.val.pack (typed r.val r.property) slots normalValue

private theorem packed_mem {rows : List (Row sig (Key keys) A)} {typed : ∀ row ∈ rows, row.Sorted}
    {slots : List (Sum A (Term sig))} {normalValue : Term sig → Term sig} {answer : Variant sig} :
    answer ∈ packRows rows typed slots normalValue ↔ ∃ r, ∃ hr : r ∈ rows, answer = r.pack (typed r hr) slots normalValue := by
  constructor
  · intro mem; obtain ⟨r,_,rfl⟩ := List.mem_map.mp mem
    exact ⟨r.val,r.property,rfl⟩
  · rintro ⟨r,hr,rfl⟩
    exact List.mem_map_of_mem (f := fun r : {v // v ∈ rows} => r.val.pack (typed _ r.property) slots normalValue)
      (List.mem_attach _ ⟨r,hr⟩)

private theorem alignedAt {α β : Type} {f : α → β → Prop} {xs : List α} {ys : List β}
    (h : Aligned f xs ys) {x} (mem : x ∈ xs) : ∃ y, f x y := by
  induction xs generalizing ys with
  | nil => contradiction
  | cons z zs ih =>
    cases ys with
    | nil => exact False.elim h
    | cons y tail =>
      rcases List.mem_cons.mp mem with rfl | later
      · exact ⟨y,h.1⟩
      · exact ih h.2 later

/-- Recover full packed variants using just the normal outputs that occur
in the query. In particular the bridge does not require a terminating
normalizer. Repeated occurrences may have been normalized independently. -/
theorem Exact.packedRepresentatives {op : A → Term sig} {rows : List (Row sig (Key keys) A)}
    (family : Exact R Subtype.val op rows) (vars : Normalized R Substitution.identity)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (n : Term sig → Term sig) (cert : ∀ t, .inr t ∈ slots → StableVariants.Representative R t (n t))
    (unique : ∀ ρ : Substitution sig, Normalized R ρ → ∀ a u v,
      NormalForm R (ρ.apply (op a)) u → NormalForm R (ρ.apply (op a)) v → EquivB u v) :
    CompleteVariants R (slots.map (packedInput op)) (packRows rows typed slots n) ∧
      ∀ answer ∈ packRows rows typed slots n, answer.Reconstructible R (slots.map (packedInput op)) := by
  have sound (r : Row sig (Key keys) A) (mem : r ∈ rows) :
      (r.pack (typed r mem) slots n).Sound R (slots.map (packedInput op)) := by
    let σ := r.project (typed r mem)
    have norm := r.project_normal (typed r mem) vars (normal r mem)
    have fits : Denotes R r (fun i => σ.image i.val) r.value := by
      refine ⟨.identity,vars,?_,?_⟩
      · intro i; simp only [σ,Row.project_key,Substitution.apply_identity]; exact .refl _
      · intro i; simp only [Substitution.apply_identity]; exact .refl _
    have forms := (family σ norm r.value (normal r mem).2).mpr ⟨r,mem,fits⟩
    refine ⟨norm,aligned_maps slots (packedInput op) (r.packedValue _ n) ?_⟩
    intro slot included
    cases slot with
    | inl a => exact forms a
    | inr t => exact (cert t included).normal σ norm
  constructor
  · constructor
    · intro answer hm
      obtain ⟨r,hr,rfl⟩ := packed_mem.mp hm
      exact sound r hr
    · intro ρ hρ values nfs
      have witness (a : A) : ∃ v, NormalForm R (ρ.apply (op a)) v :=
        alignedAt nfs (List.mem_map_of_mem (f := packedInput op) (used a))
      let value (a : A) := (witness a).choose
      have isForm (a : A) : NormalForm R (ρ.apply (op a)) (value a) := (witness a).choose_spec
      obtain ⟨r,mem,δ,hd,fit⟩ := (family ρ hρ value (fun a => (isForm a).2.1)).mp isForm
      let σ := r.project (typed r mem)
      have agree (v) (obs : Observed (slots.map (packedInput op)) v) :
          EquivB (ρ.image v) (δ.apply (σ.image v)) := by
        let i : Key keys := ⟨v,scope v obs⟩
        rw [show σ.image v = r.input i from r.project_key _ i]
        exact fit.inputs i
      refine ⟨r.pack (typed r mem) slots n,packed_mem.mpr ⟨r,mem,rfl⟩,δ,hd,agree,?_⟩
      apply aligned_values slots (packedInput op) (r.packedValue _ n) values nfs
      intro slot included actual nf
      cases slot with
      | inl a => exact (unique ρ hρ a _ _ nf (isForm a)).trans (fit.values a)
      | inr t =>
        have rep := cert t included
        have same := (n t).subst_equiv ρ.image (δ.compose σ).image (fun v hv =>
          agree v ⟨_,List.mem_map_of_mem (f := packedInput op) included,rep.variables v hv⟩)
        change EquivB (ρ.apply (n t)) ((δ.compose σ).apply (n t)) at same
        rw [Substitution.apply_compose] at same
        exact (rep.unique ρ hρ actual nf).trans same
  · intro answer hm
    obtain ⟨r,mem,rfl⟩ := packed_mem.mp hm
    have hs := sound r mem
    apply Variant.reconstructible_of_unique hs
    intro t ht u v nu nv
    obtain ⟨slot,inc,rfl⟩ := List.mem_map.mp ht
    cases slot with
    | inl a => exact unique _ hs.1 a _ _ nu nv
    | inr t =>
      have un := (cert t inc).unique _ hs.1
      exact (un u nu).trans (un v nv).symm


theorem Exact.packed {op : A → Term sig} {rows : List (Row sig (Key keys) A)}
    (family : Exact R Subtype.val op rows) (vars : Normalized R Substitution.identity)
    (typed : ∀ r ∈ rows, r.Sorted) (normal : ∀ r ∈ rows, r.IsNormal R)
    (slots : List (Sum A (Term sig))) (used : ∀ a, .inl a ∈ slots)
    (scope : ∀ v, Observed (slots.map (packedInput op)) v → v ∈ keys)
    (stable : ∀ t, .inr t ∈ slots → StableVariants.Stable R t)
    (unique : ∀ ρ : Substitution sig, Normalized R ρ → ∀ a u v,
      NormalForm R (ρ.apply (op a)) u → NormalForm R (ρ.apply (op a)) v → EquivB u v) :
    CompleteVariants R (slots.map (packedInput op)) (packRows rows typed slots) ∧
      ∀ answer ∈ packRows rows typed slots, answer.Reconstructible R (slots.map (packedInput op)) :=
  family.packedRepresentatives vars typed normal slots used scope id
    (fun t h => StableVariants.stableRepresentative (stable t h)) unique

/-- Opening each joint row in a fresh range also protects variables in stable
slots that mention several projected images. This needs the finite list of
keys to be precisely the caller's visible variables. -/
theorem Row.packedRepresentative_safe (r : Row sig (Key keys) A) (typed : r.Sorted) (op : A → Term sig)
    (slots : List (Sum A (Term sig))) (avoid : List Variable)
    (n : Term sig → Term sig) (localVars : ∀ t, .inr t ∈ slots → ∀ v, (n t).Occurs v → t.Occurs v)
    (scope : ∀ v, v ∈ keys ↔ Observed (slots.map (packedInput op)) v)
    (fresh : ∀ w, r.Uses w → w ∉ keys ++ avoid) :
    let a := r.pack typed slots n
    a.Safe (slots.map (packedInput op)) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  let σ := r.project typed
  have outside (v) (notKey : v ∉ keys) : σ.image v = .var v := by simp [σ,Row.project,notKey]
  have free {v w} (key : v ∈ keys) (occ : (σ.image v).Occurs w) : w ∉ keys ++ avoid := by
    have same := r.project_key typed (⟨v,key⟩ : Key keys)
    exact fresh w (.inl ⟨⟨v,key⟩,same ▸ occ⟩)
  constructor
  · constructor
    · intro v absent; exact outside v fun h => absent ((scope v).mp h)
    · intro v obs w occ
      exact .inr (fun bad => free ((scope v).mpr obs) occ (List.mem_append_right _ bad))
    · intro t mem w occ
      obtain ⟨slot,inc,rfl⟩ := List.mem_map.mp mem
      cases slot with
      | inl i => exact .inr (fun bad => fresh w (.inr ⟨i,occ⟩) (List.mem_append_right _ bad))
      | inr t =>
        obtain ⟨v,hv,hw⟩ := σ.occurs_in_image (n t) w occ
        have key := (scope v).mpr ⟨_,List.mem_map_of_mem (f := packedInput op) inc,localVars t inc v hv⟩
        exact .inr (fun bad => free key hw (List.mem_append_right _ bad))
  · intro v
    change σ.apply (σ.image v) = σ.image v
    by_cases key : v ∈ keys
    · exact (Term.subst_eq_of_agree _ Term.var _ (fun w occ =>
        outside w fun present => free key occ (List.mem_append_left _ present))).trans (Term.subst_id _)
    · rw [outside v key]; exact outside v key

theorem Row.packed_safe (r : Row sig (Key keys) A) (typed : r.Sorted) (op : A → Term sig)
    (slots : List (Sum A (Term sig))) (avoid : List Variable)
    (scope : ∀ v, v ∈ keys ↔ Observed (slots.map (packedInput op)) v)
    (fresh : ∀ w, r.Uses w → w ∉ keys ++ avoid) :
    let a := r.pack typed slots
    a.Safe (slots.map (packedInput op)) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v :=
  r.packedRepresentative_safe typed op slots avoid id (fun _ _ _ h => h) scope fresh

end Tamarin.Rewriting.VariantJoin
