import Tamarin.DHSignedMatrix
import Tamarin.ACBasisComplete

/-! Reify signed magnitudes into one shared bag of factors per basis column.
The number of columns depends only on the query matrix. A witness bag may
hold arbitrarily many distinct opaque factors or repetitions. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open ACBasis
variable {n : Nat} {sig : Signature}

def profiles : (n : Nat) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n+1 => [false,true].flatMap fun b => (profiles n).map fun tail => Fin.cases b tail

theorem mem_profiles (d : Fin n → Bool) : d ∈ profiles n := by
  induction n with
  | zero => exact List.mem_singleton.mpr (funext fun i => i.elim0)
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨d 0,by cases d 0 <;> simp,List.mem_map.mpr ⟨fun i => d i.succ,ih _,?_⟩⟩
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i

abbrev Column (basis : (Fin n → Bool) → List (Vec n)) :=
  (d : Fin n → Bool) × Fin (basis d).length

def columns (basis : (Fin n → Bool) → List (Vec n)) : List (Column basis) :=
  (profiles n).flatMap fun d => (List.finRange (basis d).length).map fun j => ⟨d,j⟩

theorem mem_columns (basis : (Fin n → Bool) → List (Vec n)) (g : Column basis) :
    g ∈ columns basis :=
  List.mem_flatMap.mpr ⟨g.1,mem_profiles _,List.mem_map.mpr ⟨g.2,List.mem_finRange _,rfl⟩⟩

/-- The chosen subset is finite. A factor may only appear in columns of its
own sign profile. Every coordinate uses the same bag for a shared column. -/
structure Blocks {α : Type} [DecidableEq α] (basis : (Fin n → Bool) → List (Vec n))
    (signs : α → Fin n → Bool) (mag : α → Vec n) where
  active : List (Column basis)
  branch : active ∈ FlatMatchSearch.sublists (columns basis)
  bag : Column basis → List α
  selected : ∀ g, g ∈ active ↔ bag g ≠ []
  conformal : ∀ g k, k ∈ bag g → signs k = g.1
  counts : ∀ k, mix (basis (signs k)).get (fun j => (bag ⟨signs k,j⟩).count k) = mag k

private theorem nodup {α : Type} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp [List.mem_eraseDups],nodup _⟩
termination_by xs.length
decreasing_by have := List.length_filter_le (fun (v : α) => !v == x) xs; simp; omega

theorem blocks_iff {α : Type} [DecidableEq α] (basis : (Fin n → Bool) → List (Vec n))
    (signs : α → Fin n → Bool) (mag : α → Vec n) (support : List α)
    (outside : ∀ k ∉ support, ∀ i, mag k i = 0) :
    (∃ b : Blocks basis signs mag, ∀ g k, k ∈ b.bag g → k ∈ support) ↔ ∀ k, Generates (basis (signs k)) (mag k) := by
  classical
  constructor
  · rintro ⟨b,_⟩ k
    exact ⟨_, b.counts k⟩
  intro spans
  let co (d : Fin n → Bool) (j : Fin (basis d).length) (k : α) : Nat :=
    if eq : signs k = d then (spans k).choose (eq.symm ▸ j) else 0
  let bag (g : Column basis) := support.eraseDups.flatMap fun k => List.replicate (co g.1 g.2 k) k
  let active := (columns basis).filter fun g => !(bag g).isEmpty
  refine ⟨⟨active,ACSystem.filter_mem_sublists ..,bag,?_,?_,?_⟩,?_⟩
  · intro g
    simp [active,mem_columns]
  · intro g k hk
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hk
    obtain ⟨used,rfl⟩ := List.mem_replicate.mp ha
    apply Classical.byContradiction
    intro h
    simp [co,h] at used
  · intro k
    have count (j : Fin (basis (signs k)).length) :
        (bag ⟨signs k,j⟩).count k = if k ∈ support then (spans k).choose j else 0 := by
      simp [bag,ACSystem.parts_count _ (nodup _),List.mem_eraseDups,co]
    simp only [count]
    by_cases h : k ∈ support
    · simpa [h] using (spans k).choose_spec
    · funext i
      simp [h,mix,dot,total,outside k h i,List.sum_eq_zero_iff_forall_eq_nat]

  · intro g k present
    obtain ⟨a,ha,rep⟩ := List.mem_flatMap.mp present
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp rep
    exact List.mem_eraseDups.mp ha

local instance : DecidableEq (Fin n → Bool) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext,congrFun⟩

/-- One coordinate of a symbolic answer, split into its two signs.
Repeated occurrences of a column refer to the same witness in every coordinate. -/
def slots (basis : (Fin n → Bool) → List (Vec n)) (active : List (Column basis))
    (i : Fin n) (negative : Bool) : List (Column basis) :=
  (profiles n).flatMap fun d =>
    if d i = negative then (List.finRange (basis d).length).flatMap fun j =>
      if (⟨d,j⟩ : Column basis) ∈ active then List.replicate ((basis d).get j i) (⟨d,j⟩ : Column basis) else []
    else []

private theorem profiles_nodup (n : Nat) : (profiles n).Nodup := by
  induction n with
  | zero => simp [profiles]
  | succ n ih =>
    have inj (b : Bool) : Function.Injective (fun tail : Fin n → Bool => ((Fin.cases b tail) : Fin (n+1) → Bool)) :=
      fun _ _ h => funext fun j => congrFun h j.succ
    simp only [profiles,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nodup_append]
    refine ⟨ih.map _ (fun _ _ h eq => h (inj false eq)),ih.map _ (fun _ _ h eq => h (inj true eq)),?_⟩
    intro a ha b hb eq
    subst b
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,_,he⟩ := List.mem_map.mp hb
    cases (show true = false from congrFun he 0)

private theorem sum_single {α : Type} [DecidableEq α] (xs : List α) (h : xs.Nodup) (key : α)
    (v : Nat) : (xs.map fun k => if k = key then v else 0).sum = if key ∈ xs then v else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨absent,distinct⟩ := List.nodup_cons.mp h
    by_cases eq : a = key
    · subst a; simp [ih distinct,absent]
    · simp [ih distinct,eq,Ne.symm eq]

theorem Blocks.coordinate_count {α : Type} [DecidableEq α] {basis : (Fin n → Bool) → List (Vec n)}
    {signs : α → Fin n → Bool} {mag : α → Vec n} (b : Blocks basis signs mag)
    (i : Fin n) (negative : Bool) (k : α) :
    ((slots basis b.active i negative).flatMap b.bag).count k =
      if signs k i = negative then mag k i else 0 := by
  classical
  let part (d : Fin n → Bool) := (List.finRange (basis d).length).flatMap fun j =>
    if (⟨d,j⟩ : Column basis) ∈ b.active then List.replicate ((basis d).get j i) (⟨d,j⟩ : Column basis) else []
  have countMap {β : Type} (xs : List β) (f : β → List α) :
      (xs.flatMap f).count k = (xs.map fun a => (f a).count k).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  have one (d : Fin n → Bool) (j : Fin (basis d).length) :
      ((if (⟨d,j⟩ : Column basis) ∈ b.active then List.replicate ((basis d).get j i) (⟨d,j⟩ : Column basis) else []).flatMap b.bag).count k =
        (basis d).get j i * (b.bag ⟨d,j⟩).count k := by
    by_cases h : (⟨d,j⟩ : Column basis) ∈ b.active
    · simpa [h,ACSystem.expand,List.flatMap_def] using
        ACSystem.count_expand [j] (fun t => (basis d).get t i) (fun t => b.bag ⟨d,t⟩) k
    · have empty := Classical.not_not.mp (fun ne => h ((b.selected _).mpr ne))
      simp [h,empty]
  have profile (d) : ((part d).flatMap b.bag).count k = if d = signs k then mag k i else 0 := by
    unfold part
    rw [List.flatMap_assoc,countMap]
    simp only [one,List.finRange,List.map_ofFn,Function.comp_def]
    split
    · next h => subst d; exact congrFun (b.counts k) i
    · next h =>
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro v hv
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
      have missing : k ∉ b.bag ⟨d,j⟩ := fun present => h (b.conformal _ k present).symm
      simp [List.count_eq_zero.mpr missing]
  change ((((profiles n).flatMap fun d => if d i = negative then part d else []).flatMap b.bag).count k) = _
  rw [List.flatMap_assoc,countMap]
  have each (d : Fin n → Bool) :
      (((if d i = negative then part d else []).flatMap b.bag).count k) =
        if d = signs k then (if signs k i = negative then mag k i else 0) else 0 := by
    by_cases h : d = signs k
    · subst d; split <;> simp_all
    · split <;> simp_all
  simp only [each,sum_single _ (profiles_nodup n),mem_profiles,ite_true]

open Classical

theorem slot_properties {basis : (Fin n → Bool) → List (Vec n)} {active : List (Column basis)}
    {i negative g} (used : g ∈ slots basis active i negative) : g ∈ active ∧ g.1 i = negative := by
  classical
  obtain ⟨d,_,ds⟩ := List.mem_flatMap.mp used
  split at ds <;> try contradiction
  obtain ⟨j,_,js⟩ := List.mem_flatMap.mp ds
  split at js <;> try contradiction
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp js
  constructor <;> assumption

private def side (f : sig.ACSym) : List Variable → Option (Term sig)
  | [] => none
  | a :: as => some ((ACSystem.Side.mk a as).term f)

def template (s : Symbols sig) (basis : (Fin n → Bool) → List (Vec n))
    (active : List (Column basis)) (name : Column basis → Variable) (i : Fin n) : Term sig :=
  Balance.assemble s (side s.mul ((slots basis active i false).map name))
    (side s.mul ((slots basis active i true).map name))

/-- Every symbolic coordinate is already normal at the branch, including
empty coordinates and parameters repeated with multiplicity greater than one. -/
theorem template_normal {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (mul : MulBucket E) (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (basis : (Fin n → Bool) → List (Vec n)) (active : List (Column basis))
    (name : Column basis → Variable) (inj : Function.Injective name) (sort : ∀ g, (name g).sort = .msg)
    (i : Fin n) : HasSort (template s basis active name i) .msg ∧
      Normal (ruleRoot T.rules) (template s basis active name i) := by
  let entries (d : Bool) := (slots basis active i d).map fun g => (Term.var (name g) : Term sig)
  have packed (d : Bool) : side s.mul ((slots basis active i d).map name) = DHTower.packed s (entries d) := by
    unfold entries
    cases slots basis active i d <;> simp [side,DHTower.packed,ACRepresentation.decode,ACSystem.Side.term,List.map_map,Function.comp_def]
  have fact d : ∀ t ∈ entries d, Factor s t := by
    rintro t h
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
    constructor <;> intro eq <;> cases eq
  have pos d := DHTower.Positive.packed mul (ts := entries d) (by
    rintro t h; obtain ⟨g,_,rfl⟩ := List.mem_map.mp h
    exact sort g ▸ HasSort.var (name g)) (by
    rintro t h; obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
    exact (ConstructorVariants.constructor_normal _ mul.1).1 _) (fact d)
  have disjoint : ∀ k ∈ Balance.bag s (DHTower.packed s (entries true)),
      k ∉ Balance.bag s (DHTower.packed s (entries false)) := by
    intro k hn hp
    rw [DHTower.bag_factors _ _ (fact true)] at hn
    rw [DHTower.bag_factors _ _ (fact false)] at hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hn
    obtain ⟨u,hu,eq⟩ := List.mem_map.mp hp
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
    have id := inj (Head.var.inj (Quotient.exact eq).head_eq)
    subst j
    exact Bool.noConfusion ((slot_properties hj).2.symm.trans (slot_properties hg).2)
  unfold template
  rw [packed,packed]
  have h := DHTower.assembled_normal mul inv unit (pos false) (pos true) disjoint
  exact ⟨h.1,h.2.1⟩

theorem template_read (s : Symbols sig) (R : Root sig) (vars : ∀ v, Normal R (.var v))
    (basis : (Fin n → Bool) → List (Vec n)) (active) (name : Column basis → Variable) (i : Fin n)
    (k : Cancellation.Class sig) :
    Balance.read s R k (template s basis active name i) =
      some ((((slots basis active i false).map fun g => Cancellation.classOf (.var (name g))).count k : Int) -
        (((slots basis active i true).map fun g => Cancellation.classOf (.var (name g))).count k : Int)) := by
  let cls (v : Variable) := Cancellation.classOf (sig := sig) (.var v)
  have formula (v : Variable) (vs : List Variable) :
      Balance.read s R k ((ACSystem.Side.mk v vs).term s.mul) = some ((((v::vs).map cls).count k : Nat) : Int) := by
    induction vs generalizing v with
    | nil => by_cases eq : cls v = k <;> simp [cls] at eq <;>
        simp [ACSystem.Side.term,ACRepresentation.fold,Balance.read,Balance.alien,vars,cls,eq]
    | cons a as ih =>
      change Balance.read s R k (s.product.mul (.var v) ((ACSystem.Side.mk a as).term s.mul)) = _
      rw [Balance.read_mul,ih]
      by_cases eq : cls v = k <;> simp [cls] at eq <;>
        simp [Balance.read,Balance.alien,vars,cls,eq,Balance.plus,List.count_cons,Int.add_comm]
  have assembled (ps ns : List Variable) :
      Balance.read s R k (Balance.assemble s (side s.mul ps) (side s.mul ns)) =
        some (((ps.map cls).count k : Int) - ((ns.map cls).count k : Int)) := by
    cases ps <;> cases ns <;> simp [side,Balance.assemble,formula,Balance.minus,Balance.plus,Int.sub_eq_add_neg]
  simpa [template,List.map_map,Function.comp_def,cls] using assembled
    ((slots basis active i false).map name) ((slots basis active i true).map name)

/-- Substituting one term per active witness reconstructs the original
normal input modulo structural AC alone. No cancellation after substitution
is allowed by the variant contract. -/
theorem Blocks.instantiate [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig}
    {basis : (Fin n → Bool) → List (Vec n)} {signs mag} (b : Blocks basis signs mag)
    (name : Column basis → Variable) (δ : Substitution sig)
    (realized : ∀ g ∈ b.active, Cancellation.flatten s.mul (δ.image (name g)) = b.bag g)
    {t p neg} (canonical : Balance.Canonical s R t p neg) (i : Fin n)
    (reads : ∀ k, Balance.read s R k t = some (signed (signs k) (mag k) i)) :
    EquivB (δ.apply (template s basis b.active name i)) t := by
  classical
  let part (d : Bool) := side s.mul ((slots basis b.active i d).map name)
  have factors (d : Bool) : Balance.bag s ((part d).map δ.apply) =
      (slots basis b.active i d).flatMap b.bag := by
    have raw (xs : List (Column basis)) :
        Balance.bag s ((side s.mul (xs.map name)).map δ.apply) =
          xs.flatMap fun g => Cancellation.flatten s.mul (δ.image (name g)) := by
      cases xs with
      | nil => rfl
      | cons x xs =>
        simpa [side, Balance.bag,ACSystem.Side.vars,List.flatMap_map,Function.comp_def] using
          ACSystem.flatten_side s.mul ⟨name x,xs.map name⟩ δ
    rw [show part d = _ from rfl,raw]
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro g h
    exact realized g (slot_properties h).1
  have splitCounts (k) :
      (Balance.bag s p).count k = (if signs k i = false then mag k i else 0) ∧
      (Balance.bag s neg).count k = (if signs k i = true then mag k i else 0) := by
    have count := Option.some.inj ((canonical.read_count k).symm.trans (reads k))
    have apart : (Balance.bag s neg).count k = 0 ∨ (Balance.bag s p).count k = 0 := by
      by_cases h : k ∈ Balance.bag s neg
      · exact .inr (List.count_eq_zero.mpr (canonical.disjoint k h))
      · exact .inl (List.count_eq_zero.mpr h)
    cases h : signs k i <;> simp [signed,h] at * <;> omega
  have rebuild : EquivB (Balance.assemble s ((part false).map δ.apply) ((part true).map δ.apply))
      (Balance.assemble s p neg) := by
    apply Balance.assemble_equiv <;> apply List.perm_iff_count.mpr <;> intro k
    · rw [factors,b.coordinate_count,(splitCounts k).1]
    · rw [factors,b.coordinate_count,(splitCounts k).2]
  apply EquivB.trans _ (rebuild.trans canonical.value.symm)
  change EquivB (δ.apply (Balance.assemble s (part false) (part true))) _
  cases part false <;> cases part true <;> first
    | exact .refl _
    | exact .free _ _ _ (fun j => Fin.elim0 (s.oneArity ▸ j))


/-- For normalized caller images, simultaneous equality of all observed normal
forms is equivalent to realization by one finite branch of shared factor bags. -/
theorem normalForms_blocks [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Balance.Inventory E) (env : Fin n → Term sig) (system : List (Constraint n))
    (basis : (Fin n → Bool) → List (Vec n))
    (valid : ∀ d, BasisCorrect (system.map (row d)) (basis d))
    (typed : ∀ i, HasSort (env i) .msg) (normalized : ∀ i, Normal (ruleRoot T.rules) (env i))
    (value : Expr n → Term sig)
    (normal : ∀ eq ∈ system, ∀ e, e = eq.1 ∨ e = eq.2 →
      NormalForm (ruleRoot T.rules) (e.term s env) (value e)) :
    (∀ eq ∈ system, EquivB (value eq.1) (value eq.2)) ↔
      ∃ signs mag, (∀ k i, Balance.read s (ruleRoot T.rules) k (env i) = some (signed (signs k) (mag k) i)) ∧
        Nonempty (Blocks (α := Cancellation.Class sig) basis signs mag) := by
  classical
  constructor
  · intro equal
    obtain ⟨support,signs,mag,reads,outside⟩ := finite_normal_readings E env typed normalized
    obtain ⟨b,_⟩ := (blocks_iff basis signs mag support outside).mpr
      ((normalForms_iff inventory env system signs mag reads basis valid value typed normal).mp equal)
    exact ⟨signs,mag,reads,⟨b⟩⟩
  · rintro ⟨signs,mag,reads,⟨b⟩⟩
    exact (normalForms_iff inventory env system signs mag reads basis valid value typed normal).mpr
      (fun k => ⟨_,b.counts k⟩)

private theorem factor_of_reading [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s}
    (E : ExtraTable T) {t : Term sig} (typed : HasSort t .msg) (normal : Normal (ruleRoot T.rules) t)
    {k z} (reading : Balance.read s (ruleRoot T.rules) k t = some z) (nonzero : z ≠ 0) :
    ∃ u, HasSort u (sig.acSort s.mul) ∧ Cancellation.flatten s.mul u = [k] := by
  obtain ⟨p,n,canon⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) typed normal
  have count := Option.some.inj (reading.symm.trans (canon.read_count k))
  have st := Term.checkSort_sound _ _ ((SortClash.check_equiv canon.value .msg) ▸ Term.checkSort_complete typed)
  have found : k ∈ Balance.bag s p ∨ k ∈ Balance.bag s n := by
    by_cases hp : k ∈ Balance.bag s p
    · exact .inl hp
    · apply Or.inr; apply Classical.byContradiction; intro hn
      rw [List.count_eq_zero.mpr hp,List.count_eq_zero.mpr hn] at count
      omega
  cases p with
  | none =>
    cases n with
    | none => simp [Balance.bag] at found
    | some n =>
      exact ACSystem.factor_atom s.mul n (s.mulSort ▸ E.presentation.invChild _ st) k
        (by simpa [Balance.bag] using found)
  | some p =>
    cases n with
    | none => exact ACSystem.factor_atom s.mul p (s.mulSort ▸ st) k (by simpa [Balance.bag] using found)
    | some n =>
      have sc := Term.checkSort_complete st
      change (Term.ac s.mul p (s.product.inv n)).checkSort .msg = true at sc
      simp only [Term.checkSort,Bool.and_eq_true] at sc
      rcases found with hp | hn
      · exact ACSystem.factor_atom s.mul p (Term.checkSort_sound _ _ sc.1.2) k hp
      · exact ACSystem.factor_atom s.mul n (s.mulSort ▸ E.presentation.invChild _
          (s.mulSort ▸ Term.checkSort_sound _ _ sc.2)) k hn

/-- One of the finitely many templates admits a single sorted substitution
whose images reconstruct every input at once. This is the factorization
direction; arbitrary symbolic branches still require a normality check. -/
theorem factor_through_template [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Balance.Inventory E) (env : Fin n → Term sig) (system : List (Constraint n))
    (basis : (Fin n → Bool) → List (Vec n)) (valid : ∀ d, BasisCorrect (system.map (row d)) (basis d))
    (name : Column basis → Variable) (inj : Function.Injective name) (sort : ∀ g, (name g).sort = .msg)
    (typed : ∀ i, HasSort (env i) .msg) (normalized : ∀ i, Normal (ruleRoot T.rules) (env i))
    (value : Expr n → Term sig)
    (normal : ∀ eq ∈ system, ∀ e, e = eq.1 ∨ e = eq.2 →
      NormalForm (ruleRoot T.rules) (e.term s env) (value e))
    (equal : ∀ eq ∈ system, EquivB (value eq.1) (value eq.2)) :
    ∃ branch ∈ FlatMatchSearch.sublists (columns basis), ∃ δ : Substitution sig,
      ∀ i, EquivB (δ.apply (template s basis branch name i)) (env i) := by
  classical
  obtain ⟨sup,signs,mag,reads,outside⟩ := finite_normal_readings E env typed normalized
  let support := sup.filter fun k => decide (∃ i, mag k i ≠ 0)
  have zero (k) (h : k ∉ support) (i) : mag k i = 0 := by
    by_cases hs : k ∈ sup
    · apply Classical.byContradiction; intro ne
      exact h (List.mem_filter.mpr ⟨hs,decide_eq_true ⟨i,ne⟩⟩)
    · exact outside k hs i
  obtain ⟨b,used⟩ := (blocks_iff basis signs mag support zero).mpr
    ((normalForms_iff inventory env system signs mag reads basis valid value typed normal).mp equal)
  have realized (g) (h : g ∈ b.active) := ACSystem.realize s.mul (b.bag g) ((b.selected _).mp h)
  obtain ⟨δ,images⟩ := ACSystem.instantiate_witnesses s.mul b.active name inj
    (fun g => (sort g).trans s.mulSort.symm) (fun g h => realized g h (by
      intro k hk
      obtain ⟨i,nonzero⟩ := of_decide_eq_true (List.mem_filter.mp (used g k hk)).2
      apply factor_of_reading E (typed i) (normalized i) (reads k i)
      cases d : signs k i <;> simp [signed,d,nonzero]))
  refine ⟨b.active,b.branch,δ,fun i => ?_⟩
  obtain ⟨_,_,canon⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) (typed i) (normalized i)
  exact b.instantiate name δ images canon i (fun k => reads k i)

end Tamarin.Rewriting.DHPeer.SignedMatrix
