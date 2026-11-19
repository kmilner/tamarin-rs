import Tamarin.DHSignedVariantFamily
import Tamarin.FlatMatchSearch

/-! Generators from different sign profiles can specify exactly the same
signed vector. A single parameter for each represented vector suffices even
for structural variant instantiation: combine the old parameters as a
nonempty AC product before specializing any of them. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open ACBasis Balance Cancellation
variable {n : Nat} {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem sign_part {g r : Fin n → Bool} {a b : Vec n} (agree : ∀ i, signed g a i = signed r b i)
    (i : Fin n) (d : Bool) :
    (if g i = d then a i else 0) = (if r i = d then b i else 0) := by
  have h := agree i
  cases hl : g i <;> cases hr : r i <;> cases d <;> simp_all [signed] <;> omega

private theorem count_fibers {α : Type} [DecidableEq α] (old : List α) (rep : α → α)
    (xs : List α) (g : α) :
    (xs.flatMap (fun r => old.eraseDups.filter fun v => decide (rep v = r))).count g =
      if g ∈ old then xs.count (rep g) else 0 := by
  classical
  have count (r : α) :
      (old.eraseDups.filter fun v => decide (rep v = r)).count g = if g ∈ old ∧ rep g = r then 1 else 0 := by
    rw [List.Nodup.count ((eraseDups_nodup old).filter _)]
    simp [List.mem_eraseDups]
  induction xs with
  | nil => simp
  | cons r xs ih =>
    simp only [List.flatMap_cons,List.count_append,count,ih,List.count_cons]
    by_cases h : g ∈ old <;> by_cases e : rep g = r <;> simp [h,e,Ne.symm,beq_iff_eq] <;> omega

private theorem side_bag (s : Symbols sig)
    {α : Type} (xs : List α) (name : α → Variable) (δ : Substitution sig) :
    bag s ((side s.mul (xs.map name)).map δ.apply) = xs.flatMap fun k => flatten s.mul (δ.image (name k)) := by
  cases xs with
  | nil => rfl
  | cons g gs =>
    simpa [side,bag,ACSystem.Side.vars,List.flatMap_map,Function.comp_def] using
      ACSystem.flatten_side s.mul ⟨name g,gs.map name⟩ δ

private theorem apply_assemble (s : Symbols sig) (δ : Substitution sig) (p neg : Option (Term sig)) :
    EquivB (δ.apply (assemble s p neg)) (assemble s (p.map δ.apply) (neg.map δ.apply)) := by
  cases p <;> cases neg <;> first | exact .refl _ | exact .free _ _ _ (fun j => Fin.elim0 (s.oneArity ▸ j))

/-- Any representative list covering every signed vector gives a structural
cover of all branches. Zero coordinates impose no sign requirement. The
same substitution explains the positive and negative slots in every
coordinate, without cancellation or any other oriented rewrite. -/
theorem representative_branch [DecidableEq sig.ACSym] (basis : (Fin n → Bool) → List (Vec n))
    (reps : List (Column basis)) (sub : reps.Sublist (columns basis))
    (covers : ∀ g : Column basis, ∃ r ∈ reps, ∀ i,
      signed g.1 ((basis g.1).get g.2) i = signed r.1 ((basis r.1).get r.2) i)
    (name : Column basis → Variable) (inj : Function.Injective name) (sort : ∀ g, (name g).sort = .msg)
    {old : List (Column basis)} (selected : old ∈ FlatMatchSearch.sublists (columns basis)) :
    ∃ active ∈ FlatMatchSearch.sublists reps, ∃ η : Substitution sig, ∀ i,
      EquivB (template s basis old name i) (η.apply (template s basis active name i)) := by
  classical
  let rep (g : Column basis) := (covers g).choose
  have inside g : rep g ∈ reps := (covers g).choose_spec.1
  have agree g i := (covers g).choose_spec.2 i
  let fiber (r : Column basis) := old.eraseDups.filter fun g => decide (rep g = r)
  let active := reps.filter fun r => decide (fiber r ≠ [])
  have chosen := ACSystem.filter_mem_sublists reps (fun r => decide (fiber r ≠ []))
  have full := (FlatMatchSearch.mem_sublists _ _).mpr ((List.filter_sublist (p := fun r => decide (fiber r ≠ []))).trans sub)
  have used {g} (h : g ∈ old) : rep g ∈ active := by
    apply List.mem_filter.mpr
    refine ⟨inside g,decide_eq_true (fun nope => ?_)⟩
    have mem : g ∈ fiber (rep g) := List.mem_filter.mpr ⟨List.mem_eraseDups.mpr h,decide_eq_true rfl⟩
    simp [nope] at mem
  have counts (i : Fin n) (d : Bool) :
      (slots basis old i d).Perm ((slots basis active i d).flatMap fiber) := by
    apply List.perm_iff_count.mpr
    intro g
    rw [column_counts basis old selected,show ((slots basis active i d).flatMap fiber).count g = _ from
        count_fibers old rep _ g,column_counts basis active full]
    by_cases mem : g ∈ old
    · simpa [mem,used mem,rep] using sign_part (agree g) i d
    · simp [mem]
  let cls (g : Column basis) := classOf (sig := sig) (.var (name g))
  have labels (r) (hr : r ∈ active) : ∃ t : Term sig, HasSort t (sig.acSort s.mul) ∧
      flatten s.mul t = (fiber r).map cls := by
    apply ACSystem.realize
    · exact fun e => of_decide_eq_true (List.mem_filter.mp hr).2 (List.map_eq_nil_iff.mp e)
    · intro k inBag
      obtain ⟨g,_,rfl⟩ := List.mem_map.mp inBag
      exact ⟨.var (name g),(sort g).trans s.mulSort.symm ▸ HasSort.var (name g),rfl⟩
  obtain ⟨η,images⟩ := ACSystem.instantiate_witnesses s.mul active name inj (fun g => (sort g).trans s.mulSort.symm) labels
  refine ⟨active,chosen,η,fun i => ?_⟩
  let p (as : List (Column basis)) (d : Bool) := side s.mul ((slots basis as i d).map name)
  have part (d : Bool) : (bag s (p old d)).Perm (bag s ((p active d).map η.apply)) := by
    have raw : bag s (p old d) = (slots basis old i d).map cls := by
      have h := side_bag s (slots basis old i d) name (Substitution.identity (sig := sig))
      change bag s ((p old d).map Substitution.identity.apply) =
        (slots basis old i d).flatMap (fun k => [cls k]) at h
      simpa [show Substitution.identity.apply = (id : Term sig → Term sig) from funext Substitution.apply_identity,← List.map_eq_flatMap] using h
    rw [raw,side_bag s (slots basis active i d) name η]
    have eq : (slots basis active i d).flatMap (fun g => flatten s.mul (η.image (name g))) =
        (slots basis active i d).flatMap (fun g => (fiber g).map cls) := by
      simp only [List.flatMap_def]
      apply congrArg List.flatten
      exact List.map_congr_left (fun g hg => images g (slot_properties hg).1)
    rw [eq,← List.map_flatMap]
    exact (counts i d).map cls
  exact (assemble_equiv s (part false) (part true)).trans ((apply_assemble s η (p active false) (p active true)).symm)

theorem exact_graph_representatives [DecidableEq sig.ACSym] (inventory : Inventory E) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (graph : List (Expr n × Fin n)) (basis : (Fin n → Bool) → List (Vec n))
    (valid : ∀ d, BasisCorrect (graph.map fun p => row d (p.1,.input p.2)) (basis d))
    (reps : List (Column basis)) (sub : reps.Sublist (columns basis))
    (covers : ∀ g : Column basis, ∃ r ∈ reps, ∀ i,
      signed g.1 ((basis g.1).get g.2) i = signed r.1 ((basis r.1).get r.2) i)
    (name : Column basis → Variable) (inj : Function.Injective name) (sort : ∀ g, (name g).sort = .msg)
    (env : Fin n → Term sig) (typed : ∀ i, HasSort (env i) .msg) (norm : ∀ i, Normal (ruleRoot T.rules) (env i)) :
    (∀ p ∈ graph, NormalForm (ruleRoot T.rules) (p.1.term s env) (env p.2)) ↔
      ∃ active ∈ FlatMatchSearch.sublists reps, ∃ δ : Substitution sig,
        Normalized (ruleRoot T.rules) δ ∧ ∀ i, EquivB (env i) (δ.apply (template s basis active name i)) := by
  rw [exact_graph inventory mul inv unit graph basis valid name inj sort env typed norm]
  constructor
  · rintro ⟨old,mem,δ,_,fits⟩
    obtain ⟨active,branch,η,more⟩ := representative_branch (s := s) basis reps sub covers name inj sort mem
    let q : VariantJoin.Row sig (Fin n) Empty := ⟨template s basis active name,Empty.elim⟩
    have hit : VariantJoin.Fits q env Empty.elim (δ.compose η) :=
      ⟨fun i => by rw [Substitution.apply_compose]; exact (fits i).trans ((more i).subst δ.image),fun j => j.elim⟩
    obtain ⟨δ,nd,joint⟩ := (VariantJoin.normal_witness (ConstructorVariants.constructor_normal _ inventory.1).1
      norm (fun x : Empty => x.elim) hit).2
    exact ⟨active,branch,δ,nd,joint.inputs⟩
  · rintro ⟨active,mem,δ,nd,fit⟩
    exact ⟨active,(FlatMatchSearch.mem_sublists _ _).mpr (((FlatMatchSearch.mem_sublists _ _).mp mem).trans sub),δ,nd,fit⟩

end Tamarin.Rewriting.DHPeer.SignedMatrix
