import Tamarin.TableNarrowing

/-! Proper-subproduct narrowing for kind-level AC products. A substitution
can split a variable into multiple factors only when its image is a sorted
product. Consequently every ill-sorted factor of a concrete remainder comes
from one whole symbolic factor. Keep those factors in their source context,
and let a single sorted rule-local variable stand for the rest. -/
namespace Tamarin.KindACNarrowing
open Rewriting RootNarrowing ACSubproductReduction ContextualReduction
open ACRepresentation
variable {s : Signature} [DecidableEq s.ACSym]

private def views (f : s.ACSym) (t : Term s) : List (Term s × Option (Term s)) :=
  (t,none) :: (ACSplits.splits f t).map fun (a,b) => (a,some b)

private theorem view_sound {f : s.ACSym} {t : Term s} {v}
    (h : v ∈ views f t) : EquivB t (plug f v.2 v.1) := by
  rcases List.mem_cons.mp h with rfl|hm
  · exact .refl _
  · obtain ⟨⟨a,b⟩,mem,rfl⟩ := List.mem_map.mp hm
    exact ACSplits.sound f t mem

private theorem view_cover {f : s.ACSym} {t a : Term s} {k}
    (h : EquivB t (plug f k a)) : ∃ v ∈ views f t, EquivB a v.1 := by
  cases k with
  | none => exact ⟨_,List.mem_cons_self,h.symm⟩
  | some b =>
    obtain ⟨l,r,mem,eq,_⟩ := ACSplits.complete f h
    exact ⟨(l,some r),List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(l,r),mem,rfl⟩),eq⟩

/-- Remove prescribed factors one at a time. Each can be removed with its
entire source block, regardless of duplicate values and occurrence order. -/
private theorem peel {α β γ : Type} (block : α → List β) (key : γ → β)
    (xs : List α) (inside : List β) (outside : List γ)
    (single : ∀ x ∈ xs, ∀ b ∈ outside, key b ∈ block x → block x = [key b])
    (layout : (xs.flatMap block).Perm (inside ++ outside.map key)) :
    ∃ kept rest, xs.Perm (kept ++ rest) ∧ (kept.flatMap block).Perm inside := by
  classical
  induction outside generalizing xs with
  | nil => exact ⟨xs,[],by simp,by simpa using layout⟩
  | cons b bs ih =>
    have move := List.perm_cons_append_cons (key b) (List.Perm.refl (inside ++ bs.map key))
    have start := layout.trans move.symm
    obtain ⟨x,hx,hit⟩ := List.mem_flatMap.mp (start.mem_iff.mpr List.mem_cons_self)
    have take := List.perm_cons_erase hx
    have blocks := take.flatMap_right block
    rw [List.flatMap_cons,single x hx b List.mem_cons_self hit,List.singleton_append] at blocks
    obtain ⟨kept,rest,partition,factors⟩ := ih (xs.erase x)
      (fun y hy c hc => single y (List.mem_of_mem_erase hy) c (List.mem_cons_of_mem b hc))
      ((blocks.symm.trans start).cons_inv)
    exact ⟨kept,x::rest,take.trans (List.perm_cons_append_cons x partition),factors⟩

private noncomputable def factors (f : s.ACSym) (ρ : Substitution s) (ts : List (Term s)) :=
  ts.flatMap fun t => Cancellation.flatten f (ρ.apply t)

private noncomputable def bag (f : s.ACSym) : Option (Term s) → List (Cancellation.Class s)
  | none => [] | some t => Cancellation.flatten f t

omit [DecidableEq s.ACSym] in
private theorem plug_bag (f : s.ACSym) (o : Option (Term s)) (t : Term s) :
    Cancellation.flatten f (plug f o t) = Cancellation.flatten f t ++ bag f o := by
  cases o <;> simp [bag,plug,Cancellation.flatten_ac]

private theorem source_bag (f : s.ACSym) (ρ : Substitution s) (t : Term s) :
    Cancellation.flatten f (ρ.apply t) = factors f ρ (flatten f t) := by
  rw [DHProduct.classes,StableVariants.flatten_apply,List.map_flatMap]
  simp only [factors,DHProduct.classes]

omit [DecidableEq s.ACSym] in
private theorem decoded_bag (f : s.ACSym) (ρ : Substitution s) (ts : List (Term s)) :
    bag f ((decode f ts).map ρ.apply) = factors f ρ ts := by
  cases ts with
  | nil => rfl
  | cons t ts => exact ACPivot.fold_factors f ρ t ts

omit [DecidableEq s.ACSym] in
private theorem plain_bag (f : s.ACSym) (ts : List (Term s)) :
    bag f (decode f ts) = ts.flatMap (Cancellation.flatten f) := by
  have h := decoded_bag f (.identity (sig := s)) ts
  have eq : (Substitution.identity (sig := s)).apply = id := funext Substitution.apply_identity
  simpa [factors,eq] using h

private theorem one_bad (f : s.ACSym) (t : Term s) (ρ : Substitution s)
    {x : Term s} (hx : x ∈ flatten f t) (b : Term s) (bad : ¬HasSort b (s.acSort f))
    (mem : Cancellation.classOf b ∈ Cancellation.flatten f (ρ.apply x)) :
    Cancellation.flatten f (ρ.apply x) = [Cancellation.classOf b] := by
  have singleton (a : Term s) (e : Cancellation.flatten f (ρ.apply x) = [Cancellation.classOf a]) :
      Cancellation.flatten f (ρ.apply x) = [Cancellation.classOf b] := by
    rw [e] at mem ⊢
    rw [List.mem_singleton.mp mem]
  cases x with
  | var v =>
    cases img : ρ.image v with
    | ac g l r =>
      by_cases eq : f = g
      · subst g
        have sorted := Term.checkSort_complete (ρ.sorted v)
        rw [img] at sorted
        simp only [Term.checkSort,Bool.and_eq_true] at sorted
        have typed : HasSort (ρ.apply (.var v)) (s.acSort f) := by
          change HasSort (ρ.image v) _
          rw [img]; exact .ac _ _ _ (Term.checkSort_sound _ _ sorted.1.2) (Term.checkSort_sound _ _ sorted.2)
        rw [DHProduct.classes] at mem
        obtain ⟨a,ha,eq⟩ := List.mem_map.mp mem
        have ok := Term.checkSort_complete (flatten_hasSort f _ typed a ha)
        rw [SortClash.check_equiv (Quotient.exact eq) _] at ok
        exact (bad (Term.checkSort_sound _ _ ok)).elim
      · apply singleton (.ac g l r)
        change Cancellation.flatten f (ρ.image v) = _
        simp [img,Cancellation.flatten,eq]
    | _ =>
      apply singleton (ρ.image v)
      change Cancellation.flatten f (ρ.image v) = _
      rw [img]; rfl
  | ac g a c =>
    by_cases eq : f = g
    · subst g
      have one := congrArg List.length (DHProduct.atom_factors f t (.ac f a c) hx)
      have nonempty (y : Term s) : 0 < (Cancellation.flatten f y).length := by
        simp [DHProduct.classes,List.length_pos_iff,flatten_nonempty]
      rw [Cancellation.flatten_ac,List.length_append] at one
      have := nonempty a; have := nonempty c
      simp only [List.length_singleton] at one
      omega
    · apply singleton (ρ.apply (.ac g a c))
      simp [Substitution.apply,Term.subst,Cancellation.flatten,eq]
  | _ => exact singleton _ rfl

/-- Move whole source factors outside until the concrete remainder of the
chosen view has a sort and can be represented by an ordinary variable. -/
private theorem focus (f : s.ACSym) (t : Term s) (ρ : Substitution s) (p : Term s) (k : Option (Term s))
    (before : EquivB (ρ.apply t) (plug f k p)) :
    ∃ v ∈ views f t, ∃ inner : Option (Term s),
      (∀ a ∈ inner, HasSort a (s.acSort f)) ∧ EquivB (ρ.apply v.1) (plug f inner p) := by
  let ts := (k.map (flatten f)).getD []
  let good := ts.filter (fun a => a.checkSort (s.acSort f))
  let bad := ts.filter (fun a => !(a.checkSort (s.acSort f)))
  let bagOf := fun a : Term s => Cancellation.flatten f (ρ.apply a)
  let need := Cancellation.flatten f p ++ good.map Cancellation.classOf
  have origin : bag f k = ts.map Cancellation.classOf := by
    cases k with
    | none => rfl
    | some _ => exact DHProduct.classes ..
  have atomic (y) (h : y ∈ ts) : Cancellation.flatten f y = [Cancellation.classOf y] := by
    cases k with
    | none => exact (List.not_mem_nil (a := y) h).elim
    | some z => exact DHProduct.atom_factors f z y h
  have split := (List.filter_append_perm (fun a : Term s => a.checkSort (s.acSort f)) ts).symm.map Cancellation.classOf
  have layout := Cancellation.flatten_equiv f before
  rw [source_bag,plug_bag,origin] at layout
  have all : ((flatten f t).flatMap bagOf).Perm (need ++ bad.map Cancellation.classOf) := by
    simpa only [factors,bagOf,need,good,bad,List.append_assoc,List.map_append] using
      layout.trans (split.append_left (Cancellation.flatten f p))
  obtain ⟨kept,rest,partition,pick⟩ := peel bagOf Cancellation.classOf (flatten f t) need bad (by
    intro x hx b hb mem
    have no := (List.mem_filter.mp hb).2
    exact one_bad f t ρ hx b (fun hs => by simp [Term.checkSort_complete hs] at no) mem) all
  obtain ⟨a,da⟩ : ∃ a, decode f kept = some a := by
    cases kept with
    | nil =>
      have empty := List.append_eq_nil_iff.mp (show need = [] from pick.symm.eq_nil)
      have nonempty := ACRepresentation.flatten_nonempty f p
      simp [DHProduct.classes] at empty
      exact (nonempty empty.1).elim
    | cons a as => exact ⟨_,rfl⟩
  have original : EquivB t (plug f (decode f rest) a) := by
    apply Cancellation.equiv_of_flatten_perm f
    rw [plug_bag,plain_bag]
    have one := plain_bag f kept
    rw [da] at one
    change Cancellation.flatten f a = _ at one
    rw [one]
    have regroup := partition.flatMap_right (Cancellation.flatten f)
    rw [List.flatMap_append] at regroup
    have source := source_bag f (.identity (sig := s)) t
    simp only [factors,Substitution.apply_identity] at source
    rw [source]; exact regroup
  obtain ⟨v,member,e⟩ := view_cover original
  let inner := decode f good
  have typed (u) (hu : u ∈ inner) : HasSort u (s.acSort f) := by
    have sorts (x) (hx : x ∈ good) := Term.checkSort_sound x _ (List.mem_filter.mp hx).2
    cases eq : good with
    | nil => simp [inner,eq,decode] at hu
    | cons z zs =>
      have hz : fold f z zs = u := by simpa [inner,eq,decode,eq_comm] using hu
      rw [← hz]
      exact fold_hasSort f _ _ (sorts _ (eq ▸ List.mem_cons_self)) (fun x hx => sorts x (eq ▸ List.mem_cons_of_mem _ hx))
  refine ⟨v,member,inner,typed,(e.subst ρ.image).symm.trans ?_⟩
  apply Cancellation.equiv_of_flatten_perm f
  rw [plug_bag,plain_bag]
  have reify := decoded_bag f ρ kept
  rw [da] at reify
  change Cancellation.flatten f (ρ.apply a) = _ at reify
  change (Cancellation.flatten f (ρ.apply a)).Perm _
  rw [reify]
  have token (xs : List (Term s)) (sub : xs ⊆ ts) :
      xs.flatMap (Cancellation.flatten f) = xs.map Cancellation.classOf := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.map_cons,atomic x (sub List.mem_cons_self),
        List.singleton_append,ih (fun y hy => sub (List.mem_cons_of_mem _ hy))]
  rw [token good (fun _ hy => (List.mem_filter.mp hy).1)]; exact pick

omit [DecidableEq s.ACSym] in
private theorem extend_root {rules : List (Equation s)} (bound : ReferenceReduction.Bound rules)
    (vars : Normalized (ruleRoot rules) Substitution.identity) (f : s.ACSym)
    {p q : Term s} (fire : ruleRoot rules p q) (hd : ConstructorVariants.head p = .ac f)
    (k : Option (Term s)) (typed : ∀ y ∈ k, HasSort y (s.acSort f)) :
    ruleRoot (ACEquationExtensions.extended rules) (plug f k p) (plug f k q) := by
  obtain ⟨r,hr,σ,rfl,rfl⟩ := fire
  cases k with
  | none => exact ⟨r,List.mem_append_left _ hr,σ,rfl,rfl⟩
  | some y =>
    let z := ACEquationExtensions.remainder f r
    have fresh : ¬r.lhs.Occurs z := by
      intro occ
      exact (Nat.lt_irrefl _) (VariablePermutation.lt_freshBound _ _
        (List.mem_append_left r.rhs.variables ((r.lhs.mem_variables z).mpr occ)))
    obtain ⟨η,el,er⟩ := extend_assignment r.lhs r.rhs (bound r hr) f z fresh σ y (typed y rfl)
    have head : ConstructorVariants.head r.lhs = .ac f := by
      cases lhs : r.lhs with
      | var w =>
        have st : StepModulo (ruleRoot rules) (.var w) (Substitution.identity.apply r.rhs) :=
          ⟨_,_,.refl _,.root ⟨r,hr,.identity,by simp [lhs],rfl⟩,.refl _⟩
        exact (vars w _ st).elim
      | atom | free | comm | ac => rw [lhs] at hd; exact hd
    exact ⟨pattern f z r true,List.mem_append_right _ (List.mem_filterMap.mpr ⟨r,hr,by simp [z,head]⟩),
      η,el.symm,er.symm⟩

omit [DecidableEq s.ACSym] in
private theorem apply_plug (f : s.ACSym) (ρ : Substitution s) (k : Option (Term s)) (x : Term s) :
    ρ.apply (plug f k x) = plug f (k.map ρ.apply) (ρ.apply x) := by cases k <;> rfl

omit [DecidableEq s.ACSym] in
private theorem compose_plug (f : s.ACSym) (outer inner : Option (Term s)) :
    ∃ k, ∀ x, EquivB (plug f outer (plug f inner x)) (plug f k x) := by
  cases outer with
  | none => exact ⟨inner,fun _ => .refl _⟩
  | some out =>
    cases inner with
    | none => exact ⟨some out, fun _ => .refl _⟩
    | some x => exact ⟨some (.ac f x out),fun _ => .ac_assoc ..⟩

private def observed (t : Term s) (k : Option (Term s)) (anchors : List (Term s)) :=
  t :: (k.toList ++ anchors)

private def restore (f : s.ACSym) (k : Option (Term s)) (b : Branch s) : Branch s :=
  ⟨b.subst,plug f (k.map b.subst.apply) b.value⟩

/-- Search each symbolic subbag with its original context reserved. The extra
rule handles any sorted remainder inside that subbag. -/
def roots (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)}
    (bound : ReferenceReduction.Bound rules) (f : s.ACSym) (anchors : List (Term s)) (t : Term s) :
    List (Branch s) :=
  (views f t).flatMap fun v =>
    (TableNarrowing.roots u (ACEquationExtensions.bound bound) (observed t v.2 anchors) v.1).map (restore f v.2)

theorem roots_genuine (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)}
    (bound : ReferenceReduction.Bound rules) (f : s.ACSym) (anchors : List (Term s)) (t : Term s) (b : Branch s)
    (hb : b ∈ roots u bound f anchors t) : StepModulo (ruleRoot rules) (b.subst.apply t) b.value := by
  obtain ⟨v,hv,hm⟩ := List.mem_flatMap.mp hb
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hm
  have eq := (view_sound hv).subst row.subst.image
  change EquivB (row.subst.apply t) (row.subst.apply (plug f v.2 v.1)) at eq
  rw [apply_plug] at eq
  obtain ⟨l,r,entry,step,exit⟩ := lift_step f (v.2.map row.subst.apply)
    (TableNarrowing.extended_genuine u bound _ _ _ hr)
  exact ⟨l,r,eq.trans entry,step,exit⟩

theorem roots_cover (u : VerifiedUnifier s (fun _ => True)) {rules : List (Equation s)}
    (bound : ReferenceReduction.Bound rules) (vars : Normalized (ruleRoot rules) Substitution.identity)
    (f : s.ACSym) (anchors : List (Term s)) (t : Term s) (ρ : Substitution s) {result}
    (step : Occurrence (ruleRoot rules) f (ρ.apply t) result) :
    ∃ b ∈ roots u bound f anchors t,
      FitsOn (fun w => t.Occurs w ∨ Observed anchors w) ρ result b.subst b.value := by
  obtain ⟨p,q,k,hd,fire,before,after⟩ := step
  obtain ⟨v,hv,inner,typed,focusEq⟩ := focus f t ρ p k before
  let outer := v.2.map ρ.apply
  let context := observed t v.2 anchors
  obtain ⟨merged,join⟩ := compose_plug f outer inner
  have source := (view_sound hv).subst ρ.image
  change EquivB (ρ.apply t) (ρ.apply (plug f v.2 v.1)) at source
  rw [apply_plug] at source
  have shape := source.trans ((plug_congr f outer focusEq).trans (join _))
  have rebuild := (join q).trans ((same_context f shape before (.refl _) q).trans after)
  have hit : AtRoot (ruleRoot (ACEquationExtensions.extended rules)) (ρ.apply v.1) (plug f inner q) :=
    ⟨_,_,focusEq,extend_root bound vars f fire hd inner typed,.refl _⟩
  obtain ⟨row,hr,δ,agree,value⟩ := TableNarrowing.roots_cover u (ACEquationExtensions.bound bound) context v.1 ρ hit
  refine ⟨_,List.mem_flatMap.mpr ⟨v,hv,List.mem_map_of_mem hr⟩,δ,?_,rebuild.symm.trans ?_⟩
  · intro w hw
    apply agree w ∘ Or.inr
    rcases hw with ht|⟨a,ha,hw⟩
    · exact ⟨_,List.mem_cons_self,ht⟩
    · exact ⟨_,List.mem_cons_of_mem _ (List.mem_append_right _ ha),hw⟩
  · change EquivB (plug f (v.2.map ρ.apply) (plug f inner q))
      (δ.apply (plug f (v.2.map row.subst.apply) row.value))
    cases split : v.2 with
    | none => exact value
    | some a =>
      apply EquivB.ac_congr f value
      have ctx : a ∈ context := by simp [context,observed,split]
      change EquivB (ρ.apply a) (δ.apply (row.subst.apply a))
      rw [← Substitution.apply_compose]
      exact a.subst_equiv ρ.image (δ.compose row.subst).image (fun w hw => agree w (.inr ⟨a,ctx,hw⟩))

end Tamarin.KindACNarrowing
