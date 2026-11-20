import Tamarin.TableNarrowing

/-! A finite narrowing traversal over source positions. Each recursive branch
instantiates the untouched siblings. All local unifiers reserve the full list
of observed values and input images, even when a variable occurs only outside
the selected subtree. -/
namespace Tamarin.TableNarrowing
open Rewriting RootNarrowing VariantJoin ContextualReduction ACSubproductReduction
variable {s : Signature} {rules : List (Equation s)} {R : Root s}

structure Groups (rules : List (Equation s)) where
  branches : s.ACSym → List (Term s) → Term s → List (Branch s)
  genuine : ∀ f anchors t b, b ∈ branches f anchors t → StepModulo (ruleRoot rules) (b.subst.apply t) b.value
  covers : ∀ f anchors t (ρ : Substitution s) v, Occurrence (ruleRoot rules) f (ρ.apply t) v →
    ∃ b ∈ branches f anchors t, FitsOn (fun w => t.Occurs w ∨ Observed anchors w) ρ v b.subst b.value

private structure Answers (R : Root s) (scope : Variable → Prop) (admit : Substitution s → Prop)
    (t : Term s) (selection : Substitution s → Term s → Prop) where
  branches : List (Branch s)
  genuine : ∀ b ∈ branches, StepModulo R (b.subst.apply t) b.value
  covers : CoversStep scope admit selection (· ∈ branches)

private abbrev Position (R : Root s) (scope : Variable → Prop) (admit : Substitution s → Prop) (t : Term s) :=
  Answers R scope admit t (fun σ v => StepModulo R (σ.apply t) v)

private def joinPositions {J : Type} {scope : Variable → Prop} {admit : Substitution s → Prop}
    {t : Term s} {atHead} (root : Answers R scope admit t atHead)
    (indices : List J) (complete : ∀ j, j ∈ indices) (entry : J → Term s) (frame : J → Frame s)
    (child : ∀ j, Position R scope admit (entry j))
    (tracked : ∀ j w, (frame j).Uses w → scope w)
    (lift : ∀ j (σ : Substitution s) v, StepModulo R (σ.apply (entry j)) v →
      StepModulo R (σ.apply t) ((frame j).fill σ v))
    (positions : ∀ ρ : Substitution s, ∀ v, StepModulo R (ρ.apply t) v → atHead ρ v ∨
      ∃ j w, StepModulo R (ρ.apply (entry j)) w ∧ EquivB ((frame j).fill ρ w) v) :
    Position R scope admit t where
  branches := root.branches ++ indices.flatMap fun j =>
    (child j).branches.map fun b => ⟨b.subst,(frame j).fill b.subst b.value⟩
  genuine := by
    intro b h
    rcases List.mem_append.mp h with h|h
    · exact root.genuine b h
    obtain ⟨j,_,h⟩ := List.mem_flatMap.mp h
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp h
    exact lift j d.subst d.value ((child j).genuine d hd)
  covers := by
    intro ρ ok v st
    rcases positions ρ v st with atRoot | ⟨j,w,step,eq⟩
    · obtain ⟨b,hb,h⟩ := root.covers ρ ok v atRoot
      exact ⟨b,List.mem_append_left _ hb,h⟩
    obtain ⟨b,hb,fit⟩ := (child j).covers ρ ok w step
    obtain ⟨η,agree,out⟩ := (frame j).fits (tracked j) fit
    exact ⟨_,List.mem_append_right _ (List.mem_flatMap.mpr ⟨j,complete j,List.mem_map_of_mem hb⟩),
      η,agree,eq.symm.trans out⟩

private theorem restrictFit {t : Term s} {anchors : List (Term s)} {ρ μ : Substitution s} {u value : Term s}
    (h : FitsOn (fun w => t.Occurs w ∨ Observed anchors w) ρ u μ value) :
    FitsOn (Observed anchors) ρ u μ value := by
  obtain ⟨η,agree,out⟩ := h
  exact ⟨η,fun w hw => agree w (.inr hw),out⟩

private def whole (u : VerifiedUnifier s (fun _ => True)) (bound : ReferenceReduction.Bound rules)
    (anchors : List (Term s)) (admit : Substitution s → Prop) (t : Term s) :
    Answers (ruleRoot rules) (Observed anchors) admit t (fun σ v => AtRoot (ruleRoot rules) (σ.apply t) v) :=
  ⟨roots u bound anchors t, roots_genuine u bound anchors t,fun ρ _ v st => by
    obtain ⟨b,hb,fit⟩ := roots_cover u bound anchors t ρ st
    exact ⟨b,hb,restrictFit fit⟩⟩

private def pair (a b : Term s) : Bool → Term s | false => a | true => b

private def walk [DecidableEq s.ACSym] (u : VerifiedUnifier s (fun _ => True))
    (bound : ReferenceReduction.Bound rules) (groups : Groups rules)
    (anchors : List (Term s)) (admit : Substitution s → Prop)
    (norm : ∀ ρ, admit ρ → ∀ w, Observed anchors w → Normal (ruleRoot rules) (ρ.image w))
    (t : Term s) (live : ∀ w, t.Occurs w → Observed anchors w) :
    Position (ruleRoot rules) (Observed anchors) admit t := by
  match t with
  | .var w =>
    exact ⟨[],by simp,fun ρ ok v step => (norm ρ ok w (live w rfl) v step).elim⟩
  | .atom a =>
    let top := whole u bound anchors admit (.atom a)
    refine ⟨top.branches,top.genuine,?_⟩
    rintro ρ ok v ⟨p,q,l,fire,r⟩
    apply top.covers ρ ok v
    cases p <;> cases l.head_eq
    cases fire with | root h => exact ⟨_,_,l,h,r⟩
  | .free f xs =>
    apply joinPositions (whole u bound anchors admit (.free f xs)) (List.finRange _) (List.mem_finRange)
      xs (Frame.free f xs) (fun i => walk u bound groups anchors admit norm (xs i) (fun w h => live w ⟨i,h⟩))
    · rintro i w ⟨j,_,h⟩
      exact live w ⟨j,h⟩
    · intro i σ v step
      exact (ContextualReduction.free_iff ..).mpr (.inr ⟨i,v,step,.refl _⟩)
    · exact fun ρ v => (ContextualReduction.free_iff ..).mp
  | .comm f a b =>
    let entries := pair a b
    let fr := fun i => Frame.comm f (entries (!i))
    apply joinPositions (whole u bound anchors admit (.comm f a b)) [false,true] (by decide)
      entries fr (fun | false => walk u bound groups anchors admit norm a (fun w h => live w (.inl h))
                      | true => walk u bound groups anchors admit norm b (fun w h => live w (.inr h)))
    · intro i w h; cases i
      · exact live w (.inr h)
      · exact live w (.inl h)
    · intro i σ v step; cases i
      · exact (ContextualReduction.comm_iff ..).mpr (.inr (.inl ⟨v,step,.refl _⟩))
      · exact (ContextualReduction.comm_iff ..).mpr (.inr (.inr ⟨v,step,.comm_swap ..⟩))
    · intro ρ v step
      rcases (ContextualReduction.comm_iff ..).mp step with fire|⟨v',st,out⟩|⟨v',st,out⟩
      · exact .inl fire
      · exact .inr ⟨false,v',st,out⟩
      · exact .inr ⟨true,v',st,(EquivB.comm_swap ..).trans out⟩
  | .ac f a b =>
    let t := Term.ac f a b
    let top : Answers (ruleRoot rules) (Observed anchors) admit t (fun ρ v => Occurrence (ruleRoot rules) f (ρ.apply t) v) :=
      ⟨groups.branches f anchors t,groups.genuine f anchors t,fun ρ _ v st => by
        obtain ⟨b,hb,fit⟩ := groups.covers f anchors t ρ v st
        exact ⟨b,hb,restrictFit fit⟩⟩
    let entries := pair a b
    let fr := fun i => Frame.ac f (some (entries (!i)))
    apply joinPositions top [false,true] (by decide) entries fr
      (fun | false => walk u bound groups anchors admit norm a (fun w h => live w (.inl h))
           | true => walk u bound groups anchors admit norm b (fun w h => live w (.inr h)))
    · rintro i w ⟨x,hx,hw⟩
      obtain rfl := Option.mem_some_iff.mp hx
      cases i
      · exact live w (.inr hw)
      · exact live w (.inl hw)
    · intro i σ v step; cases i
      · exact (NarrowingPositions.ac_children_iff ..).mpr (.inr (.inl ⟨v,step,.refl _⟩))
      · exact (NarrowingPositions.ac_children_iff ..).mpr (.inr (.inr ⟨v,step,.ac_swap ..⟩))
    · intro ρ v step
      rcases (NarrowingPositions.ac_children_iff ..).mp step with fire|⟨v',st,out⟩|⟨v',st,out⟩
      · exact .inl fire
      · exact .inr ⟨false,v',st,out⟩
      · exact .inr ⟨true,v',st,(EquivB.ac_swap ..).trans out⟩

/-- A rewrite using a range-restricted table can only retain variables from
the source. This also accounts for rewriting under structural equivalence. -/
private theorem stepUses (bound : ReferenceReduction.Bound rules) {a b : Term s}
    (st : Step (ruleRoot rules) a b) (v : Variable) : b.Occurs v → a.Occurs v := by
  induction st with
  | root h =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := h
    intro hv
    obtain ⟨w,hw,occ⟩ := σ.occurs_in_image _ _ hv
    have occurs (t : Term s) (inside : t.Occurs w) : (σ.apply t).Occurs v := by
      induction t with
      | var x => obtain rfl := inside; exact occ
      | atom => exact False.elim inside
      | free _ xs ih => obtain ⟨i,h⟩ := inside; exact ⟨i,ih i h⟩
      | ac f a b ih jh | comm f a b ih jh => exact inside.imp ih jh
    exact occurs _ (bound _ hr w hw)
  | free f xs i _ ih =>
    rintro ⟨j,h⟩
    by_cases e : j = i
    · exact ⟨i,ih (by simpa [e] using h)⟩
    · exact ⟨j,by simpa [e] using h⟩
  | comm_left _ _ _ ih | ac_left _ _ _ ih => exact Or.imp ih id
  | comm_right _ _ _ ih | ac_right _ _ _ ih => exact Or.imp id ih

private theorem reducesUses (bound : ReferenceReduction.Bound rules) {a b : Term s}
    (red : Reduces (ruleRoot rules) a b) (v : Variable) : b.Occurs v → a.Occurs v := by
  induction red with
  | basis h => exact (h.occurs_iff _).mpr
  | step st =>
    obtain ⟨_,_,pre,one,post⟩ := st
    exact (pre.occurs_iff _).mpr ∘ stepUses bound one v ∘ (post.occurs_iff _).mpr
  | trans _ _ ih jh => exact ih ∘ jh
  | free _ _ _ _ ih => rintro ⟨i,h⟩; exact ⟨i,ih i h⟩
  | ac _ _ _ ih jh | comm _ _ _ ih jh => exact Or.imp ih jh

open ReferenceVariantFrontier
variable {n : Nat}
private def anchors (p : Point s n) (keys : List Variable) :=
  keys.map p.assignment.image ++ List.ofFn p.value

private theorem anchors_iff (p : Point s n) (keys : List Variable) (w : Variable) :
    Observed (anchors p keys) w ↔ (p.row keys).Uses w := by
  simp [anchors,Observed,VariantJoin.Row.Uses,Point.row,List.mem_append,or_and_right,exists_or,VariantJoin.Key]
  grind

private theorem fromInputs (query : Fin n → Term s) (p : Point s n) (bound : ReferenceReduction.Bound rules)
    (hp : VariantSaturation.Sound rules query p) (i : Fin n) (w : Variable) (occ : (p.value i).Occurs w) :
    ∃ k : Key (keysOf query), (p.assignment.image k.val).Occurs w := by
  let keys := keysOf query
  let row := p.row keys
  have replay := (VariantSaturation.atFn query p.value hp.2 i).1
  obtain ⟨v,hv,hw⟩ := (p.answer keys).subst.occurs_in_image _ _ (reducesUses bound replay w occ)
  have key : v ∈ keys := (observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
  have same : (p.answer keys).subst.image v = p.assignment.image v :=
    row.project_key (fun k => p.assignment.sorted k.val) ⟨v,key⟩
  exact ⟨⟨v,key⟩,same ▸ hw⟩

/-- A symbolic value must derive every one of its variables from the
observed input images. This can be checked directly on a raw narrowing
frontier, including intermediate values which still have rewrites. -/
def Tracked (keys : List Variable) (p : Point s n) : Prop :=
  ∀ i w, (p.value i).Occurs w → ∃ k : Key keys, (p.assignment.image k.val).Occurs w

structure TrackedSteps (rules : List (Equation s)) (keys : List Variable) (p : Point s n) where
  branches : Fin n → List (Branch s)
  genuine : ∀ i b, b ∈ branches i → StepModulo (ruleRoot rules) (b.subst.apply (p.value i)) b.value
  covers : Tracked keys p → ∀ i,
    RootNarrowing.Search (ruleRoot rules) (p.row keys).Uses
      (fun δ => ∀ k : Key keys, Normal (ruleRoot rules) (δ.apply (p.assignment.image k.val)))
      (p.value i) (· ∈ branches i)

def atPoint [DecidableEq s.ACSym] (u : VerifiedUnifier s (fun _ => True))
    (bound : ReferenceReduction.Bound rules) (groups : Groups rules) (keys : List Variable) (p : Point s n) :
    TrackedSteps rules keys p := by
  -- The branch list is independent of admissibility and its proof. Construct
  -- it with specialization restricted to assignments normal on all anchors.
  let admiss (p : Point s n) (ρ : Substitution s) := ∀ w, Observed (anchors p keys) w →
    Normal (ruleRoot rules) (ρ.image w)
  let run (p : Point s n) (i : Fin n) := walk u bound groups (anchors p keys) (admiss p)
    (fun _ h => h) (p.value i) (fun w h => (anchors_iff p keys w).mpr (.inr ⟨i,h⟩))
  refine ⟨fun i => (run p i).branches,fun i => (run p i).genuine,?_⟩
  intro tracks i ρ ok v step
  have norm : admiss p ρ := by
    intro w hw
    have live := (anchors_iff p keys w).mp hw
    rcases live with ⟨k,hm⟩|⟨j,hm⟩
    · exact RulePattern.image_normal (ok k) hm
    · obtain ⟨k,hk⟩ := tracks j w hm
      exact RulePattern.image_normal (ok k) hk
  obtain ⟨b,hb,η,agree,out⟩ := (run p i).covers ρ norm v step
  exact ⟨b,hb,η,fun w h => agree w ((anchors_iff p keys w).mpr h),out⟩

/-- The verified folded search obtains tracking from the reachability proof
of each normalized point. -/
def positional [DecidableEq s.ACSym] (u : VerifiedUnifier s (fun _ => True))
    (bound : ReferenceReduction.Bound rules) (groups : Groups rules) (query : Fin n → Term s) :
    FoldingNarrowing.Narrower rules query where
  branches p := (atPoint u bound groups (keysOf query) p).branches
  genuine p _ := (atPoint u bound groups (keysOf query) p).genuine
  lifts p hp := (atPoint u bound groups (keysOf query) p).covers (fromInputs query p bound hp)

end Tamarin.TableNarrowing
