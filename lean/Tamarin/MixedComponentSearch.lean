import Tamarin.MixedRigidBranches
import Tamarin.ACReferenceBranch

/-! Combine the homogeneous answers of distinct AC operators on a shared worklist.
The denotation observes the same slots in every child, including slots that disappear
from the pending equations. A deferred child prevents completion of its parent. -/
namespace Tamarin.MixedUnification.ComponentSearch
open OperandBatch.Reference
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def sameHead : Constraint s → Constraint s → Bool
  | .atom _ a,.atom _ b => decide (a = b)
  | .free _ f _,.free _ g _ => decide (f = g)
  | .comm _ f ..,.comm _ g .. => decide (f = g)
  | .ac _ f ..,.ac _ g .. => decide (f = g)
  | _,_ => false

private def compatible (cs : List (Constraint s)) :=
  cs.all fun a => cs.all fun b => a.out != b.out || sameHead a b

private theorem model_compatible (q : System s) {V} (h : q.Model V) : compatible q.constraints := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  by_cases eq : a.out = b.out
  · have lhs := h a ha
    have rhs := h b hb
    unfold Constraint.Holds at lhs rhs
    rw [eq] at lhs
    have heads := (lhs.symm.trans rhs).head_eq
    simp [eq]
    cases a <;> cases b <;> simp_all [sameHead,Constraint.term,headModel,Model.eval]
  · simp [eq]

private def anchors (vs : List Variable) : Problem s := vs.map fun v => ⟨.var v,.var v⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] [DecidableEq s.ACSym] in
private theorem anchored (p : Problem s) (vs : List Variable) (v) (h : v ∈ vs) :
    (p ++ anchors vs).Occurs v :=
  ⟨⟨.var v,.var v⟩,List.mem_append_right _ (List.mem_map_of_mem h),.inl rfl⟩

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] [DecidableEq s.ACSym] in
private theorem solves_anchored (p : Problem s) (vs) (δ : Substitution s) :
    (p ++ anchors vs).Solves δ ↔ p.Solves δ := by
  constructor
  · exact fun h e he => h e (List.mem_append_left _ he)
  · intro h e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp he; exact .refl _

abbrev Exact (p : Problem s) (observe : List Variable) (answers : List (Substitution s)) :=
  ∀ ρ, Residual.Denotes (· ∈ observe) p .identity ρ ↔
    ∃ σ ∈ answers, Substitution.InstanceOn (· ∈ observe) ρ σ

private def direct (p : Problem s) : RigidBranches.Certified p := by
  if ok : compatible (purify p).constraints then
    exact ⟨reconstruct? p,fun _ => reconstruct_correct⟩
  else
    refine ⟨some [],?_⟩
    rintro _ ⟨⟩
    refine ⟨by simp,fun δ hd => ?_⟩
    obtain ⟨_,model,_⟩ := extend_solution p δ.image hd
    exact False.elim (ok (model_compatible _ model))

private def leaf (p : Problem s) (observe : List Variable) :
    {r : Option (List (Substitution s)) // ∀ ans, r = some ans → Exact p observe ans} := by
  let a := p ++ anchors observe
  let raw := direct a
  match hr : raw.val with
  | none => exact ⟨none,by simp⟩
  | some rows =>
    let ans := UnifierSorts.solve a rows []
    have cert := (UnifierSorts.correct a rows (raw.property _ hr) []).mathematical
    refine ⟨some ans,?_⟩
    rintro _ ⟨⟩ ρ
    constructor
    · rintro ⟨δ,hd,agree⟩
      obtain ⟨σ,hσ,μ,hm⟩ := cert.covers δ ((solves_anchored ..).mpr hd)
      exact ⟨σ,hσ,μ,fun v hv => (agree v hv).trans (hm v (anchored p observe v hv))⟩
    · rintro ⟨σ,hσ,μ,hm⟩
      exact ⟨μ.compose σ,p.solves_compose ((solves_anchored ..).mp (cert.sound σ hσ)) μ,hm⟩

/-- Sufficient structural coverage for a leaf. Either two rigid heads clash
at a slot, or every competing definition agrees modulo B for all slot values. -/
def ConstructorDecided (p : Problem s) (obs : List Variable) : Prop :=
  let cs := (purify (p ++ anchors (s := s) obs)).constraints
  compatible cs = false ∨ AgreeingDefinitions cs

private theorem leaf_completes (p : Problem s) (obs) (h : ConstructorDecided p obs) :
    (leaf p obs).val.isSome := by
  let a := p ++ anchors (s := s) obs
  have ha : (direct a).val.isSome := by
    unfold direct
    split
    next ok =>
      rcases h with bad | agree
      · change compatible (purify a).constraints = false at bad; simp_all
      · exact reconstructs_agreeing a agree
    next => rfl
  obtain ⟨rows,hr⟩ := Option.isSome_iff_exists.mp ha
  dsimp only [a] at hr
  unfold leaf
  dsimp only
  split <;> simp_all

private def selected (f : s.ACSym) (e : Equation s) : Bool :=
  match e.rhs with
  | .ac g _ _ => decide (f = g) && e.lhs.checkSort (s.acSort f) && e.rhs.checkSort (s.acSort f)
  | _ => false

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.Atom] in
private theorem selected_sort {f : s.ACSym} {e : Equation s} (h : selected f e) :
    HasSort e.lhs (s.acSort f) ∧ HasSort e.rhs (s.acSort f) := by
  unfold selected at h
  split at h <;> simp_all only [Bool.and_eq_true, Bool.false_eq_true]
  exact ⟨Term.checkSort_sound _ _ h.1.2, Term.checkSort_sound _ _ h.2⟩

private def children (p : Problem s) (f : s.ACSym) (observe : List Variable) :
    {cs : List (Problem s) // ∀ ρ,
      Residual.Denotes (· ∈ observe) p .identity ρ ↔
        ∃ c ∈ cs, Residual.Denotes (· ∈ observe) c .identity ρ} := by
  let sel := p.filter (selected f)
  let pending := p.filter (fun e => !(selected f e))
  have perm : p.Perm (sel ++ pending) := (List.filter_append_perm (selected f) p).symm
  have hs : SortedAt f sel := fun _ he => selected_sort (List.mem_filter.mp he).2
  exact ⟨splitProblem f sel hs pending observe [] .identity,
    splitProblem_correct f sel hs pending p perm observe [] .identity⟩

/-- Generate the entire residual family, independently of whether reconstruction
can close each leaf. The head list decreases at every homogeneous split. -/
def frontier (heads : List s.ACSym) (p : Problem s) (observe : List Variable) :
    {cs : List (Problem s) // ∀ ρ, Residual.Denotes (· ∈ observe) p .identity ρ ↔
      ∃ c ∈ cs, Residual.Denotes (· ∈ observe) c .identity ρ} := by
  match heads with
  | [] =>
    let r := RigidBranches.refineProblem p
    refine ⟨r.val,fun ρ => ⟨?_,?_⟩⟩
    · rintro ⟨δ,hs,agree⟩
      obtain ⟨c,hc,sol⟩ := r.property.2 δ.image hs
      exact ⟨c,hc,δ,sol,agree⟩
    · rintro ⟨c,hc,δ,hs,agree⟩
      exact ⟨δ,fun e he => hs e (r.property.1 c hc e he),agree⟩
  | f :: fs =>
    let cs := children p f observe
    let tail := fun c => frontier fs c observe
    refine ⟨cs.val.flatMap (fun c => (tail c).val),fun ρ => (cs.property ρ).trans ⟨?_,?_⟩⟩
    · rintro ⟨c,hc,hd⟩
      obtain ⟨d,mem,sol⟩ := ((tail c).property ρ).mp hd
      exact ⟨d,List.mem_flatMap.mpr ⟨c,hc,mem⟩,sol⟩
    · rintro ⟨d,mem,sol⟩
      obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp mem
      exact ⟨c,hc,((tail c).property ρ).mpr ⟨d,hd,sol⟩⟩

/-- A blocked leaf can instead force an identification of two observed
slots. Look only for literal aliases in the purified leaf. Anchoring both
variables prevents an absent variable from being mistaken for an alias. -/
private def forced {ι : Type} (key : ι → Variable × Variable)
    (c : Problem s) (obs : List Variable) (candidates : List ι) :
    Option {i : ι // i ∈ candidates ∧ ∀ ρ : Substitution s,
      Residual.Denotes (· ∈ obs) c .identity ρ →
      EquivB (ρ.image (key i).1) (ρ.image (key i).2)} := by
  let a := c ++ anchors (s := s) obs
  let k := (purify a).slot
  let test (i : ι) := let (x,y) := key i
    x != y && obs.contains x && obs.contains y && k (.var x) == k (.var y)
  match hit : candidates.find? test with
  | none => exact none
  | some i =>
    have yes := List.find?_some hit
    simp only [test,Bool.and_eq_true,List.contains_iff_mem,beq_iff_eq] at yes
    refine some ⟨i,List.mem_of_find?_eq_some hit,?_⟩
    rintro ρ ⟨δ,hd,agree⟩
    obtain ⟨V,values⟩ := inventory_values a δ.image ((solves_anchored ..).mpr hd)
    have atSlot (v) (hv : v ∈ obs) : EquivB (ρ.image v) (V (k (.var v))) :=
      (agree v hv).trans (values _ (var_in_inventory (anchored c obs v hv)))
    have left := atSlot _ yes.1.1.2
    rw [yes.2] at left
    exact left.trans (atSlot _ yes.1.2).symm

/-- Each entry either solves the remaining equations or requests an original
equality. Together the entries cover every denoted input. -/
abbrev Report {ι : Type} (key : ι → Variable × Variable) (cs : List ι)
    (p : Problem s) (obs : List Variable) :=
  {r : Option (List (Substitution s ⊕ ι)) // ∀ as, r = some as →
      (∀ i, Sum.inr i ∈ as → i ∈ cs) ∧
      (∀ σ, Sum.inl σ ∈ as → Residual.Denotes (· ∈ obs) p .identity σ) ∧
      ∀ ρ, Residual.Denotes (· ∈ obs) p .identity ρ →
        (∃ σ, Sum.inl σ ∈ as ∧ Substitution.InstanceOn (· ∈ obs) ρ σ) ∨
        ∃ i, Sum.inr i ∈ as ∧ EquivB (ρ.image (key i).1) (ρ.image (key i).2)}

private def finish {ι : Type} (key : ι → Variable × Variable)
    (cs : List ι) (p : Problem s) (obs : List Variable) :
    Report key cs p obs := by
  match hr : (leaf p obs).val with
  | some rows =>
    refine ⟨some (rows.map Sum.inl),?_⟩
    rintro _ ⟨⟩
    simp
    refine ⟨?_,?_⟩
    · intro σ hm
      exact ((leaf p obs).property rows hr σ).mpr ⟨σ,hm,Substitution.instanceOn_refl _ _⟩
    · intro ρ h
      exact ((leaf p obs).property rows hr ρ).mp h
  | none =>
    match forced key p obs cs with
    | none => exact ⟨none,by simp⟩
    | some ⟨i,hi,forces⟩ =>
      refine ⟨some [.inr i],?_⟩
      rintro _ ⟨⟩
      simpa using And.intro hi forces

/-- The combined search returns solved leaves and the original slot equalities
needed to reopen blocked ones. Every reported equality belongs to the supplied
finite list and is forced on the branch it replaces. -/
def analyze {ι : Type} (key : ι → Variable × Variable) (cs : List ι)
    (heads : List s.ACSym) (p : Problem s) (obs : List Variable) :
    Report key cs p obs := by
  let fs := frontier heads p obs
  let visit := fun (c : Problem s) => finish key cs c obs
  match RigidBranches.collect (fun c => (visit c).val) fs.val with
  | none => exact ⟨none,by simp⟩
  | some out =>
    refine ⟨some out.val,?_⟩
    rintro _ ⟨⟩
    refine ⟨?_,?_,?_⟩
    · intro i hi
      obtain ⟨c,_,ans,hr,mem⟩ := out.property.2 _ hi
      exact ((visit c).property ans hr).1 i mem
    · intro σ hm
      obtain ⟨c,hc,ans,hr,mem⟩ := out.property.2 _ hm
      exact (fs.property σ).mpr ⟨c,hc,((visit c).property ans hr).2.1 σ mem⟩
    · intro ρ h
      obtain ⟨c,hc,hd⟩ := (fs.property ρ).mp h
      obtain ⟨ans,hr,sub⟩ := out.property.1 c hc
      rcases ((visit c).property ans hr).2.2 ρ hd with ⟨σ,hm,agree⟩ | ⟨i,hm,eq⟩
      · exact .inl ⟨σ,sub hm,agree⟩
      · exact .inr ⟨i,sub hm,eq⟩

theorem analyze_closed {ι : Type} (key : ι → Variable × Variable) (candidates : List ι)
    (heads : List s.ACSym) (p : Problem s) (obs : List Variable)
    (closed : ∀ c ∈ (frontier heads p obs).val, ConstructorDecided c obs) :
    ∃ as, (analyze key candidates heads p obs).val = some as ∧ ∀ i, Sum.inr i ∉ as := by
  let fs := frontier heads p obs
  let visit := fun (c : Problem s) => (finish key candidates c obs).val
  have yes (c) (hc : c ∈ fs.val) : ∃ out, visit c = some out ∧ ∀ i, Sum.inr i ∉ out := by
    obtain ⟨rows,hr⟩ := Option.isSome_iff_exists.mp (leaf_completes c obs (closed c hc))
    refine ⟨rows.map Sum.inl,?_,by simp⟩
    unfold visit finish
    split <;> simp_all
  have total := RigidBranches.collect_completes visit fs.val (fun c hc => by
    obtain ⟨_,hr,_⟩ := yes c hc; simp [hr])
  obtain ⟨all,hr⟩ := Option.isSome_iff_exists.mp total
  refine ⟨all.val,?_,?_⟩
  · unfold analyze
    simp only [visit,fs] at hr
    simp [hr]
  · intro i hi
    obtain ⟨c,hc,rows,eq,mem⟩ := all.property.2 _ hi
    obtain ⟨_,hr,clean⟩ := yes c hc
    rw [eq] at hr; cases hr
    exact clean _ mem

end Tamarin.MixedUnification.ComponentSearch
