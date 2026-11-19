import TamarinCI

/-! A deleted constraint can be the only observation of a variable. The
residual allocator must reserve it even when the output scope of the
reduced problem contains only the other two variables. -/
namespace Tamarin.OperandRefinementTests
open OperandRefinement

private def x : Variable := ⟨0,.msg⟩
private def y : Variable := ⟨1,.msg⟩
private def z : Variable := ⟨2,.fresh⟩

private def query (s : Signature) : Problem s :=
  [⟨.var z,.var z⟩,⟨.var x,.var y⟩,⟨.var y,.var x⟩,⟨.var x,.var y⟩]

private def tag {s : Signature} : Term s → UInt64
  | .var v => v.id.toUInt64
  | _ => 0

private def decode (s : Signature) (w : UInt64) : Term s :=
  .var (if w = 0 then x else if w = 1 then y else z)

private theorem layout (s : Signature) : Encodes (query s) tag (decode s) := by
  intro e h
  simp only [query,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> exact ⟨.refl _,.refl _⟩

-- Each solver sees the same original observable scope, even when an
-- accumulated binding mentions the erased Fresh variable below a constructor.
example (s : Signature) (observed : Variable → Prop) (θ ρ : Substitution s) :
    let packet := Executable.operandRefine (wire ((query s).map (rowOf tag))).toArray
    Residual.Denotes observed (query s) θ ρ ↔ Residual.Denotes observed (reduced (query s) packet) θ ρ :=
  (semantic correct (query s) (by change 4 ≤ UInt64.size; decide) tag (decode s) (layout s)).2.2.1 observed θ ρ

private theorem erased (s : Signature) : z ∈ (query s).variables :=
  (Problem.mem_variables ..).mpr ⟨_,List.mem_cons_self,.inl rfl⟩

-- A capture of the erased variable would satisfy the retained equality but
-- disallow instances in which the Fresh variable and the shared Msg differ.
-- The reduced solver's freshness premise explicitly rules that capture out.
example {s : Signature} {σ : Substitution s} (extras : List Variable)
    (fresh : FreshFor ([⟨.var x,.var y⟩] : Problem s) ((query s).variables ++ extras) σ) :
    ¬ (σ.image x).Occurs z := by
  intro occurs
  apply fresh x ⟨_,List.mem_cons_self,.inl rfl⟩ z occurs _ (List.mem_append_left _ (erased s))
  rintro ⟨e,mem,occ⟩
  obtain rfl := List.mem_singleton.mp mem
  exact occ.elim (by intro e; cases e) (by intro e; cases e)

end Tamarin.OperandRefinementTests

namespace Tamarin.OperandRefinementTests.Freshening
variable {s : Signature} (f : s.ACSym) (hs : s.acSort f = .msg)

private def name (i : Nat) : Variable := ⟨i,.msg⟩
private def inputs : Problem s := [⟨.var x,.var x⟩,⟨.var y,.var y⟩]

private def images (first left right : Nat) : Substitution s :=
  .fromBindings [(x,.var (name first)),(y,.ac f (.var (name left)) (.var (name right)))] (by
    intro v t h
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .var _
    · change HasSort _ .msg
      rw [← hs]
      exact .ac _ _ _ (hs.symm ▸ HasSort.var _) (hs.symm ▸ HasSort.var _))

private def raw := images f hs 3 2 3
private def canonical := images f hs 4 4 5

private theorem rangeNames {v} (hv : v ∈ CallerFreshening.sources inputs (raw f hs)) :
    v = name 3 ∨ v = name 2 := by
  change v ∈ [name 3,name 3,name 2,name 3,name 2,name 3] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with h|h|h|h|h|h <;> simp [h]

-- The first image assigns 3 ↦ 4. Reaching 2 in the second image assigns
-- 2 ↦ 5, so that product must change child order to remain canonical.
private def alloc : CallerFreshening.Allocation (CallerFreshening.sources inputs (raw f hs)) where
  assign w := if w = name 2 then name 5 else name 4
  sorted := by
    intro w hw
    rcases rangeNames f hs hw with rfl|rfl <;> rfl
  injective := by
    intro u hu w hw eq
    rcases rangeNames f hs hu with rfl|rfl <;> rcases rangeNames f hs hw with rfl|rfl <;>
      first | rfl | contradiction

example : CallerFreshening.RepresentsMod inputs (raw f hs) (canonical f hs) (alloc f hs) ∧
    ¬ CallerFreshening.Represents inputs (raw f hs) (canonical f hs) (alloc f hs) := by
  constructor
  · constructor
    · intro v hv
      have keys : v = x ∨ v = y := by simpa [inputs,Problem.Occurs,Term.Occurs] using hv
      rcases keys with rfl|rfl
      · exact .refl _
      · exact .ac_swap f _ _
    · intro v outside
      apply (canonical f hs).outside
      intro mem
      apply outside
      change v ∈ [x,y] at mem
      simpa [inputs,Problem.Occurs,Term.Occurs] using mem
  · intro strict
    have eq := strict y
    change Term.ac f (.var (name 4)) (.var (name 5)) = .ac f (.var (name 5)) (.var (name 4)) at eq
    cases eq

-- Renaming the first occurrence of 3 independently would destroy sharing.
example (a : CallerFreshening.Allocation (CallerFreshening.sources inputs (raw f hs))) :
    ¬ CallerFreshening.RepresentsMod inputs (raw f hs) (images f hs 6 4 5) a := by
  intro rep
  have hx : (inputs (s := s)).Occurs x := ⟨_,List.mem_cons_self,.inl rfl⟩
  have hy : (inputs (s := s)).Occurs y := ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),.inl rfl⟩
  have shared : name 6 = a.assign (name 3) := ((rep.observed x hx).occurs_iff (name 6)).mp rfl
  have inProduct := ((rep.observed y hy).occurs_iff (name 6)).mpr (.inr shared)
  rcases inProduct with h|h <;> cases h

end Tamarin.OperandRefinementTests.Freshening

namespace Tamarin.OperandRefinementTests.Context
open Pairing (signature PTerm)
open ContextRowSelection OperandRefinement

private def box (v : Variable) : ResidualRigid.View signature :=
  .free (.other 43 2) (fun i => if i.val = 0 then .var z else .var v)
private def outer : Equation signature :=
  ⟨.ac 0 (.var z) (box x).term,.ac 0 (box y).term (.var z)⟩
private def get (i : UInt64) : PTerm :=
  if i = 0 then (box x).term else if i = 1 then (box y).term else .var z
private def key : Equation signature := ⟨.var x,.var y⟩
private def rev : Equation signature := ⟨.var y,.var x⟩

private theorem trace : Peels Executable.residualRigid Executable.cancelCommon outer key := by
  refine Peels.ac (sig := signature) 0 get #[2,0] #[1,2] ?_ 0 1 (by cbv) ?_
  · exact ⟨⟨_,rfl,.refl _⟩,⟨_,rfl,.refl _⟩⟩
  · refine Peels.free (sig := signature) (box x) (box y) (fun _ => 0) (fun _ _ => rfl)
      tag (some ∘ decode signature) ?_ (by decide +kernel) 1 (l := .var x) (r := .var y) rfl rfl ?_ ?_
    · intro t ht
      change t ∈ [.var z,.var x,.var z,.var y] at ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl <;> rfl
    · intro j hj u v hu hv
      change [.var z,.var x][j]? = some u at hu
      change [.var z,.var y][j]? = some v at hv
      have lt : j < 2 := (List.getElem?_eq_some_iff.mp hu).choose
      have : j = 0 := by omega
      subst j; cases hu; cases hv; exact .refl _
    · exact .stop _

-- Compare using x=y and its reverse, but read the selected indices from the
-- original problem. Either representative is valid for this observation.
example (observed : Variable → Prop) (θ ρ : Substitution signature) :
    let selected := Executable.operandRefine (wire ([key,rev].map (rowOf tag))).toArray
    Residual.Denotes observed [outer,rev] θ ρ ↔
      Residual.Denotes observed (reduced [outer,rev] selected) θ ρ := by
  let rows := [(outer,key),(rev,rev)]
  have steps : ∀ pair ∈ rows, Peels Executable.residualRigid Executable.cancelCommon pair.1 pair.2 := by
    intro pair hp
    change pair ∈ [(outer,key),(rev,rev)] at hp
    rcases List.mem_cons.mp hp with rfl|h
    · exact trace
    · obtain rfl := List.mem_singleton.mp h; exact .stop _
  have interned : OperandRefinement.Encodes (rows.map Prod.snd) tag (decode signature) := by
    intro e he
    change e ∈ [key,rev] at he
    rcases List.mem_cons.mp he with rfl|h
    · exact ⟨.refl _,.refl _⟩
    · obtain rfl := List.mem_singleton.mp h; exact ⟨.refl _,.refl _⟩
  exact (exportedContextRowSelection_semantic rows (by decide) steps tag (decode signature) interned).2.2.2.1
    observed θ ρ

end Tamarin.OperandRefinementTests.Context
