import Tamarin.DHPeerComplete
import TamarinRuntime.DHPeer

namespace Tamarin.Rewriting.DHPeer.Programs

/-- Semantics of the postfix instructions consumed by the native adapter. -/
def instr (stack : List (Expr Slot)) (op : UInt64) : Option (List (Expr Slot)) :=
  match op, stack with
  | 0, xs => some (peer :: xs)
  | 1, xs => some (r :: xs)
  | 2, xs => some (b :: xs)
  | 3, xs => some (p :: xs)
  | 4, xs => some (n :: xs)
  | 5, xs => some (.neutral :: xs)
  | 6, x :: xs => some (.inv x :: xs)
  | 7, y :: x :: xs => some (.mul x y :: xs)
  | 8, y :: x :: xs => some (.pow x y :: xs)
  | _, _ => none

def decode (ops : Array UInt64) : Option (Expr Slot) := do
  let [term] ← ops.toList.foldlM instr [] | none
  return term

/-- Each program must decode. Every semantic branch must have a program,
and every program must describe an allowed base. Enumeration order is free. -/
def Correct (candidate : Bool → Option (Array (Array UInt64))) : Prop :=
  candidate false = none ∧ ∃ rows, candidate true = some rows ∧
    (∀ row ∈ rows.toList, ∃ k ∈ arms, decode row = some k.pair.1) ∧
    (∀ k ∈ arms, ∃ row ∈ rows.toList, decode row = some k.pair.1)

theorem candidate_correct : Correct DHPeerCandidate.images := by
  refine ⟨rfl,_,rfl,?_,?_⟩
  · intro row h
    change row ∈ [#[0],#[5],#[2,3,8],#[2,3,1,6,7,8],#[2,1,6,8],#[2,3,4,1,7,6,7,8],#[2,4,1,7,6,8]] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact ⟨.unchanged,by decide,rfl⟩
      | exact ⟨.neutral,by decide,rfl⟩
      | exact ⟨.tower,by decide,rfl⟩
      | exact ⟨.cancelPositive,by decide,rfl⟩
      | exact ⟨.cancelAll,by decide,rfl⟩
      | exact ⟨.cancelMixed,by decide,rfl⟩
      | exact ⟨.cancelNegative,by decide,rfl⟩
  · intro k _
    cases k <;> first
      | exact ⟨#[0],by decide,rfl⟩
      | exact ⟨#[5],by decide,rfl⟩
      | exact ⟨#[2,3,8],by decide,rfl⟩
      | exact ⟨#[2,3,1,6,7,8],by decide,rfl⟩
      | exact ⟨#[2,1,6,8],by decide,rfl⟩
      | exact ⟨#[2,3,4,1,7,6,7,8],by decide,rfl⟩
      | exact ⟨#[2,4,1,7,6,8],by decide,rfl⟩


/-- The public variant API also exposes the enumeration to consumers that
traverse it in order. Keep that compatibility condition separate from
mathematical coverage, which only depends on membership. -/
def Ordered (candidate : Bool → Option (Array (Array UInt64))) : Prop :=
  ∀ rows, candidate true = some rows →
    rows.toList.map decode = arms.map (fun k => some k.pair.1)

theorem candidate_ordered : Ordered DHPeerCandidate.images := by
  intro rows run
  obtain rfl := Option.some.inj run
  rfl

/-- The executable reports only base images. A row denotes each semantic
arm with this decoded base. The corresponding normal value is uniquely
recoverable from the query by ordinary reduction. -/
def branches (rows : Array (Array UInt64)) : List Branch :=
  rows.toList.flatMap fun row => arms.filter fun k => decode row = some k.pair.1

def Semantic (candidate : Bool → Option (Array (Array UInt64))) : Prop :=
  ∀ {rows}
    (_ : candidate true = some rows)
    {sig : Signature} [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (_ : PowerBucket T) (_ : InverseBucket E) (_ : MulBucket E)
    (_ : ∀ eq ∈ T.rules, ConstructorVariants.head eq.lhs ≠ .free s.neutral)
    (_ : ∀ eq ∈ T.rules, ConstructorVariants.head eq.lhs ≠ .free s.one) (q : Names)
    (os : List (Observation sig)) (_ : .power ∈ os) (avoid : List Variable)
    (_ : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (_ : ∀ v, q.witness v → v ∉ avoid)
    (_ : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t),
    let answers := (branches rows).map fun k => q.arm s k os
    CompleteVariants (ruleRoot T.rules) (os.map (q.input s)) answers ∧
    ∀ a ∈ answers, a.Reconstructible (ruleRoot T.rules) (os.map (q.input s)) ∧
      a.Safe (os.map (q.input s)) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

private theorem emitted {sig : Signature} {R : Root sig} {candidate} (correct : Correct candidate) {rows}
    (accepted : candidate true = some rows) (query : List (Term sig)) (arm : Branch → Variant sig)
    (property : Variant sig → Prop)
    (h : CompleteVariants R query (arms.map arm) ∧ ∀ a ∈ arms.map arm, property a) :
    CompleteVariants R query ((branches rows).map arm) ∧ ∀ a ∈ (branches rows).map arm, property a := by
  obtain ⟨_,rows',out,_,covers⟩ := correct
  obtain rfl := Option.some.inj (accepted.symm.trans out)
  have branch (k : Branch) : k ∈ branches rows ↔ k ∈ arms := by
    simp only [branches,List.mem_flatMap,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨_,_,h,_⟩; exact h
    · intro h; obtain ⟨row,mem,read⟩ := covers k h
      exact ⟨row,mem,h,read⟩
  have same (a : Variant sig) : a ∈ (branches rows).map arm ↔
      a ∈ arms.map arm := by simp only [List.mem_map, branch]
  obtain ⟨⟨sound,all⟩,safe⟩ := h
  refine ⟨⟨fun a h => sound a ((same a).mp h),?_⟩,fun a h => safe a ((same a).mp h)⟩
  intro ρ hn vs nv
  obtain ⟨a,mem,h⟩ := all ρ hn vs nv
  exact ⟨a,(same a).mpr mem,h⟩

theorem certified {candidate} (correct : Correct candidate) : Semantic candidate := by
  intro rows accepted sig _ s T E power inverse mult neutral one q os occurs avoid apart reserved contexts
  exact emitted correct accepted _ _ _ (DHPeer.certified power inverse mult neutral one q os occurs avoid apart reserved contexts)

/-- The linked rows are interpreted using the entire exponent at every
occurrence of slot one, including variables shared with other observations. -/
def FactorSemantic (candidate : Bool → Option (Array (Array UInt64))) : Prop :=
  ∀ {rows} (_ : candidate true = some rows)
    {sig : Signature} [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (_ : PowerBucket T) (_ : InverseBucket E) (_ : MulBucket E)
    (_ : ∀ eq ∈ T.rules, ConstructorVariants.head eq.lhs ≠ .free s.neutral)
    (_ : ∀ eq ∈ T.rules, ConstructorVariants.head eq.lhs ≠ .free s.one) (q : Query sig)
    (_ : StableFactor s (ruleRoot T.rules) q.exponent)
    (os : List (Observation sig)) (_ : .power ∈ os) (avoid : List Variable)
    (_ : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (_ : ∀ v, q.witness v → v ∉ avoid)
    (_ : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t),
    let answers := (branches rows).map fun k => q.arm s k os
    CompleteVariants (ruleRoot T.rules) (os.map (q.input s)) answers ∧
    ∀ a ∈ answers, a.Reconstructible (ruleRoot T.rules) (os.map (q.input s)) ∧
      a.Safe (os.map (q.input s)) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

theorem certifiedFactor {candidate} (correct : Correct candidate) : FactorSemantic candidate := by
  intro rows accepted sig _ s T E power inverse mult neutral one q admit os occurs avoid apart reserved contexts
  exact emitted correct accepted _ _ _ (q.certified power inverse mult neutral one admit os occurs avoid apart reserved contexts)

end Tamarin.Rewriting.DHPeer.Programs
