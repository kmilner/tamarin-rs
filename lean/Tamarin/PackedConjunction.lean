import Tamarin.Matching

/-! Maude's administrative list, cons and nil are free at TOP. Tamarin's
variables range over the algebraic sorts below TOP, so a substitution acts
only on the algebraic leaves of these spines. The same decomposition serves
unification and matching, with different relations on the leaves. -/
namespace Tamarin.PackedConjunction

inductive Spine (α : Type) where
  | leaf (a : α)
  | nil
  | cons (head tail : Spine α)
  deriving Inhabited

variable {α β : Type} {s : Signature}

def Spine.Related (r : α → β → Prop) : Spine α → Spine β → Prop
  | .leaf a, .leaf b => r a b
  | .nil, .nil => True
  | .cons a as, .cons b bs => a.Related r b ∧ as.Related r bs
  | _, _ => False

def Spine.leaves : Spine α → List α
  | .leaf a => [a]
  | .nil => []
  | .cons a as => a.leaves ++ as.leaves

def pair : Spine α → Spine β → Option (List (α × β))
  | .leaf a, .leaf b => some [(a,b)]
  | .nil, .nil => some []
  | .cons a as, .cons b bs => return (← pair a b) ++ (← pair as bs)
  | _, _ => none

theorem pair_correct (a : Spine α) (b : Spine β) :
    match pair a b with
    | none => ∀ r : α → β → Prop, ¬ a.Related r b
    | some qs => qs.map Prod.fst = a.leaves ∧ qs.map Prod.snd = b.leaves ∧
        ∀ r : α → β → Prop, a.Related r b ↔ ∀ q ∈ qs, r q.1 q.2 := by
  induction a generalizing b with
  | leaf x => cases b <;> simp [pair,Spine.Related,Spine.leaves]
  | nil => cases b <;> simp [pair,Spine.Related,Spine.leaves]
  | cons a as ia ias =>
    cases b with
    | leaf x => simp [pair,Spine.Related]
    | nil => simp [pair,Spine.Related]
    | cons b bs =>
      specialize ia b
      specialize ias bs
      cases h : pair a b with
      | none => simp [h] at ia; simp [pair,h,Spine.Related,ia]
      | some qs =>
        simp only [h] at ia
        cases hs : pair as bs with
        | none => simp [hs] at ias; simp [pair,h,hs,Spine.Related,ias]
        | some rest =>
          simp only [hs] at ias
          simp [pair,h,hs,Spine.Related,Spine.leaves,ia.1,ia.2.1,ias.1,ias.2.1,ia.2.2,ias.2.2]
          grind

def problem (qs : List (Term s × Term s)) : Problem s :=
  qs.map fun (l,r) => ⟨l,r⟩

theorem solves_iff {a b : Spine (Term s)} {qs} (h : pair a b = some qs) (σ : Substitution s) :
    (problem qs).Solves σ ↔ a.Related (fun l r => EquivB (σ.apply l) (σ.apply r)) b := by
  have ok := pair_correct a b
  rw [h] at ok
  rw [ok.2.2]
  simp [problem,Problem.Solves]
  grind

theorem matches_iff {a b : Spine (Term s)} {qs} (h : pair a b = some qs) (σ : Substitution s) :
    Matching.Matches (problem qs) σ ↔ a.Related (fun l r => EquivB (σ.apply l) r) b := by
  have ok := pair_correct a b
  rw [h] at ok
  rw [ok.2.2]
  simp [problem,Matching.Matches]
  grind

abbrev Rows := Array (Array UInt64)

-- Postorder nodes: [i] references an algebraic leaf, [] is nil, and
-- [a,as] is a cons whose tail must itself be a list. The two roots denote
-- the sequences of left and right sides of a conjunction.
private def readNode (limit : UInt64) (prior : Array (Spine UInt64)) (row : Array UInt64) :
    Option (Spine UInt64) := do
  match row.toList with
  | [] => return .nil
  | [i] => guard (i < limit); return .leaf i
  | [a,as] =>
    let head ← prior[a.toNat]?
    let tail ← prior[as.toNat]?
    if let .leaf _ := tail then none else return .cons head tail
  | _ => none

def input (nodes : Rows) (limit lhs rhs : UInt64) : Option (Spine UInt64 × Spine UInt64) := do
  let trees ← nodes.foldlM (fun prior row => return prior.push (← readNode limit prior row)) #[]
  let a ← trees[lhs.toNat]?
  let b ← trees[rhs.toNat]?
  return (a,b)

def emit (qs : List (UInt64 × UInt64)) : Rows := (#[1] :: qs.map (fun (i,j) => #[i,j])).toArray

def run (nodes : Rows) (limit lhs rhs : UInt64) : Rows :=
  match input nodes limit lhs rhs with
  | none => #[#[0]]
  | some (a,b) => match pair a b with
    | none => #[#[2]]
    | some qs => emit qs

/-- No branch may omit a coordinate or lose its variables. Interpret r as
equivalence of two instantiated leaves for unification, or of the
instantiated pattern and untouched subject for matching. -/
def Correct (kernel : Rows → UInt64 → UInt64 → UInt64 → Rows) : Prop :=
  ∀ ns n l r, match input ns n l r with
    | none => kernel ns n l r = #[#[0]]
    | some (a,b) =>
      (kernel ns n l r = #[#[2]] ∧ ∀ rel : UInt64 → UInt64 → Prop, ¬ a.Related rel b) ∨
      ∃ qs, kernel ns n l r = emit qs ∧ qs.map Prod.fst = a.leaves ∧ qs.map Prod.snd = b.leaves ∧
        ∀ rel : UInt64 → UInt64 → Prop, a.Related rel b ↔ ∀ q ∈ qs, rel q.1 q.2

theorem correct : Correct run := by
  intro ns n l r
  cases hi : input ns n l r with
  | none => simp [run,hi]
  | some roots =>
    obtain ⟨a,b⟩ := roots
    have h := pair_correct a b
    cases hp : pair a b with
    | none => exact .inl ⟨by simp [run,hi,hp],by simpa [hp] using h⟩
    | some qs => exact .inr ⟨qs,by simp [run,hi,hp],by simpa [hp] using h⟩

end Tamarin.PackedConjunction
