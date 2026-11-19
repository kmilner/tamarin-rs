import Tamarin.ACReference
import Tamarin.TermEquality
import Tamarin.OperandBatch

/-! The unbounded reference AC step applied to arbitrary sorted operands.
The output is a family of residual conjunctions in the original term language. -/
namespace Tamarin.OperandBatch.Reference
open ACSystem OperandAbstraction
variable {sig : Signature} {n : Nat}

private theorem sorted (f : sig.ACSym) (rows : List (Row n)) :
    ∀ v ∈ variables (abstractRows 0 f rows), v.sort = sig.acSort f := by
  rw [abstract_vars]
  rintro _ hv
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv
  rfl

private def reserved (term : Fin n → Term sig) (pending : Problem sig)
    (observe avoid : List Variable) (bindings : Substitution sig) : List Variable :=
  (List.ofFn term).flatMap Term.variables ++ pending.variables ++
    observe.flatMap (fun v => (bindings.image v).variables) ++ avoid

/-- The same column may occur in any number of equations. The abstract
variables are local dictionary keys. Only their images occur in the result. -/
def split (f : sig.ACSym) (rows : List (Row n)) (term : Fin n → Term sig)
    (typed : ∀ i, HasSort (term i) (sig.acSort f)) (pending : Problem sig)
    (observe avoid : List Variable) (bindings : Substitution sig) : List (Problem sig) :=
  let abstract := abstractRows 0 f rows
  let cols := (variables abstract).eraseDups
  let answers := ACSystem.Reference.solve f abstract (sorted f rows)
    (reserved term pending observe avoid bindings)
  answers.map fun σ => residual cols (operands 0 f term typed) σ ++ pending

/-- Every original solution survives in a branch and every branch denotes
only original solutions, including the instantiation of old bindings. -/
theorem split_correct [DecidableEq sig.ACSym] (f : sig.ACSym) (rows : List (Row n))
    (term : Fin n → Term sig) (typed : ∀ i, HasSort (term i) (sig.acSort f))
    {selected : Problem sig} (layout : Represents f term rows selected)
    (pending original : Problem sig) (partition : original.Perm (selected ++ pending))
    (observe avoid : List Variable) (bindings ρ : Substitution sig) :
    Residual.Denotes (· ∈ observe) original bindings ρ ↔
      ∃ child ∈ split f rows term typed pending observe avoid bindings,
        Residual.Denotes (· ∈ observe) child bindings ρ := by
  let rs := abstractRows 0 f rows
  let cols := (variables rs).eraseDups
  let θ := operands 0 f term typed
  let keep := reserved term pending observe avoid bindings
  let answers := ACSystem.Reference.solve f rs (sorted f rows) keep
  have live (v) : v ∈ cols ↔ (problem f rs).Occurs v := by
    rw [occurs_iff_mem]; exact List.mem_eraseDups
  have separates : ∀ σ ∈ answers, ∀ v ∈ cols, ∀ w, (σ.image v).Occurs w →
      ¬ (Observed cols θ pending w ∨ ∃ x, x ∈ observe ∧ (bindings.image x).Occurs w) := by
    intro σ hσ v hv w occ h
    apply ACSystem.Reference.range_fresh hσ ((live v).mp hv) occ
    apply List.mem_append_right
    simp only [keep, reserved, List.mem_append, List.mem_flatMap, List.mem_ofFn, Term.mem_variables,
      Problem.mem_variables]
    rcases h with (⟨key, hk, hw⟩ | hw) | obs
    · have keyUsed := List.mem_eraseDups.mp hk
      rw [show variables rs = _ from abstract_vars 0 f rows] at keyUsed
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp keyUsed
      exact .inl (.inl (.inl ⟨term i, ⟨i,rfl⟩, by simpa only [θ,operand_at] using hw⟩))
    · exact .inl (.inl (.inr hw))
    · exact .inl (.inr obs)
  rw [Residual.perm _ partition]
  have same := Residual.equivalent (sig := sig) (· ∈ observe) (p := selected ++ pending)
    (q := (problem f rs).substitute θ ++ pending) (fun δ => by
      simp only [Problem.Solves, List.mem_append, or_imp, forall_and]
      exact and_congr (selected_iff 0 f term typed layout δ) Iff.rfl) bindings ρ
  rw [same, OperandAbstraction.split _ pending cols θ live answers
    (ACSystem.Reference.correct f rs (sorted f rows) keep).mathematical _ bindings separates]
  constructor
  · rintro ⟨σ, hσ, den⟩
    exact ⟨_, List.mem_map_of_mem hσ, den⟩
  · rintro ⟨child, member, den⟩
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp member
    exact ⟨σ, hσ, den⟩

section Source
variable [DecidableEq sig.ACSym] [DecidableEq (Term sig)]

/-- The source operands can be variables of proper subsorts, rigid names,
or open terms with other heads. All must admit the selected operation's sort. -/
def SortedAt (f : sig.ACSym) (p : Problem sig) : Prop :=
  ∀ e ∈ p, HasSort e.lhs (sig.acSort f) ∧ HasSort e.rhs (sig.acSort f)

private def encodeSide (table : List (Term sig)) (xs : List (Term sig))
    (nonempty : xs ≠ []) (inside : ∀ t ∈ xs, t ∈ table) :
    {side : Side table.length // side.ids.map table.get = xs} := by
  let idx (t : Term sig) (h : t ∈ table) : Fin table.length :=
    ⟨table.idxOf t, List.idxOf_lt_length_of_mem h⟩
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x rest =>
    let tail := rest.attach.map (fun t => idx t.val (inside _ (List.mem_cons_of_mem _ t.property)))
    refine ⟨⟨idx x (inside x List.mem_cons_self),tail⟩, ?_⟩
    simp [Side.ids,tail,idx,List.map_map,Function.comp_def,List.getElem_idxOf]

private def encodeRows (f : sig.ACSym) (table : List (Term sig)) (p : Problem sig)
    (inside : ∀ e ∈ p, ∀ t ∈ ACRepresentation.flatten f e.lhs ++ ACRepresentation.flatten f e.rhs,
       t ∈ table) : {rows : List (Row table.length) // Represents f table.get rows p} := by
  match p with
  | [] => exact ⟨[], .nil⟩
  | e :: es =>
    let atHead := inside e List.mem_cons_self
    let left := encodeSide table _ (ACRepresentation.flatten_nonempty f e.lhs)
      (fun t ht => atHead t (List.mem_append_left _ ht))
    let right := encodeSide table _ (ACRepresentation.flatten_nonempty f e.rhs)
      (fun t ht => atHead t (List.mem_append_right _ ht))
    let rest := encodeRows f table es fun e he => inside e (List.mem_cons_of_mem _ he)
    refine ⟨(left.val,right.val)::rest.val, .cons ?_ ?_ rest.property⟩
    · unfold Side.Represents; rw [left.property]
    · unfold Side.Represents; rw [right.property]

private structure Presentation (f : sig.ACSym) (p : Problem sig) where
  table : List (Term sig)
  rows : List (Row table.length)
  typed : ∀ i, HasSort (table.get i) (sig.acSort f)
  layout : Represents f table.get rows p

private def present (f : sig.ACSym) (p : Problem sig) (hs : SortedAt f p) :
    Presentation f p := by
  let factors (e : Equation sig) := ACRepresentation.flatten f e.lhs ++ ACRepresentation.flatten f e.rhs
  let table := (p.flatMap factors).eraseDups
  let rows := encodeRows f table p (fun e he t ht =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨e,he,ht⟩))
  refine ⟨table, rows.val, ?_, rows.property⟩
  intro i
  obtain ⟨e, he, mem⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp (List.getElem_mem i.isLt))
  rcases List.mem_append.mp mem with l|r
  · exact ACRepresentation.flatten_hasSort f e.lhs (hs e he).1 _ l
  · exact ACRepresentation.flatten_hasSort f e.rhs (hs e he).2 _ r

/-- Generate residuals directly from the source equations. The caller
selects an AC head and a batch, without constructing an abstraction or
certifying a proposed matrix or basis. -/
def splitProblem (f : sig.ACSym) (selected : Problem sig) (hs : SortedAt f selected)
    (pending : Problem sig) (observe avoid : List Variable) (bindings : Substitution sig) :
    List (Problem sig) :=
  let batch := present f selected hs
  split f batch.rows batch.table.get batch.typed pending observe avoid bindings

theorem splitProblem_correct (f : sig.ACSym) (selected : Problem sig) (hs : SortedAt f selected)
    (pending original : Problem sig) (partition : original.Perm (selected ++ pending))
    (observe avoid : List Variable) (bindings ρ : Substitution sig) :
    Residual.Denotes (· ∈ observe) original bindings ρ ↔
      ∃ child ∈ splitProblem f selected hs pending observe avoid bindings,
        Residual.Denotes (· ∈ observe) child bindings ρ :=
  let batch := present f selected hs
  split_correct f batch.rows batch.table.get batch.typed batch.layout pending original
    partition observe avoid bindings ρ

end Source
end Tamarin.OperandBatch.Reference
