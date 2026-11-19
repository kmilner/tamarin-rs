import Tamarin.VariantFrontier

/-! A rewrite of one observation must preserve every other observation and
every input image under the same substitution. This is the pointwise semantics
of narrowing a tuple under Tamarin's inert packing constructors. -/
namespace Tamarin.Rewriting.TupleNarrowingFrontier
open VariantJoin
variable {s : Signature} {I : Type} {n : Nat}

def replace (y : Fin n → Term s) (slot : Fin n) (v : Term s) (j : Fin n) : Term s :=
  if j = slot then v else y j

def Successors (rules : List (Equation s)) (q : Row s I (Fin n)) (out : List (Row s I (Fin n))) : Prop :=
  ∀ δ : Substitution s, (∀ i, Normal (ruleRoot rules) (δ.apply (q.input i))) → ∀ j u,
    StepModulo (ruleRoot rules) (δ.apply (q.value j)) u →
    ∃ r ∈ out, ∃ η, Fits r (fun i => δ.apply (q.input i)) (replace (fun a => δ.apply (q.value a)) j u) η

private def Represented (rows : List (Row s I (Fin n))) (x : I → Term s) (y : Fin n → Term s) : Prop :=
  ∃ r ∈ rows, ∃ δ, Fits r x y δ

private theorem coordinate {rules : List (Equation s)} {rows : List (Row s I (Fin n))}
    (closed : ∀ q ∈ rows, Successors rules q rows) {x : I → Term s} (nx : ∀ i, Normal (ruleRoot rules) (x i))
    (y : Fin n → Term s) (j : Fin n) (out : Term s) (red : Reduces (ruleRoot rules) (y j) out)
    (start : Represented rows x y) : Represented rows x (replace y j out) := by
  refine RootNarrowing.reduction_invariant (fun v => Represented rows x (replace y j v)) ?_ ?_ red ?_
  · intro a b haveA eq
    obtain ⟨r,hr,δ,h⟩ := haveA
    refine ⟨r,hr,δ,h.inputs,fun k => ?_⟩
    by_cases same : k = j
    · simpa [replace,same] using eq.symm.trans (by simpa [replace] using h.values j : EquivB a _)
    · simpa [replace,same] using h.values k
  · intro a b haveA step
    obtain ⟨r,hr,δ,h⟩ := haveA
    have atSlot : EquivB a (δ.apply (r.value j)) := by simpa [replace] using h.values j
    obtain ⟨l,rhs,basis,one,finish⟩ := step
    obtain ⟨g,hg,η,fit⟩ := closed r hr δ (fun i => (normal_equiv _ (h.inputs i)).mp (nx i)) j b
      ⟨l,rhs,atSlot.symm.trans basis,one,finish⟩
    refine ⟨g,hg,η,fun i => (h.inputs i).trans (fit.inputs i),fun k => ?_⟩
    by_cases same : k = j
    · simpa [replace,same] using fit.values j
    · exact (by simpa [replace,same] using h.values k : EquivB (replace y j b k) _).trans
        (by simpa [replace,same] using fit.values k)
  · have same : replace y j (y j) = y := by
      funext i; by_cases h : i = j <;> simp [replace,h]
    exact same.symm ▸ start

/-- Complete local successors and finite closure suffice for all simultaneous
normal forms. Coordinates may repeat and the empty tuple is included. -/
theorem covers {rules : List (Equation s)} (vars : Normalized (ruleRoot rules) Substitution.identity)
    (rows : List (Row s I (Fin n))) (closed : ∀ q ∈ rows, Successors rules q rows)
    (x : I → Term s) (nx : ∀ i, Normal (ruleRoot rules) (x i)) (start out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (start i) (out i))
    (seed : ∃ q ∈ rows, ∃ δ, Fits q x start δ) :
    ∃ r ∈ rows, r.IsNormal (ruleRoot rules) ∧ Denotes (ruleRoot rules) r x out := by
  let mix (k : Nat) (j : Fin n) := if j.val < k then out j else start j
  have reach (k) (bound : k ≤ n) : Represented rows x (mix k) := by
    induction k with
    | zero => simpa [mix,Represented] using seed
    | succ k ih =>
      let j : Fin n := ⟨k,by omega⟩
      have red : Reduces (ruleRoot rules) (mix k j) (out j) := by simpa [mix,j] using (forms j).1
      have one := coordinate closed nx (mix k) j (out j) red (ih (by omega))
      have eq : replace (mix k) j (out j) = mix (k+1) := by
        funext a
        by_cases same : a = j
        · simp [replace,same,mix,j]
        · have ne : a.val ≠ k := fun h => same (Fin.ext h)
          simp [replace,same,mix,show a.val < k+1 ↔ a.val < k by omega]
      exact eq ▸ one
  obtain ⟨r,mem,δ,fit⟩ : Represented rows x out := by simpa [mix] using reach n (Nat.le_refl _)
  exact ⟨r,mem,normal_witness vars nx (fun i => (forms i).2.1) fit⟩

end Tamarin.Rewriting.TupleNarrowingFrontier
