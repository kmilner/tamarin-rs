import Tamarin.ACLowRank
import Tamarin.ACSeparation
import Tamarin.ACRowElimination
import Tamarin.VariantOverlapAgreement

namespace Tamarin.ACLinearConsequence
open ACBasis ACFeasibility
variable {n : Nat} {s : Signature} {I : Type}

/-- Each coordinate counts occurrences of one shared operand. Equal
occurrences on opposite sides may cancel before checking a certificate. -/
def incidence (r : ACRowElimination.Row (Fin n)) : Row n :=
  Row.ofWeights r.lhs.count r.rhs.count

private def signedRow (v : Fin n → Int) : Row n :=
  Row.ofWeights (fun i => (v i).toNat) (fun i => (-(v i)).toNat)

private theorem signed_coeff (v : Fin n → Int) (i : Fin n) :
    LowRank.coeff (signedRow v) i = v i := by
  simp only [LowRank.coeff,signedRow,Row.ofWeights]
  omega

private theorem combination_holds (pairs : List (Int × Row n)) (x : Vec n)
    (premises : ∀ p ∈ pairs, p.2.Holds x) :
    (signedRow (Separation.combination pairs)).Holds x := by
  induction pairs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w,r⟩ := p
    refine LowRank.span_holds r (signedRow (Separation.combination rest)) _ 1 w 1
      (by decide) ?_ x (premises _ List.mem_cons_self) (ih (fun q h => premises q (List.mem_cons_of_mem _ h)))
    intro i
    simp only [Int.one_mul,signed_coeff]
    rfl

/-- Integer multipliers witness a rational row-span consequence. The
implication holds pointwise for every nonnegative valuation, including
valuations that vanish on any number of columns. -/
theorem holds_of_combination (rs : List (Row n)) (q : Row n) (weights : List Int) (scale : Int)
    (nonzero : scale ≠ 0)
    (span : ∀ i, scale * LowRank.coeff q i = Separation.combination (weights.zip rs) i)
    (x : Vec n) (common : ∀ r ∈ rs, r.Holds x) : q.Holds x := by
  let combined := signedRow (Separation.combination (weights.zip rs))
  have h : combined.Holds x := combination_holds _ _ (fun p hp => common p.2 (List.of_mem_zip hp).2)
  apply LowRank.span_holds combined combined q scale 1 0 nonzero _ x h h
  intro i
  simpa only [combined,signed_coeff,Int.one_mul,Int.zero_mul,Int.add_zero] using span i

private theorem count_dot (ks : List (Fin n)) (x : Vec n) : dot ks.count x = (ks.map x).sum := by
  induction ks with
  | nil => simp [dot,total,List.sum_eq_zero_iff_forall_eq_nat]
  | cons k ks ih =>
    have count : (k::ks).count = fun i => spike k 1 i + ks.count i := by
      funext i
      by_cases hk : k = i
      · subst i; simp [spike,Nat.add_comm]
      · simp [spike,hk,Ne.symm hk,List.count_cons_of_ne]
    have one : dot (spike k 1) x = x k := by
      rw [show dot (spike k 1) x = dot x (spike k 1) from by simp only [dot,Nat.mul_comm],dot_spike]
      omega
    rw [count]
    simp only [dot,Nat.add_mul,total_add,List.map_cons,List.sum_cons]
    change dot (spike k 1) x + dot ks.count x = _
    rw [one,ih]

theorem incidence_holds (r : ACRowElimination.Row (Fin n)) (x : Vec n) :
    (incidence r).Holds x ↔ ACRowElimination.Balanced r x := by
  rw [incidence, Row.ofWeights_holds,count_dot,count_dot]
  rfl

/-- Factor multiplicities are measured after the full substitution. A single
operand may contribute an arbitrarily large product of the same AC symbol. -/
theorem entails (f : s.ACSym) (get : Fin n → Term s)
    (rs : List (ACRowElimination.Row (Fin n))) (q : ACRowElimination.Row (Fin n))
    (implies : ∀ x, (∀ r ∈ rs.map incidence, r.Holds x) → (incidence q).Holds x)
    (σ : Substitution s) (common : ∀ r ∈ rs, ACRowElimination.Holds r f get σ) :
    ACRowElimination.Holds q f get σ := by
  intro k
  let x := ACRowElimination.multiplicity f σ get k
  apply (incidence_holds q x).mp (implies x _)
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact (incidence_holds p x).mpr (common p hp k)

/-- For ordinary unification, a row-span consequence may be added to the
original problem without excluding solutions. The dictionary can contain
open, compound operands with arbitrary shared variables. -/
theorem equation (f : s.ACSym) (get : Fin n → Term s) (p : Problem s) (goal : Equation s)
    (rs : List (ACRowElimination.Row (Fin n))) (q : ACRowElimination.Row (Fin n))
    (premises : ∀ r ∈ rs, ∃ e ∈ p, ACRowElimination.Represents r f get e)
    (target : ACRowElimination.Represents q f get goal)
    (implies : ∀ x, (∀ r ∈ rs.map incidence, r.Holds x) → (incidence q).Holds x)
    (σ : Substitution s) (sol : p.Solves σ) : EquivB (σ.apply goal.lhs) (σ.apply goal.rhs) := by
  apply (target.holds_iff σ).mp (entails f get rs q implies σ _)
  intro r hr
  obtain ⟨e,he,rep⟩ := premises r hr
  exact (rep.holds_iff σ).mpr (sol e he)

/-- On an overlap the two rows use independent substitutions. Any shared
column must represent the same term value modulo B in that joint instance.
Distinct columns are allowed to acquire equivalent values. -/
theorem agrees (f : s.ACSym) (left right : I → Term s) (a b : Term s)
    (rs : List (ACRowElimination.Row (Fin n))) (q : ACRowElimination.Row (Fin n))
    (implies : ∀ x, (∀ r ∈ rs.map incidence, r.Holds x) → (incidence q).Holds x)
    (layout : ∀ σ τ : Substitution s,
      (∀ i, EquivB (σ.apply (left i)) (τ.apply (right i))) →
      ∃ get : Fin n → Term s,
        (∀ r ∈ rs, ∃ i, ACRowElimination.Represents r f get ⟨σ.apply (left i),τ.apply (right i)⟩) ∧
        ACRowElimination.Represents q f get ⟨σ.apply a,τ.apply b⟩) :
    Rewriting.VariantOverlapAgreement.Agrees left right a b := by
  intro σ τ overlap
  obtain ⟨get,sources,result⟩ := layout σ τ overlap
  have consequence := entails f get rs q implies Substitution.identity (fun r hr => by
    obtain ⟨i,rep⟩ := sources r hr
    exact (rep.holds_iff Substitution.identity).mpr (by simpa using overlap i))
  simpa using (result.holds_iff Substitution.identity).mp consequence

/-- Subtracting two observations can leave two copies of the desired
equality. All four operands may themselves be products with the same head. -/
example (f : s.ACSym) (x y u v : Term s)
    (once : EquivB (.ac f x y) (.ac f u v))
    (thrice : EquivB (.ac f x (.ac f x (.ac f x y))) (.ac f u (.ac f u (.ac f u v)))) :
    EquivB x u := by
  let get (i : Fin 4) : Term s := [x,y,u,v][i]
  let first : ACRowElimination.Row (Fin 4) := ⟨[0,1],[2,3]⟩
  let second : ACRowElimination.Row (Fin 4) := ⟨[0,0,0,1],[2,2,2,3]⟩
  let target : ACRowElimination.Row (Fin 4) := ⟨[0],[2]⟩
  have a : ACRowElimination.Represents first f get ⟨.ac f x y,.ac f u v⟩ :=
    ⟨⟨_,rfl,.refl _⟩,⟨_,rfl,.refl _⟩⟩
  have b : ACRowElimination.Represents second f get
      ⟨.ac f x (.ac f x (.ac f x y)),.ac f u (.ac f u (.ac f u v))⟩ :=
    ⟨⟨_,rfl,.refl _⟩,⟨_,rfl,.refl _⟩⟩
  have out : ACRowElimination.Represents target f get ⟨x,u⟩ := ACRowElimination.singleton f get 0 2
  have implication := entails f get [first,second] target (fun val common =>
    holds_of_combination _ _ [-1,1] 2 (by decide) (by dsimp only [first,second,target]; decide)
      val common) Substitution.identity
  apply (show EquivB x u ↔ ACRowElimination.Holds target f get Substitution.identity from
    by simpa using (out.holds_iff Substitution.identity).symm).mpr
  apply implication
  intro r hr
  rcases List.mem_cons.mp hr with rfl|hr
  · exact (a.holds_iff Substitution.identity).mpr (by simpa using once)
  · obtain rfl := List.mem_singleton.mp hr
    exact (b.holds_iff Substitution.identity).mpr (by simpa using thrice)

end Tamarin.ACLinearConsequence
