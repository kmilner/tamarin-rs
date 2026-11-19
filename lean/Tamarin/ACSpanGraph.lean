import Tamarin.ACLinearConsequence
import Tamarin.ACSpanCertificate
import Tamarin.MixedSizeGraphDecode
import Tamarin.WholeLayout
import Tamarin.WholeProblem
import TamarinRuntime.ACSpanGraph

namespace Tamarin.ACSpanGraph
open Whole WholeProblem Cancellation ACBasis
variable {s : Signature}

/-- Count one class in an already instantiated operand. Equivalent
representatives may differ in their AC order or association. -/
private noncomputable def classCount (f : s.ACSym) (k : Class s) (x : Class s) : Nat := by
  classical
  exact Quotient.liftOn x (fun t => (flatten f t).count k)
    (fun _ _ h => (flatten_equiv f h).count_eq k)

private noncomputable def amount (f : s.ACSym) (k : Class s) : Option (Class s) → Nat
  | none => 0
  | some x => classCount f k x

private theorem additive (f : s.ACSym) (k : Class s) (a b : Option (Class s)) :
    amount f k (combine f a b) = amount f k a + amount f k b := by
  classical
  cases a with
  | none => simp [combine,amount]
  | some a =>
    cases b with
    | none => simp [combine,amount]
    | some b =>
      induction a using Quotient.inductionOn with
      | h a =>
        induction b using Quotient.inductionOn with
        | h b =>
          change (flatten f (.ac f a b)).count k = _
          rw [flatten_ac,List.count_append]
          rfl

private theorem amount_ext (f : s.ACSym) (v w : Option (Class s))
    (same : ∀ k, amount f k v = amount f k w) : v = w := by
  classical
  have bag (val : Option (Class s)) :
      ∃ xs : List (Class s), fold f xs = val ∧ ∀ k, xs.count k = amount f k val := by
    cases val with
    | none => exact ⟨[],rfl,fun _ => rfl⟩
    | some x =>
      induction x using Quotient.inductionOn with
      | h t => exact ⟨flatten f t,fold_flatten f t,fun _ => rfl⟩
  obtain ⟨xs,foldx,countx⟩ := bag v
  obtain ⟨ys,foldy,county⟩ := bag w
  exact foldx.symm.trans ((fold_perm f (List.perm_iff_count.mpr (fun k =>
    (countx k).trans ((same k).trans (county k).symm)))).trans foldy)

private theorem amount_parts (c : Codec s) (σ : Substitution s) {id : UInt64} {f : s.ACSym}
    (symbol : c.acs.get id = some f) (k : Class s) (t : Tree) :
    ((parts id t).map (fun child => amount f k (evalClass c σ child))).sum =
      amount f k (evalClass c σ t) := by
  rw [←fold_parts_eval c σ symbol t]
  induction parts id t with
  | nil => rfl
  | cons a rest ih =>
    cases h : evalClass c σ a with
    | none => simpa [h,amount] using ih
    | some x => simpa [h,fold,additive] using congrArg (amount f k (some x) + ·) ih

/-- A represented term with outer AC head supplies the codec declaration
required to interpret every occurrence at the selected symbol ID. -/
theorem ac_named (c : Codec s) (σ : Substitution s) {id : UInt64} {xs : List Tree}
    (valid : ∃ v, evalClass c σ (.app 4 id xs) = some v) : ∃ f, c.acs.get id = some f := by
  obtain ⟨v,ok⟩ := valid
  change (c.acs.get id).bind (fun f => fold f (evalClasses c σ xs)) = some v at ok
  cases h : c.acs.get id with
  | none => simp [h] at ok
  | some f => exact ⟨f,rfl⟩

theorem ac_named_of_layout (c : Codec s) {t : Term s} {raw : Tree} {id xs}
    (layout : Layout (encode c t) raw) (live : Live c t) (outer : canonical raw = .app 4 id xs) :
    ∃ f, c.acs.get id = some f := by
  apply ac_named c Substitution.identity (xs := xs)
  rw [←outer,←layout.observations.1]
  exact ⟨_,evalClass_key c Substitution.identity t live⟩

private noncomputable def value (c : Codec s) (σ τ : Substitution s) (f : s.ACSym)
    (k : Class s) (key : Key) : Nat :=
  amount f k (evalClass c (if key.1 = 1 then τ else σ) key.2)

private theorem left_tag (c : Codec s) (σ τ : Substitution s) (f : s.ACSym) (k : Class s) (a : Tree) :
    value c σ τ f k (tag 0 a) = amount f k (evalClass c σ a) := by
  cases h : ground a <;> simp [value,tag,h]

private theorem right_tag (c : Codec s) (σ τ : Substitution s) (f : s.ACSym) (k : Class s) (a : Tree) :
    value c σ τ f k (tag 1 a) = amount f k (evalClass c τ a) := by
  cases h : ground a with
  | false => simp [tag,h,value]
  | true => simp [tag,h,value,evalClass_ground c σ τ a h]

private theorem measured (c : Codec s) (σ τ : Substitution s) {id : UInt64} {f : s.ACSym}
    (named : c.acs.get id = some f) (k : Class s) (ks : List Key) (distinct : ks.Nodup) (a b : Tree)
    (present : ∀ z ∈ (profile id (a,b)).1 ++ (profile id (a,b)).2, z ∈ ks) :
    (row ks (profile id (a,b))).Holds (fun i => value c σ τ f k (ks.get i)) ↔
      amount f k (evalClass c σ a) = amount f k (evalClass c τ b) := by
  rw [row,Row.ofWeights_holds,
    MixedSizeGraph.count_weight ks _ _ distinct (fun _ hx => present _ (List.mem_append_left _ hx)),
    MixedSizeGraph.count_weight ks _ _ distinct (fun _ hx => present _ (List.mem_append_right _ hx))]
  simp only [profile,List.map_map,Function.comp_def,left_tag,right_tag,amount_parts c _ named]

/-- Each concrete factor class supplies one numeric solution on independently
instantiated observations. Ground keys have the same value on both sides.
The conclusion also applies to intermediate canonical subtrees that lack a
decoded value, as long as the selected AC symbol is declared. -/
theorem linear_sound (c : Codec s) (σ τ : Substitution s) {id : UInt64} {f : s.ACSym}
    (named : c.acs.get id = some f) (obs : Observations) (a b : Tree)
    (same : ∀ e ∈ obs, evalClass c σ e.1 = evalClass c τ e.2)
    (accepted : linear id obs a b = true) : evalClass c σ a = evalClass c τ b := by
  let rs := obs.map (profile id)
  let q := profile id (a,b)
  let ks := keys rs q
  have distinct : ks.Nodup := Matching.ACBagSearch.dedup_distinct _
  have present (p : Profile) (mem : p ∈ q :: rs) : ∀ z ∈ p.1 ++ p.2, z ∈ ks := fun z hz =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨p,mem,hz⟩)
  obtain ⟨cert,found⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨nonzero,_,span⟩ := SpanCertificate.run_sound found
  apply amount_ext f
  intro k
  apply (measured c σ τ named k ks distinct a b (present q List.mem_cons_self)).mp
  apply ACLinearConsequence.holds_of_combination (rs.map (row ks)) _ cert.weights cert.scale nonzero span
  intro r mem
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
  obtain ⟨⟨l,r⟩,observed,rfl⟩ := List.mem_map.mp hp
  apply (measured c σ τ named k ks distinct l r
    (present _ (List.mem_cons_of_mem _ (List.mem_map_of_mem observed)))).mpr
  exact congrArg (amount f k) (same _ observed)

end Tamarin.ACSpanGraph
