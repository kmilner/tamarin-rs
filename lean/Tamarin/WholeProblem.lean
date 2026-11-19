import Tamarin.WholeOrdering
import Tamarin.Cancellation
import Tamarin.Unification

/-! Semantic interpretation of request-local term identities at the whole-problem boundary. -/
namespace Tamarin.WholeProblem
open Whole
variable {sig : Signature}

structure Names (α : Type) where
  put : α → UInt64
  get : UInt64 → Option α

structure Codec (sig : Signature) where
  vars : Names Variable
  atoms : Names sig.Atom
  frees : Names sig.FreeSym
  comms : Names sig.CSym
  acs : Names sig.ACSym

def sortWord : SortId → UInt64
  | .pub => 0 | .fresh => 1 | .msg => 2 | .node => 3 | .nat => 4

def encode (c : Codec sig) : Term sig → Tree
  | .var v => .leaf 0 (c.vars.put v) (sortWord v.sort)
  | .atom a => .leaf 1 (c.atoms.put a) (sortWord (sig.atomSort a))
  | .free f args => .app 2 (c.frees.put f) (List.ofFn (fun i => encode c (args i)))
  | .comm f a b => .app 3 (c.comms.put f) [encode c a, encode c b]
  | .ac f a b => .app 4 (c.acs.put f) [encode c a, encode c b]

def Live (c : Codec sig) : Term sig → Prop
  | .var v => c.vars.get (c.vars.put v) = some v
  | .atom a => c.atoms.get (c.atoms.put a) = some a
  | .free f args => c.frees.get (c.frees.put f) = some f ∧ ∀ i, Live c (args i)
  | .comm f a b => c.comms.get (c.comms.put f) = some f ∧ Live c a ∧ Live c b
  | .ac f a b => c.acs.get (c.acs.put f) = some f ∧ Live c a ∧ Live c b

def Represents (c : Codec sig) (raw : Tree) (t : Term sig) : Prop :=
  raw = encode c t ∧ Live c t

abbrev key (c : Codec sig) (t : Term sig) := canonical (encode c t)

private theorem canonicalArgs_map (xs : List Tree) : canonicalArgs xs = xs.map canonical := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [canonicalArgs, List.map_cons, ih]

private theorem make_ac (id : UInt64) (a b : Tree) :
    make 4 id [a,b] = .app 4 id (order (parts id a ++ parts id b)) := by
  simp [make]

private theorem parts_ac (id : UInt64) (xs : List Tree) : parts id (.app 4 id xs) = xs := by
  simp [parts]

private theorem make_comm (id : UInt64) (a b : Tree) :
    make 3 id [a,b] = .app 3 id (order [a,b]) := by simp [make]

theorem key_of_equiv (c : Codec sig) {a b : Term sig} (h : EquivB a b) : key c a = key c b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ia ib => exact ia.trans ib
  | free f a b _ ih =>
    simp only [key, encode, canonical, canonicalArgs_map, List.map_ofFn, Function.comp_def] at *
    congr 2
    exact funext ih
  | comm_congr f _ _ ia ib | ac_congr f _ _ ia ib =>
    simp only [key, encode, canonical, canonicalArgs] at *
    rw [ia, ib]
  | comm_swap f a b =>
    simp only [key, encode, canonical, canonicalArgs, make_comm]
    exact congrArg _ (order_eq_of_perm (.swap _ _ []))
  | ac_swap f a b =>
    simp only [key, encode, canonical, canonicalArgs, make_ac]
    exact congrArg _ (order_eq_of_perm List.perm_append_comm)
  | ac_assoc f a b d =>
    simp only [key, encode, canonical, canonicalArgs, make_ac, parts_ac]
    apply congrArg _
    apply order_eq_of_perm
    apply ((order_perm _).append_right _).trans
    rw [List.append_assoc]
    exact ((order_perm _).symm.append_left _)

open Cancellation

private noncomputable def rep (x : Class sig) : Term sig := Classical.choose (Quotient.exists_rep x)

private theorem rep_class (x : Class sig) : classOf (rep x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

private noncomputable def freeValue (f : sig.FreeSym) (xs : List (Class sig)) : Option (Class sig) :=
  if h : xs.length = sig.arity f then
    some (classOf (.free f (fun i => rep (xs[i.val]'(by rw [h]; exact i.isLt)))))
  else none

private theorem freeValue_ofFn (f : sig.FreeSym) (a : Fin (sig.arity f) → Term sig) :
    freeValue f (List.ofFn (fun i => classOf (a i))) = some (classOf (.free f a)) := by
  simp only [freeValue, List.length_ofFn, dite_true, List.getElem_ofFn]
  apply congrArg some
  apply Quotient.sound
  exact .free f _ _ (fun i => Quotient.exact (rep_class (classOf (a i))))

private def cmul (f : sig.CSym) (a b : Class sig) : Class sig :=
  Quotient.liftOn₂ a b (fun x y => classOf (.comm f x y))
    (fun _ _ _ _ ha hb => Quotient.sound (EquivB.comm_congr f ha hb))

private theorem cmul_comm (f : sig.CSym) (a b : Class sig) : cmul f a b = cmul f b a := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact Quotient.sound (EquivB.comm_swap f a b)

private noncomputable def applyValue (c : Codec sig) (k i : UInt64) (xs : List (Class sig)) :
    Option (Class sig) :=
  if k = 4 then (c.acs.get i).bind (fun f => fold f xs)
  else if k = 3 then (c.comms.get i).bind (fun f => match xs with
    | [a,b] => some (cmul f a b)
    | _ => none)
  else if k = 2 then (c.frees.get i).bind (fun f => freeValue f xs)
  else none

mutual
  noncomputable def evalClass (c : Codec sig) (σ : Substitution sig) : Tree → Option (Class sig)
    | .leaf k i _ => if k = 0 then (c.vars.get i).map (fun v => classOf (σ.image v))
                     else if k = 1 then (c.atoms.get i).map (fun a => classOf (.atom a))
                     else none
    | .app k i xs => applyValue c k i (evalClasses c σ xs)
  noncomputable def evalClasses (c : Codec sig) (σ : Substitution sig) : List Tree → List (Class sig)
    | [] => []
    | a :: as => (evalClass c σ a).toList ++ evalClasses c σ as
end

private theorem values_filter (c : Codec sig) (σ : Substitution sig) (as : List Tree) :
    evalClasses c σ as = as.filterMap (evalClass c σ) := by
  induction as with
  | nil => rfl
  | cons a as ih => cases ha : evalClass c σ a <;> simp [evalClasses, ha, ih]

theorem fold_parts_eval (c : Codec sig) (σ : Substitution sig) {id : UInt64} {f : sig.ACSym}
    (h : c.acs.get id = some f) (a : Tree) :
    fold f ((parts id a).filterMap (evalClass c σ)) = evalClass c σ a := by
  have single (x : Tree) : fold f ([x].filterMap (evalClass c σ)) = evalClass c σ x := by
    cases hx : evalClass c σ x <;> simp [hx, fold, combine]
  cases a with
  | leaf k i s => exact single _
  | app k i xs =>
    by_cases hk : k = 4
    · subst k
      by_cases hi : id = i
      · subst i
        simp [parts_ac, evalClass, applyValue, h, values_filter]
      · simpa [parts, hi] using single (.app 4 i xs)
    · simpa [parts, hk] using single (.app k i xs)

private theorem order_pair (a b : Tree) : order [a,b] = [a,b] ∨ order [a,b] = [b,a] := by
  generalize hx : order [a,b] = xs
  have p := hx ▸ order_perm [a,b]
  cases xs with
  | nil => simp at p
  | cons x xs =>
    have hm : x ∈ [a,b] := p.mem_iff.mp (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl (congrArg _ p.cons_inv.eq_singleton)
    · exact Or.inr (congrArg _ (p.trans (.swap ..)).cons_inv.eq_singleton)

private theorem values_keys (c : Codec sig) (σ : Substitution sig) {n : Nat} (a : Fin n → Term sig)
    (h : ∀ i, evalClass c σ (key c (a i)) = some (classOf (σ.apply (a i)))) :
    evalClasses c σ (List.ofFn (fun i => key c (a i))) = List.ofFn (fun i => classOf (σ.apply (a i))) := by
  rw [values_filter]
  let indices := List.ofFn (fun i : Fin n => i)
  have hk : indices.map (fun i => key c (a i)) = List.ofFn (fun i => key c (a i)) := by
    simp [indices, List.map_ofFn, Function.comp_def]
  rw [← hk, List.filterMap_map]
  have eh : evalClass c σ ∘ (fun i => key c (a i)) = some ∘ (fun i => classOf (σ.apply (a i))) := funext h
  rw [eh, List.filterMap_eq_map, List.map_ofFn]
  rfl

theorem evalClass_key (c : Codec sig) (σ : Substitution sig) (t : Term sig) (ht : Live c t) :
    evalClass c σ (key c t) = some (classOf (σ.apply t)) := by
  induction t with
  | var v => simp [key, encode, canonical, evalClass, show c.vars.get (c.vars.put v) = some v from ht]; rfl
  | atom a => simp [key, encode, canonical, evalClass, show c.atoms.get (c.atoms.put a) = some a from ht]; rfl
  | free f a ih =>
    obtain ⟨hf, ha⟩ := ht
    have hv := values_keys c σ a (fun i => ih i (ha i))
    simp only [key, encode, canonical, canonicalArgs_map, List.map_ofFn, Function.comp_def,
      make, show (2 : UInt64) ≠ 4 by decide, show (2 : UInt64) ≠ 3 by decide, ite_false, evalClass,
      applyValue, ite_true, hf, Option.bind_some]
    rw [hv, freeValue_ofFn]
    rfl
  | comm f a b ia ib =>
    obtain ⟨hf, ha, hb⟩ := ht
    have va := ia ha
    have vb := ib hb
    change evalClass c σ (make 3 _ [key c a, key c b]) = _
    rw [make_comm]
    rcases order_pair (key c a) (key c b) with ho | ho <;>
      simp [ho, evalClass, applyValue, evalClasses, va, vb, hf, cmul_comm] <;> rfl
  | ac f a b ia ib =>
    obtain ⟨hf, ha, hb⟩ := ht
    change evalClass c σ (make 4 _ [key c a, key c b]) = _
    rw [make_ac]
    simp only [evalClass, applyValue, ite_true, hf, Option.bind_some, values_filter]
    rw [fold_perm _ (List.Perm.filterMap _ (order_perm _)), List.filterMap_append, fold_append,
      fold_parts_eval c σ hf, fold_parts_eval c σ hf, ia ha, ib hb]
    rfl

theorem canonical_iff (c : Codec sig) {a b : Term sig} (ha : Live c a) (hb : Live c b) :
    canonical (encode c a) = canonical (encode c b) ↔ EquivB a b := by
  refine ⟨fun h => ?_, key_of_equiv c⟩
  have eq := (evalClass_key c .identity a ha).symm.trans
    ((congrArg (evalClass c .identity) h).trans (evalClass_key c .identity b hb))
  have same : classOf a = classOf b := by simpa only [Substitution.apply_identity] using Option.some.inj eq
  exact Quotient.exact same

/- A rigid graph term has the same value in any two independent row substitutions. -/
mutual
  theorem evalClass_ground (c : Codec sig) (σ τ : Substitution sig) (t : Tree)
      (rigid : ground t = true) : evalClass c σ t = evalClass c τ t := by
    cases t with
    | leaf k i sort =>
      have one : k = 1 := beq_iff_eq.mp rigid
      subst k
      rfl
    | app k id xs => exact congrArg (applyValue c k id) (evalClasses_ground c σ τ xs rigid)
  theorem evalClasses_ground (c : Codec sig) (σ τ : Substitution sig) (ts : List Tree)
      (rigid : groundArgs ts = true) : evalClasses c σ ts = evalClasses c τ ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [groundArgs,Bool.and_eq_true] at rigid
      obtain ⟨head,tail⟩ := rigid
      simp only [evalClasses,evalClass_ground c σ τ t head,evalClasses_ground c σ τ ts tail]
end

end Tamarin.WholeProblem
