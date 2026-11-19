import Tamarin.FactorCheck
import Tamarin.WholeProblem
import Tamarin.WholeLayout
import Tamarin.MatchingFree

/-! A value algebra for the factoring checker, interpreted in the quotient by B
after an arbitrary sorted substitution. Totality on malformed trees lets the
checker use free injectivity without preconditions on intermediate syntax. -/
namespace Tamarin.FactorInterpretation
open Cancellation Whole WholeProblem
variable {sig : Signature}

inductive Value (sig : Signature) where
  | semantic (val : Class sig)
  | invalid
  | malformedFree (id : UInt64) (children : List (Value sig))

private def typed (t : Term sig) : Value sig := .semantic (classOf t)

private def args (f : sig.FreeSym) (a : Fin (sig.arity f) → Term sig) : List (Value sig) :=
  List.ofFn fun i => typed (a i)

private theorem args_iff (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig) :
    args f a = args f b ↔ typed (.free f a) = typed (.free f b) := by
  constructor
  · intro h
    apply congrArg Value.semantic
    apply Quotient.sound
    apply EquivB.free
    intro i
    have hi := congrArg (fun l : List (Value sig) => l[i.val]?) h
    have hi : typed (a i) = typed (b i) := by simpa [args, List.getElem?_ofFn, i.isLt] using hi
    exact Quotient.exact (Value.semantic.inj hi)
  · intro h
    have eq := (Matching.free_equiv_iff f a b).mp (Quotient.exact (Value.semantic.inj h))
    apply congrArg List.ofFn
    funext i
    exact congrArg Value.semantic (Quotient.sound (eq i))

private noncomputable def freeValue (id : UInt64) (f : sig.FreeSym) (xs : List (Value sig)) :
    Value sig := by
  classical
  exact if h : ∃ a, xs = args f a then typed (.free f h.choose) else .malformedFree id xs

private theorem freeValue_args (id : UInt64) (f : sig.FreeSym) (a : Fin (sig.arity f) → Term sig) :
    freeValue id f (args f a) = typed (.free f a) := by
  unfold freeValue
  split
  next h => exact (args_iff f _ _).mp h.choose_spec.symm
  next h => exact False.elim (h ⟨a, rfl⟩)

private theorem freeValue_inj (id : UInt64) (f : sig.FreeSym) : Function.Injective (freeValue id f) := by
  intro xs ys eq
  unfold freeValue at eq
  split at eq <;> split at eq
  next hx hy => exact hx.choose_spec.trans (((args_iff f _ _).mpr eq).trans hy.choose_spec.symm)
  next => contradiction
  next => contradiction
  next => exact (Value.malformedFree.inj eq).2

private def asClass : Value sig → Option (Class sig)
  | .semantic x => some x
  | _ => none

private def pack : Option (Class sig) → Value sig
  | some x => .semantic x
  | none => .invalid

private def commValue (f : sig.CSym) (a b : Class sig) : Class sig :=
  Quotient.liftOn₂ a b (fun x y => classOf (.comm f x y))
    (fun _ _ _ _ ha hb => Quotient.sound (EquivB.comm_congr f ha hb))

private noncomputable def app (c : Codec sig) (k i : UInt64) (xs : List (Value sig)) : Value sig :=
  if k = 2 then
    match c.frees.get i with
    | some f => freeValue i f xs
    | none => .malformedFree i xs
  else if k = 3 then
    match c.comms.get i, xs with
    | some f, [.semantic a, .semantic b] => .semantic (commValue f a b)
    | _, _ => .invalid
  else if k = 4 then
    match c.acs.get i with
    | some f => pack (fold f (xs.filterMap asClass))
    | none => .invalid
  else .invalid

private theorem app_inj (c : Codec sig) (i : UInt64) : Function.Injective (app c 2 i) := by
  cases h : c.frees.get i with
  | none =>
    intro xs ys eq
    simpa [app, h] using eq
  | some f =>
    intro xs ys eq
    exact freeValue_inj i f (by simpa [app, h] using eq)

private theorem fold_pack (f : sig.ACSym) (u : Option (Class sig)) (ys : List (Value sig)) :
    fold f ((pack u :: ys).filterMap asClass) = combine f u (fold f (ys.filterMap asClass)) := by
  cases u <;> rfl

private theorem app_flatten (c : Codec sig) (i : UInt64) (pre inner post : List (Value sig)) :
    app c 4 i (pre ++ app c 4 i inner :: post) = app c 4 i (pre ++ inner ++ post) := by
  cases h : c.acs.get i with
  | none => simp [app, h]
  | some f => simp [app, h, List.filterMap_append, fold_append, fold_pack]

private theorem commValue_swap (f : sig.CSym) (a b : Class sig) : commValue f a b = commValue f b a := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact Quotient.sound (EquivB.comm_swap f a b)

private theorem pair_orientations {α : Type} {xs : List α} (a b : α) (h : xs.Perm [a,b]) :
    xs = [a,b] ∨ xs = [b,a] := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
    have mem := h.mem_iff.mp (List.mem_cons_self ..)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact Or.inl (congrArg _ h.cons_inv.eq_singleton)
    · exact Or.inr (congrArg _ (h.trans (.swap ..)).cons_inv.eq_singleton)

private theorem app_perm (c : Codec sig) (k : UInt64) (kind : k = 3 ∨ k = 4)
    (i : UInt64) {xs ys : List (Value sig)} (h : xs.Perm ys) : app c k i xs = app c k i ys := by
  rcases kind with rfl | rfl
  · by_cases len : xs.length = 2
    · obtain ⟨a,b,eq⟩ : ∃ a b, xs = [a,b] := ⟨_,_,List.eq_getElem_of_length_eq_two xs len⟩
      subst xs
      rcases pair_orientations a b h.symm with rfl | rfl
      · rfl
      · cases a <;> cases b <;> cases hu : c.comms.get i <;> simp [app,hu,commValue_swap]
    · have invalid (zs : List (Value sig)) (n : zs.length ≠ 2) : app c 3 i zs = .invalid := by
        cases zs with
        | nil => simp [app]
        | cons a zs =>
          cases zs with
          | nil => cases a <;> simp [app]
          | cons b zs =>
            cases zs with
            | nil => contradiction
            | cons z zs => cases a <;> cases b <;> simp [app]
      rw [invalid xs len, invalid ys (h.length_eq ▸ len)]
  · cases hu : c.acs.get i with
    | none => simp [app,hu]
    | some f => simp [app,hu,fold_perm f (h.filterMap asClass)]

private def leaf (c : Codec sig) (ρ : Substitution sig) (k i _s : UInt64) : Value sig :=
  if k = 0 then pack ((c.vars.get i).map (fun v => classOf (ρ.image v)))
  else if k = 1 then pack ((c.atoms.get i).map (fun a => classOf (.atom a)))
  else .invalid

open FactorCheck

noncomputable def model (c : Codec sig) (ρ : Substitution sig) : Interpretation (Value sig) where
  leaf := leaf c ρ
  app := app c
  free_inj := app_inj c
  perm := app_perm c
  flatten := app_flatten c

/-- The layout theorem also holds after updating variables with packet bindings. -/
theorem eval_layout_with (c : Codec sig) (ρ : Substitution sig) (m : Interpretation (Value sig))
    (apps : m.app = (model c ρ).app) {a b : Tree} (h : Layout a b) :
    m.eval a = m.eval b := by
  induction h with
  | refl => rfl
  | trans _ _ ih hj => exact ih.trans hj
  | child k i pre post _ ih =>
    simp only [Interpretation.eval, m.evalArgs_map, List.map_append, List.map_cons, ih]
  | flatten i pre inner post =>
    simp only [Interpretation.eval, m.evalArgs_map, List.map_append, List.map_cons, apps]
    exact app_flatten c i _ _ _

theorem eval_layout (c : Codec sig) (ρ : Substitution sig) {a b : Tree} (h : Layout a b) :
    (model c ρ).eval a = (model c ρ).eval b :=
  eval_layout_with c ρ _ rfl h

/-- For a binding update, it suffices to interpret only the variables that
actually occur in the encoded term. The actual image may contain fresh symbols
or variables outside the request-local codec. -/
theorem eval_encode_with (c : Codec sig) (ρ : Substitution sig) (m : Interpretation (Value sig))
    (apps : m.app = (model c ρ).app) (atoms : m.leaf 1 = (model c ρ).leaf 1)
    (t : Term sig) (ht : Live c t)
    (vars : ∀ v, t.Occurs v → m.eval (encode c (.var v)) = .semantic (classOf (ρ.image v))) :
    m.eval (encode c t) = .semantic (classOf (ρ.apply t)) := by
  induction t with
  | var v => exact vars v rfl
  | atom a =>
    change m.leaf 1 _ _ = _
    rw [atoms]
    simp [model, leaf, show c.atoms.get (c.atoms.put a) = some a from ht, pack]
    rfl
  | free f a ih =>
    obtain ⟨hf, ha⟩ := ht
    have hi (i) := ih i (ha i) (fun v hv => vars v ⟨i, hv⟩)
    simp only [encode, Interpretation.eval, m.evalArgs_map, List.map_ofFn, Function.comp_def, hi,
      apps, model, app, ite_true, hf]
    exact freeValue_args _ f (fun i => ρ.apply (a i))
  | comm f a b ia ib =>
    obtain ⟨hf, ha, hb⟩ := ht
    have va := ia ha (fun v hv => vars v (.inl hv))
    have vb := ib hb (fun v hv => vars v (.inr hv))
    simp [encode, Interpretation.eval, m.evalArgs_map, va, vb, apps, model, app, hf]
    rfl
  | ac f a b ia ib =>
    obtain ⟨hf, ha, hb⟩ := ht
    have va := ia ha (fun v hv => vars v (.inl hv))
    have vb := ib hb (fun v hv => vars v (.inr hv))
    simp [encode, Interpretation.eval, m.evalArgs_map, va, vb, apps, model, app, hf, asClass, fold,
      combine, pack]
    rfl

private theorem live_var (c : Codec sig) {t : Term sig} (ht : Live c t) {v : Variable}
    (hv : t.Occurs v) : Live c (.var v) := by
  induction t with
  | var w => obtain rfl := hv; exact ht
  | atom => exact False.elim hv
  | free f a ih => obtain ⟨i, hi⟩ := hv; exact ih i (ht.2 i) hi
  | comm f a b ia ib | ac f a b ia ib =>
    rcases hv with h | h
    · exact ia ht.2.1 h
    · exact ib ht.2.2 h

theorem eval_encode (c : Codec sig) (ρ : Substitution sig) (t : Term sig) (ht : Live c t) :
    (model c ρ).eval (encode c t) = .semantic (classOf (ρ.apply t)) := by
  apply eval_encode_with c ρ _ rfl rfl _ ht
  intro v hv
  have h : c.vars.get (c.vars.put v) = some v := live_var c ht hv
  simp [model, encode, Interpretation.eval, leaf, h, pack]

end Tamarin.FactorInterpretation
