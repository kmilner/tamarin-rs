import Tamarin.Unification

/-!
# Shared rewriting and variant contracts

A theory supplies a root rewrite relation on the existing sorted free/C/AC
signature. Finite rewrite tables instantiate that relation using one shared,
finite, sort-respecting substitution per rule application. Contextual closure
and rewriting modulo B belong to this specification, not to a candidate.

No termination, confluence, normal-form oracle, or finite-variant assumption
is granted merely by supplying rules. Implementations must prove the promised
properties on their admitted domain, and exhaustion is not completion.
-/
namespace Tamarin.Rewriting
variable {sig : Signature}

/-- Positional correspondence, including equal lengths and repeated entries. -/
def Aligned {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => r a b ∧ Aligned r as bs
  | _, _ => False

theorem aligned_map {α β : Type} (r : α → β → Prop) (xs : List α) (f : α → β)
    (h : ∀ x ∈ xs, r x (f x)) : Aligned r xs (xs.map f) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

theorem Aligned.map_right {α β γ : Type} {r : α → β → Prop} {s : β → γ → Prop}
    {xs : List α} {ys : List β} (h : Aligned r xs ys) (f : α → γ)
    (hs : ∀ x ∈ xs, ∀ y, r x y → s y (f x)) : Aligned s ys (xs.map f) := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact h
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim h
    | cons y ys => exact ⟨hs x (by simp) y h.1,
        ih h.2 (fun z hz w hw => hs z (by simp [hz]) w hw)⟩

theorem aligned_maps {α β γ} {r : β → γ → Prop} (q : List α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ q, r (f a) (g a)) : Aligned r (q.map f) (q.map g) := by
  induction q with
  | nil => trivial
  | cons a _ ih => exact ⟨h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))⟩

theorem aligned_values {α β γ η} {r : β → γ → Prop} {p : γ → η → Prop}
    (q : List α) (f : α → β) (g : α → η) (ys : List γ) (h : Aligned r (q.map f) ys)
    (k : ∀ a ∈ q, ∀ y, r (f a) y → p y (g a)) : Aligned p ys (q.map g) := by
  induction q generalizing ys with
  | nil => cases ys <;> exact h
  | cons a _ ih => cases ys with
    | nil => exact False.elim h
    | cons y ys => exact ⟨k a (by simp) y h.1, ih ys h.2 (fun b hb => k b (List.mem_cons_of_mem _ hb))⟩

abbrev Root (sig : Signature) := Term sig → Term sig → Prop

/-- Declarative finite rule tables; rule variables are bound locally to an
application, independently of the variables of the term being rewritten. -/
def ruleRoot (rules : List (Equation sig)) : Root sig := fun a b =>
  ∃ r ∈ rules, ∃ σ : Substitution sig, a = σ.apply r.lhs ∧ b = σ.apply r.rhs

/-- One genuine rewrite, at any depth. B rearrangement is separate so an
identity B step does not make every term count as reducible. -/
inductive Step (root : Root sig) : Term sig → Term sig → Prop where
  | root {a b} : root a b → Step root a b
  | free (f : sig.FreeSym) (args : Fin (sig.arity f) → Term sig)
      (i : Fin (sig.arity f)) {u} : Step root (args i) u →
      Step root (.free f args) (.free f (fun j => if j = i then u else args j))
  | comm_left (f : sig.CSym) {a b} (c) : Step root a b → Step root (.comm f a c) (.comm f b c)
  | comm_right (f : sig.CSym) (c) {a b} : Step root a b → Step root (.comm f c a) (.comm f c b)
  | ac_left (f : sig.ACSym) {a b} (c) : Step root a b → Step root (.ac f a c) (.ac f b c)
  | ac_right (f : sig.ACSym) (c) {a b} : Step root a b → Step root (.ac f c a) (.ac f c b)

/-- A rewrite may be exposed by reassociation or commutation anywhere. -/
def StepModulo (root : Root sig) (a b : Term sig) : Prop :=
  ∃ a' b', EquivB a a' ∧ Step root a' b' ∧ EquivB b' b

def Normal (root : Root sig) (t : Term sig) : Prop := ∀ u, ¬ StepModulo root t u

inductive Reduces (root : Root sig) : Term sig → Term sig → Prop where
  | basis {a b} : EquivB a b → Reduces root a b
  | step {a b} : StepModulo root a b → Reduces root a b
  | trans {a b c} : Reduces root a b → Reduces root b c → Reduces root a c
  | free (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig)
      (h : ∀ i, Reduces root (a i) (b i)) : Reduces root (.free f a) (.free f b)
  | comm (f : sig.CSym) {a b c d} : Reduces root a c → Reduces root b d →
      Reduces root (.comm f a b) (.comm f c d)
  | ac (f : sig.ACSym) {a b c d} : Reduces root a c → Reduces root b d →
      Reduces root (.ac f a b) (.ac f c d)

theorem normal_equiv (root : Root sig) {a b : Term sig} (h : EquivB a b) :
    Normal root a ↔ Normal root b := by
  constructor
  · intro hn u ⟨a', b', ha, hs, hb⟩
    exact hn u ⟨a', b', h.trans ha, hs, hb⟩
  · intro hn u ⟨a', b', ha, hs, hb⟩
    exact hn u ⟨a', b', h.symm.trans ha, hs, hb⟩

/-- The reference semantics imposes no algorithm or canonical B ordering. -/
def NormalForm (root : Root sig) (input result : Term sig) : Prop :=
  Reduces root input result ∧ Normal root result ∧
    ∀ s, HasSort input s → HasSort result s

/-- Normalizer candidates cannot report a partial reduction as complete. -/
inductive NormalizeResult (sig : Signature) where
  | complete (term : Term sig)
  | stopped (reason : StopReason) (term : Term sig)

def NormalizeResult.Correct (root : Root sig) (input : Term sig) :
    NormalizeResult sig → Prop
  | .complete result => NormalForm root input result
  | .stopped _ result => Reduces root input result

/-- Correctness and completion are separate; an always-stopped candidate
cannot satisfy a total contract on an admitted input domain. -/
structure Normalizer (root : Root sig) (domain : Term sig → Prop) where
  run : Term sig → NormalizeResult sig
  correct : ∀ t, domain t → (run t).Correct root t
  completes : ∀ t, domain t → ∃ u, run t = .complete u

def Normalized (root : Root sig) (σ : Substitution sig) : Prop :=
  ∀ v, Normal root (σ.image v)

def Observed (query : List (Term sig)) (v : Variable) : Prop :=
  ∃ t ∈ query, t.Occurs v

/-- Values are part of the answer, so soundness checks the actual candidate
output rather than silently replacing it with a reference normalizer. -/
structure Variant (sig : Signature) where
  subst : Substitution sig
  values : List (Term sig)

def Variant.Sound (root : Root sig) (query : List (Term sig)) (answer : Variant sig) : Prop :=
  Normalized root answer.subst ∧
    Aligned (fun t u => NormalForm root (answer.subst.apply t) u) query answer.values

/-- A substitution-only adapter re-normalizes each observation. Every choice
of normal values must recover the certified tuple modulo B. This obligation
is local to the returned arm and does not require global confluence. -/
def Variant.Reconstructible (root : Root sig) (query : List (Term sig)) (answer : Variant sig) : Prop :=
  ∀ values, Aligned (fun t u => NormalForm root (answer.subst.apply t) u) query values →
    Aligned EquivB values answer.values

theorem Variant.reconstructible_of_unique {root : Root sig} {query : List (Term sig)} {a : Variant sig}
    (ha : a.Sound root query)
    (unique : ∀ t ∈ query, ∀ u v, NormalForm root (a.subst.apply t) u →
      NormalForm root (a.subst.apply t) v → EquivB u v) : a.Reconstructible root query := by
  intro values nf
  have stored := ha.2
  clear ha
  generalize h : a.values = vs at stored ⊢
  clear h
  induction query generalizing values vs with
  | nil => cases values <;> cases vs <;> simp_all [Aligned]
  | cons t ts ih =>
    cases values with
    | nil => exact False.elim nf
    | cons v tail =>
      cases vs with
      | nil => exact False.elim stored
      | cons w rest => exact ⟨unique t (by simp) v w nf.1 stored.1,
          ih (fun u hu => unique u (List.mem_cons_of_mem _ hu)) _ nf.2 _ stored.2⟩

/-- One shared instantiation covers input variables AND all value components.
In particular the instantiated variant values are not normalized again. -/
def Variant.Covers (root : Root sig) (query : List (Term sig))
    (ρ : Substitution sig) (normalValues : List (Term sig)) (answer : Variant sig) : Prop :=
  ∃ δ : Substitution sig, Normalized root δ ∧
    (∀ v, Observed query v → EquivB (ρ.image v) (δ.apply (answer.subst.image v))) ∧
    Aligned (fun actual value => EquivB actual (δ.apply value)) normalValues answer.values

def CompleteVariants (root : Root sig) (query : List (Term sig))
    (answers : List (Variant sig)) : Prop :=
  (∀ answer ∈ answers, answer.Sound root query) ∧
  ∀ ρ, Normalized root ρ → ∀ values,
    Aligned (fun t u => NormalForm root (ρ.apply t) u) query values →
    ∃ answer ∈ answers, answer.Covers root query ρ values

/-- Every returned value and every visible substitution image may retain a
query variable or introduce a name fresh for the caller. A witness used only
in values has its own freshness obligation. -/
structure Variant.Safe (query : List (Term sig)) (avoid : List Variable) (answer : Variant sig) : Prop where
  domain : ∀ v, ¬ Observed query v → answer.subst.image v = .var v
  ranges : ∀ v, Observed query v → ∀ w, (answer.subst.image v).Occurs w →
    Observed query w ∨ w ∉ avoid
  values : ∀ t ∈ answer.values, ∀ w, t.Occurs w → Observed query w ∨ w ∉ avoid

theorem Variant.safe_identity (query : List (Term sig)) (avoid : List Variable) :
    (Variant.mk Substitution.identity query).Safe query avoid :=
  ⟨fun _ _ => rfl, fun _ hv _ hw => Or.inl (hw ▸ hv), fun t ht _ hw => Or.inl ⟨t, ht, hw⟩⟩

end Tamarin.Rewriting
